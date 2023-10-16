import ControlFlow.Path
import ControlFlow.Graphs.DAG
import ControlFlow.Graphs.UndirectedGraph

import Mathlib.Data.Tree

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

@[reducible, simp] def UndirectedGraph.Cyclic {g : Graph α}
    (_ug : UndirectedGraph g) : Prop := ∃ v, ∃ ps, Path.Undirected g v v ps

@[reducible, simp] def UndirectedGraph.Acyclic {g : Graph α}
    (_ug : UndirectedGraph g) : Prop := ∀ v, ¬∃ ps, Path.Undirected g v v ps

@[simp] theorem UndirectedGraph.Acyclic.iff_not_cyclic {g : Graph α}
    (ug : UndirectedGraph g) : Acyclic ug ↔ ¬Cyclic ug := by simp

@[simp] theorem UndirectedGraph.Cyclic.iff_not_acyclic {g : Graph α}
    (ug : UndirectedGraph g) : Cyclic ug ↔ ¬Acyclic ug := by simp

theorem UndirectedGraph.Acyclic.add_edge_finish {g : Graph α}
    {ug : UndirectedGraph g}
    (acyclic : Acyclic ug)
    (e : Edge α)
    (u_not_in : ¬Digraph.has_vertex g e.start)
    (neq : e.start ≠ e.finish)
    : Acyclic (add_edge ug e) := by
  intro w
  have h := acyclic w
  have := Path.Undirected.add_edge_new_start_no_cycle u_not_in neq
  if eq : e.start = w then rw [←eq]; exact this else
    simp at h
    intro h'
    apply Exists.elim h'; intro a upath
    exact Path.Undirected.add_edge_new_start_pres ug u_not_in upath
      (neq_symm eq) (neq_symm eq) |> h a


structure Tree (g : Graph α) : Prop where
  undirected : UndirectedGraph g
  connected  : Digraph.Connected g
  acyclic    : UndirectedGraph.Acyclic undirected

structure Tree.Poly {g : Graph α} (dag : DAG g) where
  undirected   := Digraph.undirect g
  undirected_g := undirected.fst
  undirected_prop : UndirectedGraph undirected_g := by simp
  tree : Tree undirected_g

abbrev PolyTree     : {g : Graph α} → DAG g → Type := Tree.Poly
abbrev DirectedTree : {g : Graph α} → DAG g → Type := Tree.Poly

namespace Tree

open Digraph

@[reducible, simp] def graph {g : Graph α} (_ : Tree g) : Graph α := g

def empty : Tree (Digraph.empty : Graph α) :=
  { undirected := UndirectedGraph.empty
  , connected  := Digraph.Connected.empty
  , acyclic    := by simp; intro u ps; exact Path.Undirected.empty
  }

def trivial (v : α) : Tree (Digraph.trivial v : Graph α) :=
  { undirected := UndirectedGraph.add_vertex UndirectedGraph.empty v
  , connected  := Digraph.Connected.trivial v
  , acyclic    := by
      simp; intro u ps upath
      have no_edge := Digraph.trivial_no_edge (Graph := Graph) v
      cases upath.path
      case edge h   => exact no_edge _ h
      case cons h _ => exact no_edge _ h
  }

def add_branch_from_start {g : Graph α} (tree : Tree g) (e : Edge α)
    (start_in : Digraph.has_vertex g e.start)
    (finish_out : ¬Digraph.has_vertex g e.finish)
    (neq : e.start ≠ e.finish)
    : Tree (Digraph.add_undirected_edge g e) :=
  { undirected := UndirectedGraph.add_edge tree.undirected e
  , connected  := Digraph.Connected.add_vertex_start tree.connected e start_in
  , acyclic    := sorry
  }

def add_branch_from_finish {g : Graph α} (tree : Tree g) (e : Edge α)
    (start_out : ¬Digraph.has_vertex g e.start)
    (finish_in : Digraph.has_vertex g e.finish)
    (neq : e.start ≠ e.finish)
    : Tree (Digraph.add_undirected_edge g e) :=
  { undirected := UndirectedGraph.add_edge tree.undirected e
  , connected  := Digraph.Connected.add_vertex_finish tree.connected e finish_in
  , acyclic    :=
      UndirectedGraph.Acyclic.add_edge_finish tree.acyclic e start_out neq
  }

private structure ofInductiveTree.walker.Result
    [Digraph (Nat × α) Graph] (orig : Graph (Nat × α)) where
  n           : Nat
  tree        : Graph (Nat × α)
  ptree       : Tree tree
  pres_vertex : ∀ v, has_vertex orig v → has_vertex tree v
  lt_in_tree  : ∀ m < n, ∃ x, has_vertex tree (m, x)
  ge_not_in   : ∀ m ≥ n, ∀ x, ¬has_vertex tree (m, x)

def ofInductiveTree [Digraph (Nat × α) Graph] (itree : _root_.Tree α)
    : (tree : Graph (Nat × α)) ×' Tree tree :=
  match itree with
  | .nil => ⟨Digraph.empty, empty⟩
  | .node x .nil .nil => ⟨Digraph.trivial (0, x), trivial (0, x)⟩
  | .node x l r =>
    let root := (0, x)
    let res :=
      walker itree 1 (Digraph.trivial root) root (trivial root)
        (Digraph.add_vertex_adds _ _)
        (fun m h => by
          simp at h; simp [h]; exact Exists.intro x (add_vertex_adds _ _))
        (fun m h₁ y h₂ => by
          have h₃ := trivial_vertex_eq (m, y) (0, x) h₂
          simp at h₃; simp [h₃.left] at h₁)
    ⟨res.tree, res.ptree⟩
where walker (itree : _root_.Tree α)
    (id : Nat)
    (tree : Graph (Nat × α))
    (ancestor : Nat × α)
    (ptree : Tree tree)
    (ancestor_in : has_vertex tree ancestor)
    (lt_in_tree : ∀ m < id, ∃ x, has_vertex tree (m, x))
    (ge_not_in : ∀ m ≥ id, ∀ x, ¬has_vertex tree (m, x))
    : ofInductiveTree.walker.Result tree :=
  match itree with
  | .nil => ⟨id, tree, ptree, by simp, lt_in_tree, ge_not_in⟩
  | .node x l r =>
    let x' := (id, x)
    have x'_not_in := ge_not_in id .refl x
    have ptree' := add_branch_from_finish ptree ⟨_, _⟩ x'_not_in ancestor_in
      (by intro eq; simp at eq; apply x'_not_in; rw [eq]; exact ancestor_in)

    have x'_in_tree' := add_undirected_edge_adds tree ⟨x', ancestor⟩
      |>.left |> edge_vertices _ _ _ |>.left

    have lt_in_tree' := fun m h =>
      if eq : m = id then Exists.intro x (by simp [eq]; exact x'_in_tree') else
      let res := lt_in_tree m (lt_of_le_of_ne (Nat.lt_succ_iff.mp h) eq)
      Exists.elim res (fun y in_tree =>
        Exists.intro y (add_undirected_edge_pres_existing_vertex _ _ _ in_tree)
      )

    have ge_not_in' := fun m h₁ y h₂ =>
      have res := ge_not_in m (Nat.le_of_succ_le h₁) y
      if eq : m = id then
        by simp [eq] at h₁; exact Nat.not_succ_le_self _ h₁
      else
        add_undirected_edge_pres_vertex tree (m, y) x' ancestor
          (by simp [eq]) (by intro eq'; rw [eq'] at res; exact res ancestor_in)
        |>.mpr h₂ |> res

    have lres :=
      walker l (id + 1) _ x' ptree' x'_in_tree' lt_in_tree' ge_not_in'
    have rres :=
      walker r lres.n lres.tree x' lres.ptree
        (lres.pres_vertex x' x'_in_tree') lres.lt_in_tree lres.ge_not_in
    have pres := fun v =>
        (rres.pres_vertex v)
      ∘ (lres.pres_vertex v)
      ∘ (add_undirected_edge_pres_existing_vertex _ _ v)
    ⟨rres.n, rres.tree, rres.ptree, pres, rres.lt_in_tree, rres.ge_not_in⟩


theorem iff_acyclic_add_cycle {g : Graph α} (ug : UndirectedGraph g)
    : Tree g
    ↔ UndirectedGraph.Acyclic ug
      ∧ (∀ e, e ∉ g
            ∧ Digraph.has_vertex g e.start
            ∧ Digraph.has_vertex g e.finish
            → UndirectedGraph.Cyclic (UndirectedGraph.add_edge ug e)) := by
  apply Iff.intro
  . intro tree
    apply And.intro
    exact tree.acyclic
    intro e h₂
    have := tree.connected
    -- simp at *
    sorry
  . sorry
