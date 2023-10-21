import ControlFlow.Reachable
import ControlFlow.Connected
import ControlFlow.Graphs.DAG
import ControlFlow.UndirectedCycle

import Mathlib.Data.Tree

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]



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

/- The empty graph is generally not considered a tree, but this is mostly due to
    trees being defined using the V - E = 1 relation, with implicit assumptions
    on most theorems which would break for empty trees.
 -/
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
  , acyclic    :=
      UndirectedGraph.Acyclic.add_edge_start tree.acyclic e finish_out neq
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


-- todo: finish; maybe split out the unfinished part, since it isn't clear how
--    useful this is (i.e. is it worth the effort to finish soon?)
theorem iff_acyclic_add_cycle {g : Graph α} (ug : UndirectedGraph g)
    : Tree g
    ↔ UndirectedGraph.Acyclic ug
      ∧ (∀ e, e ∉ g ∧ has_vertex g e.start ∧ has_vertex g e.finish
            → UndirectedGraph.Cyclic (UndirectedGraph.add_edge ug e)) := by
  apply Iff.intro
  . intro tree
    apply And.intro (tree.acyclic)
    intro e h₂
    apply Exists.intro e.start
    have e_is : e = ⟨e.start, e.finish⟩ := by rfl
    if eq : e.start = e.finish then
      rw [e_is, eq]; apply Exists.intro [e.finish]
      exact Path.Undirected.add_edge_self_makes_cycle ug e.finish
    else
      have eupath := Path.Reachable.toUndirectedPath ug
        (tree.connected e.start e.finish h₂.right.left h₂.right.right) eq
      apply Exists.elim eupath; intro ps upath_and
      apply Exists.intro (e.start :: ps)
      simp at upath_and
      have upath := upath_and.left
      have upath'
        : Path.Undirected (add_undirected_edge g e) e.start e.finish ps := upath
      cases ps
      case nil => have := Path.pathlist_nonempty upath'.path; contradiction
      case cons x xs =>
        cases xs
        case nil =>
          have := h₂.left (Path.single_pathlist_imp_edge upath.path)
          contradiction
        case cons y ys =>
          exact Path.Undirected.cons
            (add_undirected_edge_adds g e |>.right) upath' upath_and.right
  . intro h₁
    apply (Tree.mk ug · h₁.left)
    intro u v u_in v_in
    if uv_in : has_edge g ⟨u, v⟩ then
      exact Path.Reachable.edge' uv_in |>.snd.snd
    else
      have cyclic := h₁.right ⟨u, v⟩ (And.intro uv_in (And.intro u_in v_in))
      apply Exists.elim cyclic; intro w eupath
      apply Exists.elim eupath; intro ps upath
      if uv_eq : u = v then simp [uv_eq]; exact .refl else
      have := h₁.left u
      have := Path.in_pathlist_has_path (u := u) (v := v) upath.path

      if u_in_ps : u ∈ ps then
        if v_in_ps : v ∈ ps then
          have possible_paths :=
            Path.in_pathlist_has_path upath.path u_in_ps v_in_ps uv_eq
          apply Or.elim possible_paths
              <;> (intro epath'; apply Exists.elim epath'; intro ps' path')
          . sorry
          . sorry
    -- todo: abstract the lines below? since they are quite repeatitive
        else if vw_eq : v = w then
          simp [←vw_eq] at upath
          have := v_in_ps (Path.finish_in_pathlist upath.path)
          contradiction
        else
          have upath_ww :=
            Path.Undirected.add_edge_not_use_finish_pres ug upath v_in_ps vw_eq
          have := h₁.left w (Exists.intro ps upath_ww)
          contradiction
      else if uw_eq : u = w then
        simp [←uw_eq] at upath
        have := u_in_ps (Path.finish_in_pathlist upath.path)
        contradiction
      else
        have upath_ww :=
          Path.Undirected.add_edge_not_use_start_pres ug upath u_in_ps uw_eq
        have := h₁.left w (Exists.intro ps upath_ww)
        contradiction
