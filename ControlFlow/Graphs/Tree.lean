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

def add_branch_start {g : Graph α} (tree : Tree g) (e : Edge α)
    (start_in : Digraph.has_vertex g e.start)
    (finish_out : ¬Digraph.has_vertex g e.finish)
    (neq : e.start ≠ e.finish)
    : Tree (Digraph.add_undirected_edge g e) :=
  { undirected := UndirectedGraph.add_edge tree.undirected e
  , connected  := Digraph.Connected.add_vertex_start tree.connected e start_in
  , acyclic    := sorry
  }

def add_branch_finish {g : Graph α} (tree : Tree g) (e : Edge α)
    (start_out : ¬Digraph.has_vertex g e.start)
    (finish_in : Digraph.has_vertex g e.finish)
    (neq : e.start ≠ e.finish)
    : Tree (Digraph.add_undirected_edge g e) :=
  { undirected := UndirectedGraph.add_edge tree.undirected e
  , connected  := Digraph.Connected.add_vertex_finish tree.connected e finish_in
  , acyclic    :=
      UndirectedGraph.Acyclic.add_edge_finish tree.acyclic e start_out neq
  }


def ofInductiveTree [Digraph (Nat × α) Graph] (itree : _root_.Tree α)
    : (tree : Graph (Nat × α)) ×' Tree tree :=
  walker 0 itree (fun _ => ⟨Digraph.empty, Tree.empty⟩)
where walker (id : Nat) (itree : _root_.Tree α)
    ( k : Nat → (tree : Graph (Nat × α)) ×' Tree tree) :=
  match itree with
  | .nil => k id
  | .node x .nil .nil =>
    let ⟨tree, ptree⟩ := k (id + 1)
    sorry
  | .node x (.node y ll lr) .nil => sorry
  | .node x .nil (.node y rl rr) => sorry
  | .node x (.node y ll lr) (.node z rl rr) => sorry


theorem iff_acyclic_add_cycle {g : Graph α} (ug : UndirectedGraph g)
    : Tree g
    ↔ UndirectedGraph.Acyclic ug
      ∧ (∀ e, e ∉ g
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
