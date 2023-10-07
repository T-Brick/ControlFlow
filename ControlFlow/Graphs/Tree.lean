import ControlFlow.Path
import ControlFlow.Graphs.DAG

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

@[reducible, simp] def UndirectedGraph.Cyclic {g : Graph α}
    (_ : UndirectedGraph g) : Prop := ∃ v, ∃ ps, Path.Undirected g v v ps

@[reducible, simp] def UndirectedGraph.Acyclic {g : Graph α}
    (_ : UndirectedGraph g) : Prop := ∀ v, ¬∃ ps, Path.Undirected g v v ps

@[simp] theorem UndirectedGraph.Acyclic.iff_not_cyclic {g : Graph α}
    (ug : UndirectedGraph g) : Acyclic ug ↔ ¬Cyclic ug := by simp

@[simp] theorem UndirectedGraph.Cyclic.iff_not_acyclic {g : Graph α}
    (ug : UndirectedGraph g) : Cyclic ug ↔ ¬Acyclic ug := by simp

structure Tree {g : Graph α} (ug : UndirectedGraph g) : Prop where
  connected : Digraph.Connected g
  acyclic : UndirectedGraph.Acyclic ug

class Tree.Poly {g : Graph α} (dag : DAG g) where
  undirected   := Digraph.undirect g
  undirected_g := undirected.fst
  undirected_prop : UndirectedGraph undirected_g := by simp
  tree : Tree undirected_prop

abbrev PolyTree     : {g : Graph α} → DAG g → Type := Tree.Poly
abbrev DirectedTree : {g : Graph α} → DAG g → Type := Tree.Poly

namespace Tree

-- theorem iff_acyclic_add_cycle {g : Graph α} (ug : UndirectedGraph g)
    -- : Tree ug
    -- ↔ UndirectedGraph.Acyclic ug
      -- ∧ (∀ e, e ∉ g
            -- → UndirectedGraph.Cyclic (UndirectedGraph.add_edge g e)) := by
  -- sorry
