import ControlFlow.Path
import ControlFlow.DAG

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

@[reducible, simp] def UndirectedGraph.Cyclic (g : Graph α) [UndirectedGraph g] :=
  ∃ v, g |= v → ∃ ps, Path.Undirected g v v ps

@[reducible, simp] def UndirectedGraph.Acyclic (g : Graph α)
    [UndirectedGraph g] : Prop :=
  ∀ v, g |= v → ¬∃ ps, Path.Undirected g v v ps

@[simp] theorem UndirectedGraph.Cyclic.not_to_acyclic [UndirectedGraph g]
    : (¬UndirectedGraph.Cyclic g) → UndirectedGraph.Acyclic (g : Graph α) := by
  simp; intro h₁ x _h₂; exact (h₁ x).right

class Tree [Digraph α Graph] (g : Graph α) [ug : UndirectedGraph g] where
  connected : Digraph.Connected g
  acyclic : UndirectedGraph.Acyclic g

class Tree.Poly [Digraph α Graph] (g : Graph α) [DAG g] where
  undirected   := Digraph.undirect g
  undirected_g := undirected.fst
  undirected_prop : UndirectedGraph undirected_g := by simp
  tree : Tree undirected_g

abbrev PolyTree     : (g : Graph α) → [DAG g] → Type := Tree.Poly
abbrev DirectedTree : (g : Graph α) → [DAG g] → Type := Tree.Poly

namespace Tree

