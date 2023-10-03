import ControlFlow.Path

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

@[reducible] def UndirectedGraph.Acyclic (g : Graph α)
    [UndirectedGraph g] : Prop :=
  ∀ v ∈ Digraph.toVertices g, ¬∃ ps, Path.Undirected g v v ps

class Tree [Digraph α Graph] (g : Graph α) [UndirectedGraph g] where
  connected : Digraph.Connected g
  acyclic : UndirectedGraph.Acyclic g

namespace Tree
