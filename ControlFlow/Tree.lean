import ControlFlow.Path

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

class Tree [Digraph α Graph] (g : Graph α) [UndirectedGraph g] where
  connected : Digraph.Connected g
  acyclic : Digraph.Acyclic g

namespace Tree
