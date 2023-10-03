import ControlFlow.Path

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

class Digraph.Acyclic [Digraph α Graph] (g : Graph α) where
  acyclic : ∀ v ∈ Digraph.toVertices g, ¬∃ ps, Path g v v ps

abbrev DAG : (g : Graph α) → Type := Digraph.Acyclic

namespace Digraph.Acyclic
