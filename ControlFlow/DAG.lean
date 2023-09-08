import ControlFlow.Path

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

structure Digraph.Acyclic (g : Graph α) where
  acyclic : ∀ v ∈ Digraph.toVertices g, ¬∃ ps, g |= ps : v -> v

abbrev DAG : (g : Graph α) → Type := Digraph.Acyclic

namespace Digraph.Acyclic


