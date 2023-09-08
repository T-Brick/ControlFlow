import ControlFlow.Path

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

structure CFG (α : Type) [Digraph α Graph] where
  digraph : Graph α
  start : α
  start_in_graph : digraph |= start
  reachable : ∀ v ∈ Digraph.toVertices digraph,
                v = start ∨ ∃ ps, digraph |= ps : start -> v

namespace CFG

