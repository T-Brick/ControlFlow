import ControlFlow.Path
import Mathlib.Order.Lattice

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

structure CFG (α : Type) (Graph : (α : Type) → Type) [Digraph α Graph] where
  digraph : Graph α
  start : α
  start_in_graph : digraph |= start
  reachable : ∀ v ∈ Digraph.toVertices digraph,
                v = start ∨ ∃ ps, digraph |= ps : start -> v

instance : Coe (Graph α → α → β) (CFG α Graph → β) where
  coe graph_node := fun cfg => graph_node cfg.digraph cfg.start

namespace CFG

def kildall [SemilatticeSup α] (cfg : CFG α Graph) (bottom : β) : α → β :=
  let init : α → β := fun _ => bottom
  sorry
where work (worklist : List α) (acc : α → β) : α → β :=
  match worklist with
  | [] => acc
  | n :: ns =>
    sorry
