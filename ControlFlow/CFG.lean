import ControlFlow.Path
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

structure CFG (α : Type) (Graph : (α : Type) → Type) [Digraph α Graph] where
  digraph : Graph α
  start : α
  start_in_graph : digraph |= start
  reachable : ∀ v ∈ Digraph.toVertices digraph,
                v = start ∨ ∃ ps, digraph |= ps : start -> v

instance : Coe (CFG α Graph) (Graph α) where
  coe cfg := cfg.digraph
instance : Coe (Graph α → α → β) (CFG α Graph → β) where
  coe graph_node := fun cfg => graph_node cfg.digraph cfg.start

namespace CFG

namespace Dataflow

inductive Combine where | may | must
inductive Direction where | forward | backward

def Combine.is_may  : Combine → Bool | .may => true  | .must => false
def Combine.is_must : Combine → Bool | .may => false | .must => true

def Direction.is_forward  : Direction → Bool
  | .forward => true  | .backward => false
def Direction.is_backward : Direction → Bool
  | .forward => false | .backward => true

structure Result (α β : Type) [Lattice β] [Top β] [Bot β] where
  input : α → β
  output : α → β

/- Kildall's algorithm computes the fixpoint of a dataflow analysis
    - `flow` computes the output data of node given its input
    - `entry` is the initial data of the entry node in the CFG
    - `direction` dictates where to use successors (`forward`)
        or predecessors (`backward`) when traversing the CFG
    - `combine` determines which direction in the lattice the algorithm travels
        - `.may` means travelling up (union/join)
        - `.must` means travelling down (intersection/meet)
  TODOs:
    - termination (since flow is monotonic and we don't add to the
        worklist unless we move higher/lower in the lattice, we are guarenteed
        to stop after number of nodes * height of lattice iterations)
    - worklist ordering -- postorder/reverse postorder traversal is on average
        significantly faster
 -/
partial def kildall [Lattice β] [Top β] [Bot β] [DecidableEq β]
    (cfg : CFG α Graph)
    (flow : α → β → β)
    (entry : β)
    (direction : Direction)
    (combine : Combine)
    (flow_monotonic : ∀ n, Monotone (flow n))
    : Result α β :=
  let next := if direction.is_forward then Digraph.succ else Digraph.pred

  let init_value : β := if combine.is_may then ⊥ else ⊤
  let init : α → β := fun v => if v = cfg.start then entry else init_value

  work (next cfg.digraph) (Digraph.toVertices cfg.digraph) ⟨init, init⟩

where work (next : α → List α) (worklist : List α) (acc : Result α β) : Result α β :=
  match worklist with
  | [] => acc
  | n :: ns =>
    let ⟨input, output⟩ := acc

    let new_n_output := flow n (input n)
    let new_output := fun v => if v = n then new_n_output else output v

    let (acc', worklist') := (next n).foldl (init := (⟨input, new_output⟩, ns))
      (fun (⟨input, output⟩, worklist) m =>
        let m_input := input m
        let new_m_input :=
          if combine.is_may
          then m_input ⊔ new_n_output
          else m_input ⊓ new_n_output

        if m_input = new_m_input then
          ( ⟨fun v => if v = m then new_m_input else input v, output⟩
          , if worklist.elem m then worklist else m::worklist
          )
        else ⟨⟨input, output⟩, worklist⟩
      )
    work next worklist' acc'
