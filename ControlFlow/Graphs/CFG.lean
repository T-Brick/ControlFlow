import ControlFlow.Reachable
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Height

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

structure CFG (α : Type) (Graph : (α : Type) → Type) [Digraph α Graph] where
  digraph : Graph α
  start : Digraph.Vertices digraph
  reachable : ∀ v, Path.Reachable digraph start v

instance : Coe (CFG α Graph) (Graph α) where
  coe cfg := cfg.digraph
instance : Coe (Graph α → α → β) (CFG α Graph → β) where
  coe graph_node := fun cfg => graph_node cfg.digraph cfg.start.val

namespace CFG

@[reducible] def Reachable (cfg : CFG α Graph)
    (v : Digraph.Vertices cfg.digraph) : Prop :=
  Path.Reachable cfg.digraph cfg.start v

/- TODO?: reducibility of a CFG
    A cfg is reducible if:
      - forward edges form a DAG
      - for all back edges (a, b), b ≫ a
        (i.e. cannot enter a loop-body without going throught the loop entry)
    This can be useful for specific optimisations
 -/

nonrec def toString [ToString α] (cfg : CFG α Graph) : String :=
  s!"CFG (start = {cfg.start.val}):\n\t".append (
    Digraph.verticesToString
      (Digraph.toVertices cfg.digraph)
      (Digraph.succ cfg.digraph)
      (spacer := "\n\t")
  )
instance [ToString α] : ToString (CFG α Graph) := ⟨toString⟩

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
  flow : α → β → β
  next : α → List α
  input : α → β
  output : α → β
  fixpoint_solution : ∀ n s, s ∈ next n → flow n (input n) ≤ input s

structure State (α β : Type) [Lattice β] [Top β] [Bot β] where
  flow : α → β → β
  next : α → List α
  input : α → β
  output : α → β
  worklist : List α
  invariant : ∀ n, n ∈ worklist ∨ (∀ s, s ∈ next n → flow n (input n) ≤ input s)

/- Kildall's algorithm computes the fixpoint of a dataflow analysis
    - `flow` computes the output data of node given its input
    - `entry` is the initial data of the entry node in the CFG
    - `direction` dictates whether to use successors (`forward`)
        or predecessors (`backward`) when traversing the CFG
    - `combine` determines which direction in the lattice the algorithm travels
        - `.may` means travelling up (union/join)
        - `.must` means travelling down (intersection/meet)
  TODOs:
    - termination -- since flow is monotonic and we don't add to the
        worklist unless we move higher/lower in the lattice, we are guarenteed
        to stop after number of nodes * height of lattice iterations
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
    : Option (Result α β) :=
  let next :=
    if direction.is_forward
    then Digraph.succ cfg.digraph
    else Digraph.pred cfg.digraph

  let init_value : β := if combine.is_may then ⊥ else ⊤
  let init : α → β := fun v => if v = cfg.start.val then entry else init_value

  let state : State α β  :=
    { flow := flow
    , next := next
    , input := init
    , output := init
    , worklist := Digraph.toVertices cfg.digraph
    , invariant := by
        intro n
        have inGraph := Digraph.toVertices_has_vertex cfg.digraph n
        if h₁ : Digraph.has_vertex cfg.digraph n then
          exact .inl (inGraph.mpr h₁)
        else
          apply Or.inr
          intro s h₂
          simp only [h₁, Bool.false_eq_true, iff_false] at inGraph
          cases h₃ : direction.is_forward <;> simp [next, h₃] at h₂
          . have := Digraph.pred_of_in_graph n s h₂ |> h₁; contradiction
          . have := Digraph.succ_of_in_graph n s h₂ |> h₁; contradiction
    }
  work state

where work (state : State α β) : Option (Result α β) :=
  match hworklist : state.worklist with
  | [] =>
    .some
      { flow := state.flow
      , next := state.next
      , input := state.input
      , output := state.output
      , fixpoint_solution := by
          have := state.invariant
          simp only [hworklist, List.not_mem_nil, false_or] at this
          exact this
      }
  | n :: ns =>
    let new_n_output := flow n (state.input n)
    let new_output := fun v => if v = n then new_n_output else state.output v

    let next_nodes := state.next n
    let new_input := fun m =>
      let m_input := state.input m
      if m ∈ next_nodes then
        if combine.is_may
        then m_input ⊔ new_n_output
        else m_input ⊓ new_n_output
      else m_input
      
    have old_le_new_input : ∀ m, state.input m ≤ new_input m := by
      intro m
      simp [new_input]
      if m_in_next : m ∈ next_nodes then
        simp [m_in_next, new_n_output]
        if h₁ : combine.is_may then
          simp only [h₁, ↓reduceIte, le_sup_left]
        else
          simp [h₁]
          have := flow_monotonic n
          have invariant := state.invariant

          sorry
      else simp [m_in_next]

    let nextState :=
      { flow := state.flow
      , next := state.next
      , input := new_input
      , output := new_output
      , worklist := ns ∪ next_nodes
      , invariant := by
          intro m
          have old_invariant := state.invariant m
          simp [hworklist] at old_invariant
          if m_in_ns : m ∈ ns then simp [m_in_ns] else
          simp [m_in_ns] at old_invariant ⊢
          if m_in_next : m ∈ next_nodes then exact .inl m_in_next else
          simp [m_in_next, new_input, next_nodes]
          intro s s_in_next
          -- simp [new_input]
          sorry
      }
    -- let nextState := (state.next n).foldl (init := initState)
    --   (fun state m =>
    --     have invariant := state.invariant

    --     let m_input := state.input m
    --     let new_m_input :=
    --       if combine.is_may
    --       then m_input ⊔ new_n_output
    --       else m_input ⊓ new_n_output

    --     have m_le_new_m : m_input ≤ new_m_input := by
    --       if h₁ : combine.is_may then simp [new_m_input, h₁]
    --       else
    --         simp [new_m_input, h₁, new_n_output, m_input]
    --         sorry

    --     let new_worklist :=
    --       if state.worklist.elem m
    --       then state.worklist
    --       else m::state.worklist

    --     if m_input ≠ new_m_input then
    --       { flow := state.flow
    --       , next := state.next
    --       , input := fun v => if v = m then new_m_input else state.input v
    --       , output := state.output
    --       , worklist := new_worklist
    --       , invariant := by
    --           intro v
    --           simp [new_worklist, new_m_input]
    --           have := invariant v
    --           if m_in : m ∈ state.worklist then
    --             simp [m_in]
    --             if v_eq_m : v = m then
    --               simp [v_eq_m]
    --               sorry
    --             else
    --               simp [v_eq_m]
    --               sorry
    --           else
    --             simp [m_in]
    --             if v_eq_m : v = m then exact .inl (.inl v_eq_m)
    --             else
    --               simp [v_eq_m]
    --               sorry
    --       }
    --     else state
    --   )
    work nextState
