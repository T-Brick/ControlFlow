import Graph.Path

namespace ControlFlow

-- TODO: clean this up and finish. also is this even useful?

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

inductive PathEdges (g : Graph α) : List (Edge α) → Type where
| edge  : e ∈ g → PathEdges g [e]
| cons : ⟨v, w⟩ ∈ g
       → PathEdges g (⟨u, v⟩::es)
       → (∀ e ∈ ⟨u, v⟩::es, w ≠ e.finish)
       → PathEdges g (⟨v, w⟩::⟨u, v⟩::es)

namespace PathEdges

open Digraph
open Path

def start {g : Graph α} : PathEdges g lst → α
  | .edge _h     => by next e => exact e.start
  | .cons _ p _ => start p

def finish {g : Graph α} : PathEdges g lst → α
  | .edge _h        => by next e => exact e.finish
  | .cons _h₁ _p h₂ => by next w => exact w

inductive Result (g : Graph α) : (lst : List (Edge α)) → Type where
| nil : Result g []
| cons_err : Result g lst → Result g (e::lst)
| ret : PathEdges g lst → Result g lst
| no_edge : (e : Edge α ) → e ∉ g → Result g (e :: lst)
| edge_connects : (e₁ e₂ : Edge α)
                →  e₁.start ≠ e₂.finish
                → Result g (e₁::e₂::lst)
| revisit : (e₁ e₂ : Edge α)
          → PathEdges g (e₂ :: lst)
          → ¬(∀ e ∈ e₂::lst, e₁.finish ≠ e.finish)
          → Result g (e₁::e₂::lst)

-- instance : Coe (Result (g : Graph α) lst) (Option (PathEdges g lst)) where
  -- coe res := match res with | .ret r => .some r | _ => .none

def Result.ok {g : Graph α} {lst : List (Edge α)} : Result g lst → Bool
  | .ret _ => true
  | _ => false

def ofEdgeList (g : Graph α) (lst : List (Edge α)) : Result g lst :=
  match lst with
  | [] => .nil
  | e :: [] =>
    if h : has_edge g e
    then .ret (.edge (has_edge_membership g e |>.mp h))
    else .no_edge e (Iff.subst (has_edge_membership g e) h)
  | ⟨v₂, w⟩ :: ⟨u, v₁⟩ :: es =>
    if h₁ : v₁ = v₂ then
      if h₂ : has_edge g ⟨v₂, w⟩ then
        match ofEdgeList g (⟨u, v₁⟩ :: es) with
        | .ret res =>
          if h₃ : List.all (⟨u, v₁⟩ :: es) (fun e => w ≠ e.finish )
          then .ret (by
              have := PathEdges.cons h₂ (by simp [←h₁] at *; exact res)
                (by simp [List.all_eq_true] at h₃; simp [←h₁]; exact h₃)
              rw [h₁]
              exact this
            )
          else
            .revisit ⟨v₂, w⟩ ⟨u, v₁⟩ res
              (by simp [List.all_eq_true, *] at *; exact h₃)
        | x => .cons_err x
      else .no_edge ⟨v₂, w⟩ (Iff.subst (has_edge_membership g ⟨v₂, w⟩) h₂)
    else .edge_connects ⟨v₂, w⟩ ⟨u, v₁⟩ (by simp [h₁, neq_symm])

def ofVertexList (g : Graph α) (lst : List α)
    : (edges : List (Edge α)) ×' (Result g edges) :=
  let edges := vertices_toEdges lst
  ⟨edges, ofEdgeList g edges⟩

def ofPath {g : Graph α} (_ : g |= ps : u → v)
    : (edges : List (Edge α)) ×' (Result g edges) := ofVertexList g ps

-- def toPath {g : Graph α} (epath : PathEdges g lst)
    -- : ((ps : List α) ×' (g |= ps : epath.start → epath.finish)) := by
  -- induction epath
  -- case edge h => next e => exact ⟨[e.finish], .edge h⟩
  -- case cons h₁ path h₂ ih => next u v es w =>
    -- let next : Path g v w [w] := .edge h₁
    -- let ps := ih.fst
    -- let path' : Path g _ _ _ := ih.snd
    -- exact ⟨w :: ps, .merge path' (sorry) (sorry)⟩

end PathEdges
