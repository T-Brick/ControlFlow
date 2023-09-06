import ControlFlow.Path

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

/-
  maybe we should make a specific graph with an entry node?
 -/
inductive Dom (g : Graph α) (e v₁ v₂ : α) : Prop where
| dom : (∀ p, (g |= p : e → v₂) → v₁ ∈ p) → Dom g e v₁ v₂


inductive Dom.Strict (g : Graph α) (e v₁ v₂ : α) : Prop where
| sdom : (∀ p, (g |= p : e → v₂) → v₁ ≠ v₂ ∧ v₁ ∈ p) → Dom.Strict g e v₁ v₂


instance {g : Graph α} : Coe (Dom.Strict g e v₁ v₂) (Dom g e v₁ v₂) where
  coe x := match x with
    | .sdom f => .dom (fun p path => f p path |>.right)

-- maybe make cursed notation local
notation:50 g:51 " ( " e:51 " ) |= " v₁:51 " ≫= " v₂:51 => Dom g e v₁ v₂
notation:50 g:51 " ( " e:51 " ) |= " v₁:51 " ≫ " v₂:51  => Dom.Strict g e v₁ v₂

namespace Dom

-- hehe
theorem trans {g : Graph α} {e v₁ v₂ v₃ : α}
    (h₁ : g(e) |= v₁ ≫= v₂)
    (h₂ : g(e) |= v₂ ≫= v₃)
    : g(e) |= v₁ ≫= v₃ := by
  sorry

theorem Strict.trans {g : Graph α} {e v₁ v₂ v₃ : α}
    (h₁ : g(e) |= v₁ ≫ v₂)
    (h₂ : g(e) |= v₂ ≫ v₃)
    : g(e) |= v₁ ≫ v₃ := by
  sorry

theorem unreachable {g : Graph α} {e v₂ : α}
    (h : ∀ps, ¬(g |= ps : e → v₂)) : ∀ v₁, g(e) |= v₁ ≫ v₂ := by
  intro v₁
  exact .sdom (fun ps path => by have := h ps path; contradiction)

theorem Strict.acyclic {g : Graph α} {e v : α}
    (path : g |= ps : e → v) : ¬(g(e) |= v ≫ v) := by
  intro h₁; cases h₁; case sdom f => exact (f ps path).left rfl
