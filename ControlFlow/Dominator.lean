import ControlFlow.Path

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

/-
  maybe we should make a specific graph with an entry node?
 -/
inductive Dom (g : Graph α) (e v₁ v₂ : α) : Prop where
| dom : (∀ ps, (g |= ps : e -> v₂) → v₁ ∈ ps) → Dom g e v₁ v₂


inductive Dom.Strict (g : Graph α) (e v₁ v₂ : α) : Prop where
| sdom : (∀ ps, (g |= ps : e -> v₂) → v₁ ≠ v₂ ∧ v₁ ∈ ps) → Dom.Strict g e v₁ v₂

instance {g : Graph α} : Coe (Dom.Strict g e v₁ v₂) (Dom g e v₁ v₂) where
  coe x := match x with
    | .sdom f => .dom (fun p path => f p path |>.right)

-- maybe make cursed notation local
notation:50 g:51 "(" e:51 ") |= " v₁:51 " ≫= " v₂:51 => Dom g e v₁ v₂
notation:50 g:51 "(" e:51 ") |= " v₁:51 " ≫ " v₂:51  => Dom.Strict g e v₁ v₂

namespace Dom

theorem refl {g : Graph α} (e v : α) : g(e) |= v ≫= v :=
  .dom (fun _ps path => Path.path_finish_in_pathlist path)

-- hehe
theorem trans {g : Graph α} {e v₁ v₂ v₃ : α}
    (h₁ : g(e) |= v₁ ≫= v₂)
    (h₂ : g(e) |= v₂ ≫= v₃)
    : g(e) |= v₁ ≫= v₃ := by
  cases h₁; case dom f₁ =>
  cases h₂; case dom f₂ =>
  cases decEq v₂ v₃
  case isTrue eq => rw [eq] at f₁; exact dom f₁
  case isFalse neq =>
    exact dom (fun ps₃ path₃ =>
      have p₂ := f₂ ps₃ path₃
      have splits := Path.split p₂ neq path₃
      Exists.elim splits (fun ps₁ splits' =>
        Exists.elim splits' (fun ps₂ h => by
          have := f₁ ps₁ h.right.right.left
          rw [h.right.left]; exact List.mem_append_right ps₂ this
        )
      )
    )

theorem Strict.trans {g : Graph α} {e v₁ v₂ v₃ : α}
    (h₁ : g(e) |= v₁ ≫ v₂)
    (h₂ : g(e) |= v₂ ≫ v₃)
    : g(e) |= v₁ ≫ v₃ := by
  cases h₁; case sdom f₁ =>
  cases h₂; case sdom f₂ =>
  exact sdom (fun ps₃ path₃ =>
    have p₂ := f₂ ps₃ path₃
    have split := Path.split p₂.right p₂.left path₃
    Exists.elim split (fun ps₁ split' =>
      Exists.elim split' (fun ps₂ h => by
        have p₁ := f₁ ps₁ h.right.right.left
        apply And.intro
        . intro h₃
          simp [h₃] at *
          apply List.disjoint_left.mp h.left p₁.right
          exact Path.path_finish_in_pathlist h.right.right.right
        . rw [h.right.left]; exact List.mem_append_right ps₂ p₁.right
      )
    )
  )

theorem unreachable {g : Graph α} {e v₂ : α}
    (h : ∀ps, ¬(g |= ps : e -> v₂)) : ∀ v₁, g(e) |= v₁ ≫ v₂ := by
  intro v₁
  exact .sdom (fun ps path => by have := h ps path; contradiction)

theorem Strict.acyclic {g : Graph α} {e v : α}
    (path : g |= ps : e -> v) : ¬(g(e) |= v ≫ v) := by
  intro h₁; cases h₁; case sdom f => exact (f ps path).left rfl
