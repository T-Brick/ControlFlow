import Std
import Mathlib.Data.List.Basic

theorem _root_.List.filter_remove [DecidableEq α]
    (p : α → Bool) (l : List α) (v : α)
    : ¬ p v → v ∉ l.filter p := by
  intro h₁ h₂
  simp at h₁
  induction l <;> simp [List.filter] at h₂
  case cons x xs ih =>
    cases h₃ : p x <;> simp [h₃] at h₂
    case false => apply ih h₂
    case true  =>
      cases decEq x v
      case isFalse neq =>
        cases h₂
        case inl h₄ => apply neq (Eq.symm h₄)
        case inr h₄ => apply ih h₄
      case isTrue eq => simp [eq, h₁] at h₃

theorem _root_.List.filter_preserve_in [DecidableEq α]
    (p : α → Bool) (l : List α) (v : α)
    : v ∈ l ∧ p v ↔ v ∈ l.filter p := by
  apply Iff.intro
  case mp =>
    intro h
    have h₁ := h.left
    have h₂ := h.right
    induction l <;> simp [List.filter, *]
    case nil => contradiction
    case cons x xs ih =>
      cases h₃ : p x <;> simp [h₃]
      case false =>
        cases decEq x v
        case isFalse neq =>
          cases h₁
          case head => contradiction
          case tail _ h₄ => apply ih (And.intro h₄ h₂) h₄
        case isTrue eq =>
          rw [eq, h₂] at h₃
          contradiction
      case true =>
        cases decEq x v
        case isFalse neq =>
          cases h₁
          case head => contradiction
          case tail _ h₄ => exact Or.inr (ih (And.intro h₄ h₂) h₄)
        case isTrue eq => simp [eq]
  case mpr =>
    intro h₁
    induction l <;> simp [List.filter, *] at h₁
    case cons x xs ih =>
      cases h₂ : p x <;> simp [h₂] at h₁
      case false =>
        have := ih h₁
        apply And.intro
        exact List.Mem.tail x this.left
        exact this.right
      case true =>
        cases decEq x v
        case isFalse neq =>
          cases h₁
          case inl h₃ => simp [h₃] at neq
          case inr _ h₃ =>
            have := ih h₃
            apply And.intro
            exact List.Mem.tail x this.left
            exact this.right
        case isTrue eq => simp [← eq]; exact h₂

theorem _root_.List.Mem.not_mem : v ∉ x :: xs ↔ v ≠ x ∧ v ∉ xs := by
  apply Iff.intro
  case mp =>
    intro h₁
    apply And.intro <;> intro h₂ <;> simp [*] at *
  case mpr =>
    intro h₁ h₂
    cases h₂ <;> simp [*] at *
    case tail _ h₃ => exact h₁.right h₃

theorem _root_.List.filter_preserve_out [DecidableEq α]
    (p : α → Bool) (l : List α) (v : α)
    : v ∉ l → v ∉ l.filter p := by
  intro h₁ h₂
  induction l <;> simp [List.filter, *] at h₂
  case cons x xs ih =>
    cases h₃ : p x <;> simp [h₃] at h₂
    case false => exact ih (List.Mem.not_mem.mp h₁).right h₂
    case true =>
      have := List.Mem.not_mem.mp h₁
      cases h₂ <;> simp [*] at *

@[simp] def List.mapMember
    (lst : List α) (f : (a : α) → (h : a ∈ lst) → β) : List β :=
  List.attach lst |>.map (fun a => f a.val a.property)

def _root_.List.splitFirst [DecidableEq α] (y : α) (lst : List α) : Option (List α × List α) :=
  match lst with
  | [] => .none
  | x::xs =>
    if x = y then .some ([], xs ) else
    match splitFirst y xs with
    | .none => .none
    | .some (r₁, r₂) => .some (x::r₁, r₂)

theorem _root_.List.splitFirst_append [DecidableEq α]
    (y : α) (lst : List α)
    : ∀ res₁ res₂, List.splitFirst y lst = .some (res₁, res₂) → lst = res₁ ++ (y :: res₂) := by
  induction lst <;> simp [List.splitFirst, *] at *
  intro res₁ res₂ h₁
  case cons x xs ih =>
    cases decEq x y <;> simp [*] at *
    case isFalse neq =>
      split at h₁ <;> simp at *
      next r₁ r₂ heq =>
        have := ih r₁ r₂ heq
        rw [←h₁.right, ←h₁.left, this, List.cons_append]
    case isTrue eq => simp [←h₁.left, ←h₁.right]

theorem _root_.List.splitFirst_none [DecidableEq α]
    (y : α) (lst : List α)
    : List.splitFirst y lst = .none → y ∉ lst := by
  intro h₁ h₂
  induction lst <;> simp [List.splitFirst, *] at *
  case cons x xs ih =>
    cases decEq x y <;> simp [*] at *
    case isFalse neq =>
      split at h₁ <;> simp at *
      next heq =>
        apply Or.elim h₂
        . intro h₃; apply neq (Eq.symm h₃)
        . exact ih heq

theorem neq_symm [DecidableEq α] {x y : α} (h₁ : ¬x = y) : (¬y = x) :=
  fun h₂ => h₁ (Eq.symm h₂)

@[simp] theorem _root_.Or.assoc : a ∨ (b ∨ c) ↔ (a ∨ b) ∨ c := by
  apply Iff.intro <;> intro h₁
  . apply Or.elim h₁ <;> intro h₂
    . simp [h₂]
    . apply Or.elim h₂ <;> intro h₃ <;> simp [*]
  . apply Or.elim h₁ <;> intro h₂
    . apply Or.elim h₂ <;> intro h₃ <;> simp [*]
    . simp [h₂]
