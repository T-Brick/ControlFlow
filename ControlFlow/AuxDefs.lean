import Batteries
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

theorem _root_.List.filter_remove [DecidableEq α]
    (p : α → Bool) (l : List α) (v : α)
    : ¬ p v → v ∉ l.filter p := by
  intro h₁ h₂
  simp at h₁
  induction l <;> simp [List.filter] at h₂
  case cons x xs ih =>
    cases h₃ : p x <;> simp only [h₃] at h₂
    case false =>
      apply ih h₂
    case true  =>
      cases decEq x v
      case isFalse neq =>
        cases h₂
        case head h₄ => contradiction
        case tail h₄ => apply ih h₄
      case isTrue eq => simp only [eq, h₁, Bool.false_eq_true] at h₃

theorem _root_.List.filter_preserve_in [DecidableEq α]
    (p : α → Bool) (l : List α) (v : α)
    : v ∈ l ∧ p v ↔ v ∈ l.filter p := by
  apply Iff.intro
  case mp =>
    intro h
    have h₁ := h.left
    have h₂ := h.right
    induction l <;> simp only [List.filter, h]
    case cons x xs ih =>
      cases h₃ : p x <;> simp only [List.mem_cons, List.mem_filter]
      case false =>
        cases decEq x v
        case isFalse neq =>
          cases h₁
          case head => contradiction
          case tail _ h₄ => exact ⟨h₄, h.right⟩
        case isTrue eq =>
          rw [eq, h₂] at h₃
          contradiction
      case true =>
        cases decEq x v
        case isFalse neq =>
          cases h₁
          case head => contradiction
          case tail _ h₄ => exact Or.inr ⟨h₄, h.right⟩
        case isTrue eq => simp [eq]
  case mpr =>
    intro h₁
    induction l <;> simp only [List.filter, List.not_mem_nil] at h₁
    case cons x xs ih =>
      cases h₂ : p x <;> simp only [h₂] at h₁
      case false =>
        have := ih h₁
        exact ⟨List.Mem.tail x this.left, this.right⟩
      case true =>
        cases decEq x v
        case isFalse neq =>
          cases h₁
          case head h₃ => contradiction
          case tail _ h₃ =>
            have := ih h₃
            apply And.intro
            exact List.Mem.tail x this.left
            exact this.right
        case isTrue eq =>
          simp only [← eq, List.mem_cons, true_or, true_and]
          exact h₂

theorem _root_.List.Mem.not_mem : v ∉ x :: xs ↔ v ≠ x ∧ v ∉ xs := by
  apply Iff.intro
  case mp =>
    intro h₁
    apply And.intro <;> intro h₂ <;>
      simp only [List.mem_cons, true_or, or_true, not_true_eq_false, h₂] at h₁
  case mpr =>
    intro h₁ h₂
    cases h₂ <;> simp only [ne_eq, not_true_eq_false, false_and] at h₁
    case tail _ h₃ => exact h₁.right h₃

theorem _root_.List.filter_preserve_out [DecidableEq α]
    (p : α → Bool) (l : List α) (v : α)
    : v ∉ l → v ∉ l.filter p := by
  intro h₁ h₂
  induction l <;> simp only [List.filter, h₁] at h₂
  case cons x xs ih =>
    cases h₃ : p x <;> simp only [h₃] at h₂
    case false => exact ih (List.Mem.not_mem.mp h₁).right h₂
    case true =>
      have := List.Mem.not_mem.mp h₁
      cases h₂
      case head => exact this.left rfl
      case tail h => exact ih this.right h

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
  induction lst
    <;> simp only [ List.splitFirst, reduceCtorEq, List.nil_eq,
                    List.append_eq_nil_iff, and_false, imp_self, implies_true ]
  intro res₁ res₂ h₁
  case cons x xs ih =>
    cases decEq x y
    case isFalse neq =>
      simp [neq] at h₁
      split at h₁ <;> simp at *
      next r₁ r₂ heq =>
        have := ih r₁ r₂ heq
        rw [←h₁.right, ←h₁.left, this, List.cons_append]
    case isTrue eq =>
      simp [eq] at h₁
      simp only [h₁, List.nil_append, List.cons.injEq, and_true]
      exact eq

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

-- def List.first_common [DecidableEq α]
    -- (l₁ l₂ : List α)
    -- (h : ¬List.Disjoint l₁ l₂)
    -- : (x : α) ×' x ∈ l₁ ∧ x ∈ l₂ := by
  -- induction l₁
  -- case nil => have := List.disjoint_nil_left l₂; contradiction
  -- case cons n ns ih =>
    -- if is_in : n ∈ l₂ then exact ⟨n, And.intro (by simp) is_in⟩ else
      -- have := Iff.subst List.disjoint_cons_left h
      -- simp at this
      -- let ⟨x, hres⟩ := ih (this is_in)
      -- exact ⟨x, And.intro (List.mem_cons_of_mem n hres.left) hres.right⟩

-- probs a better way to write this
-- theorem List.disjoint_reverse_left {l₁ l₂ : List α}
--     : List.Disjoint l₁ l₂ ↔ List.Disjoint l₁.reverse l₂ := by
--   apply Iff.intro <;> intro h₁ a h₂ <;> rw [Disjoint] at * <;> apply h₁
--   . exact List.mem_reverse |>.mp h₂
--   . exact List.mem_reverse |>.mpr h₂

-- theorem List.disjoint_reverse_right {l₁ l₂ : List α}
--     : List.Disjoint l₁ l₂ ↔ List.Disjoint l₁ l₂.reverse := by
--   apply Iff.intro <;> intro h₁ a h₂ h₃ <;> rw [Disjoint] at * <;> apply h₁ h₂
--   . exact List.mem_reverse |>.mp h₃
--   . exact List.mem_reverse |>.mpr h₃

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
