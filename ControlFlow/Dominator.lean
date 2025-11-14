import ControlFlow.Graphs.CFG
import Mathlib.Data.Finset.Basic

namespace ControlFlow

open Digraph
open CFG

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph]

structure Dom (g : Graph α) (e v₁ v₂ : Vertices g) : Prop where
  reach : Path.Reachable g e v₂
  in_path : (∀ ps, (g |= ps : e.val -> v₂.val) → v₁.val ∈ ps)

structure Dom.Strict (g : Graph α) (e v₁ v₂ : Vertices g) : Prop
    extends Dom g e v₁ v₂ where
  differ : v₁ ≠ v₂

/- v is the immediate dominator of w if
    v ≫ w and every other dominator (u) of w dominates v as well
-/
structure Dom.Immediate (g : Graph α) (e v w : Vertices g) : Prop
    extends Dom.Strict g e v w where
  others : ∀ u, Dom.Strict g e u w → Dom.Strict g e u v

-- maybe make cursed notation local
notation:50 g:51 "(" e:51 ")" " |= " v₁:51 " ≫= " v₂:51 => Dom g e v₁ v₂
notation:50 g:51 "(" e:51 ")" " |= " v₁:51 " ≫ " v₂:51  => Dom.Strict g e v₁ v₂
notation:50 g:51 "(" e:51 ")" " |= " v₁:51 " ⋙ " v₂:51  => Dom.Immediate g e v₁ v₂

namespace Dom

def ofCFG (cfg : CFG α Graph)           := Dom cfg.digraph cfg.start
def Strict.ofCFG (cfg : CFG α Graph)    := Strict cfg.digraph cfg.start
def Immediate.ofCFG (cfg : CFG α Graph) := Immediate cfg.digraph cfg.start

theorem refl {g : Graph α} (e v : Vertices g)
    (reach : Path.Reachable g e v)
    : g(e) |= v ≫= v :=
  ⟨reach, fun _ps path => Path.finish_in_pathlist path⟩

theorem cfg_refl  {cfg : CFG α Graph} (v : Vertices cfg.digraph)
    : cfg.digraph(cfg.start) |= v ≫= v :=
  cfg.reachable v |> Dom.refl cfg.start v

theorem Strict.not_refl {g : Graph α} {e v : Vertices g}
    : ¬(g(e) |= v ≫ v) := by
  intro d; exact d.differ rfl

theorem Strict.cfg_not_refl {cfg : CFG α Graph} {v : Vertices cfg.digraph}
    : ¬cfg.digraph(cfg.start) |= v ≫ v :=
  Strict.not_refl

theorem antisymm [DecidableEq α] {g : Graph α} {e v₁ v₂ : Vertices g}
    (d₁ : g(e) |= v₂ ≫= v₁)
    (d₂ : g(e) |= v₁ ≫= v₂)
    : v₁ = v₂ := by
  cases d₁.reach
  case refl =>
    cases d₂.reach
    case refl => rfl
    case path u v ps path₁ =>
      cases decEq u v
      case isFalse neq =>
        have path₂ := Path.split (d₂.in_path ps path₁) neq path₁
        apply Exists.elim path₂; intro ps₁ path₂'
        apply Exists.elim path₂'; intro ps₂ h₁
        have h₂ := Path.finish_in_pathlist h₁.right.right.left
        have h₃ := d₂.in_path ps₂ h₁.right.right.right
        have := List.disjoint_left.mp h₁.left h₂ h₃
        contradiction
      case isTrue eq => exact Subtype.mk_eq_mk.mpr eq
  case path u v ps path₁ =>
    cases decEq v v₂.val
    case isFalse neq =>
      have path₂ := Path.split (d₁.in_path ps path₁) (neq_symm neq) path₁
      apply Exists.elim path₂; intro ps₁ path₂'
      apply Exists.elim path₂'; intro ps₂ h₁
      have h₂ := d₂.in_path ps₁ h₁.right.right.left
      have h₃ := Path.finish_in_pathlist h₁.right.right.right
      have := List.disjoint_left.mp h₁.left h₂ h₃
      contradiction
    case isTrue eq => exact Subtype.mk_eq_mk.mpr eq

theorem cfg_antisymm [DecidableEq α]
    {cfg : CFG α Graph} {v₁ v₂ : Vertices cfg.digraph}
    (d₁ : cfg.digraph(cfg.start) |= v₂ ≫= v₁)
    (d₂ : cfg.digraph(cfg.start) |= v₁ ≫= v₂)
    : v₁ = v₂ :=
  antisymm d₁ d₂

-- hehe
theorem trans [DecidableEq α]
    {g : Graph α} {e : Vertices g} {v₁ v₂ v₃ : Vertices g}
    (d₁ : g(e) |= v₁ ≫= v₂)
    (d₂ : g(e) |= v₂ ≫= v₃)
    : g(e) |= v₁ ≫= v₃ := by
  have f₁ := d₁.in_path
  have f₂ := d₂.in_path
  cases decEq v₂.val v₃.val
  case isTrue eq => rw [eq] at f₁; exact ⟨d₂.reach, f₁⟩
  case isFalse neq =>
    exact ⟨d₂.reach, fun ps₃ path₃ =>
      have p₂ := f₂ ps₃ path₃
      have splits := Path.split p₂ neq path₃
      Exists.elim splits (fun ps₁ splits' =>
        Exists.elim splits' (fun ps₂ h => by
          have := f₁ ps₁ h.right.right.left
          rw [h.right.left]; exact List.mem_append_right ps₂ this
        )
      )
    ⟩

theorem cfg_trans [DecidableEq α]
    {cfg : CFG α Graph} {v₁ v₂ v₃ : Vertices cfg.digraph}
    (d₁ : cfg.digraph(cfg.start) |= v₁ ≫= v₂)
    (d₂ : cfg.digraph(cfg.start) |= v₂ ≫= v₃)
    : cfg.digraph(cfg.start) |= v₁ ≫= v₃ :=
  trans d₁ d₂

nonrec theorem Strict.trans [DecidableEq α]
    {g : Graph α} {e v₁ v₂ v₃ : Vertices g}
    (d₁ : g(e) |= v₁ ≫ v₂)
    (d₂ : g(e) |= v₂ ≫ v₃)
    : g(e) |= v₁ ≫ v₃ := by
  have d₃ := trans d₁.toDom d₂.toDom
  exact ⟨d₃, fun eq => by
    cases d₃.reach
    case refl =>
      simp [eq] at *
      have eq' := Dom.antisymm d₁.toDom d₂.toDom
      simp [eq'] at d₁
      exact Strict.not_refl d₁
    case path ps₃ path₃ =>
      have split := Path.split (d₂.in_path ps₃ path₃)
        (Iff.subst Subtype.mk_eq_mk d₂.differ) path₃
      apply Exists.elim split; intro ps₁ split'
      apply Exists.elim split'; intro ps₂ h
      simp [eq] at *
      apply List.disjoint_left.mp h.left (d₁.in_path ps₁ h.right.right.left)
      exact Path.finish_in_pathlist h.right.right.right
  ⟩

theorem Strict.cfg_trans [DecidableEq α]
    {cfg : CFG α Graph} {v₁ v₂ v₃ : Vertices cfg.digraph}
    (d₁ : cfg.digraph(cfg.start) |= v₁ ≫ v₂)
    (d₂ : cfg.digraph(cfg.start) |= v₂ ≫ v₃)
    : cfg.digraph(cfg.start) |= v₁ ≫ v₃ :=
  Strict.trans d₁ d₂

theorem total {g : Graph α} {e : Vertices g} {v₁ v₂ v₃ : Vertices g}
    (h₁ : g(e) |= v₁ ≫= v₃)
    (h₂ : g(e) |= v₂ ≫= v₃)
    : g(e) |= v₁ ≫= v₂ ∨ g(e) |= v₂ ≫= v₁ := by
  sorry

theorem dom_iff_sdom_not_sdom [DecidableEq α]
    {g : Graph α} {e v₁ v₂ : Vertices g}
    : g(e) |= v₁ ≫ v₂ ↔ g(e) |= v₁ ≫= v₂ ∧ ¬g(e) |= v₂ ≫= v₁ := by
  apply Iff.intro
  . intro d₁
    apply And.intro (d₁.toDom)
    intro d₂
    exact d₁.differ (antisymm d₁.toDom d₂ |> Eq.symm)
  . intro h₁
    apply Strict.mk h₁.left
    intro h₂
    simp [h₂] at h₁

instance {cfg : CFG α Graph} : LE (Vertices cfg.digraph) := ⟨Dom.ofCFG cfg⟩
instance {cfg : CFG α Graph} : LT (Vertices cfg.digraph) := ⟨Dom.Strict.ofCFG cfg⟩
instance [DecidableEq α] {cfg : CFG α Graph} : Preorder (Vertices cfg.digraph) where
  le_refl := cfg_refl
  le_trans _ _ _ d₁ d₂ := cfg_trans d₁ d₂
  lt_iff_le_not_ge _ _ := dom_iff_sdom_not_sdom
instance [DecidableEq α] {cfg : CFG α Graph} : PartialOrder (Vertices cfg.digraph) where
  le_antisymm _ _ d₁ d₂ := cfg_antisymm (cfg := cfg) d₂ d₁

-- Any algorithm which computes dominance sets should obey these properties
class Algorithm [Digraph α Graph] where
  sdom : (cfg : CFG α Graph) → Vertices cfg.digraph → Set (Vertices cfg.digraph)
  dom : (cfg : CFG α Graph) → Vertices cfg.digraph → Set (Vertices cfg.digraph) :=
    fun g v => {v} ∪ sdom g v
  entry_no_sdom : ∀ cfg : CFG α Graph, sdom cfg cfg.start = ∅
  sound    : ∀ cfg : CFG α Graph, ∀ res v,
              res ∈ sdom cfg v → cfg.digraph(cfg.start) |= res ≫ v
  complete : ∀ cfg : CFG α Graph, ∀ res v,
              cfg.digraph(cfg.start) |= res ≫ v → res ∈ sdom cfg v

namespace Algorithm

def Dom (α : Type) := Option (Set α)

instance [DecidableEq (Set α)] : DecidableEq (Dom α) :=
  fun a b => by
    cases a <;> cases b
    case none.none => exact .isTrue rfl
    case none.some bv => exact .isFalse (by simp only [reduceCtorEq, not_false_eq_true])
    case some.none av => exact .isFalse (by simp only [reduceCtorEq, not_false_eq_true])
    case some.some av bv =>
      simp only [Option.some_inj (a := av)]
      exact decEq av bv


inductive Dom.LE : Dom α → Dom α → Prop where
| refl : Dom.LE x x
| bot : Dom.LE .none x
| subset : y ⊆ x → Dom.LE (.some x) (.some y)

instance : Top (Dom α) where
  top := .some ∅
instance : Bot (Dom α) where
  bot := .none

@[refl]
theorem Dom.LE.reflexive (a : Dom α) : Dom.LE a a := .refl

@[trans]
theorem Dom.LE.trans (h₁ : Dom.LE a b) (h₂ : Dom.LE b c) : Dom.LE a c := by
  cases h₁
  case refl => exact h₂
  case bot => exact .bot
  case subset x y h₃ =>
    cases h₂
    case refl => exact .subset h₃
    case subset z h₄ => exact Dom.LE.subset (Set.Subset.trans h₄ h₃)

theorem Dom.LE.antisymm (h₁ : Dom.LE a b) (h₂ : Dom.LE b a) : a = b := by
  cases h₁
  case refl => rfl
  case bot => cases h₂ <;> rfl
  case subset x y h₁ =>
    cases h₂
    case refl => rfl
    case subset h₂ => exact Option.some_inj.mpr (Set.Subset.antisymm h₂ h₁)

/-
 - Defined as set intersection lifted into an option, where `none` is the
 - bottom, i.e. an identity for `join`
 -/
def Dom.join (l r : Dom α) : Dom α :=
  match l with
  | .none => r
  | .some lv =>
    match r with
    | .none => l
    | .some rv => .some (lv ∩ rv)

theorem Dom.LE.join_left (x y : Dom α) : Dom.LE x (x.join y) := by
  cases x
  case none => exact .bot
  case some xv =>
    cases y
    case none => exact .refl
    case some yv => exact Dom.LE.subset Set.inter_subset_left

theorem Dom.LE.join_right (x y : Dom α) : Dom.LE y (x.join y) := by
  cases x
  case none => exact .refl
  case some xv =>
    cases y
    case none => exact .bot
    case some yv => exact Dom.LE.subset Set.inter_subset_right

theorem Dom.LE.join_lub
    (h₁ : Dom.LE x z)
    (h₂ : Dom.LE y z)
    : Dom.LE (x.join y) z := by
  cases x
  case none => exact h₂
  case some xv =>
    cases y
    case none => exact h₁
    case some yv =>
      cases z
      case none => cases h₁
      case some zv =>
        apply Dom.LE.subset
        apply Set.subset_inter_iff.mpr
        apply And.intro
        . cases h₁
          . rfl
          . assumption
        . cases h₂
          . rfl
          . assumption

instance : Lattice (Dom α) where
  sup := Dom.join
  le := Dom.LE
  le_refl := Dom.LE.reflexive
  le_trans := fun a b c => Dom.LE.trans
  le_antisymm := fun a b => Dom.LE.antisymm
  le_sup_left := Dom.LE.join_left
  le_sup_right := Dom.LE.join_right
  sup_le := fun a b c => Dom.LE.join_lub
  inf := sorry
  inf_le_left := sorry
  inf_le_right := sorry
  le_inf := sorry

def Dom.flow (v : α) (input : Dom α) : Dom α :=
  match input with
  | .none => .none
  | .some input => .some (input.insert v)

theorem Dom.flow_monotonic (v : α) : Monotone (Dom.flow v) := by
  intro a b h₁
  rw [flow.eq_def, flow.eq_def]
  cases a <;> cases b <;> simp
  case none.some bv => exact .bot
  case some.none av => contradiction
  case some.some av bv =>
    apply Dom.LE.subset
    cases h₁
    case a.refl => rfl
    case a.subset h₁ => exact Set.insert_subset_insert h₁

def compute [DecidableEq α] [DecidableEq (Set α)] (cfg : CFG α Graph) : Unit :=
  let res := Dataflow.kildall cfg Dom.flow ⊤ .forward .may Dom.flow_monotonic
  sorry

end Algorithm
