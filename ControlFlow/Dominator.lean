import ControlFlow.CFG

namespace ControlFlow

open Digraph
open CFG

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

/-
  maybe we should make a specific graph with an entry node?
 -/
structure Dom (g : Graph α) (e : Vertices g) (v₁ v₂ : α) : Prop where
  reach : Path.Reachable g e.val v₂
  in_path : (∀ ps, (g |= ps : e.val -> v₂) → v₁ ∈ ps)

structure Dom.Strict (g : Graph α) (e : Vertices g) (v₁ v₂ : α)
    extends Dom g e v₁ v₂ : Prop where
  differ : v₁ ≠ v₂

/- v is the immediate dominator of w if
    v ≫ w and every other dominator (u) of w dominates v as well
-/
structure Dom.Immediate (g : Graph α) (e : Vertices g) (v w : α)
    extends Dom.Strict g e v w : Prop where
  others : ∀ u, Dom.Strict g e u w → Dom.Strict g e u v

-- maybe make cursed notation local
notation:50 g:51 "(" e:51 ") |= " v₁:51 " ≫= " v₂:51 => Dom g e v₁ v₂
notation:50 g:51 "(" e:51 ") |= " v₁:51 " ≫ " v₂:51  => Dom.Strict g e v₁ v₂

namespace Dom

def ofCFG (cfg : CFG α Graph)           := Dom cfg.digraph cfg.start
def Strict.ofCFG (cfg : CFG α Graph)    := Strict cfg.digraph cfg.start
def Immediate.ofCFG (cfg : CFG α Graph) := Immediate cfg.digraph cfg.start

theorem entry_in_graph {g : Graph α} {e : Vertices g} {v₁ v₂ : α}
    (_ : Dom g e v₁ v₂) : g |= e.val :=
  e.property

theorem snd_in_graph {g : Graph α} {e : Vertices g} {v₁ v₂ : α}
    (self : Dom g e v₁ v₂) : g |= v₂ := by
  cases self.reach
  case refl => exact self.entry_in_graph
  case path _ path => exact Path.finish_in_graph path

theorem snd_in_graph' {g : Graph α} {e : Vertices g} {v₁ v₂ : α}
    (self : Dom g e v₁ v₂) : v₂ ∈ Digraph.toVertices g := by
  exact Digraph.toVertices_has_vertex g v₂ |>.mpr self.snd_in_graph


theorem refl {g : Graph α} (e : Vertices g) (v : α)
    (reach : Path.Reachable g e.val v)
    : g(e) |= v ≫= v :=
  ⟨reach, fun _ps path => Path.finish_in_pathlist path⟩

theorem cfg_refl  {cfg : CFG α Graph} (v : α) (h : cfg.digraph |= v)
    : cfg.digraph(cfg.start) |= v ≫= v :=
  cfg.reachable v (Digraph.toVertices_has_vertex cfg.digraph v |>.mpr h)
  |> Dom.refl cfg.start v

theorem Strict.not_refl {g : Graph α} {e : Vertices g} {v : α}
    : ¬(g(e) |= v ≫ v) := by
  intro d; exact d.differ rfl

theorem Strict.cfg_not_refl {cfg : CFG α Graph} {v : α}
    : ¬cfg.digraph(cfg.start) |= v ≫ v :=
  Strict.not_refl

theorem antisymm {g : Graph α} {e : Vertices g} {v₁ v₂ : α}
    (d₁ : g(e) |= v₂ ≫= v₁)
    (d₂ : g(e) |= v₁ ≫= v₂)
    : v₁ = v₂ := by
  cases d₁.reach
  case refl =>
    cases d₂.reach
    case refl => rfl
    case path ps path₁ =>
      cases decEq e.val v₂
      case isFalse neq =>
        have path₂ := Path.split (d₂.in_path ps path₁) neq path₁
        apply Exists.elim path₂; intro ps₁ path₂'
        apply Exists.elim path₂'; intro ps₂ h₁
        have h₂ := Path.finish_in_pathlist h₁.right.right.left
        have h₃ := d₂.in_path ps₂ h₁.right.right.right
        have := List.disjoint_left.mp h₁.left h₂ h₃
        contradiction
      case isTrue eq => exact eq
  case path ps path₁ =>
    cases decEq v₁ v₂
    case isFalse neq =>
      have path₂ := Path.split (d₁.in_path ps path₁) (neq_symm neq) path₁
      apply Exists.elim path₂; intro ps₁ path₂'
      apply Exists.elim path₂'; intro ps₂ h₁
      have h₂ := d₂.in_path ps₁ h₁.right.right.left
      have h₃ := Path.finish_in_pathlist h₁.right.right.right
      have := List.disjoint_left.mp h₁.left h₂ h₃
      contradiction
    case isTrue eq => exact eq

theorem cfg_antisymm {cfg : CFG α Graph} {v₁ v₂ : α}
    (d₁ : cfg.digraph(cfg.start) |= v₂ ≫= v₁)
    (d₂ : cfg.digraph(cfg.start) |= v₁ ≫= v₂)
    : v₁ = v₂ :=
  antisymm d₁ d₂

-- hehe
theorem trans {g : Graph α} {e : Vertices g} {v₁ v₂ v₃ : α}
    (d₁ : g(e) |= v₁ ≫= v₂)
    (d₂ : g(e) |= v₂ ≫= v₃)
    : g(e) |= v₁ ≫= v₃ := by
  have f₁ := d₁.in_path
  have f₂ := d₂.in_path
  cases decEq v₂ v₃
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

theorem cfg_trans {cfg : CFG α Graph} {v₁ v₂ v₃ : α}
    (d₁ : cfg.digraph(cfg.start) |= v₁ ≫= v₂)
    (d₂ : cfg.digraph(cfg.start) |= v₂ ≫= v₃)
    : cfg.digraph(cfg.start) |= v₁ ≫= v₃ :=
  trans d₁ d₂

nonrec theorem Strict.trans {g : Graph α} {e : Vertices g} {v₁ v₂ v₃ : α}
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
      have split := Path.split (d₂.in_path ps₃ path₃) d₂.differ path₃
      apply Exists.elim split; intro ps₁ split'
      apply Exists.elim split'; intro ps₂ h
      simp [eq] at *
      apply List.disjoint_left.mp h.left (d₁.in_path ps₁ h.right.right.left)
      exact Path.finish_in_pathlist h.right.right.right
  ⟩

theorem Strict.cfg_trans {cfg : CFG α Graph} {v₁ v₂ v₃ : α}
    (d₁ : cfg.digraph(cfg.start) |= v₁ ≫ v₂)
    (d₂ : cfg.digraph(cfg.start) |= v₂ ≫ v₃)
    : cfg.digraph(cfg.start) |= v₁ ≫ v₃ :=
  Strict.trans d₁ d₂

-- does this require classical reasoning?
theorem total {g : Graph α} {e : Vertices g} {v₁ v₂ v₃ : α}
    (h₁ : g(e) |= v₁ ≫= v₃)
    (h₂ : g(e) |= v₂ ≫= v₃)
    : g(e) |= v₁ ≫= v₂ ∨ g(e) |= v₂ ≫= v₁ := by
  sorry

theorem dom_iff_sdom_not_sdom {g : Graph α} {e : Vertices g} {v₁ v₂ : α}
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

instance {cfg : CFG α Graph} : LE (Vertices cfg.digraph) where
  le x y := Dom.ofCFG cfg x.val y.val
instance {cfg : CFG α Graph} : LT (Vertices cfg.digraph) where
  lt x y := Dom.Strict.ofCFG cfg x.val y.val
instance {cfg : CFG α Graph} : Preorder (Vertices cfg.digraph) where
  le_refl v := cfg_refl v.val v.property
  le_trans _ _ _ d₁ d₂ := cfg_trans d₁ d₂
  lt_iff_le_not_le _ _ := dom_iff_sdom_not_sdom
instance {cfg : CFG α Graph} : PartialOrder (Vertices cfg.digraph) where
  le_antisymm _ _ d₁ d₂ := cfg_antisymm (cfg := cfg) d₂ d₁ |> Subtype.eq

-- Any algorithm which computes dominance sets should obey these properties
-- todo maybe actually use sets
class Algorithm [Digraph α Graph] where
  sdom : Graph α → α → List α
  dom : Graph α → α → List α := fun g v => [v] ++ sdom g v
  entry_no_sdom : ∀ cfg : CFG α Graph, sdom cfg.digraph cfg.start.val = []
  sound    : ∀ cfg : CFG α Graph, ∀ res,
              res ∈ sdom g v → cfg.digraph(cfg.start) |= res ≫ v
  complete : ∀ cfg : CFG α Graph, ∀ res,
              cfg.digraph(cfg.start) |= res ≫ v → res ∈ sdom g v

