import ControlFlow.CFG

namespace ControlFlow

open CFG

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

/-
  maybe we should make a specific graph with an entry node?
 -/
structure Dom (g : Graph α) (e v₁ v₂ : α) : Prop where
  fst_in_graph : g |= v₁
  snd_in_graph : g |= v₂
  dom : (∀ ps, (g |= ps : e -> v₂) → v₁ ∈ ps)

structure Dom.Strict (g : Graph α) (e v₁ v₂ : α) extends Dom g e v₁ v₂ : Prop where
  sdom : (∀ ps, (g |= ps : e -> v₂) → v₁ ≠ v₂)

/- v is the immediate dominator of w if
    v ≫ w and every other dominator (u) of w dominates v as well
-/
structure Dom.Immediate (g : Graph α) (e v w : α) extends Dom.Strict g e v w : Prop where
  others : ∀ u, Dom.Strict g e u w → Dom.Strict g e u v

-- maybe make cursed notation local
notation:50 g:51 "(" e:51 ") |= " v₁:51 " ≫= " v₂:51 => Dom g e v₁ v₂
notation:50 g:51 "(" e:51 ") |= " v₁:51 " ≫ " v₂:51  => Dom.Strict g e v₁ v₂

namespace Dom

def ofCFG (cfg : CFG α Graph)           := Dom cfg.digraph cfg.start
def Strict.ofCFG (cfg : CFG α Graph)    := Strict cfg.digraph cfg.start
def Immediate.ofCFG (cfg : CFG α Graph) := Immediate cfg.digraph cfg.start

theorem refl {g : Graph α} (e v : α) (hv : g |= v) : g(e) |= v ≫= v :=
  ⟨hv, hv, fun _ps path => Path.finish_in_pathlist path⟩

-- hehe
theorem trans {g : Graph α} {e v₁ v₂ v₃ : α}
    (d₁ : g(e) |= v₁ ≫= v₂)
    (d₂ : g(e) |= v₂ ≫= v₃)
    : g(e) |= v₁ ≫= v₃ := by
  have f₁ := d₁.dom
  have f₂ := d₂.dom
  cases decEq v₂ v₃
  case isTrue eq => rw [eq] at f₁; exact ⟨d₁.fst_in_graph, d₂.snd_in_graph, f₁⟩
  case isFalse neq =>
    exact ⟨d₁.fst_in_graph, d₂.snd_in_graph, fun ps₃ path₃ =>
      have p₂ := f₂ ps₃ path₃
      have splits := Path.split p₂ neq path₃
      Exists.elim splits (fun ps₁ splits' =>
        Exists.elim splits' (fun ps₂ h => by
          have := f₁ ps₁ h.right.right.left
          rw [h.right.left]; exact List.mem_append_right ps₂ this
        )
      )
    ⟩

nonrec theorem Strict.trans {g : Graph α} {e v₁ v₂ v₃ : α}
    (d₁ : g(e) |= v₁ ≫ v₂)
    (d₂ : g(e) |= v₂ ≫ v₃)
    : g(e) |= v₁ ≫ v₃ := by
  exact ⟨trans d₁.toDom d₂.toDom, fun ps₃ path₃ =>
    have split := Path.split (d₂.dom ps₃ path₃) (d₂.sdom ps₃ path₃) path₃
    Exists.elim split (fun ps₁ split' =>
      Exists.elim split' (fun ps₂ h => by
        intro h₃
        simp [h₃] at *
        apply List.disjoint_left.mp h.left (d₁.dom ps₁ h.right.right.left)
        exact Path.finish_in_pathlist h.right.right.right
      )
    )
  ⟩

-- Antisymmetry only holds if the nodes are reachable from the entry point
def antisymm {g : Graph α} {e v₁ v₂ : α}
    (path₁ : g |= ps : e -> v₁)
    (d₁ : g(e) |= v₂ ≫= v₁)
    (d₂ : g(e) |= v₁ ≫= v₂)
    : v₁ = v₂ := by
  cases decEq v₁ v₂
  case isFalse neq =>
    have path₂ := Path.split (d₁.dom ps path₁) (neq_symm neq) path₁
    apply Exists.elim path₂; intro ps₁ path₂'
    apply Exists.elim path₂'; intro ps₂ h₁
    have h₂ := d₂.dom ps₁ h₁.right.right.left
    have h₃ := Path.finish_in_pathlist h₁.right.right.right
    have := List.disjoint_left.mp h₁.left h₂ h₃
    contradiction
  case isTrue eq => exact eq

theorem cfg_antisym {cfg : CFG α Graph} {v₁ v₂ : α}
    (d₁ : cfg.digraph(cfg.start) |= v₂ ≫= v₁)
    (d₂ : cfg.digraph(cfg.start) |= v₁ ≫= v₂)
    : v₁ = v₂ := by
  have := cfg.reachable v₁
    (Digraph.toVertices_has_vertex cfg.digraph v₁ |>.mpr d₁.snd_in_graph)
  apply Or.elim this <;> intro h₁
  . have := cfg.reachable v₂
      (Digraph.toVertices_has_vertex cfg.digraph v₂ |>.mpr d₂.snd_in_graph)
    apply Or.elim this <;> intro h₂
    . simp [h₁, h₂]
    . exact Exists.elim h₂ (fun ps path => antisymm path d₂ d₁ |> Eq.symm)
  . exact Exists.elim h₁ (fun ps path => antisymm path d₁ d₂)


-- does this require classical reasoning?
theorem ordering {g : Graph α} {e v₁ v₂ v₃ : α}
    (h₁ : g(e) |= v₁ ≫= v₃)
    (h₂ : g(e) |= v₂ ≫= v₃)
    : g(e) |= v₁ ≫= v₂ ∨ g(e) |= v₂ ≫= v₁ := by
  sorry

theorem unreachable {g : Graph α} {e v₂ : α}
    (h : ∀ps, ¬(g |= ps : e -> v₂))
    (hv₂ : g |= v₂)
    : ∀ v₁, g |= v₁ → g(e) |= v₁ ≫= v₂ := by
  intro v₁ hv₁
  exact ⟨hv₁, hv₂, fun ps path => by have := h ps path; contradiction⟩

nonrec theorem Strict.unreachable  {g : Graph α} {e v₂ : α}
    (h : ∀ps, ¬(g |= ps : e -> v₂))
    (hv₂ : g |= v₂)
    : ∀ v₁, g |= v₁ → g(e) |= v₁ ≫ v₂ := by
  intro v₁ hv₁
  exact ⟨unreachable h hv₂ v₁ hv₁, fun ps path => by have := h ps path; contradiction⟩

theorem Strict.acyclic {g : Graph α} {e v : α}
    (path : g |= ps : e -> v) : ¬(g(e) |= v ≫ v) := by
  intro d₁; exact (d₁.sdom ps path) rfl
