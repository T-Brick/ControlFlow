import ControlFlow.Path

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

@[reducible, simp] def Digraph.Cyclic [Digraph α Graph] (g : Graph α) : Prop :=
  ∃ v, ∃ ps, Path g v v ps

@[reducible, simp] def Digraph.Acyclic [Digraph α Graph] (g : Graph α) : Prop :=
  ∀ v, ¬∃ ps, Path g v v ps

@[reducible, simp] abbrev DAG : (g : Graph α) → Prop := Digraph.Acyclic

@[simp] theorem Digraph.Acyclic.iff_not_cyclic {g : Graph α}
    : Acyclic g ↔ ¬Cyclic g := by simp

@[simp] theorem Digraph.Cyclic.iff_not_acyclic {g : Graph α}
    : Cyclic g ↔ ¬Acyclic g := by simp

namespace Path

theorem Reachable.antisymm
    {g : Graph α} (dag : DAG g) {u v : Digraph.Vertices g}
    (r₁ : Path.Reachable g u v) (r₂ : Path.Reachable g v u) : u = v := by
  have u_in := u.property
  cases r₁
  case refl => rfl
  case path ps₁ path₁ =>
    cases r₂
    case refl => rfl
    case path ps₂ path₂ => next u v =>
      simp at *
      apply Exists.elim (merge path₁ path₂); intro ps h₁
      have := dag u ps h₁
      contradiction

instance {g : Graph α} (dag : DAG g) : PartialOrder (Reachable.Vertices g) where
  le_antisymm u v := Reachable.antisymm dag (u := u) (v := v)

end Path

namespace Digraph.Acyclic
