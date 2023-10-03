import ControlFlow.Path

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

class Digraph.Acyclic [Digraph α Graph] (g : Graph α) where
  acyclic : ∀ v, g |= v → ¬∃ ps, Path g v v ps

abbrev DAG : (g : Graph α) → Type := Digraph.Acyclic

namespace Path

theorem Reachable.antisymm
    {g : Graph α} [dag : DAG g] {u v : Digraph.Vertices g}
    (r₁ : Path.Reachable g u v) (r₂ : Path.Reachable g v u) : u = v := by
  have acyclic := dag.acyclic
  have u_in := u.property
  have v_in := v.property
  cases r₁
  case refl => rfl
  case path ps₁ path₁ =>
    cases r₂
    case refl => rfl
    case path ps₂ path₂ => next u v =>
      simp at *
      apply Exists.elim (merge path₁ path₂); intro ps h₁
      have := acyclic u u_in ps h₁
      contradiction

instance {g : Graph α} [DAG g] : PartialOrder (Reachable.Vertices g) where
  le_antisymm u v := Reachable.antisymm (u := u) (v := v)

end Path

namespace Digraph.Acyclic
