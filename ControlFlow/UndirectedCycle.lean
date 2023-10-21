import ControlFlow.Reachable
import ControlFlow.Connected
import ControlFlow.Graphs.DAG

namespace ControlFlow.UndirectedGraph

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

@[reducible, simp] def Cyclic {g : Graph α} (_ug : UndirectedGraph g) : Prop :=
  ∃ v, ∃ ps, Path.Undirected g v v ps

@[reducible, simp] def Acyclic {g : Graph α} (_ug : UndirectedGraph g) : Prop :=
  ∀ v, ¬∃ ps, Path.Undirected g v v ps

@[simp] theorem Acyclic.iff_not_cyclic {g : Graph α} (ug : UndirectedGraph g)
  : Acyclic ug ↔ ¬Cyclic ug := by simp

@[simp] theorem Cyclic.iff_not_acyclic {g : Graph α} (ug : UndirectedGraph g)
  : Cyclic ug ↔ ¬Acyclic ug := by simp

namespace Acyclic

@[simp] theorem add_edge_flip_iff {g : Graph α} (ug : UndirectedGraph g)
    {e : Edge α}
    : Acyclic (add_edge ug e.flip)
    ↔ Acyclic (add_edge ug e) := by
  apply Iff.intro <;> (
    intro acyclic v eps; apply acyclic v
    exact Exists.imp (fun _ => Path.Undirected.add_edge_flip_iff.mp) eps
  )

theorem add_edge_finish {g : Graph α}
    {ug : UndirectedGraph g}
    (acyclic : Acyclic ug)
    (e : Edge α)
    (u_not_in : ¬Digraph.has_vertex g e.start)
    (neq : e.start ≠ e.finish)
    : Acyclic (add_edge ug e) := by
  intro w
  have h := acyclic w
  have := Path.Undirected.add_edge_new_start_no_cycle u_not_in neq
  if eq : e.start = w then rw [←eq]; exact this else
    simp at h
    intro h'
    apply Exists.elim h'; intro a upath
    exact Path.Undirected.add_edge_new_start_pres ug u_not_in upath
      (neq_symm eq) (neq_symm eq) |> h a

theorem add_edge_start {g : Graph α}
    {ug : UndirectedGraph g}
    (acyclic : Acyclic ug)
    (e : Edge α)
    (u_not_in : ¬Digraph.has_vertex g e.finish)
    (neq : e.start ≠ e.finish)
    : Acyclic (add_edge ug e) :=
  add_edge_finish acyclic e.flip u_not_in (neq_symm neq)
    |> (add_edge_flip_iff ug).mp

instance {g : Graph α} {e : Edge α} {ug : UndirectedGraph g}
    : Coe (Acyclic (add_edge ug e.flip))
          (Acyclic (add_edge ug e)) :=
  ⟨(add_edge_flip_iff ug).mp⟩
