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

open Digraph

namespace Cyclic

@[simp] theorem add_edge_flip_iff {g : Graph α} (ug : UndirectedGraph g)
    {e : Edge α} : Cyclic (add_edge ug e.flip) ↔ Cyclic (add_edge ug e) := by
  apply Iff.intro <;> (
    intro cyclic; exact cyclic.imp (fun _ =>
      Exists.imp (fun _ => Path.Undirected.add_edge_flip_iff.mp)
    )
  )

theorem add_edge {g : Graph α} {ug : UndirectedGraph g} (cyclic : Cyclic ug)
    (e : Edge α) : Cyclic (add_edge ug e) :=
  cyclic.imp (fun _ =>
    Exists.imp (fun _ => Path.Undirected.add_edge_pres e)
  )

theorem merge {g₁ g₂ : Graph α}
    (ug₁ : UndirectedGraph g₁)
    (ug₂ : UndirectedGraph g₂)
    (either_cyclic : Cyclic ug₁ ∨ Cyclic ug₂)
    : Cyclic (UndirectedGraph.merge ug₁ ug₂) := by
  apply Or.elim either_cyclic <;> (
    intro cyclic
    exact cyclic.imp (fun _ =>
      Exists.imp (fun _ upath => by
        try exact Path.Undirected.graph_merge_pres ug₁ ug₂ (Or.inl upath)
        try exact Path.Undirected.graph_merge_pres ug₁ ug₂ (Or.inr upath)
      )
    )
  )


instance {g : Graph α} {e : Edge α} {ug : UndirectedGraph g}
    : Coe (Cyclic (UndirectedGraph.add_edge ug e.flip))
          (Cyclic (UndirectedGraph.add_edge ug e)) :=
  ⟨(add_edge_flip_iff ug).mp⟩

end Cyclic

namespace Acyclic

theorem empty : Acyclic (UndirectedGraph.empty : UndirectedGraph (_ : Graph α))
  := by simp; intro u ps; exact Path.Undirected.empty

theorem trivial (w : α)
    : Acyclic (UndirectedGraph.trivial w : UndirectedGraph (_ : Graph α)) := by
  simp; intro _ _ upath; exact Path.Undirected.trivial w upath

@[simp] theorem add_edge_flip_iff {g : Graph α} (ug : UndirectedGraph g)
    {e : Edge α} : Acyclic (add_edge ug e.flip) ↔ Acyclic (add_edge ug e) := by
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

theorem merge_disjoint {g₁ g₂ : Graph α}
    {ug₁ : UndirectedGraph g₁}
    {ug₂ : UndirectedGraph g₂}
    (acyclic₁ : Acyclic ug₁)
    (acyclic₂ : Acyclic ug₂)
    (disjoint_left : ∀ v, has_vertex g₁ v → ¬has_vertex g₂ v)
    (disjoint_right : ∀ v, has_vertex g₂ v → ¬has_vertex g₁ v)
    (disjoint_edge : ∀ u v, has_vertex g₁ u ∧ has_vertex g₂ v
                          → ⟨u, v⟩ ∉ Digraph.merge g₁ g₂)
    : Acyclic (UndirectedGraph.merge ug₁ ug₂) := by
  intro v eps
  apply Exists.elim eps; intro ps upath
  apply Or.elim (Path.finish_in_graph upath.path |> merge_has_vertex.mp)
      <;> intro v_in
  . have v_not_in := disjoint_left v v_in
    have := Path.Undirected.graph_merge_pathlist_left ug₁ upath v_not_in
      (fun x h => by
        have := Path.in_pathlist_in_graph upath.path x h |> merge_has_vertex.mp
        apply Or.elim this <;> intro x_in
        . exact And.intro x_in (disjoint_left x x_in)
        . have := Path.graph_merge_cross upath.path v_in
            (Exists.intro x (And.intro h x_in))
          apply Exists.elim this; intro w₁ this
          apply Exists.elim this; intro w₂ h
          have :=
            disjoint_edge w₁ w₂ (And.intro h.left h.right.left) h.right.right
          contradiction
      )
    exact acyclic₁ v (Exists.intro ps this)
  . have v_not_in := disjoint_right v v_in
    have := Path.Undirected.graph_merge_pathlist_right ug₂ upath v_not_in
      (fun x h => by
        have := Path.in_pathlist_in_graph upath.path x h |> merge_has_vertex.mp
        apply Or.elim this <;> intro x_in
        . have := Path.graph_merge_cross' upath.path v_in
            (Exists.intro x (And.intro h x_in))
          apply Exists.elim this; intro w₁ this
          apply Exists.elim this; intro w₂ h
          have w₁w₂_edge :=
            (UndirectedGraph.merge ug₁ ug₂).undirected w₁ w₂
            |>.mpr h.right.right
          have :=
            disjoint_edge w₁ w₂ (And.intro h.left h.right.left) w₁w₂_edge
          contradiction
        . exact And.intro (disjoint_right x x_in) x_in
      )
    exact acyclic₂ v (Exists.intro ps this)


instance {g : Graph α} {e : Edge α} {ug : UndirectedGraph g}
    : Coe (Acyclic (add_edge ug e.flip))
          (Acyclic (add_edge ug e)) :=
  ⟨(add_edge_flip_iff ug).mp⟩
