import ControlFlow.Path

/- todo: reorganise this file ? -/
namespace ControlFlow.Path

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

/- A directed path is restricted so that only the starting node can
    be revisited (to allow for a path to form a cycle). For our definition of
    undirected graph this is a problem since we can have paths: `u -> v -> u`
    which used the same (undirected) edge twice.
 -/
structure Undirected (g : Graph α) (u v : α) (ps : List α) : Prop where
  path : Path g u v ps
  undirected : UndirectedGraph g
  pathlist_start : ∀ w ps', ps ≠ ps' ++ [u, w]

instance {g : Graph α} : Coe (Undirected g u v ps) (Path g u v ps) :=
  ⟨(·.path)⟩

abbrev UndirectedPath : (g : Graph α) → α → α → List α → Prop := Undirected


/- all acyclic paths are undirected -/
theorem Acyclic.toUndirected {g : Graph α} {u v : α} {ps : List α}
    (ug : UndirectedGraph g)
    (acyclic : Acyclic g u v ps)
    : Undirected g u v ps := by
  apply Undirected.mk (acyclic.path) ug
  intro w ps' ps_eq
  have u_not_in := acyclic.acyclic
  simp [ps_eq] at u_not_in


namespace Undirected
open Digraph
open UndirectedGraph

theorem empty : ¬Undirected (Digraph.empty : Graph α) u v ps := by
  intro upath; exact Path.empty upath.path

theorem trivial (w : α) : ¬Undirected (Digraph.trivial w : Graph α) u v ps := by
  intro upath; exact Path.trivial w upath.path

theorem cons {g : Graph α} {u v w x y: α} {ps : List α}
    (vw_in : ⟨v, w⟩ ∈ g)
    (upath : Undirected g u v (x::y::ps))
    (not_in_ps : w ∉ (x::y::ps))
    : Undirected g u w (w::x::y::ps) :=
  ⟨ .cons vw_in upath.path not_in_ps
  , upath.undirected
  , fun w' ps' eq => by
      cases ps' <;> simp at eq
      case cons z zs => exact (upath.pathlist_start w' zs) eq.right
  ⟩

theorem prior_path_undirected_cons {g : Graph α} {u v w₁ w₂ : α} {ps : List α}
    (upath : Undirected g u v (w₂::w₁::ps))
    : Undirected g u w₁ (w₁::ps) := by
  cases upath.path
  case cons v' h₁ path' h₂ =>
    have v'w₁_eq := finish_cons_eq path'
    rw [v'w₁_eq] at path' h₁
    have pathlist_start : ∀ (w : α) (ps' : List α), _ := by
      intro w' ps'
      have := upath.pathlist_start w' (v :: ps')
      simp at this
      exact this
    exact ⟨path', upath.undirected, pathlist_start⟩

theorem prior_path_undirected {g : Graph α} {u v w₂ : α} {ps : List α}
    (upath : Undirected g u v (w₂ :: ps))
    : ps ≠ [] → ∃ w₁, Undirected g u w₁ ps := by
  intro neq
  apply Exists.elim (List.exists_cons_of_ne_nil neq); intro w₁ h
  apply Exists.elim h; intro ps' h
  simp [h] at *
  exact Exists.intro w₁ (prior_path_undirected_cons upath)

theorem cycle_length {g : Graph α} {u v : α} {ps : List α}
    (upath : Undirected g u v ps)
    : u = v → ps.length ≠ 2 := by
  intro eq len; simp [eq] at upath
  cases ps; case nil => contradiction
  case cons x xs =>
    cases xs; case nil => simp [length] at len
    case cons y ys =>
      simp [List.length_cons, List.length_eq_zero] at len
      have neq := upath.pathlist_start y []
      simp [len] at neq
      exact neq (finish_cons_eq upath.path |>.symm)

theorem add_edge_new_start_from_must_use {g : Graph α} {u v : α}
    (u_not_in : ¬has_vertex g u)
    : ∀ w ps, Undirected (add_undirected_edge g ⟨u, v⟩) u w ps → v ∈ ps := by
  intro w ps up
  exact Path.add_undirected_edge_new_start_from_must_use u_not_in w ps up.path

theorem add_edge_new_start_from_must_use_last {g : Graph α} {u v : α}
    (u_not_in : ¬has_vertex g u)
    : ∀ w ps, (upath : Undirected (add_undirected_edge g ⟨u, v⟩) u w ps)
            → ps.getLast (pathlist_nonempty upath.path) = v := by
  intro w ps upath
  exact add_undirected_edge_new_start_from_must_use_last
    u_not_in w ps upath.path

theorem add_edge_new_start_from_singleton {g : Graph α} {u v : α}
    (u_not_in : ¬has_vertex g u)
    : ∀ ps, Undirected (add_undirected_edge g ⟨u, v⟩) u v ps → ps = [v] := by
  intro ps upath
  exact add_undirected_edge_new_start_from_singleton u_not_in ps upath.path

-- todo rewrite (call existing versions of this function)
theorem add_edge_new_start_to_no_more {g : Graph α} {u v w : α}
    {ps : List α}
    (u_not_in : ¬has_vertex g u)
    (upath :  Undirected (add_undirected_edge g ⟨u, v⟩) w u ps)
    : ∀ w', ¬(Undirected (add_undirected_edge g ⟨u, v⟩) w w' (w'::ps)) := by
  intro w' upath'
  have path := upath.path
  have path' := upath'.path
  if uv_eq : u = v then
    cases path
    case edge h₁ =>
      have h := first_pathlist_imp_edge [] path'
      have vw'_eq :=
        add_undirected_edge_new_start_antisymm g u u_not_in v w' (Or.inr h)
      simp only [vw'_eq, uv_eq] at *
      cases path'
      case cons h₂ => apply h₂; simp
    case cons v' ps'' path'' h₁ h₂ =>
      have vs_eq :=
        add_undirected_edge_new_start_antisymm g u u_not_in v v' (Or.inl h₁)
      simp [uv_eq, vs_eq] at h₂
      exact h₂ (finish_in_pathlist path'')
  else if vw_eq : v = w then
    rw [←vw_eq] at path path' upath upath'
    cases upath.path
    case edge h₁ =>
      have uw'_in := first_pathlist_imp_edge _ upath'.path
      have vw'_eq :=
        add_undirected_edge_new_start_antisymm g u u_not_in v w' (Or.inr uw'_in)
      have := upath'.pathlist_start u []
      simp [←vw'_eq] at this
    case cons v' ps'' path'' h₁ h₂ =>
      have uw'_in := first_pathlist_imp_edge _ upath'.path
      have vw'_eq :=
        add_undirected_edge_new_start_antisymm g u u_not_in v w' (Or.inr uw'_in)
      have vv'_eq :=
        add_undirected_edge_new_start_antisymm g u u_not_in v v' (Or.inl h₁)
      simp [←vv'_eq] at path''
      have v_in_ps'' := finish_in_pathlist path''
      simp [←vw'_eq] at upath'
      cases upath'.path
      case cons h => exact h (List.Mem.tail u v_in_ps'')
  else
    have vw_neq := vw_eq
    cases path
    case edge h =>
      exact add_undirected_edge_new_start_no_in_edge
        g u u_not_in v w uv_eq vw_neq h
    case cons w'' ps'' path'' h₁ h₂ =>
      have vw''_eq : v = w'' := by
        exact add_undirected_edge_new_start_antisymm g u u_not_in v w''
          (Or.inl h₁)
      rw [←vw''_eq] at path'' h₁
      have v_in_ps'' := finish_in_pathlist path''
      have uw'_in := first_pathlist_imp_edge ps'' path'
      have vw'_eq :=
        add_undirected_edge_new_start_antisymm g u u_not_in v w' (Or.inr uw'_in)
      rw [←vw'_eq] at path'
      apply Exists.elim (finish_cons_rest path'); intro ps₂'' h
      simp only [List.cons.injEq, true_and] at h
      simp [←h.left] at h
      exact h (Or.inr v_in_ps'')

theorem add_edge_new_start_no_cycle {g : Graph α} {u v : α}
    (u_not_in : ¬has_vertex g u)
    (neq : u ≠ v)
    : ¬∃ ps, Undirected (add_undirected_edge g ⟨u, v⟩) u u ps := by
  intro h₁; apply Exists.elim h₁; intro ps upath
  have :=
    add_undirected_edge_new_start_cycle_pathlist u_not_in neq ps upath.path
  exact upath.cycle_length rfl (by simp [this])

theorem add_edge_self_makes_cycle {g : Graph α} (ug : UndirectedGraph g) (u : α)
    : Undirected (add_undirected_edge g ⟨u, u⟩) u u [u] :=
  ⟨ Path.add_undirected_edge_self_makes_cycle g u
  , add_edge ug ⟨u, u⟩
  , by intro w ps' h; cases ps' <;> simp at h
  ⟩

@[simp] theorem add_edge_flip_iff {g : Graph α} {e : Edge α}
    {u v : α} {ps : List α}
    : Undirected (add_undirected_edge g e.flip) u v ps
    ↔ Undirected (add_undirected_edge g e) u v ps := by
  apply Iff.intro <;> (
    intro upath
    have path := upath.path
    simp [Path.add_undirected_edge_flip_iff] at path
    exact Undirected.mk path upath.undirected upath.pathlist_start
  )


/- Presevation across graph changes -/

theorem add_vertex_pres {g : Graph α} {u v : α} {ps : List α} (w : α)
    (upath : Undirected g u v ps)
    : Undirected (add_vertex g w) u v ps :=
  ⟨ upath.path, add_vertex upath.undirected w, upath.pathlist_start⟩

theorem add_edge_pres {g : Graph α} {u v : α} {ps : List α} (e : Edge α)
    (upath : Undirected g u v ps)
    : Undirected (add_undirected_edge g e) u v ps :=
  ⟨ upath.path, add_edge upath.undirected e, upath.pathlist_start⟩

theorem add_edge_new_start_pres {g : Graph α} {u v w₁ w₂ : α} {ps : List α}
    (ug : UndirectedGraph g) -- todo do we need this??
    (u_not_in : ¬has_vertex g u)
    (upath : Undirected (add_undirected_edge g ⟨u, v⟩) w₁ w₂ ps)
    (w₁u_neq : w₁ ≠ u)
    (w₂u_neq : w₂ ≠ u)
    : Undirected g w₁ w₂ ps := by
  induction upath.path
  case edge w₂ h =>
    apply Or.elim (add_undirected_edge_eq_or_in g ⟨w₁,w₂⟩ ⟨u,v⟩ h) <;> intro h₁
    . apply Or.elim h₁ <;> (simp; intro h₁ h₂; contradiction)
    . exact ⟨.edge h₁, ug, upath.pathlist_start⟩
  case cons cons v' ps' w h₁ path' h₂ ih =>
    apply Exists.elim (prior_path_undirected upath (pathlist_nonempty path'))
    intro w' upath'
    have wv'_eq : w' = v' :=
      pathlist_finish_antisymm upath'.path path'
    rw [wv'_eq] at upath'
    if eq : v' = u then
      rw [eq] at upath'
      have := add_edge_new_start_to_no_more u_not_in upath' w upath
      contradiction
    else
      have := add_undirected_edge_pres_edges g ⟨v', w⟩ ⟨u, v⟩
        (by simp; intro eq' _; exact eq eq')
        (by simp; intro _ eq'; exact w₂u_neq eq')
      exact ⟨.cons (this.mpr h₁) (ih upath' eq) h₂, ug, upath.pathlist_start⟩

theorem add_edge_not_use_start_pres {g : Graph α} {u v w₁ w₂ : α} {ps : List α}
    (ug : UndirectedGraph g) -- todo do we need this??
    (upath : Undirected (add_undirected_edge g ⟨u, v⟩) w₁ w₂ ps)
    (u_not_in_ps : u ∉ ps)
    (uw₁_neq : u ≠ w₁)
    : Undirected g w₁ w₂ ps :=
  ⟨ add_undirected_edge_not_use_start_pres upath.path u_not_in_ps uw₁_neq
  , ug
  , upath.pathlist_start
  ⟩

theorem add_edge_not_use_finish_pres {g : Graph α} {u v w₁ w₂ : α} {ps : List α}
    (ug : UndirectedGraph g) -- todo do we need this??
    (upath : Undirected (add_undirected_edge g ⟨u, v⟩) w₁ w₂ ps)
    (v_not_in_ps : v ∉ ps)
    (vw₁_neq : v ≠ w₁)
    : Undirected g w₁ w₂ ps :=
  ⟨ add_undirected_edge_not_use_finish_pres upath.path v_not_in_ps vw₁_neq
  , ug
  , upath.pathlist_start
  ⟩


/- Coercions for undirected path preservations -/

instance {g : Graph α}
    : Coe (Undirected g u v ps) (Undirected (add_vertex g w) u v ps) :=
  ⟨add_vertex_pres w⟩

instance {g : Graph α}
    : Coe (Undirected g u v ps) (Undirected (add_undirected_edge g e) u v ps) :=
  ⟨add_edge_pres e⟩

instance {g : Graph α}
    : Coe (Undirected (add_undirected_edge g e.flip) u v ps)
          (Undirected (add_undirected_edge g e) u v ps) :=
  ⟨add_edge_flip_iff.mp⟩

end Undirected
