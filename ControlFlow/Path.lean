
import ControlFlow.Graphs.Digraph
import ControlFlow.Graphs.UndirectedGraph

/- todo: reorganise this file -/
namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

-- we exclude u from the list so a path can be cyclical
inductive Path (g : Graph α) : α → α → List α → Prop where
| edge  : ⟨u, v⟩ ∈ g → Path g u v [v]
| cons  : ⟨v, w⟩ ∈ g
        → Path g u v ps
        → w ∉ ps
        → Path g u w (w::ps)

/- A directed path is restricted so that only the starting node can
    be revisited (to allow for a path to form a cycle). For our definition of
    undirected graph this is a problem since we can have paths: `u -> v -> u`
    which used the same (undirected) edge twice.
 -/
structure Path.Undirected (g : Graph α) (u v : α) (ps : List α) : Prop where
  path : Path g u v ps
  undirected : UndirectedGraph g
  pathlist_start : ∀ w ps', ps ≠ ps' ++ [u, w]

instance {g : Graph α} : Coe (Path.Undirected g u v ps) (Path g u v ps) :=
  ⟨(·.path)⟩

abbrev DiPath : (g : Graph α) → α → α → List α → Prop := Path
abbrev UndirectedPath : (g : Graph α) → α → α → List α → Prop := Path.Undirected

namespace Path
open Digraph

notation:50 g:51 " |= " p:51 " : " s:51 " -> " t:51 => Path g s t p

def merge_disjoint {g : Graph α} {u v w : α} {ps₁ ps₂ : List α}
    (path₁ : Path g u v ps₁)
    (path₂ : Path g v w ps₂)
    (h₁ : List.Disjoint ps₁ ps₂)
    : Path g u w (ps₂ ++ ps₁) :=
  match path₂ with
  | .edge h₂ => .cons h₂ path₁ (by simp at h₁; exact h₁)
  | .cons h₂ path₂' h₃ => by next ps' =>
    let new_disjoint := List.disjoint_cons_right.mp h₁
    let res := merge_disjoint path₁ path₂' (new_disjoint.right)
    exact .cons h₂ res (by
      intro h₄
      apply Or.elim (List.mem_append.mp h₄) <;> intro h₄
      . exact h₃ h₄
      . exact new_disjoint.left h₄
    )

def length {g : Graph α} {u v : α} {ps : List α} (_ : g |= ps : u -> v) : Nat :=
  ps.length + 1

theorem empty : ¬Path (empty : Graph α) u v ps := by
  intro path; cases path
  case edge h => exact Digraph.empty_edges ⟨u, v⟩ h
  case cons w _ _ h _ => exact Digraph.empty_edges ⟨w, v⟩ h

theorem Undirected.empty : ¬Undirected (Digraph.empty : Graph α) u v ps := by
  intro upath; exact Path.empty upath.path

theorem out_edges {g : Graph α} {u v w : α}
    (path₁ : g |= ps : u -> v)
    (h₁ : ⟨v, w⟩ ∈ out_edges g v)
    (h₂ : w ∉ ps)
    : g |= (w::ps) : u -> w := by
  have path₂ := Path.edge (Digraph.out_edges_has_edge g v w |>.mp h₁)
  exact Path.merge_disjoint path₁ path₂ (by simp [*])

theorem in_edges {g : Graph α} {u v w : α}
    (path₂ : g |= ps : v -> w)
    (h₁ : ⟨u, v⟩ ∈ in_edges g v)
    (h₂ : v ∉ ps)
    : g |= (ps ++ [v]) : u -> w := by
  have path₁ := Path.edge (Digraph.in_edges_has_edge g u v |>.mp h₁)
  exact Path.merge_disjoint path₁ path₂ (by simp [*])

@[simp] theorem succ {g : Graph α} {u v : α}
    (h : v ∈ succ g u) : g |= [v] : u -> v :=
  Path.edge (succ_edge_in_graph.mp h)

@[simp] theorem pred {g : Graph α} {u v : α}
    (h : u ∈ pred g v) : g |= [v] : u -> v :=
  Path.edge (pred_edge_in_graph.mp h)

theorem succ_merge {g : Graph α} {u v w : α}
    (path₁ : g |= ps : u -> v)
    (h₁ : w ∈ Digraph.succ g v)
    (h₂ : w ∉ ps)
    : g |= (w::ps) : u -> w := by
  exact Path.out_edges path₁ (succ_has_edge.mp h₁) h₂

theorem pred_merge {g : Graph α} {u v w : α}
    (path₂ : g |= ps : v -> w)
    (h₁ : u ∈ Digraph.pred g v)
    (h₂ : v ∉ ps)
    : g |= (ps ++ [v]) : u -> w := by
  exact Path.in_edges path₂ (pred_has_edge.mp h₁) h₂

theorem pathlist_nonempty {g : Graph α} {u v : α} {ps : List α}
    (path : g |= ps : u -> v) : ps ≠ [] := by
  intro eq; cases path <;> contradiction

theorem in_pathlist_in_graph {g : Graph α} {u v : α}
    (path : g |= nodes : v -> w) (h₁ : u ∈ nodes) : g |= u := by
  induction path <;> simp
  case edge h₂ =>
    cases h₁ <;> simp [*] at *
    case head => exact (edge_vertices g _ _ h₂).right
    case tail _ _ => contradiction
  case cons w h₂ _path₁ h₃ ih =>
    cases h₁
    . exact (edge_vertices g _ _ h₂).right
    . next h₄ => exact ih h₄

theorem start_in_graph {g : Graph α} {u v : α}
    (path : g |= nodes : u -> v) : g |= u := by
  induction path <;> simp
  case edge h₁ => exact (edge_vertices g _ _ h₁).left
  case cons ih => exact ih

theorem finish_in_graph {g : Graph α} {u v : α}
    (path : g |= nodes : u -> v) : g |= v := by
  cases path <;> simp
  case edge h₁ => exact (edge_vertices g _ _ h₁).right
  case cons path₁ h₁ h₂ => exact (edge_vertices g _ _ h₁).right

theorem finish_in_pathlist {g : Graph α} {u v : α} {ps : List α}
    (path : g |= ps : u -> v) : v ∈ ps := by
  cases path <;> simp

theorem finish_has_edge {g : Graph α} {u v : α}
    (path : g |= nodes : u -> v) : ∃w, ⟨w, v⟩ ∈ g := by
  cases path <;> simp
  case edge h₁ => exact Exists.intro u h₁
  case cons w _ path₁ h₁ h₂ => exact Exists.intro w h₁

theorem finish_cons_rest {g : Graph α} {u v : α} {ps : List α}
    : (g |= ps : u -> v) → ∃ps', ps = v :: ps' ∧ v ∉ ps' := by
  intro path; cases path <;> simp; case cons h => exact h

theorem finish_cons_eq {g : Graph α} {u v w : α} {ps : List α}
    : (g |= (w :: ps) : u -> v) → v = w := by
  intro path; cases path <;> simp

theorem finish_pathlist_equiv
    {g : Graph α} {p u v : α} {ps : List α}
    : (g |= (p::ps) : u -> v) → p = v := by intro path; cases path <;> simp

theorem pathlist_finish_antisymm {g : Graph α} {u v w: α} {ps : List α}
    (path₁ : g |= ps : u -> v)
    (path₂ : g |= ps : u -> w)
    : v = w := by
  cases ps
  case nil => contradiction
  case cons p ps' =>
    have veq := finish_pathlist_equiv path₁
    have weq := finish_pathlist_equiv path₂
    simp [←veq, ←weq]

theorem first_pathlist_imp_edge {g : Graph α} {u v w₁ w₂ : α} (ps₁ : List α)
    (path : g |= (v :: u :: ps₁) : w₁ -> w₂)
    : ⟨u, v⟩ ∈ g := by
  cases path
  case cons h₁ path' h₂ =>
    apply Exists.elim (finish_cons_rest path'); intro _ h
    simp at h; rw [←h.left.left] at h₁; exact h₁

def split {g : Graph α} {u v w : α} {ps : List α}
    (h₁ : v ∈ ps)
    (h₂ : v ≠ w)
    (path : g |= ps : u -> w)
    : (∃ ps₁ ps₂, List.Disjoint ps₁ ps₂
                ∧ ps = ps₂ ++ ps₁
                ∧ g |= ps₁ : u -> v
                ∧ g |= ps₂ : v -> w) :=
  match path with
  | .edge h₃ => by cases h₁ <;> contradiction
  | .cons h₃ path' h₄ => by next v' ps' =>
    cases decEq v v'
    case isFalse neq =>
      have res := split (by
          cases h₁
          case head => contradiction
          case _ h => exact h
        ) neq path'
      apply Exists.elim res; intro ps₁ h
      apply Exists.elim h; intro ps₂ h'
      apply Exists.intro ps₁
      apply Exists.intro (w :: ps₂)
      apply And.intro <;> simp
      . apply And.intro
        . intro h₅
          rw [h'.right.left] at h₄
          exact h₄ (List.mem_append_of_mem_right ps₂ h₅)
        . exact h'.left
      . apply And.intro
        . exact h'.right.left
        . apply And.intro
          . exact h'.right.right.left
          . exact Path.cons h₃ h'.right.right.right (by
              intro h₅
              rw [h'.right.left] at h₄
              exact h₄ (List.mem_append_of_mem_left ps₁ h₅)
            )
    case isTrue eq =>
      simp [eq]
      apply Exists.intro ps'
      apply Exists.intro [w]
      apply And.intro
      . simp; exact h₄
      . apply And.intro (by simp)
        exact And.intro path' (.edge h₃)

def prior_vertex {g : Graph α} {u v : α} {ps : List α}
    (path : g |= ps : u -> v) : α :=
  match ps with
  | []      => by have := pathlist_nonempty path; contradiction
  | _ :: [] => u
  | _ :: x :: _  => x

structure Cyclic (g : Graph α) (u : α) (ps : List α) : Prop where
  cycle : g |= ps : u -> u

instance {g : Graph α} : Coe (Path g u u ps) (Cyclic g u ps) where
  coe path := ⟨path⟩
instance {g : Graph α} : Coe (Cyclic g u ps) (Path g u u ps) where
  coe cycle := cycle.cycle

structure Acyclic (g : Graph α) (u v : α) (ps : List α) : Prop where
  path : g |= ps : u -> v
  acyclic : u ∉ ps

instance {g : Graph α} : Coe (Acyclic g u v ps) (Path g u v ps) where
  coe path := path.path

def split_cycle {g : Graph α} {u v : α} {ps : List α}
    (path : g |= ps : u -> v)
    (h₁ : u ∈ ps)
    (h₂ : u ≠ v)
    : (∃ ps₁ ps₂, List.Disjoint ps₁ ps₂
                ∧ ps = ps₂ ++ ps₁
                ∧ Cyclic g u ps₁
                ∧ Acyclic g u v ps₂) :=
  let split_res := split h₁ h₂ path
  Exists.elim split_res (fun ps₁ rest =>
      Exists.elim rest (fun ps₂ h₃ =>
        Exists.intro ps₁ (
          Exists.intro ps₂ (
            And.intro (h₃.left)
            <| And.intro (h₃.right.left)
            <| And.intro (h₃.right.right.left)
            <| ⟨ h₃.right.right.right
               , by intro h₄
                    apply List.disjoint_right.mp h₃.left h₄
                    exact finish_in_pathlist h₃.right.right.left
               ⟩
          )
        )
      )
    )

def remove_cycle {g : Graph α} {u v : α} {ps : List α}
    (path : g |= ps : u -> v)
    (h₁ : u ≠ v)
    : ∃ ps', Acyclic g u v ps' :=
  if h₂ : u ∈ ps then
    let split_res := split h₂ h₁ path
    Exists.elim split_res (fun _ps₁ rest =>
      Exists.elim rest (fun ps₂ h₃ =>
        Exists.intro ps₂
          ⟨ h₃.right.right.right
          , by intro h₄
               apply List.disjoint_right.mp h₃.left h₄
               exact finish_in_pathlist h₃.right.right.left
          ⟩
      )
    )
  else Exists.intro ps ⟨path, h₂⟩

-- todo finish
theorem merge {g : Graph α} {u v w : α} {ps₁ ps₂ : List α}
    (path₁ : Path g u v ps₁)
    (path₂ : Path g v w ps₂)
    : ∃ps, Path g u w ps := by
  if h₁ : List.Disjoint ps₁ ps₂
  then exact ⟨ps₂ ++ ps₁, merge_disjoint path₁ path₂ h₁⟩
  else if uv_eq : u = v then simp [uv_eq] at *; exact ⟨ps₂, path₂⟩
  else if vw_eq : v = w then simp [vw_eq] at *; exact ⟨ps₁, path₁⟩
  else
    have ⟨x, hsplit⟩ := List.first_common ps₁.reverse ps₂
      (Iff.subst List.disjoint_reverse_left h₁)
    simp at *
    apply Exists.elim (remove_cycle path₁ uv_eq); intro ps₁' acyclic₁
    apply Exists.elim (remove_cycle path₂ vw_eq); intro ps₂' acyclic₂
    sorry


theorem leave_vertex_no_revisit {g : Graph α} {u v : α} {ps₁ : List α}
    (path₁ : g |= ps₁ : u -> v)
    : ¬∃ps₂, ps₂ ≠ [] ∧ g |= (ps₂ ++ ps₁) : u -> v := by
  intro h₁; apply Exists.elim h₁; intro ps₂ h₁
  have path₂ := h₁.right
  apply Exists.elim (finish_cons_rest path₁); intro ps₁' h₃
  apply Exists.elim (finish_cons_rest path₂); intro ps₂' h₂
  cases ps₂
  case nil => exact h₁.left rfl
  case cons x xs =>
    simp [h₁] at h₂
    have v_not_in := h₂.right
    rw [←h₂.left.right] at v_not_in
    apply Iff.subst List.mem_append v_not_in
    apply Or.inr
    simp [h₃.left]

-- todo
theorem adj_pathlist_imp_edge {g : Graph α} {u v w₁ w₂ : α} (ps₁ ps₂ : List α)
    (path : g |= (ps₂ ++ v :: u :: ps₁) : w₁ -> w₂)
    : ⟨u, v⟩ ∈ g := by
  cases ps₂
  case nil => exact first_pathlist_imp_edge ps₁ path
  case cons p ps =>
    sorry

theorem no_edge_no_path_from {g : Graph α} {u : α}
    : ∀ v, ¬has_vertex g u → ¬∃ ps, g |= ps : u -> v := by
  intro v h₁ h₂
  apply Exists.elim h₂; intro ps path
  induction path
  case edge w h => exact Digraph.edge_vertices g _ _ h |>.left |> h₁
  case cons v' ps' w _ path' _ ih => exact ih (Exists.intro ps' path')

theorem no_edge_no_path_to {g : Graph α} {u : α}
    : ∀ v, ¬has_vertex g u → ¬∃ ps, g |= ps : v -> u := by
  intro v h₁ h₂
  apply Exists.elim h₂; intro ps path
  cases path
  case edge h => exact Digraph.edge_vertices g _ _ h |>.right |> h₁
  case cons w ps path' h h₄ =>
    exact Digraph.edge_vertices g _ _ h |>.right |> h₁

theorem no_succ_no_path {g : Graph α} {u : α}
    : ∀ v, (∀ w, w ∉ Digraph.succ g u) → ¬∃ ps, g |= ps : u -> v := by
  intro v h₁ h₂
  apply Exists.elim h₂; intro ps path
  induction path
  case edge h => have := Digraph.succ_edge_in_graph.mpr h; simp [h₁] at this
  case cons v' ps' w _ path' _ ih => exact ih (Exists.intro ps' path')

theorem no_pred_no_path {g : Graph α} {u : α}
    : ∀ v, (∀ w, w ∉ Digraph.pred g u) → ¬∃ ps, g |= ps : v -> u := by
  intro v h₁ h₂
  apply Exists.elim h₂; intro ps path
  cases path
  case edge h => have := Digraph.pred_edge_in_graph.mpr h; simp [h₁] at this
  case cons w ps path' h h₄ =>
    have := Digraph.pred_edge_in_graph.mpr h
    simp [h₁] at this

theorem add_vertex_no_path {g : Graph α} {u : α}
    : ¬has_vertex g u → ∀ v, (¬∃ ps, (add_vertex g u) |= ps : u -> v)
                           ∧ (¬∃ ps, (add_vertex g u) |= ps : v -> u) := by
  intro u_not_in v
  have e_not_in := add_vertex_no_edges g u u_not_in
  apply And.intro <;> (intro h₁; apply Exists.elim h₁; intro ps path)
  . apply Digraph.no_edge_no_succ u (e_not_in · |>.left) |> no_succ_no_path v
    exact Exists.intro ps path
  . apply Digraph.no_edge_no_pred u (e_not_in · |>.right) |> no_pred_no_path v
    exact Exists.intro ps path

theorem add_edge_new_start_from_must_use {g : Graph α} {u v : α}
    (u_not_in : ¬has_vertex g u)
    : ∀ w ps, add_edge g ⟨u, v⟩ |= ps : u -> w → v ∈ ps := by
  intro w ps path
  induction path
  case edge v' h =>
    simp; exact add_edge_new_start_antisymm g u u_not_in v v' h
  case cons ih => simp; apply Or.inr ih

theorem add_edge_new_start_from_must_use_last {g : Graph α} {u v : α}
    (u_not_in : ¬has_vertex g u)
    : ∀ w ps, (path : add_edge g ⟨u, v⟩ |= ps : u -> w)
            → ps.getLast (pathlist_nonempty path) = v := by
  intro w ps path
  induction path
  case edge v' h =>
    simp; exact add_edge_new_start_antisymm g u u_not_in v v' h |> Eq.symm
  case cons v' ps' w _ path' _ ih => rw [List.getLast_cons]; exact ih

theorem add_edge_new_start_from_singleton {g : Graph α} {u v : α}
    (u_not_in : ¬has_vertex g u)
    : ∀ ps, add_edge g ⟨u, v⟩ |= ps : u -> v → ps = [v] := by
  intro ps path
  apply Exists.elim (finish_cons_rest path); intro ps' cons_rest
  cases ps'
  case nil => exact cons_rest.left
  case cons x xs =>
    rw [cons_rest.left] at path
    have last := add_edge_new_start_from_must_use_last u_not_in v _ path
    have := List.getLast?_eq_getLast (x :: xs) (by simp)
    simp at last
    rw [last] at this
    have := List.mem_of_mem_getLast? this |> cons_rest.right
    contradiction

theorem add_edge_new_start_no_cycle {g : Graph α} {u v : α}
    (u_not_in : ¬has_vertex g u)
    (neq : u ≠ v)
    : ¬∃ ps, add_edge g ⟨u, v⟩ |= ps : u -> u := by
  intro h₁; apply Exists.elim h₁; intro ps path
  cases path
  case edge h =>
    exact Digraph.add_edge_new_start_antisymm g u u_not_in _ _ h |>.symm |> neq
  case cons w ps path h₁ h₂ =>
    exact Digraph.add_edge_new_start_no_in_edge g u u_not_in v w neq h₁

-- todo clean this up
theorem add_edge_new_start_to_no_more {g : Graph α} {u v w : α} {ps : List α}
    (u_not_in : ¬has_vertex g u)
    (path : add_edge g ⟨u, v⟩ |= ps : w -> u)
    : ∀ w', ¬(add_edge g ⟨u, v⟩ |= w'::ps : w -> w') := by
  intro w' path'
  if uv_eq : u = v then
    simp only [uv_eq] at *
    cases path
    case edge h₁ =>
      have h := first_pathlist_imp_edge [] path'
      have vw'_eq := add_edge_new_start_antisymm g v u_not_in v w' h
      cases path'
      case cons h₂ => apply h₂; simp [vw'_eq]
    case cons v' ps'' path'' h₁ h₂ =>
      have vs_eq := add_edge_new_finish_antisymm g v u_not_in v v' h₁
      simp [vs_eq] at h₂
      exact h₂ (finish_in_pathlist path'')
  else
    cases path
    case edge h => exact add_edge_new_start_no_in_edge g u u_not_in v w uv_eq h
    case cons w'' ps'' path'' h₁ h₂ =>
      exact add_edge_new_start_no_in_edge g u u_not_in v w'' uv_eq h₁

theorem add_edge_self_makes_cycle {g : Graph α}
    : add_edge g ⟨u, u⟩ |= [u] : u -> u :=
  .edge (add_edge_adds g ⟨u, u⟩)

theorem add_undirected_edge_new_start_from_must_use {g : Graph α} {u v : α}
    (u_not_in : ¬has_vertex g u)
    : ∀ w ps, add_undirected_edge g ⟨u, v⟩ |= ps : u -> w → v ∈ ps := by
  intro w ps path
  induction path
  case edge v' h =>
    simp; exact add_undirected_edge_new_start_antisymm g u u_not_in v v'
      (Or.inr h)
  case cons ih => simp; apply Or.inr ih

theorem add_undirected_edge_new_start_from_must_use_last {g : Graph α} {u v : α}
    (u_not_in : ¬has_vertex g u)
    : ∀ w ps, (path : add_undirected_edge g ⟨u, v⟩ |= ps : u -> w)
            → ps.getLast (pathlist_nonempty path) = v := by
  intro w ps path
  induction path
  case edge v' h =>
    simp
    exact add_undirected_edge_new_start_antisymm g u u_not_in v v' (Or.inr h)
      |> Eq.symm
  case cons v' ps' w _ path' _ ih => rw [List.getLast_cons]; exact ih

theorem add_undirected_edge_new_start_from_singleton {g : Graph α} {u v : α}
    (u_not_in : ¬has_vertex g u)
    : ∀ ps, add_undirected_edge g ⟨u, v⟩ |= ps : u -> v → ps = [v] := by
  intro ps path
  apply Exists.elim (finish_cons_rest path); intro ps' cons_rest
  cases ps'
  case nil => exact cons_rest.left
  case cons x xs =>
    rw [cons_rest.left] at path
    have last :=
      add_undirected_edge_new_start_from_must_use_last u_not_in v _ path
    have := List.getLast?_eq_getLast (x :: xs) (by simp)
    simp at last
    rw [last] at this
    have := List.mem_of_mem_getLast? this |> cons_rest.right
    contradiction

theorem add_undirected_edge_new_start_cycle_pathlist {g : Graph α} {u v : α}
    (u_not_in : ¬has_vertex g u)
    (neq : u ≠ v)
    : ∀ ps, add_undirected_edge g ⟨u, v⟩ |= ps : u -> u → ps = [u, v] := by
  intro ps path
  cases path
  case edge h =>
    simp; apply neq; apply Eq.symm
    exact add_undirected_edge_new_start_antisymm g u u_not_in v u (Or.inl h)
  case cons w ps path h₁ h₂ =>
    have vw_eq :=
      add_undirected_edge_new_start_antisymm g u u_not_in _ _ (Or.inl h₁)
    simp [←vw_eq] at path
    have ps_single :=
      add_undirected_edge_new_start_from_singleton u_not_in ps path
    simp [ps_single]

-- todo clean up this function
theorem add_undirected_edge_new_start_to_no_more {g : Graph α} {u v w : α}
    {ps : List α}
    (u_not_in : ¬has_vertex g u)
    (vw_neq : v ≠ w)
    (path : add_undirected_edge g ⟨u, v⟩ |= ps : w -> u)
    : ∀ w', ¬(add_undirected_edge g ⟨u, v⟩ |= w'::ps : w -> w') := by
  intro w' path'
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
  else
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

theorem add_undirected_edge_makes_cycle {g : Graph α} {u v : α}
    (neq : u ≠ v)
    : add_undirected_edge g ⟨u, v⟩ |= [u, v] : u -> u :=
  .cons (add_undirected_edge_adds g ⟨u, v⟩ |>.right)
    (.edge (add_undirected_edge_adds g ⟨u, v⟩ |>.left))
    (List.not_mem_cons_of_ne_of_not_mem neq (List.not_mem_nil u))

theorem add_undirected_edge_self_makes_cycle {g : Graph α} {u : α}
    : add_undirected_edge g ⟨u, u⟩ |= [u] : u -> u :=
  .edge (add_undirected_edge_adds g ⟨u, u⟩ |>.left)


/- Persevation of paths through graph changes -/

theorem add_vertex_pres {g : Graph α} {u v : α} {ps : List α} (w : α)
    (path : g |= ps : u -> v)
    : add_vertex g w |= ps : u -> v := by
  cases path
  case edge h => exact .edge h
  case cons path' h₁ h₂ => exact .cons h₁ (add_vertex_pres w path') h₂

theorem add_edge_pres {g : Graph α} {u v : α} {ps : List α} (e : Edge α)
    (path : g |= ps : u -> v)
    : add_edge g e |= ps : u -> v := by
  cases path
  case edge h => exact .edge h
  case cons path' h₁ h₂ => exact .cons h₁ (add_edge_pres e path') h₂

theorem add_edge_new_start_pres {g : Graph α} {u v w₁ w₂ : α} {ps : List α}
    (u_not_in : ¬has_vertex g u)
    (path : add_edge g ⟨u, v⟩ |= ps : w₁ -> w₂)
    (w₁_neq : w₁ ≠ u)
    (w₂_neq : w₂ ≠ u)
    : g |= ps : w₁ -> w₂ := by
  induction path
  case edge w₂ h =>
    apply Or.elim (Digraph.add_edge_eq_or_in g ⟨w₁, w₂⟩ ⟨u, v⟩ h) <;> intro h₁
    . simp at h₁; have := h₁.left; contradiction
    . exact .edge h₁
  case cons cons v' ps' w h₁ path' h₂ ih =>
    if eq : v' = u then
      have old_path := Path.cons h₁ path' h₂
      rw [eq] at path'
      have := add_edge_new_start_to_no_more u_not_in path' w old_path
      contradiction
    else
      have := add_edge_pres_edges g ⟨v', w⟩ ⟨u, v⟩
        (by simp; intro eq' _; exact eq eq') |>.mpr h₁
      exact .cons this (ih eq) h₂

theorem add_undirected_edge_pres {g : Graph α} {u v : α} {ps : List α}
    (e : Edge α)
    (path : g |= ps : u -> v)
    : add_undirected_edge g e |= ps : u -> v := by
  cases path
  case edge h => exact .edge h
  case cons path' h₁ h₂ => exact .cons h₁ (add_undirected_edge_pres e path') h₂

theorem add_undirected_edge_new_start_pres {g : Graph α} {u v w₁ w₂ : α}
    {ps : List α}
    (u_not_in : ¬has_vertex g u)
    (path : add_undirected_edge g ⟨u, v⟩ |= ps : w₁ -> w₂)
    (w₁u_neq : w₁ ≠ u)
    (w₂u_neq : w₂ ≠ u)
    (w₁v_neq : w₁ ≠ v)
    : g |= ps : w₁ -> w₂ := by
  induction path
  case edge w₂ h =>
    apply Or.elim (add_undirected_edge_eq_or_in g ⟨w₁,w₂⟩ ⟨u,v⟩ h) <;> intro h₁
    . apply Or.elim h₁ <;> (simp; intro h₁; contradiction)
    . exact .edge h₁
  case cons cons v' ps' w h₁ path' h₂ ih =>
    if eq : v' = u then
      have old_path := Path.cons h₁ path' h₂
      rw [eq] at path'
      have := add_undirected_edge_new_start_to_no_more u_not_in
        (neq_symm w₁v_neq) path' w old_path
      contradiction
    else
      have := add_undirected_edge_pres_edges g ⟨v', w⟩ ⟨u, v⟩
        (by simp; intro eq' _; exact eq eq')
        (by simp; intro _ eq'; exact w₂u_neq eq')
      exact .cons (this.mpr h₁) (ih eq) h₂


/- Coercions for path preservations -/

instance {g : Graph α} : Coe (Path g u v ps) (Path (add_vertex g w) u v ps) :=
  ⟨add_vertex_pres w⟩

instance {g : Graph α} : Coe (Path g u v ps) (Path (add_edge g e) u v ps) :=
  ⟨add_edge_pres e⟩

instance {g : Graph α}
    : Coe (Path g u v ps) (Path (add_undirected_edge g e) u v ps) :=
  ⟨add_undirected_edge_pres e⟩


namespace Undirected

open UndirectedGraph

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

theorem add_edge_self_makes_cycle {g : Graph α} (ug : UndirectedGraph g)
    : Undirected (add_undirected_edge g ⟨u, u⟩) u u [u] :=
  ⟨ Path.add_undirected_edge_self_makes_cycle
  , add_edge ug ⟨u, u⟩
  , by intro w ps' h; cases ps' <;> simp at h
  ⟩


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
    (u_not_in : ¬has_vertex g u)
    (upath : Undirected (add_undirected_edge g ⟨u, v⟩) w₁ w₂ ps)
    (w₁u_neq : w₁ ≠ u)
    (w₂u_neq : w₂ ≠ u)
    : Undirected g w₁ w₂ ps := by
  induction upath.path
  case edge w₂ h =>
    apply Or.elim (add_undirected_edge_eq_or_in g ⟨w₁,w₂⟩ ⟨u,v⟩ h) <;> intro h₁
    . apply Or.elim h₁ <;> (simp; intro h₁ h₂; contradiction)
    . exact ⟨.edge h₁, sorry, sorry⟩
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
      exact ⟨.cons (this.mpr h₁) (ih upath' eq) h₂, sorry, sorry⟩


/- Coercions for undirected path preservations -/

instance {g : Graph α}
    : Coe (Undirected g u v ps) (Undirected (add_vertex g w) u v ps) :=
  ⟨add_vertex_pres w⟩

instance {g : Graph α}
    : Coe (Undirected g u v ps) (Undirected (add_undirected_edge g e) u v ps) :=
  ⟨add_edge_pres e⟩

end Undirected

/- Reachability -/
-- todo: should this remain in this namespace/file ??

inductive Reachable (g : Graph α) : (u v : Vertices g) → Prop where
| refl : Reachable g u u
| path : (ps : List α)
       → (path : g |= ps : u -> v)
       → Reachable g ⟨u, start_in_graph path⟩ ⟨v, finish_in_graph path⟩

namespace Reachable

theorem trans {g : Graph α} {u v w : Vertices g}
    (r₁ : Reachable g u v)
    (r₂ : Reachable g v w)
    : Reachable g u w := by
  cases r₁
  case refl => exact r₂
  case path ps₁ p₁ =>
    cases r₂
    case refl => exact .path ps₁ p₁
    case path ps₂ p₂ =>
      apply Exists.elim (merge p₁ p₂); intro ps p
      exact .path ps p

nonrec def Vertices (g : Graph α) : Type := Vertices g

instance {g : Graph α} : LE (Reachable.Vertices g) where
  le u v := Reachable g u v

instance {g : Graph α} : Preorder (Reachable.Vertices g) where
  le_refl u := .refl
  le_trans u v w := Reachable.trans

def edge {g : Graph α} {u v : Vertices g} (uv_in : ⟨u.val, v.val⟩ ∈ g)
    : Reachable g u v := .path [v.val] (Path.edge uv_in)

def edge' {g : Graph α} {e : Edge α} (e_in : e ∈ g)
    :  (s_in : has_vertex g e.start)
    ×' (f_in : has_vertex g e.finish)
    ×' Reachable g ⟨e.start, s_in⟩ ⟨e.finish, f_in⟩ :=
  let evs_in := edge_vertices g e.start e.finish e_in
  let u : Vertices g := ⟨e.start, evs_in.left⟩
  let v : Vertices g := ⟨e.finish, evs_in.right⟩
  let uv_in : ⟨u.val, v.val⟩ ∈ g := by simp [*]; exact e_in
  ⟨evs_in.left, evs_in.right, edge uv_in⟩


/- Preservation properties for graphs -/

theorem add_vertex_pres {g : Graph α} {u v : Digraph.Vertices g} (w : α)
    (reach : Reachable g u v)
    : Reachable (Digraph.add_vertex g w) u v := by
  cases reach
  case refl => exact .refl
  case path ps path => exact Reachable.path ps (Path.add_vertex_pres w path)

theorem add_edge_pres {g : Graph α} {u v : Digraph.Vertices g} (e : Edge α)
    (reach : Reachable g u v)
    : Reachable (Digraph.add_edge g e) u v := by
  cases reach
  case refl => exact .refl
  case path ps path => exact Reachable.path ps (Path.add_edge_pres e path)

theorem add_undirected_edge_pres {g : Graph α} {u v : Digraph.Vertices g}
    (e : Edge α)
    (reach : Reachable g u v)
    : Reachable (Digraph.add_undirected_edge g e) u v := by
  cases reach
  case refl => exact .refl
  case path ps path =>
    exact Reachable.path ps (Path.add_undirected_edge_pres e path)


/- Coercions for preservation -/

instance {g : Graph α} {u v : Digraph.Vertices g} {w : α}
    : Coe (Reachable g u v) (Reachable (Digraph.add_vertex g w) u v) :=
  ⟨add_vertex_pres w⟩

instance {g : Graph α} {u v : Digraph.Vertices g} {e : Edge α}
    : Coe (Reachable g u v) (Reachable (Digraph.add_edge g e) u v) :=
  ⟨add_edge_pres e⟩

instance {g : Graph α} {u v : Digraph.Vertices g} {e : Edge α}
    : Coe (Reachable g u v) (Reachable (Digraph.add_undirected_edge g e) u v) :=
  ⟨add_undirected_edge_pres e⟩

end Reachable
end Path

namespace Digraph

/- TODO: should this all be moved to a different file/namespace ???
      maybe Tree.lean or `ControlFlow.Graph` ?
-/

-- todo: maybe use the `Vertices g` subtype
@[reducible, simp] def Connected (g : Graph α) : Prop :=
  ∀ u v, (h₁ : g |= u) → (h₂ : g |= v) → Path.Reachable g ⟨u, h₁⟩ ⟨v, h₂⟩

namespace Connected

theorem empty : Connected (Digraph.empty : Graph α) := by
  intro u _ h₁; have := Digraph.empty_vertex u h₁; contradiction

theorem trivial (w : α)
    : Connected (Digraph.trivial w : Graph α) := by
  intro u v h₁ h₂
  have eq_uw := Digraph.trivial_vertex_eq u w h₁
  have eq_vw := Digraph.trivial_vertex_eq v w h₂
  simp [*]
  exact .refl

def add_edge {g : Graph α} (connected : Connected g) (e : Edge α)
    (h₁ : has_vertex g e.start)
    (h₂ : has_vertex g e.finish)
    : Connected (Digraph.add_undirected_edge g e) := by
  intro u v u_in v_in
  have node_in := Digraph.add_undirected_edge_in_in_pres_vertices g e h₁ h₂
  have u_in' := node_in u |>.mpr u_in
  have v_in' := node_in v |>.mpr v_in
  exact Path.Reachable.add_undirected_edge_pres e (connected u v u_in' v_in')

def add_vertex_start {g : Graph α} (connected : Connected g) (e : Edge α)
    (start_in : has_vertex g e.start)
    : Connected (Digraph.add_undirected_edge g e) := by
  if h₁ : has_vertex g e.finish then exact add_edge connected e start_in h₁ else
  intro u v u_in v_in

  have e_in : ⟨e.start, e.finish⟩ ∈ Digraph.add_undirected_edge g e :=
    Digraph.add_undirected_edge_adds g e |>.left
  have rev_e_in : ⟨e.finish, e.start⟩ ∈ Digraph.add_undirected_edge g e :=
    Digraph.add_undirected_edge_adds g e |>.right

  if eq_uf : u = e.finish then
    simp [eq_uf]
    if eq_vf : v = e.finish then simp [eq_vf]; exact .refl else
    have v_in' :=
      Digraph.add_undirected_edge_in_out_pres_vertices g e start_in v eq_vf v_in
    apply Path.Reachable.trans (Path.Reachable.edge' rev_e_in |>.snd.snd)
    exact connected e.start v start_in v_in'
       |> Path.Reachable.add_undirected_edge_pres e
  else if eq_vf : v = e.finish then
    simp [eq_vf]
    have u_in' :=
      Digraph.add_undirected_edge_in_out_pres_vertices g e start_in u eq_uf u_in
    apply Path.Reachable.trans
    exact connected u e.start u_in' start_in
       |> Path.Reachable.add_undirected_edge_pres e
    exact Path.Reachable.edge' e_in |>.snd.snd
  else
    have is_in' := Digraph.add_undirected_edge_in_out_pres_vertices g e start_in
    exact connected u v (is_in' u eq_uf u_in) (is_in' v eq_vf v_in)
       |> Path.Reachable.add_undirected_edge_pres e

def add_vertex_finish {g : Graph α} (connected : Connected g) (e : Edge α)
    (h₁ : has_vertex g e.finish)
    : Connected (Digraph.add_undirected_edge g e) := by
  sorry

end Connected
