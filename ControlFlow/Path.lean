
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

abbrev DiPath : (g : Graph α) → α → α → List α → Prop := Path

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
  case edge h => exact empty_edges _ h
  case cons h _ => exact empty_edges _ h

theorem trivial (w : α): ¬Path (trivial w : Graph α) u v ps := by
  intro path; cases path
  case edge h => exact trivial_no_edge _ _ h
  case cons h _ => exact trivial_no_edge _ _ h

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

theorem single_pathlist_imp_edge {g : Graph α} {u v : α}
    (path : g |= [w] : u -> v)
    : ⟨u, v⟩ ∈ g := by
  cases path
  case edge h => exact h
  case cons path _ => have := pathlist_nonempty path; contradiction

theorem last_pathlist_imp_edge {g : Graph α} {u v w : α} {ps : List α}
    (path : g |= ps : u -> v)
    (w_last : ps.getLast (pathlist_nonempty path) = w)
    : ⟨u, w⟩ ∈ g := by
  induction path
  case edge h => simp at w_last; rw [w_last] at h; exact h
  case cons path' _ ih =>
    rw [List.getLast_cons (pathlist_nonempty path')] at w_last
    exact ih w_last

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

theorem in_pathlist_has_path {g : Graph α} {u v w₁ w₂ : α} {ps : List α}
    (path : g |= ps : w₁ -> w₂)
    (u_in_ps : u ∈ ps)
    (v_in_ps : v ∈ ps)
    (uv_neq : u ≠ v)
    : (∃ ps', g |= ps' : u -> v) ∨ (∃ ps', g |= ps' : v -> u) := by
  if uw₁_eq : u = w₁ then
    simp [uw₁_eq]; apply Or.inl
    if vw₂_eq : v = w₂ then simp [vw₂_eq]; exact Exists.intro ps path else
    apply Exists.elim (split v_in_ps vw₂_eq path); intro ps₁ h
    apply Exists.elim h; intro ps₂ h
    exact Exists.intro ps₁ h.right.right.left
  else if uw₂_eq : u = w₂ then
    simp [uw₂_eq]; apply Or.inr
    if vw₁_eq : v = w₁ then simp [vw₁_eq]; exact Exists.intro ps path else
    have vw₂_neq : v ≠ w₂ := fun eq => by simp [←eq] at uw₂_eq; contradiction
    apply Exists.elim (split v_in_ps vw₂_neq path); intro ps₁ h
    apply Exists.elim h; intro ps₂ h
    exact Exists.intro ps₂ h.right.right.right
  else
    apply Exists.elim (split u_in_ps uw₂_eq path); intro ps₁ h
    apply Exists.elim h; intro ps₂ h
    simp [h.right.left] at v_in_ps
    apply Or.elim v_in_ps <;> intro v_in
    . apply Or.inl
      have path' := h.right.right.right
      if vw₂_eq : v = w₂ then simp [vw₂_eq]; exact Exists.intro ps₂ path' else
      apply Exists.elim (split v_in vw₂_eq path'); intro ps₁' h
      apply Exists.elim h; intro ps₂' h
      exact Exists.intro ps₁' h.right.right.left
    . apply Or.inr
      have path' := h.right.right.left
      apply Exists.elim (split v_in (neq_symm uv_neq) path'); intro ps₁' h
      apply Exists.elim h; intro ps₂' h
      exact Exists.intro ps₂' h.right.right.right


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

theorem add_undirected_edge_self_makes_cycle (g : Graph α) (u : α)
    : add_undirected_edge g ⟨u, u⟩ |= [u] : u -> u :=
  .edge (add_undirected_edge_adds g ⟨u, u⟩ |>.left)

@[simp] theorem add_undirected_edge_flip_iff {g : Graph α} {e : Edge α}
    {u v : α} {ps : List α}
    : add_undirected_edge g e.flip |= ps : u -> v
    ↔ add_undirected_edge g e |= ps : u -> v := by
  apply Iff.intro <;> (
    intro path
    induction path
    case edge h => exact .edge h
    case cons h₁ _path' h₂ ih => exact .cons h₁ ih h₂
  )

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

theorem add_edge_not_use_start_pres {g : Graph α} {u v w₁ w₂ : α}
    {ps : List α}
    (path : add_edge g ⟨u, v⟩ |= ps : w₁ -> w₂)
    (u_not_in_ps : u ∉ ps)
    (uw₁_neq : u ≠ w₁)
    : g |= ps : w₁ -> w₂ := by
  induction path
  case edge v' h =>
    exact .edge (add_edge_pres_edges g ⟨w₁, v'⟩ ⟨u, v⟩
      (by simp; intro eq _; exact uw₁_neq (Eq.symm eq)) |>.mpr h)
  case cons v' ps' w' h₁ path' h₂ ih =>
    have u_not_in_ps' := List.not_mem_of_not_mem_cons u_not_in_ps
    have e_neq : Edge.mk v' w' ≠ ⟨u, v⟩ := by
      simp; intro eq₁ _eq₂; rw [eq₁] at path'
      exact u_not_in_ps' (finish_in_pathlist path')
    have e_in := add_edge_pres_edges g ⟨v', w'⟩ ⟨u, v⟩ e_neq |>.mpr h₁
    exact .cons e_in (ih u_not_in_ps') h₂

theorem add_edge_not_use_finish_pres {g : Graph α} {u v w₁ w₂ : α}
    {ps : List α}
    (path : add_edge g ⟨u, v⟩ |= ps : w₁ -> w₂)
    (v_not_in_ps : v ∉ ps)
    : g |= ps : w₁ -> w₂ := by
  induction path
  case edge v' h =>
    exact .edge (add_edge_pres_edges g ⟨w₁, v'⟩ ⟨u, v⟩
      (by simp; intro _ eq; simp [eq] at v_not_in_ps) |>.mpr h)
  case cons v' ps' w' h₁ _path' h₂ ih =>
    have v_not_in_ps' := List.not_mem_of_not_mem_cons v_not_in_ps
    have e_neq : Edge.mk v' w' ≠ ⟨u, v⟩ := by
      simp; intro _ eq; simp [eq] at v_not_in_ps
    have e_in := add_edge_pres_edges g ⟨v', w'⟩ ⟨u, v⟩ e_neq |>.mpr h₁
    exact .cons e_in (ih v_not_in_ps') h₂

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

theorem add_undirected_edge_not_use_start_pres {g : Graph α} {u v w₁ w₂ : α}
    {ps : List α}
    (path : add_undirected_edge g ⟨u, v⟩ |= ps : w₁ -> w₂)
    (u_not_in_ps : u ∉ ps)
    (uw₁_neq : u ≠ w₁)
    : g |= ps : w₁ -> w₂ :=
  add_edge_not_use_start_pres
    (add_edge_not_use_finish_pres path u_not_in_ps) u_not_in_ps uw₁_neq

theorem add_undirected_edge_not_use_finish_pres {g : Graph α} {u v w₁ w₂ : α}
    {ps : List α}
    (path : add_undirected_edge g ⟨u, v⟩ |= ps : w₁ -> w₂)
    (v_not_in_ps : v ∉ ps)
    (vw₁_neq : v ≠ w₁)
    : g |= ps : w₁ -> w₂ :=
  add_edge_not_use_finish_pres
    (add_edge_not_use_start_pres path v_not_in_ps vw₁_neq) v_not_in_ps

theorem add_edges_pres {g : Graph α} {u v : α} {ps : List α}
    (edges : List (Edge α))
    (path : g |= ps : u -> v)
    : (add_edges g edges) |= ps : u -> v := by
  induction path with
  | edge h => exact .edge (add_edges_pres_existing_edge _ _ _ h)
  | cons h₁ _path' h₂ ih =>
    exact .cons (add_edges_pres_existing_edge _ _ _ h₁) ih h₂

theorem add_vertices_pres {g : Graph α} {u v : α} {ps : List α}
    (vertices : List α)
    (path : g |= ps : u -> v)
    : (add_vertices g vertices) |= ps : u -> v := by
  induction path with
  | edge h => exact .edge (add_vertices_pres_edges _ _ _ |>.mp h)
  | cons h₁ _path' h₂ ih =>
    exact .cons (add_vertices_pres_edges _ _ _ |>.mp h₁) ih h₂

theorem graph_merge_pres {g₁ g₂ : Graph α} {u v : α} {ps : List α}
    (or_path : (g₁ |= ps : u -> v) ∨ (g₂ |= ps : u -> v))
    : (Digraph.merge g₁ g₂) |= ps : u -> v := by
  apply Or.elim or_path <;> (
    intro path
    induction path with
    | edge h =>
      apply .edge ∘ merge_has_edge.mpr
      try exact Or.inl h
      try exact Or.inr h
    | cons h₁ path' h₂ ih =>
      try exact .cons (merge_has_edge.mpr (Or.inl h₁)) (Or.inl path' |> ih) h₂
      try exact .cons (merge_has_edge.mpr (Or.inr h₁)) (Or.inr path' |> ih) h₂
  )


/- Coercions for path preservations -/

instance {g : Graph α} : Coe (Path g u v ps) (Path (add_vertex g w) u v ps) :=
  ⟨add_vertex_pres w⟩

instance {g : Graph α} : Coe (Path g u v ps) (Path (add_edge g e) u v ps) :=
  ⟨add_edge_pres e⟩

instance {g : Graph α} : Coe (Path g u v ps)
                             (Path (add_undirected_edge g e) u v ps) :=
  ⟨add_undirected_edge_pres e⟩

instance {g : Graph α} : Coe (Path (add_undirected_edge g e.flip) u v ps)
                             (Path (add_undirected_edge g e) u v ps) :=
  ⟨add_undirected_edge_flip_iff.mp⟩

instance {g₁ g₂ : Graph α} : Coe (Path g₁ u v ps)
                                 (Path (Digraph.merge g₁ g₂) u v ps) :=
  ⟨graph_merge_pres ∘ Or.inl⟩

instance {g₁ g₂ : Graph α} : Coe (Path g₂ u v ps)
                                 (Path (Digraph.merge g₁ g₂) u v ps) :=
  ⟨graph_merge_pres ∘ Or.inr⟩

end Path
