
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

    We can resolve this by enforcing that all paths from `u` to `u` must have
    at least 3 vertices.
 -/
structure Path.Undirected (g : Graph α) (u v : α) (ps : List α) : Prop where
  path : Path g u v ps
  cycle_large : u = v → ps.length > 2

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

theorem finish_cons_rest {g : Graph α} {u v : α} {ps : List α}
    : (g |= ps : u -> v) → ∃ps', ps = v :: ps' := by
  intro path; cases path <;> simp

theorem finish_pathlist_equiv
    {g : Graph α} {p u v : α} {ps : List α}
    : (g |= (p::ps) : u -> v) → p = v := by intro path; cases path <;> simp

-- is there a better name for this?
theorem pathlist_finish_equiv {g : Graph α} {u v w: α} {ps : List α}
    (path₁ : g |= ps : u -> v)
    (path₂ : g |= ps : u -> w)
    : v = w := by
  cases ps
  case nil => contradiction
  case cons p ps' =>
    have veq := finish_pathlist_equiv path₁
    have weq := finish_pathlist_equiv path₂
    simp [←veq, ←weq]

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


/- Persevation of paths throuhg graph changes -/

theorem add_vertex_pres {g : Graph α} {u v : α} {ps : List α} (w : α)
    (path : g |= ps : u -> v)
    : add_vertex g w |= ps : u -> v := by
  sorry
instance {g : Graph α} : Coe (Path g u v ps) (Path (add_vertex g w) u v ps) :=
  ⟨add_vertex_pres w⟩

theorem add_edge_pres {g : Graph α} {u v : α} {ps : List α} (e : Edge α)
    (path : g |= ps : u -> v)
    : add_edge g e |= ps : u -> v := by
  sorry
instance {g : Graph α} : Coe (Path g u v ps) (Path (add_edge g e) u v ps) :=
  ⟨add_edge_pres e⟩

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


theorem add_vertex_pres {g : Graph α} {u v : Digraph.Vertices g} (w : α)
    (reach : Reachable g u v)
    : Reachable (Digraph.add_vertex g w) u v := by
  sorry

theorem add_edge_pres {g : Graph α} {u v : Digraph.Vertices g} (e : Edge α)
    (reach : Reachable g u v)
    : Reachable (Digraph.add_edge g e) u v := by
  sorry

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

def add_vertex_start {g : Graph α} (connected : Connected g) (e : Edge α)
    (h₁ : has_vertex g e.start)
    : Connected (Digraph.add_undirected_edge g e) := by
  if h₂ : has_vertex g e.finish then
    have h₃ := add_undirected_edge_pres_existing_vertex g e e.start h₁
    have h₄ := add_undirected_edge_pres_existing_vertex g e e.finish h₂
    have := connected e.start e.finish
    sorry
  else
    intro u v u_in v_in
    simp [Path.Reachable]
    sorry

def add_vertex_finish {g : Graph α} (connected : Connected g) (e : Edge α)
    (h₁ : has_vertex g e.finish)
    : Connected (Digraph.add_undirected_edge g e) := by
  sorry

end Connected
