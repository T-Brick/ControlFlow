
import ControlFlow.Digraph

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

namespace Path
open Digraph

notation:50 g:51 " |= " p:51 " : " s:51 " -> " t:51 => Path g s t p

def merge {g : Graph α} {u v w : α} {ps₁ ps₂ : List α}
    (path₁ : Path g u v ps₁)
    (path₂ : Path g v w ps₂)
    (h₁ : List.Disjoint ps₁ ps₂)
    : Path g u w (ps₂ ++ ps₁) :=
  match path₂ with
  | .edge h₂ => .cons h₂ path₁ (by simp at h₁; exact h₁)
  | .cons h₂ path₂' h₃ => by next ps' =>
    let new_disjoint := List.disjoint_cons_right.mp h₁
    let res := merge path₁ path₂' (new_disjoint.right)
    exact .cons h₂ res (by
      intro h₄
      apply Or.elim (List.mem_append.mp h₄) <;> intro h₄
      . exact h₃ h₄
      . exact new_disjoint.left h₄
    )

def length {g : Graph α} {u v : α} {ps : List α} (_ : g |= ps : u -> v) : Nat :=
  ps.length + 1

theorem out_edges {g : Graph α} {u v w : α}
    (path₁ : g |= ps : u -> v)
    (h₁ : ⟨v, w⟩ ∈ out_edges g v)
    (h₂ : w ∉ ps)
    : g |= (w::ps) : u -> w := by
  have path₂ := Path.edge (Digraph.out_edges_has_edge g v w |>.mp h₁)
  exact Path.merge path₁ path₂ (by simp [*])

theorem in_edges {g : Graph α} {u v w : α}
    (path₂ : g |= ps : v -> w)
    (h₁ : ⟨u, v⟩ ∈ in_edges g v)
    (h₂ : v ∉ ps)
    : g |= (ps ++ [v]) : u -> w := by
  have path₁ := Path.edge (Digraph.in_edges_has_edge g u v |>.mp h₁)
  exact Path.merge path₁ path₂ (by simp [*])

@[simp] theorem succ {g : Graph α} {u v : α}
    (h : v ∈ succ g u) : g |= [v] : u -> v :=
  Path.edge (succ_edge_in_graph g u v h)

@[simp] theorem pred {g : Graph α} {u v : α}
    (h : u ∈ pred g v) : g |= [v] : u -> v :=
  Path.edge (pred_edge_in_graph g u v h)

theorem succ_merge {g : Graph α} {u v w : α}
    (path₁ : g |= ps : u -> v)
    (h₁ : w ∈ Digraph.succ g v)
    (h₂ : w ∉ ps)
    : g |= (w::ps) : u -> w := by
  exact Path.out_edges path₁ (succ_has_edge g v w |>.mp h₁) h₂

theorem pred_merge {g : Graph α} {u v w : α}
    (path₂ : g |= ps : v -> w)
    (h₁ : u ∈ Digraph.pred g v)
    (h₂ : v ∉ ps)
    : g |= (ps ++ [v]) : u -> w := by
  exact Path.in_edges path₂ (pred_has_edge g u v |>.mp h₁) h₂

theorem in_graph {g : Graph α} {u v : α}
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
