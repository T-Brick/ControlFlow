import ControlFlow.AuxDefs

/- todo: reorganise, standardise names/theorems -/
namespace ControlFlow

variable [DecidableEq α]

structure Edge (α : Type) where
  start  : α
  finish : α
deriving Inhabited, Repr, DecidableEq

instance : Coe (Edge α) (α × α) where coe e := (e.start, e.finish)
instance : Coe (α × α) (Edge α) where coe e := ⟨e.fst, e.snd⟩

def Edge.elem (v : α) (e : Edge α) : Bool := v = e.start || v = e.finish
instance : Membership α (Edge α) where mem v e := Edge.elem v e

@[reducible, simp] def Edge.flip (e : Edge α) : Edge α := ⟨e.finish, e.start⟩

@[simp] theorem Edge.elem_iff [DecidableEq α] {v : α} {e : Edge α}
    : Edge.elem v e = true ↔ v ∈ e :=
  ⟨by simp [Membership.mem], by simp [Membership.mem]⟩

theorem Edge.mem_flip {w : α} {e: Edge α} : w ∈ e ↔ w ∈ e.flip := by
  simp [←Edge.elem_iff, elem]
  apply Iff.intro <;> (intro h; apply Or.symm; exact h)

instance [ToString α] : ToString (Edge α) where
  toString e := s!"({e.start}, {e.finish})"

/- Properties that we care about (according to 210)
    - [ ] map over vertices/edges (not implemented yet, idk what the invariants would be)
    - [x] degree of vertex (not directly implemented)
    - [x] determine if edge is in graph
    - [x] insert/delete a vertex or an edge

    TODO: split this into different subclasses
 -/
class Digraph (α : Type) (T : (α : Type) → Type) where
  empty      : T α
  has_edge   : T α → Edge α → Bool
  has_vertex : T α → α → Bool
  add_edge   : T α → Edge α → T α
  rem_edge   : T α → Edge α → T α
  add_vertex : T α → α → T α
  rem_vertex : T α → α → T α
  out_edges  : T α → α → List (Edge α)
  in_edges   : T α → α → List (Edge α)
  toVertices : T α → List α
  edge_vertices             : ∀ g u v, has_edge g ⟨u, v⟩ → has_vertex g u ∧ has_vertex g v
  empty_edges               : ∀ e, ¬has_edge empty e
  empty_vertex              : ∀ v, ¬has_vertex empty v
  add_edge_adds             : ∀ g e, has_edge (add_edge g e) e
  add_edge_pres_edges       : ∀ g e₁ e₂, e₁ ≠ e₂ → (has_edge g e₁ ↔ has_edge (add_edge g e₂) e₁)
  add_edge_pres_vertex      : ∀ g u v w, u ≠ v → u ≠ w → (has_vertex g u ↔ has_vertex (add_edge g ⟨v, w⟩) u)
  rem_edge_removes          : ∀ g e, ¬has_edge (rem_edge g e) e
  rem_edge_pres_edges       : ∀ g e₁ e₂, e₁ ≠ e₂ → (has_edge g e₁ ↔ has_edge (rem_edge g e₂) e₁)
  rem_edge_pres_vertex      : ∀ g u v w, (has_vertex g u ↔ has_vertex (rem_edge g ⟨v, w⟩) u)
  add_vertex_adds           : ∀ g v, has_vertex (add_vertex g v) v
  add_vertex_pres_edges     : ∀ g v e, has_edge g e ↔ has_edge (add_vertex g v) e
  add_vertex_pres_vertex    : ∀ g u v, u ≠ v → (has_vertex g u ↔ has_vertex (add_vertex g v) u)
  rem_vertex_removes_vertex : ∀ g v, ¬has_vertex (rem_vertex g v) v
  rem_vertex_removes_edge   : ∀ g u v, (¬has_edge (rem_vertex g v) ⟨u, v⟩) ∧ (¬has_edge (rem_vertex g v) ⟨v, u⟩)
  rem_vertex_pres_edges     : ∀ g u v w, u ≠ v → u ≠ w → (has_edge g ⟨v, w⟩ ↔ has_edge (rem_vertex g u) ⟨v, w⟩)
  rem_vertex_pres_vertex    : ∀ g u v, u ≠ v → (has_vertex g u ↔ has_vertex (rem_vertex g v) u)
  out_edges_has_edge        : ∀ g u v, ⟨u, v⟩ ∈ (out_edges g u) ↔ has_edge g ⟨u, v⟩
  out_edges_start           : ∀ g e u, e ∈ (out_edges g u) → e.start = u
  in_edges_has_edge         : ∀ g u v, ⟨u, v⟩ ∈ (in_edges g v) ↔ has_edge g ⟨u, v⟩
  in_edges_finish           : ∀ g e v, e ∈ (in_edges g v) → e.finish = v
  toVertices_has_vertex     : ∀ g v, v ∈ toVertices g ↔ has_vertex g v

instance [Digraph α Graph] : Membership (Edge α) (Graph α) :=
  ⟨fun e g => Digraph.has_edge g e⟩

class UndirectedGraph [Digraph α Graph] (g : Graph α) : Prop where
  undirected : ∀ u v, Digraph.has_edge g ⟨u, v⟩ ↔ Digraph.has_edge g ⟨v, u⟩

@[reducible] def Digraph.Oriented [Digraph α Graph] (g : Graph α) : Prop :=
  ∀ u v, ⟨u, v⟩ ∈ g → ⟨v, u⟩ ∉ g

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

namespace Digraph

def Vertices (g : Graph α) := {v : α // has_vertex g v}

instance {g : Graph α} : DecidableEq (Vertices g) :=
  fun u v =>
    match decEq u.val v.val with
    | isFalse h₁ => isFalse (fun h₂ => h₁ (Subtype.val_inj.mpr h₂))
    | isTrue  h₁ => isTrue (Subtype.eq h₁)

theorem has_edge_membership (g : Graph α) (e : Edge α)
  : has_edge g e ↔ e ∈ g := by simp [Membership.mem]


/- Additional theorems directly related to graph preservation -/

theorem add_edge_pres_existing_edge (g : Graph α)
    : ∀ e₁ e₂, e₁ ∈ g → e₁ ∈ add_edge g e₂ := by
  intro e₁ e₂ h₁
  if eq : e₁ = e₂
  then rw [eq]; exact add_edge_adds g e₂
  else exact add_edge_pres_edges g e₁ e₂ eq |>.mp h₁

theorem add_edge_pres_existing_vertex (g : Graph α)
    : ∀ e v, has_vertex g v → has_vertex (add_edge g e) v := by
  intro e v h₁
  if eq_s : v = e.start then
    rw [eq_s]
    exact add_edge_adds g e |> edge_vertices _ e.start e.finish |>.left
  else if eq_f : v = e.finish then
    rw [eq_f]
    exact add_edge_adds g e |> edge_vertices _ e.start e.finish |>.right
  else exact add_edge_pres_vertex g v e.start e.finish eq_s eq_f |>.mp h₁

theorem add_edge_eq_or_in (g : Graph α)
    : ∀ e₁ e₂, e₁ ∈ add_edge g e₂ → e₁ = e₂ ∨ e₁ ∈ g := by
  intro e₁ e₂ h₁
  if eq : e₁ = e₂
  then exact Or.inl eq
  else apply Or.inr; exact add_edge_pres_edges g e₁ e₂ eq |>.mpr h₁

theorem add_vertex_pres_existing_vertex (g : Graph α)
    : ∀ v₁ v₂, has_vertex g v₁ → has_vertex (add_vertex g v₂) v₁ := by
  intro v₁ v₂ h₁
  if eq : v₁ = v₂
  then rw [eq]; exact add_vertex_adds g v₂
  else exact add_vertex_pres_vertex g v₁ v₂ eq |>.mp h₁

theorem add_vertex_eq_or_in (g : Graph α)
    : ∀ v₁ v₂, has_vertex (add_vertex g v₂) v₁ → v₁ = v₂ ∨ has_vertex g v₁ := by
  intro v₁ v₂ h₁
  if eq : v₁ = v₂
  then exact Or.inl eq
  else apply Or.inr; exact add_vertex_pres_vertex g v₁ v₂ eq |>.mpr h₁

theorem out_in_edges {g : Graph α} {u v : α}
    : ⟨u, v⟩ ∈ out_edges g u ↔ ⟨u, v⟩ ∈ in_edges g v := by
  apply Iff.intro <;> intro h
  . exact in_edges_has_edge g u v |>.mpr (out_edges_has_edge g u v |>.mp h)
  . exact out_edges_has_edge g u v |>.mpr (in_edges_has_edge g u v |>.mp h)


/- Successors / Predecessor utility functions -/

@[reducible, simp] def succ_edges (g : Graph α) (v : α) : List (Edge α) :=
  Digraph.out_edges g v
@[reducible, simp] def pred_edges (g : Graph α) (v : α) : List (Edge α) :=
  Digraph.in_edges g v
@[reducible, simp] def neighbors_edges (g : Graph α) (v : α) : List (Edge α) :=
  List.union (succ_edges g v) (pred_edges g v)

def succ (g : Graph α) (v : α) : List α := succ_edges g v |>.map (·.finish)
def pred (g : Graph α) (v : α) : List α := pred_edges g v |>.map (·.start)
def neighbors (g : Graph α) (v : α) : List α :=
  List.union (succ g v) (pred g v)

def deg_out (g : Graph α) (v : α) : Nat := (succ g v).length
def deg_in  (g : Graph α) (v : α) : Nat := (pred g v).length

notation:50 g:51 " |= " v:51 => has_vertex g v
notation:50 g:51 " |= N⁺( " v:51 " ) " => succ g v
notation:50 g:51 " |= N⁻( " v:51 " ) " => pred g v
notation:50 g:51 " |= N( "  v:51 " ) " => neighbors g v
notation:50 g:51 " |= deg_out( "  v:51 " ) " => deg_out g v
notation:50 g:51 " |= deg_in( "  v:51 " ) " => deg_in g v


/- Successor theorems -/

theorem succ_has_edge {g : Graph α} {u v : α}
    : v ∈ succ g u ↔ ⟨u, v⟩ ∈ out_edges g u := by
  apply Iff.intro <;> intro h₁ <;> simp [succ] at *
  . apply Exists.elim h₁
    intro e h₂
    have h₃ := out_edges_start g e u h₂.left
    simp [←h₃, ←h₂.right] at *
    exact h₂
  . apply Exists.intro ⟨u, v⟩; simp [*]

theorem succ_edge_in_graph {g : Graph α} {u v : α}
    : v ∈ succ g u ↔ ⟨u, v⟩ ∈ g :=
  Iff.intro
    (fun h => succ_has_edge.mp h |> (out_edges_has_edge g u v |>.mp))
    (fun h => out_edges_has_edge g u v |>.mpr h |> succ_has_edge.mpr)

theorem succ_in_graph {g : Graph α} {u v : α}
    (h : v ∈ succ g u) : has_vertex g v :=
  (succ_edge_in_graph.mp h) |> (edge_vertices g u v) |>.right


/- Predecessor theorems -/

theorem pred_has_edge {g : Graph α} {u v : α}
    : u ∈ pred g v ↔ ⟨u, v⟩ ∈ in_edges g v := by
  apply Iff.intro <;> intro h₁ <;> simp [pred] at *
  . apply Exists.elim h₁
    intro e h₂
    have h₃ := in_edges_finish g e v h₂.left
    simp [←h₃, ←h₂.right] at *
    exact h₂
  . apply Exists.intro ⟨u, v⟩; simp [*]

theorem pred_edge_in_graph {g : Graph α} {u v : α}
    : u ∈ pred g v ↔ ⟨u, v⟩ ∈ g :=
  Iff.intro
    (fun h => pred_has_edge.mp h |> (in_edges_has_edge g u v |>.mp))
    (fun h => in_edges_has_edge g u v |>.mpr h |> pred_has_edge.mpr)

theorem pred_in_graph {g : Graph α} {u v : α}
    (h : u ∈ pred g v) : has_vertex g u :=
  (pred_edge_in_graph.mp h) |> (edge_vertices g u v) |>.left


theorem in_succ_iff_in_pred {g : Graph α} {u v : α}
    : u ∈ succ g v ↔ v ∈ pred g u :=
  Iff.intro
    (fun h => succ_edge_in_graph.mp h |> pred_edge_in_graph.mpr)
    (fun h => pred_edge_in_graph.mp h |> succ_edge_in_graph.mpr)


/- Neighbor theorems -/

theorem neighbors_edge_in_graph {g : Graph α} {u v : α}
    : v ∈ neighbors g u ↔ ⟨u, v⟩ ∈ g ∨ ⟨v, u⟩ ∈ g := by
  simp [neighbors]
  apply Iff.intro <;> intro h₁ <;> apply Or.elim h₁ <;> intro h₂
  . exact Or.inl (succ_edge_in_graph.mp h₂)
  . exact Or.inr (pred_edge_in_graph.mp h₂)
  . exact Or.inl (succ_edge_in_graph.mpr h₂)
  . exact Or.inr (pred_edge_in_graph.mpr h₂)

theorem neighbors_in_graph {g : Graph α} {u v : α} (h₁ : v ∈ neighbors g u)
    : has_vertex g v := by
  apply Or.elim (neighbors_edge_in_graph.mp h₁) <;> intro h₂
  . exact edge_vertices g u v h₂ |>.right
  . exact edge_vertices g v u h₂ |>.left


/- Function and theorem for adding undirected edges -/

def add_undirected_edge (g : Graph α) (e : Edge α) : Graph α :=
  add_edge (add_edge g e) e.flip

theorem add_undirected_edge_adds (g : Graph α) (e : Edge α)
    : has_edge (add_undirected_edge g e) e
    ∧ has_edge (add_undirected_edge g e) e.flip := by
  simp [add_undirected_edge]; apply And.intro
  exact add_edge_pres_existing_edge _ _ _ (add_edge_adds _ _)
  exact add_edge_adds _ _

theorem add_undirected_edge_pres_edges (g : Graph α) (e₁ e₂ : Edge α)
    (neq : e₁ ≠ e₂) (neqf : e₁ ≠ e₂.flip)
    : has_edge g e₁ ↔ has_edge (add_undirected_edge g e₂) e₁ := by
  rw [ add_undirected_edge
     , add_edge_pres_edges _ _ _ _
     , add_edge_pres_edges _ _ _ _
     ]
  exact neqf; exact neq

theorem add_undirected_edge_pres_existing_edge (g : Graph α)
    : ∀ e₁ e₂, has_edge g e₁ → has_edge (add_undirected_edge g e₂) e₁ := by
  intro e₁ e₂ h; simp [add_undirected_edge]
  exact add_edge_pres_existing_edge _ _ _ (add_edge_pres_existing_edge _ _ _ h)

theorem add_undirected_edge_eq_or_in (g : Graph α)
    : ∀ e₁ e₂, e₁ ∈ add_undirected_edge g e₂
             → (e₁ = e₂ ∨ e₁ = e₂.flip) ∨ e₁ ∈ g := by
  simp [add_undirected_edge]; intro e₁ e₂ h
  apply Or.elim (add_edge_eq_or_in _ _ _ h) <;> intro h
  . exact Or.inl (Or.inr h)
  . apply Or.elim (add_edge_eq_or_in _ _ _ h) <;> intro h
    . exact Or.inl (Or.inl h)
    . exact Or.inr h

theorem add_undirected_edge_pres_vertex (g : Graph α) (u v w : α)
    (h₁ : u ≠ v) (h₂ : u ≠ w)
    : has_vertex g u ↔ has_vertex (add_undirected_edge g ⟨v, w⟩) u := by
  rw [ add_undirected_edge
     , add_edge_pres_vertex _ _ _ _ h₁ h₂
     , add_edge_pres_vertex _ _ _ _ h₂ h₁
     ]

theorem add_undirected_edge_pres_existing_vertex (g : Graph α)
    : ∀ e v, has_vertex g v → has_vertex (add_undirected_edge g e) v := by
  intro e v h; simp [add_undirected_edge]
  apply add_edge_pres_existing_vertex _ _ _
  exact add_edge_pres_existing_vertex _ _ _ h


/- Function and theorems for adding lists of edges -/

def add_edges (g : Graph α) : List (Edge α) → Graph α
  | [] => g
  | e :: es => add_edge (add_edges g es) e

theorem add_edges_adds (g : Graph α) (edges : List (Edge α))
    : ∀ e ∈ edges, has_edge (add_edges g edges) e := by
  intro e h₁
  induction edges
  case nil => contradiction
  case cons x xs ih =>
    simp [add_edges]
    cases h₁
    case head => exact add_edge_adds (add_edges g xs) e
    case tail _ h₂ =>
      have := ih h₂
      if h₃ : e = x then simp [h₃]; exact add_edge_adds (add_edges g xs) x else
        apply add_edge_pres_edges (add_edges g xs) e x h₃ |>.mp
        exact ih h₂

theorem add_edges_pres_edges (g : Graph α) (edges : List (Edge α))
    : ∀ e, e ∉ edges → (has_edge g e ↔ has_edge (add_edges g edges) e) := by
  intro e h₁
  induction edges <;> simp [add_edges]
  case cons x xs ih =>
    if h₂ : e = x then simp [h₂] at h₁ else
      have := add_edge_pres_edges (add_edges g xs) e x h₂
      rw [←this]
      exact ih (List.not_mem_of_not_mem_cons h₁)

theorem add_edges_pres_existing_edge (g : Graph α) (edges : List (Edge α))
    : ∀ e ∈ g, e ∈ add_edges g edges := by
  intro e h₁
  if e_in : e ∈ edges
  then exact add_edges_adds g edges e e_in
  else exact add_edges_pres_edges g edges e e_in |>.mp h₁

theorem add_edges_in_list_or_graph (g : Graph α) (edges : List (Edge α))
    : ∀ e ∈ add_edges g edges, e ∈ edges ∨ e ∈ g := by
  intro e h₁
  if e_in : e ∈ edges
  then exact Or.inl e_in
  else apply Or.inr; exact add_edges_pres_edges g edges e e_in |>.mpr h₁

theorem add_edges_pres_existing_vertex (g : Graph α) (edges : List (Edge α))
    : ∀ u, has_vertex g u → has_vertex (add_edges g edges) u := by
  intro u h₁
  induction edges <;> simp [add_edges]
  case nil => exact h₁
  case cons x xs ih => exact add_edge_pres_existing_vertex _ x u ih

theorem add_edges_pres_vertex (g : Graph α) (edges : List (Edge α))
    : ∀ u, (∀ e ∈ edges, u ≠ e.start ∧ u ≠ e.finish)
         → (has_vertex g u ↔ has_vertex (add_edges g edges) u) := by
  intro u not_eq
  apply Iff.intro
  . exact add_edges_pres_existing_vertex g edges u
  . intro h₁
    induction edges <;> simp [add_edges] at *
    case nil => exact h₁
    case cons x xs ih =>
      apply ih not_eq.right
      exact add_edge_pres_vertex _ u x.start x.finish
        not_eq.left.left not_eq.left.right |>.mpr h₁


/- Function and theorems for removing undirected edges -/

def rem_undirected_edge (g : Graph α) (e : Edge α) : Graph α :=
  rem_edge (rem_edge g e) e.flip


/- Function and theorems for removing lists of edges -/

def rem_edges (g : Graph α) : List (Edge α) → Graph α
  | [] => g
  | e :: es => rem_edges (rem_edge g e) es


/- Function and theorems for getting all edges from a list of vertices -/

def all_neighbors (g : Graph α) (vertices : List α) : List (Edge α) :=
  match vertices with
  | [] => []
  | v :: vs => List.union (neighbors_edges g v) (all_neighbors g vs)

theorem all_neighbors_sound (g : Graph α) (vertices : List α)
    : ∀ e, e.start ∈ vertices ∨ e.finish ∈ vertices
         → (e ∈ g → e ∈ all_neighbors g vertices) := by
  intro e h₁ h₂
  induction vertices <;> simp [all_neighbors]
  case nil => simp at h₁
  case cons x xs ih =>
    if x_eq_start : x = e.start then
      apply Or.inl
      apply Or.inl
      simp [x_eq_start]
      exact (out_edges_has_edge g e.start e.finish).mpr h₂
    else if x_eq_finish : x = e.finish then
      apply Or.inl
      apply Or.inr
      simp [x_eq_finish]
      exact (in_edges_has_edge g e.start e.finish).mpr h₂
    else
      apply Or.elim h₁ <;> intro h₁
      . simp [neq_symm x_eq_start] at h₁
        exact Or.inr (ih (Or.inl h₁))
      . simp [neq_symm x_eq_finish] at h₁
        exact Or.inr (ih (Or.inr h₁))

theorem all_neighbors_complete (g : Graph α) (vertices : List α)
    : ∀ e ∈ all_neighbors g vertices, e ∈ g := by
  intro e h₁
  induction vertices <;> simp [all_neighbors] at h₁
  case cons x xs ih =>
    apply Or.elim h₁ <;> intro h₁
    . apply Or.elim h₁ <;> intro h₁
      . have e_start_eq_x := out_edges_start g e x h₁
        simp [←e_start_eq_x] at h₁
        exact out_edges_has_edge g e.start e.finish |>.mp h₁
      . have e_start_eq_x := in_edges_finish g e x h₁
        simp [←e_start_eq_x] at h₁
        exact in_edges_has_edge g e.start e.finish |>.mp h₁
    . exact ih h₁

/- Function and theorems for finding all edges in a graph -/

def toEdges (g : Graph α) : List (Edge α) := all_neighbors g (toVertices g)

theorem toEdges_sound (g : Graph α) : ∀ e ∈ g, e ∈ toEdges g := by
  intro e h₁
  simp [toEdges]
  apply all_neighbors_sound g (toVertices g) e
  apply Or.inl
  rw [toVertices_has_vertex g e.start]
  exact edge_vertices g e.start e.finish h₁ |>.left
  exact h₁

theorem toEdges_complete (g : Graph α) : ∀e ∈ toEdges g, e ∈ g := by
  simp [toEdges]; exact all_neighbors_complete g (toVertices g)

theorem toEdges_iff (g : Graph α) : ∀e, e ∈ g ↔ e ∈ toEdges g := by
  intro e; apply Iff.intro; exact toEdges_sound g e; exact toEdges_complete g e

theorem toEdges_vertices_in_graph (g : Graph α)
    : ∀ e ∈ toEdges g, ∀ v ∈ e, has_vertex g v := by
  intro e h₁ v h₂
  have := edge_vertices g e.start e.finish (toEdges_complete g e h₁)
  simp [←Edge.elem_iff, Edge.elem] at h₂
  apply Or.elim h₂ <;> (intro eq; simp [eq, this])


/- Function and theorems for adding lists of vertices to a graph -/

def add_vertices (g : Graph α) : List α → Graph α
  | [] => g
  | v :: vs => add_vertex (add_vertices g vs) v


/- Function and theorems for removing lists of vertices from a graph -/

def rem_vertices (g : Graph α) : List α → Graph α
  | [] => g
  | v :: vs => rem_vertex (rem_vertices g vs) v


/- Functions and theorems for flipping/reversing edges -/

def reverse_edges : List (Edge α) → List (Edge α) := List.map (·.flip)

theorem in_edges_in_reverse (edges : List (Edge α))
    : ∀ u v, ⟨u, v⟩ ∈ edges → ⟨v, u⟩ ∈ reverse_edges edges := by
  intro u v h₁; simp [reverse_edges]; apply Exists.intro ⟨u, v⟩; simp; exact h₁

theorem in_reverse_in_edges (edges : List (Edge α))
    : ∀ u v, ⟨v, u⟩ ∈ reverse_edges edges → ⟨u, v⟩ ∈ edges := by
  intro u v h₁; simp [reverse_edges] at h₁
  apply Exists.elim h₁; intro e h₂
  simp [←h₂.right.left, ←h₂.right.right]
  exact h₂.left

theorem reverse_pres_vertex (edges : List (Edge α)) (w : α)
    : ∀ u v, ⟨u, v⟩ ∈ edges ∧ w ∈ (Edge.mk u v)
           ↔ ⟨v, u⟩ ∈ reverse_edges edges ∧ w ∈ (Edge.mk v u) := by
  intro u v
  apply Iff.intro <;> (intro h₁; apply And.intro)
  . exact in_edges_in_reverse edges u v h₁.left
  . simp [←Edge.elem_iff, Edge.elem] at *
    exact Or.symm h₁.right
  . exact in_reverse_in_edges edges u v h₁.left
  . simp [←Edge.elem_iff, Edge.elem] at *
    exact Or.symm h₁.right

theorem reverse_toEdge_vertices_in_graph (g : Graph α)
    : ∀ u v, ⟨u, v⟩ ∈ reverse_edges (toEdges g)
           → ∀ w ∈ (Edge.mk u v), has_vertex g w := by
  intro u v h₁ w h₂
  have := in_reverse_in_edges (toEdges g) v u h₁
  exact toEdges_vertices_in_graph _ ⟨v, u⟩ this w (Edge.mem_flip.mp h₂)


/- Making a Digraph into an undirected graph -/

def undirect (g : Graph α)
    : (undirected_g : Graph α) ×' UndirectedGraph undirected_g :=
  let edges := toEdges g
  let rev_edges : List (Edge α) := reverse_edges edges
  let undirected_g := add_edges g rev_edges

  have undirected_edges : ∀ u v, Digraph.has_edge undirected_g ⟨u, v⟩
                               ↔ Digraph.has_edge undirected_g ⟨v, u⟩ := by
    intro u v
    if in_edges : ⟨u, v⟩ ∈ edges then -- todo make this a helper
      have in_rev_edges := (in_edges_in_reverse edges) u v in_edges
      have in_edges := toEdges_complete g ⟨u, v⟩ in_edges
      apply Iff.intro <;> intro _h₁
      . exact add_edges_adds g rev_edges ⟨v, u⟩ in_rev_edges
      . exact add_edges_pres_existing_edge g rev_edges ⟨u, v⟩ in_edges
    else if rev_in_edges : ⟨v, u⟩ ∈ edges then
      have in_rev_edges := (in_edges_in_reverse edges) v u rev_in_edges
      have rev_in_edges := toEdges_complete g ⟨v, u⟩ rev_in_edges
      apply Iff.intro <;> intro _h₁
      . exact add_edges_pres_existing_edge g rev_edges ⟨v, u⟩ rev_in_edges
      . exact add_edges_adds g rev_edges ⟨u, v⟩ in_rev_edges
    else
      apply Iff.intro <;> intro h₁
      . have := add_edges_in_list_or_graph g rev_edges ⟨u, v⟩ h₁
        apply Or.elim this <;> intro h₂
        . have := (in_reverse_in_edges edges) v u h₂; contradiction
        . have := toEdges_sound g ⟨u, v⟩ h₂; contradiction
      . have := add_edges_in_list_or_graph g rev_edges ⟨v, u⟩ h₁
        apply Or.elim this <;> intro h₂
        . have := (in_reverse_in_edges edges) u v h₂; contradiction
        . have := toEdges_sound g ⟨v, u⟩ h₂; contradiction

  ⟨undirected_g, UndirectedGraph.mk undirected_edges⟩

theorem undirect_pres_vertex (g : Graph α)
    : ∀ v, has_vertex g v ↔ has_vertex (undirect g).fst v := by
  intro v
  simp [undirect]
  apply Iff.intro <;> intro h₁
  . exact add_edges_pres_existing_vertex _ _ v h₁
  . have := add_edges_adds g (reverse_edges (toEdges g))
    if v_in : (reverse_edges (toEdges g)) |>.any (v ∈ ·) then
      simp at v_in
      apply Exists.elim v_in; intro e h₂
      exact reverse_toEdge_vertices_in_graph g
        e.start e.finish h₂.left v h₂.right
    else
      simp [←Edge.elem_iff, Edge.elem] at v_in
      have : ∀ (e : Edge α), e ∈ _ → v ≠ e.start ∧ v ≠ e.finish :=
        (fun e in_e => by
          apply And.intro <;> (intro h; apply (v_in e in_e))
          exact Or.inl h; exact Or.inr h
        )
      exact add_edges_pres_vertex g (reverse_edges (toEdges g)) v this |>.mpr h₁

theorem undirect_pres_edge (g : Graph α) : ∀ e ∈ g, e ∈ (undirect g).fst := by
  intro e h₁; simp [undirect]; exact add_edges_pres_existing_edge g _ e h₁


/- Misc utility functions -/

nonrec def toString [ToString α] (g : Graph α) : String :=
  Digraph.toVertices g
  |>.map (fun v =>
    let next := succ g v |>.map toString
    s!"{v} | {next}"
    )
  |> String.intercalate "\n"
instance [ToString α] : ToString (Graph α) := ⟨toString⟩

def vertices_toEdges : List α → List (Edge α)
  | []         => []
  | _::[]      => []
  | v₁::v₂::[] => ⟨v₁,v₂⟩ :: []
  | v₁::v₂::vs => ⟨v₁,v₂⟩ :: vertices_toEdges (v₂::vs)

def vertices_toEdges' (g : Graph α) : List α → Option (List (Edge α))
  | [] => .none
  | _::[] => .none
  | vs =>
    let es := vertices_toEdges vs
    if es.all (Digraph.has_edge g) then .some es else .none

end Digraph

namespace UndirectedGraph

def empty : UndirectedGraph (Digraph.empty : Graph α) :=
  ⟨by intro u v
      have uv := Digraph.empty_edges (α:=α) (T := Graph) ⟨u, v⟩
      have vu := Digraph.empty_edges (α:=α) (T := Graph) ⟨v, u⟩
      apply Iff.intro <;> (intro h; contradiction)
  ⟩


end UndirectedGraph
