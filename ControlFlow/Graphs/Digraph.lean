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

@[simp] theorem Edge.elem_iff [DecidableEq α] {v : α} {e : Edge α}
    : Edge.elem v e = true ↔ v ∈ e :=
  ⟨ by simp only [Membership.mem, imp_self]
  , by simp only [Membership.mem, imp_self]
  ⟩

@[reducible, simp] def Edge.flip (e : Edge α) : Edge α := ⟨e.finish, e.start⟩

@[simp] theorem Edge.flip_flip (e : Edge α) : e.flip.flip = e := by
  simp only [flip]

@[simp] theorem Edge.flip_symm {e₁ e₂ : Edge α}
    : e₁.flip = e₂ ↔ e₁ = e₂.flip := by
  let ⟨start₁, finish₁⟩ := e₁
  let ⟨start₂, finish₂⟩ := e₂
  simp only [flip, mk.injEq]
  exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩

@[simp] theorem Edge.flip_inj (e₁ e₂ : Edge α)
    : e₁.flip = e₂.flip → e₁ = e₂ := by
  let ⟨start₁, finish₁⟩ := e₁
  let ⟨start₂, finish₂⟩ := e₂
  simp only [flip, mk.injEq]
  exact fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩

@[simp] theorem Edge.mem_flip {w : α} {e: Edge α} : w ∈ e.flip ↔ w ∈ e := by
  simp only [flip, ← elem_iff, elem, Bool.or_eq_true, decide_eq_true_eq]
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

@[reducible] def Digraph.Oriented [Digraph α Graph] (g : Graph α) : Prop :=
  ∀ u v, ⟨u, v⟩ ∈ g → ⟨v, u⟩ ∉ g

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

namespace Digraph

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

theorem add_edge_in_in_pres_vertices (g : Graph α) (e : Edge α)
    (start_in : has_vertex g e.start)
    (finish_in : has_vertex g e.finish)
    : ∀ v, has_vertex g v ↔ has_vertex (add_edge g e) v := by
  intro v; apply Iff.intro
  . exact add_edge_pres_existing_vertex g e v
  . intro h₁
    if eq_s : v = e.start then simp [eq_s]; exact start_in else
    if eq_f : v = e.finish then simp [eq_f]; exact finish_in else
    exact add_edge_pres_vertex g v _ _ eq_s eq_f |>.mpr h₁

theorem add_edge_in_out_pres_vertices (g : Graph α) (e : Edge α)
    (start_in : has_vertex g e.start)
    : ∀ v, v ≠ e.finish → has_vertex (add_edge g e) v → has_vertex g v := by
  intro v neq_f h₁
  if eq_s : v = e.start then simp [eq_s]; exact start_in else
  exact add_edge_pres_vertex g _ _ _ eq_s neq_f |>.mpr h₁

theorem add_edge_out_in_pres_vertices (g : Graph α) (e : Edge α)
    (finish_in : has_vertex g e.finish)
    : ∀ v, v ≠ e.start → has_vertex (add_edge g e) v → has_vertex g v := by
  intro v neq_s h₁
  if eq_f : v = e.finish then simp [eq_f]; exact finish_in else
  exact add_edge_pres_vertex g _ _ _ neq_s eq_f |>.mpr h₁

theorem add_edge_new_start_antisymm (g : Graph α) (u : α)
    (u_not_in : ¬has_vertex g u)
    : ∀ v w, ⟨u, w⟩ ∈ add_edge g ⟨u, v⟩ → v = w := by
  intro v w e_in
  apply Or.elim (add_edge_eq_or_in g ⟨u, w⟩ ⟨u, v⟩ e_in) <;> intro h₁
  . exact Edge.mk.inj h₁ |>.right |>.symm
  . have := edge_vertices g u w h₁ |>.left |> u_not_in
    contradiction

theorem add_edge_new_finish_antisymm (g : Graph α) (u : α)
    (u_not_in : ¬has_vertex g u)
    : ∀ v w, ⟨w, u⟩ ∈ add_edge g ⟨v, u⟩ → v = w := by
  intro v w e_in
  apply Or.elim (add_edge_eq_or_in g ⟨w, u⟩ ⟨v, u⟩ e_in) <;> intro h₁
  . exact Edge.mk.inj h₁ |>.left |>.symm
  . have := edge_vertices g w u h₁ |>.right |> u_not_in
    contradiction

theorem add_edge_new_start_no_in_edge (g : Graph α) (u : α)
    (u_not_in : ¬has_vertex g u)
    : ∀ v w, u ≠ v → ⟨w, u⟩ ∉ add_edge g ⟨u, v⟩ := by
  intro v w uv_neq wu_in
  exact add_edge_pres_edges g ⟨w, u⟩ ⟨u, v⟩ (by simp; intro _; exact uv_neq)
    |>.mpr wu_in |> edge_vertices g w u |>.right |> u_not_in

theorem add_edge_new_finish_no_out_edge (g : Graph α) (u : α)
    (u_not_in : ¬has_vertex g u)
    : ∀ v w, u ≠ v → ⟨u, w⟩ ∉ add_edge g ⟨v, u⟩ := by
  intro v w uv_neq uw_in
  exact add_edge_pres_edges g ⟨u, w⟩ ⟨v, u⟩
    (by simp; intro eq; have := uv_neq eq; contradiction)
    |>.mpr uw_in |> edge_vertices g u w |>.left |> u_not_in

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

theorem add_vertex_no_edges (g : Graph α)
    : ∀ u, ¬has_vertex g u → ∀ v, ⟨u, v⟩ ∉ add_vertex g u
                                ∧ ⟨v, u⟩ ∉ add_vertex g u := by
  intro u u_not_in v
  apply And.intro <;> intro e_in
  . exact add_vertex_pres_edges g u _ |>.mpr e_in
      |> edge_vertices g _ _ |>.left |> u_not_in
  . exact add_vertex_pres_edges g u _ |>.mpr e_in
      |> edge_vertices g _ _ |>.right |> u_not_in

theorem rem_edge_pres_nonexisting_edge (g : Graph α)
    : ∀ e₁ e₂, e₁ ∉ g → e₁ ∉ rem_edge g e₂ := by
  intro e₁ e₂ h₁
  if eq : e₁ = e₂ then rw [eq]; exact rem_edge_removes g e₂ else
    intro h₂; apply h₁
    exact rem_edge_pres_edges g e₁ e₂ eq |>.mpr h₂

theorem in_rem_edge_neq (g : Graph α)
    : ∀ e₁ e₂, e₁ ∈ rem_edge g e₂ → e₁ ≠ e₂ := by
  intro e₁ e₂ h₁ eq; rw [eq] at h₁; exact rem_edge_removes g e₂ h₁

theorem rem_edge_eq_or_not_in (g : Graph α)
    : ∀ e₁ e₂, e₁ ∉ rem_edge g e₂ → e₁ = e₂ ∨ e₁ ∉ g := by
  intro e₁ e₂ h₁
  if eq : e₁ = e₂ then exact Or.inl eq else
    apply Or.inr; intro h₂; apply h₁
    exact rem_edge_pres_edges g e₁ e₂ eq |>.mp h₂

theorem rem_vertex_pres_nonexisting_edge (g : Graph α)
    : ∀ v e, e ∉ g → e ∉ rem_vertex g v := by
  intro v e h₁ h₂
  if eq_s : v = e.start
  then rw [eq_s] at h₂; exact rem_vertex_removes_edge g _ _ |>.right h₂
  else if eq_f : v = e.finish
  then rw [eq_f] at h₂; exact rem_vertex_removes_edge g _ _ |>.left h₂
  else apply h₁; exact rem_vertex_pres_edges g v _ _ eq_s eq_f |>.mpr h₂

theorem rem_vertex_pres_nonexisting_vertex (g : Graph α)
    : ∀ u v, ¬has_vertex g u → ¬has_vertex (rem_vertex g v) u := by
  intro u v h₁
  if eq : u = v
  then rw [eq]; exact rem_vertex_removes_vertex g v
  else exact rem_vertex_pres_vertex g u v eq |> Iff.not |>.mp h₁

theorem in_rem_vertex_neq (g : Graph α)
    : ∀ u v, has_vertex (rem_vertex g v) u → u ≠ v := by
  intro u v h₁ eq; simp [eq, rem_vertex_removes_vertex] at h₁

theorem rem_vertex_eq_or_not_in (g : Graph α)
    : ∀ u v, ¬has_vertex (rem_vertex g v) u → u = v ∨ ¬has_vertex g u := by
  intro u v h₁
  if eq : u = v then exact Or.inl eq else
    apply Or.inr; intro h₂; apply h₁
    exact rem_vertex_pres_vertex g u v eq |>.mp h₂

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

theorem no_edge_no_succ {g : Graph α}
    : ∀ u, (∀ v, ⟨u, v⟩ ∉ g) → (∀ v, v ∉ succ g u) := by
  intro u e_not_in v v_in_s; exact e_not_in v (succ_edge_in_graph.mp v_in_s)


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

theorem no_edge_no_pred {g : Graph α}
    : ∀ u, (∀ v, ⟨v, u⟩ ∉ g) → (∀ v, v ∉ pred g u) := by
  intro u e_not_in v v_in_s; exact e_not_in v (pred_edge_in_graph.mp v_in_s)


theorem in_succ_iff_in_pred {g : Graph α} {u v : α}
    : u ∈ succ g v ↔ v ∈ pred g u :=
  Iff.intro
    (fun h => succ_edge_in_graph.mp h |> pred_edge_in_graph.mpr)
    (fun h => pred_edge_in_graph.mp h |> succ_edge_in_graph.mpr)


/- Neighbor theorems -/
theorem neighbors_edge_in_graph {g : Graph α} {u v : α}
    : v ∈ neighbors g u ↔ ⟨u, v⟩ ∈ g ∨ ⟨v, u⟩ ∈ g := by
  simp [neighbors]
  apply Iff.intro <;> intro h₁
  . exact Or.imp succ_edge_in_graph.mp pred_edge_in_graph.mp
      (List.mem_union_iff.mp h₁)
  . apply List.mem_union_iff.mpr
    exact Or.imp succ_edge_in_graph.mpr pred_edge_in_graph.mpr h₁

theorem neighbors_in_graph {g : Graph α} {u v : α} (h₁ : v ∈ neighbors g u)
    : has_vertex g v := by
  apply Or.elim (neighbors_edge_in_graph.mp h₁) <;> intro h₂
  . exact edge_vertices g u v h₂ |>.right
  . exact edge_vertices g v u h₂ |>.left


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
    rw [add_edges]
    cases h₁
    case head => exact add_edge_adds (add_edges g xs) e
    case tail _ h₂ =>
      if h₃ : e = x then rw [h₃]; exact add_edge_adds (add_edges g xs) x else
        apply add_edge_pres_edges (add_edges g xs) e x h₃ |>.mp
        exact ih h₂

theorem add_edges_pres_edges (g : Graph α) (edges : List (Edge α))
    : ∀ e, e ∉ edges → (has_edge g e ↔ has_edge (add_edges g edges) e) := by
  intro e h₁
  induction edges
  case nil => simp only [add_edges]
  case cons x xs ih =>
    if h₂ : e = x then
      simp only [h₂, List.mem_cons, true_or, not_true_eq_false] at h₁
    else
      rw [ih (List.not_mem_of_not_mem_cons h₁)]
      exact add_edge_pres_edges (add_edges g xs) e x h₂

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

theorem add_edges_pres_vertex_not_in (g : Graph α) (edges : List (Edge α))
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

theorem add_edges_pres_vertex (g : Graph α) (edges : List (Edge α))
    : ∀ u, (∀ e ∈ edges, (u ≠ e.start ∧ u ≠ e.finish) ∨ g |= u)
         → (has_vertex g u ↔ has_vertex (add_edges g edges) u) := by
  intro u not_eq
  apply Iff.intro
  . exact add_edges_pres_existing_vertex g edges u
  . intro h₁
    induction edges <;> simp [add_edges] at *
    case nil => exact h₁
    case cons x xs ih =>
      apply Or.elim not_eq.left
      . intro h₂; apply ih not_eq.right
        exact add_edge_pres_vertex _ u _ _ h₂.left h₂.right |>.mpr h₁
      . simp


/- Function and theorems for removing lists of edges -/

def rem_edges (g : Graph α) : List (Edge α) → Graph α
  | [] => g
  | e :: es => rem_edge (rem_edges g es) e

theorem rem_edges_removes (g : Graph α) (edges : List (Edge α))
    : ∀ e ∈ edges, ¬has_edge (rem_edges g edges) e := by
  intro e h₁
  induction edges
  case nil => contradiction
  case cons x xs ih =>
    rw [rem_edges]
    cases h₁
    case head => exact rem_edge_removes (rem_edges g xs) e
    case tail _ h₂ =>
      if eq : e = x then rw [eq]; exact rem_edge_removes (rem_edges g xs) x else
        intro h₄
        apply ih h₂
        exact rem_edge_pres_edges (rem_edges g xs) e x eq |>.mpr h₄

theorem rem_edges_pres_edges (g : Graph α) (edges : List (Edge α))
    : ∀ e, e ∉ edges → (has_edge g e ↔ has_edge (rem_edges g edges) e) := by
  intro e h₁
  induction edges
  case nil => simp only [rem_edges]
  case cons x xs ih =>
    if h₂ : e = x then
      simp only [h₂, List.mem_cons, true_or, not_true_eq_false] at h₁
    else
      rw [ih (List.not_mem_of_not_mem_cons h₁)]
      exact rem_edge_pres_edges (rem_edges g xs) e x h₂

theorem rem_edges_pres_nonexisting_edge (g : Graph α) (edges : List (Edge α))
    : ∀ e, e ∉ g → e ∉ rem_edges g edges := by
  intro e h₁
  if e_in : e ∈ edges then exact rem_edges_removes g edges e e_in else
    intro h₂; apply h₁
    exact rem_edges_pres_edges g edges e e_in |>.mpr h₂

theorem in_rem_edges_not_in (g : Graph α) (edges : List (Edge α))
    : ∀ e, e ∈ rem_edges g edges → e ∉ edges := by
  intro e h₁ h₂; exact rem_edges_removes g edges e h₂ h₁

theorem rem_edges_in_list_or_not_graph (g : Graph α) (edges : List (Edge α))
    : ∀ e, e ∉ rem_edges g edges → e ∈ edges ∨ e ∉ g := by
  intro e h₁
  if e_in : e ∈ edges then exact Or.inl e_in else
    apply Or.inr; intro h₂; apply h₁
    exact rem_edges_pres_edges g edges e e_in |>.mp h₂

theorem rem_edges_pres_vertex (g : Graph α) (edges : List (Edge α))
    : ∀ u, has_vertex g u ↔ has_vertex (rem_edges g edges) u := by
  intro u
  induction edges
  case nil => simp only [rem_edges]
  case cons x xs ih =>
    simp only [
      ih,
      rem_edge_pres_vertex (rem_edges g xs) u x.start x.finish,
      rem_edges
    ]


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
      apply List.mem_union_iff.mpr
      apply Or.inl
      apply List.mem_union_iff.mpr
      apply Or.inl
      simp [x_eq_start]
      exact (out_edges_has_edge g e.start e.finish).mpr h₂
    else if x_eq_finish : x = e.finish then
      apply List.mem_union_iff.mpr
      apply Or.inl
      apply List.mem_union_iff.mpr
      apply Or.inr
      simp [x_eq_finish]
      exact (in_edges_has_edge g e.start e.finish).mpr h₂
    else
      apply Or.elim h₁ <;> intro h₁
      . simp [neq_symm x_eq_start] at h₁
        apply List.mem_union_iff.mpr
        exact Or.inr (ih (Or.inl h₁))
      . simp [neq_symm x_eq_finish] at h₁
        apply List.mem_union_iff.mpr
        exact Or.inr (ih (Or.inr h₁))

theorem all_neighbors_complete (g : Graph α) (vertices : List α)
    : ∀ e ∈ all_neighbors g vertices, e ∈ g := by
  intro e h₁
  induction vertices <;> simp [all_neighbors] at h₁
  case cons x xs ih =>
    apply Or.elim (List.mem_union_iff.mp h₁) <;> intro h₁
    . apply Or.elim (List.mem_union_iff.mp h₁) <;> intro h₁
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

@[simp] theorem toEdges_iff (g : Graph α) : ∀e, e ∈ toEdges g ↔ e ∈ g := by
  intro e; apply Iff.intro; exact toEdges_complete g e; exact toEdges_sound g e

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

theorem add_vertices_adds (g : Graph α) (vertices : List α)
    : ∀ v ∈ vertices, has_vertex (add_vertices g vertices) v := by
  intro v h₁
  induction vertices <;> simp [add_vertices]
  case nil => contradiction
  case cons x xs ih =>
    cases h₁
    case head => exact add_vertex_adds _ v
    case tail h₁ => exact add_vertex_pres_existing_vertex _ v x (ih h₁)

theorem add_vertices_pres_edges (g : Graph α) (vertices : List α)
    : ∀ e, e ∈ g ↔ has_edge (add_vertices g vertices) e := by
  intro e
  induction vertices <;> simp [add_vertices]
  case nil => simp [has_edge_membership]
  case cons x xs ih =>
    simp [ih, add_vertex_pres_edges (add_vertices g xs) x e]

theorem add_vertices_pres_vertex (g : Graph α) (vertices : List α)
    : ∀ v, v ∉ vertices
         → (has_vertex g v ↔ has_vertex (add_vertices g vertices) v) := by
  intro v h₁
  induction vertices
  case nil => simp only [add_vertices]
  case cons x xs ih =>
    if eq : v = x then
      simp only [eq, List.mem_cons, true_or, not_true_eq_false] at h₁
    else
      rw [ ih (List.not_mem_of_not_mem_cons h₁)
         , add_vertex_pres_vertex _ v x eq
         , add_vertices
         ]

theorem add_vertices_pres_existing_vertex (g : Graph α) (vertices : List α)
    : ∀ v, has_vertex g v → has_vertex (add_vertices g vertices) v := by
  intro v h₁
  induction vertices <;> simp [add_vertices]
  case nil => exact h₁
  case cons x xs ih => exact add_vertex_pres_existing_vertex _ v x ih

theorem add_vertices_in_list_or_graph (g : Graph α) (vertices : List α)
    : ∀ v, has_vertex (add_vertices g vertices) v
         → v ∈ vertices ∨ has_vertex g v := by
  intro v h₁
  if v_in : v ∈ vertices
  then exact Or.inl v_in
  else apply Or.inr; exact add_vertices_pres_vertex g vertices v v_in |>.mpr h₁


/- Function and theorems for removing lists of vertices from a graph -/

def rem_vertices (g : Graph α) : List α → Graph α
  | [] => g
  | v :: vs => rem_vertex (rem_vertices g vs) v

theorem rem_vertices_removes_vertex (g : Graph α) (vertices : List α)
    : ∀ v ∈ vertices, ¬has_vertex (rem_vertices g vertices) v := by
  intro v h₁ h₂
  induction vertices <;> simp [rem_vertices] at *
  case cons x xs ih =>
    if eq : v = x then
      rw [eq] at h₂; exact rem_vertex_removes_vertex _ x h₂
    else
      simp [eq] at h₁
      have := rem_vertex_pres_vertex (rem_vertices g xs) v x eq |>.mpr h₂
      simp [ih h₁] at this

theorem rem_vertices_removes_edge (g : Graph α) (vertices : List α)
    : ∀ u, ∀ v ∈ vertices, ⟨u, v⟩ ∉ rem_vertices g vertices
                         ∧ ⟨v, u⟩ ∉ rem_vertices g vertices := by
  intro u v h₁
  induction vertices <;> simp [rem_vertices] at *
  case cons x xs ih =>
    apply Or.elim h₁ <;> intro h₁
    . simp [h₁] at *
      exact rem_vertex_removes_edge _ u x
    . apply And.intro
      . exact rem_vertex_pres_nonexisting_edge _ x _ (ih h₁).left
      . exact rem_vertex_pres_nonexisting_edge _ x _ (ih h₁).right

theorem rem_vertices_pres_edges (g : Graph α) (vertices : List α)
    : ∀ u v, u ∉ vertices → v ∉ vertices
           → (⟨u, v⟩ ∈ g ↔ ⟨u, v⟩ ∈ rem_vertices g vertices) := by
  intro u v h₁ h₂
  induction vertices <;> simp [rem_vertices]
  case cons x xs ih =>
    if eq_xu : x = u then simp [eq_xu] at h₁ else
    if eq_xv : x = v then simp [eq_xv] at h₂ else
      have h₁ := List.not_mem_of_not_mem_cons h₁
      have h₂ := List.not_mem_of_not_mem_cons h₂
      rw [ih h₁ h₂]
      exact rem_vertex_pres_edges _ x u v eq_xu eq_xv

theorem rem_vertices_pres_vertex (g : Graph α) (vertices : List α)
    : ∀ v, v ∉ vertices
         → (has_vertex g v ↔ has_vertex (rem_vertices g vertices) v) := by
  intro v h₁
  induction vertices
  case nil => simp only [rem_vertices]
  case cons x xs ih =>
    if eq : v = x then
      simp only [eq, List.mem_cons, true_or, not_true_eq_false] at h₁
    else
      rw [ih (List.not_mem_of_not_mem_cons h₁)]
      exact rem_vertex_pres_vertex _ _ _ eq

theorem rem_vertices_pres_nonexisting_edge (g : Graph α) (vertices : List α)
    : ∀ e, e ∉ g → e ∉ rem_vertices g vertices := by
  intro e h₁ h₂
  induction vertices <;> simp [rem_vertices] at *
  case nil => contradiction
  case cons x xs ih => exact rem_vertex_pres_nonexisting_edge _ x e ih h₂

theorem rem_vertices_pres_nonexisting_vertex (g : Graph α) (vertices : List α)
    : ∀ v, ¬has_vertex g v → ¬has_vertex (rem_vertices g vertices) v := by
  intro v h₁ h₂
  induction vertices <;> simp [rem_vertices] at *
  case nil => simp [h₂] at h₁
  case cons x xs ih =>
    if eq : v = x
    then simp [eq, rem_vertex_removes_vertex (rem_vertices g xs) x] at h₂
    else
      have := rem_vertex_pres_vertex _ _ _ eq |>.mpr h₂
      simp [ih] at this

theorem in_rem_vertices_neq (g : Graph α) (vertices : List α)
    : ∀ v, has_vertex (rem_vertices g vertices) v → v ∉ vertices := by
  intro v h₁ h₂
  induction vertices <;> rw [rem_vertices] at *
  case nil => contradiction
  case cons x xs ih =>
    if eq : v = x then
      simp [eq, rem_vertex_removes_vertex (rem_vertices g xs) x] at h₁
    else
      apply rem_vertex_pres_vertex _ _ _ eq |>.mpr h₁ |> ih
      exact List.mem_of_ne_of_mem eq h₂

theorem rem_vertices_in_list_or_not_graph (g : Graph α) (vertices : List α)
    : ∀ v, ¬has_vertex (rem_vertices g vertices) v
         → v ∈ vertices ∨ ¬has_vertex g v := by
  intro v h₁
  induction vertices <;> rw [rem_vertices] at *
  case nil => simp at *; exact h₁
  case cons x xs ih =>
    if eq : v = x then simp [eq] else
      simp only [eq, List.find?, List.mem_cons, eq, false_or]
      exact rem_vertex_pres_vertex _ _ _ eq |> Iff.not |>.mpr h₁ |> ih


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


/- Merging graphs -/

def merge (g₁ g₂ : Graph α) : Graph α :=
  let g₁_vertices := Digraph.toVertices g₁
  let g₁_edges    := Digraph.toEdges g₁
  Digraph.add_edges (Digraph.add_vertices g₂ g₁_vertices) g₁_edges

theorem merge_has_edge {g₁ g₂ : Graph α} {e : Edge α}
    : e ∈ merge g₁ g₂ ↔ e ∈ g₁ ∨ e ∈ g₂ := by
  simp [merge]; apply Iff.intro <;> intro h₁
  . rw [ ←toEdges_iff
       , add_vertices_pres_edges g₂ _ e
       ]
    exact add_edges_in_list_or_graph _ _ e h₁
  . apply Or.elim h₁ <;> intro h₁
    . exact add_edges_adds _ _ e (toEdges_iff g₁ e |>.mpr h₁)
    . exact add_edges_pres_existing_edge _ _ e
        (add_vertices_pres_edges g₂ _ e |>.mp h₁)

theorem merge_has_vertex {g₁ g₂ : Graph α} {u : α}
    : has_vertex (merge g₁ g₂) u ↔ has_vertex g₁ u ∨ has_vertex g₂ u := by
  simp [merge]; apply Iff.intro <;> intro h₁
  . rw [←toVertices_has_vertex]
    apply add_vertices_in_list_or_graph g₂ (toVertices g₁) u
    have in_g₁ := add_vertices_adds g₂ _ u ∘ (toVertices_has_vertex g₁ u).mpr
    exact add_edges_pres_vertex _ _ u (fun e e_in => by
        if us_eq : u = e.start then
          apply Or.inr ∘ in_g₁; simp [us_eq]
          exact toEdges_iff _ _ |>.mp e_in |> edge_vertices _ _ _ |>.left
        else if uf_eq : u = e.finish then
          apply Or.inr ∘ in_g₁; simp [uf_eq]
          exact toEdges_iff _ _ |>.mp e_in |> edge_vertices _ _ _ |>.right
        else exact Or.inl (And.intro us_eq uf_eq)
      ) |>.mpr h₁
  . apply Or.elim h₁ <;> intro h₁
    . apply add_edges_pres_existing_vertex _ _ u
      exact add_vertices_adds g₂ _ u (toVertices_has_vertex g₁ u |>.mpr h₁)
    . apply add_edges_pres_existing_vertex _ _ u
      exact add_vertices_pres_existing_vertex g₂ _ u h₁

theorem merge_has_edge_comm {g₁ g₂ : Graph α} {e : Edge α}
    : e ∈ merge g₁ g₂ ↔ e ∈ merge g₂ g₁ := by
  simp [merge_has_edge]; apply Iff.intro <;> (intro h; exact Or.symm h)

theorem merge_has_vertex_comm {g₁ g₂ : Graph α} {u : α}
    : has_vertex (merge g₁ g₂) u ↔ has_vertex (merge g₂ g₁) u := by
  simp [merge_has_vertex]; apply Iff.intro <;> (intro h; exact Or.symm h)


/- Vertices type -/

def Vertices (g : Graph α) := {v : α // has_vertex g v}

instance {g : Graph α} : DecidableEq (Vertices g) :=
  fun u v =>
    match decEq u.val v.val with
    | isFalse h₁ => isFalse (fun h₂ => h₁ (Subtype.val_inj.mpr h₂))
    | isTrue  h₁ => isTrue (Subtype.eq h₁)

instance {g : Graph α} {w : α}
    : Coe (Vertices g) (Vertices (add_vertex g w)) where
  coe v := ⟨v.val, add_vertex_pres_existing_vertex g v.val w v.property⟩

instance {g : Graph α} {e : Edge α}
    : Coe (Vertices g) (Vertices (add_edge g e)) where
  coe v := ⟨v.val, add_edge_pres_existing_vertex g e v.val v.property⟩


/- Coercions for various graph operations -/

instance {g : Graph α} {e₁ e₂ : Edge α}
    : Coe (e₁ ∈ g) (e₁ ∈ add_edge g e₂) :=
  ⟨add_edge_pres_existing_edge g e₁ e₂⟩

instance {g : Graph α} {e : Edge α} {v : α}
    : Coe (has_vertex g v) (has_vertex (add_edge g e) v) :=
  ⟨add_edge_pres_existing_vertex g e v⟩

instance {g : Graph α } {e : Edge α} {v : α}
    : Coe (e ∈ g) (e ∈ add_vertex g v) :=
  ⟨add_vertex_pres_edges g v e |>.mp⟩

instance {g : Graph α} {v₁ v₂ : α}
    : Coe (has_vertex g v₁) (has_vertex (add_vertex g v₂) v₁) :=
  ⟨add_vertex_pres_existing_vertex g v₁ v₂⟩


/- Misc utility functions -/

@[reducible, simp] def trivial (v : α) : Graph α := add_vertex empty v

theorem trivial_vertex_eq
    : ∀ u v, has_vertex (trivial v : Graph α) u → u = v := by
  intro u v h
  if eq : u = v then exact eq else
  have := add_vertex_pres_vertex (empty : Graph α) u v eq |>.mpr h
    |> empty_vertex u
  contradiction

theorem trivial_no_edge (v : α)
    : ∀ e, e ∉ (trivial v : Graph α) := by
  intro e h₁
  simp at h₁
  exact add_vertex_pres_edges (empty : Graph α) v e
    |> Iff.not |>.mp (empty_edges e) h₁

def of_succ (vertices : List α) (succ : α → List α) : Graph α :=
  add_edges (add_vertices empty vertices)
            (vertices.bind (fun v => succ v |>.map (v, ·)))

def of_pred (vertices : List α) (pred : α → List α) : Graph α :=
  add_edges (add_vertices empty vertices)
            (vertices.bind (fun v => pred v |>.map (·, v)))

theorem of_succ_vertices_in {v : α} {vertices : List α} {succ : α → List α}
    : v ∈ vertices → has_vertex (of_succ vertices succ : Graph α) v :=
  add_edges_pres_existing_vertex _ _ v ∘ add_vertices_adds _ _ v

theorem of_pred_vertices_in {v : α} {vertices : List α} {succ : α → List α}
    : v ∈ vertices → has_vertex (of_pred vertices succ : Graph α) v :=
  add_edges_pres_existing_vertex _ _ v ∘ add_vertices_adds _ _ v

def verticesToString [ToString α]
    (vertices : List α)
    (succ : α → List α)
    (spacer := "\n")
    : String :=
  vertices.map (fun v => s!"{v} | {succ v |>.map toString}")
  |> String.intercalate spacer

nonrec def toString [ToString α] (g : Graph α) : String :=
  "Digraph:\n\t".append (
    verticesToString (toVertices g) (succ g) (spacer := "\n\t")
  )
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
