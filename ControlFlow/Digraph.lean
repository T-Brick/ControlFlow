import ControlFlow.AuxDefs

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
  ⟨by simp [Membership.mem], by simp [Membership.mem]⟩

instance [ToString α] : ToString (Edge α) where
  toString e := s!"({e.start}, {e.finish})"

/- Properties that we care about (according to 210)
    - [ ] map over vertices/edges (not implemented yet, idk what the invariants would be)
    - [x] degree of vertex (not directly implemented)
    - [x] determine if edge is in graph
    - [x] insert/delete a vertex or an edge
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
  add_edge_adds             : ∀ g u v, has_edge (add_edge g ⟨u, v⟩) ⟨u, v⟩
  add_edge_pres_edges       : ∀ g e₁ e₂, e₁ ≠ e₂ → (has_edge g e₁ ↔ has_edge (add_edge g e₂) e₁)
  add_edge_pres_vertex      : ∀ g u v w, u ≠ v → u ≠ w → (has_vertex g u ↔ has_vertex (add_edge g ⟨v, w⟩) u)
  rem_edge_removes          : ∀ g e, ¬has_edge (rem_edge g e) e
  rem_edge_pres_edges       : ∀ g e₁ e₂, e₁ ≠ e₂ → (has_edge g e₁ ↔ has_edge (rem_edge g e₂) e₁)
  rem_edge_pres_vertex      : ∀ g u v w, (has_vertex g u ↔ has_vertex (rem_edge g ⟨v, w⟩) u)
  add_vertex_has_vertex     : ∀ g v, has_vertex (add_vertex g v) v
  add_vertex_pres_edges     : ∀ g v e, has_edge g e ↔ has_edge (add_vertex g v) e
  add_vertex_pres_vertex    : ∀ g u v, u ≠ v → (has_vertex g v ↔ has_vertex (add_vertex g u) v)
  rem_vertex_removes_vertex : ∀ g v, ¬has_vertex (rem_vertex g v) v
  rem_vertex_removes_edge   : ∀ g u v, (¬has_edge (rem_vertex g v) ⟨u, v⟩) ∧ (¬has_edge (rem_vertex g v) ⟨v, u⟩)
  rem_vertex_pres_edges     : ∀ g u v w, u ≠ v → u ≠ w → (has_edge g ⟨v, w⟩ ↔ has_edge (rem_vertex g u) ⟨v, w⟩)
  rem_vertex_pres_vertex    : ∀ g u v, u ≠ v → (has_vertex g v ↔ has_vertex (rem_vertex g u) v)
  out_edges_has_edge        : ∀ g u v, ⟨u, v⟩ ∈ (out_edges g u) ↔ has_edge g ⟨u, v⟩
  out_edges_start           : ∀ g e u, e ∈ (out_edges g u) → e.start = u
  in_edges_has_edge         : ∀ g u v, ⟨u, v⟩ ∈ (in_edges g v) ↔ has_edge g ⟨u, v⟩
  in_edges_finish           : ∀ g e v, e ∈ (in_edges g v) → e.finish = v
  toVertices_has_vertex     : ∀ g v, v ∈ toVertices g ↔ has_vertex g v

namespace Digraph

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

instance : Membership (Edge α) (Graph α) := ⟨fun e g => has_edge g e⟩

theorem has_edge_membership (g : Graph α) (e : Edge α)
  : has_edge g e ↔ e ∈ g := by simp [Membership.mem]

def succ (g : Graph α) (v : α) : List α :=
  Digraph.out_edges g v |>.map (·.finish)
def pred (g : Graph α) (v : α) : List α :=
  Digraph.in_edges g v |>.map (·.start)
def neighbors (g : Graph α) (v : α) : List α :=
  List.union (succ g v) (pred g v)


notation:50 g:51 " |= " v:51 => has_vertex g v
notation:50 g:51 " |= N⁺( " v:51 " ) " => succ g v
notation:50 g:51 " |= N⁻( " v:51 " ) " => pred g v
notation:50 g:51 " |= N( "  v:51 " ) " => neighbors g v

theorem succ_has_edge (g : Graph α) (u v : α)
    : v ∈ succ g u ↔ ⟨u, v⟩ ∈ out_edges g u := by
  apply Iff.intro <;> intro h₁ <;> simp [succ] at *
  . apply Exists.elim h₁
    intro e h₂
    have h₃ := out_edges_start g e u h₂.left
    simp [←h₃, ←h₂.right] at *
    exact h₂
  . apply Exists.intro ⟨u, v⟩; simp [*]

theorem succ_edge_in_graph (g : Graph α) (u v : α) (h : v ∈ succ g u) : ⟨u, v⟩ ∈ g :=
  succ_has_edge g u v |>.mp h |> (out_edges_has_edge g u v |>.mp)

theorem succ_in_graph (g : Graph α) (u v : α) (h : v ∈ succ g u) : has_vertex g v :=
  (succ_edge_in_graph g u v h) |> (edge_vertices g u v) |>.right


theorem pred_has_edge (g : Graph α) (u v : α)
    : u ∈ pred g v ↔ ⟨u, v⟩ ∈ in_edges g v := by
  apply Iff.intro <;> intro h₁ <;> simp [pred] at *
  . apply Exists.elim h₁
    intro e h₂
    have h₃ := in_edges_finish g e v h₂.left
    simp [←h₃, ←h₂.right] at *
    exact h₂
  . apply Exists.intro ⟨u, v⟩; simp [*]

theorem pred_edge_in_graph (g : Graph α) (u v : α) (h : u ∈ pred g v) : ⟨u, v⟩ ∈ g :=
  pred_has_edge g u v |>.mp h |> (in_edges_has_edge g u v |>.mp)

theorem pred_in_graph (g : Graph α) (u v : α) (h : u ∈ pred g v) : has_vertex g u :=
  (pred_edge_in_graph g u v h) |> (edge_vertices g u v) |>.left


theorem out_in_edges (g : Graph α) (u v : α)
    : ⟨u, v⟩ ∈ out_edges g u ↔ ⟨u, v⟩ ∈ in_edges g v := by
  apply Iff.intro <;> intro h
  . exact in_edges_has_edge g u v |>.mpr (out_edges_has_edge g u v |>.mp h)
  . exact out_edges_has_edge g u v |>.mpr (in_edges_has_edge g u v |>.mp h)

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
