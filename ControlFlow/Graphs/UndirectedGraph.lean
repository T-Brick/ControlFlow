import ControlFlow.Graphs.Digraph

namespace ControlFlow

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

structure UndirectedGraph [Digraph α Graph] (g : Graph α) : Prop where
  undirected : ∀ u v, Digraph.has_edge g ⟨u, v⟩ ↔ Digraph.has_edge g ⟨v, u⟩


namespace Digraph

/- Function and theorems for adding undirected edges -/

def add_undirected_edge (g : Graph α) (e : Edge α) : Graph α :=
  add_edge (add_edge g e) e.flip

theorem add_undirected_edge_adds (g : Graph α) (e : Edge α)
    : has_edge (add_undirected_edge g e) e
    ∧ has_edge (add_undirected_edge g e) e.flip := by
  simp [add_undirected_edge]; apply And.intro
  . exact add_edge_pres_existing_edge _ _ _ (add_edge_adds _ _)
  . exact add_edge_adds _ _

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


/- Function and theorems for removing undirected edges -/

def rem_undirected_edge (g : Graph α) (e : Edge α) : Graph α :=
  rem_edge (rem_edge g e) e.flip

theorem rem_undirected_edge_removes (g : Graph α) (e : Edge α)
    : ¬has_edge (rem_undirected_edge g e) e
    ∧ ¬has_edge (rem_undirected_edge g e) e.flip := by
  rw [rem_undirected_edge]; apply And.intro
  . exact rem_edge_pres_nonexisting_edge _ _ _ (rem_edge_removes _ _)
  . exact rem_edge_removes _ _

theorem rem_undirected_edge_pres_edges (g : Graph α) (e₁ e₂ : Edge α)
    (neq : e₁ ≠ e₂) (neqf : e₁ ≠ e₂.flip)
    : has_edge g e₁ ↔ has_edge (rem_undirected_edge g e₂) e₁ := by
  rw [ rem_undirected_edge
     , rem_edge_pres_edges _ _ _ _
     , rem_edge_pres_edges _ _ _ _
     ]
  exact neqf; exact neq

theorem rem_undirected_edge_pres_nonexisting_edge (g : Graph α)
    : ∀ e₁ e₂, e₁ ∉ g → e₁ ∉ rem_undirected_edge g e₂ := by
  intro e₁ e₂ h; simp [rem_undirected_edge]
  exact rem_edge_pres_nonexisting_edge _ _ _
    (rem_edge_pres_nonexisting_edge _ _ _ h)

theorem in_rem_undirected_edge_neq (g : Graph α)
    : ∀ e₁ e₂, e₁ ∈ rem_undirected_edge g e₂ → e₁ ≠ e₂ ∧ e₁ ≠ e₂.flip := by
  simp [rem_undirected_edge]; intro e₁ e₂ h₁
  apply And.intro <;> (intro eq; rw [eq] at h₁)
  . exact rem_undirected_edge_removes _ _ |>.left h₁
  . exact rem_undirected_edge_removes _ _ |>.right h₁

theorem rem_undirected_edge_eq_or_not_in (g : Graph α)
    : ∀ e₁ e₂, e₁ ∉ rem_undirected_edge g e₂
             → (e₁ = e₂ ∨ e₁ = e₂.flip) ∨ e₁ ∉ g := by
  simp [rem_undirected_edge]; intro e₁ e₂ h
  apply Or.elim (rem_edge_eq_or_not_in _ _ _ h) <;> intro h
  . exact Or.inl (Or.inr h)
  . apply Or.elim (rem_edge_eq_or_not_in _ _ _ h) <;> intro h
    . exact Or.inl (Or.inl h)
    . exact Or.inr h

theorem rem_undirected_edge_pres_vertex (g : Graph α) (u v w : α)
    : has_vertex g u ↔ has_vertex (rem_undirected_edge g ⟨v, w⟩) u := by
  rw [ rem_undirected_edge
     , rem_edge_pres_vertex _ _ _ _
     , rem_edge_pres_vertex _ _ _ _
     ]


/- Converting a digraph into an undirected graph -/

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

end Digraph


namespace UndirectedGraph

def empty : UndirectedGraph (Digraph.empty : Graph α) :=
  ⟨by intro u v
      have uv := Digraph.empty_edges (α:=α) (T := Graph) ⟨u, v⟩
      have vu := Digraph.empty_edges (α:=α) (T := Graph) ⟨v, u⟩
      apply Iff.intro <;> (intro h; contradiction)
  ⟩

def add_edge {g : Graph α} (ug : UndirectedGraph g) (e : Edge α)
    : UndirectedGraph (Digraph.add_undirected_edge g e) :=
  ⟨by intro u v
      if eq_uv : e = ⟨u, v⟩ then
        have := Digraph.add_undirected_edge_adds g ⟨u, v⟩
        simp [eq_uv] at *
        apply Iff.intro <;> intro _h
        . exact this.right
        . exact this.left
      else if eq_vu : e = ⟨v, u⟩ then
        have := Digraph.add_undirected_edge_adds g ⟨v, u⟩
        simp [eq_vu] at *
        apply Iff.intro <;> intro _h
        . exact this.left
        . exact this.right
      else
        have pres := Digraph.add_undirected_edge_pres_edges g
        have h₁ := pres ⟨u, v⟩ e (neq_symm eq_uv) (fun h => by
          have := Edge.flip_symm.mp (Eq.symm h); simp at this; exact eq_vu this)
        have h₂ := pres ⟨v, u⟩ e (neq_symm eq_vu) (fun h => by
          have := Edge.flip_symm.mp (Eq.symm h); simp at this; exact eq_uv this)
        rw [←h₁, ←h₂, ug.undirected u v]
  ⟩

def rem_edge {g : Graph α} (ug : UndirectedGraph g) (e : Edge α)
    : UndirectedGraph (Digraph.rem_undirected_edge g e) :=
  ⟨by intro u v
      if eq_uv : e = ⟨u, v⟩ then
        have := Digraph.rem_undirected_edge_removes g ⟨u, v⟩
        simp only [Edge.flip, eq_uv] at *
        apply Iff.intro <;> intro h
        . have := this.left h; contradiction
        . have := this.right h; contradiction
      else if eq_vu : e = ⟨v, u⟩ then
        have := Digraph.rem_undirected_edge_removes g ⟨v, u⟩
        simp only [Edge.flip, eq_vu] at *
        apply Iff.intro <;> intro h
        . have := this.right h; contradiction
        . have := this.left h; contradiction
      else
        have pres := Digraph.rem_undirected_edge_pres_edges g
        have h₁ := pres ⟨u, v⟩ e (neq_symm eq_uv) (fun h => by
          have := Edge.flip_symm.mp (Eq.symm h); simp at this; exact eq_vu this)
        have h₂ := pres ⟨v, u⟩ e (neq_symm eq_vu) (fun h => by
          have := Edge.flip_symm.mp (Eq.symm h); simp at this; exact eq_uv this)
        rw [←h₁, ←h₂, ug.undirected u v]
  ⟩

def add_vertex {g : Graph α} (ug : UndirectedGraph g) (w : α)
    : UndirectedGraph (Digraph.add_vertex g w) :=
  ⟨by intro u v
      have pres := Digraph.add_vertex_pres_edges g w
      rw [←pres ⟨u, v⟩, ←pres ⟨v, u⟩]
      exact ug.undirected u v
  ⟩

def rem_vertex {g : Graph α} (ug : UndirectedGraph g) (w : α)
    : UndirectedGraph (Digraph.rem_vertex g w) :=
  ⟨by intro u v
      have := Digraph.rem_vertex_removes_edge g
      if eq_u : w = u then
        simp only [Edge.flip, eq_u] at *
        apply Iff.intro <;> intro h
        . have := (this v u).right h; contradiction
        . have := (this v u).left h; contradiction
      else if eq_v : w = v then
        simp only [Edge.flip, eq_v] at *
        apply Iff.intro <;> intro h
        . have := (this u v).left h; contradiction
        . have := (this u v).right h; contradiction
      else
        have pres := Digraph.rem_vertex_pres_edges g w
        rw [←pres u v eq_u eq_v, ←pres v u eq_v eq_u]
        exact ug.undirected u v
  ⟩

end UndirectedGraph
