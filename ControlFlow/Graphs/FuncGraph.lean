import ControlFlow.Graphs.Digraph

namespace ControlFlow.Digraph

variable [DecidableEq α]

structure FuncGraphType (α : Type) where
  vertex_list : List α
  vertices : α → Bool
  edges : Edge α → Bool
  out_edges : α → List (Edge α)
  in_edges  : α → List (Edge α)
  edge_vertices : ∀ u v, edges ⟨u, v⟩ → vertices u ∧ vertices v
  out_edges_has_edge : ∀ u v, ⟨u, v⟩ ∈ (out_edges u) ↔ edges ⟨u, v⟩
  out_edges_start : ∀ e u, e ∈ (out_edges u) → e.start = u
  in_edges_has_edge : ∀ u v, ⟨u, v⟩ ∈ (in_edges v) ↔ edges ⟨u, v⟩
  in_edges_finish : ∀ e v, e ∈ (in_edges v) → e.finish = v
  toList_has_vertex : ∀ v, v ∈ vertex_list ↔ vertices v

@[reducible]
def FuncGraphType.empty : FuncGraphType α :=
  { vertex_list        := []
  , vertices           := fun _ => false
  , edges              := fun _ => false
  , out_edges          := fun _ => []
  , in_edges           := fun _ => []
  , edge_vertices      := by simp
  , out_edges_has_edge := by simp
  , out_edges_start    := by simp
  , in_edges_has_edge  := by simp
  , in_edges_finish    := by simp
  , toList_has_vertex  := by simp
  }

@[reducible]
def FuncGraphType.add_edge : FuncGraphType α → Edge α → FuncGraphType α :=
  fun g e =>
    ⟨ let vertices' := e.finish :: g.vertex_list.filter (fun v => v ≠ e.start && v ≠ e.finish)
      if e.start = e.finish then vertices' else e.start :: vertices'
    , fun v => v = e.start || v = e.finish || g.vertices v
    , fun e' => e = e' || g.edges e'
    , fun v =>
        let res := g.out_edges v
        if v = e.start && ¬res.elem e then e :: res else res
    , fun v =>
        let res := g.in_edges v
        if v = e.finish && ¬res.elem e then e :: res else res
    , by
        intro u v h₁
        have h₂ := g.edge_vertices u v
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h₁ ⊢
        apply And.intro
        all_goals (
          cases h₁ with
          | inl h₁ => simp only [h₁, or_true, true_or]
          | inr h₁ =>
            apply Or.inr
            have ⟨l, r⟩ := h₂ h₁
            assumption
        )
    , by
        intro u v
        have h₁ := g.out_edges_has_edge u v
        simp only [List.elem_eq_mem, decide_eq_true_eq, decide_not,
          Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
          Bool.or_eq_true]
        apply Iff.intro <;> intro h₂
        . if eq : u = e.start then
            simp only [← eq, true_and, ite_not] at h₂
            if e_in : e ∈ g.out_edges u then
              simp only [e_in, ↓reduceIte] at h₂
              exact Or.inr (h₁.mp h₂)
            else
              simp only [e_in, ↓reduceIte, List.mem_cons] at h₂
              cases h₂ with
              | inl h₂ => exact Or.inl h₂.symm
              | inr h₂ => exact Or.inr (h₁.mp h₂)
          else
            simp only [eq, false_and, ↓reduceIte] at h₂
            exact Or.inr (h₁.mp h₂)
        . if eq : u = e.start then
            simp only at h₂
            if e_in : e ∈ g.out_edges u then
              simp only [e_in, not_true_eq_false, and_false, ↓reduceIte]
              cases h₂ with
              | inl h₂ => rw [←h₂]; exact e_in
              | inr h₂ => exact h₁.mpr h₂
            else
              simp only [e_in, not_false_eq_true, and_true]
              cases h₂ with
              | inl h₂ => simp only [h₂, ↓reduceIte, List.mem_cons, true_or]
              | inr h₂ =>
                simp only [eq, ↓reduceIte, List.mem_cons] at h₁ h₂ ⊢
                exact Or.inr (h₁.mpr h₂)
          else
            simp only [eq, false_and, ↓reduceIte] at h₂ ⊢
            cases h₂ with
            | inl h₂ => simp only [h₂, not_true_eq_false] at eq
            | inr h₂ => exact h₁.mpr h₂
    , by
        intro e' u h₁
        simp only [List.elem_eq_mem, decide_eq_true_eq, decide_not,
          Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h₁
        have h₂ := g.out_edges_start e' u
        if eq : u = e.start then
          if e_in : e ∈ out_edges g e.start then
            simp only [eq, e_in, not_true_eq_false, and_false, ↓reduceIte]
              at h₁ h₂ ⊢
            exact h₂ h₁
          else
            simp only [eq, e_in, not_false_eq_true, and_self, ↓reduceIte,
              List.mem_cons] at h₁ h₂ ⊢
            cases h₁ with
            | inl h₁ => simp only [h₁]
            | inr h₁ => exact h₂ h₁
        else
          simp only [eq, false_and, ↓reduceIte] at h₁
          exact h₂ h₁
    , by
        intro u v
        have h₁ := g.in_edges_has_edge u v
        simp only [List.elem_eq_mem, decide_eq_true_eq, decide_not,
          Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
          Bool.or_eq_true]
        apply Iff.intro <;> intro h₂
        . if eq : v = e.finish then
            simp only [← eq, true_and, ite_not] at h₂
            if e_in : e ∈ g.in_edges v then
              simp only [e_in, ↓reduceIte] at h₂
              exact Or.inr (h₁.mp h₂)
            else
              simp only [e_in, ↓reduceIte, List.mem_cons] at h₂
              cases h₂ with
              | inl h₂ => exact Or.inl h₂.symm
              | inr h₂ => exact Or.inr (h₁.mp h₂)
          else
            simp only [eq, false_and, ↓reduceIte] at h₂
            exact Or.inr (h₁.mp h₂)
        . if eq : v = e.finish then
            simp only at h₂
            if e_in : e ∈ g.in_edges v then
              simp only [e_in, not_true_eq_false, and_false, ↓reduceIte]
              cases h₂ with
              | inl h₂ => rw [←h₂]; exact e_in
              | inr h₂ => exact h₁.mpr h₂
            else
              simp only [e_in, not_false_eq_true, and_true]
              cases h₂ with
              | inl h₂ => simp only [h₂, ↓reduceIte, List.mem_cons, true_or]
              | inr h₂ =>
                simp only [eq, ↓reduceIte, List.mem_cons] at h₁ h₂ ⊢
                exact Or.inr (h₁.mpr h₂)
          else
            simp only [eq, false_and, ↓reduceIte] at h₂ ⊢
            cases h₂ with
            | inl h₂ => simp only [h₂, not_true_eq_false] at eq
            | inr h₂ => exact h₁.mpr h₂
    , by
        intro e' u h₁
        simp only [List.elem_eq_mem, decide_eq_true_eq, decide_not,
          Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h₁
        have h₂ := g.in_edges_finish e' u
        if eq : u = e.finish then
          if e_in : e ∈ in_edges g e.finish then
            simp only [eq, e_in, not_true_eq_false, and_false, ↓reduceIte]
              at h₁ h₂ ⊢
            exact h₂ h₁
          else
            simp only [eq, e_in, not_false_eq_true, and_self, ↓reduceIte,
              List.mem_cons] at h₁ h₂ ⊢
            cases h₁ with
            | inl h₁ => simp only [h₁]
            | inr h₁ => exact h₂ h₁
        else
          simp only [eq, false_and, ↓reduceIte] at h₁
          exact h₂ h₁
    , by
        intro v
        have h₁ := g.toList_has_vertex v
        simp only [ne_eq, decide_not, Bool.or_eq_true, decide_eq_true_eq]
        apply Iff.intro <;> intro h₂
        . if eq : e.start = e.finish then
            simp only [eq, ↓reduceIte, Bool.and_self, List.mem_cons, or_self]
              at h₂ ⊢
            cases h₂ with
            | inl h₂ => exact Or.inl h₂
            | inr h₂ =>
              have := (List.filter_preserve_in _ g.vertex_list v).mpr h₂
              exact Or.inr (h₁.mp this.left)
          else
            simp only [eq, ↓reduceIte, List.mem_cons, Or.assoc] at h₁ h₂
            cases h₂ with
            | inl h₂ => exact Or.inl h₂
            | inr h₂ =>
              have := (List.filter_preserve_in _ g.vertex_list v).mpr h₂
              exact Or.inr (h₁.mp this.left)
        . if eq : e.start = e.finish then
            simp only [eq, or_self, ↓reduceIte, Bool.and_self, List.mem_cons]
              at h₂ ⊢
            if v_eq : v = e.finish then exact Or.inl v_eq else
            cases h₂ with
            | inl h₂ => contradiction
            | inr h₂ =>
              let p := (fun v => !decide (v = e.finish))
              have := (List.filter_preserve_in p g.vertex_list v).mp
                ⟨ h₁.mpr h₂
                , by simp only [p, v_eq, decide_False, Bool.not_false]
                ⟩
              exact Or.inr this
          else
            simp only [eq, ↓reduceIte, List.mem_cons, Or.assoc]
            if v_eq_s : v = e.start then exact Or.inl (Or.inl v_eq_s) else
            if v_eq_f : v = e.finish then exact Or.inl (Or.inr v_eq_f) else
            simp only [v_eq_s, v_eq_f, or_self, false_or] at h₂ ⊢
            let p := (fun v => !decide (v = e.start) && !decide (v = e.finish))
            apply (List.filter_preserve_in p g.vertex_list v).mp
            refine ⟨h₁.mpr h₂, ?_⟩
            simp only [v_eq_s, decide_False, Bool.not_false, v_eq_f,
              Bool.and_self, p]
    ⟩

@[reducible]
def FuncGraphType.rem_edge : FuncGraphType α → Edge α → FuncGraphType α :=
  fun g e =>
    ⟨ g.vertex_list
    , g.vertices
    , fun e' => e' ≠ e && g.edges e'
    , fun v => (g.out_edges v).filter (· ≠ e)
    , fun v => (g.in_edges v).filter (· ≠ e)
    , by
        intro u v h₁
        simp only [ne_eq, decide_not, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not] at h₁ ⊢
        exact (g.edge_vertices u v) h₁.right
    , by
        intro u v
        let p : Edge α → Bool := (· ≠ e)
        simp only [ne_eq, decide_not, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not]
        apply Iff.intro <;> intro h₁
        . apply And.intro
          . intro h₂
            simp only [h₂] at h₁
            have := List.filter_remove p (FuncGraphType.out_edges g u) e
              (by simp only [ne_eq, decide_not, decide_True, Bool.not_true,
                    not_false_eq_true, p])
            apply this
            simp only [ne_eq, decide_not, p]
            exact h₁
          . have := List.filter_preserve_in _ (g.out_edges u) ⟨u, v⟩ |>.mpr h₁
            exact g.out_edges_has_edge u v |>.mp this.left
        . apply List.filter_preserve_in _ (out_edges g u) ⟨u, v⟩ |>.mp
          apply And.intro
          . exact g.out_edges_has_edge u v |>.mpr h₁.right
          . simp only [Bool.not_eq_true', decide_eq_false_iff_not]
            exact h₁.left
    , by
        intro e' u h₁
        simp only [ne_eq, decide_not] at h₁
        apply g.out_edges_start e' u
        exact List.filter_preserve_in _ (out_edges g u) e' |>.mpr h₁ |>.left
    , by
        intro u v
        let p : Edge α → Bool := (· ≠ e)
        simp only [ne_eq, decide_not, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not]
        apply Iff.intro <;> intro h₁
        . apply And.intro
          . intro h₂
            simp only [h₂] at h₁
            have := List.filter_remove p (FuncGraphType.in_edges g v) e
              (by simp only [ne_eq, decide_not, decide_True, Bool.not_true,
                    not_false_eq_true, p])
            apply this
            simp only [ne_eq, decide_not, p]
            exact h₁
          . have := List.filter_preserve_in _ (g.in_edges v) ⟨u, v⟩ |>.mpr h₁
            exact g.in_edges_has_edge u v |>.mp this.left
        . apply List.filter_preserve_in _ (in_edges g v) ⟨u, v⟩ |>.mp
          apply And.intro
          . exact g.in_edges_has_edge u v |>.mpr h₁.right
          . simp only [Bool.not_eq_true', decide_eq_false_iff_not]
            exact h₁.left
    , by
        intro e' u h₁
        simp only [ne_eq, decide_not] at h₁
        apply g.in_edges_finish e' u
        exact List.filter_preserve_in _ (in_edges g u) e' |>.mpr h₁ |>.left
    , g.toList_has_vertex
    ⟩

@[reducible]
def FuncGraphType.add_vertex : FuncGraphType α → α → FuncGraphType α :=
  fun g v =>
    ⟨ v :: g.vertex_list.filter (· ≠ v)
    , fun v' => v = v' || g.vertices v'
    , g.edges
    , g.out_edges
    , g.in_edges
    , by
        intro u w h₁
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        have h₂ := g.edge_vertices u w h₁
        apply And.intro <;> apply Or.inr
        . exact h₂.left
        . exact h₂.right
    , g.out_edges_has_edge
    , g.out_edges_start
    , g.in_edges_has_edge
    , g.in_edges_finish
    , by
        intro u
        simp only [ne_eq, decide_not, List.mem_cons, Bool.or_eq_true,
          decide_eq_true_eq]
        if eq : u = v then simp only [eq, true_or] else
        simp only [eq, neq_symm eq, false_or]
        apply Iff.intro <;> intro h₁
        . apply (g.toList_has_vertex u).mp
          exact List.filter_preserve_in _ g.vertex_list u |>.mpr h₁ |>.left
        . apply List.filter_preserve_in _ g.vertex_list u |>.mp
          apply And.intro
          exact g.toList_has_vertex u |>.mpr h₁
          simp only [eq, decide_False, Bool.not_false]
    ⟩

@[reducible]
def FuncGraphType.rem_vertex : FuncGraphType α → α → FuncGraphType α :=
  fun g v =>
    ⟨ g.vertex_list.filter (· ≠ v)
    , fun v' => v ≠ v' && g.vertices v'
    , fun e => v ≠ e.start && v ≠ e.finish && g.edges e
    , fun u => (g.out_edges u).filter (fun e => e.start ≠ v && e.finish ≠ v)
    , fun u => (g.in_edges u).filter (fun e => e.start ≠ v && e.finish ≠ v)
    , by
        intro u w h₁
        simp only [ne_eq, decide_not, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not] at h₁ ⊢
        have h₂ := g.edge_vertices u w h₁.right
        apply And.intro
        . exact ⟨h₁.left.left, h₂.left⟩
        . exact ⟨h₁.left.right, h₂.right⟩
    , by
        intro u w
        simp only [ne_eq, decide_not, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not]
        apply Iff.intro <;> intro h₁
        . have := List.filter_preserve_in _ (out_edges g u) ⟨u, w⟩ |>.mpr h₁
          apply And.intro
          . apply And.intro <;> (
              intro eq
              simp only [eq, decide_True, Bool.not_true, Bool.false_and,
                Bool.and_false, and_false] at this
            )
          . exact (g.out_edges_has_edge u w).mp this.left
        . apply List.filter_preserve_in _ (out_edges g u) ⟨u, w⟩ |>.mp
          simp only [Bool.and_eq_true, Bool.not_eq_true',
            decide_eq_false_iff_not]
          refine ⟨?_, (neq_symm h₁.left.left), (neq_symm h₁.left.right)⟩
          exact (g.out_edges_has_edge u w).mpr h₁.right
    , by
        intro e u h₁
        apply g.out_edges_start e u
        exact List.filter_preserve_in _ (out_edges g u) e |>.mpr h₁ |>.left
    , by
        intro u w
        simp only [ne_eq, decide_not, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not]
        apply Iff.intro <;> intro h₁
        . have := List.filter_preserve_in _ (in_edges g w) ⟨u, w⟩ |>.mpr h₁
          apply And.intro
          . apply And.intro <;> (
              intro eq
              simp only [eq, decide_True, Bool.not_true, Bool.false_and,
                Bool.and_false, and_false] at this
            )
          . exact (g.in_edges_has_edge u w).mp this.left
        . apply List.filter_preserve_in _ (in_edges g w) ⟨u, w⟩ |>.mp
          simp only [Bool.and_eq_true, Bool.not_eq_true',
            decide_eq_false_iff_not]
          refine ⟨?_, (neq_symm h₁.left.left), (neq_symm h₁.left.right)⟩
          exact (g.in_edges_has_edge u w).mpr h₁.right
    , by
        intro e u h₁
        apply g.in_edges_finish e u
        exact List.filter_preserve_in _ (in_edges g u) e |>.mpr h₁ |>.left
    , by
        intro u
        simp only [ne_eq, decide_not, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not]
        -- have h₁ := g.toList_has_vertex u
        apply Iff.intro <;> intro h₁
        . have := List.filter_preserve_in _ g.vertex_list u |>.mpr h₁
          simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
          refine ⟨neq_symm this.right, ?_⟩
          exact g.toList_has_vertex u |>.mp this.left
        . apply List.filter_preserve_in _ g.vertex_list u |>.mp
          simp only [Bool.not_eq_true', decide_eq_false_iff_not]
          refine ⟨?_, neq_symm h₁.left⟩
          exact g.toList_has_vertex u |>.mpr h₁.right
    ⟩

def FuncGraph [DecidableEq α] : Digraph α (FuncGraphType) :=
  { empty         := FuncGraphType.empty
  , has_edge      := (·.edges)
  , has_vertex    := (·.vertices)
  , add_edge      := FuncGraphType.add_edge
  , rem_edge      := FuncGraphType.rem_edge
  , add_vertex    := FuncGraphType.add_vertex
  , rem_vertex    := FuncGraphType.rem_vertex
  , out_edges     := fun g => g.out_edges
  , in_edges      := fun g => g.in_edges
  , toVertices    := fun g => g.vertex_list
  , edge_vertices := by intro g; exact g.edge_vertices
  , empty_edges   := by simp only [not_false_eq_true, implies_true]
  , empty_vertex  := by simp only [not_false_eq_true, implies_true]
  , add_edge_adds := by simp only [decide_True, Bool.true_or, implies_true]
  , add_edge_pres_edges := by
      simp only [ne_eq, Bool.or_eq_true, decide_eq_true_eq]
      intro g e₁ e₂ h₁
      apply Iff.intro <;> intro h₂
      . exact Or.inr h₂
      . cases h₂ with
        | inl h₂ => have := h₂.symm; contradiction
        | inr h₂ => exact h₂
  , add_edge_pres_vertex := by
      simp only [ne_eq, Bool.or_eq_true, decide_eq_true_eq]
      intro g u v w h₁ h₂
      apply Iff.intro <;> intro h₃
      . exact Or.inr h₃
      . cases h₃ with
        | inl h₃ =>
          cases h₃ with
          | inl h₃ => contradiction
          | inr h₃ => contradiction
        | inr h₃ => exact h₃
  , rem_edge_removes := by
      simp only [ne_eq, not_true_eq_false, decide_False, Bool.false_and,
        not_false_eq_true, implies_true]
  , rem_edge_pres_edges := by
      simp only [ne_eq, decide_not, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, iff_and_self]
      intro g e₁ e₂ h₁ _h₂
      exact h₁
  , rem_edge_pres_vertex := by simp only [implies_true]
  , add_vertex_adds := by simp only [decide_True, Bool.true_or, implies_true]
  , add_vertex_pres_edges := by simp only [implies_true]
  , add_vertex_pres_vertex := by
      simp only [ne_eq, Bool.or_eq_true, decide_eq_true_eq]
      intro g u v h₁
      apply Iff.intro <;> intro h₂
      . exact Or.inr h₂
      . cases h₂ with
        | inl h₂ => have := h₂.symm; contradiction
        | inr h₂ => exact h₂
  , rem_vertex_removes_vertex := by
      simp only [ne_eq, not_true_eq_false, decide_False, Bool.false_and,
        not_false_eq_true, implies_true]
  , rem_vertex_removes_edge := by
      simp only [ne_eq, decide_not, not_true_eq_false, decide_False,
        Bool.and_false, Bool.false_and, not_false_eq_true, and_self,
        implies_true]
  , rem_vertex_pres_edges := by
      simp only [ne_eq, decide_not, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, iff_and_self]
      intro g u v w h₁ h₂ _h₃
      exact ⟨h₁, h₂⟩
  , rem_vertex_pres_vertex := by
      simp only [ne_eq, decide_not, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, iff_and_self]
      intro g u v h₁ _h₂
      exact neq_symm h₁
  , out_edges_has_edge    := fun g => g.out_edges_has_edge
  , out_edges_start       := fun g => g.out_edges_start
  , in_edges_has_edge     := fun g => g.in_edges_has_edge
  , in_edges_finish       := fun g => g.in_edges_finish
  , toVertices_has_vertex := fun g => g.toList_has_vertex
  }
instance : Digraph α FuncGraphType := FuncGraph
