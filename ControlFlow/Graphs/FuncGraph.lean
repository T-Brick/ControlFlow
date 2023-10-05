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

def FuncGraph [DecidableEq α] : Digraph α (FuncGraphType) :=
  { empty :=
      ⟨ []
      , fun _ => false
      , fun _ => false
      , fun _ => []
      , fun _ => []
      , by simp
      , by simp
      , by simp
      , by simp
      , by simp
      , by simp
      ⟩
  , has_edge := (·.edges)
  , has_vertex := (·.vertices)
  , add_edge := fun g e =>
      ⟨ e.start :: e.finish :: g.vertex_list.filter (fun v => v ≠ e.start && v ≠ e.finish)
      , fun v => v = e.start || v = e.finish || g.vertices v
      , fun e' => e = e' || g.edges e'
      , fun v => if v = e.start then e :: g.out_edges v else g.out_edges v
      , fun v => if v = e.finish then e :: g.in_edges v else g.in_edges v
      , by
          intro u v h₁
          have h₂ := g.edge_vertices u v
          apply And.intro <;> simp at *
          . apply Or.elim h₁ <;> intro h₃
            . simp [h₃]
            . exact Or.inr (h₂ h₃ |>.left)
          . apply Or.elim h₁ <;> intro h₃
            . simp [h₃]
            . exact Or.inr (h₂ h₃ |>.right)
      , by
          intro u v
          have h₁ := g.out_edges_has_edge u v
          apply Iff.intro <;> simp at * <;> intro h₂
          . cases decEq u e.start
            case isFalse neq => simp [*] at *; exact Or.inr h₂
            case isTrue eq =>
              simp [←eq] at h₂
              cases h₂
              case inl h₃ => simp [h₃]
              case inr _ h₃ => exact Or.inr (h₁.mp h₃)
          . cases decEq u e.start <;> simp [*] at *
            case isFalse neq =>
              apply Or.elim h₂ <;> intro h₃ <;> simp [*] at *
            case isTrue eq =>
              apply Or.elim h₂ <;> intro h₃
              . simp [←h₃]
              . exact Or.inr (h₁.mpr h₃)
      , by
          intro e' u h₁
          simp [*] at *
          have h₂ := g.out_edges_start e' u
          cases decEq u e.start <;> simp [*] at *
          case isFalse neq => exact h₂ h₁
          case isTrue eq => apply Or.elim h₁ <;> intro h₃ <;> simp [*]
      , by
          intro u v
          have h₁ := g.in_edges_has_edge u v
          apply Iff.intro <;> simp at * <;> intro h₂
          . cases decEq v e.finish
            case isFalse neq => simp [*] at *; exact Or.inr h₂
            case isTrue eq =>
              simp [←eq] at h₂
              cases h₂
              case inl h₃ => simp [h₃]
              case inr _ h₃ => exact Or.inr (h₁.mp h₃)
          . cases decEq v e.finish <;> simp [*] at *
            case isFalse neq =>
              apply Or.elim h₂ <;> intro h₃ <;> simp [*] at *
            case isTrue eq =>
              apply Or.elim h₂ <;> intro h₃
              . simp [←h₃]
              . exact Or.inr (h₁.mpr h₃)
      , by
          intro e' u h₁
          simp [*] at *
          have h₂ := g.in_edges_finish e' u
          cases decEq u e.finish <;> simp [*] at *
          case isFalse neq => exact h₂ h₁
          case isTrue eq => apply Or.elim h₁ <;> intro h₃ <;> simp [*]
      , by
          intro v
          let p := (fun v => v ≠ e.start && v ≠ e.finish)
          have := List.filter_preserve_in p g.vertex_list v
          have h₁ := g.toList_has_vertex v
          apply Iff.intro <;> intro h₂ <;> simp [*] at *
          . apply Or.elim h₂ <;> intro h₃
            . exact Or.inl h₃
            . apply Or.elim h₂ <;> intro h₄ <;> simp [*] at *
              exact Or.inr this.left
          . apply Or.elim h₂ <;> intro h₃ <;> simp [*] at *
            cases decEq v e.start <;> simp [*]
            case isFalse neq₁ =>
              cases decEq v e.finish <;> simp [*]
              case isFalse neq₂ => apply this.mp; apply And.intro neq₁ neq₂
      ⟩
  , rem_edge := fun g e =>
      ⟨ g.vertex_list
      , g.vertices
      , fun e' => e' ≠ e && g.edges e'
      , fun v => (g.out_edges v).filter (· ≠ e)
      , fun v => (g.in_edges v).filter (· ≠ e)
      , by
          intro u v h₁
          simp at *
          have h₂ := g.edge_vertices u v
          exact h₂ h₁.right
      , by
          intro u v
          have h₁ := g.out_edges_has_edge u v
          let p : Edge α → Bool := (· ≠ e)
          let uv : Edge α := {start:=u, finish:=v}
          apply Iff.intro <;> simp at * <;> intro h₂
          . have h₃ :=
              List.filter_remove p (FuncGraphType.out_edges g u) e (by simp)
            apply And.intro
            . intro h₄; simp [h₄] at *; contradiction
            . cases decEq e uv <;> simp [*] at *
              case isFalse neq =>
                have :=
                  List.filter_preserve_in p (FuncGraphType.out_edges g u) uv
                simp at this
                exact h₁.mp (this.mpr h₂).left
              case isTrue eq => contradiction
          . intro h₄
            have h₃ :=
              List.filter_preserve_in p (FuncGraphType.out_edges g u) uv
            simp at *
            exact h₃.mp (And.intro (h₁.mpr h₄) h₂)
      , by
          intro e' u h₁
          have h₂ := g.out_edges_start e' u
          let p : Edge α → Bool := (· ≠ e)
          have pres_in :=
            List.filter_preserve_in p (FuncGraphType.out_edges g u) e'
          simp [*] at *
          have := pres_in.mpr h₁
          exact h₂ this.left
      , by
          intro u v
          have h₁ := g.in_edges_has_edge u v
          let p : Edge α → Bool := (· ≠ e)
          let uv : Edge α := {start:=u, finish:=v}
          apply Iff.intro <;> simp at * <;> intro h₂
          . have h₃ :=
              List.filter_remove p (FuncGraphType.in_edges g v) e (by simp)
            apply And.intro
            . intro h₄; simp [h₄] at *; contradiction
            . cases decEq e uv <;> simp [*] at *
              case isFalse neq =>
                have :=
                  List.filter_preserve_in p (FuncGraphType.in_edges g v) uv
                simp at this
                exact h₁.mp (this.mpr h₂).left
              case isTrue eq => contradiction
          . intro h₄
            have h₃ :=
              List.filter_preserve_in p (FuncGraphType.in_edges g v) uv
            simp at *
            exact h₃.mp (And.intro (h₁.mpr h₄) h₂)
      , by
          intro e' u h₁
          have h₂ := g.in_edges_finish e' u
          let p : Edge α → Bool := (· ≠ e)
          have pres_in :=
            List.filter_preserve_in p (FuncGraphType.in_edges g u) e'
          simp [*] at *
          have := pres_in.mpr h₁
          exact h₂ this.left
      , g.toList_has_vertex
      ⟩
  , add_vertex := fun g v =>
      ⟨ v :: g.vertex_list.filter (· ≠ v)
      , fun v' => v = v' || g.vertices v'
      , g.edges
      , g.out_edges
      , g.in_edges
      , by
          intro u w h₁
          simp at *
          have h₂ := g.edge_vertices u w h₁
          apply And.intro
          . exact Or.inr h₂.left
          . exact Or.inr h₂.right
      , g.out_edges_has_edge
      , g.out_edges_start
      , g.in_edges_has_edge
      , g.in_edges_finish
      , by
          intro u
          let p := (· ≠ v)
          have := List.filter_preserve_in p g.vertex_list u
          have h₁ := g.toList_has_vertex u
          cases decEq u v <;> simp [*]
          case isFalse neq =>
            apply Iff.intro <;> intro h₂ <;> simp [*] at *
            . exact Or.inr this
            . apply Or.elim h₂ <;> intro h₃ <;> simp [*] at *
              exact this
      ⟩
  , rem_vertex := fun g v =>
      ⟨ g.vertex_list.filter (· ≠ v)
      , fun v' => v ≠ v' && g.vertices v'
      , fun e => v ≠ e.start && v ≠ e.finish && g.edges e
      , fun u => (g.out_edges u).filter (fun e => e.start ≠ v && e.finish ≠ v)
      , fun u => (g.in_edges u).filter (fun e => e.start ≠ v && e.finish ≠ v)
      , by
          intro u w h₁
          simp at *
          have h₂ := g.edge_vertices u w h₁.right
          apply And.intro
          . exact And.intro h₁.left.left h₂.left
          . exact And.intro h₁.left.right h₂.right
      , by
          intro u w
          have h₁ := g.out_edges_has_edge u w
          let p : Edge α → Bool := (fun e => e.start ≠ v && e.finish ≠ v)
          let uw : Edge α := {start:=u, finish:=w}
          apply Iff.intro <;> simp at * <;> intro h₂
          . have := List.filter_preserve_in p (FuncGraphType.out_edges g u) uw
              |>.mpr
            simp at *
            have h₃ := this h₂
            apply And.intro
            . apply And.intro <;> (intro h; simp [*] at *)
            . exact h₁.mp h₃.left
          . have := List.filter_preserve_in p (FuncGraphType.out_edges g u) uw
              |>.mp
            simp at *
            intro h₃ h₄
            exact this (h₁.mpr h₄) (neq_symm h₂) (neq_symm h₃)
      , by
          intro e u h₁
          have h₂ := g.out_edges_start e u
          let p : Edge α → Bool := (fun e => e.start ≠ v && e.finish ≠ v)
          have pres_in :=
            List.filter_preserve_in p (FuncGraphType.out_edges g u) e
          simp [*] at *
          have := pres_in.mpr h₁
          exact h₂ this.left
      , by
          intro u w
          have h₁ := g.in_edges_has_edge u w
          let p : Edge α → Bool := (fun e => e.start ≠ v && e.finish ≠ v)
          let uw : Edge α := {start:=u, finish:=w}
          apply Iff.intro <;> simp at * <;> intro h₂
          . have := List.filter_preserve_in p (FuncGraphType.in_edges g w) uw
              |>.mpr
            simp at *
            have h₃ := this h₂
            apply And.intro
            . apply And.intro <;> (intro h; simp [*] at *)
            . exact h₁.mp h₃.left
          . have := List.filter_preserve_in p (FuncGraphType.in_edges g w) uw
              |>.mp
            simp at *
            intro h₃ h₄
            exact this (h₁.mpr h₄) (neq_symm h₂) (neq_symm h₃)
      , by
          intro e u h₁
          have h₂ := g.in_edges_finish e u
          let p : Edge α → Bool := (fun e => e.start ≠ v && e.finish ≠ v)
          have pres_in :=
            List.filter_preserve_in p (FuncGraphType.in_edges g u) e
          simp [*] at *
          have := pres_in.mpr h₁
          exact h₂ this.left
      , by
          intro u
          let p := (· ≠ v)
          have := List.filter_preserve_in p g.vertex_list u
          have h₁ := g.toList_has_vertex u
          apply Iff.intro <;> intro h₂ <;> simp [*] at *
          . have h₃ := this.mpr h₂
            apply And.intro
            exact neq_symm h₃.right
            exact h₃.left
          . apply this.mp
            apply And.intro
            exact h₂.right
            exact neq_symm h₂.left
      ⟩
  , out_edges     := fun g => g.out_edges
  , in_edges      := fun g => g.in_edges
  , toVertices    := fun g => g.vertex_list
  -- , toEdges       := fun g => g.vertex_list.bind g.out_edges
  , edge_vertices := by intro g; exact g.edge_vertices
  , empty_edges   := by simp
  , empty_vertex  := by simp
  , add_edge_adds := by simp
  , add_edge_pres_edges := by
      intro g e₁ e₂ h₁
      apply Iff.intro <;> simp at * <;> intro h₂
      . apply Or.inr h₂
      . apply Or.elim h₂ <;> intro h₃
        . simp [h₃] at h₁
        . exact h₃
  , add_edge_pres_vertex := by
      intro g u v w h₁ h₂
      apply Iff.intro <;> simp at * <;> intro h₃
      . apply Or.inr h₃
      . apply Or.elim h₃ <;> intro h₄
        . apply Or.elim h₄ <;> intro h₅ <;> simp [h₅] at *
        . exact h₄
  , rem_edge_removes := by simp
  , rem_edge_pres_edges := by
      intro g e₁ e₂ h₁
      apply Iff.intro <;> simp at *
      . intro h₂; simp [h₁] at *; exact h₂
  , rem_edge_pres_vertex := by simp
  , add_vertex_adds := by simp
  , add_vertex_pres_edges := by simp
  , add_vertex_pres_vertex := by
      intro g u v h₁
      apply Iff.intro <;> simp at * <;> intro h₂
      . apply Or.inr h₂
      . apply Or.elim h₂ <;> intro h₃
        . simp [h₃] at h₁
        . exact h₃
  , rem_vertex_removes_vertex := by simp
  , rem_vertex_removes_edge := by simp
  , rem_vertex_pres_edges := by
      intro g u v w h₁ h₂
      apply Iff.intro <;> simp at *; intro h₃
      . apply And.intro
        . exact And.intro h₁ h₂
        . exact h₃
  , rem_vertex_pres_vertex := by
      intro g u v h₁
      apply Iff.intro <;> simp at *
      . intro h₂; exact And.intro (neq_symm h₁) h₂
  , out_edges_has_edge    := fun g =>
      g.out_edges_has_edge
  , out_edges_start       := fun g => g.out_edges_start
  , in_edges_has_edge     := fun g => g.in_edges_has_edge
  , in_edges_finish       := fun g => g.in_edges_finish
  , toVertices_has_vertex := fun g => g.toList_has_vertex
  }
instance : Digraph α FuncGraphType := FuncGraph
