import ControlFlow.UndirectedPath

namespace ControlFlow.Path

open Digraph

variable {Graph  : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

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

theorem toPath {g : Graph α} {u v : Vertices g}
    (reach : Reachable g u v) (neq : u.val ≠ v.val)
    : ∃ ps, g |= ps : u.val -> v.val := by
  cases reach
  case refl => contradiction
  case path ps path => exact Exists.intro ps path

theorem toAcyclic {g : Graph α} {u v : Vertices g}
    (reach : Reachable g u v)
    (neq : u.val ≠ v.val)
    : ∃ ps, Acyclic g u.val v.val ps := by
  apply Exists.elim (reach.toPath neq); intro ps path
  if u_in : u.val ∈ ps then
    apply Exists.elim (split_cycle path u_in neq); intro ps₁ h
    apply Exists.elim h; intro ps₂ h
    exact Exists.intro ps₂ h.right.right.right
  else
    exact Exists.intro ps ⟨path, u_in⟩

theorem toUndirectedPath {g : Graph α} {u v : Vertices g}
    (ug : UndirectedGraph g)
    (reach : Reachable g u v)
    (neq : u.val ≠ v.val)
    : ∃ ps, Undirected g u.val v.val ps ∧ u.val ∉ ps :=
  Exists.elim (reach.toAcyclic neq) (fun ps acyclic =>
    Exists.intro ps (And.intro (acyclic.toUndirected ug) acyclic.acyclic)
  )


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

@[simp] theorem add_undirected_edge_flip_iff {g : Graph α}
    (u v : α) (e : Edge α)
    (u_in_e : has_vertex (add_undirected_edge g e) u)
    (u_in_eflip : has_vertex (add_undirected_edge g e.flip) u)
    (v_in_e : has_vertex (add_undirected_edge g e) v)
    (v_in_eflip : has_vertex (add_undirected_edge g e.flip) v)
    : Reachable (add_undirected_edge g e.flip) ⟨u, u_in_eflip⟩ ⟨v, v_in_eflip⟩
    ↔ Reachable (add_undirected_edge g e) ⟨u, u_in_e⟩ ⟨v, v_in_e⟩ := by
  apply Iff.intro <;> (
    intro reach
    cases reach
    case refl => exact .refl
    case path ps path =>
      exact Reachable.path ps (add_undirected_edge_flip_iff.mp path)
  )


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
