import ControlFlow.Reachable

namespace ControlFlow.Digraph

open Path
open Digraph

variable {Graph  : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

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

def add_edge {g : Graph α} (connected : Connected g) (e : Edge α)
    (h₁ : has_vertex g e.start)
    (h₂ : has_vertex g e.finish)
    : Connected (Digraph.add_undirected_edge g e) := by
  intro u v u_in v_in
  have node_in := Digraph.add_undirected_edge_in_in_pres_vertices g e h₁ h₂
  have u_in' := node_in u |>.mpr u_in
  have v_in' := node_in v |>.mpr v_in
  exact Path.Reachable.add_undirected_edge_pres e (connected u v u_in' v_in')

theorem add_edge_flip_iff {g : Graph α} {e : Edge α}
    : Connected (Digraph.add_undirected_edge g e.flip)
      ↔ Connected (Digraph.add_undirected_edge g e) := by
  apply Iff.intro <;> (intro h u v h₁ h₂)
  . exact Path.Reachable.add_undirected_edge_flip_iff u v e h₁ h₁ h₂ h₂
      |>.mp (h u v h₁ h₂)
  . exact Path.Reachable.add_undirected_edge_flip_iff u v e h₁ h₁ h₂ h₂
      |>.mpr (h u v h₁ h₂)

def add_vertex_start {g : Graph α} (connected : Connected g) (e : Edge α)
    (start_in : has_vertex g e.start)
    : Connected (Digraph.add_undirected_edge g e) := by
  if h₁ : has_vertex g e.finish then exact add_edge connected e start_in h₁ else
  intro u v u_in v_in

  have e_in : ⟨e.start, e.finish⟩ ∈ Digraph.add_undirected_edge g e :=
    Digraph.add_undirected_edge_adds g e |>.left
  have rev_e_in : ⟨e.finish, e.start⟩ ∈ Digraph.add_undirected_edge g e :=
    Digraph.add_undirected_edge_adds g e |>.right

  if eq_uf : u = e.finish then
    simp [eq_uf]
    if eq_vf : v = e.finish then simp [eq_vf]; exact .refl else
    have v_in' :=
      Digraph.add_undirected_edge_in_out_pres_vertices g e start_in v eq_vf v_in
    apply Path.Reachable.trans (Path.Reachable.edge' rev_e_in |>.snd.snd)
    exact connected e.start v start_in v_in'
       |> Path.Reachable.add_undirected_edge_pres e
  else if eq_vf : v = e.finish then
    simp [eq_vf]
    have u_in' :=
      Digraph.add_undirected_edge_in_out_pres_vertices g e start_in u eq_uf u_in
    apply Path.Reachable.trans
    exact connected u e.start u_in' start_in
       |> Path.Reachable.add_undirected_edge_pres e
    exact Path.Reachable.edge' e_in |>.snd.snd
  else
    have is_in' := Digraph.add_undirected_edge_in_out_pres_vertices g e start_in
    exact connected u v (is_in' u eq_uf u_in) (is_in' v eq_vf v_in)
       |> Path.Reachable.add_undirected_edge_pres e

def add_vertex_finish {g : Graph α} (connected : Connected g) (e : Edge α)
    (h₁ : has_vertex g e.finish)
    : Connected (Digraph.add_undirected_edge g e) :=
  add_vertex_start connected e.flip h₁ |> add_edge_flip_iff.mp

def merge {g₁ g₂ : Graph α} {w : α}
    (connected₁ : Connected g₁)
    (connected₂ : Connected g₂)
    (shared : has_vertex g₁ w ∧ has_vertex g₂ w)
    : Connected (Digraph.merge g₁ g₂) := by
  intro u v h₁ h₂
  apply Or.elim (Digraph.merge_has_vertex.mp h₁) <;> (
      intro h₁
      apply Or.elim (Digraph.merge_has_vertex.mp h₂) <;> (
        intro h₂
        try exact Reachable.graph_merge_left h₁ h₂ (connected₁ u v h₁ h₂)
        try exact Reachable.graph_merge_right h₁ h₂ (connected₂ u v h₁ h₂)
      )
    )
  . have uw_reach := connected₁ u w h₁ shared.left
      |> Reachable.graph_merge_left (g₂ := g₂) _ _
    have wv_reach := connected₂ w v shared.right h₂
      |> Reachable.graph_merge_right (g₁ := g₁) _ _
    exact Reachable.trans uw_reach wv_reach
  . have uw_reach := connected₂ u w h₁ shared.right
      |> Reachable.graph_merge_right (g₁ := g₁) _ _
    have wv_reach := connected₁ w v shared.left h₂
      |> Reachable.graph_merge_left (g₂ := g₂) _ _
    exact Reachable.trans uw_reach wv_reach

end Connected
