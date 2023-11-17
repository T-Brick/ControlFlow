import ControlFlow.Path
import ControlFlow.Reachable

/-
    TODO: Refactor all of this
 -/

namespace ControlFlow.Path.Find

open Digraph
open Path

variable {Graph : (α : Type) → Type}
variable [Digraph α Graph] [DecidableEq α]

structure Visited (g : Graph α) (s : α) where
  node    : α
  nodes   : List α
  path    : g |= (node :: nodes) : s -> node
deriving DecidableEq

@[simp] def Visited.toList {g : Graph α} (lst : List (Visited g s)) : List α :=
  lst.map (·.node)

@[simp] theorem Visited.in_list {g : Graph α} {visited : List (Visited g s)}
    (h : u ∈ Visited.toList visited)
    : ∃ v ∈ visited, v.node = u := by simp at *; exact h

instance : Membership α (List (Visited (g : Graph α) s)) where
  mem v visits := v ∈ Visited.toList visits

structure Frontier (g : Graph α) (visited : List (Visited g s)) (skip : α → Bool) (s : α) where
  cur : α
  nodes : List α
  path : g |= (cur :: nodes) : s -> cur
  nodes_visited : ∀ n ∈ nodes, n ∈ Visited.toList visited
  cur_not_visit : cur ∉ visited
  nodes_not_skip : ∀ n ∈ nodes, ¬skip n
  cur_not_skip : ¬skip cur
deriving DecidableEq

@[simp] theorem Frontier.path_not_skip
    {g : Graph α}
    {visited : List (Visited g s)}
    (f : Frontier g visited skip s)
    : ∀ n ∈ f.cur::f.nodes, ¬skip n :=
  fun n h₁ => by
    cases h₁
    case head => exact f.cur_not_skip
    case tail _ h₂ => exact f.nodes_not_skip n h₂

@[simp] def Frontier.toList {g : Graph α} {visited : List (Visited g s)}
    (lst : List (Frontier g visited skip s)) : List α :=
  lst.map (·.cur)

@[simp] theorem Frontier.mem_ToList
    {g : Graph α}
    {visited : List (Visited g s)}
    {f : Frontier g visited skip s}
    {fs : List (Frontier g visited skip s)}
    {u : α}
    : u ∈ Frontier.toList (f::fs) → u = f.cur ∨ u ∈ Frontier.toList fs := by
  simp

@[simp] theorem Frontier.toList_mem_append
    {g : Graph α}
    {visited : List (Visited g s)}
    {frontier₁ frontier₂ : List (Frontier g visited skip s)}
    : v ∈ Frontier.toList (frontier₁ ++ frontier₂)
      ↔ v ∈ Frontier.toList frontier₁ ∨ v ∈ Frontier.toList frontier₂ := by
  simp

@[simp] theorem Frontier.in_list
    {g : Graph α}
    {visited : List (Visited g s)}
    {frontier : List (Frontier g visited skip s)}
    (h : v ∈ Frontier.toList frontier)
    : ∃ f ∈ frontier, f.cur = v := by
  simp at *
  exact h

-- todo: great name
@[simp] theorem Frontier.in_list'
    {g : Graph α}
    {visited : List (Visited g s)}
    {frontier : List (Frontier g visited skip s)}
    {f : Frontier g visited skip s}
    (h₁ : f ∈ frontier)
    : f.cur ∈ Frontier.toList frontier := by
  simp; exact Exists.intro f (And.intro h₁ rfl)

@[reducible] def Frontier.visit {g : Graph α}
    (visited : List (Visited g s)) (f : Frontier g visited skip s)
    : List (Visited g s) :=
  ⟨f.cur, f.nodes, f.path⟩::visited

structure NewFrontier
    (g : Graph α)
    (visited : List (Visited g s))
    (skip : α → Bool)
    (f : Frontier g visited skip s)
    (fs : List (Frontier g visited skip s))
  where
    frontier : List (Frontier g (f.visit visited) skip s)
    pres_old : ∀ u, u ∈ Frontier.toList fs
                → u ∉ Visited.toList (f.visit visited)
                → u ∈ Frontier.toList frontier
    pres_new : ∀ u, u ∈ Digraph.succ g f.cur
                → u ∉ Visited.toList (f.visit visited) ∧ ¬skip u
                → u ∈ Frontier.toList frontier

private def get_succ_frontier
    (g : Graph α)
    (visited : List (Visited g s))
    (f : Frontier g visited skip s)
    : (succ_frontier : List (Frontier g (f.visit visited) skip s))
      ×' ∀ u, u ∈ Digraph.succ g f.cur
            → u ∉ Visited.toList (f.visit visited) ∧ ¬skip u
            → u ∈ Frontier.toList succ_frontier :=
  let visited' := f.visit visited

  let frontier_nodes := Digraph.succ g f.cur
  let filter_func := (fun v => v ∉ Visited.toList visited' ∧ ¬skip v)
  let frontier_nodes_filtered := frontier_nodes.filter filter_func

  have frontier_nodes_filter_not_visit
      : (v : α)
      → v ∈ frontier_nodes_filtered
      → v ∉ Visited.toList visited' ∧ ¬skip v := by
    intro v h₁
    let p := filter_func
    exact List.filter_preserve_in p frontier_nodes v
      |>.mpr h₁ |>.right |> of_decide_eq_true
  have frontier_nodes_filter_pres
      : (v : α)
      → v ∈ frontier_nodes_filtered
      → v ∈ frontier_nodes := by
    intro v h₁
    exact List.filter_preserve_in filter_func frontier_nodes v |>.mpr h₁ |>.left
  have frontier_nodes_filter_pres'
      : (v : α)
      → v ∈ frontier_nodes
      → v ∉ Visited.toList visited' ∧ ¬skip v
      → v ∈ frontier_nodes_filtered := by
    intro v h₁ h₂
    have := List.filter_preserve_in filter_func frontier_nodes v |>.mp
    exact this (And.intro h₁ (by
      apply decide_eq_true_iff (filter_func v) |>.mpr
      simp at *
      exact h₂
    ))

  let frontier : List (Frontier g visited' skip s) :=
    frontier_nodes_filtered.mapMember (fun v h =>
      have h₂ := frontier_nodes_filter_not_visit v h
      { cur := v
      , nodes := f.cur :: f.nodes
      , path := by
          have h₃ := h₂.left
          apply Path.succ_merge f.path (frontier_nodes_filter_pres v h)
          intro h₄
          cases h₄
          case head => simp at h₃
          case tail _ h₅ =>
            exact h₃ (f.nodes_visited v h₅ |> List.Mem.tail f.cur)
      , nodes_visited := by
          intro n h₃
          have last := f.nodes_visited n
          cases h₃ <;> simp [*] at *
          case tail _ h₄ => apply Or.inr (last h₄)
      , cur_not_visit := by intro h₃; apply h₂.left h₃
      , nodes_not_skip := by
          intro n h₃
          cases h₃
          case head => exact f.cur_not_skip
          case tail _ h₄ => exact f.nodes_not_skip n h₄
      , cur_not_skip := h₂.right
      }
    )
  have frontier_pres : (u : α)
      → u ∈ Digraph.succ g f.cur
      → u ∉ Visited.toList visited' ∧ ¬skip u
      → u ∈ Frontier.toList frontier := by
    intro u h₁ h₂
    have := frontier_nodes_filter_pres' u h₁ h₂
    simp at *
    exact this

  ⟨frontier, frontier_pres⟩


private def get_updated_fs
    (g : Graph α)
    (visited : List (Visited g s))
    (f : Frontier g visited skip s)
    (fs : List (Frontier g visited skip s))
    : (new_fs : List (Frontier g (f.visit visited) skip s))
      ×' ∀ u, u ∈ Frontier.toList fs
            → u ∉ Visited.toList (f.visit visited)
            → u ∈ Frontier.toList new_fs :=

  let visited' := f.visit visited

  let filter_func := fun (f': Frontier g visited skip s) =>
    f'.cur ∉ Visited.toList visited'
  let fs_filter := fs.filter filter_func
  have fs_filter_not_visit
      : (f : Frontier g visited skip s)
      → f ∈ fs_filter
      → f.cur ∉ Visited.toList visited' := by
    intro f h₁
    exact List.filter_preserve_in filter_func fs f
      |>.mpr h₁ |>.right |> of_decide_eq_true
  have fs_filter_pres
      : (f : Frontier g visited skip s)
      → f ∈ fs
      → f.cur ∉ Visited.toList visited'
      → f ∈ fs_filter := by
    intro f h₁ h₂
    have := List.filter_preserve_in filter_func fs f |>.mp
    exact this (And.intro h₁ (by
      apply decide_eq_true_iff (filter_func f) |>.mpr
      simp at *
      exact h₂
    ))

  let update_fs : (f : Frontier g visited skip s)
                → f ∈ fs_filter
                → Frontier g visited' skip s :=
    fun f h =>
      have h₂ := fs_filter_not_visit f h
      ⟨ f.cur
      , f.nodes
      , f.path
      , by
          intro n h₃
          have last := f.nodes_visited
          simp [*] at *
          exact Or.inr (last n h₃)
      , by intro h₃; exact h₂ h₃
      , f.nodes_not_skip
      , f.cur_not_skip
      ⟩

  let new_fs := fs_filter.mapMember update_fs
  have new_fs_pres
      : ∀ u, u ∈ Frontier.toList fs
           → u ∉ Visited.toList (f.visit visited)
           → u ∈ Frontier.toList new_fs := by
    intro u h₁ h₂
    apply Exists.elim (Frontier.in_list h₁) (fun f' h₃ => by
      rw [←h₃.right] at h₂
      rw [←h₃.right]
      have := fs_filter_pres f' h₃.left h₂
      simp at *
      apply Exists.intro f'
      apply And.intro
      exact this
      rfl
    )

  ⟨new_fs, new_fs_pres⟩


private def get_new_frontier
    (g : Graph α)
    (visited : List (Visited g s))
    (f : Frontier g visited skip s)
    (fs : List (Frontier g visited skip s))
    : NewFrontier g visited skip f fs :=
  let visited' := f.visit visited

  let new_frontier_res := get_succ_frontier g visited f
  let new_frontier := new_frontier_res.fst
  let new_frontier_pres := new_frontier_res.snd

  let new_fs_res := get_updated_fs g visited f fs
  let new_fs := new_fs_res.fst
  let new_fs_pres := new_fs_res.snd

  let frontier' := new_frontier ++ new_fs
  have frontier'_pres_fs
      : (u : α)
      → u ∈ Frontier.toList fs
      → u ∉ Visited.toList visited'
      → u ∈ Frontier.toList frontier' := by
    intro u h₁ h₂
    rw [Frontier.toList_mem_append]
    apply Or.intro_right
    exact new_fs_pres u h₁ h₂
  have frontier'_pres_new_frontier_nodes
      : (u : α)
      → u ∈ Digraph.succ g f.cur
      → u ∉ Visited.toList visited' ∧ ¬skip u
      → u ∈ Frontier.toList frontier' := by
    intro u h₁ h₂
    rw [Frontier.toList_mem_append]
    apply Or.intro_left
    exact new_frontier_pres u h₁ h₂

  ⟨frontier', frontier'_pres_fs, frontier'_pres_new_frontier_nodes⟩

inductive Result (g : Graph α) (s : α) (p : α → Bool) (skip : α → Bool) where
| found     : (t : α) → p t → (ps : List α)
            → (∀ v ∈ ps, ¬skip v)
            → (g |= ps : s -> t)
            → Result g s p skip
| not_found : (visited : List (Visited g s))
            → (∀ u ∈ Visited.toList visited, ∀ v ∈ Digraph.succ g u,
                ¬skip v → v ∈ Visited.toList visited)
            → (∀ v ∈ Visited.toList visited, ¬p v)
            → Result g s p skip

@[simp] def is_found {g : Graph α} (res : Result g s found skip) : Bool :=
  match res with
  | .found _ _ _ _ _ => true
  | .not_found _ _ _ => false

def explore
    (g : Graph α) (s : α)
    (found : α → Bool)
    (skip : α → Bool)
    (visited : List (Visited g s))
    (frontier : List (Frontier g visited skip s))
    (visited_succ : ∀ u ∈ Visited.toList visited, ∀ v ∈ Digraph.succ g u,
                      ¬skip v → v ∈ Frontier.toList frontier
                              ∨ v ∈ Visited.toList visited)
    (visited_not_found : ∀ v ∈ Visited.toList visited, ¬found v)
    (vlen : visited.length < (Digraph.toVertices g).length + 1)
    : Result g s found skip :=
  match frontier with
  | [] =>
    .not_found visited
      (by
        intro u h₁ v h₂ h₃
        apply Or.elim (visited_succ u h₁ v h₂ h₃) <;> intro h₄ <;> simp at *
        exact h₄
      ) visited_not_found
  | f :: fs =>
    if h₁ : found f.cur then
      .found f.cur h₁ (f.cur :: f.nodes) f.path_not_skip f.path
    else
      let visited' := f.visit visited
      have cur_now_visited : f.cur ∈ Visited.toList visited' := by simp
      let new_frontier := get_new_frontier g visited f fs

      -- for termination
      have : List.length (toVertices g) - List.length visited
             < List.length (toVertices g) + 1 - List.length visited := by
        have := Nat.sub_lt_sub_left (Nat.sub_pos_of_lt vlen) (Nat.zero_lt_one)
        rw [Nat.sub_right_comm, Nat.add_sub_cancel] at this
        exact this

      explore g s found skip visited' new_frontier.frontier
        (by
          intro v h₂ u h₃ u_skip
          cases h₂
          case head =>
            simp at h₃
            cases h : decide (u ∈ Visited.toList visited')
            case false =>
              have h := of_decide_eq_false h
              apply Or.inl
              have := And.intro h u_skip
              exact new_frontier.pres_new u h₃ this
            case true => exact Or.inr (of_decide_eq_true h)
          case tail _ h₄ =>
            apply Or.elim (visited_succ v h₄ u h₃ u_skip) <;> intro h₅
            . cases h : decide (u ∈ Visited.toList visited')
              case false =>
                have h := of_decide_eq_false h
                apply Or.elim (Frontier.mem_ToList h₅) <;> intro h₆
                . rw [Eq.symm h₆] at cur_now_visited; contradiction
                . apply Or.inl
                  exact new_frontier.pres_old u h₆ h
              case true => exact Or.inr (of_decide_eq_true h)
            . apply Or.inr (.tail _ h₅)
        ) (by
          intro v h₂
          simp at h₂
          apply Or.elim h₂ <;> intro h₃
          . rw [h₃]; exact h₁
          . simp at visited_not_found
            apply Exists.elim h₃
            intro x h
            simp [←h.right]; exact visited_not_found x h.left
        ) (by
            -- should hold since:
            -- all elements of visited are in the graph (is a subset)
            -- all elements of visited are unique
            -- ergo length of visited doesn't exceed length of graph
          sorry
        )

termination_by explore visited frontier h₁ h₂ h₃ =>
  (Digraph.toVertices g).length + 1 - visited.length

def find_path
    (g : Graph α)
    (s : α)
    (found : α → Bool)
    (skip : α → Bool)
    : Result g s found skip :=
  let succs := Digraph.succ g s
  let valid_succs := succs |>.filter (¬skip ·)

  explore g s found skip []
    (valid_succs |>.mapMember (fun v h =>
      { cur := v
      , nodes := []
      , path :=
          List.filter_preserve_in (¬skip ·) succs v
          |>.mpr h
          |>.left
          |> Path.succ
      , nodes_visited := by simp
      , cur_not_visit := (by intro h₁; cases h₁)
      , nodes_not_skip := by simp
      , cur_not_skip := by
          have := List.filter_preserve_in (¬skip ·) succs v |>.mpr h |>.right
          rw [decide_eq_true_eq] at this
          exact this
      }
    ))
    (by simp)
    (by simp)
    (by simp [List.length, ←Nat.succ_eq_add_one, Nat.zero_lt_succ])

theorem find_path_for_false {g : Graph α} {s : α}
    (h₁ : ∀ v, has_vertex g v → ¬found v)
    : ¬is_found (find_path g s found skip) := by
  intro h₂
  let res := find_path g s found skip
  cases h₃ : res
  case found t h₄ _ _ path => exact h₁ t (finish_in_graph path) h₄
  case not_found _ _ _ => simp [*] at h₂

def find_path_to (g : Graph α) (s t : α)
    : Result g s (· = t) (fun _ => false) :=
  find_path g s (· = t) (fun _ => false)

def find_reachable_skipping (g : Graph α) (s : α) (skip : α → Bool)
    : (visited : List (Visited g s))
      ×' (∀ u ∈ Visited.toList visited, ∀ v ∈ Digraph.succ g u,
            ¬skip v → v ∈ Visited.toList visited) :=
  let found := (fun _ => false)
  match find_path g s found skip with
  | .found _ _ _ _ _ => by
    have : ¬is_found (find_path g s found skip) := find_path_for_false (by simp)
    contradiction
  | .not_found visited h _ => ⟨visited, h⟩

def find_reachable (g : Graph α) (s : α)
    : (visited : List (Visited g s))
      ×' (∀ u ∈ Visited.toList visited, ∀ v ∈ Digraph.succ g u,
            v ∈ Visited.toList visited) :=
  let ⟨visited, hvisit⟩ := find_reachable_skipping g s (fun _ => false)
  let hvisit' := fun u h₁ v h₂ => hvisit u h₁ v h₂ (by simp)
  ⟨visited, hvisit'⟩

def reachable_list (g : Graph α) (u : Vertices g)
    : (nodes : List α) ×' ∀ v, (v = u) ∨ (v.val ∈ nodes) → Reachable g u v :=
  let ⟨visited, _⟩ := find_reachable g u.val
  let nodes := Visited.toList visited
  ⟨ nodes
  , fun w h₁ => by
      apply Or.elim h₁ <;> intro h₁
      . rw [h₁]; exact .refl
      . have := Visited.in_list h₁
        exact Exists.elim (Visited.in_list h₁) (fun v h₃ => by
          have := v.path
          rw [h₃.right] at this
          exact .path (w.val :: v.nodes) this
        )
  ⟩
