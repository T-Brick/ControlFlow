import ControlFlow.Path

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

instance : Membership α (List (Visited (g : Graph α) s)) where
  mem v visits := v ∈ (Visited.toList visits)

structure Frontier (g : Graph α) (visited : List (Visited g s)) (s : α) where
  cur : α
  nodes : List α
  path : g |= (cur :: nodes) : s -> cur
  nodes_visited : ∀ n ∈ nodes, n ∈ Visited.toList visited
  cur_not_visit : cur ∉ visited
deriving DecidableEq

@[simp] def Frontier.toList {g : Graph α} {visited : List (Visited g s)}
    (lst : List (Frontier g visited s)) : List α :=
  lst.map (·.cur)

@[simp] theorem Frontier.mem_ToList
    {g : Graph α}
    {visited : List (Visited g s)}
    {f : Frontier g visited s}
    {fs : List (Frontier g visited s)}
    {u : α}
    : u ∈ Frontier.toList (f::fs) → u = f.cur ∨ u ∈ Frontier.toList fs := by
  simp

@[simp] theorem Frontier.toList_mem_append
    {g : Graph α}
    {visited : List (Visited g s)}
    {frontier₁ frontier₂ : List (Frontier g visited s)}
    : v ∈ Frontier.toList (frontier₁ ++ frontier₂)
      ↔ v ∈ Frontier.toList frontier₁ ∨ v ∈ Frontier.toList frontier₂ := by
  simp

@[simp] theorem Frontier.in_list
    {g : Graph α}
    {visited : List (Visited g s)}
    {frontier : List (Frontier g visited s)}
    (h : v ∈ Frontier.toList frontier)
    : ∃ f ∈ frontier, f.cur = v := by
  simp at *
  exact h

-- todo: great name
@[simp] theorem Frontier.in_list'
    {g : Graph α}
    {visited : List (Visited g s)}
    {frontier : List (Frontier g visited s)}
    {f : Frontier g visited s}
    (h₁ : f ∈ frontier)
    : f.cur ∈ Frontier.toList frontier := by
  simp; exact Exists.intro f (And.intro h₁ rfl)

structure NewFrontier
    (g : Graph α)
    (visited : List (Visited g s))
    (f : Frontier g visited s)
    (fs : List (Frontier g visited s))
  where
    frontier : List (Frontier g (⟨f.cur, f.nodes, f.path⟩::visited) s)
    pres_old : ∀ u, u ∈ Frontier.toList fs
                → ¬(Visited.toList (⟨f.cur, f.nodes, f.path⟩::visited)).elem u
                → u ∈ Frontier.toList frontier
    pres_new : ∀ u, u ∈ Digraph.succ g f.cur
                → ¬(Visited.toList (⟨f.cur, f.nodes, f.path⟩::visited)).elem u
                → u ∈ Frontier.toList frontier

private def get_succ_frontier
    (g : Graph α)
    (visited : List (Visited g s))
    (f : Frontier g visited s)
    : (succ_frontier : List (Frontier g (⟨f.cur, f.nodes, f.path⟩::visited) s))
      ×' ∀ u, u ∈ Digraph.succ g f.cur
            → ¬(Visited.toList (⟨f.cur, f.nodes, f.path⟩::visited)).elem u
            → u ∈ Frontier.toList succ_frontier :=
  let visited' := ⟨f.cur, f.nodes, f.path⟩::visited

  let frontier_nodes := Digraph.succ g f.cur
  let frontier_nodes_filtered :=
    frontier_nodes.filter (fun v => ¬(Visited.toList visited' |>.elem v))

  have frontier_nodes_filter_not_visit
      : (v : α)
      → v ∈ frontier_nodes_filtered
      → ¬(Visited.toList visited' |>.elem v) := by
    intro v h₁
    let p := (fun v => ¬(Visited.toList visited' |>.elem v))
    exact List.filter_preserve_in p frontier_nodes v
      |>.mpr h₁ |>.right |> of_decide_eq_true
  have frontier_nodes_filter_pres
      : (v : α)
      → v ∈ frontier_nodes_filtered
      → v ∈ frontier_nodes := by
    intro v h₁
    let p := (fun v => ¬(Visited.toList visited' |>.elem v))
    exact List.filter_preserve_in p frontier_nodes v |>.mpr h₁ |>.left
  have frontier_nodes_filter_pres'
      : (v : α)
      → v ∈ frontier_nodes
      → ¬(Visited.toList visited' |>.elem v)
      → v ∈ frontier_nodes_filtered
      := by
    intro v h₁ h₂
    let p := (fun v => ¬(Visited.toList visited' |>.elem v))
    have := List.filter_preserve_in p frontier_nodes v |>.mp
    simp at *
    exact this h₁ h₂

  let frontier : List (Frontier g visited' s) :=
    frontier_nodes_filtered.mapMember (fun v h =>
      have h₂ := frontier_nodes_filter_not_visit v h
      ⟨ v
      , f.cur :: f.nodes
      , by
          have h₃ := Iff.subst List.elem_iff h₂
          apply Path.succ_merge f.path (frontier_nodes_filter_pres v h)
          intro h₄
          cases h₄
          case head => simp at h₃
          case tail _ h₅ =>
            exact h₃ (f.nodes_visited v h₅ |> List.Mem.tail f.cur)
      , by
          intro n h₃
          have last := f.nodes_visited n
          cases h₃ <;> simp [*] at *
          case tail _ h₄ => simp at h₄; apply Or.inr (last h₄)
      , by intro h₃; apply h₂ ((List.elem_iff |>.mpr) h₃)
      ⟩
    )
  have frontier_pres : (u : α)
      → u ∈ Digraph.succ g f.cur
      → ¬(Visited.toList visited').elem u
      → u ∈ Frontier.toList frontier := by
    intro u h₁ h₂
    simp
    apply Exists.intro (Subtype.mk u (frontier_nodes_filter_pres' u h₁ h₂))
    simp

  ⟨frontier, frontier_pres⟩


private def get_updated_fs
    (g : Graph α)
    (visited : List (Visited g s))
    (f : Frontier g visited s)
    (fs : List (Frontier g visited s))
    : (new_fs : List (Frontier g (⟨f.cur, f.nodes, f.path⟩::visited) s))
      ×' ∀ u, u ∈ Frontier.toList fs
            → ¬(Visited.toList (⟨f.cur, f.nodes, f.path⟩::visited)).elem u
            → u ∈ Frontier.toList new_fs :=

  let visited' := ⟨f.cur, f.nodes, f.path⟩::visited

  let fs_filter := fs.filter (fun f' => ¬((Visited.toList visited').elem f'.cur))
  have fs_filter_not_visit
      : (f : Frontier g visited s)
      → f ∈ fs_filter
      → ¬(Visited.toList visited' |>.elem f.cur) := by
    intro f h₁
    let p : Frontier g visited s → Prop :=
      fun f' => ¬((Visited.toList visited').elem f'.cur)
    exact List.filter_preserve_in p fs f |>.mpr h₁ |>.right |> of_decide_eq_true
  have fs_filter_pres
      : (f : Frontier g visited s)
      → f ∈ fs
      → ¬(Visited.toList visited' |>.elem f.cur)
      → f ∈ fs_filter := by
    intro f h₁ h₂
    let p : Frontier g visited s → Prop :=
      fun f' => ¬((Visited.toList visited').elem f'.cur)
    have := List.filter_preserve_in p fs f |>.mp
    simp at *
    exact this h₁ h₂

  let update_fs
      : (f : Frontier g visited s) → (f ∈ fs_filter) → Frontier g visited' s :=
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
      , by intro h₃; rw [List.elem_iff] at h₂; exact h₂ h₃
      ⟩

  let new_fs : List (Frontier g visited' s) := fs_filter.mapMember update_fs
  have new_fs_pres
      : ∀ u, u ∈ Frontier.toList fs
           → ¬(Visited.toList (⟨f.cur, f.nodes, f.path⟩::visited)).elem u
           → u ∈ Frontier.toList new_fs := by
    intro u h₁ h₂
    apply Exists.elim (Frontier.in_list h₁) (fun f' h₃ => by
      rw [←h₃.right] at h₂
      rw [←h₃.right]
      simp
      apply Exists.intro (Subtype.mk f' (fs_filter_pres f' h₃.left h₂))
      simp
    )

  ⟨new_fs, new_fs_pres⟩


private def get_new_frontier
    (g : Graph α)
    (visited : List (Visited g s))
    (f : Frontier g visited s)
    (fs : List (Frontier g visited s))
    : NewFrontier g visited f fs :=
  let visited' := ⟨f.cur, f.nodes, f.path⟩::visited

  let new_frontier_res := get_succ_frontier g visited f
  let new_frontier := new_frontier_res.fst
  let new_frontier_pres := new_frontier_res.snd

  let new_fs_res := get_updated_fs g visited f fs
  let new_fs := new_fs_res.fst
  let new_fs_pres := new_fs_res.snd

  let frontier' := new_fs ++ new_frontier
  have frontier'_pres_fs
      : (u : α)
      → u ∈ Frontier.toList fs
      → ¬(Visited.toList visited').elem u
      → u ∈ Frontier.toList frontier' := by
    intro u h₁ h₂
    rw [Frontier.toList_mem_append]
    apply Or.intro_left
    exact new_fs_pres u h₁ h₂
  have frontier'_pres_new_frontier_nodes
      : (u : α)
      → u ∈ Digraph.succ g f.cur
      → ¬(Visited.toList visited').elem u
      → u ∈ Frontier.toList frontier' := by
    intro u h₁ h₂
    rw [Frontier.toList_mem_append]
    apply Or.intro_right
    exact new_frontier_pres u h₁ h₂

  ⟨frontier', frontier'_pres_fs, frontier'_pres_new_frontier_nodes⟩

inductive Result (g : Graph α) (s t : α) where
| found     : (p : List α) → (g |= p : s -> t) → Result g s t
| not_found : (visited : List (Visited g s))
            → (∀ u ∈ Visited.toList visited, ∀ v ∈ Digraph.succ g u,
                v ∈ Visited.toList visited)
            → t ∉ Visited.toList visited
            → Result g s t


def is_found {g : Graph α} {s t : α} (res : Result g s t)
    : Bool :=
  match res with
  | .found _ _       => true
  | .not_found _ _ _ => false

theorem is_found_true {g : Graph α} {s t : α} {res : Result g s t}
    : is_found res → ∃ps, ∃(path : g |= ps : s -> t), res = .found ps path := by
  intro h₁
  sorry

theorem is_found_false {g : Graph α} {s t : α} {res : Result g s t}
    : ¬ is_found res → ∃visited h₁ h₂, res = .not_found visited h₁ h₂ := by
  intro h₁
  sorry

/- TODO: CPS-ify maybe? -/
private def explore
    (g : Graph α)
    (s t : α)
    (visited : List (Visited g s))
    (frontier : List (Frontier g visited s))
    (visited_succ : ∀ u ∈ Visited.toList visited, ∀ v ∈ Digraph.succ g u,
                      v ∈ Frontier.toList frontier ∨ v ∈ Visited.toList visited)
    (t_not_found : t ∉ Visited.toList visited)
    (vlen : visited.length < (Digraph.toVertices g).length + 1)
    : Result g s t :=
  match frontier with
  | [] =>
    .not_found visited
      (by
        intro u h₁ v h₂
        apply Or.elim (visited_succ u h₁ v h₂) <;> intro h₃ <;> simp at *
        exact h₃
      ) (t_not_found)
  | f :: fs =>
    if h₁ : f.cur = t then
      .found (f.cur :: f.nodes) (by rw [←h₁]; exact f.path)
    else
      let visited' := ⟨f.cur, f.nodes, f.path⟩ :: visited
      have cur_now_visited : f.cur ∈ Visited.toList visited' := by simp
      let new_frontier := get_new_frontier g visited f fs

      -- for termination
      have : List.length (toVertices g) - List.length visited
             < List.length (toVertices g) + 1 - List.length visited := by
        have := Nat.sub_lt_sub_left (Nat.sub_pos_of_lt vlen) (Nat.zero_lt_one)
        rw [Nat.sub_right_comm, Nat.add_sub_cancel] at this
        exact this

      explore g s t visited' new_frontier.frontier
        (by
          intro v h₂ u h₃
          cases h₂
          case head =>
            simp at h₃
            cases h : decide (u ∈ Visited.toList visited')
            case false =>
              have h := of_decide_eq_false h
              apply Or.inl
              exact new_frontier.pres_new u h₃ (Iff.subst (Iff.symm List.elem_iff) h)
            case true => exact Or.inr (of_decide_eq_true h)
          case tail _ h₄ =>
            apply Or.elim (visited_succ v h₄ u h₃) <;> intro h₅
            . cases h : decide (u ∈ Visited.toList visited')
              case false =>
                have h := of_decide_eq_false h
                apply Or.elim (Frontier.mem_ToList h₅) <;> intro h₆
                . rw [Eq.symm h₆] at cur_now_visited; contradiction
                . apply Or.inl
                  exact new_frontier.pres_old u h₆ (Iff.subst (Iff.symm List.elem_iff) h)
              case true => exact Or.inr (of_decide_eq_true h)
            . apply Or.inr (.tail _ h₅)
        ) (by
          intro h₂
          simp at h₂
          apply Or.elim h₂ <;> intro h₃
          . exact h₁ (Eq.symm h₃)
          . simp at t_not_found
            exact Exists.elim h₃ (fun x h => t_not_found x h.left h.right)
        ) (by
            -- should hold since:
            -- all elements of visited are in the graph (is a subset)
            -- all elements of visited are unique
            -- ergo length of visited doesn't exceed length of graph
          sorry
        )

termination_by explore visited frontier h₁ h₂ h₃ =>
  (Digraph.toVertices g).length + 1 - visited.length


def find_path (g : Graph α) (s t : α) : Result g s t :=
  explore g s t []
    (Digraph.succ g s |>.mapMember (fun v h =>
      ⟨v, [], Path.succ h, by simp, by intro h₁; cases h₁⟩
    ))
    (by simp)
    (by simp)
    (by simp [List.length, ←Nat.succ_eq_add_one, Nat.zero_lt_succ])
