/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Basic

/-!
# Degree profile of the HSFN graph (Theorem thm:deg-II(i))

The neighbours of an address split into three classes decided by tier:
siblings (`N - 1` of them), the anchor (present iff tier `≥ 2`), and the
spawned cell (`N` children, present iff tier `< m`). The unified formula
`deg u = (N-1) + [2 ≤ tier u] + N·[tier u < m]` specializes to the paper's
three classes `2N-1 / 2N / N` (and to `N-1` at `m = 1`).
-/

namespace HSFN

variable {N m : ℕ}

open Finset

/-- Sibling neighbours: same cell, different final digit. -/
def sibF (u : Addr N m) : Finset (Addr N m) :=
  univ.filter fun v => Sib u v ∧ v ≠ u

/-- The anchor (parent) neighbour, as a finset. -/
def parF (u : Addr N m) : Finset (Addr N m) :=
  univ.filter fun v => u.1.length = v.1.length + 1 ∧ u.1.dropLast = v.1

/-- Child neighbours: the members of the cell spawned at `u`. -/
def chiF (u : Addr N m) : Finset (Addr N m) :=
  univ.filter fun v => v.1.length = u.1.length + 1 ∧ v.1.dropLast = u.1

theorem Par.ne {u v : Addr N m} (h : Par u v) : u ≠ v := by
  intro heq
  subst heq
  rcases h with ⟨hlen, -⟩ | ⟨hlen, -⟩ <;> omega

/-- Decomposition of adjacency into the three neighbour classes. -/
theorem mem_neighborFinset_iff (u v : Addr N m) :
    v ∈ (graph N m).neighborFinset u ↔ v ∈ sibF u ∨ v ∈ parF u ∨ v ∈ chiF u := by
  rw [SimpleGraph.mem_neighborFinset]
  simp only [sibF, parF, chiF, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hne, hS | hP⟩
    · exact Or.inl ⟨hS, fun h => hne h.symm⟩
    · rcases hP with ⟨hlen, hpre⟩ | ⟨hlen, hpre⟩
      · exact Or.inr (Or.inr ⟨hlen, hpre⟩)
      · exact Or.inr (Or.inl ⟨hlen, hpre⟩)
  · rintro (⟨hS, hne⟩ | ⟨hlen, hpre⟩ | ⟨hlen, hpre⟩)
    · exact ⟨fun h => hne h.symm, Or.inl hS⟩
    · exact ⟨Par.ne (Or.inr ⟨hlen, hpre⟩), Or.inr (Or.inr ⟨hlen, hpre⟩)⟩
    · exact ⟨Par.ne (Or.inl ⟨hlen, hpre⟩), Or.inr (Or.inl ⟨hlen, hpre⟩)⟩

theorem neighborFinset_eq (u : Addr N m) :
    (graph N m).neighborFinset u = sibF u ∪ parF u ∪ chiF u := by
  ext v
  rw [mem_neighborFinset_iff]
  simp [or_assoc]

/-- The three classes are pairwise disjoint: siblings share `u`'s tier, the
anchor sits one tier above, the children one tier below. -/
theorem disj_sib_par (u : Addr N m) : Disjoint (sibF u) (parF u) := by
  rw [disjoint_left]
  intro v hv hv'
  simp only [sibF, parF, mem_filter, mem_univ, true_and] at hv hv'
  have h1 := hv.1.1
  have h2 := hv'.1
  omega

theorem disj_sib_chi (u : Addr N m) : Disjoint (sibF u) (chiF u) := by
  rw [disjoint_left]
  intro v hv hv'
  simp only [sibF, chiF, mem_filter, mem_univ, true_and] at hv hv'
  have h1 := hv.1.1
  have h2 := hv'.1
  omega

theorem disj_par_chi (u : Addr N m) : Disjoint (parF u) (chiF u) := by
  rw [disjoint_left]
  intro v hv hv'
  simp only [parF, chiF, mem_filter, mem_univ, true_and] at hv hv'
  have h1 := hv.1
  have h2 := hv'.1
  omega

/-- Reconstruction: a sibling of `u` is `u.dropLast ++ [d]` for its last digit. -/
theorem sib_eq_dropLast_concat {u v : Addr N m} (h : Sib u v) :
    ∃ d, v.1 = u.1.dropLast ++ [d] := by
  refine ⟨v.1.getLast v.2.1, ?_⟩
  conv_lhs => rw [← List.dropLast_append_getLast v.2.1]
  rw [h.2]

/-- Build the cell member of `u` with final digit `d`. -/
def cellMem (u : Addr N m) (d : ℕ) (hd : d < N) : Addr N m :=
  ⟨u.1.dropLast ++ [⟨d, hd⟩],
    by simp,
    by
      rw [List.length_append, List.length_dropLast]
      have h1 : 1 ≤ u.1.length := Addr.one_le_tier u
      have h2 : u.1.length ≤ m := Addr.tier_le u
      simp only [List.length_cons, List.length_nil]
      omega⟩

theorem cellMem_mem (u : Addr N m) (d : ℕ) (hd : d < N) :
    cellMem u d hd ∈ univ.filter fun v : Addr N m => Sib u v := by
  simp only [mem_filter, mem_univ, true_and, Sib, cellMem]
  constructor
  · rw [List.length_append, List.length_dropLast]
    have h1 : 1 ≤ u.1.length := Addr.one_le_tier u
    simp only [List.length_cons, List.length_nil]
    omega
  · simp [List.dropLast_concat]

/-- The cell of `u` (its siblings, `u` included) has exactly `N` members. -/
theorem card_cell (u : Addr N m) :
    (univ.filter fun v : Addr N m => Sib u v).card = N := by
  classical
  refine Finset.card_eq_of_bijective (cellMem u) ?_ (cellMem_mem u) ?_
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    obtain ⟨d, hd⟩ := sib_eq_dropLast_concat hv
    refine ⟨d.1, d.2, (Addr.ext ?_).symm⟩
    rw [hd]
    rfl
  · intro d₁ d₂ h₁ h₂ heq
    have hl := congrArg (fun a : Addr N m => a.1.getLast?) heq
    simp [cellMem] at hl
    exact hl

theorem card_sibF (u : Addr N m) : (sibF u).card = N - 1 := by
  classical
  have hu : u ∈ univ.filter fun v : Addr N m => Sib u v := by
    simp [Sib]
  have hs : sibF u = (univ.filter fun v : Addr N m => Sib u v).erase u := by
    ext v
    simp only [sibF, mem_filter, mem_univ, true_and, mem_erase]
    tauto
  rw [hs, Finset.card_erase_of_mem hu, card_cell]

/-- The anchor exists iff the tier is at least `2`. -/
theorem card_par (u : Addr N m) :
    (parF u).card = if 2 ≤ u.tier then 1 else 0 := by
  classical
  by_cases h : 2 ≤ u.tier
  · rw [if_pos h]
    rw [Finset.card_eq_one]
    refine ⟨⟨u.1.dropLast, ?_, ?_⟩, ?_⟩
    · intro hnil
      have := congrArg List.length hnil
      simp [List.length_dropLast] at this
      unfold Addr.tier at h
      omega
    · rw [List.length_dropLast]
      have := Addr.tier_le u
      unfold Addr.tier at this
      omega
    · ext v
      simp only [parF, mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨hlen, hpre⟩
        exact Addr.ext hpre.symm
      · rintro rfl
        refine ⟨?_, rfl⟩
        rw [List.length_dropLast]
        unfold Addr.tier at h
        omega
  · rw [if_neg h]
    rw [Finset.card_eq_zero]
    ext v
    simp only [parF, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨hlen, -⟩
    have := Addr.one_le_tier v
    unfold Addr.tier at h this
    omega

/-- Build the child of `u` with final digit `d` (requires room below). -/
def childMem (u : Addr N m) (h : u.1.length < m) (d : ℕ) (hd : d < N) : Addr N m :=
  ⟨u.1 ++ [⟨d, hd⟩],
    by simp,
    by
      rw [List.length_append]
      simp only [List.length_cons, List.length_nil]
      omega⟩

/-- The spawned cell exists iff the tier is below `m`, and then holds `N`
children. -/
theorem card_chi (u : Addr N m) :
    (chiF u).card = if u.tier < m then N else 0 := by
  classical
  by_cases h : u.tier < m
  · rw [if_pos h]
    unfold Addr.tier at h
    refine Finset.card_eq_of_bijective (childMem u h) ?_ ?_ ?_
    · intro v hv
      simp only [chiF, mem_filter, mem_univ, true_and] at hv
      obtain ⟨hlen, hpre⟩ := hv
      have hne : v.1 ≠ [] := v.2.1
      refine ⟨(v.1.getLast hne).1, (v.1.getLast hne).2, (Addr.ext ?_).symm⟩
      show v.1 = u.1 ++ [v.1.getLast hne]
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      rw [hpre]
    · intro d hd
      simp only [chiF, mem_filter, mem_univ, true_and, childMem]
      constructor
      · rw [List.length_append]; simp
      · simp [List.dropLast_concat]
    · intro d₁ d₂ h₁ h₂ heq
      have hl := congrArg (fun a : Addr N m => a.1.getLast?) heq
      simp [childMem] at hl
      exact hl
  · rw [if_neg h]
    rw [Finset.card_eq_zero]
    ext v
    simp only [chiF, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨hlen, -⟩
    have := Addr.tier_le v
    unfold Addr.tier at h this
    omega

/-- **Degree formula** (Theorem thm:deg-II(i), unified over all cases):
`deg u = (N-1) + [2 ≤ tier u] + N·[tier u < m]`. -/
theorem degree_eq (u : Addr N m) :
    (graph N m).degree u =
      (N - 1) + (if 2 ≤ u.tier then 1 else 0) + (if u.tier < m then N else 0) := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_eq]
  rw [Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_union_left]
        exact ⟨disj_sib_chi u, disj_par_chi u⟩),
      Finset.card_union_of_disjoint (disj_sib_par u)]
  rw [card_sibF u, card_par u, card_chi u]

/-- Paper's three degree classes (`m ≥ 2`): tier 1 has degree `2N-1`. -/
theorem degree_tier_one (u : Addr N m) (hm : 2 ≤ m)
    (h : u.tier = 1) : (graph N m).degree u = 2 * N - 1 := by
  rw [degree_eq u, h]
  simp only [if_neg (by omega : ¬ 2 ≤ 1), if_pos (by omega : 1 < m)]
  omega

/-- Interior tiers (`2 ≤ t ≤ m-1`) have degree `2N`. -/
theorem degree_interior (u : Addr N m)
    (h1 : 2 ≤ u.tier) (h2 : u.tier < m) : (graph N m).degree u = 2 * N := by
  have hN := Addr.N_pos u
  rw [degree_eq u]
  simp only [if_pos h1, if_pos h2]
  omega

/-- Leaves (tier `m`, `m ≥ 2`) have degree `N`. -/
theorem degree_leaf (u : Addr N m) (hm : 2 ≤ m)
    (h : u.tier = m) : (graph N m).degree u = N := by
  have hN := Addr.N_pos u
  rw [degree_eq u, h]
  simp only [if_pos (by omega : 2 ≤ m), if_neg (lt_irrefl m)]
  omega

/-- At `m = 1` the graph is the single cell `K_N`: all degrees are `N - 1`. -/
theorem degree_m_one (u : Addr N 1) :
    (graph N 1).degree u = N - 1 := by
  have h1 := Addr.one_le_tier u
  have h2 := Addr.tier_le u
  rw [degree_eq u]
  simp only [if_neg (by omega : ¬ 2 ≤ u.tier), if_neg (by omega : ¬ u.tier < 1)]
  omega

end HSFN
