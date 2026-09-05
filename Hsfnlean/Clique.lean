/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Degree

/-!
# Blocks and maximal cliques (Lemma lem:maxclique)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
The maximal cliques of `F(N,m)` (`m ≥ 2`) are the anchored cliques
`{v} ∪ cell(v)` of the non-leaf nodes, of order `N+1`, together with the
tier-`1` cell, of order `N`; hence the clique number is `N+1`. The part
proved here: every clique lies inside one anchored clique or inside the
tier-`1` cell, the two candidate sets are cliques of the stated sizes, and
the clique number is `N+1`. The statements below are frozen; only the proofs
are to be supplied.
-/

namespace HSFN

variable {N m : ℕ}

open Finset

/-- The anchored clique of `u`: the node together with the cell it spawns
(for a leaf this is just `{u}`). -/
def anchored (u : Addr N m) : Finset (Addr N m) := insert u (chiF u)

/-- The tier-`1` (seed) cell. -/
def tier1 (N m : ℕ) : Finset (Addr N m) := univ.filter fun v => v.tier = 1

private theorem aux_mem_chiF {u v : Addr N m} :
    v ∈ chiF u ↔ v.1.length = u.1.length + 1 ∧ v.1.dropLast = u.1 := by
  simp [chiF]

private theorem aux_mem_anchored {u v : Addr N m} :
    v ∈ anchored u ↔ v = u ∨ v ∈ chiF u := by
  simp [anchored]

private theorem aux_mem_tier1 {v : Addr N m} :
    v ∈ tier1 N m ↔ v.tier = 1 := by
  simp [tier1]

private theorem aux_notMem_chiF_self (u : Addr N m) : u ∉ chiF u := by
  intro hu
  have := (aux_mem_chiF.mp hu).1
  omega

/-- An anchored set is a clique. -/
theorem isClique_anchored (u : Addr N m) :
    (graph N m).IsClique (anchored u : Set (Addr N m)) := by
  intro a ha b hb hab
  have ha' : a = u ∨ a ∈ chiF u := aux_mem_anchored.mp (by simpa using ha)
  have hb' : b = u ∨ b ∈ chiF u := aux_mem_anchored.mp (by simpa using hb)
  rcases ha' with rfl | haChi
  · rcases hb' with rfl | hbChi
    · exact (hab rfl).elim
    · have hbChi' := aux_mem_chiF.mp hbChi
      exact ⟨hab, Or.inr (Or.inl hbChi')⟩
  · rcases hb' with rfl | hbChi
    · have haChi' := aux_mem_chiF.mp haChi
      exact ⟨hab, Or.inr (Or.inr haChi')⟩
    · have haChi' := aux_mem_chiF.mp haChi
      have hbChi' := aux_mem_chiF.mp hbChi
      refine ⟨hab, Or.inl ⟨?_, ?_⟩⟩
      · omega
      · rw [haChi'.2, hbChi'.2]

private theorem aux_dropLast_of_tier_one {a : Addr N m} (h : a.tier = 1) :
    a.1.dropLast = [] := by
  have hlen : a.1.dropLast.length = 0 := by
    rw [List.length_dropLast]
    unfold Addr.tier at h
    omega
  exact List.length_eq_zero_iff.mp hlen

/-- The tier-`1` cell is a clique. -/
theorem isClique_tier1 (N m : ℕ) :
    (graph N m).IsClique (tier1 N m : Set (Addr N m)) := by
  intro a ha b hb hab
  have ha1 : a.tier = 1 := aux_mem_tier1.mp (by simpa using ha)
  have hb1 : b.tier = 1 := aux_mem_tier1.mp (by simpa using hb)
  refine ⟨hab, Or.inl ⟨?_, ?_⟩⟩
  · unfold Addr.tier at ha1 hb1
    omega
  · rw [aux_dropLast_of_tier_one ha1, aux_dropLast_of_tier_one hb1]

/-- A non-leaf anchored clique has `N + 1` members. -/
theorem card_anchored (u : Addr N m) (h : u.tier < m) : (anchored u).card = N + 1 := by
  rw [anchored, card_insert_of_notMem (aux_notMem_chiF_self u), card_chi, if_pos h, add_comm]

/-- The tier-`1` cell has `N` members (for `m ≥ 1`). -/
theorem card_tier1 (N m : ℕ) (hm : 1 ≤ m) : (tier1 N m).card = N := by
  unfold tier1
  rw [show (univ.filter fun v : Addr N m => v.tier = 1).card =
        Fintype.card { a : Addr N m // a.tier = 1 } from
      (Fintype.card_of_subtype (p := fun a : Addr N m => a.tier = 1)
        (univ.filter fun v : Addr N m => v.tier = 1)
        (fun x => by simp)).symm]
  rw [Addr.card_tier N m 1 le_rfl hm, pow_one]

private theorem aux_child_or_sib {K : Finset (Addr N m)} {x z : Addr N m}
    (hK : (graph N m).IsClique (K : Set (Addr N m)))
    (hxK : x ∈ K) (hxmin : ∀ y ∈ K, x.tier ≤ y.tier)
    (hz : z ∈ K) (hzx : z ≠ x) :
    Sib x z ∨ (z.1.length = x.1.length + 1 ∧ z.1.dropLast = x.1) := by
  have hadj : (graph N m).Adj x z := hK hxK hz hzx.symm
  rcases hadj.2 with hSib | hPar
  · exact Or.inl hSib
  · rcases hPar with hchild | hpar
    · exact Or.inr hchild
    · have hzlt : z.tier < x.tier := by
        unfold Addr.tier
        omega
      have : x.tier ≤ z.tier := hxmin z hz
      omega

private theorem aux_not_sib_and_child {x s c : Addr N m}
    (hsib : Sib x s) (hne : s ≠ x)
    (hchild : c.1.length = x.1.length + 1 ∧ c.1.dropLast = x.1) :
    ¬ (graph N m).Adj s c := by
  intro hAdj
  rcases hAdj.2 with hS | hP
  · have : s.1.length = c.1.length := hS.1
    have : x.1.length = s.1.length := hsib.1
    omega
  · rcases hP with ⟨_, hpre⟩ | ⟨hlen, _⟩
    · have : s = x := Addr.ext (hpre.symm.trans hchild.2)
      exact hne this
    · have : s.1.length = x.1.length := hsib.1.symm
      omega

private theorem aux_parent (x : Addr N m) (hx : 2 ≤ x.tier) :
    ∃ p : Addr N m, x ∈ chiF p ∧ ∀ z, Sib x z → z ∈ chiF p := by
  refine ⟨⟨x.1.dropLast, ?ne, ?le⟩, ?memx, ?memz⟩
  case ne =>
    apply List.ne_nil_of_length_pos
    rw [List.length_dropLast]
    unfold Addr.tier at hx
    omega
  case le =>
    rw [List.length_dropLast]
    have := Addr.tier_le x
    unfold Addr.tier at this
    omega
  case memx =>
    refine aux_mem_chiF.mpr ⟨?_, rfl⟩
    rw [List.length_dropLast]
    unfold Addr.tier at hx
    omega
  case memz =>
    intro z hz
    refine aux_mem_chiF.mpr ⟨?_, hz.2.symm⟩
    have hlen : z.1.length = x.1.length := hz.1.symm
    rw [List.length_dropLast, hlen]
    unfold Addr.tier at hx
    omega

/-- **Clique confinement** (Lemma lem:maxclique): every clique of `F(N,m)`
lies inside one anchored clique or inside the tier-`1` cell. -/
theorem isClique_subset (K : Finset (Addr N m))
    (hK : (graph N m).IsClique (K : Set (Addr N m))) :
    (∃ u : Addr N m, K ⊆ anchored u) ∨ K ⊆ tier1 N m := by
  by_cases hK0 : K = ∅
  · right
    subst hK0
    exact empty_subset _
  · have hne : K.Nonempty := nonempty_iff_ne_empty.mpr hK0
    obtain ⟨x, hxK, hxmin⟩ := exists_min_image K Addr.tier hne
    by_cases hS : ∃ s ∈ K, s ≠ x ∧ Sib x s
    · have hSibOnly : ∀ z ∈ K, z ≠ x → Sib x z := by
        intro z hz hzx
        rcases aux_child_or_sib hK hxK hxmin hz hzx with hSib | hChild
        · exact hSib
        · rcases hS with ⟨s, hsK, hsx, hsib⟩
          have hsne_z : s ≠ z := by
            intro h
            subst h
            have : s.1.length = x.1.length := hsib.1.symm
            omega
          have hadj : (graph N m).Adj s z := hK hsK hz hsne_z
          exact (aux_not_sib_and_child hsib hsx hChild hadj).elim
      by_cases hx1 : x.tier = 1
      · right
        intro z hz
        refine aux_mem_tier1.mpr ?_
        by_cases hzx : z = x
        · rw [hzx]; exact hx1
        · have hsib := hSibOnly z hz hzx
          have : z.tier = x.tier := by
            unfold Addr.tier
            exact hsib.1.symm
          omega
      · left
        have hx2 : 2 ≤ x.tier := by
          have := Addr.one_le_tier x
          omega
        obtain ⟨p, hxp, hcell⟩ := aux_parent x hx2
        refine ⟨p, ?_⟩
        intro z hz
        have hsib : Sib x z := by
          by_cases hzx : z = x
          · subst hzx
            exact ⟨rfl, rfl⟩
          · exact hSibOnly z hz hzx
        exact aux_mem_anchored.mpr (Or.inr (hcell z hsib))
    · left
      refine ⟨x, ?_⟩
      intro z hz
      by_cases hzx : z = x
      · rw [hzx]
        exact mem_insert_self _ _
      · have hChild : z.1.length = x.1.length + 1 ∧ z.1.dropLast = x.1 := by
          rcases aux_child_or_sib hK hxK hxmin hz hzx with hSib | hChild
          · exact (hS ⟨z, hz, hzx, hSib⟩).elim
          · exact hChild
        exact aux_mem_anchored.mpr (Or.inr (aux_mem_chiF.mpr hChild))

private theorem aux_card_anchored_le (u : Addr N m) : (anchored u).card ≤ N + 1 := by
  have hle : (anchored u).card ≤ (chiF u).card + 1 := by
    rw [anchored]
    exact card_insert_le u (chiF u)
  have hchi : (chiF u).card ≤ N := by
    rw [card_chi]
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le N
  omega

private theorem aux_card_tier1_le : (tier1 N m).card ≤ N := by
  by_cases hm : 1 ≤ m
  · exact (card_tier1 N m hm).le
  · have hm0 : m = 0 := by omega
    subst hm0
    have : tier1 N 0 = ∅ := by
      apply eq_empty_of_forall_notMem
      intro v hv
      have ht : v.tier = 1 := aux_mem_tier1.mp hv
      have := Addr.tier_le v
      omega
    simp [this]

/-- Every clique has at most `N + 1` vertices. -/
theorem card_le_of_isClique (K : Finset (Addr N m))
    (hK : (graph N m).IsClique (K : Set (Addr N m))) : K.card ≤ N + 1 := by
  rcases isClique_subset K hK with ⟨u, hsub⟩ | htier
  · exact (card_le_card hsub).trans (aux_card_anchored_le u)
  · exact (card_le_card htier).trans ((aux_card_tier1_le).trans (Nat.le_succ N))

/-- **Clique number** (Lemma lem:maxclique): for `m ≥ 2` and `N ≥ 1` the
clique number of `F(N,m)` is `N + 1`, attained by the anchored cliques. -/
theorem cliqueNum_eq (hN : 1 ≤ N) (hm : 2 ≤ m) : (graph N m).cliqueNum = N + 1 := by
  let z : Addr N m := ⟨[⟨0, hN⟩], by simp, by
    simp only [List.length_cons, List.length_nil]
    omega⟩
  have hz : z.tier < m := by
    have : z.tier = 1 := by simp [z, Addr.tier]
    omega
  apply le_antisymm
  · obtain ⟨s, hs⟩ := (graph N m).exists_isNClique_cliqueNum
    have hle := card_le_of_isClique s hs.isClique
    rwa [hs.card_eq] at hle
  · have hcl : (graph N m).IsClique (anchored z : Set (Addr N m)) := isClique_anchored z
    have hcard : (anchored z).card = N + 1 := card_anchored z hz
    have hle : (anchored z).card ≤ (graph N m).cliqueNum :=
      SimpleGraph.IsClique.card_le_cliqueNum (t := anchored z) (tc := hcl)
    exact hcard.symm.trans_le hle

end HSFN
