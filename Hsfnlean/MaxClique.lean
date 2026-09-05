/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Clique

/-!
# The maximal cliques (Lemma lem:maxclique, completed)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
For `m ≥ 2` and `N ≥ 2` the maximal cliques of `F(N,m)` are exactly the anchored
cliques of the non-leaf nodes and the tier-`1` cell. A clique is *maximal* when no
clique properly contains it. The statements below are frozen; only the proofs are to
be supplied.
-/

namespace HSFN

variable {N m : ℕ}

open Finset

/-- A finite clique is maximal when every clique containing it equals it. -/
def IsMaxClique (K : Finset (Addr N m)) : Prop :=
  (graph N m).IsClique (K : Set (Addr N m)) ∧
    ∀ K' : Finset (Addr N m), (graph N m).IsClique (K' : Set (Addr N m)) → K ⊆ K' → K' = K

/-- Two distinct nodes have disjoint spawned cells. -/
theorem chiF_disjoint {u u' : Addr N m} (h : u ≠ u') : Disjoint (chiF u) (chiF u') := by
  rw [disjoint_left]
  intro v hv hv'
  simp only [chiF, mem_filter, mem_univ, true_and] at hv hv'
  exact h (Addr.ext (hv.2.symm.trans hv'.2))

/-- A non-leaf anchored clique is maximal (`N ≥ 2`). -/
theorem isMaxClique_anchored (hN : 2 ≤ N) (u : Addr N m) (hu : u.tier < m) :
    IsMaxClique (anchored u) := by
  refine ⟨isClique_anchored u, ?_⟩
  intro K' hK' hsub
  have := hN
  apply (eq_of_subset_of_card_le hsub ?_).symm
  rw [card_anchored u hu]
  exact card_le_of_isClique K' hK'

/-- The tier-`1` cell is maximal (`N ≥ 2`, `m ≥ 1`). -/
theorem isMaxClique_tier1 (hN : 2 ≤ N) (hm : 1 ≤ m) : IsMaxClique (tier1 N m) := by
  refine ⟨isClique_tier1 N m, ?_⟩
  intro K' hK' hsub
  rcases isClique_subset K' hK' with ⟨u, hu⟩ | ht
  · have hsingle : tier1 N m ⊆ {u} := by
      intro v hv
      have hv1 : v.tier = 1 := by simpa [tier1] using hv
      have hmem := hu (hsub hv)
      simp only [anchored, mem_insert] at hmem
      rcases hmem with rfl | hchi
      · exact mem_singleton_self _
      · have hlen : v.1.length = u.1.length + 1 := by
          simp only [chiF, mem_filter, mem_univ, true_and] at hchi
          exact hchi.1
        have hpos := Addr.one_le_tier u
        unfold Addr.tier at *
        omega
    have hc := card_le_card hsingle
    rw [card_tier1 N m hm, card_singleton] at hc
    omega
  · exact Subset.antisymm ht hsub

/-- **Maximal cliques classified** (Lemma lem:maxclique): for `N ≥ 2`, `m ≥ 1`, a finite
set is a maximal clique iff it is the tier-`1` cell or the anchored clique of a
non-leaf node. -/
theorem isMaxClique_iff (hN : 2 ≤ N) (hm : 1 ≤ m) (K : Finset (Addr N m)) :
    IsMaxClique K ↔ K = tier1 N m ∨ ∃ u : Addr N m, u.tier < m ∧ K = anchored u := by
  constructor
  · intro hK
    rcases isClique_subset K hK.1 with ⟨u, hu⟩ | ht
    · have heq : K = anchored u := (hK.2 _ (isClique_anchored u) hu).symm
      by_cases hlt : u.tier < m
      · exact Or.inr ⟨u, hlt, heq⟩
      have hchi : chiF u = ∅ := by
        apply card_eq_zero.mp
        rw [card_chi, if_neg hlt]
      have hsingle : K = {u} := by simpa [anchored, hchi] using heq
      by_cases hu1 : u.tier = 1
      · have hsub : K ⊆ tier1 N m := by
          rw [hsingle]
          simpa [tier1] using hu1
        have heq' := hK.2 _ (isClique_tier1 N m) hsub
        have hc := congrArg Finset.card heq'
        rw [card_tier1 N m hm, hsingle, card_singleton] at hc
        omega
      · have hu2 : 2 ≤ u.1.length := by
          have := Addr.one_le_tier u
          unfold Addr.tier at *
          omega
        let p : Addr N m := ⟨u.1.dropLast,
          List.ne_nil_of_length_pos (by rw [List.length_dropLast]; omega),
          by rw [List.length_dropLast]; have := u.2.2; omega⟩
        have hp : p.tier < m := by
          dsimp [p, Addr.tier]
          rw [List.length_dropLast]
          have := u.2.2
          omega
        have hup : u ∈ anchored p := by
          apply mem_insert_of_mem
          simp only [chiF, mem_filter, mem_univ, true_and]
          change u.1.length = u.1.dropLast.length + 1 ∧ u.1.dropLast = u.1.dropLast
          rw [List.length_dropLast]
          exact ⟨by omega, rfl⟩
        have heq' := hK.2 _ (isClique_anchored p)
          (by simpa only [hsingle, singleton_subset_iff] using hup)
        have hc := congrArg Finset.card heq'
        rw [card_anchored p hp, hsingle, card_singleton] at hc
        omega
    · exact Or.inl (hK.2 _ (isClique_tier1 N m) ht).symm
  · rintro (rfl | ⟨u, hu, rfl⟩)
    · exact isMaxClique_tier1 hN hm
    · exact isMaxClique_anchored hN u hu

end HSFN
