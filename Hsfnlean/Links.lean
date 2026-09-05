/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Degree

/-!
# Link count of the HSFN (Theorem thm:deg-II(ii))

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
The link count `L = N(N-1)/2 + N(N+1)(N^m - N)/(2(N-1))` is stated here in the
subtraction-free form `(N-1)·2L = N (N-1)^2 + N (N+1) (N^m - N)` with `N = n+1`.
The statements below are frozen; only the proofs are to be supplied.
-/

namespace HSFN

open Finset

/-- Handshake lemma specialised to the HSFN graph: twice the number of links
is the sum of all degrees. -/
theorem two_mul_card_edges (N m : ℕ) :
    2 * (graph N m).edgeFinset.card = ∑ v, (graph N m).degree v :=
  (SimpleGraph.sum_degrees_eq_twice_card_edges (graph N m)).symm

private theorem aux_pow_degree_leaf (N t : ℕ) (ht : 1 ≤ t) :
    N ^ t * ((N - 1) + 1) = N ^ t * N := by
  cases N with
  | zero => simp [zero_pow (show t ≠ 0 by omega)]
  | succ n => simp

private theorem aux_pow_degree_interior (N t : ℕ) (ht : 1 ≤ t) :
    N ^ t * ((N - 1) + 1 + N) = N ^ t * (2 * N) := by
  cases N with
  | zero => simp [zero_pow (show t ≠ 0 by omega)]
  | succ n => simp; ring

private theorem aux_sum_degree_by_tier (N m : ℕ) (_hm : 1 ≤ m) :
    ∑ v, (graph N m).degree v =
      ∑ t ∈ Icc 1 m,
        N ^ t * ((N - 1) + (if 2 ≤ t then 1 else 0) + (if t < m then N else 0)) := by
  classical
  have hmaps : ∀ v ∈ (univ : Finset (Addr N m)), v.tier ∈ Icc 1 m := by
    intro v _
    simp [mem_Icc, Addr.one_le_tier, Addr.tier_le]
  simp_rw [degree_eq]
  rw [← sum_fiberwise_of_maps_to' hmaps
      (fun t => (N - 1) + (if 2 ≤ t then 1 else 0) + (if t < m then N else 0))]
  refine sum_congr rfl fun t ht => ?_
  have hcard : #{v ∈ univ | (v : Addr N m).tier = t} = N ^ t := by
    simp only [mem_Icc] at ht
    rw [← Fintype.card_subtype]
    exact Addr.card_tier N m t ht.1 ht.2
  rw [sum_const, Nat.nsmul_eq_mul, hcard]

/-- The degree sum by tiers. Tier `1` holds `N` nodes of degree
`(N-1) + N·[1 < m]`, tiers `2 … m-1` hold `N^t` nodes of degree `2N`, and
tier `m` (for `m ≥ 2`) holds `N^m` nodes of degree `N`. -/
theorem sum_degree_eq (N m : ℕ) (hm : 1 ≤ m) :
    ∑ v, (graph N m).degree v =
      N * ((N - 1) + (if 1 < m then N else 0)) +
        (∑ t ∈ Finset.Ico 2 m, N ^ t * (2 * N)) +
        (if 2 ≤ m then N ^ m * N else 0) := by
  rw [aux_sum_degree_by_tier N m hm]
  have hIcc : Icc 1 m = insert 1 (Icc 2 m) := by
    ext x
    simp only [mem_insert, mem_Icc]
    omega
  have h1 : 1 ∉ Icc 2 m := by simp [mem_Icc]
  rw [hIcc, sum_insert h1]
  have htier1 :
      N ^ 1 * ((N - 1) + (if 2 ≤ 1 then 1 else 0) + (if 1 < m then N else 0)) =
        N * ((N - 1) + (if 1 < m then N else 0)) := by
    simp
  rw [htier1]
  by_cases hm2 : 2 ≤ m
  · have hIcc2 : Icc 2 m = insert m (Ico 2 m) := by
      ext x
      simp only [mem_insert, mem_Icc, mem_Ico]
      omega
    have hm_not : m ∉ Ico 2 m := by simp [mem_Ico]
    have hleaf :
        N ^ m * ((N - 1) + (if 2 ≤ m then 1 else 0) + (if m < m then N else 0)) =
          N ^ m * N := by
      simp only [if_pos hm2, lt_irrefl, ite_false, add_zero]
      exact aux_pow_degree_leaf N m (le_trans (by omega : 1 ≤ 2) hm2)
    have hinter :
        ∑ t ∈ Ico 2 m,
            N ^ t * ((N - 1) + (if 2 ≤ t then 1 else 0) + (if t < m then N else 0)) =
          ∑ t ∈ Ico 2 m, N ^ t * (2 * N) := by
      refine sum_congr rfl fun t ht => ?_
      have ht' : 2 ≤ t ∧ t < m := mem_Ico.mp ht
      simp only [if_pos ht'.1, if_pos ht'.2]
      exact aux_pow_degree_interior N t (le_trans (by omega : 1 ≤ 2) ht'.1)
    rw [if_pos hm2, hIcc2, sum_insert hm_not, hleaf, hinter]
    abel
  · have hempty : Icc 2 m = ∅ := by
      ext x
      simp only [mem_Icc, notMem_empty, iff_false]
      omega
    have hempty' : Ico 2 m = ∅ := by
      ext x
      simp only [mem_Ico, notMem_empty, iff_false]
      omega
    simp [if_neg hm2, hempty, hempty']

private theorem aux_geom (n k : ℕ) :
    n * ∑ t ∈ range k, (n + 1) ^ t + 1 = (n + 1) ^ k := by
  rw [mul_comm n]
  exact geom_sum_mul_add n k

private theorem aux_closed (n m : ℕ) (hm : 1 ≤ m) :
    n *
        ((n + 1) * (n + (if 1 < m then n + 1 else 0)) +
          (∑ t ∈ Ico 2 m, (n + 1) ^ t * (2 * (n + 1))) +
          (if 2 ≤ m then (n + 1) ^ (m + 1) else 0)) =
      (n + 1) * n ^ 2 + (n + 1) * (n + 2) * ((n + 1) ^ m - (n + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  cases k with
  | zero =>
      simp [pow_one]
      ring
  | succ j =>
      set N := n + 1
      have hm1 : 1 < j + 1 + 1 := by omega
      have hm2 : 2 ≤ j + 1 + 1 := by omega
      simp only [if_pos hm1, if_pos hm2]
      have hsum :
          ∑ t ∈ Ico 2 (j + 1 + 1), N ^ t = N ^ 2 * ∑ i ∈ range j, N ^ i := by
        rw [sum_Ico_eq_sum_range]
        change ∑ i ∈ range ((j + 2) - 2), N ^ (2 + i) = _
        simp only [Nat.add_sub_cancel]
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [pow_add, pow_two, mul_assoc]
      have hinter :
          ∑ t ∈ Ico 2 (j + 1 + 1), N ^ t * (2 * N) =
            2 * N ^ 3 * ∑ i ∈ range j, N ^ i := by
        simp_rw [mul_comm (N ^ _) (2 * N), ← mul_sum, hsum]
        ring
      rw [hinter]
      set G := ∑ i ∈ range j, N ^ i
      have hgeom : n * G + 1 = N ^ j := aux_geom n j
      have hextra :
          n * N ^ 2 + 2 * n * N ^ 3 * G + n * N ^ (j + 3) + N ^ 2 * (N + 1) =
            N * (N + 1) * N ^ (j + 2) := by
        calc
          n * N ^ 2 + 2 * n * N ^ 3 * G + n * N ^ (j + 3) + N ^ 2 * (N + 1)
              = n * N ^ 2 + 2 * n * N ^ 3 * G + n * N ^ (j + 3) + (N ^ 3 + N ^ 2) := by
                ring
            _ = (n * N ^ 2 + N ^ 2) + 2 * n * N ^ 3 * G + n * N ^ (j + 3) + N ^ 3 := by
                ring
            _ = N ^ 3 + 2 * n * N ^ 3 * G + n * N ^ (j + 3) + N ^ 3 := by
                have : n * N ^ 2 + N ^ 2 = N ^ 3 := by
                  have hN3 : N ^ 3 = N * N ^ 2 := by rw [pow_succ']
                  rw [hN3]
                  ring
                rw [this]
            _ = 2 * N ^ 3 * (n * G + 1) + n * N ^ (j + 3) := by
                ring
            _ = 2 * N ^ 3 * N ^ j + n * N ^ (j + 3) := by
                rw [hgeom]
            _ = (n + 2) * N ^ (j + 3) := by
                have : 2 * N ^ 3 * N ^ j = 2 * N ^ (j + 3) := by
                  rw [mul_assoc, ← pow_add]
                  congr 1
                  ring
                rw [this]
                ring
            _ = N * (N + 1) * N ^ (j + 2) := by
                have : N ^ (j + 3) = N * N ^ (j + 2) := by
                  rw [pow_succ']
                rw [this]
                ring
      have hLHS :
          n *
              (N * (n + N) + 2 * N ^ 3 * G + N ^ (j + 1 + 1 + 1)) =
            n * N ^ 2 + 2 * n * N ^ 3 * G + n * N ^ (j + 3) + N * n ^ 2 := by
        ring
      rw [hLHS]
      have hle : N ≤ N ^ (j + 2) := Nat.le_self_pow (by omega : j + 2 ≠ 0) N
      have : n * N ^ 2 + 2 * n * N ^ 3 * G + n * N ^ (j + 3) =
          N * (N + 1) * (N ^ (j + 2) - N) := by
        have hB : N ^ 2 * (N + 1) = N * (N + 1) * N := by ring
        calc
          n * N ^ 2 + 2 * n * N ^ 3 * G + n * N ^ (j + 3)
              = n * N ^ 2 + 2 * n * N ^ 3 * G + n * N ^ (j + 3) +
                  N ^ 2 * (N + 1) - N ^ 2 * (N + 1) := by
                rw [Nat.add_sub_cancel]
            _ = N * (N + 1) * N ^ (j + 2) - N * (N + 1) * N := by
                rw [hextra, hB]
            _ = N * (N + 1) * (N ^ (j + 2) - N) := by
                rw [Nat.mul_sub_left_distrib]
      rw [this]
      ring

/-- **Link count** (Theorem thm:deg-II(ii)), subtraction-free closed form with
`N = n + 1`: `n · 2L = N n^2 + N (N+1) (N^m - N)`. -/
theorem card_edges_closed (n m : ℕ) (hm : 1 ≤ m) :
    n * (2 * (graph (n + 1) m).edgeFinset.card) =
      (n + 1) * n ^ 2 + (n + 1) * (n + 2) * ((n + 1) ^ m - (n + 1)) := by
  rw [two_mul_card_edges, sum_degree_eq (n + 1) m hm]
  simp only [Nat.add_sub_cancel]
  have hleaf :
      (if 2 ≤ m then (n + 1) ^ m * (n + 1) else 0) =
        (if 2 ≤ m then (n + 1) ^ (m + 1) else 0) := by
    split_ifs
    · rw [pow_succ]
    · rfl
  rw [hleaf]
  exact aux_closed n m hm

end HSFN
