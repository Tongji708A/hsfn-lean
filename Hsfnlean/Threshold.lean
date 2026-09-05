/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Mathlib

/-!
# Depth-uniform reliability threshold (Theorem prop:threshold-b, items 2–3; Corollary thm:threshold)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
With `k = ⌈b/2⌉`, the level map is `f_b(x) = 1 - (1-q) S_b(x)` where
`S_b(x) = P[Bin(b,x) ≤ k-1]`. The union bound `1 - S_b(x) ≤ C(b,k) x^k` makes the
interval `[q, 2q]` invariant under `f_b` whenever `2^k C(b,k) q^{k-1} < 1`, which is
the polynomial form of `q < q_0(N,b)`; hence every iterate from `q` stays below `2q`.
The survivor-side union bound gives the upper bracket of the threshold: for
`q > 1 - C(b, ⌊b/2⌋+1)^{-1}` the map satisfies `f_b(x) > x` on `[0,1)`.
The dense-variant root correction is the same union bound at the root.
Everything here is real algebra; no probability theory is invoked.
The statements below are frozen; only the proofs are to be supplied.
-/

namespace HSFN

open Finset

noncomputable section

/-- Lower binomial tail `P[Bin(b,x) ≤ k-1] = ∑_{i<k} C(b,i) x^i (1-x)^{b-i}`. -/
def binTail (b k : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ range k, (b.choose i : ℝ) * x ^ i * (1 - x) ^ (b - i)

/-- `⌈b/2⌉` as a natural number. -/
def half (b : ℕ) : ℕ := (b + 1) / 2

/-- `S_b(x) = P[Bin(b,x) ≤ ⌈b/2⌉ - 1]`, the probability that fewer than half of `b`
children fail when each fails independently with probability `x`. -/
def S (b : ℕ) (x : ℝ) : ℝ := binTail b (half b) x

/-- The level recursion `f_b(x) = 1 - (1-q) S_b(x)` (Theorem thm:security). -/
def f (b : ℕ) (q x : ℝ) : ℝ := 1 - (1 - q) * S b x

/-- The polynomial form of `q < q_0(N,b)`: `2^k C(b,k) q^{k-1} < 1` with `k = ⌈b/2⌉`. -/
def BelowQ0 (b : ℕ) (q : ℝ) : Prop :=
  (2 : ℝ) ^ half b * (b.choose (half b) : ℝ) * q ^ (half b - 1) < 1

/-- `q_0(N,b) = [2^k C(b,k)]^{-1/(k-1)}` with `k = ⌈b/2⌉` (real power). -/
def q0 (b : ℕ) : ℝ :=
  ((2 : ℝ) ^ half b * (b.choose (half b) : ℝ)) ^ (-(1 : ℝ) / ((half b : ℝ) - 1))

variable {b k : ℕ} {q x : ℝ}

private theorem aux_term_nonneg (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (i : ℕ) :
    0 ≤ (b.choose i : ℝ) * x ^ i * (1 - x) ^ (b - i) :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
    (pow_nonneg (sub_nonneg.mpr hx1) _)

private theorem aux_binTail_full (b : ℕ) (x : ℝ) :
    ∑ i ∈ range (b + 1), (b.choose i : ℝ) * x ^ i * (1 - x) ^ (b - i) = 1 := by
  have h := add_pow x (1 - x) b
  have hx1 : x + (1 - x) = (1 : ℝ) := by ring
  rw [hx1, one_pow] at h
  convert h.symm using 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem aux_binTail_eq_min (b k : ℕ) (x : ℝ) :
    binTail b k x = binTail b (min k (b + 1)) x := by
  unfold binTail
  obtain hle | hge := le_total k (b + 1)
  · rw [min_eq_left hle]
  · rw [min_eq_right hge]
    have hs : range (b + 1) ⊆ range k := Finset.range_subset_range.mpr hge
    have hsum := Finset.sum_sdiff (s₁ := range (b + 1)) (s₂ := range k)
      (f := fun i => (b.choose i : ℝ) * x ^ i * (1 - x) ^ (b - i)) hs
    have hextra :
        ∑ i ∈ range k \ range (b + 1),
          (b.choose i : ℝ) * x ^ i * (1 - x) ^ (b - i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have : b < i := by
        simp only [Finset.mem_sdiff, Finset.mem_range] at hi
        omega
      simp [Nat.choose_eq_zero_of_lt this]
    linarith

private theorem aux_one_sub_binTail (_hx0 : 0 ≤ x) (_hx1 : x ≤ 1) (hk : k ≤ b + 1) :
    1 - binTail b k x =
      ∑ i ∈ Ico k (b + 1), (b.choose i : ℝ) * x ^ i * (1 - x) ^ (b - i) := by
  have hfull := aux_binTail_full b x
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i => (b.choose i : ℝ) * x ^ i * (1 - x) ^ (b - i)) hk
  unfold binTail
  linarith

private theorem aux_half_le (b : ℕ) : half b ≤ b := by
  unfold half
  omega

private theorem aux_half_ge_two (hb : 3 ≤ b) : 2 ≤ half b := by
  unfold half
  omega

private theorem aux_binTail_reflect (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hk : k ≤ b) :
    1 - binTail b k x = binTail b (b - k + 1) (1 - x) := by
  have hk' : k ≤ b + 1 := Nat.le_succ_of_le hk
  rw [aux_one_sub_binTail hx0 hx1 hk']
  let f : ℕ → ℝ := fun j =>
    (b.choose j : ℝ) * (1 - x) ^ j * x ^ (b - j)
  have hterm : ∀ j ∈ Ico k (b + 1),
      (b.choose j : ℝ) * x ^ j * (1 - x) ^ (b - j) = f (b - j) := by
    intro j hj
    have hjb : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hj).2
    have hsym : (b.choose (b - j) : ℝ) = (b.choose j : ℝ) := by
      exact_mod_cast Nat.choose_symm hjb
    have hsub : b - (b - j) = j := Nat.sub_sub_self hjb
    simp only [f, hsym, hsub]
    ring
  have h1 :
      ∑ j ∈ Ico k (b + 1), (b.choose j : ℝ) * x ^ j * (1 - x) ^ (b - j) =
        ∑ j ∈ Ico k (b + 1), f (b - j) :=
    Finset.sum_congr rfl hterm
  have hrefl := Finset.sum_Ico_reflect f k (n := b) (m := b + 1) le_rfl
  have hlen : b + 1 - k = b - k + 1 := Nat.succ_sub hk
  unfold binTail
  rw [h1, hrefl]
  change ∑ j ∈ Ico (b + 1 - (b + 1)) (b + 1 - k), f j = _
  simp only [Nat.sub_self]
  rw [Nat.Ico_zero_eq_range, hlen]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [f, sub_sub_cancel]

theorem binTail_nonneg (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ binTail b k x := by
  unfold binTail
  exact Finset.sum_nonneg fun i _ => aux_term_nonneg hx0 hx1 i

/-- A partial binomial sum is at most the full sum `(x + (1-x))^b = 1`. -/
theorem binTail_le_one (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : binTail b k x ≤ 1 := by
  have hmin := aux_binTail_eq_min b k x
  have hsub : range (min k (b + 1)) ⊆ range (b + 1) :=
    Finset.range_subset_range.mpr (min_le_right _ _)
  rw [hmin]
  unfold binTail
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_).trans_eq (aux_binTail_full b x)
  intro i _ _
  exact aux_term_nonneg hx0 hx1 i

/-- **Union bound over `k`-subsets of failing children**:
`P[Bin(b,x) ≥ k] ≤ C(b,k) x^k`. -/
theorem one_sub_binTail_le (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hk : k ≤ b) :
    1 - binTail b k x ≤ (b.choose k : ℝ) * x ^ k := by
  have hk' : k ≤ b + 1 := Nat.le_succ_of_le hk
  rw [aux_one_sub_binTail hx0 hx1 hk']
  have hterm : ∀ i ∈ Ico k (b + 1),
      (b.choose i : ℝ) * x ^ i * (1 - x) ^ (b - i) ≤
        (b.choose k : ℝ) * ((b - k).choose (i - k) : ℝ) * x ^ i * (1 - x) ^ (b - i) := by
    intro i hi
    have hik : k ≤ i := (Finset.mem_Ico.mp hi).1
    have hC : (b.choose i : ℝ) ≤
        (b.choose k : ℝ) * ((b - k).choose (i - k) : ℝ) := by
      have hmul : (b.choose i : ℝ) * (i.choose k : ℝ) =
          (b.choose k : ℝ) * ((b - k).choose (i - k) : ℝ) := by
        exact_mod_cast Nat.choose_mul hik
      have hge : (1 : ℝ) ≤ (i.choose k : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt (Nat.choose_pos hik))
      calc
        (b.choose i : ℝ) = (b.choose i : ℝ) * 1 := by ring
        _ ≤ (b.choose i : ℝ) * (i.choose k : ℝ) :=
          mul_le_mul_of_nonneg_left hge (Nat.cast_nonneg _)
        _ = (b.choose k : ℝ) * ((b - k).choose (i - k) : ℝ) := hmul
    have hxnn : 0 ≤ x ^ i := pow_nonneg hx0 _
    have hynn : 0 ≤ (1 - x) ^ (b - i) := pow_nonneg (sub_nonneg.mpr hx1) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hxnn) hynn
  refine (Finset.sum_le_sum hterm).trans ?_
  have hfactor :
      (∑ i ∈ Ico k (b + 1),
          (b.choose k : ℝ) * ((b - k).choose (i - k) : ℝ) * x ^ i * (1 - x) ^ (b - i)) =
        (b.choose k : ℝ) * x ^ k *
          ∑ j ∈ range (b - k + 1),
            ((b - k).choose j : ℝ) * x ^ j * (1 - x) ^ (b - k - j) := by
    have hpull :
        ∑ i ∈ Ico k (b + 1),
            (b.choose k : ℝ) * ((b - k).choose (i - k) : ℝ) * x ^ i * (1 - x) ^ (b - i) =
          (b.choose k : ℝ) *
            ∑ i ∈ Ico k (b + 1),
              ((b - k).choose (i - k) : ℝ) * x ^ i * (1 - x) ^ (b - i) := by
      have hform :
          ∀ i,
            (b.choose k : ℝ) * ((b - k).choose (i - k) : ℝ) * x ^ i * (1 - x) ^ (b - i) =
              (b.choose k : ℝ) *
                (((b - k).choose (i - k) : ℝ) * x ^ i * (1 - x) ^ (b - i)) := by
        intro i
        ring
      simp_rw [hform]
      rw [← Finset.mul_sum]
    rw [hpull, Finset.sum_Ico_eq_sum_range]
    have hlen : b + 1 - k = b - k + 1 := Nat.succ_sub hk
    rw [hlen]
    have hreidx :
        ∑ j ∈ range (b - k + 1),
            ((b - k).choose (k + j - k) : ℝ) * x ^ (k + j) * (1 - x) ^ (b - (k + j)) =
          ∑ j ∈ range (b - k + 1),
            ((b - k).choose j : ℝ) * (x ^ k * x ^ j) * (1 - x) ^ (b - k - j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : k + j - k = j := Nat.add_sub_cancel_left k j
      have hpow : x ^ (k + j) = x ^ k * x ^ j := pow_add _ _ _
      have hsub : b - (k + j) = b - k - j := Nat.sub_add_eq b k j
      rw [hjk, hpow, hsub]
    rw [hreidx]
    have hpullx :
        ∑ j ∈ range (b - k + 1),
            ((b - k).choose j : ℝ) * (x ^ k * x ^ j) * (1 - x) ^ (b - k - j) =
          x ^ k *
            ∑ j ∈ range (b - k + 1),
              ((b - k).choose j : ℝ) * x ^ j * (1 - x) ^ (b - k - j) := by
      have :
          ∑ j ∈ range (b - k + 1),
              ((b - k).choose j : ℝ) * (x ^ k * x ^ j) * (1 - x) ^ (b - k - j) =
            ∑ j ∈ range (b - k + 1),
              x ^ k * (((b - k).choose j : ℝ) * x ^ j * (1 - x) ^ (b - k - j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [this, ← Finset.mul_sum]
    rw [hpullx]
    ring
  rw [hfactor, aux_binTail_full (b - k) x]
  simp

/-- `f_b(x) ≥ q` on `[0,1]`. -/
theorem q_le_f (hq1 : q ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : q ≤ f b q x := by
  have hS0 := binTail_nonneg (b := b) (k := half b) hx0 hx1
  have hS1 := binTail_le_one (b := b) (k := half b) hx0 hx1
  unfold f S
  nlinarith

/-- `f_b(x) ≤ 1` on `[0,1]` for `q ≤ 1`. -/
theorem f_le_one (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : f b q x ≤ 1 := by
  have hS0 := binTail_nonneg (b := b) (k := half b) hx0 hx1
  have := hq0
  unfold f S
  nlinarith

/-- Below `q_0` the trap fits inside `[0,1]`: `2q < 1`. Uses `b ≥ 3` (so `k ≥ 2`). -/
theorem two_mul_lt_one_of_belowQ0 (hb : 3 ≤ b) (hq0 : 0 < q) (h : BelowQ0 b q) : 2 * q < 1 := by
  have hk := aux_half_ge_two hb
  have hhalf := aux_half_le b
  have := hq0
  by_contra hne
  have h2q : 1 ≤ 2 * q := le_of_not_gt hne
  have hkeq : half b - 1 + 1 = half b := Nat.sub_add_cancel (by omega)
  have hident : (2 : ℝ) ^ half b * q ^ (half b - 1) = 2 * (2 * q) ^ (half b - 1) := by
    calc
      (2 : ℝ) ^ half b * q ^ (half b - 1)
          = (2 : ℝ) ^ (half b - 1 + 1) * q ^ (half b - 1) := by rw [hkeq]
      _ = (2 * (2 : ℝ) ^ (half b - 1)) * q ^ (half b - 1) := by rw [pow_succ']
      _ = 2 * ((2 : ℝ) ^ (half b - 1) * q ^ (half b - 1)) := by ring
      _ = 2 * (2 * q) ^ (half b - 1) := by rw [mul_pow]
  have hge : (1 : ℝ) ≤ (2 * q) ^ (half b - 1) := one_le_pow₀ h2q
  have hC : (1 : ℝ) ≤ (b.choose (half b) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.choose_pos hhalf))
  unfold BelowQ0 at h
  have heq : (2 : ℝ) ^ half b * (b.choose (half b) : ℝ) * q ^ (half b - 1) =
      (b.choose (half b) : ℝ) * (2 * (2 * q) ^ (half b - 1)) := by
    calc
      (2 : ℝ) ^ half b * (b.choose (half b) : ℝ) * q ^ (half b - 1)
          = (b.choose (half b) : ℝ) * ((2 : ℝ) ^ half b * q ^ (half b - 1)) := by ring
      _ = (b.choose (half b) : ℝ) * (2 * (2 * q) ^ (half b - 1)) := by rw [hident]
  nlinarith

/-- **Invariant interval** (Theorem prop:threshold-b, item 2): for `b ≥ 3` and
`q < q_0`, `f_b` maps `[q, 2q]` into itself. -/
theorem f_mem_Icc (hb : 3 ≤ b) (hq0 : 0 < q) (h : BelowQ0 b q)
    (hx : x ∈ Set.Icc q (2 * q)) : f b q x ∈ Set.Icc q (2 * q) := by
  have h2q := two_mul_lt_one_of_belowQ0 hb hq0 h
  have hx0 : 0 ≤ x := le_trans (le_of_lt hq0) hx.1
  have hx1 : x ≤ 1 := le_trans hx.2 (le_of_lt h2q)
  have hq1 : q ≤ 1 := le_trans hx.1 hx1
  refine ⟨q_le_f hq1 hx0 hx1, ?_⟩
  have hk := aux_half_le b
  have hS := one_sub_binTail_le (b := b) (k := half b) hx0 hx1 hk
  have hf : f b q x = q + (1 - q) * (1 - S b x) := by
    unfold f
    exact (by ring : (1 : ℝ) - (1 - q) * S b x = q + (1 - q) * (1 - S b x))
  have h1S : 0 ≤ 1 - S b x := sub_nonneg.mpr (binTail_le_one hx0 hx1)
  have h1q1 : 1 - q ≤ 1 := by linarith
  have hprod : (1 - q) * (1 - S b x) ≤ 1 - S b x :=
    mul_le_of_le_one_left h1S h1q1
  have hxpow : x ^ half b ≤ (2 * q) ^ half b := pow_le_pow_left₀ hx0 hx.2 _
  have hC : (0 : ℝ) ≤ b.choose (half b) := Nat.cast_nonneg _
  have hCx : (b.choose (half b) : ℝ) * x ^ half b ≤
      (b.choose (half b) : ℝ) * (2 * q) ^ half b :=
    mul_le_mul_of_nonneg_left hxpow hC
  have hk2 := aux_half_ge_two hb
  have hkeq : half b - 1 + 1 = half b := Nat.sub_add_cancel (by omega)
  have hrew : (b.choose (half b) : ℝ) * (2 * q) ^ half b =
      ((2 : ℝ) ^ half b * (b.choose (half b) : ℝ) * q ^ (half b - 1)) * q := by
    have hmul : (2 * q) ^ half b = (2 : ℝ) ^ half b * q ^ half b := mul_pow _ _ _
    have hqpow : q ^ half b = q ^ (half b - 1) * q := by
      conv_lhs => rw [← hkeq]
      exact pow_succ q (half b - 1)
    rw [hmul, hqpow]
    ring
  have hB : (2 : ℝ) ^ half b * (b.choose (half b) : ℝ) * q ^ (half b - 1) < 1 := h
  have hstrict : (b.choose (half b) : ℝ) * (2 * q) ^ half b < q := by
    rw [hrew]
    have hlt := mul_lt_mul_of_pos_right hB hq0
    rwa [one_mul] at hlt
  have hS' : 1 - S b x = 1 - binTail b (half b) x := rfl
  calc
    f b q x = q + (1 - q) * (1 - S b x) := hf
    _ ≤ q + (1 - S b x) := by linarith
    _ ≤ q + (b.choose (half b) : ℝ) * x ^ half b := by
      rw [hS']
      linarith
    _ ≤ q + (b.choose (half b) : ℝ) * (2 * q) ^ half b := by linarith
    _ ≤ 2 * q := by linarith

/-- **Depth-uniform bound** (Theorem prop:threshold-b, item 2): every iterate of
`f_b` started at `q` stays in `[q, 2q]`, hence `P_1^{II} = f_N^{m-1}(q) ≤ 2q`
(Corollary cor:threshold-II with `b = N`). -/
theorem iterate_mem_Icc (hb : 3 ≤ b) (hq0 : 0 < q) (h : BelowQ0 b q) (n : ℕ) :
    (f b q)^[n] q ∈ Set.Icc q (2 * q) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id]
    exact ⟨le_rfl, by nlinarith [hq0]⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact f_mem_Icc hb hq0 h ih

theorem iterate_le_two_mul (hb : 3 ≤ b) (hq0 : 0 < q) (h : BelowQ0 b q) (n : ℕ) :
    (f b q)^[n] q ≤ 2 * q :=
  (iterate_mem_Icc hb hq0 h n).2

/-- The real-power form agrees with the polynomial form: `q < q_0(N,b) ↔ 2^k C(b,k) q^{k-1} < 1`
for `b ≥ 3`, `q > 0`. -/
theorem lt_q0_iff (hb : 3 ≤ b) (hq0 : 0 < q) : q < q0 b ↔ BelowQ0 b q := by
  set k := half b with hkdef
  set A := (2 : ℝ) ^ k * (b.choose k : ℝ)
  set e := (k : ℝ) - 1
  have hk : 2 ≤ k := by rw [hkdef]; exact aux_half_ge_two hb
  have hk1 : 1 ≤ k := by omega
  have hke : 0 < e := by
    have : (1 : ℝ) ≤ (k : ℝ) - 1 := by
      exact_mod_cast (show 1 ≤ k - 1 by omega)
    linarith
  have hA : 0 < A := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) _
    have hC : (0 : ℝ) < (b.choose k : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos (by rw [hkdef]; exact aux_half_le b))
    exact mul_pos h2 hC
  have hq0eq : q0 b = A ^ (-(1 : ℝ) / e) := by
    simp only [q0, A, e, k]
  have hpowq : q ^ e = q ^ (k - 1) := by
    have heq : e = ((k - 1 : ℕ) : ℝ) := by
      simp only [e]
      rw [Nat.cast_sub hk1, Nat.cast_one]
    rw [heq, Real.rpow_natCast]
  have hiff1 : q < A ^ (-(1 : ℝ) / e) ↔ q ^ e < A⁻¹ := by
    have hnonneg : 0 ≤ A ^ (-(1 : ℝ) / e) := Real.rpow_nonneg hA.le _
    have hmul : (-(1 : ℝ) / e) * e = -1 := by field_simp
    constructor
    · intro hlt
      have := (Real.rpow_lt_rpow_iff hq0.le hnonneg hke).mpr hlt
      rwa [← Real.rpow_mul hA.le, hmul, Real.rpow_neg_one] at this
    · intro hlt
      have h' : (A ^ (-(1 : ℝ) / e)) ^ e = A⁻¹ := by
        rw [← Real.rpow_mul hA.le, hmul, Real.rpow_neg_one]
      have := (Real.rpow_lt_rpow_iff hq0.le hnonneg hke).mp (h'.symm ▸ hlt)
      exact this
  have hiff2 : q ^ e < A⁻¹ ↔ A * q ^ (k - 1) < 1 := by
    rw [hpowq]
    constructor
    · intro hlt
      have := mul_lt_mul_of_pos_left hlt hA
      have hA1 : A * A⁻¹ = 1 := mul_inv_cancel₀ hA.ne'
      rwa [hA1] at this
    · intro hlt
      have hA1 : A * A⁻¹ = 1 := mul_inv_cancel₀ hA.ne'
      have : A * q ^ (k - 1) < A * A⁻¹ := by
        rwa [hA1]
      exact (mul_lt_mul_iff_right₀ hA).mp this
  change q < q0 b ↔ (2 : ℝ) ^ half b * (b.choose (half b) : ℝ) * q ^ (half b - 1) < 1
  rw [hq0eq, hiff1, hiff2]

/-- **Upper bracket of the threshold** (Theorem prop:threshold-b, item 3): if
`q > 1 - C(b, ⌊b/2⌋+1)^{-1}` then `f_b(x) > x` for every `x ∈ [0,1)`, so `1` is the
only fixed point. -/
theorem lt_f_of_large_q (hb : 1 ≤ b) (hq : 1 - 1 / (b.choose (b / 2 + 1) : ℝ) < q) (hq1 : q ≤ 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) : x < f b q x := by
  have hx1' : x ≤ 1 := le_of_lt hx1
  have h1x0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1'
  have h1x1 : 1 - x ≤ 1 := by linarith
  have hj : b / 2 + 1 = b - half b + 1 := by
    unfold half
    omega
  have hjb : b / 2 + 1 ≤ b := by
    have : 1 ≤ half b := by
      unfold half
      omega
    omega
  have hS : S b x = 1 - binTail b (b / 2 + 1) (1 - x) := by
    unfold S
    have hrefl := aux_binTail_reflect (b := b) (k := half b) hx0 hx1' (aux_half_le b)
    rw [← hj] at hrefl
    linarith
  have hbound : S b x ≤ (b.choose (b / 2 + 1) : ℝ) * (1 - x) ^ (b / 2 + 1) := by
    have := one_sub_binTail_le (b := b) (k := b / 2 + 1) (x := 1 - x) h1x0 h1x1 hjb
    linarith
  have h1q : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hCnn : (0 : ℝ) ≤ b.choose (b / 2 + 1) := Nat.cast_nonneg _
  have hpow : (1 - x) ^ (b / 2 + 1) ≤ 1 - x := by
    rw [pow_succ]
    exact mul_le_of_le_one_left h1x0 (pow_le_one₀ h1x0 h1x1)
  have hCpos : (0 : ℝ) < b.choose (b / 2 + 1) :=
    Nat.cast_pos.mpr (Nat.choose_pos hjb)
  have hstrictC : (1 - q) * (b.choose (b / 2 + 1) : ℝ) < 1 := by
    have : 1 - q < 1 / (b.choose (b / 2 + 1) : ℝ) := by linarith
    have hmul := mul_lt_mul_of_pos_right this hCpos
    have hcancel : (1 / (b.choose (b / 2 + 1) : ℝ)) * (b.choose (b / 2 + 1) : ℝ) = 1 :=
      div_mul_cancel₀ _ hCpos.ne'
    rwa [hcancel] at hmul
  have h1 : (1 - q) * S b x ≤
      (1 - q) * (b.choose (b / 2 + 1) : ℝ) * (1 - x) ^ (b / 2 + 1) := by
    have := mul_le_mul_of_nonneg_left hbound h1q
    linarith
  have h2 : (1 - q) * (b.choose (b / 2 + 1) : ℝ) * (1 - x) ^ (b / 2 + 1) ≤
      (1 - q) * (b.choose (b / 2 + 1) : ℝ) * (1 - x) :=
    mul_le_mul_of_nonneg_left hpow (mul_nonneg h1q hCnn)
  have h3 : (1 - q) * (b.choose (b / 2 + 1) : ℝ) * (1 - x) < 1 - x := by
    simpa using mul_lt_mul_of_pos_right hstrictC (sub_pos.mpr hx1)
  have hlt : (1 - q) * S b x < 1 - x := lt_of_le_of_lt (h1.trans h2) h3
  unfold f
  linarith

/-- **Dense-variant root correction** (Corollary thm:threshold, eq:threshold-bound):
if the level-2 failure probability `P` satisfies `P ≤ 2q`, then the root application of
`f_N` gives `P_1 ≤ q + C(N, ⌈N/2⌉) (2q)^{⌈N/2⌉}`. -/
theorem root_bound (N : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {P : ℝ} (hP0 : 0 ≤ P) (hP : P ≤ 2 * q)
    (h2q : 2 * q ≤ 1) :
    f N q P ≤ q + (N.choose (half N) : ℝ) * (2 * q) ^ half N := by
  have := hq1
  have hP1 : P ≤ 1 := le_trans hP h2q
  have hk := aux_half_le N
  have hS := one_sub_binTail_le (b := N) (k := half N) hP0 hP1 hk
  have hf : f N q P = q + (1 - q) * (1 - S N P) := by
    unfold f
    exact (by ring : (1 : ℝ) - (1 - q) * S N P = q + (1 - q) * (1 - S N P))
  have h1S : 0 ≤ 1 - S N P := sub_nonneg.mpr (binTail_le_one hP0 hP1)
  have h1q1 : 1 - q ≤ 1 := by linarith
  have hprod : (1 - q) * (1 - S N P) ≤ 1 - S N P :=
    mul_le_of_le_one_left h1S h1q1
  have hPpow : P ^ half N ≤ (2 * q) ^ half N := pow_le_pow_left₀ hP0 hP _
  have hC : (0 : ℝ) ≤ N.choose (half N) := Nat.cast_nonneg _
  have hCx : (N.choose (half N) : ℝ) * P ^ half N ≤
      (N.choose (half N) : ℝ) * (2 * q) ^ half N :=
    mul_le_mul_of_nonneg_left hPpow hC
  calc
    f N q P = q + (1 - q) * (1 - S N P) := hf
    _ ≤ q + (1 - S N P) := by linarith
    _ ≤ q + (N.choose (half N) : ℝ) * P ^ half N := by
      have hS' : 1 - S N P = 1 - binTail N (half N) P := rfl
      rw [hS']
      linarith
    _ ≤ q + (N.choose (half N) : ℝ) * (2 * q) ^ half N := by linarith

end

end HSFN
