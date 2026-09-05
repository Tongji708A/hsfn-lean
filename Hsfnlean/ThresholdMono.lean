/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Threshold

/-!
# Monotone convergence of the level map (Theorem prop:threshold-b, item 1)

`S_b` is a binomial lower tail, hence nonincreasing in the failure probability `x`
on `[0,1]`; therefore `f_b` is nondecreasing, and the iterates from `q` form a
nondecreasing sequence bounded by `1`. The statements below are frozen; only the
proofs are to be supplied. (The convergence to the least fixed point follows from
monotone boundedness and continuity and is not restated here.)
-/

namespace HSFN

open Finset

noncomputable section

variable {b k : ℕ} {q : ℝ}

private theorem aux_hasDerivAt_binTerm (b i : ℕ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => (b.choose i : ℝ) * t ^ i * (1 - t) ^ (b - i))
      ((b.choose i : ℝ) *
        ((i : ℝ) * y ^ (i - 1) * (1 - y) ^ (b - i) -
          (↑(b - i) : ℝ) * y ^ i * (1 - y) ^ (b - i - 1))) y := by
  have hp := hasDerivAt_pow i y
  have hs : HasDerivAt (fun t : ℝ => (1 : ℝ) - t) (-1) y :=
    (hasDerivAt_id' y).const_sub (1 : ℝ)
  have hq := (hasDerivAt_pow (b - i) (1 - y)).comp y hs
  have hmul : HasDerivAt (fun t : ℝ => t ^ i * (1 - t) ^ (b - i))
      ((i : ℝ) * y ^ (i - 1) * (1 - y) ^ (b - i) +
        y ^ i * ((↑(b - i) : ℝ) * (1 - y) ^ (b - i - 1) * (-1))) y := by
    have heq : (fun t : ℝ => t ^ i * (1 - t) ^ (b - i)) =
        (fun x : ℝ => x ^ i) * ((fun x : ℝ => x ^ (b - i)) ∘ HSub.hSub (1 : ℝ)) := by
      ext t
      simp [Pi.mul_apply, Function.comp_apply]
    rw [heq]
    exact (hp.mul hq).congr_deriv (by simp [Function.comp_apply])
  have hC := hmul.const_mul (b.choose i : ℝ)
  have hfun :
      (fun t : ℝ => (b.choose i : ℝ) * t ^ i * (1 - t) ^ (b - i)) =
        fun t : ℝ => (b.choose i : ℝ) * (t ^ i * (1 - t) ^ (b - i)) := by
    ext t
    ring
  rw [hfun]
  refine hC.congr_deriv ?_
  ring

private theorem aux_choose_scale_left {b i : ℕ} (hi : 1 ≤ i) :
    (i : ℝ) * (b.choose i : ℝ) = (b : ℝ) * ((b - 1).choose (i - 1) : ℝ) := by
  cases' i with i
  · omega
  · cases b with
    | zero =>
      simp [Nat.choose_eq_zero_of_lt (Nat.succ_pos i)]
    | succ n =>
      have h := Nat.add_one_mul_choose_eq n i
      simp only [Nat.add_one_sub_one]
      exact_mod_cast (by
        rw [mul_comm]
        exact h.symm)

private theorem aux_choose_scale_right {b i : ℕ} :
    (↑(b - i) : ℝ) * (b.choose i : ℝ) = (b : ℝ) * ((b - 1).choose i : ℝ) := by
  cases b with
  | zero =>
    simp
  | succ n =>
    have h := Nat.choose_mul_succ_eq n i
    exact_mod_cast (by
      simpa [mul_comm] using h.symm)

private theorem aux_term_deriv_formula (b i : ℕ) (hi : 1 ≤ i) (y : ℝ) :
    (b.choose i : ℝ) *
        ((i : ℝ) * y ^ (i - 1) * (1 - y) ^ (b - i) -
          (↑(b - i) : ℝ) * y ^ i * (1 - y) ^ (b - i - 1)) =
      (b : ℝ) * ((b - 1).choose (i - 1) : ℝ) * y ^ (i - 1) * (1 - y) ^ (b - i) -
        (b : ℝ) * ((b - 1).choose i : ℝ) * y ^ i * (1 - y) ^ (b - i - 1) := by
  have hL := aux_choose_scale_left (b := b) (i := i) hi
  have hR := aux_choose_scale_right (b := b) (i := i)
  calc
    (b.choose i : ℝ) *
          ((i : ℝ) * y ^ (i - 1) * (1 - y) ^ (b - i) -
            (↑(b - i) : ℝ) * y ^ i * (1 - y) ^ (b - i - 1)) =
        ((i : ℝ) * (b.choose i : ℝ)) * y ^ (i - 1) * (1 - y) ^ (b - i) -
          ((↑(b - i) : ℝ) * (b.choose i : ℝ)) * y ^ i * (1 - y) ^ (b - i - 1) := by
      ring
    _ = (b : ℝ) * ((b - 1).choose (i - 1) : ℝ) * y ^ (i - 1) * (1 - y) ^ (b - i) -
          (b : ℝ) * ((b - 1).choose i : ℝ) * y ^ i * (1 - y) ^ (b - i - 1) := by
      rw [hL, hR]

private theorem aux_binTail_hasDerivAt (b k : ℕ) (hk : 1 ≤ k) (y : ℝ) :
    HasDerivAt (binTail b k)
      (-(b : ℝ) * ((b - 1).choose (k - 1) : ℝ) * y ^ (k - 1) * (1 - y) ^ (b - k)) y := by
  induction k, hk using Nat.le_induction with
  | base =>
    have heq : binTail b 1 = fun t : ℝ => (b.choose 0 : ℝ) * t ^ 0 * (1 - t) ^ (b - 0) := by
      funext t
      simp [binTail]
    have h := aux_hasDerivAt_binTerm b 0 y
    rw [heq]
    refine h.congr_deriv ?_
    simp [Nat.choose_zero_right, pow_zero]
  | succ k hk ih =>
    have heq : binTail b (k + 1) =
        binTail b k + fun t : ℝ => (b.choose k : ℝ) * t ^ k * (1 - t) ^ (b - k) := by
      funext t
      simp [binTail, Finset.sum_range_succ]
    have hterm := aux_hasDerivAt_binTerm b k y
    rw [heq]
    have hi : 1 ≤ k := hk
    have hform := aux_term_deriv_formula b k hi y
    refine (ih.add hterm).congr_deriv ?_
    rw [hform, Nat.sub_add_eq]
    simp [Nat.add_comm k]
    ring

/-- The lower binomial tail is nonincreasing in the success probability on `[0,1]`. -/
theorem binTail_antitoneOn (b k : ℕ) : AntitoneOn (binTail b k) (Set.Icc (0 : ℝ) 1) := by
  cases k with
  | zero =>
    intro x hx y hy hxy
    simp [binTail]
  | succ k =>
    have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hder := aux_binTail_hasDerivAt b (k + 1) hk
    have hdiff : Differentiable ℝ (binTail b (k + 1)) := fun y => (hder y).differentiableAt
    refine antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 1)
      hdiff.continuous.continuousOn hdiff.differentiableOn ?_
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
    rw [(hder x).deriv]
    have hx0 : 0 ≤ x := hxI.1
    have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hxI.2
    have hprod :
        (0 : ℝ) ≤ (b : ℝ) * ((b - 1).choose (k + 1 - 1) : ℝ) *
          x ^ (k + 1 - 1) * (1 - x) ^ (b - (k + 1)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (pow_nonneg hx0 _)) (pow_nonneg h1x _)
    have hneg :
        -↑b * ↑((b - 1).choose (k + 1 - 1)) * x ^ (k + 1 - 1) * (1 - x) ^ (b - (k + 1)) =
          -((b : ℝ) * ((b - 1).choose (k + 1 - 1) : ℝ) *
            x ^ (k + 1 - 1) * (1 - x) ^ (b - (k + 1))) := by
      ring
    rw [hneg]
    exact neg_nonpos.mpr hprod

/-- `f_b` is nondecreasing on `[0,1]` for `q ≤ 1`. -/
theorem f_monotoneOn (b : ℕ) (hq1 : q ≤ 1) : MonotoneOn (f b q) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hS := binTail_antitoneOn b (half b) hx hy hxy
  have h1q : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  unfold f S
  nlinarith

private theorem aux_iterate_mem_unit (b : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    (f b q)^[n] q ∈ Set.Icc (0 : ℝ) 1 := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id]
    exact ⟨hq0, hq1⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨le_trans hq0 (q_le_f hq1 ih.1 ih.2), f_le_one hq0 hq1 ih.1 ih.2⟩

/-- The iterates from `q` are nondecreasing: `f_b^{n}(q) ≤ f_b^{n+1}(q)`. -/
theorem iterate_mono (b : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    (f b q)^[n] q ≤ (f b q)^[n + 1] q := by
  induction n with
  | zero =>
    simpa using q_le_f (b := b) hq1 hq0 hq1
  | succ n ih =>
    have hx := aux_iterate_mem_unit (b := b) hq0 hq1 (n + 1)
    have hy := aux_iterate_mem_unit (b := b) hq0 hq1 (n + 2)
    have : (f b q)^[n + 2] q = f b q ((f b q)^[n + 1] q) := by
      rw [Function.iterate_succ_apply']
    have : (f b q)^[n + 1] q = f b q ((f b q)^[n] q) := by
      rw [Function.iterate_succ_apply']
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact f_monotoneOn (b := b) hq1
      (aux_iterate_mem_unit (b := b) hq0 hq1 n)
      (aux_iterate_mem_unit (b := b) hq0 hq1 (n + 1)) ih

/-- The iterates stay in `[0,1]`. -/
theorem iterate_mem_unit (b : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    (f b q)^[n] q ∈ Set.Icc (0 : ℝ) 1 :=
  aux_iterate_mem_unit b hq0 hq1 n

end

end HSFN
