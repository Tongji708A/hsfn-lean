/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Threshold
import Hsfnlean.ThresholdMono
import Hsfnlean.SecurityRec

/-!
# Failure recursion on the physical graph (Proposition prop:phys-recursion)

Paper: "The Hyper-Simplex Fractal Network as Space, Protocol and Dynamical System" (R260409).

Cell size `N = n + 1`, PBFT tolerance `f = ⌊(N-1)/3⌋ = n / 3`, and `r = ⌈N/2⌉ - 1`, the
largest number of lost children a cell absorbs, so that `r + 1 = half N`. With per-node fault
probability `p`, the physical level map is

`g_N(x) = 1 - ∑_{j ≤ min(f, r)} C(N,j) p^j (1-p)^(N-j) · P[Bin(N-j, x) ≤ r - j]`,

where `P[Bin(N-j, x) ≤ r - j] = binTail (N-j) (half N - j) x`. The overlay map of
Theorem thm:security is `f_N(x) = 1 - (1-q) S_N(x)` with `q = leafQ n p`.

Mechanized here, as real algebra with no probability theory:
* `binTail_le_succ`, `binTail_shift` — the binomial-tail inequality behind the coupling
  `Bin(N, x) ≤ Bin(N-j, x) + j`: `P[Bin(N-j,x) ≤ r-j] ≤ P[Bin(N,x) ≤ r]`;
* `f_le_g` — `g_N ≥ f_N` on `[0,1]` (the comparison claimed by the proposition);
* `g_mem_unit`, `g_monotoneOn` — `g_N` maps `[0,1]` into itself and is nondecreasing;
* `iterate_f_le_iterate_g` — the comparison propagates to every depth:
  `f_N^[k] q ≤ g_N^[k] q`, i.e. `P_1^phys ≥ P_1^II` at every depth.
The exactness of `g_N` as the failure probability of the executed protocol is the paper's
probabilistic argument and is not mechanized. The statements are frozen; only the proofs are
to be supplied.
-/

namespace HSFN
namespace PhysRecursion

open Finset

/-- Weight of exactly `j` faulty members among `N` when each fails with probability `p`. -/
def w (N : ℕ) (p : ℝ) (j : ℕ) : ℝ := (N.choose j : ℝ) * p ^ j * (1 - p) ^ (N - j)

/-- The physical level map `g_N` for `N = n + 1`. -/
def g (n : ℕ) (p x : ℝ) : ℝ :=
  1 - ∑ j ∈ range (min (n / 3) (half (n + 1) - 1) + 1),
        w (n + 1) p j * binTail (n + 1 - j) (half (n + 1) - j) x

/-- Pascal's rule for one binomial term:
`T_{b+1}(i+1) = x T_b(i) + (1-x) T_b(i+1)`. -/
theorem aux_term_pascal (b i : ℕ) (x : ℝ) :
    ((b + 1).choose (i + 1) : ℝ) * x ^ (i + 1) * (1 - x) ^ (b + 1 - (i + 1)) =
      x * ((b.choose i : ℝ) * x ^ i * (1 - x) ^ (b - i)) +
        (1 - x) * ((b.choose (i + 1) : ℝ) * x ^ (i + 1) * (1 - x) ^ (b - (i + 1))) := by
  have hc : ((b + 1).choose (i + 1) : ℝ) = (b.choose i : ℝ) + (b.choose (i + 1) : ℝ) := by
    exact_mod_cast Nat.choose_succ_succ b i
  have he : b + 1 - (i + 1) = b - i := by omega
  rw [hc, he]
  rcases Nat.lt_or_ge b (i + 1) with hlt | hge
  · rw [Nat.choose_eq_zero_of_lt hlt]
    push_cast
    ring
  · have he2 : b - i = (b - (i + 1)) + 1 := by omega
    rw [he2]
    ring

/-- Pascal's rule for the tail:
`binTail (b+1) (k+1) x = x * binTail b k x + (1-x) * binTail b (k+1) x`. -/
theorem aux_binTail_pascal (b k : ℕ) (x : ℝ) :
    binTail (b + 1) (k + 1) x = x * binTail b k x + (1 - x) * binTail b (k + 1) x := by
  unfold binTail
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (n := k)
    (fun i => (b.choose i : ℝ) * x ^ i * (1 - x) ^ (b - i))]
  simp_rw [aux_term_pascal b _ x]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
  rw [pow_succ]
  ring

/-- One Pascal step of the lower binomial tail: `P[Bin(b,x) ≤ k-1] ≤ P[Bin(b+1,x) ≤ k]`. -/
theorem binTail_le_succ (b k : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    binTail b k x ≤ binTail (b + 1) (k + 1) x := by
  rw [aux_binTail_pascal]
  have hstep : binTail b k x ≤ binTail b (k + 1) x := by
    unfold binTail
    rw [Finset.sum_range_succ]
    have : 0 ≤ (b.choose k : ℝ) * x ^ k * (1 - x) ^ (b - k) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx0 _))
        (pow_nonneg (sub_nonneg.mpr hx1) _)
    linarith
  have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  nlinarith [mul_le_mul_of_nonneg_left hstep h1x]

/-- The shifted tail: `P[Bin(b-j,x) ≤ k-j-1] ≤ P[Bin(b,x) ≤ k-1]` for `j ≤ b` and `j ≤ k`. -/
theorem binTail_shift {b k j : ℕ} (hjb : j ≤ b) (hjk : j ≤ k) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    binTail (b - j) (k - j) x ≤ binTail b k x := by
  induction j generalizing b k with
  | zero => simp
  | succ j ih =>
    have h1 := binTail_le_succ (b - (j + 1)) (k - (j + 1)) hx0 hx1
    have hb : b - (j + 1) + 1 = b - j := by omega
    have hk : k - (j + 1) + 1 = k - j := by omega
    rw [hb, hk] at h1
    exact h1.trans (ih (by omega) (by omega))

/-- The binomial weights are nonnegative on `[0,1]`. -/
theorem aux_w_nonneg (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : ℕ) :
    0 ≤ w (n + 1) p j :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

/-- The comparison of Proposition prop:phys-recursion: `f_N ≤ g_N` on `[0,1]`. -/
theorem f_le_g (n : ℕ) {p x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    f (n + 1) (leafQ n p) x ≤ g n p x := by
  set M := min (n / 3) (half (n + 1) - 1) with hM
  have hw : ∀ j, 0 ≤ w (n + 1) p j := fun j => aux_w_nonneg n hp0 hp1 j
  have hS0 : 0 ≤ S (n + 1) x := binTail_nonneg hx0 hx1
  have hq : 1 - leafQ n p = ∑ j ∈ range (n / 3 + 1), w (n + 1) p j := by
    simp only [leafQ, binTail, w]
    ring
  have hterm : ∀ j ∈ range (M + 1),
      w (n + 1) p j * binTail (n + 1 - j) (half (n + 1) - j) x ≤
        w (n + 1) p j * S (n + 1) x := by
    intro j hj
    have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjh : j ≤ half (n + 1) - 1 := hjM.trans (min_le_right _ _)
    have hh : half (n + 1) ≤ n + 1 := by unfold half; omega
    refine mul_le_mul_of_nonneg_left ?_ (hw j)
    exact binTail_shift (by omega) (by omega) hx0 hx1
  have hsub : range (M + 1) ⊆ range (n / 3 + 1) :=
    Finset.range_subset_range.mpr (Nat.succ_le_succ (min_le_left _ _))
  have h2 : ∑ j ∈ range (M + 1), w (n + 1) p j * S (n + 1) x ≤
      ∑ j ∈ range (n / 3 + 1), w (n + 1) p j * S (n + 1) x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => mul_nonneg (hw j) hS0
  have h1 := Finset.sum_le_sum hterm
  unfold f g
  rw [hq, Finset.sum_mul]
  linarith

/-- `g_N` maps `[0,1]` into itself. -/
theorem g_mem_unit (n : ℕ) {p x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ g n p x ∧ g n p x ≤ 1 := by
  set M := min (n / 3) (half (n + 1) - 1) with hM
  have hw : ∀ j, 0 ≤ w (n + 1) p j := fun j => aux_w_nonneg n hp0 hp1 j
  have hlo : 0 ≤ ∑ j ∈ range (M + 1),
      w (n + 1) p j * binTail (n + 1 - j) (half (n + 1) - j) x :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (binTail_nonneg hx0 hx1)
  have hhi : ∑ j ∈ range (M + 1),
      w (n + 1) p j * binTail (n + 1 - j) (half (n + 1) - j) x ≤
        ∑ j ∈ range (M + 1), w (n + 1) p j :=
    Finset.sum_le_sum fun j _ =>
      mul_le_of_le_one_right (hw j) (binTail_le_one hx0 hx1)
  have hsum : ∑ j ∈ range (M + 1), w (n + 1) p j = binTail (n + 1) (M + 1) p := by
    simp only [binTail, w]
  have hle : binTail (n + 1) (M + 1) p ≤ 1 := binTail_le_one hp0 hp1
  unfold g
  constructor <;> linarith

/-- `g_N` is nondecreasing on `[0,1]`. -/
theorem g_monotoneOn (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    MonotoneOn (g n p) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  unfold g
  have : ∑ j ∈ range (min (n / 3) (half (n + 1) - 1) + 1),
        w (n + 1) p j * binTail (n + 1 - j) (half (n + 1) - j) y ≤
      ∑ j ∈ range (min (n / 3) (half (n + 1) - 1) + 1),
        w (n + 1) p j * binTail (n + 1 - j) (half (n + 1) - j) x :=
    Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (binTail_antitoneOn _ _ hx hy hxy) (aux_w_nonneg n hp0 hp1 j)
  linarith

/-- The iterates of `g_N` from the leaf value stay in `[0,1]`. -/
theorem aux_iterate_g_mem_unit (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    (g n p)^[k] (leafQ n p) ∈ Set.Icc (0 : ℝ) 1 := by
  induction k with
  | zero => simpa using leafQ_mem_unit n hp0 hp1
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact g_mem_unit n hp0 hp1 ih.1 ih.2

/-- Every depth: the physical iterate dominates the overlay iterate from the same leaf value
`q`, i.e. `P_1^phys = g_N^{m-1}(q) ≥ f_N^{m-1}(q) = P_1^II`. -/
theorem iterate_f_le_iterate_g (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    (f (n + 1) (leafQ n p))^[k] (leafQ n p) ≤ (g n p)^[k] (leafQ n p) := by
  have hq := leafQ_mem_unit n hp0 hp1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hfk := iterate_mem_unit (n + 1) hq.1 hq.2 k
    have hgk := aux_iterate_g_mem_unit n hp0 hp1 k
    exact (f_monotoneOn (n + 1) hq.2 hfk hgk ih).trans (f_le_g n hp0 hp1 hgk.1 hgk.2)

end PhysRecursion
end HSFN
