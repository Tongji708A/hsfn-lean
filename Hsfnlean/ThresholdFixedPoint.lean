/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.ThresholdMono

/-!
# The least fixed point and the threshold `q_c` (Theorem prop:threshold-b, items 1 and 3)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
The iterates `f_b^n(q)` are nondecreasing and bounded, hence converge to `x*(q)`, the
least fixed point of `f_b` in `[q, 1]`. `x*` is nondecreasing in `q`, at most `2q` below
`q_0`, and equal to `1` above the survivor-side bound. The threshold is
`q_c = sup {q ∈ [0,1] : x*(q) < 1}`, with `q_0 ≤ q_c ≤ 1 - C(b, ⌊b/2⌋+1)^{-1}`, and
`x*(q) < 1` for `q < q_c` while `x*(q) = 1` for `q > q_c`.
The statements below are frozen; only the proofs are to be supplied.
-/

namespace HSFN

open Filter Topology Set

noncomputable section

variable {b : ℕ} {q q' : ℝ}

/-- The least fixed point `x*(q)`, as the supremum of the iterates from `q`. -/
def xstar (b : ℕ) (q : ℝ) : ℝ := ⨆ n : ℕ, (f b q)^[n] q

private theorem aux_monotone_iterate (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Monotone (fun n : ℕ => (f b q)^[n] q) :=
  monotone_nat_of_le_succ fun n => iterate_mono b hq0 hq1 n

private theorem aux_bddAbove_iterate (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    BddAbove (range fun n : ℕ => (f b q)^[n] q) :=
  ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact (iterate_mem_unit b hq0 hq1 n).2⟩

/-- The iterates converge to `x*(q)` (item 1, monotone convergence). -/
theorem tendsto_iterate (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Tendsto (fun n : ℕ => (f b q)^[n] q) atTop (𝓝 (xstar b q)) :=
  tendsto_atTop_ciSup (aux_monotone_iterate hq0 hq1) (aux_bddAbove_iterate hq0 hq1)

theorem iterate_le_xstar (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) : (f b q)^[n] q ≤ xstar b q :=
  le_ciSup (aux_bddAbove_iterate hq0 hq1) n

theorem xstar_mem_Icc (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : xstar b q ∈ Set.Icc q 1 := by
  refine ⟨?_, ciSup_le fun n => (iterate_mem_unit b hq0 hq1 n).2⟩
  have : q = (f b q)^[0] q := by simp
  rw [this]
  exact iterate_le_xstar hq0 hq1 0

private theorem aux_continuous_f (b : ℕ) (q : ℝ) : Continuous (f b q) := by
  unfold f S binTail
  fun_prop

/-- `x*(q)` is a fixed point of `f_b`. -/
theorem f_xstar (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : f b q (xstar b q) = xstar b q := by
  have hlim := tendsto_iterate (b := b) hq0 hq1
  have hcomp : Tendsto (fun n : ℕ => f b q ((f b q)^[n] q)) atTop (𝓝 (f b q (xstar b q))) :=
    ((aux_continuous_f b q).tendsto (xstar b q)).comp hlim
  have heq : Tendsto (fun n : ℕ => (f b q)^[n + 1] q) atTop (𝓝 (f b q (xstar b q))) :=
    hcomp.congr fun n => (Function.iterate_succ_apply' (f b q) n q).symm
  have hshift : Tendsto (fun n : ℕ => (f b q)^[n + 1] q) atTop (𝓝 (xstar b q)) :=
    (tendsto_add_atTop_iff_nat 1).mpr hlim
  exact tendsto_nhds_unique heq hshift

/-- `x*(q)` is the least fixed point in `[q, 1]`. -/
theorem xstar_le_of_fixed (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {y : ℝ} (hy : y ∈ Set.Icc q 1)
    (hfy : f b q y = y) : xstar b q ≤ y := by
  have hy01 : y ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hq0 hy.1, hy.2⟩
  have hle : ∀ n, (f b q)^[n] q ≤ y := by
    intro n
    induction n with
    | zero =>
      simpa using hy.1
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (f_monotoneOn b hq1 (iterate_mem_unit b hq0 hq1 n) hy01 ih).trans_eq hfy
  exact ciSup_le hle

/-- Below `q_0` the least fixed point is at most `2q` (item 2). -/
theorem xstar_le_two_mul (hb : 3 ≤ b) (hq0 : 0 < q) (h : BelowQ0 b q) : xstar b q ≤ 2 * q :=
  ciSup_le fun n => iterate_le_two_mul hb hq0 h n

private theorem aux_f_le_f_of_le_q (b : ℕ) {q q' x : ℝ} (hqq : q ≤ q')
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : f b q x ≤ f b q' x := by
  have hS := binTail_nonneg (b := b) (k := half b) hx0 hx1
  unfold f S
  nlinarith

/-- `x*` is nondecreasing in `q` (item 3). -/
theorem xstar_mono (hq0 : 0 ≤ q) (hqq : q ≤ q') (hq1 : q' ≤ 1) : xstar b q ≤ xstar b q' := by
  have hq1q : q ≤ 1 := hqq.trans hq1
  have hq0' : 0 ≤ q' := hq0.trans hqq
  have hiter : ∀ n, (f b q)^[n] q ≤ (f b q')^[n] q' := by
    intro n
    induction n with
    | zero =>
      simpa using hqq
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hx := iterate_mem_unit b hq0 hq1q n
      have hy := iterate_mem_unit b hq0' hq1 n
      exact (aux_f_le_f_of_le_q b hqq hx.1 hx.2).trans (f_monotoneOn b hq1 hx hy ih)
  exact ciSup_le fun n => (hiter n).trans (le_ciSup (aux_bddAbove_iterate hq0' hq1) n)

/-- Above the survivor-side bound the only fixed point is `1` (item 3, upper bracket). -/
theorem xstar_eq_one_of_large (hb : 1 ≤ b) (hq : 1 - 1 / (b.choose (b / 2 + 1) : ℝ) < q)
    (hq1 : q ≤ 1) : xstar b q = 1 := by
  have hjb : b / 2 + 1 ≤ b := by
    have : 1 ≤ half b := by
      unfold half
      omega
    omega
  have hCpos : (0 : ℝ) < (b.choose (b / 2 + 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hjb)
  have hCge : (1 : ℝ) ≤ (b.choose (b / 2 + 1) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos hjb)
  have hdiv : (1 : ℝ) / (b.choose (b / 2 + 1) : ℝ) ≤ 1 :=
    (div_le_one hCpos).mpr hCge
  have hq0 : 0 ≤ q := by linarith
  have hx := xstar_mem_Icc (b := b) hq0 hq1
  have hfix := f_xstar (b := b) hq0 hq1
  apply le_antisymm hx.2
  by_contra hne
  have hlt : xstar b q < 1 := lt_of_le_of_ne hx.2 (by linarith)
  have hstrict :=
    lt_f_of_large_q (b := b) (x := xstar b q) hb hq hq1 (le_trans hq0 hx.1) hlt
  rw [hfix] at hstrict
  exact lt_irrefl _ hstrict

/-- The threshold `q_c(N,b) = sup {q ∈ [0,1] : x*(q) < 1}`. -/
def qc (b : ℕ) : ℝ := sSup {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ xstar b q < 1}

private theorem aux_qcSet_bddAbove (b : ℕ) :
    BddAbove {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ xstar b q < 1} :=
  ⟨1, fun _ hx => hx.2.1⟩

private theorem aux_S_zero (hb : 1 ≤ b) : S b 0 = 1 := by
  unfold S binTail
  have hmem : (0 : ℕ) ∈ Finset.range (half b) := by
    simp [half]
    omega
  rw [Finset.sum_eq_single 0]
  · simp [pow_zero]
  · intro i _hi hne
    simp [zero_pow hne]
  · intro hnot
    exact (hnot hmem).elim

private theorem aux_iterate_zero (hb : 1 ≤ b) (n : ℕ) : (f b 0)^[n] (0 : ℝ) = 0 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold f
    rw [aux_S_zero hb]
    ring

private theorem aux_xstar_zero (hb : 1 ≤ b) : xstar b 0 = 0 := by
  have h : (fun n : ℕ => (f b 0)^[n] (0 : ℝ)) = fun _ => 0 :=
    funext (aux_iterate_zero hb)
  simp only [xstar, h, ciSup_const]

private theorem aux_zero_mem_qcSet (hb : 1 ≤ b) :
    (0 : ℝ) ∈ {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ xstar b q < 1} := by
  refine ⟨le_rfl, zero_le_one, ?_⟩
  rw [aux_xstar_zero hb]
  exact zero_lt_one

private theorem aux_qc_nonneg (b : ℕ) : 0 ≤ qc b := by
  by_cases hne : ({q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ xstar b q < 1}).Nonempty
  · obtain ⟨r, hr⟩ := hne
    exact le_trans hr.1 (le_csSup (aux_qcSet_bddAbove b) hr)
  · have hempty : {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ xstar b q < 1} = ∅ :=
      not_nonempty_iff_eq_empty.mp hne
    simp only [qc, hempty, Real.sSup_empty, le_rfl]

/-- Lower bracket `q_0 ≤ q_c` (`b ≥ 3`). -/
theorem q0_le_qc (hb : 3 ≤ b) : q0 b ≤ qc b := by
  have hb1 : 1 ≤ b := by omega
  have hbdd := aux_qcSet_bddAbove b
  have hqc0 : 0 ≤ qc b := le_csSup hbdd (aux_zero_mem_qcSet hb1)
  have hq0pos : 0 < q0 b := by
    unfold q0
    refine Real.rpow_pos_of_pos ?_ _
    refine mul_pos (pow_pos (by norm_num) _) ?_
    exact Nat.cast_pos.mpr (Nat.choose_pos (by unfold half; omega))
  by_contra hne
  have hlt : qc b < q0 b := not_le.mp hne
  obtain ⟨r, hrl, hrr⟩ := exists_between hlt
  have hrpos : 0 < r := lt_of_le_of_lt hqc0 hrl
  have hBelow : BelowQ0 b r := (lt_q0_iff (q := r) hb hrpos).mp hrr
  have h2q := two_mul_lt_one_of_belowQ0 (q := r) hb hrpos hBelow
  have hr1 : r ≤ 1 := by nlinarith
  have hx : xstar b r ≤ 2 * r := xstar_le_two_mul (q := r) hb hrpos hBelow
  have hx1 : xstar b r < 1 := lt_of_le_of_lt hx h2q
  have hmem : r ∈ {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ xstar b q < 1} :=
    ⟨le_of_lt hrpos, hr1, hx1⟩
  have : r ≤ qc b := le_csSup hbdd hmem
  exact this.not_gt hrl

/-- Upper bracket `q_c ≤ 1 - C(b, ⌊b/2⌋+1)^{-1}` (`b ≥ 1`). -/
theorem qc_le (hb : 1 ≤ b) : qc b ≤ 1 - 1 / (b.choose (b / 2 + 1) : ℝ) := by
  refine csSup_le ⟨0, aux_zero_mem_qcSet hb⟩ ?_
  intro r hr
  by_contra hgt
  have hlarge : 1 - 1 / (b.choose (b / 2 + 1) : ℝ) < r := not_le.mp hgt
  have := xstar_eq_one_of_large (q := r) hb hlarge hr.2.1
  exact hr.2.2.ne this

/-- Below the threshold the root survives with positive probability: `x*(q) < 1`. -/
theorem xstar_lt_one_of_lt_qc (hq0 : 0 ≤ q) (hq : q < qc b) : xstar b q < 1 := by
  set s := {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ xstar b r < 1}
  have hsne : s.Nonempty := by
    by_contra hempty
    have : s = ∅ := not_nonempty_iff_eq_empty.mp hempty
    have hqc : qc b = 0 := by
      change sSup s = 0
      rw [this, Real.sSup_empty]
    linarith
  obtain ⟨r, hr, hqr⟩ := exists_lt_of_lt_csSup (s := s) hsne hq
  exact (xstar_mono hq0 (le_of_lt hqr) hr.2.1).trans_lt hr.2.2

/-- Above the threshold the root failure probability is `1`. -/
theorem xstar_eq_one_of_qc_lt (hq : qc b < q) (hq1 : q ≤ 1) : xstar b q = 1 := by
  have hq0 : 0 ≤ q := le_trans (aux_qc_nonneg b) (le_of_lt hq)
  have hx1 : xstar b q ≤ 1 := (xstar_mem_Icc hq0 hq1).2
  refine le_antisymm hx1 ?_
  by_contra hne
  have hlt : xstar b q < 1 := not_le.mp hne
  have hmem : q ∈ {r : ℝ | 0 ≤ r ∧ r ≤ 1 ∧ xstar b r < 1} := ⟨hq0, hq1, hlt⟩
  have : q ≤ qc b := le_csSup (aux_qcSet_bddAbove b) hmem
  exact this.not_gt hq


end

end HSFN
