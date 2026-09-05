/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Mathlib
import Hsfnlean.Basic
import Hsfnlean.Dense

/-!
# Confirmation delay is logarithmic in the population (Proposition thm:delay)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409),
Section `subsec:delay`, Proposition `thm:delay` and equation `eq:delay`.

The paper states the confirmation delay of a depth-`m` network on `V` nodes as
`D = m · t_ave = (log₂ V / log₂ λ + O(1)) · t_ave`, with `λ = N` the branching of
the HSFN cell tree and `λ = 2N-2` that of the dense variant, "the `O(1)` term being
bounded uniformly in `m`".

Nothing here is asymptotic: the `O(1)` is replaced everywhere by explicit numerical
constants, valid for every admissible `m` simultaneously (which is exactly what
"uniform in `m`" abbreviates).

* `HSFN.Delay.card_pow_bounds` / `card_pow_bounds_real` — the population sandwich
  `N^m ≤ V ≤ 2 N^m` behind `V = N(N^m - 1)/(N-1) ∼ N/(N-1) · N^m`
  (Corollary `cor:count-II`, via `HSFN.Addr.card_closed`).
* `HSFN.Delay.depth_eq_logb` — the resulting two-sided pin of the depth,
  `m ≤ log_N V ≤ m + 1`, i.e. `log_N V - 1 ≤ m ≤ log_N V`.
* `HSFN.Delay.delay_eq_logb` — `eq:delay` itself, in the form
  `D = m · t_ave` with `m · t_ave ≤ (log_N V) · t_ave ≤ m · t_ave + t_ave`.
* `HSFN.Delay.dense_pow_bounds` / `dense_depth_eq_logb` — the dense counterpart
  with base `λ = 2N-2` (Theorem `thm:node-count`, via `HSFN.Dense.V_bounds`):
  `λ^(m-1) ≤ V ≤ λ^(m+2)`, hence `m - 1 ≤ log_λ V ≤ m + 2`.
* `HSFN.Delay.dense_delay_eq_logb` — the same rescaled by `t_ave`, with the two
  explicit constants of the dense case.
* `HSFN.Delay.depth_le_of_card_le` / `delay_le_of_card_le` — the design corollary of
  the closing paragraph of `subsec:delay`: to meet a target depth bound `D` (a target
  delay `D · t_ave`) it suffices that `V ≤ N^D`.

Subtraction-free forms are used in the statements wherever the paper divides or
subtracts, following the convention of `Hsfnlean/Basic.lean`.

Not modelled here: the paper's standing hypothesis that consecutive layers overlap,
and the layer time `t_ave` itself.  These are protocol-level timing assumptions with
no combinatorial content; `t_ave` enters only as an arbitrary nonnegative real scale,
and `delay m tave = m * tave` is the paper's `D = m · t_ave` *given* that hypothesis.
The mathematical content of `eq:delay` carried by this file is the depth-versus-log
sandwich, which the delay statements merely rescale by `t_ave`.
-/

set_option linter.unusedVariables false

namespace HSFN.Delay

/-! ## The HSFN population sandwich (Corollary cor:count-II) -/

/-- **Population sandwich, HSFN** (Corollary `cor:count-II`).  The closed count
`(N-1)·V + N = N^(m+1)` of `HSFN.Addr.card_closed`, i.e. `V = N(N^m - 1)/(N - 1)`,
pins the population between `N^m` and `2 N^m` for every `N ≥ 2` and `m ≥ 1`.
This is the quantitative content of the paper's `V ∼ N/(N-1) · N^m`. -/
theorem card_pow_bounds (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) :
    N ^ m ≤ Fintype.card (Addr N m) ∧ Fintype.card (Addr N m) ≤ 2 * N ^ m := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  have key : (n + 1) * Fintype.card (Addr (n + 2) m) + (n + 2) = (n + 2) ^ (m + 1) :=
    Addr.card_closed (n + 1) m
  have hpow : n + 2 ≤ (n + 2) ^ m := by
    calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
      _ ≤ (n + 2) ^ m := Nat.pow_le_pow_right (by omega) hm
  rw [pow_succ] at key
  constructor
  · have hstep : (n + 1) * (n + 2) ^ m + (n + 2)
        ≤ (n + 1) * Fintype.card (Addr (n + 2) m) + (n + 2) := by
      rw [key]; nlinarith [hpow]
    exact Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_right hstep) (by omega)
  · have hstep : (n + 1) * Fintype.card (Addr (n + 2) m) + (n + 2)
        ≤ (n + 1) * (2 * (n + 2) ^ m) + (n + 2) := by
      rw [key]; nlinarith [hpow]
    exact Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_right hstep) (by omega)

/-- **Population sandwich, HSFN, over `ℝ`**: `N^m ≤ V ≤ 2 N^m` (Corollary `cor:count-II`). -/
theorem card_pow_bounds_real (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) :
    (N : ℝ) ^ m ≤ (Fintype.card (Addr N m) : ℝ) ∧
      (Fintype.card (Addr N m) : ℝ) ≤ 2 * (N : ℝ) ^ m := by
  obtain ⟨h1, h2⟩ := card_pow_bounds N m hN hm
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-! ## The depth is the logarithm of the population (Proposition thm:delay) -/

/-- **Depth is the logarithm, HSFN** (Proposition `thm:delay`).  Taking `log_N` of
`card_pow_bounds_real` pins the depth of a depth-`m`, `V`-node HSFN to
`m ≤ log_N V ≤ m + 1`; equivalently `log_N V - 1 ≤ m ≤ log_N V`.  The additive
constant `1` is the explicit form of the paper's `O(1)`, and it does not depend
on `m`. -/
theorem depth_eq_logb (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) :
    (m : ℝ) ≤ Real.logb N (Fintype.card (Addr N m)) ∧
      Real.logb N (Fintype.card (Addr N m)) ≤ (m : ℝ) + 1 := by
  obtain ⟨h1, h2⟩ := card_pow_bounds_real N m hN hm
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) < (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hpowpos : (0 : ℝ) < (N : ℝ) ^ m := pow_pos hNpos m
  have hcardpos : (0 : ℝ) < (Fintype.card (Addr N m) : ℝ) := lt_of_lt_of_le hpowpos h1
  constructor
  · have hstep := Real.logb_le_logb_of_le hN1 hpowpos h1
    rwa [Real.logb_pow, Real.logb_self_eq_one hN1, mul_one] at hstep
  · have hstep := Real.logb_le_logb_of_le hN1 hcardpos h2
    rw [Real.logb_mul (two_ne_zero) (ne_of_gt hpowpos), Real.logb_pow,
      Real.logb_self_eq_one hN1, mul_one] at hstep
    have hlog2 : Real.logb (N : ℝ) 2 ≤ 1 := by
      have h := Real.logb_le_logb_of_le hN1 (by norm_num : (0 : ℝ) < 2) hNR
      rwa [Real.logb_self_eq_one hN1] at h
    linarith

/-- The confirmation delay of a depth-`m` network whose layers overlap: one layer
per tier on the critical path, at `t_ave` per layer (Proposition `thm:delay`). -/
def delay (m : ℕ) (tave : ℝ) : ℝ := m * tave

/-- **Equation `eq:delay`**, with the `O(1)` made explicit.  For `N ≥ 2`, `m ≥ 1`
and any nonnegative layer time `t_ave`, the delay `D = m · t_ave` differs from
`(log_N V) · t_ave` by at most one `t_ave`, uniformly in `m`. -/
theorem delay_eq_logb (N m : ℕ) (tave : ℝ) (hN : 2 ≤ N) (hm : 1 ≤ m) (ht : 0 ≤ tave) :
    delay m tave ≤ Real.logb N (Fintype.card (Addr N m)) * tave ∧
      Real.logb N (Fintype.card (Addr N m)) * tave ≤ delay m tave + tave := by
  obtain ⟨h1, h2⟩ := depth_eq_logb N m hN hm
  have k1 := mul_le_mul_of_nonneg_right h1 ht
  have k2 := mul_le_mul_of_nonneg_right h2 ht
  simp only [delay]
  constructor
  · linarith
  · nlinarith [k2]

/-! ## The dense variant, base `λ = 2N-2` (Theorem thm:node-count) -/

/-- **Population sandwich, dense variant** (Theorem `thm:node-count`).  From
`HSFN.Dense.V_bounds`, `N^2 λ^(m-2) ≤ V ≤ N + N^2 λ^(m-1)` with `λ = 2N-2`, the
population of the dense variant lies between `λ^(m-1)` and `λ^(m+2)` for `N ≥ 3`
and `m ≥ 2`.  This is the quantitative content of `V ∼ N²/(2N-3) · (2N-2)^(m-1)`.
The exponent offsets `1` and `2` are explicit constants independent of `m`, which is
all `eq:delay` asserts; no optimality of either constant is claimed. -/
theorem dense_pow_bounds (N m : ℕ) (hN : 3 ≤ N) (hm : 2 ≤ m) :
    (2 * N - 2) ^ (m - 1) ≤ Dense.V N m ∧ Dense.V N m ≤ (2 * N - 2) ^ (m + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  have hb := Dense.V_bounds (k + 3) (j + 2) (by omega) (by omega)
  have e1 : 2 * (k + 3) - 2 = 2 * k + 4 := by omega
  have e2 : j + 2 - 1 = j + 1 := by omega
  have e3 : j + 2 - 2 = j := by omega
  have e4 : j + 2 + 2 = j + 1 + 3 := by omega
  rw [e1, e3, e2] at hb
  rw [e1, e2, e4]
  obtain ⟨hlo, hhi⟩ := hb
  constructor
  · calc (2 * k + 4) ^ (j + 1) = (2 * k + 4) ^ j * (2 * k + 4) := pow_succ _ _
      _ ≤ (2 * k + 4) ^ j * (k + 3) ^ 2 := Nat.mul_le_mul le_rfl (by nlinarith)
      _ = (k + 3) ^ 2 * (2 * k + 4) ^ j := Nat.mul_comm _ _
      _ ≤ Dense.V (k + 3) (j + 2) := hlo
  · have hP : 2 * k + 4 ≤ (2 * k + 4) ^ (j + 1) := by
      calc 2 * k + 4 = (2 * k + 4) ^ 1 := (pow_one _).symm
        _ ≤ (2 * k + 4) ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    calc Dense.V (k + 3) (j + 2) ≤ (k + 3) + (k + 3) ^ 2 * (2 * k + 4) ^ (j + 1) := hhi
      _ ≤ (2 * k + 4) ^ (j + 1) + (k + 3) ^ 2 * (2 * k + 4) ^ (j + 1) :=
          Nat.add_le_add_right (le_trans (by omega) hP) _
      _ = ((k + 3) ^ 2 + 1) * (2 * k + 4) ^ (j + 1) := by ring
      _ ≤ (2 * k + 4) ^ 3 * (2 * k + 4) ^ (j + 1) := Nat.mul_le_mul (by
            have e : (2 * k + 4) ^ 3
                = (k + 3) ^ 2 + 1 + (8 * k ^ 3 + 47 * k ^ 2 + 90 * k + 54) := by ring
            rw [e]; exact Nat.le_add_right _ _) le_rfl
      _ = (2 * k + 4) ^ (j + 1 + 3) := by rw [← pow_add]; ring_nf

/-- **Depth is the logarithm, dense variant** (Proposition `thm:delay`, `λ = 2N-2`).
For `N ≥ 3` and `m ≥ 2` the depth of the dense variant satisfies
`m - 1 ≤ log_λ V ≤ m + 2` with `λ = 2N - 2`; the two constants `1` and `2` are
independent of `m`.  Stated subtraction-free on the left. -/
theorem dense_depth_eq_logb (N m : ℕ) (hN : 3 ≤ N) (hm : 2 ≤ m) :
    (m : ℝ) ≤ Real.logb (2 * (N : ℝ) - 2) (Dense.V N m) + 1 ∧
      Real.logb (2 * (N : ℝ) - 2) (Dense.V N m) ≤ (m : ℝ) + 2 := by
  obtain ⟨h1, h2⟩ := dense_pow_bounds N m hN hm
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcast : ((2 * N - 2 : ℕ) : ℝ) = 2 * (N : ℝ) - 2 := by
    have hle : (2 : ℕ) ≤ 2 * N := by omega
    rw [Nat.cast_sub hle]; push_cast; ring
  have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have hle : (1 : ℕ) ≤ m := by omega
    rw [Nat.cast_sub hle]; push_cast; ring
  set b : ℝ := 2 * (N : ℝ) - 2 with hbdef
  have hb1 : (1 : ℝ) < b := by rw [hbdef]; linarith
  have hbpos : (0 : ℝ) < b := by linarith
  have h1R : b ^ (m - 1) ≤ (Dense.V N m : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr h1
    rwa [Nat.cast_pow, hcast] at h
  have h2R : (Dense.V N m : ℝ) ≤ b ^ (m + 2) := by
    have h := (Nat.cast_le (α := ℝ)).mpr h2
    rwa [Nat.cast_pow, hcast] at h
  have hVpos : (0 : ℝ) < (Dense.V N m : ℝ) := lt_of_lt_of_le (pow_pos hbpos _) h1R
  constructor
  · have hstep := Real.logb_le_logb_of_le hb1 (pow_pos hbpos (m - 1)) h1R
    rw [Real.logb_pow, Real.logb_self_eq_one hb1, mul_one, hmcast] at hstep
    linarith
  · have hstep := Real.logb_le_logb_of_le hb1 hVpos h2R
    rw [Real.logb_pow, Real.logb_self_eq_one hb1, mul_one] at hstep
    push_cast at hstep
    linarith

/-- **Dense confirmation delay** (`eq:delay` with `λ = 2N-2`): the delay
`D = m · t_ave` and `(log_λ V) · t_ave` differ by at most two layer times, namely
`(log_λ V - 2) · t_ave ≤ D ≤ (log_λ V + 1) · t_ave`, stated subtraction-free.
Both constants are independent of `m`. -/
theorem dense_delay_eq_logb (N m : ℕ) (tave : ℝ) (hN : 3 ≤ N) (hm : 2 ≤ m)
    (ht : 0 ≤ tave) :
    delay m tave ≤ Real.logb (2 * (N : ℝ) - 2) (Dense.V N m) * tave + tave ∧
      Real.logb (2 * (N : ℝ) - 2) (Dense.V N m) * tave ≤ delay m tave + 2 * tave := by
  obtain ⟨h1, h2⟩ := dense_depth_eq_logb N m hN hm
  have k1 := mul_le_mul_of_nonneg_right h1 ht
  have k2 := mul_le_mul_of_nonneg_right h2 ht
  simp only [delay]
  constructor
  · nlinarith [k1]
  · nlinarith [k2]

/-! ## The design corollary (closing paragraph of subsec:delay) -/

/-- **Design rule** (closing paragraph of `subsec:delay`): a target depth bound
`D ≥ 1` — equivalently, a target delay `D · t_ave` — is met as soon as the
population fits under `N^D`.  Monotone consequence of the lower half of
`card_pow_bounds`. -/
theorem depth_le_of_card_le (N m D : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (h : Fintype.card (Addr N m) ≤ N ^ D) : m ≤ D := by
  have h1 := (card_pow_bounds N m hN hm).1
  exact (Nat.pow_le_pow_iff_right (by omega)).mp (h1.trans h)

/-- The same rule in delay units: if the population fits under `N^D` then the
confirmation delay `m · t_ave` is at most the target `D · t_ave`. -/
theorem delay_le_of_card_le (N m D : ℕ) (tave : ℝ) (hN : 2 ≤ N) (hm : 1 ≤ m)
    (hD : 1 ≤ D) (ht : 0 ≤ tave) (h : Fintype.card (Addr N m) ≤ N ^ D) :
    delay m tave ≤ D * tave := by
  have hmd := depth_le_of_card_le N m D hN hm hD h
  have hR : (m : ℝ) ≤ (D : ℝ) := by exact_mod_cast hmd
  simpa [delay] using mul_le_mul_of_nonneg_right hR ht

end HSFN.Delay
