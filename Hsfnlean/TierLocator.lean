/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Dense

/-!
# The dense-variant tier locator (Appendix app:update, Section subsec:duality)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

The dense-variant subscript-pair representation translates into a binary address,
the *tier locator*. Each of the `m` subscript pairs costs `⌈log₂ N⌉ + 1` bits
(a first component in `{1,…,N}` and a one-bit second component), and a further
`⌈log₂ N⌉` bits encode `N-1`, a zero-based code for the cell size; padding pairs
are set to the invalid `(N,1)` so that the last zero bit identifies the generation
tier. A node of `V_{N,m}` is therefore addressed by

  `tierBits N m = (m+1) ⌈log₂ N⌉ + m`

bits. Since `log₂ |V_{N,m}| = (m-1) log₂(2N-2) + O(1)` — here obtained from the
two-sided count `HSFN.Dense.V_bounds`, which is the same geometric-sum content as
the closed form `eq:closed-form` (`HSFN.Dense.V_closed`) — the ratio of the
locator length to the counting bound `log₂ |V_{N,m}|` tends, as `m → ∞`, to
`(⌈log₂ N⌉ + 1) / log₂(2N-2)`. That limit equals `4/3` at `N = 5` and `3/2` at
`N = 3`.

`⌈log₂ N⌉` is rendered as `Nat.clog 2 N`. The statements below are frozen; only
the proofs are to be supplied.

## What this file proves, and what it does not

Formalized: `tierBits_eq` (the bit count `(m+1)⌈log₂ N⌉ + m`, part (a));
`countingBound_bounds` (the explicit `O(1)` window around
`(m-1) log₂(2N-2)`); `tendsto_tierBits_div_countingBound` (part (b), the full
`Tendsto` for every fixed `N ≥ 3`); `ratioLimit_five`, `ratioLimit_three` and
their limit forms `tendsto_ratio_five`, `tendsto_ratio_three` (part (c)).

**Not** formalized here, and deliberately out of scope:

* The *adequacy* of the encoding. `tierBits` is a bit **count**, not a coding
  map: no injection `V_{N,m} ↪ Bool^(tierBits N m)` is constructed, and the
  padding convention "set padding pairs to the invalid `(N,1)` so that the last
  zero bit identifies the generation tier" is described in prose only. Nothing
  below rules out a shorter code; the file establishes the *cost* of the paper's
  locator and its ratio to the counting bound, not its optimality.
* The subscript-pair label grammar `Label_{N,m}` itself (the veto
  `last(label) ≠ l`, the scale invariance under relabeling `τ`) — that is
  `Hsfnlean.Relabel` / `Hsfnlean.Dense` territory; here `|V_{N,m}|` enters only
  through the count `HSFN.Dense.V`.
* The remaining two clauses of the paper's sentence on the limit: that it is
  `≤ 3/2` for all `N ≥ 3` with equality only at `N = 3`, and that it decreases
  toward `1` along `N = 2^k`. Only the two numeric values are proved.
* Routing (the LCA comparison of two locators, the `≤ 2m` hop bound of
  Section subsec:duality) — none of it is touched.
-/

namespace HSFN

namespace TierLocator

noncomputable section

open Filter Topology

/-- Cost in bits of one subscript pair `(i, j)` with `i ∈ {1,…,N}` and `j ∈ {0,1}`:
`⌈log₂ N⌉ + 1` bits (Section subsec:duality). -/
def pairBits (N : ℕ) : ℕ := Nat.clog 2 N + 1

/-- Length in bits of the dense-variant **tier locator** of a node of `V_{N,m}`:
`m` subscript pairs at `pairBits N` bits each, plus `⌈log₂ N⌉` bits encoding `N-1`
(the zero-based code for the cell size). -/
def tierBits (N m : ℕ) : ℕ := m * pairBits N + Nat.clog 2 N

/-- **(a)** The locator length is `(m+1)⌈log₂ N⌉ + m` bits (Section subsec:duality). -/
theorem tierBits_eq (N m : ℕ) :
    tierBits N m = (m + 1) * Nat.clog 2 N + m := by
  simp only [tierBits, pairBits]
  ring

/-- The limiting locator-to-counting-bound ratio `(⌈log₂ N⌉ + 1) / log₂(2N-2)`. -/
def ratioLimit (N : ℕ) : ℝ := ((Nat.clog 2 N : ℝ) + 1) / Real.logb 2 (2 * (N : ℝ) - 2)

/-- The counting bound `log₂ |V_{N,m}|` of the dense variant. -/
def countingBound (N m : ℕ) : ℝ := Real.logb 2 (HSFN.Dense.V N m : ℝ)

/-- Auxiliary: for `N ≥ 1` the real cast of the natural `2N-2` is the real `2N-2`. -/
private theorem aux_cast_two_mul_sub_two (N : ℕ) (hN : 1 ≤ N) :
    ((2 * N - 2 : ℕ) : ℝ) = 2 * (N : ℝ) - 2 := by
  have h : 2 ≤ 2 * N := by omega
  rw [Nat.cast_sub h]
  push_cast
  ring

/-- `log₂ |V_{N,m}| = (m-1) log₂(2N-2) + O(1)`, in the explicit two-sided form obtained
by squeezing the bounds `HSFN.Dense.V_bounds` (which come from the closed form
`eq:closed-form`, `HSFN.Dense.V_closed`):
`(m-2) log₂(2N-2) + 2 log₂ N ≤ log₂|V_{N,m}| ≤ (m-1) log₂(2N-2) + 2 log₂ N + 1`. -/
theorem countingBound_bounds (N m : ℕ) (hN : 3 ≤ N) (hm : 2 ≤ m) :
    ((m : ℝ) - 2) * Real.logb 2 (2 * (N : ℝ) - 2) + 2 * Real.logb 2 (N : ℝ)
      ≤ countingBound N m
    ∧ countingBound N m
      ≤ ((m : ℝ) - 1) * Real.logb 2 (2 * (N : ℝ) - 2) + 2 * Real.logb 2 (N : ℝ) + 1 := by
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hlow, hupp⟩ := HSFN.Dense.V_bounds N m hN2 hm
  have hcast : ((2 * N - 2 : ℕ) : ℝ) = 2 * (N : ℝ) - 2 := aux_cast_two_mul_sub_two N (by omega)
  have hKpos : 0 < 2 * N - 2 := by omega
  have hb : (1 : ℝ) < 2 := by norm_num
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hKR : (0 : ℝ) < ((2 * N - 2 : ℕ) : ℝ) := by exact_mod_cast hKpos
  have hmc : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
    rw [Nat.cast_sub hm]; norm_num
  have hmc1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
  have hpow2 : (0 : ℝ) < (N : ℝ) ^ 2 * ((2 * N - 2 : ℕ) : ℝ) ^ (m - 2) := by positivity
  have hlowR : (N : ℝ) ^ 2 * ((2 * N - 2 : ℕ) : ℝ) ^ (m - 2) ≤ (HSFN.Dense.V N m : ℝ) := by
    exact_mod_cast hlow
  have hVpos : (0 : ℝ) < (HSFN.Dense.V N m : ℝ) := lt_of_lt_of_le hpow2 hlowR
  have hlogLow :
      Real.logb 2 ((N : ℝ) ^ 2 * ((2 * N - 2 : ℕ) : ℝ) ^ (m - 2))
        = 2 * Real.logb 2 (N : ℝ) + ((m : ℝ) - 2) * Real.logb 2 (2 * (N : ℝ) - 2) := by
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow, hcast, hmc]
    norm_num
  have hnat : HSFN.Dense.V N m ≤ 2 * (N ^ 2 * (2 * N - 2) ^ (m - 1)) := by
    have h1 : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N
    have h2 : 0 < (2 * N - 2) ^ (m - 1) := pow_pos hKpos _
    have h3 : N ^ 2 ≤ N ^ 2 * (2 * N - 2) ^ (m - 1) := Nat.le_mul_of_pos_right _ h2
    calc HSFN.Dense.V N m ≤ N + N ^ 2 * (2 * N - 2) ^ (m - 1) := hupp
      _ ≤ N ^ 2 * (2 * N - 2) ^ (m - 1) + N ^ 2 * (2 * N - 2) ^ (m - 1) :=
          Nat.add_le_add_right (le_trans h1 h3) _
      _ = 2 * (N ^ 2 * (2 * N - 2) ^ (m - 1)) := by ring
  have huppR : (HSFN.Dense.V N m : ℝ)
      ≤ 2 * ((N : ℝ) ^ 2 * ((2 * N - 2 : ℕ) : ℝ) ^ (m - 1)) := by
    exact_mod_cast hnat
  have hlogUp :
      Real.logb 2 (2 * ((N : ℝ) ^ 2 * ((2 * N - 2 : ℕ) : ℝ) ^ (m - 1)))
        = 1 + (2 * Real.logb 2 (N : ℝ) + ((m : ℝ) - 1) * Real.logb 2 (2 * (N : ℝ) - 2)) := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_mul (by positivity) (by positivity),
      Real.logb_pow, Real.logb_pow, hcast, hmc1, Real.logb_self_eq_one (by norm_num)]
    norm_num
  refine ⟨?_, ?_⟩
  · have h := Real.logb_le_logb_of_le hb hpow2 hlowR
    rw [hlogLow] at h
    simp only [countingBound]
    linarith
  · have h := Real.logb_le_logb_of_le hb hVpos huppR
    rw [hlogUp] at h
    simp only [countingBound]
    linarith

/-- Auxiliary: the real cast of the locator length, `m(⌈log₂ N⌉ + 1) + ⌈log₂ N⌉`. -/
private theorem aux_tierBits_cast (N m : ℕ) :
    (tierBits N m : ℝ) = (m : ℝ) * ((Nat.clog 2 N : ℝ) + 1) + (Nat.clog 2 N : ℝ) := by
  simp only [tierBits, pairBits]
  push_cast
  ring

/-- Auxiliary: `L + K/m → L` as `m → ∞`. -/
private theorem aux_tendsto_affine (L K : ℝ) :
    Tendsto (fun m : ℕ => L + K / (m : ℝ)) atTop (𝓝 L) := by
  simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat K)

/-- Auxiliary: the locator length per tier tends to `⌈log₂ N⌉ + 1`. -/
private theorem aux_tendsto_num (N : ℕ) :
    Tendsto (fun m : ℕ => (tierBits N m : ℝ) / (m : ℝ)) atTop
      (𝓝 ((Nat.clog 2 N : ℝ) + 1)) := by
  refine (aux_tendsto_affine ((Nat.clog 2 N : ℝ) + 1) (Nat.clog 2 N : ℝ)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [aux_tierBits_cast]
  field_simp

/-- Auxiliary: the counting bound per tier tends to `log₂(2N-2)`; this is the squeeze
of `countingBound_bounds`, whose two sides share the leading coefficient. -/
private theorem aux_tendsto_den (N : ℕ) (hN : 3 ≤ N) :
    Tendsto (fun m : ℕ => countingBound N m / (m : ℝ)) atTop
      (𝓝 (Real.logb 2 (2 * (N : ℝ) - 2))) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (aux_tendsto_affine (Real.logb 2 (2 * (N : ℝ) - 2))
      (2 * Real.logb 2 (N : ℝ) - 2 * Real.logb 2 (2 * (N : ℝ) - 2)))
    (aux_tendsto_affine (Real.logb 2 (2 * (N : ℝ) - 2))
      (2 * Real.logb 2 (N : ℝ) + 1 - Real.logb 2 (2 * (N : ℝ) - 2))) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with m hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      have : 0 < m := by omega
      exact_mod_cast this
    have key : Real.logb 2 (2 * (N : ℝ) - 2)
          + (2 * Real.logb 2 (N : ℝ) - 2 * Real.logb 2 (2 * (N : ℝ) - 2)) / (m : ℝ)
        = (((m : ℝ) - 2) * Real.logb 2 (2 * (N : ℝ) - 2)
            + 2 * Real.logb 2 (N : ℝ)) / (m : ℝ) := by
      field_simp
      ring
    rw [key, div_le_div_iff_of_pos_right hm0]
    exact (countingBound_bounds N m hN hm).1
  · filter_upwards [eventually_ge_atTop 2] with m hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      have : 0 < m := by omega
      exact_mod_cast this
    have key : Real.logb 2 (2 * (N : ℝ) - 2)
          + (2 * Real.logb 2 (N : ℝ) + 1 - Real.logb 2 (2 * (N : ℝ) - 2)) / (m : ℝ)
        = (((m : ℝ) - 1) * Real.logb 2 (2 * (N : ℝ) - 2)
            + 2 * Real.logb 2 (N : ℝ) + 1) / (m : ℝ) := by
      field_simp
      ring
    rw [key, div_le_div_iff_of_pos_right hm0]
    exact (countingBound_bounds N m hN hm).2

/-- **(b)** For fixed `N ≥ 3`, the ratio of the tier-locator length to the counting
bound `log₂ |V_{N,m}|` tends, as `m → ∞`, to `(⌈log₂ N⌉ + 1) / log₂(2N-2)`
(Section subsec:duality). -/
theorem tendsto_tierBits_div_countingBound (N : ℕ) (hN : 3 ≤ N) :
    Tendsto (fun m : ℕ => (tierBits N m : ℝ) / countingBound N m) atTop
      (𝓝 (ratioLimit N)) := by
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hL : 0 < Real.logb 2 (2 * (N : ℝ) - 2) :=
    Real.logb_pos (by norm_num) (by linarith)
  have h := (aux_tendsto_num N).div (aux_tendsto_den N hN) (ne_of_gt hL)
  rw [ratioLimit]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Pi.div_apply]
  exact div_div_div_cancel_right₀ hm0 _ _

/-- **(c)** The limiting ratio equals `4/3` at `N = 5`
(`⌈log₂ 5⌉ = 3`, `log₂ 8 = 3`). -/
theorem ratioLimit_five : ratioLimit 5 = 4 / 3 := by
  have hc : Nat.clog 2 5 = 3 := by norm_num [Nat.clog]
  have h8 : 2 * ((5 : ℕ) : ℝ) - 2 = (2 : ℝ) ^ (3 : ℕ) := by norm_num
  rw [ratioLimit, hc, h8, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- **(c)** The limiting ratio equals `3/2` at `N = 3`
(`⌈log₂ 3⌉ = 2`, `log₂ 4 = 2`). -/
theorem ratioLimit_three : ratioLimit 3 = 3 / 2 := by
  have hc : Nat.clog 2 3 = 2 := by norm_num [Nat.clog]
  have h4 : 2 * ((3 : ℕ) : ℝ) - 2 = (2 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [ratioLimit, hc, h4, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- **(c)**, in limit form at `N = 5`: the locator spends `4/3` of the counting bound. -/
theorem tendsto_ratio_five :
    Tendsto (fun m : ℕ => (tierBits 5 m : ℝ) / countingBound 5 m) atTop (𝓝 (4 / 3)) := by
  have h := tendsto_tierBits_div_countingBound 5 (by norm_num)
  rwa [ratioLimit_five] at h

/-- **(c)**, in limit form at `N = 3`: the locator spends `3/2` of the counting bound. -/
theorem tendsto_ratio_three :
    Tendsto (fun m : ℕ => (tierBits 3 m : ℝ) / countingBound 3 m) atTop (𝓝 (3 / 2)) := by
  have h := tendsto_tierBits_div_countingBound 3 (by norm_num)
  rwa [ratioLimit_three] at h

end

end TierLocator

end HSFN
