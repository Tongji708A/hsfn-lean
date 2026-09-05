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
`(⌈log₂ N⌉ + 1) / log₂(2N-2)`. That limit equals `4/3` at `N = 5`, is at most
`3/2` with equality only at `N = 3`, and decreases toward `1` along `N = 2^k`.

`⌈log₂ N⌉` is rendered as `Nat.clog 2 N`. The statements below are frozen; only
the proofs are to be supplied.

## What this file proves, and what it does not

Formalized: `tierBits_eq` (the bit count `(m+1)⌈log₂ N⌉ + m`, part (a));
`countingBound_bounds` (the explicit `O(1)` window around
`(m-1) log₂(2N-2)`); `tendsto_tierBits_div_countingBound` (part (b), the full
`Tendsto` for every fixed `N ≥ 3`); `ratioLimit_five`, `ratioLimit_three` and
their limit forms `tendsto_ratio_five`, `tendsto_ratio_three` (part (c)).

The general shape of the limit — the rest of the paper's sentence — is parts (d)
and (e): `ratioLimit_le_three_halves` (at most `3/2` for every `N ≥ 3`),
`ratioLimit_lt_three_halves` (strict as soon as `N ≥ 4`) and
`ratioLimit_eq_three_halves_iff` (equality *only* at `N = 3`); along the powers
of two, `ratioLimit_two_pow` (the closed form `(k+1)/log₂(2^{k+1}-2)`),
`ratioLimit_two_pow_bounds` (`1 ≤ · ≤ (k+1)/k` for `k ≥ 1`),
`ratioLimit_two_pow_antitone` (the decrease, non-strict form),
`ratioLimit_two_pow_strictAnti` (the *strict* decrease for `1 ≤ j < k`) with its
consecutive-powers corollary `ratioLimit_two_pow_succ_lt`, and
`tendsto_ratioLimit_two_pow` (convergence to `1`).  These are the dense-variant twins of
`HSFN.Locator.clog_ratio_le`, `clog_ratio_lt` and `clog_ratio_eq_one_iff`.

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
* The behaviour of `ratioLimit N` *between* consecutive powers of two. Along
  `N = 2^k` the decrease is now proved in both the non-strict and the strict form
  (`ratioLimit_two_pow_antitone`, `ratioLimit_two_pow_strictAnti`,
  `ratioLimit_two_pow_succ_lt`) with convergence to `1`; but `N ↦ ratioLimit N` is
  **not** monotone in `N` — `ratioLimit_four_lt_five` proves
  `ratioLimit 4 = 3/log₂ 6 < 4/3 = ratioLimit 5` — and no interpolating statement is
  proved here. For general `N` only the bound `ratioLimit_le_three_halves` and its
  strict/equality refinements (`ratioLimit_lt_three_halves`,
  `ratioLimit_eq_three_halves_iff`) are available.
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

/-! ## The general shape of the limit (Section subsec:duality) -/

/-- Auxiliary: `⌈log₂ N⌉ ≥ 2` for `N ≥ 3`. -/
private theorem aux_two_le_clog (N : ℕ) (hN : 3 ≤ N) : 2 ≤ Nat.clog 2 N := by
  have h : 1 < Nat.clog 2 N := by
    rw [Nat.lt_clog_iff_pow_lt one_lt_two, pow_one]
    omega
  omega

/-- Auxiliary: `2^⌈log₂ N⌉ ≤ 2N - 2` for `N ≥ 3`, because `2^(⌈log₂ N⌉ - 1) < N`. -/
private theorem aux_pow_clog_le (N : ℕ) (hN : 3 ≤ N) :
    2 ^ Nat.clog 2 N ≤ 2 * N - 2 := by
  have hc2 : 2 ≤ Nat.clog 2 N := aux_two_le_clog N hN
  have hp : 2 ^ (Nat.clog 2 N).pred < N := Nat.pow_pred_clog_lt_self one_lt_two (by omega)
  rw [Nat.pred_eq_sub_one] at hp
  have hsplit : Nat.clog 2 N = (Nat.clog 2 N - 1) + 1 := by omega
  rw [hsplit, pow_succ]
  omega

/-- Auxiliary: `⌈log₂ N⌉ ≤ log₂(2N-2)` for `N ≥ 3`.  This is the one inequality
driving the whole `≤ 3/2` clause: the denominator of `ratioLimit` is at least as
large as `⌈log₂ N⌉`. -/
private theorem aux_clog_le_logb (N : ℕ) (hN : 3 ≤ N) :
    (Nat.clog 2 N : ℝ) ≤ Real.logb 2 (2 * (N : ℝ) - 2) := by
  have hcast : ((2 * N - 2 : ℕ) : ℝ) = 2 * (N : ℝ) - 2 :=
    aux_cast_two_mul_sub_two N (by omega)
  have hR : ((2 : ℝ)) ^ (Nat.clog 2 N) ≤ 2 * (N : ℝ) - 2 := by
    rw [← hcast]
    exact_mod_cast aux_pow_clog_le N hN
  have hpos : (0 : ℝ) < ((2 : ℝ)) ^ (Nat.clog 2 N) := by positivity
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hR
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h

/-- Auxiliary: the denominator `log₂(2N-2)` is positive for `N ≥ 3`. -/
private theorem aux_logb_pos (N : ℕ) (hN : 3 ≤ N) :
    0 < Real.logb 2 (2 * (N : ℝ) - 2) := by
  have h := aux_clog_le_logb N hN
  have hc : (2 : ℝ) ≤ (Nat.clog 2 N : ℝ) := by exact_mod_cast aux_two_le_clog N hN
  linarith

/-- **(d)** The general upper bound of Section subsec:duality: for every `N ≥ 3` the
limiting locator-to-counting-bound ratio is at most `3/2`.

This is the dense-variant twin of `HSFN.Locator.clog_ratio_le`: writing
`c = ⌈log₂ N⌉`, one has `2^(c-1) < N`, hence `2^c ≤ 2N-2` and therefore
`log₂(2N-2) ≥ c ≥ 2`, so `(c+1)/log₂(2N-2) ≤ (c+1)/c ≤ 3/2`. -/
theorem ratioLimit_le_three_halves (N : ℕ) (hN : 3 ≤ N) :
    ratioLimit N ≤ 3 / 2 := by
  have hc : (2 : ℝ) ≤ (Nat.clog 2 N : ℝ) := by exact_mod_cast aux_two_le_clog N hN
  have hlog := aux_clog_le_logb N hN
  have hpos := aux_logb_pos N hN
  rw [ratioLimit, div_le_iff₀ hpos]
  linarith

/-- **(d)** The bound of `ratioLimit_le_three_halves` is strict as soon as `N ≥ 4`:
either `⌈log₂ N⌉ ≥ 3`, and then `(c+1)/c ≤ 4/3 < 3/2`, or `N = 4`, where the
denominator `log₂ 6` is strictly larger than `⌈log₂ 4⌉ = 2`. -/
theorem ratioLimit_lt_three_halves (N : ℕ) (hN : 4 ≤ N) :
    ratioLimit N < 3 / 2 := by
  have hN3 : 3 ≤ N := by omega
  have hlog := aux_clog_le_logb N hN3
  have hpos := aux_logb_pos N hN3
  by_cases h3 : 3 ≤ Nat.clog 2 N
  · have hc : (3 : ℝ) ≤ (Nat.clog 2 N : ℝ) := by exact_mod_cast h3
    rw [ratioLimit, div_lt_iff₀ hpos]
    linarith
  · -- `⌈log₂ N⌉ ≤ 2` forces `N ≤ 4`, hence `N = 4`
    have hle : N ≤ 2 ^ Nat.clog 2 N := Nat.le_pow_clog one_lt_two N
    have hpow : 2 ^ Nat.clog 2 N ≤ 4 := by
      have hc2 : Nat.clog 2 N ≤ 2 := by omega
      calc 2 ^ Nat.clog 2 N ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hc2
        _ = 4 := by norm_num
    have hN4 : N = 4 := by omega
    subst hN4
    have hc : Nat.clog 2 4 = 2 := by
      have h1 : Nat.clog 2 4 ≤ 2 := Nat.clog_le_of_le_pow (by norm_num)
      have h2 : 1 < Nat.clog 2 4 := (Nat.lt_clog_iff_pow_lt one_lt_two).2 (by norm_num)
      omega
    have harg : 2 * ((4 : ℕ) : ℝ) - 2 = (6 : ℝ) := by norm_num
    have h4 : Real.logb 2 (4 : ℝ) = 2 := by
      have he : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      rw [he, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      norm_num
    have hlt := Real.logb_lt_logb (b := 2) (by norm_num) (show (0 : ℝ) < 4 by norm_num)
      (show (4 : ℝ) < 6 by norm_num)
    rw [h4] at hlt
    rw [ratioLimit, hc, harg, div_lt_iff₀ (by linarith)]
    push_cast
    linarith

/-- **(d)** Equality in `ratioLimit_le_three_halves` holds **only** at `N = 3`
(Section subsec:duality: the limit "is at most `3/2` with equality only at `N = 3`"). -/
theorem ratioLimit_eq_three_halves_iff (N : ℕ) (hN : 3 ≤ N) :
    ratioLimit N = 3 / 2 ↔ N = 3 := by
  constructor
  · intro h
    by_contra hne
    have h4 : 4 ≤ N := by omega
    exact absurd h (ne_of_lt (ratioLimit_lt_three_halves N h4))
  · rintro rfl
    exact ratioLimit_three

/-! ## The behaviour along the powers of two -/

/-- **(e)** Closed form along `N = 2^k`: the limiting ratio is
`(k+1) / log₂(2^{k+1} - 2)` (Section subsec:duality).  Stated for every `k`; the
paper's range of interest is `k ≥ 2`, i.e. `N ≥ 4`. -/
theorem ratioLimit_two_pow (k : ℕ) :
    ratioLimit (2 ^ k) = ((k : ℝ) + 1) / Real.logb 2 ((2 : ℝ) ^ (k + 1) - 2) := by
  have hc : Nat.clog 2 (2 ^ k) = k := Nat.clog_pow 2 k one_lt_two
  have harg : 2 * ((2 ^ k : ℕ) : ℝ) - 2 = (2 : ℝ) ^ (k + 1) - 2 := by
    push_cast
    ring
  rw [ratioLimit, hc, harg]

/-- Auxiliary: `k ≤ log₂(2^{k+1} - 2) ≤ k+1` for `k ≥ 1`, since
`2^k ≤ 2^{k+1} - 2 ≤ 2^{k+1}`. -/
private theorem aux_two_pow_logb_bounds (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ (k + 1) - 2)
      ∧ Real.logb 2 ((2 : ℝ) ^ (k + 1) - 2) ≤ (k : ℝ) + 1 := by
  have h2k : (2 : ℝ) ≤ (2 : ℝ) ^ k := by
    have hn : (2 : ℕ) ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h' : (((2 : ℕ) ^ 1 : ℕ) : ℝ) ≤ (((2 : ℕ) ^ k : ℕ) : ℝ) := by exact_mod_cast hn
    push_cast at h'
    linarith
  have hsucc : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
  have hlow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) - 2 := by rw [hsucc]; linarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hargpos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) - 2 := lt_of_lt_of_le hpos hlow
  refine ⟨?_, ?_⟩
  · have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hlow
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
  · have hle : (2 : ℝ) ^ (k + 1) - 2 ≤ (2 : ℝ) ^ (k + 1) := by linarith
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hargpos hle
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
    push_cast at h
    linarith

/-- Auxiliary: `(k+1)/k → 1`. -/
private theorem aux_tendsto_succ_div :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) / (k : ℝ)) atTop (𝓝 1) := by
  have h2 : Tendsto (fun k : ℕ => (1 : ℝ) / k) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h3 := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  field_simp

/-- **(e)** The two-sided bound behind the convergence along powers of two: for
`k ≥ 1` the limiting ratio at `N = 2^k` lies in `[1, (k+1)/k]`. -/
theorem ratioLimit_two_pow_bounds (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ ratioLimit (2 ^ k) ∧ ratioLimit (2 ^ k) ≤ ((k : ℝ) + 1) / (k : ℝ) := by
  obtain ⟨hlo, hhi⟩ := aux_two_pow_logb_bounds k hk
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hpos : (0 : ℝ) < Real.logb 2 ((2 : ℝ) ^ (k + 1) - 2) := by linarith
  refine ⟨?_, ?_⟩
  · rw [ratioLimit_two_pow, le_div_iff₀ hpos]
    linarith
  · rw [ratioLimit_two_pow]
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) hlo

/-- **(e)** Along the powers of two the limiting ratio tends to `1`
(Section subsec:duality: the limit "decreases toward `1` along `N = 2^k`").
This theorem supplies only the "toward `1`" half, squeezed from the two-sided bound
`1 ≤ ratioLimit (2^k) ≤ (k+1)/k` of `ratioLimit_two_pow_bounds`; the "decreases"
half is `ratioLimit_two_pow_antitone` / `ratioLimit_two_pow_strictAnti`. -/
theorem tendsto_ratioLimit_two_pow :
    Tendsto (fun k : ℕ => ratioLimit (2 ^ k)) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds aux_tendsto_succ_div
    ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk
    exact (ratioLimit_two_pow_bounds k hk).1
  · filter_upwards [eventually_ge_atTop 1] with k hk
    exact (ratioLimit_two_pow_bounds k hk).2


/-- Auxiliary: `log₂(2^{k+1}) = k+1`. -/
private theorem aux_logb_two_pow_succ (k : ℕ) :
    Real.logb 2 ((2 : ℝ) ^ (k + 1)) = (k : ℝ) + 1 := by
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  push_cast
  ring

/-- Auxiliary: `4 ≤ 2^{k+1}` for `k ≥ 1`. -/
private theorem aux_four_le_two_pow (k : ℕ) (hk : 1 ≤ k) : (4 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
  have hn : (2 : ℕ) ^ 2 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h' : ((2 : ℝ)) ^ 2 ≤ ((2 : ℝ)) ^ (k + 1) := by exact_mod_cast hn
  calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
    _ ≤ (2 : ℝ) ^ (k + 1) := h'

/-- Auxiliary: `2^{j+1} ≤ 2^{k+1}` for `j ≤ k`. -/
private theorem aux_two_pow_le {j k : ℕ} (hjk : j ≤ k) :
    (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (k + 1) := by
  have hn : (2 : ℕ) ^ (j + 1) ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast hn

/-- Auxiliary: the *excess* `e_k = (k+1) - log₂(2^{k+1} - 2)` — the amount by which the
denominator of the closed form falls short of the numerator — is antitone in `k`,
because `2^{k+1}/(2^{k+1} - 2)` shrinks as `k` grows. -/
private theorem aux_excess_le {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    ((k : ℝ) + 1) - Real.logb 2 ((2 : ℝ) ^ (k + 1) - 2)
      ≤ ((j : ℝ) + 1) - Real.logb 2 ((2 : ℝ) ^ (j + 1) - 2) := by
  have hk : 1 ≤ k := le_trans hj hjk
  have hA4 : (4 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := aux_four_le_two_pow k hk
  have hB4 : (4 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := aux_four_le_two_pow j hj
  have hBA : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (k + 1) := aux_two_pow_le hjk
  have hA2 : (0 : ℝ) < (2 : ℝ) ^ (k + 1) - 2 := by linarith
  have hB2 : (0 : ℝ) < (2 : ℝ) ^ (j + 1) - 2 := by linarith
  have hratio : (2 : ℝ) ^ (k + 1) / ((2 : ℝ) ^ (k + 1) - 2)
      ≤ (2 : ℝ) ^ (j + 1) / ((2 : ℝ) ^ (j + 1) - 2) := by
    rw [div_le_div_iff₀ hA2 hB2]
    nlinarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) / ((2 : ℝ) ^ (k + 1) - 2) :=
    div_pos (by positivity) hA2
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos hratio
  rw [Real.logb_div (by positivity) (ne_of_gt hA2),
    Real.logb_div (by positivity) (ne_of_gt hB2),
    aux_logb_two_pow_succ k, aux_logb_two_pow_succ j] at h
  linarith

/-- **(e)** The limiting ratio decreases along the powers of two: for `1 ≤ j ≤ k`
one has `ratioLimit (2^k) ≤ ratioLimit (2^j)`.  This is the non-strict form;
`ratioLimit_two_pow_strictAnti` sharpens it to `<` for `j < k`.  Together with
`tendsto_ratioLimit_two_pow` this is the paper's clause that the limit "decreases
toward `1` along `N = 2^k`" (Section subsec:duality). -/
theorem ratioLimit_two_pow_antitone {j k : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    ratioLimit (2 ^ k) ≤ ratioLimit (2 ^ j) := by
  have hk : 1 ≤ k := le_trans hj hjk
  obtain ⟨hklo, hkhi⟩ := aux_two_pow_logb_bounds k hk
  obtain ⟨hjlo, hjhi⟩ := aux_two_pow_logb_bounds j hj
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjkR : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
  have hLk : (0 : ℝ) < Real.logb 2 ((2 : ℝ) ^ (k + 1) - 2) := by linarith
  have hLj : (0 : ℝ) < Real.logb 2 ((2 : ℝ) ^ (j + 1) - 2) := by linarith
  have hee := aux_excess_le hj hjk
  have hej : (0 : ℝ) ≤ ((j : ℝ) + 1) - Real.logb 2 ((2 : ℝ) ^ (j + 1) - 2) := by linarith
  have key : ((j : ℝ) + 1) * (((k : ℝ) + 1) - Real.logb 2 ((2 : ℝ) ^ (k + 1) - 2))
      ≤ ((k : ℝ) + 1) * (((j : ℝ) + 1) - Real.logb 2 ((2 : ℝ) ^ (j + 1) - 2)) := by
    have h1 := mul_le_mul_of_nonneg_left hee (show (0 : ℝ) ≤ (j : ℝ) + 1 by linarith)
    have h2 := mul_le_mul_of_nonneg_right (show (j : ℝ) + 1 ≤ (k : ℝ) + 1 by linarith) hej
    linarith
  rw [ratioLimit_two_pow, ratioLimit_two_pow, div_le_div_iff₀ hLk hLj]
  nlinarith [key]

/-- Auxiliary: the excess `e_k = (k+1) - log₂(2^{k+1} - 2)` is *strictly* positive for
`k ≥ 1`, since `0 < 2^{k+1} - 2 < 2^{k+1}` and `log₂(2^{k+1}) = k+1`. -/
private theorem aux_excess_pos (k : ℕ) (hk : 1 ≤ k) :
    0 < ((k : ℝ) + 1) - Real.logb 2 ((2 : ℝ) ^ (k + 1) - 2) := by
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := aux_four_le_two_pow k hk
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) - 2 := by linarith
  have hlt : Real.logb 2 ((2 : ℝ) ^ (k + 1) - 2) < Real.logb 2 ((2 : ℝ) ^ (k + 1)) :=
    Real.logb_lt_logb (by norm_num) hpos (by linarith)
  rw [aux_logb_two_pow_succ k] at hlt
  linarith

/-- **(e)** The decrease along the powers of two is in fact **strict**: for `1 ≤ j < k`
one has `ratioLimit (2^k) < ratioLimit (2^j)`.  Strictness comes from
`aux_excess_pos`: the excess `e_j = (j+1) - log₂(2^{j+1}-2)` is strictly positive,
so the antitone comparison `(j+1) e_k ≤ (j+1) e_j < (k+1) e_j` is strict at the last
step.  This is the sharp form of `ratioLimit_two_pow_antitone`. -/
theorem ratioLimit_two_pow_strictAnti {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) :
    ratioLimit (2 ^ k) < ratioLimit (2 ^ j) := by
  have hk : 1 ≤ k := le_trans hj (le_of_lt hjk)
  obtain ⟨hklo, hkhi⟩ := aux_two_pow_logb_bounds k hk
  obtain ⟨hjlo, hjhi⟩ := aux_two_pow_logb_bounds j hj
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hjkR : (j : ℝ) < (k : ℝ) := by exact_mod_cast hjk
  have hLk : (0 : ℝ) < Real.logb 2 ((2 : ℝ) ^ (k + 1) - 2) := by linarith
  have hLj : (0 : ℝ) < Real.logb 2 ((2 : ℝ) ^ (j + 1) - 2) := by linarith
  have hee := aux_excess_le hj (le_of_lt hjk)
  have hej := aux_excess_pos j hj
  have key : ((j : ℝ) + 1) * (((k : ℝ) + 1) - Real.logb 2 ((2 : ℝ) ^ (k + 1) - 2))
      < ((k : ℝ) + 1) * (((j : ℝ) + 1) - Real.logb 2 ((2 : ℝ) ^ (j + 1) - 2)) := by
    have h1 := mul_le_mul_of_nonneg_left hee (show (0 : ℝ) ≤ (j : ℝ) + 1 by linarith)
    have h2 := mul_lt_mul_of_pos_right (show (j : ℝ) + 1 < (k : ℝ) + 1 by linarith) hej
    linarith
  rw [ratioLimit_two_pow, ratioLimit_two_pow, div_lt_div_iff₀ hLk hLj]
  nlinarith [key]

/-- **(e)** The special case of `ratioLimit_two_pow_strictAnti` that the paper's
"decreases toward `1` along `N = 2^k`" literally asserts: consecutive powers of two
give a strictly smaller limiting ratio. -/
theorem ratioLimit_two_pow_succ_lt (k : ℕ) (hk : 1 ≤ k) :
    ratioLimit (2 ^ (k + 1)) < ratioLimit (2 ^ k) :=
  ratioLimit_two_pow_strictAnti hk (Nat.lt_succ_self k)

/-- Auxiliary: `log₂ 6 > 5/2`, because `6^2 = 36 > 32 = 2^5`. -/
private theorem aux_logb_six_gt : (5 : ℝ) / 2 < Real.logb 2 6 := by
  have h : Real.logb 2 (32 : ℝ) < Real.logb 2 (36 : ℝ) :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  have h32 : Real.logb 2 (32 : ℝ) = 5 := by
    have he : (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
    rw [he, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have h36 : Real.logb 2 (36 : ℝ) = 2 * Real.logb 2 6 := by
    have he : (36 : ℝ) = (6 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [he, Real.logb_pow]
    norm_num
  rw [h32, h36] at h
  linarith

/-- The limiting ratio is **not** monotone in `N`: `ratioLimit 4 = 3/log₂ 6 < 4/3 =
ratioLimit 5`.  Hence the decrease established by `ratioLimit_two_pow_antitone` /
`ratioLimit_two_pow_strictAnti` is genuinely a statement about the subsequence
`N = 2^k` and does not extend to all of `N`. -/
theorem ratioLimit_four_lt_five : ratioLimit 4 < ratioLimit 5 := by
  have hc : Nat.clog 2 4 = 2 := by
    have h1 : Nat.clog 2 4 ≤ 2 := Nat.clog_le_of_le_pow (by norm_num)
    have h2 : 1 < Nat.clog 2 4 := (Nat.lt_clog_iff_pow_lt one_lt_two).2 (by norm_num)
    omega
  have harg : 2 * ((4 : ℕ) : ℝ) - 2 = (6 : ℝ) := by norm_num
  have h6 := aux_logb_six_gt
  rw [ratioLimit_five, ratioLimit, hc, harg, div_lt_iff₀ (by linarith)]
  push_cast
  linarith

end

end TierLocator

end HSFN
