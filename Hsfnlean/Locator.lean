/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Mathlib
import Hsfnlean.Basic

/-!
# The length-prefixed HSFN locator (Proposition prop:locator-II)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

The address `a = a₁ a₂ ⋯ a_t ∈ 𝒲_{N,m}` is published on the wire as the
length-prefixed locator `⟨N, t, a₁ ⋯ a_t⟩`, made of three fields:

* a cell-size field of `⌈log₂ N⌉` bits carrying the zero-based code `N-1`;
* a tier field of `⌈log₂ m⌉` bits carrying `t ∈ {1, …, m}`;
* `t` digit fields of `⌈log₂ N⌉` bits each, one per digit `aᵢ ∈ Fin N`.

Hence the locator length is `⌈log₂ N⌉ + ⌈log₂ m⌉ + t⌈log₂ N⌉` bits, which is
monotone in `t` and therefore maximal at `t = m`, where it equals
`⌈log₂ m⌉ + (m+1)⌈log₂ N⌉`.  Measured against the counting yardstick
`log₂ V_II(N,m)` (Proposition prop:addr-bij, here `Fintype.card (Addr N m)`,
see `HSFN.Addr.card_eq_sum` and `HSFN.Addr.card_closed`), the overhead ratio
converges, for fixed `N ≥ 3`, to `⌈log₂ N⌉ / log₂ N`; that limit is at least
`1`, is strictly below `1 + 1/log₂ N`, and equals `1` exactly when `N` is a
power of two.  The bound `1 + 1/log₂ N` itself tends to `1` as `N → ∞`.

That the three field widths really encode an address is recorded by the three
capacity lemmas and by `card_tier_le_two_pow_digits` / `card_le_two_pow_locMax`,
which say that the locator has at least as many codewords as there are nodes.

Throughout, `⌈log₂ x⌉` is `Nat.clog 2 x` (the least `k` with `x ≤ 2^k`) and the
statements are kept subtraction-free: "a field of `w` bits carries the
zero-based code of `x` values" is written `x ≤ 2 ^ w`.

## Scope: what is *not* formalized here

* No encoder/decoder is built.  The locator is treated as a *bit budget*: the
  widths are defined, and the capacity lemmas above prove the budget large
  enough (each field has at least as many codewords as it must distinguish, and
  `2 ^ locMax N m` at least as many as there are nodes).  An explicit injection
  `Addr N m ↪ Bool^(locMax N m)` and its inverse are left to a wire-format file.
* No optimality claim: nothing here says that fewer than `locBits N m t` bits
  would *not* suffice.  The paper likewise only asserts the length of this
  particular encoding, and compares it against the counting yardstick.
* The yardstick `log₂ V_II(N,m)` is handled through the two-sided bound
  `N^m ≤ V_II(N,m) ≤ N^{m+1}` (`pow_le_card`, `card_le_pow`, `logb_card_bounds`)
  rather than through the exact closed form; this is enough for the limit and is
  the same `m log₂ N + O(1)` estimate the paper's proof uses.
* Nothing about greedy forwarding on locators (Theorem thm:distance-II) is
  proved here; see `Hsfnlean.Greedy`.
-/

namespace HSFN.Locator

open Filter Topology

/-! ## The three locator fields -/

/-- Width of the cell-size field of the locator: `⌈log₂ N⌉` bits, carrying the
zero-based code of the cell size `N` (Proposition prop:locator-II). -/
def cellField (N : ℕ) : ℕ := Nat.clog 2 N

/-- Width of the tier field of the locator: `⌈log₂ m⌉` bits, carrying the tier
`t ∈ {1, …, m}` (Proposition prop:locator-II). -/
def tierField (m : ℕ) : ℕ := Nat.clog 2 m

/-- Width of one digit field of the locator: `⌈log₂ N⌉` bits, carrying a digit
`aᵢ ∈ Fin N` (Proposition prop:locator-II). -/
def digitField (N : ℕ) : ℕ := Nat.clog 2 N

/-- The cell-size field is wide enough for the `N` zero-based cell sizes. -/
theorem cellField_capacity (N : ℕ) : N ≤ 2 ^ cellField N :=
  Nat.le_pow_clog one_lt_two N

/-- The tier field is wide enough for every admissible tier `1 ≤ t ≤ m`
(the zero-based code `t-1` ranges over `{0, …, m-1}`). -/
theorem tierField_capacity (m t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ m) :
    t ≤ 2 ^ tierField m :=
  h2.trans (Nat.le_pow_clog one_lt_two m)

/-- Each digit field is wide enough for every digit of the alphabet `Fin N`. -/
theorem digitField_capacity (N : ℕ) (d : Fin N) : (d : ℕ) < 2 ^ digitField N :=
  lt_of_lt_of_le d.isLt (Nat.le_pow_clog one_lt_two N)

/-! ## Part (a): the locator length and its maximum -/

/-- Length in bits of the length-prefixed locator `⟨N, t, a₁ ⋯ a_t⟩` of a
tier-`t` address of the depth-`m` HSFN over the alphabet `Fin N`
(Proposition prop:locator-II). -/
def locBits (N m t : ℕ) : ℕ := cellField N + tierField m + t * digitField N

/-- Part (a) of Proposition prop:locator-II: the locator costs
`⌈log₂ N⌉ + ⌈log₂ m⌉ + t⌈log₂ N⌉` bits. -/
theorem locBits_eq (N m t : ℕ) :
    locBits N m t = Nat.clog 2 N + Nat.clog 2 m + t * Nat.clog 2 N := rfl

/-- The locator length of an actual address, read off its tier. -/
def addrBits {N m : ℕ} (a : Addr N m) : ℕ := locBits N m a.tier

/-- The worst-case locator length `⌈log₂ m⌉ + (m+1)⌈log₂ N⌉`
(Proposition prop:locator-II). -/
def locMax (N m : ℕ) : ℕ := Nat.clog 2 m + (m + 1) * Nat.clog 2 N

/-- The locator length is monotone in the tier. -/
theorem locBits_mono (N m : ℕ) {t t' : ℕ} (h : t ≤ t') :
    locBits N m t ≤ locBits N m t' := by
  unfold locBits
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- The worst case is attained at `t = m`. -/
theorem locBits_top (N m : ℕ) : locBits N m m = locMax N m := by
  unfold locBits locMax cellField tierField digitField
  ring

/-- Part (a) of Proposition prop:locator-II: for every admissible tier
`1 ≤ t ≤ m` the locator costs at most `⌈log₂ m⌉ + (m+1)⌈log₂ N⌉` bits. -/
theorem locBits_le_locMax (N m t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ m) :
    locBits N m t ≤ locMax N m := by
  have h := locBits_mono N m h2
  rwa [locBits_top] at h

/-- Every address of the depth-`m` HSFN has a locator of at most
`⌈log₂ m⌉ + (m+1)⌈log₂ N⌉` bits. -/
theorem addrBits_le_locMax {N m : ℕ} (a : Addr N m) : addrBits a ≤ locMax N m := by
  have h := locBits_mono N m (Addr.tier_le a)
  rwa [locBits_top] at h

/-- The `t` digit fields on their own already separate the tier-`t` addresses:
there are `N^t` of them (`HSFN.Addr.card_tier`, Proposition prop:addr-bij) and
`2^(t⌈log₂ N⌉)` available digit codes. -/
theorem card_tier_le_two_pow_digits (N m t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ m) :
    Fintype.card { a : Addr N m // a.tier = t } ≤ 2 ^ (t * digitField N) := by
  rw [Addr.card_tier N m t h1 h2, mul_comm t (digitField N), pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two N) t

/-- `⌈log₂ 5⌉ = 3`. -/
private theorem aux_clog_five : Nat.clog 2 5 = 3 := by
  have h1 : Nat.clog 2 5 ≤ 3 := Nat.clog_le_of_le_pow (by norm_num)
  have h2 : 2 < Nat.clog 2 5 := (Nat.lt_clog_iff_pow_lt one_lt_two).2 (by norm_num)
  omega

/-- `⌈log₂ 3⌉ = 2`. -/
private theorem aux_clog_three : Nat.clog 2 3 = 2 := by
  have h1 : Nat.clog 2 3 ≤ 2 := Nat.clog_le_of_le_pow (by norm_num)
  have h2 : 1 < Nat.clog 2 3 := (Nat.lt_clog_iff_pow_lt one_lt_two).2 (by norm_num)
  omega

/-- The running example of the paper (`N = 5`, `m = 3`, `t = 3`):
`⌈log₂ 5⌉ = 3`, `⌈log₂ 3⌉ = 2`, so `⟨5, 3, 431⟩` costs `3 + 2 + 9 = 14` bits. -/
theorem locBits_example : locBits 5 3 3 = 14 := by
  unfold locBits cellField tierField digitField
  rw [aux_clog_five, aux_clog_three]

/-! ## The counting yardstick `log₂ V_II(N,m)` -/

/-- The node count `V_II(N,m)` dominates `N^m` (from `HSFN.Addr.card_closed`:
`(N-1)|V| + N = N^{m+1}`). -/
theorem pow_le_card (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) :
    N ^ m ≤ Fintype.card (Addr N m) := by
  have h := Addr.card_tier N m m hm le_rfl
  calc N ^ m = Fintype.card { a : Addr N m // a.tier = m } := h.symm
    _ ≤ Fintype.card (Addr N m) := Fintype.card_subtype_le _

/-- The node count `V_II(N,m)` is dominated by `N^{m+1}`
(from `HSFN.Addr.card_closed`). -/
theorem card_le_pow (N m : ℕ) (hN : 2 ≤ N) :
    Fintype.card (Addr N m) ≤ N ^ (m + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have h := Addr.card_closed n m
  calc Fintype.card (Addr (n + 1) m)
      = 1 * Fintype.card (Addr (n + 1) m) := (one_mul _).symm
    _ ≤ n * Fintype.card (Addr (n + 1) m) := Nat.mul_le_mul hn le_rfl
    _ ≤ n * Fintype.card (Addr (n + 1) m) + (n + 1) := Nat.le_add_right _ _
    _ = (n + 1) ^ (m + 1) := h

/-- `log₂ V_II(N,m) = m log₂ N + O(1)`, in the explicit two-sided form used in
the proof of Proposition prop:locator-II. -/
theorem logb_card_bounds (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) :
    (m : ℝ) * Real.logb 2 N ≤ Real.logb 2 (Fintype.card (Addr N m)) ∧
      Real.logb 2 (Fintype.card (Addr N m)) ≤ ((m : ℝ) + 1) * Real.logb 2 N := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have h1 : ((N : ℝ)) ^ m ≤ (Fintype.card (Addr N m) : ℝ) := by
    exact_mod_cast pow_le_card N m hN hm
  have h2 : (Fintype.card (Addr N m) : ℝ) ≤ ((N : ℝ)) ^ (m + 1) := by
    exact_mod_cast card_le_pow N m hN
  have hpow : (0 : ℝ) < ((N : ℝ)) ^ m := by positivity
  constructor
  · have h := Real.logb_le_logb_of_le one_lt_two hpow h1
    rwa [Real.logb_pow] at h
  · have h := Real.logb_le_logb_of_le one_lt_two (lt_of_lt_of_le hpow h1) h2
    rw [Real.logb_pow] at h
    push_cast at h
    linarith

/-- The locator genuinely addresses the whole network: the `⌈log₂ m⌉ + (m+1)⌈log₂ N⌉`
bit codewords are at least as many as the `V_II(N,m)` nodes.  This is what makes
the count of Proposition prop:locator-II a locator *length* rather than an
arbitrary arithmetic expression. -/
theorem card_le_two_pow_locMax (N m : ℕ) (hN : 2 ≤ N) :
    Fintype.card (Addr N m) ≤ 2 ^ locMax N m := by
  calc Fintype.card (Addr N m) ≤ N ^ (m + 1) := card_le_pow N m hN
    _ ≤ (2 ^ Nat.clog 2 N) ^ (m + 1) :=
        Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two N) _
    _ = 2 ^ ((m + 1) * Nat.clog 2 N) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ locMax N m := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)

/-! ## Part (b): the asymptotic locator overhead -/

/-- `log₂ n ≤ ⌈log₂ n⌉`, in the real-valued reading of the ceiling. -/
private theorem aux_logb_le_clog (n : ℕ) : Real.logb 2 n ≤ (Nat.clog 2 n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h : (n : ℝ) ≤ ((2 : ℝ)) ^ Nat.clog 2 n := by
      have := Nat.le_pow_clog (b := 2) one_lt_two n
      exact_mod_cast this
    have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h2 := Real.logb_le_logb_of_le (b := 2) one_lt_two hpos h
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2

/-- `⌈log₂ n⌉ < log₂ n + 1` for `n ≥ 1`. -/
private theorem aux_clog_lt_logb_add_one (n : ℕ) (hn : 1 ≤ n) :
    (Nat.clog 2 n : ℝ) < Real.logb 2 n + 1 := by
  rcases eq_or_lt_of_le hn with h1 | h1
  · rw [← h1]
    norm_num
  · have hk : 0 < Nat.clog 2 n := Nat.clog_pos one_lt_two h1
    have hp : 2 ^ (Nat.clog 2 n).pred < n := Nat.pow_pred_clog_lt_self one_lt_two h1
    rw [Nat.pred_eq_sub_one] at hp
    have hpr : ((2 : ℝ)) ^ (Nat.clog 2 n - 1) < (n : ℝ) := by exact_mod_cast hp
    have hlt := Real.logb_lt_logb (b := 2) one_lt_two (by positivity) hpr
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlt
    rw [Nat.cast_sub hk, Nat.cast_one] at hlt
    linarith

/-- `log₂ n / n → 0`. -/
private theorem aux_tendsto_logb_div_nat :
    Tendsto (fun n : ℕ => Real.logb 2 n / n) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h' : Tendsto (fun n : ℕ => Real.log n / n) atTop (𝓝 0) :=
    h.comp tendsto_natCast_atTop_atTop
  have h'' := h'.div_const (Real.log 2)
  rw [zero_div] at h''
  refine h''.congr fun n => ?_
  rw [Real.logb]
  ring

/-- `⌈log₂ n⌉ / n → 0`: the tier field is asymptotically free. -/
private theorem aux_tendsto_clog_div_nat :
    Tendsto (fun n : ℕ => (Nat.clog 2 n : ℝ) / n) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n : ℕ => (Real.logb 2 n + 1) / n) atTop (𝓝 0) := by
    have h1 := aux_tendsto_logb_div_nat
    have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr fun n => ?_
    rw [add_div]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hle : (Nat.clog 2 n : ℝ) ≤ Real.logb 2 n + 1 :=
      (aux_clog_lt_logb_add_one n hn).le
    have h0 : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hle h0

/-- `(n+1)/n → 1`. -/
private theorem aux_tendsto_succ_div_nat :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) / n) atTop (𝓝 1) := by
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h3 := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  field_simp

/-- Part (b) of Proposition prop:locator-II: for fixed `N ≥ 3`,
`(⌈log₂ m⌉ + (m+1)⌈log₂ N⌉) / log₂ V_II(N,m) → ⌈log₂ N⌉ / log₂ N` as `m → ∞`. -/
theorem locator_ratio_tendsto (N : ℕ) (hN : 3 ≤ N) :
    Tendsto (fun m : ℕ => (locMax N m : ℝ) / Real.logb 2 (Fintype.card (Addr N m)))
      atTop (𝓝 ((Nat.clog 2 N : ℝ) / Real.logb 2 N)) := by
  -- Squeeze the ratio between the two bounds of `logb_card_bounds`, using
  -- `aux_tendsto_clog_div_nat` (the tier field is asymptotically free) and
  -- `aux_tendsto_succ_div_nat`.
  have hN2 : 2 ≤ N := by omega
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hLpos : 0 < Real.logb 2 (N : ℝ) := Real.logb_pos one_lt_two hNR
  have hL0 : Real.logb 2 (N : ℝ) ≠ 0 := ne_of_gt hLpos
  have hcnn : (0 : ℝ) ≤ (Nat.clog 2 N : ℝ) := Nat.cast_nonneg _
  -- The upper envelope `⌈log₂ m⌉/(m log₂ N) + ((m+1)/m)·(⌈log₂ N⌉/log₂ N)`.
  have hupper : Tendsto
      (fun m : ℕ => (Nat.clog 2 m : ℝ) / ((m : ℝ) * Real.logb 2 (N : ℝ))
        + ((m : ℝ) + 1) / (m : ℝ) * ((Nat.clog 2 N : ℝ) / Real.logb 2 (N : ℝ)))
      atTop (𝓝 ((Nat.clog 2 N : ℝ) / Real.logb 2 (N : ℝ))) := by
    have h1 : Tendsto (fun m : ℕ => (Nat.clog 2 m : ℝ) / ((m : ℝ) * Real.logb 2 (N : ℝ)))
        atTop (𝓝 0) := by
      have h := aux_tendsto_clog_div_nat.div_const (Real.logb 2 (N : ℝ))
      rw [zero_div] at h
      refine h.congr fun m => ?_
      rw [div_div]
    have h2 := aux_tendsto_succ_div_nat.mul_const
      ((Nat.clog 2 N : ℝ) / Real.logb 2 (N : ℝ))
    rw [one_mul] at h2
    have h3 := h1.add h2
    rwa [zero_add] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · -- the ratio never drops below `⌈log₂ N⌉ / log₂ N`
    filter_upwards [eventually_ge_atTop 1] with m hm
    obtain ⟨hlo, hhi⟩ := logb_card_bounds N m hN2 hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hmL : 0 < (m : ℝ) * Real.logb 2 (N : ℝ) := mul_pos hm0 hLpos
    have hDpos : 0 < Real.logb 2 (Fintype.card (Addr N m)) := lt_of_lt_of_le hmL hlo
    have hnum : ((locMax N m : ℕ) : ℝ)
        = (Nat.clog 2 m : ℝ) + ((m : ℝ) + 1) * (Nat.clog 2 N : ℝ) := by
      unfold locMax
      push_cast
      ring
    rw [div_le_div_iff₀ hLpos hDpos, hnum]
    have hA : (Nat.clog 2 N : ℝ) * Real.logb 2 (Fintype.card (Addr N m))
        ≤ (Nat.clog 2 N : ℝ) * (((m : ℝ) + 1) * Real.logb 2 (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hhi hcnn
    have hB : (0 : ℝ) ≤ (Nat.clog 2 m : ℝ) * Real.logb 2 (N : ℝ) := by positivity
    nlinarith [hA, hB]
  · -- and never exceeds the envelope
    filter_upwards [eventually_ge_atTop 1] with m hm
    obtain ⟨hlo, hhi⟩ := logb_card_bounds N m hN2 hm
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
    have hm0' : (m : ℝ) ≠ 0 := ne_of_gt hm0
    have hmL : 0 < (m : ℝ) * Real.logb 2 (N : ℝ) := mul_pos hm0 hLpos
    have hnum : ((locMax N m : ℕ) : ℝ)
        = (Nat.clog 2 m : ℝ) + ((m : ℝ) + 1) * (Nat.clog 2 N : ℝ) := by
      unfold locMax
      push_cast
      ring
    have hgm : (Nat.clog 2 m : ℝ) / ((m : ℝ) * Real.logb 2 (N : ℝ))
        + ((m : ℝ) + 1) / (m : ℝ) * ((Nat.clog 2 N : ℝ) / Real.logb 2 (N : ℝ))
        = ((Nat.clog 2 m : ℝ) + ((m : ℝ) + 1) * (Nat.clog 2 N : ℝ))
            / ((m : ℝ) * Real.logb 2 (N : ℝ)) := by
      field_simp
    rw [hnum, hgm]
    exact div_le_div_of_nonneg_left (by positivity) hmL hlo

/-! ## Part (c): the limit lies in `[1, 1 + 1/log₂ N)` -/

/-- The limiting overhead is never below `1`: the locator never beats the
counting bound (Proposition prop:locator-II). -/
theorem one_le_clog_ratio (N : ℕ) (hN : 2 ≤ N) :
    1 ≤ (Nat.clog 2 N : ℝ) / Real.logb 2 N := by
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hlpos : 0 < Real.logb 2 (N : ℝ) := Real.logb_pos one_lt_two hNR
  exact (one_le_div hlpos).2 (aux_logb_le_clog N)

/-- Part (c) of Proposition prop:locator-II, the stated form:
`⌈log₂ N⌉ / log₂ N ≤ 1 + 1/log₂ N` for `N ≥ 2`. -/
theorem clog_ratio_le (N : ℕ) (hN : 2 ≤ N) :
    (Nat.clog 2 N : ℝ) / Real.logb 2 N ≤ 1 + 1 / Real.logb 2 N := by
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hlpos : 0 < Real.logb 2 (N : ℝ) := Real.logb_pos one_lt_two hNR
  have h := aux_clog_lt_logb_add_one N (by omega)
  rw [div_le_iff₀ hlpos]
  have hexp : (1 + 1 / Real.logb 2 (N : ℝ)) * Real.logb 2 (N : ℝ)
      = Real.logb 2 (N : ℝ) + 1 := by
    field_simp
  rw [hexp]
  linarith

/-- Part (c) of Proposition prop:locator-II, sharp form: the limiting overhead
is *strictly* below `1 + 1/log₂ N`, since `⌈log₂ N⌉ < log₂ N + 1`. -/
theorem clog_ratio_lt (N : ℕ) (hN : 2 ≤ N) :
    (Nat.clog 2 N : ℝ) / Real.logb 2 N < 1 + 1 / Real.logb 2 N := by
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hlpos : 0 < Real.logb 2 (N : ℝ) := Real.logb_pos one_lt_two hNR
  have h := aux_clog_lt_logb_add_one N (by omega)
  rw [div_lt_iff₀ hlpos]
  have hexp : (1 + 1 / Real.logb 2 (N : ℝ)) * Real.logb 2 (N : ℝ)
      = Real.logb 2 (N : ℝ) + 1 := by
    field_simp
  rw [hexp]
  linarith

/-- Part (c) of Proposition prop:locator-II: the limiting overhead equals `1`
exactly when `N` is a power of two. -/
theorem clog_ratio_eq_one_iff (N : ℕ) (hN : 2 ≤ N) :
    (Nat.clog 2 N : ℝ) / Real.logb 2 N = 1 ↔ ∃ k : ℕ, N = 2 ^ k := by
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlpos : 0 < Real.logb 2 (N : ℝ) := Real.logb_pos one_lt_two hNR
  have hlne : Real.logb 2 (N : ℝ) ≠ 0 := ne_of_gt hlpos
  constructor
  · intro h
    have hce : (Nat.clog 2 N : ℝ) = Real.logb 2 (N : ℝ) := by
      field_simp at h
      linarith
    refine ⟨Nat.clog 2 N, ?_⟩
    have hpow : ((2 : ℝ)) ^ (Nat.clog 2 N) = (N : ℝ) := by
      rw [← Real.rpow_natCast (2 : ℝ) (Nat.clog 2 N), hce]
      exact Real.rpow_logb (by norm_num) (by norm_num) hNpos
    have : ((2 ^ Nat.clog 2 N : ℕ) : ℝ) = (N : ℝ) := by push_cast; exact hpow
    exact_mod_cast this.symm
  · rintro ⟨k, rfl⟩
    have hk : k ≠ 0 := by
      rintro rfl
      norm_num at hN
    have hkR : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hk
    rw [Nat.clog_pow 2 k one_lt_two]
    have hcast : ((2 ^ k : ℕ) : ℝ) = ((2 : ℝ)) ^ k := by push_cast; ring
    rw [hcast, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    exact div_self hkR

/-- Part (c) of Proposition prop:locator-II: the bound `1 + 1/log₂ N` tends to
`1` as `N → ∞`. -/
theorem clog_ratio_bound_tendsto :
    Tendsto (fun N : ℕ => 1 + 1 / Real.logb 2 N) atTop (𝓝 (1 : ℝ)) := by
  have h : Tendsto (fun N : ℕ => Real.logb 2 (N : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => (Real.logb 2 (N : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    h.inv_tendsto_atTop.congr fun _ => rfl
  have hsum := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).add hinv
  rw [add_zero] at hsum
  simpa only [one_div] using hsum

end HSFN.Locator
