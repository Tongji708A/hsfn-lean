/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Mathlib
import Hsfnlean.Basic
import Hsfnlean.Dense

/-!
# Partial-fill message proxies (Appendix subsec:partial-fill)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

For a partially filled network the message proxy of Proposition `thm:complexity`
acquires a top-layer correction.  The dense-variant displays are the fill ratio
`eq:fill-ratio` and the proxy `eq:general-complexity`; the HSFN counterpart
`C^{II}` of Appendix `subsec:partial-fill` runs the same uniform-allocation
argument on the uniform `N`-ary cell tree, whose top layer holds `N^{m-1}` cells.

With `m ≥ 2` minimal subject to `V ≤ V_II(N,m)` and

  `k̄ = (V - V_II(N,m-1)) / N^{m-1}`

the average number of newly allocated nodes per top-layer cell, the paper's HSFN
proxy is

  `C^{II} = N²(N^{m-1}-1)/(N-1)
            + [⌊k̄⌋²(⌊k̄⌋+1-k̄) + (⌊k̄⌋+1)²(k̄-⌊k̄⌋)] N^{m-1} + V`.

This file states:

* `mix` — the two-point mixture `⌊k̄⌋²(⌊k̄⌋+1-k̄) + (⌊k̄⌋+1)²(k̄-⌊k̄⌋)` in the
  bracket, together with `mix_ge_sq` and `mix_eq_sq_iff`: it dominates the
  balanced-fill cell cost `k̄²` with equality exactly at integer `k̄`
  (convexity of `x ↦ x²` on the two lattice points bracketing `k̄`), and
  `mix_gt_sq_of_not_int` for the strict inequality at a genuinely uneven fill;
* `floor_sq_lt_mix`, `mix_lt_succ_sq` and `CII_strict_between` — at non-integer
  `k̄` the proxy lies *strictly between* the two proxies obtained by rounding `k̄`
  down and up, so neither rounding may be substituted for the mixture;
* `mix_mono`, `kbar_mono` and `CII_mono_V` — at fixed depth, with the lower tiers
  filled, `C^{II}` is monotone in the population: more participants cannot
  decrease the proxy;
* `CII_full` — collapse at full population, `k̄ = N` and `C^{II} = (N+1)V`;
* `full_population_form_independent` — the same value is produced by the dense
  form `HSFN.Dense.message_proxy`, so the full-population proxy is
  form-independent (the claim of Section `subsec:complexity`);
* a worked partial fill inside the paper's standing regime `N ≥ 3`:
  `minimalDepth_witness_three` (`N = 3`, `m = 3`, `V = 25`), where
  `k̄ = 13/9 ∉ ℤ` (`kbar_witness`, `kbar_witness_not_int`) and the three closed
  values `70 < 82 < 97` of `CII_witness_strict_between` exhibit the correction
  term at work away from the collapse point.

The lower-tier cell count `(N^{m-1}-1)/(N-1)` is carried subtraction-free as the
geometric sum `∑_{t<m-1} N^t` (`lowerCells`), with `lowerCells_closed` recording
the closed form.  Every declaration in this file carries a complete proof; the
axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`.

## Scope: what is *not* formalized here

* The *derivation* of the bracket from the allocation rule.  `mix` is **defined**
  as the paper writes it; that a uniform allocation of `k̄ · N^{m-1}` nodes over
  `N^{m-1}` cells really produces cells of size `⌊k̄⌋` and `⌊k̄⌋+1` in exactly the
  proportions `⌊k̄⌋+1-k̄` and `k̄-⌊k̄⌋`, and that a cell of size `k` costs `k²`
  messages, are the modelling assumptions of Appendix `subsec:partial-fill` and
  are taken as given.  Only the *convexity* content of the bracket (`mix_ge_sq`,
  `mix_eq_sq_iff`) and its full-population value (`mix_natCast`) are proved.
* The dense-variant display `eq:general-complexity` itself, i.e. the closed form
  `N² + N³((2N-2)^{m-2}-1)/(2N-3) + [bracket] · N(2N-2)^{m-2} + V`, and the fill
  ratio `eq:fill-ratio`.  Only its full-population collapse is reached here, and
  only through `HSFN.Dense.message_proxy`; `HSFN.Dense.V_closed` carries the
  dense closed form separately.
* Existence and uniqueness of the minimal depth `m` of `MinimalDepth`.  It is
  used only as a hypothesis, and it is satisfiable both at `N = 2`
  (`minimalDepth_witness`) and inside the paper's standing regime `N ≥ 3`
  (`minimalDepth_witness_three`), so the theorems taking it are not vacuous;
  `CII_full` in fact needs only `2 ≤ m`.
* `CII` takes the occupancy `k` and the population `V` as independent real
  arguments.  Nothing forces `k = kbar N m V` at the definition; the theorems
  below instantiate it that way.  A genuinely partial fill is exercised only at
  the single witness `(N,m,V) = (3,3,25)`; the bracketing `CII_strict_between`
  is general in `(N,m,V,k̄)`, but no closed form for `C^{II}` at partial fill is
  derived, and no general comparison with `(N+1)V` is proved.  At the witness
  `C^{II} = 82 < 100 = (N+1)V` (`CII_witness_lt_full_form`), which rules out an
  inequality of the shape `C^{II} > (N+1)V` at partial fill.
* Monotonicity of `C^{II}` in the population is proved at **fixed** depth `m`
  (`CII_mono_V`).  The population increase that forces a deeper network, i.e.
  monotonicity along the minimal depth `m = m(V)` of `MinimalDepth`, is not
  proved: it would need the lower-tier term to be compared across depths.
* `full_population_form_independent` is a conjunction of the two collapses, each
  for its own population; `CII_full_eq_dense_proxy` is the sharper statement that
  ties both forms to the *same* `V`.
-/

namespace HSFN.PartialFill

open Finset

/-! ### The HSFN node count `V_II(N,m)` -/

/-- `V_II(N,m) = ∑_{t=1}^{m} N^t = N(N^m-1)/(N-1)`, the node count of the
depth-`m` HSFN: display `eq:unified-V` of Theorem `thm:unified-count`, restated
via the address bijection of Proposition `prop:addr-bij` (Corollary
`cor:count-II` is the asymptotic form `V_II = Θ(N^m)` of the same count). -/
def VII (N m : ℕ) : ℕ := ∑ t ∈ Finset.range m, N ^ (t + 1)

/-- `V_II(N,m)` is the number of addresses, i.e. `Basic.Addr.card_eq_sum`. -/
theorem VII_eq_card (N m : ℕ) : VII N m = Fintype.card (HSFN.Addr N m) :=
  (HSFN.Addr.card_eq_sum N m).symm

/-- The number of cells of the filled lower tiers, `(N^{m-1}-1)/(N-1)`, written
subtraction-free as the geometric sum `∑_{t<m-1} N^t`. -/
def lowerCells (N m : ℕ) : ℕ := ∑ t ∈ Finset.range (m - 1), N ^ t

/-- Closed form of `lowerCells`, subtraction-free: with `N = n+1`,
`n · lowerCells + 1 = N^{m-1}`, i.e. `lowerCells = (N^{m-1}-1)/(N-1)`. -/
theorem lowerCells_closed (n m : ℕ) :
    n * lowerCells (n + 1) m + 1 = (n + 1) ^ (m - 1) := by
  have h := geom_sum_mul_add n (m - 1)
  simpa [lowerCells, Nat.mul_comm] using h

/-! ### The two-point mixture of the top layer -/

/-- The bracket of `eq:general-complexity`: under uniform allocation the
top-layer cells hold `⌊k̄⌋` or `⌊k̄⌋+1` nodes, in the proportions that average to
`k̄`, and each cell of size `k` is charged `k²` messages. -/
noncomputable def mix (k : ℝ) : ℝ :=
  (⌊k⌋ : ℝ) ^ 2 * ((⌊k⌋ : ℝ) + 1 - k) + ((⌊k⌋ : ℝ) + 1) ^ 2 * (k - (⌊k⌋ : ℝ))

/-- The convexity defect of the two-point mixture is `θ(1-θ)` for the fractional
part `θ = k̄ - ⌊k̄⌋`: a ring identity in `k̄` and `⌊k̄⌋`. -/
theorem aux_mix_sub_sq (k : ℝ) :
    mix k - k ^ 2 = (k - (⌊k⌋ : ℝ)) * (1 - (k - (⌊k⌋ : ℝ))) := by
  unfold mix
  ring

/-- **(a)** The two-point mixture dominates the balanced-fill cell cost `k̄²`:
convexity of `x ↦ x²` evaluated on the two lattice points `⌊k̄⌋, ⌊k̄⌋+1`
bracketing `k̄`. -/
theorem mix_ge_sq (k : ℝ) (hk : 0 ≤ k) : k ^ 2 ≤ mix k := by
  have h0 : (⌊k⌋ : ℝ) ≤ k := Int.floor_le k
  have h1 : k < (⌊k⌋ : ℝ) + 1 := Int.lt_floor_add_one k
  have hid := aux_mix_sub_sq k
  have hfloor : (0 : ℝ) ≤ (⌊k⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hk
  nlinarith [hid, h0, h1, hfloor]

/-- **(a), equality case** The mixture is exactly `k̄²` precisely when `k̄` is an
integer, i.e. when the uniform allocation is an exactly balanced fill. -/
theorem mix_eq_sq_iff (k : ℝ) (hk : 0 ≤ k) :
    mix k = k ^ 2 ↔ ∃ n : ℤ, k = (n : ℝ) := by
  constructor
  · intro h
    have h0 : (⌊k⌋ : ℝ) ≤ k := Int.floor_le k
    have h1 : k < (⌊k⌋ : ℝ) + 1 := Int.lt_floor_add_one k
    have hid := aux_mix_sub_sq k
    rw [h] at hid
    have hid0 : (k - (⌊k⌋ : ℝ)) * (1 - (k - (⌊k⌋ : ℝ))) = 0 := by linarith
    have hθ : k - (⌊k⌋ : ℝ) = 0 := by
      rcases mul_eq_zero.mp hid0 with h2 | h2
      · exact h2
      · linarith
    exact ⟨⌊k⌋, by linarith⟩
  · rintro ⟨n, rfl⟩
    simp only [mix, Int.floor_intCast]
    ring

/-- The mixture at an integer point is the plain square. -/
theorem mix_natCast (n : ℕ) : mix (n : ℝ) = (n : ℝ) ^ 2 := by
  simp only [mix, Int.floor_natCast]
  push_cast
  ring

/-- The mixture at an integer point is the plain square, integer form of
`mix_natCast`; it identifies `CII N m (⌊k̄⌋ : ℝ) V` and `CII N m (⌊k̄⌋+1 : ℝ) V`
as the two *rounded* proxies bracketing `C^{II}`. -/
theorem mix_intCast (n : ℤ) : mix (n : ℝ) = (n : ℝ) ^ 2 := by
  simp only [mix, Int.floor_intCast]
  ring

/-- The mixture written on the bracketing interval: on `[⌊k̄⌋, ⌊k̄⌋+1]` it is the
chord of `x ↦ x²` through the two bracketing lattice points, in point-slope
form.  A ring identity, the working form of the three inequalities below. -/
theorem aux_mix_eq (k : ℝ) :
    mix k = (⌊k⌋ : ℝ) ^ 2 + (k - (⌊k⌋ : ℝ)) * (2 * (⌊k⌋ : ℝ) + 1) := by
  unfold mix
  ring

/-- **(a), strict form** At a non-integer `k̄` — a genuinely partial fill, whose
top-layer cells cannot all have the same size — the two-point mixture *strictly*
exceeds the balanced-fill cell cost `k̄²`.  Together with `mix_ge_sq` this is the
statement that the correction term of `eq:general-complexity` does work rather
than being decorative. -/
theorem mix_gt_sq_of_not_int (k : ℝ) (hk : 0 ≤ k) (hnint : ¬ ∃ n : ℤ, k = (n : ℝ)) :
    k ^ 2 < mix k :=
  lt_of_le_of_ne (mix_ge_sq k hk) fun h => hnint ((mix_eq_sq_iff k hk).mp h.symm)

/-- The mixture is strictly above the round-down proxy `⌊k̄⌋²` at a non-integer
`k̄` (the top layer holds at least one cell of size `⌊k̄⌋+1`). -/
theorem floor_sq_lt_mix (k : ℝ) (hk : 0 ≤ k) (hnint : ¬ ∃ n : ℤ, k = (n : ℝ)) :
    ((⌊k⌋ : ℝ)) ^ 2 < mix k := by
  have h0 : (⌊k⌋ : ℝ) ≤ k := Int.floor_le k
  have hne : (⌊k⌋ : ℝ) ≠ k := fun h => hnint ⟨⌊k⌋, h.symm⟩
  have hpos : 0 < k - (⌊k⌋ : ℝ) := sub_pos.mpr (lt_of_le_of_ne h0 hne)
  have hfl : (0 : ℝ) ≤ (⌊k⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hk
  rw [aux_mix_eq]
  nlinarith

/-- The mixture is strictly below the round-up proxy `(⌊k̄⌋+1)²`, for every
`k̄ ≥ 0` (the top layer holds at least one cell of size `⌊k̄⌋`; at integer `k̄`
this is `k̄² < (k̄+1)²`). -/
theorem mix_lt_succ_sq (k : ℝ) (hk : 0 ≤ k) :
    mix k < ((⌊k⌋ : ℝ) + 1) ^ 2 := by
  have h1 : k < (⌊k⌋ : ℝ) + 1 := Int.lt_floor_add_one k
  have hfl : (0 : ℝ) ≤ (⌊k⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr hk
  rw [aux_mix_eq]
  nlinarith

/-- **(c), top layer** The mixture is monotone on `[0, ∞)`: raising the average
top-layer occupancy cannot lower the top-layer message count.  Piecewise the
chord has slope `2⌊k̄⌋+1 > 0`, and the chords match at the lattice points. -/
theorem mix_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : mix a ≤ mix b := by
  have hfa : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
  have hfb : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
  have ha1 : a < (⌊a⌋ : ℝ) + 1 := Int.lt_floor_add_one a
  have hna : (0 : ℝ) ≤ (⌊a⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr ha
  have hfab : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_le_floor hab
  rw [aux_mix_eq, aux_mix_eq]
  rcases eq_or_lt_of_le hfab with h | h
  · rw [h]
    have hnb : (0 : ℝ) ≤ (⌊b⌋ : ℝ) := by rw [← h]; exact hna
    nlinarith
  · have h' : (⌊a⌋ : ℝ) + 1 ≤ (⌊b⌋ : ℝ) := by exact_mod_cast h
    nlinarith

/-! ### The HSFN partial-fill proxy `C^{II}` -/

/-- `m` is the smallest integer `≥ 2` whose HSFN capacity accommodates `V`
nodes.  (Instance: `N = 2`, `V = 6`, `m = 2`, since `V_II(2,2) = 6`.) -/
def MinimalDepth (N m V : ℕ) : Prop :=
  2 ≤ m ∧ V ≤ VII N m ∧ ∀ m' : ℕ, 2 ≤ m' → V ≤ VII N m' → m ≤ m'

/-- The average number of newly allocated nodes per top-layer cell,
`k̄ = (V - V_II(N,m-1)) / N^{m-1}` (the HSFN counterpart of `eq:fill-ratio`). -/
noncomputable def kbar (N m V : ℕ) : ℝ :=
  ((V : ℝ) - (VII N (m - 1) : ℝ)) / (N : ℝ) ^ (m - 1)

/-- The HSFN partial-fill message proxy `C^{II}` of Appendix
`subsec:partial-fill`: the `(N^{m-1}-1)/(N-1)` cells of the filled lower tiers
contribute `N²` messages each, the `N^{m-1}` top-layer cells contribute the
two-point mixture `mix k̄` each, and every node receives one leader message. -/
noncomputable def CII (N m : ℕ) (k V : ℝ) : ℝ :=
  (N : ℝ) ^ 2 * (lowerCells N m : ℝ) + mix k * (N : ℝ) ^ (m - 1) + V

/-- Peeling the top tier off the counting law: `V_II(N,m+1) = V_II(N,m) + N^{m+1}`. -/
theorem aux_VII_succ (N m : ℕ) : VII N (m + 1) = VII N m + N ^ (m + 1) :=
  Finset.sum_range_succ (fun t => N ^ (t + 1)) m

/-- Lower tiers plus top layer: the `lowerCells` cells and the `N^{m-1}` top-layer
cells together carry `N · V_II(N,m)` messages at `N²` per cell. -/
theorem aux_cells_total (N j : ℕ) :
    N ^ 2 * lowerCells N (j + 1) + N ^ 2 * N ^ j = N * VII N (j + 1) := by
  have hL : N ^ 2 * lowerCells N (j + 1) + N ^ 2 * N ^ j
      = ∑ t ∈ Finset.range (j + 1), N ^ (t + 2) := by
    rw [Finset.sum_range_succ]
    simp only [lowerCells, Nat.add_sub_cancel, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun t _ => by ring
    · ring
  have hR : N * VII N (j + 1) = ∑ t ∈ Finset.range (j + 1), N ^ (t + 2) := by
    simp only [VII, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [hL, hR]

/-- At full population the average top-layer occupancy is `k̄ = N`. -/
theorem kbar_full (N m V : ℕ) (hN : 2 ≤ N) (hmin : MinimalDepth N m V)
    (hfull : V = VII N m) : kbar N m V = (N : ℝ) := by
  have hm : 2 ≤ m := hmin.1
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hV : V = VII N j + N ^ (j + 1) := by rw [hfull]; exact aux_VII_succ N j
  simp only [kbar, Nat.add_sub_cancel]
  rw [hV]
  push_cast
  field_simp
  ring

/-- **(b)** Collapse at full population: when the depth-`m` HSFN is fully
populated, `V = V_II(N,m)` and `k̄ = N`, the partial-fill proxy collapses to the
full-population proxy `C^{II} = (N+1)V` of Proposition `thm:complexity`. -/
theorem CII_full (N m V : ℕ) (hN : 2 ≤ N) (hmin : MinimalDepth N m V)
    (hfull : V = VII N m) :
    CII N m (kbar N m V) (V : ℝ) = ((N : ℝ) + 1) * (V : ℝ) := by
  have hm : 2 ≤ m := hmin.1
  have hk := kbar_full N m V hN hmin hfull
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hcells : ((N ^ 2 * lowerCells N (j + 1) + N ^ 2 * N ^ j : ℕ) : ℝ)
      = ((N * VII N (j + 1) : ℕ) : ℝ) := by rw [aux_cells_total]
  push_cast at hcells
  rw [CII, hk, mix_natCast, hfull]
  simp only [Nat.add_sub_cancel]
  linarith [hcells]

/-! ### Partial fill: `C^{II}` strictly between its two rounded proxies -/

/-- Below the full-population point the proxy is bracketed by the two proxies
obtained by rounding the average occupancy `k̄` down and up.  At a non-integer
`k̄` — i.e. whenever the top layer is *not* evenly filled — both inequalities are
strict, so the two-point mixture is not interchangeable with either rounding. -/
theorem CII_strict_between (N m : ℕ) (k V : ℝ) (hN : 1 ≤ N) (hk : 0 ≤ k)
    (hnint : ¬ ∃ n : ℤ, k = (n : ℝ)) :
    CII N m ((⌊k⌋ : ℝ)) V < CII N m k V ∧
      CII N m k V < CII N m ((⌊k⌋ : ℝ) + 1) V := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hpow : (0 : ℝ) < (N : ℝ) ^ (m - 1) := pow_pos hNpos _
  have hm1 : mix ((⌊k⌋ : ℝ)) = (⌊k⌋ : ℝ) ^ 2 := mix_intCast ⌊k⌋
  have hm2 : mix ((⌊k⌋ : ℝ) + 1) = ((⌊k⌋ : ℝ) + 1) ^ 2 := by
    have h := mix_intCast (⌊k⌋ + 1)
    push_cast at h
    exact h
  refine ⟨?_, ?_⟩
  · unfold CII
    rw [hm1]
    nlinarith [floor_sq_lt_mix k hk hnint]
  · unfold CII
    rw [hm2]
    nlinarith [mix_lt_succ_sq k hk]

/-! ### Monotonicity of the proxy in the population, at fixed depth -/

/-- The average top-layer occupancy is nonnegative once the lower tiers are
filled, `V_II(N,m-1) ≤ V`. -/
theorem kbar_nonneg (N m V : ℕ) (hN : 1 ≤ N) (hlow : VII N (m - 1) ≤ V) :
    0 ≤ kbar N m V := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hpow : (0 : ℝ) < (N : ℝ) ^ (m - 1) := pow_pos hNpos _
  have hnum : (0 : ℝ) ≤ (V : ℝ) - (VII N (m - 1) : ℝ) := by
    have h : ((VII N (m - 1) : ℕ) : ℝ) ≤ (V : ℝ) := by exact_mod_cast hlow
    linarith
  exact div_nonneg hnum hpow.le

/-- At fixed depth the average top-layer occupancy is monotone in the
population. -/
theorem kbar_mono (N m V V' : ℕ) (hN : 1 ≤ N) (hVV : V ≤ V') :
    kbar N m V ≤ kbar N m V' := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hpow : (0 : ℝ) < (N : ℝ) ^ (m - 1) := pow_pos hNpos _
  have hV : (V : ℝ) ≤ (V' : ℝ) := by exact_mod_cast hVV
  unfold kbar
  gcongr

/-- **(c)** Monotonicity of the proxy in the population at fixed depth: with the
lower tiers filled (`V_II(N,m-1) ≤ V`), more participants cannot decrease
`C^{II}`.  The depth `m` is held fixed here; the statement therefore covers a
fill of one and the same top layer, not a population increase that forces a
deeper network. -/
theorem CII_mono_V (N m V V' : ℕ) (hN : 1 ≤ N) (hlow : VII N (m - 1) ≤ V)
    (hVV : V ≤ V') :
    CII N m (kbar N m V) (V : ℝ) ≤ CII N m (kbar N m V') (V' : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hpow : (0 : ℝ) < (N : ℝ) ^ (m - 1) := pow_pos hNpos _
  have hmix := mix_mono (kbar_nonneg N m V hN hlow) (kbar_mono N m V V' hN hVV)
  have hV : (V : ℝ) ≤ (V' : ℝ) := by exact_mod_cast hVV
  unfold CII
  nlinarith [mul_le_mul_of_nonneg_right hmix hpow.le]

/-! ### Form-independence of the full-population proxy -/

/-- The HSFN population is a whole number of cells. -/
theorem N_dvd_VII (N m : ℕ) : N ∣ VII N m :=
  Finset.dvd_sum fun t _ => dvd_pow_self N (Nat.succ_ne_zero t)

/-- **(c)** At full population the HSFN partial-fill proxy `C^{II}` agrees with
the dense-variant proxy `HSFN.Dense.message_proxy` evaluated on the same
population: `V/N` cells at `N²` messages each plus one leader message per node. -/
theorem CII_full_eq_dense_proxy (N m V : ℕ) (hN : 2 ≤ N) (hmin : MinimalDepth N m V)
    (hfull : V = VII N m) :
    CII N m (kbar N m V) (V : ℝ) = ((V / N * N ^ 2 + V : ℕ) : ℝ) := by
  have hdvd : N ∣ V := by rw [hfull]; exact N_dvd_VII N m
  have h2 := HSFN.Dense.message_proxy N V (by omega) hdvd
  rw [CII_full N m V hN hmin hfull, h2]
  push_cast
  ring

/-- **(c)** Form-independence of the full-population proxy (Section
`subsec:complexity`): a fully populated HSFN of depth `m` and a dense variant of
any depth `m'` are both charged `(N+1)` times their own node count, so only the
partial-fill correction distinguishes the two forms. -/
theorem full_population_form_independent (N m m' V : ℕ) (hN : 2 ≤ N)
    (hmin : MinimalDepth N m V) (hfull : V = VII N m) :
    CII N m (kbar N m V) (V : ℝ) = ((N : ℝ) + 1) * (V : ℝ) ∧
      HSFN.Dense.V N m' / N * N ^ 2 + HSFN.Dense.V N m'
        = (N + 1) * HSFN.Dense.V N m' :=
  ⟨CII_full N m V hN hmin hfull,
    HSFN.Dense.message_proxy N (HSFN.Dense.V N m') (by omega) (HSFN.Dense.N_dvd_V N m')⟩

/-- `MinimalDepth` is satisfiable, so the hypotheses of `kbar_full`, `CII_full`
and `CII_full_eq_dense_proxy` are not contradictory: for `N = 2` the depth-`2`
HSFN holds `V_II(2,2) = 6` nodes and `2` is minimal for it. -/
theorem minimalDepth_witness : MinimalDepth 2 2 6 ∧ (6 : ℕ) = VII 2 2 :=
  ⟨⟨le_refl 2, by decide, fun _ h1 _ => h1⟩, by decide⟩


/-! ### A partial-fill witness inside the paper's regime `N ≥ 3` -/

/-- `MinimalDepth` is satisfiable inside the paper's standing regime `N ≥ 3`
(Section `sec:prelim`): with `N = 3` the depth-`3` HSFN holds
`V_II(3,3) = 39 ≥ 25` nodes while `V_II(3,2) = 12 < 25`, so `3` is the minimal
depth for a population of `25`. -/
theorem minimalDepth_witness_three : MinimalDepth 3 3 25 := by
  refine ⟨by norm_num, by decide, ?_⟩
  intro m' h2 hle
  rcases Nat.lt_or_ge m' 3 with h | h
  · have hm : m' = 2 := by omega
    subst hm
    exact absurd hle (by decide)
  · exact h

/-- The witness is a *proper* partial fill: `25 < V_II(3,3) = 39`, and the lower
tiers are filled, `V_II(3,2) = 12 ≤ 25`. -/
theorem witness_partial : VII 3 2 ≤ 25 ∧ (25 : ℕ) < VII 3 3 := by
  constructor <;> decide

/-- The average top-layer occupancy at the witness: `k̄ = (25-12)/9 = 13/9`, so
the `9` top-layer cells of the depth-`3` HSFN receive `13` new nodes. -/
theorem kbar_witness : kbar 3 3 25 = 13 / 9 := by
  have h : VII 3 2 = 12 := by decide
  simp only [kbar, h]
  norm_num

/-- The witness occupancy is **not** an integer, so the fill is genuinely
uneven: `13` nodes cannot be spread over `9` cells with all cells equal. -/
theorem kbar_witness_not_int : ¬ ∃ n : ℤ, kbar 3 3 25 = (n : ℝ) := by
  rintro ⟨n, hn⟩
  rw [kbar_witness] at hn
  have h9 : (13 : ℝ) = 9 * (n : ℝ) := by
    field_simp at hn
    linarith
  have hz : (13 : ℤ) = 9 * n := by exact_mod_cast h9
  omega

/-- The witness occupancy is strictly below the full-population value `k̄ = N`
of `kbar_full`: `13/9 < 3`. -/
theorem kbar_witness_lt_full : kbar 3 3 25 < (3 : ℝ) := by
  rw [kbar_witness]
  norm_num

theorem floor_kbar_witness : ⌊kbar 3 3 25⌋ = 1 := by
  rw [kbar_witness]
  norm_num

/-- **(b)** At the witness the correction term is strictly active: the two-point
mixture `mix k̄ = 7/3` exceeds the balanced-fill cost `k̄² = 169/81`.  This is
`mix_gt_sq_of_not_int` instantiated at a non-integer `k̄` in the paper's
regime — the inequality of `mix_ge_sq` is strict here, not an equality. -/
theorem mix_witness_gt_sq : (kbar 3 3 25) ^ 2 < mix (kbar 3 3 25) :=
  mix_gt_sq_of_not_int _ (by rw [kbar_witness]; norm_num) kbar_witness_not_int

/-- The mixture at the witness, in closed form: `mix (13/9) = 7/3`. -/
theorem mix_witness : mix (kbar 3 3 25) = 7 / 3 := by
  rw [kbar_witness]
  simp only [mix]
  norm_num

/-- The partial-fill proxy at the witness: `C^{II}(3,3,25) = 82`. -/
theorem CII_witness_value : CII 3 3 (kbar 3 3 25) (25 : ℝ) = 82 := by
  have hl : lowerCells 3 3 = 4 := by decide
  simp only [CII, hl, mix_witness]
  norm_num

/-- The round-down proxy at the witness (all `9` top-layer cells charged
`⌊k̄⌋² = 1`): `70`. -/
theorem CII_witness_floor : CII 3 3 (1 : ℝ) (25 : ℝ) = 70 := by
  have hl : lowerCells 3 3 = 4 := by decide
  have hm : mix (1 : ℝ) = 1 := by
    have h := mix_natCast 1
    push_cast at h
    rw [h]; norm_num
  simp only [CII, hl, hm]
  norm_num

/-- The round-up proxy at the witness (all `9` top-layer cells charged
`(⌊k̄⌋+1)² = 4`): `97`. -/
theorem CII_witness_ceil : CII 3 3 (2 : ℝ) (25 : ℝ) = 97 := by
  have hl : lowerCells 3 3 = 4 := by decide
  have hm : mix (2 : ℝ) = 4 := by
    have h := mix_natCast 2
    push_cast at h
    rw [h]; norm_num
  simp only [CII, hl, hm]
  norm_num

/-- **(b)** The partial-fill proxy at the witness lies *strictly between* its two
rounded proxies, `70 < 82 < 97`: at `N = 3`, `m = 3`, `V = 25` neither rounding
of `k̄` reproduces `C^{II}`, so the two-point mixture carries real content in the
paper's parameter regime.  (Numerically this is `CII_strict_between` at
`⌊k̄⌋ = 1`; the proof here is the arithmetic of the three closed values.) -/
theorem CII_witness_strict_between :
    CII 3 3 (1 : ℝ) (25 : ℝ) < CII 3 3 (kbar 3 3 25) (25 : ℝ) ∧
      CII 3 3 (kbar 3 3 25) (25 : ℝ) < CII 3 3 (2 : ℝ) (25 : ℝ) := by
  rw [CII_witness_value, CII_witness_floor, CII_witness_ceil]
  norm_num

/-- At the witness the partial-fill proxy is *below* the full-population form
`(N+1)V = 100`, not above it: `82 < 100`.  A partially filled top layer is
charged less than `N²` per cell, so no inequality of the shape
`C^{II} > (N+1)V` can hold at partial fill. -/
theorem CII_witness_lt_full_form :
    CII 3 3 (kbar 3 3 25) (25 : ℝ) < ((3 : ℝ) + 1) * 25 := by
  rw [CII_witness_value]
  norm_num

end HSFN.PartialFill
