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
  (convexity of `x ↦ x²` on the two lattice points bracketing `k̄`);
* `CII_full` — collapse at full population, `k̄ = N` and `C^{II} = (N+1)V`;
* `full_population_form_independent` — the same value is produced by the dense
  form `HSFN.Dense.message_proxy`, so the full-population proxy is
  form-independent (the claim of Section `subsec:complexity`).

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
  used only as a hypothesis, and it is satisfiable (`minimalDepth_witness`), so
  the theorems taking it are not vacuous; `CII_full` in fact needs only `2 ≤ m`.
* `CII` takes the occupancy `k` and the population `V` as independent real
  arguments.  Nothing forces `k = kbar N m V` at the definition; the theorems
  below instantiate it that way, but a partial-fill statement for `k̄ < N` (a
  strict inequality `C^{II} > (N+1)V`, say) is not proved.
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

end HSFN.PartialFill
