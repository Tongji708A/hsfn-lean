/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Basic
import Hsfnlean.Degree
import Hsfnlean.Distance
import Hsfnlean.Greedy
import Hsfnlean.Locator
import Hsfnlean.IFS
import Hsfnlean.Threshold
import Hsfnlean.KpiAffine

/-!
# The running example `N = 5`, `m = 3`: a regression witness

Paper: "A Mathematical Theory of Hyper-Simplex Fractal Network" (R260409).
The paper threads one instance through the whole text, "the smallest instance
faithful to the general case": `N = 5`, `m = 3`, and prints concrete numbers
for it in half a dozen places.

**What this file is.** It proves *no general theorem*.  Every statement below
is either (i) a general result of another module applied at `N = 5`, `m = 3`,
or (ii) a `decide`-level check of a concrete object of the running example (a
named address, a hop, a configuration) that no general theorem mentions.  Its
purpose is regression: if a definition in `Hsfnlean.Basic`, `Hsfnlean.Degree`,
`Hsfnlean.Distance`, `Hsfnlean.Greedy`, `Hsfnlean.Locator`, `Hsfnlean.IFS`,
`Hsfnlean.Threshold`, `Hsfnlean.Calculus` (reached through `Hsfnlean.KpiAffine`)
or `Hsfnlean.KpiAffine` is changed in a way that no longer
reproduces the numbers the paper prints, this file stops compiling.  A reader
who wants to know *why* a general claim holds must go to the module named
against it, not here.

## What is checked, and which general result it instantiates

| here | paper | general result (module) |
| --- | --- | --- |
| `card_addr`, `card_addr_sum` (`155` nodes) | `prop:addr-bij`, `thm:unified-count` | `HSFN.Addr.card_eq_sum` (`Hsfnlean.Basic`) |
| `card_tier_one/two/three` (`5 / 25 / 125`) | `cor:count-II` | `HSFN.Addr.card_tier` (`Hsfnlean.Basic`) |
| `card_mem_cells` (each cell holds `5`) | `cor:count-II` | `HSFN.card_cell` (`Hsfnlean.Degree`) |
| `card_cells` (`31` cells), `cellsOfTier`, `card_cells_split`, `card_cells_one_five_twentyfive` (`1 + 5 + 25`) | `cor:count-II` and the running example after it | double counting over `HSFN.card_cell`; the sibling-class bookkeeping is done here, since no module defines the cell set |
| `dist_le_five`, `exists_dist_eq_five`, `diam_eq_five`, `dist_a000_a444` (diameter `5 = 2m - 1`) | `thm:distance-II(iii)` | `HSFN.dist_le_diam`, `HSFN.exists_dist_eq_diam`, `HSFN.dist_eq_dval` (`Hsfnlean.Distance`) |
| `lcp_a420_a431`, `not_prefixComp_a420_a431`, `dval_a420_a431`, `dist_a420_a431` (`d(420,431) = 3`) | `thm:distance-II(i)` | `HSFN.dist_eq_dval` (`Hsfnlean.Distance`) |
| `route_a420_a431`, `tree_route_a420_a431` | the paper's two routes | none: a `decide` check of the concrete hops |
| `greedy_hop_a420/a42/a43` (the rule picks `420 → 42 → 43 → 431`) | `thm:distance-II(ii)` | `HSFN.greedyW`, `HSFN.greedyStep_adj`, `HSFN.dval_greedyStep` (`Hsfnlean.Greedy`) |
| `degree_of_tier_one/two/three`, `degree_a4/a42/a420` (`9 / 10 / 5`) | `thm:deg-II(i)`, Fig. "Decision support" | `HSFN.degree_tier_one`, `HSFN.degree_interior`, `HSFN.degree_leaf` (`Hsfnlean.Degree`) |
| `locatorBits_a431`, `locBits_a431`, `locMax_five_three` (`14` bits), `card_le_two_pow_locator` | `prop:locator-II(a)` | `HSFN.Locator.locBits`, `locBits_example`, `card_le_two_pow_locMax` (`Hsfnlean.Locator`) |
| `locator_ratio_five`, `logb_five_gt`, `locator_ratio_lt_four_thirds` (`3 / log₂ 5 < 4/3`) | `prop:locator-II(b)` and the comparison with the dense limit | `HSFN.Locator.locator_ratio_tendsto` (`Hsfnlean.Locator`); the dense limit `4/3` is `HSFN.TierLocator.ratioLimit_five` (`Hsfnlean.TierLocator`, not imported here), quoted here only as the numeral it is compared against |
| `moranDim_five`, `moran_five`, `moranDim_five_lower/upper` (`2.32 < log₂ 5 < 2.325`) | `thm:dim-II`, `subsec:dimension` | `HSFN.IFS.moranDim`, `HSFN.IFS.moran_moranDim` (`Hsfnlean.IFS`) |
| `q0_five` (`80^{-1/2}`), `q0_eight` (`1120^{-1/3}`) | `thm:security` and the threshold table | `HSFN.q0` (`Hsfnlean.Threshold`); only the closed forms are evaluated |
| `xRun`, `graft_xRun`, `kappa_*`, `graft_card_Sl_xRun`, `graft_L_xRun` (the graft `42 → 13`) | `prop:kpi-affine` and its running example | `HSFN.Calc.graft` (`Hsfnlean.Calculus`), `HSFN.Kpi.kappa`, `HSFN.Kpi.graft_card_Sl`, `HSFN.Kpi.graft_L` (`Hsfnlean.KpiAffine`) |
| `a423_ne_a433`, `not_adj_a423_a433` | `rem:coincident` at `42` | none: a `decide` check; see the gap list below |

The only non-instantiation reasoning in the file is the cell bookkeeping of
section (b) — `card_cells` and `cellsOfTier` — because no module defines the
set of cells; and the elementary `log`/`clog` arithmetic used to turn the
general statements into the paper's numerals (`clog_five`, `clog_three`,
`logb_five_gt`, the two `moranDim_five_*` brackets).

## Honest gaps: running-example claims *not* checked here

* The *shape* of the cell tree.  `card_cells_split` proves the counts
  `1 + 5 + 25` and `cells_eq_union` proves the three tiers exhaust the cells
  disjointly, but no parent map on cells is defined, so "the complete `5`-ary
  tree of depth `2`" is verified only as a count, not as a tree.
* `tree_route_a420_a431` records the four-hop spawn-tree route as a chain of
  clause-(P) links; its minimality *among clause-(P) walks* is not asserted,
  since no imported module defines the spawn-tree subgraph.
* Co-location.  `rem:coincident` says `ι(423) = ι(433)` and `ι(420) = ι(42)`;
  no module defines an address-to-simplex embedding `ι` (`Hsfnlean.IFS` has the
  corner maps but no address map, `Hsfnlean.Spacetime` uses word coordinates),
  so only distinctness and non-adjacency are checked.
* The wire format.  `Hsfnlean.Locator` treats the locator as a *bit budget*
  (widths plus capacity lemmas), so the padded word `42␣` over the six-letter
  alphabet `{0,…,4,␣}` is not formalized here or anywhere.
* Decimal approximations.  `≈ 1.29`, `≈ 2.322`, `≈ 0.0963`, `≈ 0.1118` are
  paper prose.  Only `log₂ 5` is bracketed (`2.32 … 2.325`) and only the
  comparison `3 / log₂ 5 < 4/3` is proved; `q0 5` and `q0 8` are given in
  closed form and are *not* bounded numerically (that needs `rpow` estimates).
* The dense-variant degree classes `29 / 49 / 9` of the same figure are not
  checked: `Hsfnlean.Dense` counts nodes and edges of the dense variant but
  proves no degree formula to instantiate.
* The graft instance is fully occupied (`μ = Sl`), a specialization of the
  paper's "all anchors and the members of `C(42)` are occupied"; the paper's
  deployed-*cell*-graph boundary counts (`σ_x(42) = 1`, two edges cut, one
  created) are not checked, because `Hsfnlean.KpiAffine` builds only the
  slot-level link count `L`, which an equal-tier graft leaves invariant
  (`graft_L_xRun`).  The node-level "five uplinks cut, five created" is
  checked in the form `moved_cell`: the five members of `C(42)` are renamed
  onto the five members of `C(13)`.
-/
namespace HSFN
namespace RunningExample

open Finset

/-! ## The instance and its named addresses -/

/-- The tier-1 node `4`. -/
def a4 : Addr 5 3 := ⟨[4], by decide, by decide⟩

/-- The tier-2 node `42` (the anchor of the paper's worked spawn event). -/
def a42 : Addr 5 3 := ⟨[4, 2], by decide, by decide⟩

/-- The tier-2 node `43`, the sibling of `42` used by the lateral hop. -/
def a43 : Addr 5 3 := ⟨[4, 3], by decide, by decide⟩

/-- The tier-3 node `420`. -/
def a420 : Addr 5 3 := ⟨[4, 2, 0], by decide, by decide⟩

/-- The tier-3 node `431`. -/
def a431 : Addr 5 3 := ⟨[4, 3, 1], by decide, by decide⟩

/-- The tier-3 slot `423` of the event anchored at `42`: the slot pointing at
the peer `43`. -/
def a423 : Addr 5 3 := ⟨[4, 2, 3], by decide, by decide⟩

/-- The tier-3 slot `433` of the matching event anchored at `43`: the slot
pointing back at the peer `42`. -/
def a433 : Addr 5 3 := ⟨[4, 3, 3], by decide, by decide⟩

/-- The tier-3 node `000`, one end of a diametral pair. -/
def a000 : Addr 5 3 := ⟨[0, 0, 0], by decide, by decide⟩

/-- The tier-3 node `444`, the other end of that diametral pair. -/
def a444 : Addr 5 3 := ⟨[4, 4, 4], by decide, by decide⟩

theorem tier_a4 : a4.tier = 1 := by decide

theorem tier_a42 : a42.tier = 2 := by decide

theorem tier_a43 : a43.tier = 2 := by decide

theorem tier_a420 : a420.tier = 3 := by decide

theorem tier_a431 : a431.tier = 3 := by decide

/-! ## (a) Node counts (`thm:unified-count`, `prop:addr-bij`, `cor:count-II`)

"The tiers hold `5`, `25` and `125` nodes, `155` in all."
-/

/-- The paper's node total: `G_II(5,3)` has `5 + 25 + 125 = 155` nodes. -/
theorem card_addr : Fintype.card (Addr 5 3) = 155 := by
  rw [Addr.card_eq_sum 5 3]
  norm_num [Finset.sum_range_succ]

/-- The summed counting law at the running example. -/
theorem card_addr_sum : Fintype.card (Addr 5 3) = ∑ t ∈ Finset.range 3, 5 ^ (t + 1) :=
  Addr.card_eq_sum 5 3

/-- Tier 1 holds `5` nodes. -/
theorem card_tier_one : Fintype.card { a : Addr 5 3 // a.tier = 1 } = 5 := by
  have h := Addr.card_tier 5 3 1 (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- Tier 2 holds `25` nodes. -/
theorem card_tier_two : Fintype.card { a : Addr 5 3 // a.tier = 2 } = 25 := by
  have h := Addr.card_tier 5 3 2 (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- Tier 3 holds `125` nodes. -/
theorem card_tier_three : Fintype.card { a : Addr 5 3 // a.tier = 3 } = 125 := by
  have h := Addr.card_tier 5 3 3 (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-! ## (b) Cell count: `31` cells

The cells are the sibling classes; each holds `N = 5` nodes, and the `155`
nodes fall into `1 + 5 + 25 = 31` of them (the complete `5`-ary tree of
depth `2`).
-/

/-- The set of cells of `G_II(5,3)`: the sibling classes of the addresses. -/
def cells : Finset (Finset (Addr 5 3)) :=
  Finset.univ.image fun u => Finset.univ.filter fun v => Sib u v

/-- Every cell holds exactly `N = 5` nodes (`card_cell` at `N = 5`). -/
theorem card_mem_cells : ∀ c ∈ cells, c.card = 5 := by
  intro c hc
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hc
  exact card_cell u

/-- Sibling classes with a common member coincide (`Sib` is an equivalence). -/
private theorem aux_cell_eq_of_sib {u w : Addr 5 3} (h : Sib w u) :
    (Finset.univ.filter fun v => Sib u v) = Finset.univ.filter fun v => Sib w v := by
  ext v
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h1 => ⟨h.1.trans h1.1, h.2.trans h1.2⟩,
         fun h1 => ⟨h.1.symm.trans h1.1, h.2.symm.trans h1.2⟩⟩

/-- The fiber of the "cell of" map over a cell `c` is `c` itself. -/
private theorem aux_fiber_eq (w : Addr 5 3) :
    (Finset.univ.filter fun u : Addr 5 3 =>
        (Finset.univ.filter fun v => Sib u v) = Finset.univ.filter fun v => Sib w v)
      = Finset.univ.filter fun v => Sib w v := by
  ext u
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    have hu : u ∈ Finset.univ.filter fun v => Sib u v := by
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨rfl, rfl⟩
    rw [h] at hu
    simpa only [mem_filter, mem_univ, true_and] using hu
  · intro h
    exact aux_cell_eq_of_sib h

/-- The paper's cell count: `G_II(5,3)` has `31` cells. -/
theorem card_cells : cells.card = 31 := by
  have hfib : (Finset.univ : Finset (Addr 5 3)).card
      = ∑ c ∈ cells, (Finset.univ.filter fun u : Addr 5 3 =>
          (Finset.univ.filter fun v => Sib u v) = c).card :=
    Finset.card_eq_sum_card_image _ _
  have hfiber : ∀ c ∈ cells, (Finset.univ.filter fun u : Addr 5 3 =>
      (Finset.univ.filter fun v => Sib u v) = c).card = 5 := by
    intro c hc
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hc
    rw [aux_fiber_eq w, card_cell w]
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, card_addr] at hfib
  omega

/-- The paper's arithmetic, "`155` nodes in `31` cells": the cells, each of
size `5`, account for all the nodes. -/
theorem cells_times_size : cells.card * 5 = Fintype.card (Addr 5 3) := by
  rw [card_cells, card_addr]

/-- The paper's own derivation of the cell total ("dividing by the cell size
`N` gives the cell total"). -/
theorem card_addr_div : Fintype.card (Addr 5 3) / 5 = 31 := by
  rw [card_addr]

/-- The cell total as the sum of the per-tier cell counts `N^{t-1}`
(`cor:count-II`): `1 + 5 + 25 = 31`.  The per-tier split itself is
`card_cells_split` below. -/
theorem cell_count_sum : cells.card = ∑ t ∈ Finset.range 3, 5 ^ t := by
  rw [card_cells]
  norm_num [Finset.sum_range_succ]

/-! ### The per-tier cell split `1 + 5 + 25`

The paper says the `31` cells "form the complete `5`-ary tree of depth `2`".
The cells carry a tier (all members of a cell share one, by clause (S)), and
the tier-`t` cells are counted by `N^{t-1}`.
-/

/-- The cells whose members sit at tier `t`. -/
def cellsOfTier (t : ℕ) : Finset (Finset (Addr 5 3)) :=
  (Finset.univ.filter fun a : Addr 5 3 => a.tier = t).image
    fun u => Finset.univ.filter fun v => Sib u v

/-- Siblings share a tier, so a cell has a well-defined tier. -/
theorem tier_of_sib {u v : Addr 5 3} (h : Sib u v) : v.tier = u.tier := h.1.symm

/-- Inside the tier-`t` addresses, the fiber of the "cell of" map over a cell
is again that whole cell. -/
private theorem aux_fiber_tier_eq (t : ℕ) (w : Addr 5 3) (hw : w.tier = t) :
    ((Finset.univ.filter fun a : Addr 5 3 => a.tier = t).filter fun u =>
        (Finset.univ.filter fun v => Sib u v) = Finset.univ.filter fun v => Sib w v)
      = Finset.univ.filter fun v => Sib w v := by
  ext u
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩
    have hu : u ∈ Finset.univ.filter fun v => Sib u v := by
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨rfl, rfl⟩
    rw [h] at hu
    simpa only [mem_filter, mem_univ, true_and] using hu
  · intro h
    exact ⟨by rw [← hw]; exact tier_of_sib h, aux_cell_eq_of_sib h⟩

/-- The tier-`t` cells, each of size `5`, partition the `5 ^ t` tier-`t`
addresses. -/
theorem card_cellsOfTier_mul (t : ℕ) (h1 : 1 ≤ t) (h2 : t ≤ 3) :
    (cellsOfTier t).card * 5 = 5 ^ t := by
  have hcard : (Finset.univ.filter fun a : Addr 5 3 => a.tier = t).card = 5 ^ t := by
    rw [← Fintype.card_subtype]
    exact Addr.card_tier 5 3 t h1 h2
  have hfib : (Finset.univ.filter fun a : Addr 5 3 => a.tier = t).card
      = ∑ c ∈ (Finset.univ.filter fun a : Addr 5 3 => a.tier = t).image
            (fun u => Finset.univ.filter fun v => Sib u v),
          ((Finset.univ.filter fun a : Addr 5 3 => a.tier = t).filter fun u =>
            (Finset.univ.filter fun v => Sib u v) = c).card :=
    Finset.card_eq_sum_card_image _ _
  have hfiber : ∀ c ∈ (Finset.univ.filter fun a : Addr 5 3 => a.tier = t).image
      (fun u => Finset.univ.filter fun v => Sib u v),
      ((Finset.univ.filter fun a : Addr 5 3 => a.tier = t).filter fun u =>
        (Finset.univ.filter fun v => Sib u v) = c).card = 5 := by
    intro c hc
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
    rw [mem_filter] at hw
    rw [aux_fiber_tier_eq t w hw.2, card_cell w]
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, hcard] at hfib
  unfold cellsOfTier
  omega

/-- Tier 1 is a single cell, the initial simplex. -/
theorem card_cellsOfTier_one : (cellsOfTier 1).card = 1 := by
  have h := card_cellsOfTier_mul 1 (by norm_num) (by norm_num)
  norm_num at h
  omega

/-- Tier 2 carries `5` cells, one per tier-1 anchor. -/
theorem card_cellsOfTier_two : (cellsOfTier 2).card = 5 := by
  have h := card_cellsOfTier_mul 2 (by norm_num) (by norm_num)
  norm_num at h
  omega

/-- Tier 3 carries `25` cells, one per tier-2 anchor. -/
theorem card_cellsOfTier_three : (cellsOfTier 3).card = 25 := by
  have h := card_cellsOfTier_mul 3 (by norm_num) (by norm_num)
  norm_num at h
  omega

/-- Every tier-`t` cell is a cell. -/
theorem cellsOfTier_subset (t : ℕ) : cellsOfTier t ⊆ cells := by
  intro c hc
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hc
  exact Finset.mem_image_of_mem _ (Finset.mem_univ w)

/-- Cells of different tiers are different: a cell determines the tier of its
members. -/
theorem cellsOfTier_disjoint {t t' : ℕ} (h : t ≠ t') :
    Disjoint (cellsOfTier t) (cellsOfTier t') := by
  rw [Finset.disjoint_left]
  intro c hc hc'
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨w', hw', hcc⟩ := Finset.mem_image.mp hc'
  rw [mem_filter] at hw hw'
  have hmem : w' ∈ Finset.univ.filter fun v => Sib w' v := by
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨rfl, rfl⟩
  rw [hcc] at hmem
  simp only [mem_filter, mem_univ, true_and] at hmem
  exact h (hw.2 ▸ hw'.2 ▸ (tier_of_sib hmem).symm)

/-- The `31` cells split by tier as `1 + 5 + 25`: every cell has a tier
between `1` and `m = 3`. -/
theorem cells_eq_union :
    cells = cellsOfTier 1 ∪ cellsOfTier 2 ∪ cellsOfTier 3 := by
  apply Finset.Subset.antisymm
  · intro c hc
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hc
    have h1 := Addr.one_le_tier w
    have h2 := Addr.tier_le w
    have hmem : ∀ t, w.tier = t →
        (Finset.univ.filter fun v => Sib w v) ∈ cellsOfTier t := by
      intro t ht
      exact Finset.mem_image_of_mem _ (by simp only [mem_filter, mem_univ, true_and]; exact ht)
    have hcases : w.tier = 1 ∨ w.tier = 2 ∨ w.tier = 3 := by omega
    rcases hcases with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hmem 1 h))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hmem 2 h))
    · exact Finset.mem_union_right _ (hmem 3 h)
  · exact Finset.union_subset (Finset.union_subset (cellsOfTier_subset 1)
      (cellsOfTier_subset 2)) (cellsOfTier_subset 3)

/-- The paper's tree shape, in counts: the `31` cells are `1 + 5 + 25`, the
node counts of a complete `5`-ary tree of depth `2`. -/
theorem card_cells_split :
    cells.card = (cellsOfTier 1).card + (cellsOfTier 2).card + (cellsOfTier 3).card := by
  rw [cells_eq_union]
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint (cellsOfTier_disjoint (by norm_num))]
  · exact Finset.disjoint_union_left.mpr
      ⟨cellsOfTier_disjoint (by norm_num), cellsOfTier_disjoint (by norm_num)⟩

/-- The split in the paper's numerals: `31 = 1 + 5 + 25`. -/
theorem card_cells_one_five_twentyfive : cells.card = 1 + 5 + 25 := by
  rw [card_cells_split, card_cellsOfTier_one, card_cellsOfTier_two,
    card_cellsOfTier_three]

/-! ## (c) Diameter `2m - 1 = 5` (`thm:distance-II(iii)`) -/

/-- No pair of addresses is farther apart than `2m - 1 = 5`
(`dist_le_diam` at `N = 5`, `m = 3`). -/
theorem dist_le_five (u v : Addr 5 3) : (graph 5 3).dist u v ≤ 5 := by
  have h := dist_le_diam u v
  omega

/-- The bound `5` is attained (`exists_dist_eq_diam` at `N = 5`, `m = 3`). -/
theorem exists_dist_eq_five : ∃ u v : Addr 5 3, (graph 5 3).dist u v = 5 := by
  obtain ⟨u, v, h⟩ := exists_dist_eq_diam (N := 5) (m := 3) (by norm_num) (by norm_num)
  exact ⟨u, v, by omega⟩

/-- The address type of the running example is inhabited. -/
private theorem aux_nonempty : Nonempty (Addr 5 3) := ⟨a4⟩

/-- `G_II(5,3)` is connected, hence its extended diameter is finite. -/
private theorem aux_ediam_ne_top : (graph 5 3).ediam ≠ ⊤ := by
  haveI := aux_nonempty
  have hconn : (graph 5 3).Connected := by
    rw [SimpleGraph.connected_iff]
    exact ⟨fun u v => graph_connected u v, aux_nonempty⟩
  exact SimpleGraph.connected_iff_ediam_ne_top.mp hconn

/-- **The diameter is exactly `2m - 1 = 5`** at the running example. -/
theorem diam_eq_five : (graph 5 3).diam = 5 := by
  haveI := aux_nonempty
  refine le_antisymm ?_ ?_
  · obtain ⟨u, v, huv⟩ := SimpleGraph.exists_dist_eq_diam (G := graph 5 3)
    rw [← huv]
    exact dist_le_five u v
  · obtain ⟨u, v, huv⟩ := exists_dist_eq_five
    calc (5 : ℕ) = (graph 5 3).dist u v := huv.symm
      _ ≤ (graph 5 3).diam := SimpleGraph.dist_le_diam aux_ediam_ne_top

/-- The paper's diametral pair: `u = 000`, `v = 444` have `ℓ = 0` and
`d = 5 = 2m - 1`. -/
theorem lcp_a000_a444 : lcp a000.1 a444.1 = 0 := by decide

theorem not_prefixComp_a000_a444 : ¬ PrefixComp a000 a444 := by decide

theorem dist_a000_a444 : (graph 5 3).dist a000 a444 = 5 := by
  rw [dist_eq_dval]
  decide

/-! ## (d) The worked pair `d(420, 431) = 3` (`thm:distance-II(i),(ii)`)

"The longest common prefix is `4`, giving `ℓ = 1`.  Since the pair is not
prefix-comparable, `d(u,v) = 3 + 3 - 2 - 1 = 3`."
-/

/-- The longest common prefix of `420` and `431` is the single digit `4`. -/
theorem lcp_a420_a431 : lcp a420.1 a431.1 = 1 := by decide

/-- The pair is not prefix-comparable, so the second clause of the metric
applies. -/
theorem not_prefixComp_a420_a431 : ¬ PrefixComp a420 a431 := by decide

/-- The candidate distance: `t_u + t_v - (2ℓ + 1) = 3 + 3 - (2·1 + 1) = 3`. -/
theorem dval_a420_a431 : dval a420 a431 = 3 := by decide

/-- **The worked pair**: `d(420, 431) = 3`. -/
theorem dist_a420_a431 : (graph 5 3).dist a420 a431 = 3 := by
  rw [dist_eq_dval]
  exact dval_a420_a431

/-- The greedy route of the paper, with the clause used at each hop: ascend
`420 → 42` by clause (P), hop laterally `42 → 43` by clause (S) inside
`cell(4)`, descend `43 → 431` by clause (P); three hops, matching the
distance `d(420,431) = 3`. -/
theorem route_a420_a431 :
    ((graph 5 3).Adj a420 a42 ∧ Par a420 a42) ∧
      ((graph 5 3).Adj a42 a43 ∧ Sib a42 a43) ∧
      ((graph 5 3).Adj a43 a431 ∧ Par a43 a431) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

/-- The spawn-tree route `420 — 42 — 4 — 43 — 431` of the paper: four hops,
every one of them a clause-(P) link, passing through the shared anchor `4`.
Against `dist_a420_a431` this records that the sibling link `42 — 43`
replaces the two hops through `4`.  (Minimality of this route among
clause-(P) walks is *not* asserted: the spawn-tree subgraph is not defined
in the imported modules.) -/
theorem tree_route_a420_a431 :
    ((graph 5 3).Adj a420 a42 ∧ Par a420 a42) ∧
      ((graph 5 3).Adj a42 a4 ∧ Par a42 a4) ∧
      ((graph 5 3).Adj a4 a43 ∧ Par a4 a43) ∧
      ((graph 5 3).Adj a43 a431 ∧ Par a43 a431) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

/-! ## (e) Degree classes `9 / 10 / 5` (`thm:deg-II(i)`) -/

/-- Tier-1 nodes have degree `2N - 1 = 9`. -/
theorem degree_of_tier_one (u : Addr 5 3) (h : u.tier = 1) :
    (graph 5 3).degree u = 9 := by
  have hd := degree_tier_one u (by norm_num) h
  omega

/-- Tier-2 (interior) nodes have degree `2N = 10`. -/
theorem degree_of_tier_two (u : Addr 5 3) (h : u.tier = 2) :
    (graph 5 3).degree u = 10 := by
  have hd := degree_interior u (by omega) (by omega)
  omega

/-- Tier-3 (leaf) nodes have degree `N = 5`. -/
theorem degree_of_tier_three (u : Addr 5 3) (h : u.tier = 3) :
    (graph 5 3).degree u = 5 :=
  degree_leaf u (by norm_num) h

theorem degree_a4 : (graph 5 3).degree a4 = 9 :=
  degree_of_tier_one a4 tier_a4

theorem degree_a42 : (graph 5 3).degree a42 = 10 :=
  degree_of_tier_two a42 tier_a42

theorem degree_a420 : (graph 5 3).degree a420 = 5 :=
  degree_of_tier_three a420 tier_a420

/-! ## (f) Greedy routing selects exactly those hops (`thm:distance-II(ii)`)

`Hsfnlean.Greedy` turns the greedy rule into the function `HSFN.greedyW` on
words and proves in general that each of its hops is an edge which lowers the
distance by one (`greedyStep_adj`, `dval_greedyStep`).  Evaluating it on the
paper's pair shows that the route of `route_a420_a431` is the one the rule
actually picks.
-/

/-- Hop 1 of the paper's route: at `420`, bound for `431`, the rule ascends
to the anchor `42`. -/
theorem greedy_hop_a420 : greedyW a431.1 a420.1 = a42.1 := by decide

/-- Hop 2: at `42` the rule hops laterally to the sibling `43`. -/
theorem greedy_hop_a42 : greedyW a431.1 a42.1 = a43.1 := by decide

/-- Hop 3: at `43` the rule descends onto the destination `431`. -/
theorem greedy_hop_a43 : greedyW a431.1 a43.1 = a431.1 := by decide

/-! ## (g) Locator length (`prop:locator-II`)

`⟨N, t, a_1 ⋯ a_t⟩` costs `⌈log₂ N⌉ + ⌈log₂ m⌉ + t⌈log₂ N⌉` bits.
-/

/-- The length-prefixed locator of a tier-`t` address of `F(N,m)`, in bits:
`⌈log₂ N⌉` for the cell-size field, `⌈log₂ m⌉` for the tier field and
`⌈log₂ N⌉` per digit. -/
def locatorBits (N m t : ℕ) : ℕ := Nat.clog 2 N + Nat.clog 2 m + t * Nat.clog 2 N

theorem clog_five : Nat.clog 2 5 = 3 := by
  have h1 : Nat.clog 2 5 ≤ 3 := (Nat.clog_le_iff_le_pow (by norm_num)).mpr (by norm_num)
  have h2 : ¬ Nat.clog 2 5 ≤ 2 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    norm_num
  omega

theorem clog_three : Nat.clog 2 3 = 2 := by
  have h1 : Nat.clog 2 3 ≤ 2 := (Nat.clog_le_iff_le_pow (by norm_num)).mpr (by norm_num)
  have h2 : ¬ Nat.clog 2 3 ≤ 1 := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    norm_num
  omega

/-- The paper's locator arithmetic: `⟨5, 3, 431⟩` costs `3 + 2 + 9 = 14` bits. -/
theorem locatorBits_a431 : locatorBits 5 3 a431.tier = 14 := by
  rw [tier_a431]
  unfold locatorBits
  rw [clog_five, clog_three]

/-- The paper's worst case: at most `⌈log₂ m⌉ + (m+1)⌈log₂ N⌉ = 14` bits for
any address of `F(5,3)`, attained at `t = m` (witness `a431`). -/
theorem locatorBits_le (u : Addr 5 3) : locatorBits 5 3 u.tier ≤ 14 := by
  have h := Addr.tier_le u
  unfold locatorBits
  rw [clog_five, clog_three]
  omega

/-- The locator width used here is the `HSFN.Locator.locBits` of
`Hsfnlean.Locator` at `N = 5`, `m = 3`; the general module also supplies the
capacity lemmas that make it a locator *length* and not just an expression. -/
theorem locatorBits_eq_locBits (t : ℕ) : locatorBits 5 3 t = Locator.locBits 5 3 t := rfl

/-- The paper's `14` bits, obtained from the general
`HSFN.Locator.locBits_example` rather than recomputed. -/
theorem locBits_a431 : Locator.locBits 5 3 a431.tier = 14 := by
  rw [tier_a431]
  exact Locator.locBits_example

/-- The worst case `⌈log₂ 3⌉ + 4⌈log₂ 5⌉ = 14` bits
(`HSFN.Locator.locMax` at the running example). -/
theorem locMax_five_three : Locator.locMax 5 3 = 14 := by
  unfold Locator.locMax
  rw [clog_five, clog_three]

/-- The locator really addresses the running example: `155` nodes against
`2 ^ 14 = 16384` codewords (`HSFN.Locator.card_le_two_pow_locMax`). -/
theorem card_le_two_pow_locator : Fintype.card (Addr 5 3) ≤ 2 ^ 14 := by
  have h := Locator.card_le_two_pow_locMax 5 3 (by norm_num)
  rwa [locMax_five_three] at h

/-- The paper's asymptotic locator ratio at `N = 5`: as the depth grows, the
locator length divided by the counting bound `log₂ V_II(5,m)` tends to
`3 / log₂ 5 ≈ 1.29` (`HSFN.Locator.locator_ratio_tendsto` at `N = 5`). -/
theorem locator_ratio_five :
    Filter.Tendsto
      (fun m : ℕ => (Locator.locMax 5 m : ℝ) / Real.logb 2 (Fintype.card (Addr 5 m)))
      Filter.atTop (nhds (3 / Real.logb 2 5)) := by
  have h := Locator.locator_ratio_tendsto 5 (by norm_num)
  rw [clog_five] at h
  norm_num at h
  exact h

/-- `log₂ 5 > 9/4`, the arithmetic behind `3 / log₂ 5 ≈ 1.292`
(from `5 ^ 4 = 625 > 512 = 2 ^ 9`). -/
theorem logb_five_gt : (9 : ℝ) / 4 < Real.logb 2 5 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have key : Real.log ((2 : ℝ) ^ (9 : ℕ)) < Real.log ((5 : ℝ) ^ (4 : ℕ)) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at key
  rw [Real.logb, lt_div_iff₀ hlog2]
  push_cast at key
  linarith

/-- The paper's comparison: the HSFN locator ratio `3 / log₂ 5` at the running
example is strictly below the dense-variant tier-locator limit `4/3`
(`HSFN.ratioLimit_five` of `Hsfnlean.TierLocator`). -/
theorem locator_ratio_lt_four_thirds : 3 / Real.logb 2 5 < 4 / 3 := by
  have hpos : (0 : ℝ) < Real.logb 2 5 := by linarith [logb_five_gt]
  have h : 3 / Real.logb 2 5 < 3 / ((9 : ℝ) / 4) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) logb_five_gt
  norm_num at h
  exact h

/-! ## (h) The dimension `log₂ 5 ≈ 2.322` (`thm:dim-II`, `subsec:dimension`)

The seed of the running example is the `4`-simplex, so the attractor of the
corner IFS has similarity dimension `log₂ 5`, strictly between the values
`log₂ 4 = 2` and `log₂ 8 = 3` of the neighboring powers of two.
-/

/-- The similarity dimension at `N = 5` (`HSFN.IFS.moranDim`). -/
theorem moranDim_five : IFS.moranDim 5 = Real.logb 2 5 := by
  rw [IFS.moranDim]
  norm_num

/-- Moran's equation at the running example: `5 · (1/2) ^ (log₂ 5) = 1`
(`HSFN.IFS.moran_moranDim` at `N = 5`). -/
theorem moran_five : ((5 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ IFS.moranDim 5 = 1 :=
  IFS.moran_moranDim (by norm_num)

/-- `2.32 < log₂ 5` (from `5 ^ 25 > 2 ^ 58`). -/
theorem moranDim_five_lower : (2.32 : ℝ) < IFS.moranDim 5 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have key : Real.log ((2 : ℝ) ^ (58 : ℕ)) < Real.log ((5 : ℝ) ^ (25 : ℕ)) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at key
  rw [moranDim_five, Real.logb, lt_div_iff₀ hlog2]
  push_cast at key
  linarith

/-- `log₂ 5 < 2.325` (from `5 ^ 40 < 2 ^ 93`). -/
theorem moranDim_five_upper : IFS.moranDim 5 < 2.325 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have key : Real.log ((5 : ℝ) ^ (40 : ℕ)) < Real.log ((2 : ℝ) ^ (93 : ℕ)) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at key
  rw [moranDim_five, Real.logb, div_lt_iff₀ hlog2]
  push_cast at key
  linarith

/-! ## (i) The two consensus thresholds at `N = 5` (`thm:security`)

`Hsfnlean.Threshold` defines `q₀(b) = [2^k C(b,k)]^{-1/(k-1)}` with
`k = ⌈b/2⌉`.  The paper's table entry for the running example uses the HSFN
branching `b = N = 5` and the dense-variant branching `b = 2N - 2 = 8`.
-/

/-- `q₀(5,5) = 80^{-1/2}` on the HSFN: `k = 3`, `2³·C(5,3) = 80`. -/
theorem q0_five : q0 5 = (80 : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hk : half 5 = 3 := rfl
  have hc : Nat.choose 5 3 = 10 := rfl
  rw [q0, hk, hc]
  norm_num

/-- `q₀(5,8) = 1120^{-1/3}` on the dense variant: `k = 4`,
`2⁴·C(8,4) = 1120`. -/
theorem q0_eight : q0 8 = (1120 : ℝ) ^ (-(1 : ℝ) / 3) := by
  have hk : half 8 = 4 := rfl
  have hc : Nat.choose 8 4 = 70 := rfl
  rw [q0, hk, hc]
  norm_num

/-! ## (j) The graft `42 → 13` of the running example (`prop:kpi-affine`)

The paper's configuration is `D = {ε, 1, 4, 42, 44}`, in which `25` slots host
`5` cells; every slot is occupied, so the graft `42 → 13` is applicable.  The
operations calculus of `Hsfnlean.Calculus` and the indicators of
`Hsfnlean.KpiAffine` are used unchanged; only the instance is new.
-/

open Calc in
/-- The paper's deployed-cell set `D = {ε, 1, 4, 42, 44}`. -/
def dRun : Finset (Word 5) := {[], [1], [4], [4, 2], [4, 4]}

open Calc in
/-- The paper's configuration: `D` as above, every slot occupied, nothing
decommissioned. -/
def xRun : Config 5 3 := ⟨dRun, dRun.biUnion cellW, ∅⟩

open Calc in
/-- The configuration after the graft `42 → 13`, spelled out by the
substitution of `HSFN.Calc.graft`. -/
def yRun : Config 5 3 :=
  ⟨xRun.D.image (subst false [4, 2] [1, 3]),
    xRun.μ.image (subst true [4, 2] [1, 3]),
    xRun.ζ.image (subst true [4, 2] [1, 3])⟩

/-- The configuration is well-formed. -/
theorem xRun_wf : xRun.WF := by
  unfold Calc.Config.WF
  decide

/-- "`25` slots host `5` cells." -/
theorem card_D_xRun : xRun.D.card = 5 := by decide

theorem card_Sl_xRun : xRun.Sl.card = 25 := by decide

/-- The graft `42 → 13` is applicable at `xRun`, with result `yRun`. -/
theorem graft_xRun : Calc.graft [4, 2] [1, 3] xRun = some yRun := by
  unfold Calc.graft
  split
  · rfl
  · rename_i hcond
    exact absurd (by decide) hcond

/-- The moved set is the single cell `42` with its five members, renamed onto
the five members of `13`. -/
theorem moved_cell :
    (Calc.cellW ([4, 2] : Calc.Word 5)).image (Calc.subst true [4, 2] [1, 3])
      = Calc.cellW [1, 3] := by decide

/-- The designated duplicate `420` of `42` becomes the designated duplicate
`130` of `13`. -/
theorem moved_duplicate :
    Calc.subst true ([4, 2] : Calc.Word 5) [1, 3] [4, 2, 0] = [1, 3, 0] := by decide

/-- The deployed cells after the graft: `D' = {ε, 1, 4, 13, 44}`. -/
theorem D_yRun : yRun.D = ({[], [1], [4], [1, 3], [4, 4]} : Finset (Calc.Word 5)) := by decide

/-- The paper's two-bin transfer of the tier-2 anchoring histogram,
`κ(4) : 2 → 1`. -/
theorem kappa_four_before : Kpi.kappa xRun [4] = 2 := by decide

theorem kappa_four_after : Kpi.kappa yRun [4] = 1 := by decide

/-- And `κ(1) : 0 → 1`. -/
theorem kappa_one_before : Kpi.kappa xRun [1] = 0 := by decide

theorem kappa_one_after : Kpi.kappa yRun [1] = 1 := by decide

/-- Every anchoring bin other than `4` and `1` is unchanged, here at the two
remaining tier-2 anchors and at the root. -/
theorem kappa_unchanged :
    Kpi.kappa yRun [] = Kpi.kappa xRun [] ∧
      Kpi.kappa yRun [0] = Kpi.kappa xRun [0] ∧
      Kpi.kappa yRun [2] = Kpi.kappa xRun [2] ∧
      Kpi.kappa yRun [3] = Kpi.kappa xRun [3] := by decide

/-- "Every other indicator of `prop:kpi-affine` is unchanged": the equal-tier
graft preserves the slot count and the provisioned link count
(`HSFN.Kpi.graft_card_Sl`, `HSFN.Kpi.graft_L` at this instance). -/
theorem graft_card_Sl_xRun : yRun.Sl.card = xRun.Sl.card :=
  Kpi.graft_card_Sl (a := [4, 2]) (b := [1, 3]) xRun_wf rfl graft_xRun

theorem graft_L_xRun : Kpi.L yRun = Kpi.L xRun :=
  Kpi.graft_L (a := [4, 2]) (b := [1, 3]) xRun_wf rfl graft_xRun

/-! ## (k) The one-event picture at `42` (`rem:coincident`)

The event at `42` deploys the slot `423` toward its peer `43`, and the matching
event at `43` deploys `433` toward `42`.  The paper calls these two *co-located,
distinct and non-adjacent*.  Co-location is geometry — it needs the embedding
`ι` into the simplex, which no imported module defines — but the graph-theoretic
half is checkable here.
-/

/-- The two slots of the coincident pair are distinct. -/
theorem a423_ne_a433 : a423 ≠ a433 := by decide

/-- They are non-adjacent: neither siblings (their anchors differ) nor in a
parent-child relation. -/
theorem not_adj_a423_a433 : ¬ (graph 5 3).Adj a423 a433 := by decide

/-- Both sit at tier `3`. -/
theorem tier_a423 : a423.tier = 3 := by decide

theorem tier_a433 : a433.tier = 3 := by decide


end RunningExample
end HSFN
