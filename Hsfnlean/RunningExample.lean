/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Basic
import Hsfnlean.Degree
import Hsfnlean.Distance

/-!
# The running example `N = 5`, `m = 3`

Paper: "A Mathematical Theory of Hyper-Simplex Fractal Network" (R260409).
The paper threads one instance through the whole text, "the smallest instance
faithful to the general case": `N = 5`, `m = 3`.  This file instantiates the
general theorems of the *static* layer at that instance and checks the numbers
the paper prints there.

Paper labels covered:
* `thm:unified-count` / `prop:addr-bij` / `cor:count-II` — the tiers hold
  `5`, `25`, `125` nodes, `155` in all, in `31` cells (running example after
  `cor:count-II`).
* `thm:distance-II` — `d(420, 431) = 3` through the longest common prefix
  `4` (`ℓ = 1`), the greedy route `420 → 42 → 43 → 431`, and the diameter
  `d(000, 444) = 5 = 2m - 1` (running example after `prop:locator-II`).
* `thm:deg-II(i)` — the degree classes `9 / 10 / 5` at tiers `1 / 2 / 3`
  (Fig. "Decision support", HSFN column).
* `prop:locator-II` — the locator `⟨5, 3, 431⟩` costs `14` bits.

Everything here is instantiation plus arithmetic, except `card_cells`, which
needs the sibling classes to be counted.

Not formalized here (the paper's running example says more than this file
proves, and the rest lives in other modules or nowhere yet):
* "the `31` cells form the complete `5`-ary tree of depth `2`" — only the
  cell *total* `31` is proved (`card_cells`, `cell_count_sum`); the tree
  structure on the cells, and the per-tier split `1 + 5 + 25`, are not.
* "*Greedy* routing ascends `420 → 42` …" — `route_a420_a431` exhibits the
  three hops with the adjacency clause each one uses, and `dist_a420_a431`
  shows `3` hops is optimal, but that the greedy rule of `thm:distance-II(ii)`
  *selects* these hops is not asserted (`Hsfnlean.Greedy` is not imported).
  Likewise `tree_route_a420_a431` records the four-hop spawn-tree route only
  as a clause-(P) walk; its minimality among clause-(P) walks is not asserted,
  since the spawn-tree subgraph is not defined in the imported modules.
* the locator: `locatorBits` is the paper's formula written down here as a
  definition, not derived from an encoding; the asymptotic ratio
  `3 / log₂ 5 ≈ 1.29` and the padded wire word `42␣` are not formalized.
* the other running-example passages of the paper are out of scope for this
  file: the Hausdorff dimension `log₂ 5 ≈ 2.322` (`subsec:dimension`), the
  one-event spawn/co-location example at `42` (`rem:coincident`), the graft
  `42 → 13` (`prop:kpi-affine`), the thresholds `q₀(5,5)`, `q₀(5,8)`, and the
  dense-variant degree classes `29 / 49 / 9`.
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
(`cor:count-II`): `1 + 5 + 25 = 31`.  Only the total is asserted here; the
per-tier split itself is not (it would need the tier of a cell). -/
theorem cell_count_sum : cells.card = ∑ t ∈ Finset.range 3, 5 ^ t := by
  rw [card_cells]
  norm_num [Finset.sum_range_succ]

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

/-! ## Locator length (`prop:locator-II`)

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

end RunningExample
end HSFN
