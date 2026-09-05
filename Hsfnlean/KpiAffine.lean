/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Calculus

/-!
# Affine indicators and `O(1)` maintenance (Proposition prop:kpi-affine)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

For a configuration `x = (D, μ, ζ)` of `F(N,m)` the paper introduces the *tier profile*
`{M0_t, o_t, h_t}`: `M0_t` is the number of deployed tier-`t` cells (the `w ∈ D` with
`|w| = t-1`), `o_t(k)` the number of them with exactly `k` occupied members, and `h_t(k)`
the number of them with exactly `k` deployed child cells. This file formalizes the parts of
Proposition prop:kpi-affine that are counting statements about `D`, `μ` and the slot set,
together with the `O(1)`-maintenance clause and the equal-tier invariance of
Theorem thm:graft-iso(iii):

* item (i), slot and participant counts: `card_Sl`, `card_Sl_profile` (`|Sl(x)| = N ∑_t M0_t`)
  and `card_mu_sum`, `card_mu_profile` (`|μ| = ∑_t M1(o_t)`), with the histogram-to-moment
  identity `M1_o` of the paragraph "Histograms are equivalent to the moments";
* item (ii), provisioned links: the edge inventory of the state graph `G(x)` is re-derived
  here from the two-clause law `Calc.AdjW` restricted to `Sl(x)` — `adjPairs_eq` splits the
  adjacent slot pairs into sibling pairs and uplink pairs, `card_sibPairs` and `card_upPairs`
  count them, and `card_L`, `card_L_profile` give
  `L(x) = C(N,2)|D| + N(|D|-1) = (C(N,2)+N) ∑_t M0_t - N`;
* item (iii), message proxies: `Cfull_eq`, `Cfull_profile` for the full-occupancy proxy
  `(N+1) N ∑_t M0_t`, plus the occupancy-refined proxy `Cload` with its histogram form
  `Cload_hist` and its full-occupancy value `Cload_full`;
* the maintenance clause: `card_join`, `card_leave`, `card_spawn`, `card_retract` and
  `card_graft` show that each bookkeeping letter moves `|D|` and `|μ|` by a constant, and
  `occ_join`, `occ_leave`, `kappa_spawn`, `kappa_retract` show that the corresponding
  histogram edit touches exactly one cell's bin, which is what "affine indicators are
  maintainable in constant time" means. `occ_kappa_spawn_new` is the paper's remaining
  spawn/retract clause, the fresh cell arriving at the bin `(o_{|a|+1}(0), h_{|a|+1}(0))`, and
  `disable_D_mu`, `enable_D_mu` are its clause that `disable` and `enable` move no bin at all.
  `graft_card_Sl`, `graft_L`, `graft_Cfull` are the *indicator* half of the equal-tier
  invariance of Theorem thm:graft-iso(iii).

**Not formalized here.** Item (iv), the anchor overlay: neither the deployed-cell graph
`Γ(x)`, nor its identification with the subgraph of `G(x)` induced on the anchors, nor the
link count `∑_t ∑_k C(k,2) h_t(k) + ∑_{t≥3} M0_t` appears below; only the anchoring degree
`kappa` is defined, and the anchoring histograms `h_t` are not. The *histogram* half of the
equal-tier graft clause is likewise absent: the paper's `± 1` two-bin transfer
`κ(pre a) -= 1`, `κ(pre b) += 1` in `h_{|a|}` (Theorem thm:graft-iso(iii), and the graft
entry of the maintenance sentence) is not stated, nor is its cancellation when
`pre(a) = pre(b)`, nor the anchor-overlay boundary term `σ_{x'}(b) - σ_x(a)` of
Lemma lem:edge-cut. What is stated for an equal-tier graft is only that `|D|`, `|μ|`,
`|Sl|`, `L` and `Cfull` are unchanged. Also absent: the balanced-fill
specialization of `Cload` to the partial-fill proxy and to eq:general-complexity, the `O(m)`
cost of a cross-tier graft, the `permute` letter, and everything about reliability
(Proposition prop:rel-exact). Decommissioned slots `ζ` enter none of the indicators below
(they occur only inside `Config.WF` and inside the generator guards of `Calculus.lean`),
matching the paper's remark that they are vacant and anchor nothing. The `O(1)` claim itself
is not formalized as a cost bound: what is proved is that each generator's effect on the
indicators is a fixed constant read off the letter, not a re-derivation from the state.
-/

namespace HSFN

namespace Kpi

open Calc Calc.Config

set_option linter.unusedVariables false

variable {N m : ℕ}

/-! ## Word-level scaffolding

`Calculus.lean` keeps its membership characterisations private, so the two we need are
restated here. -/

private theorem aux_mem_cellW {v w : Word N} :
    v ∈ cellW w ↔ v ≠ [] ∧ v.dropLast = w := by
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨d, _, rfl⟩
    simp
  · rintro ⟨hv, rfl⟩
    exact Finset.mem_image.mpr
      ⟨v.getLast hv, Finset.mem_univ _, List.dropLast_append_getLast hv⟩

private theorem aux_mem_Sl {x : Config N m} {w : Word N} :
    w ∈ x.Sl ↔ w ≠ [] ∧ w.dropLast ∈ x.D := by
  simp only [Config.Sl, Finset.mem_biUnion, aux_mem_cellW]
  aesop

private theorem aux_dropLast_ne {w : Word N} (hw : w ≠ []) : w.dropLast ≠ w := by
  intro he
  have h1 := congrArg List.length he
  have h2 := List.length_pos_of_ne_nil hw
  simp only [List.length_dropLast] at h1
  omega

/-! ## Cell atomicity: the cells of `D` are `N`-element and pairwise disjoint -/

/-- Each cell has exactly `N` member slots. -/
theorem card_cellW (w : Word N) : (cellW w).card = N := by
  have hinj : Function.Injective (fun d : Fin N => w ++ [d]) := by
    intro d e hde
    simpa using hde
  simp only [cellW, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- `cellW w` determines `w`: every member slot of the cell at `w` has `w` as its `dropLast`.
This is why distinct deployed cells are slot-disjoint. -/
theorem cellW_disjoint {u v : Word N} (h : u ≠ v) : Disjoint (cellW u) (cellW v) := by
  refine Finset.disjoint_left.mpr ?_
  intro s hu hv
  exact h (((aux_mem_cellW.mp hu).2).symm.trans (aux_mem_cellW.mp hv).2)

/-! ## The tier profile -/

/-- The tier-`t` deployed cells: the `w ∈ D` with `|w| = t - 1` (tiers are one-based, so the
seed cell `[]` is the unique tier-1 cell). -/
def tierCells (x : Config N m) (t : ℕ) : Finset (Word N) :=
  x.D.filter fun w => w.length + 1 = t

/-- `M0_t`, the number of deployed tier-`t` cells. -/
def M0 (x : Config N m) (t : ℕ) : ℕ := (tierCells x t).card

/-- The number of occupied members of the cell at `w`, i.e. `|C(w) ∩ μ|`. -/
def occ (x : Config N m) (w : Word N) : ℕ := ((cellW w).filter fun s => s ∈ x.μ).card

/-- The occupancy histogram `o_t(k)`: the number of tier-`t` cells with exactly `k` occupied
members. -/
def o (x : Config N m) (t k : ℕ) : ℕ := ((tierCells x t).filter fun w => occ x w = k).card

/-- The anchoring degree `κ(w) = |{d : wd ∈ D}|`, the number of deployed child cells of `w`. -/
def kappa (x : Config N m) (w : Word N) : ℕ := ((cellW w).filter fun s => s ∈ x.D).card

/-- The tiers `1, …, m` partition the deployed cells: this is the bridge between the
cell-indexed sums below and the profile-indexed displays of the paper. -/
theorem sum_tierCells {x : Config N m} (hx : x.WF) (f : Word N → ℕ) :
    ∑ t ∈ Finset.Icc 1 m, ∑ w ∈ tierCells x t, f w = ∑ w ∈ x.D, f w := by
  simp only [tierCells]
  exact Finset.sum_fiberwise_of_maps_to
    (g := fun w : Word N => w.length + 1)
    (fun w hw => Finset.mem_Icc.mpr ⟨Nat.le_add_left 1 w.length, hx.2.1 w hw⟩) f

/-- `∑_t M0_t = |D|`. -/
theorem sum_M0 {x : Config N m} (hx : x.WF) :
    ∑ t ∈ Finset.Icc 1 m, M0 x t = x.D.card := by
  simp only [M0, Finset.card_eq_sum_ones]
  exact sum_tierCells hx (fun _ => 1)

/-- The occupancy of a cell never exceeds `N`, so the histograms live on `{0, …, N}`. -/
private theorem aux_occ_le (x : Config N m) (w : Word N) : occ x w ≤ N := by
  calc occ x w ≤ (cellW w).card := Finset.card_filter_le _ _
    _ = N := card_cellW w

/-- The generic histogram-to-moment identity. `M1_o` and `Cload_hist` are the instances
`g = id` and `g k = k² + k`. -/
private theorem aux_hist_sum (x : Config N m) (t : ℕ) (g : ℕ → ℕ) :
    ∑ k ∈ Finset.range (N + 1), g k * o x t k = ∑ w ∈ tierCells x t, g (occ x w) := by
  have hmaps : ∀ w ∈ tierCells x t, occ x w ∈ Finset.range (N + 1) := fun w _ =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (aux_occ_le x w))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun w => g (occ x w))]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : ∀ w ∈ (tierCells x t).filter (fun w => occ x w = k), g (occ x w) = g k :=
    fun w hw => by rw [(Finset.mem_filter.mp hw).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
  simp only [o]
  exact Nat.mul_comm _ _

/-- "Histograms are equivalent to the moments": the first moment `M1(o_t)` of the occupancy
histogram is the total occupancy of the tier-`t` cells. -/
theorem M1_o (x : Config N m) (t : ℕ) :
    ∑ k ∈ Finset.range (N + 1), k * o x t k = ∑ w ∈ tierCells x t, occ x w :=
  aux_hist_sum x t (fun k => k)

/-! ## (i) Slot and participant counts -/

/-- Slot count: `|Sl(x)| = N |D|` (cell atomicity). -/
theorem card_Sl {x : Config N m} (hx : x.WF) : x.Sl.card = N * x.D.card := by
  have hdis : (↑x.D : Set (Word N)).PairwiseDisjoint (fun w : Word N => cellW w) :=
    fun u _ v _ huv => cellW_disjoint huv
  show (x.D.biUnion cellW).card = N * x.D.card
  rw [Finset.card_biUnion hdis,
    Finset.sum_congr rfl (fun w (_ : w ∈ x.D) => card_cellW w),
    Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- Slot count in profile form: `|Sl(x)| = N ∑_t M0_t`. -/
theorem card_Sl_profile {x : Config N m} (hx : x.WF) :
    x.Sl.card = N * ∑ t ∈ Finset.Icc 1 m, M0 x t := by
  rw [card_Sl hx, sum_M0 hx]

/-- Participant count, cell by cell: `|μ| = ∑_{w ∈ D} |C(w) ∩ μ|`. Every occupied slot lies in
exactly one deployed cell. -/
theorem card_mu_sum {x : Config N m} (hx : x.WF) : x.μ.card = ∑ w ∈ x.D, occ x w := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun s : Word N => s.dropLast) (t := x.D)
    (fun s hs => (aux_mem_Sl.mp (hx.2.2.2.1 hs)).2)]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [occ]
  congr 1
  ext v
  simp only [Finset.mem_filter, aux_mem_cellW]
  constructor
  · rintro ⟨hv, rfl⟩
    exact ⟨⟨(aux_mem_Sl.mp (hx.2.2.2.1 hv)).1, rfl⟩, hv⟩
  · rintro ⟨⟨hvn, rfl⟩, hv⟩
    exact ⟨hv, rfl⟩

/-- Participant count in profile form: `|μ| = ∑_t M1(o_t)`. -/
theorem card_mu_profile {x : Config N m} (hx : x.WF) :
    x.μ.card = ∑ t ∈ Finset.Icc 1 m, ∑ k ∈ Finset.range (N + 1), k * o x t k := by
  rw [card_mu_sum hx, ← sum_tierCells hx (fun w => occ x w)]
  exact (Finset.sum_congr rfl fun t _ => M1_o x t).symm

/-! ## (ii) Provisioned links: the edge inventory of the state graph `G(x)`

`G(x)` is the graph on `Sl(x)` whose adjacency is the two-clause law `Calc.AdjW` of
Theorem thm:adjacency-II restricted to the deployed slots. Pairs are counted as *ordered*
pairs in `adjPairs`, `sibPairs`, `upPairs`; `L` halves the total. -/

instance instDecidableAdjW (u v : Word N) : Decidable (AdjW u v) := by
  unfold AdjW; infer_instance

/-- The ordered adjacent slot pairs of `G(x)`. -/
def adjPairs (x : Config N m) : Finset (Word N × Word N) :=
  (x.Sl ×ˢ x.Sl).filter fun p => AdjW p.1 p.2

/-- The ordered sibling pairs: clause (S), two distinct slots of the same cell. -/
def sibPairs (x : Config N m) : Finset (Word N × Word N) :=
  (x.Sl ×ˢ x.Sl).filter fun p =>
    p.1 ≠ p.2 ∧ p.1.length = p.2.length ∧ p.1.dropLast = p.2.dropLast

/-- The ordered uplink pairs `(anchor, member)`: clause (P), a deployed non-seed cell `u`
together with one of the `N` members of the cell it anchors. -/
def upPairs (x : Config N m) : Finset (Word N × Word N) :=
  (x.Sl ×ˢ x.Sl).filter fun p => p.2.length = p.1.length + 1 ∧ p.2.dropLast = p.1

/-- `L(x)`, the number of provisioned links: unordered adjacent pairs of slots. -/
def L (x : Config N m) : ℕ := (adjPairs x).card / 2

/-- The edge inventory: every adjacent slot pair is a sibling pair or an uplink pair (in one
of its two orientations). -/
theorem adjPairs_eq (x : Config N m) :
    adjPairs x = sibPairs x ∪ (upPairs x ∪ (upPairs x).image Prod.swap) := by
  ext p
  constructor
  · intro hp
    rw [adjPairs, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hu, hv⟩, hne, hcase⟩ := hp
    rcases hcase with ⟨hl, hd⟩ | ⟨hl, hd⟩ | ⟨hl, hd⟩
    · refine Finset.mem_union_left _ ?_
      rw [sibPairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hu, hv⟩, hne, hl, hd⟩
    · refine Finset.mem_union_right _ (Finset.mem_union_left _ ?_)
      rw [upPairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hu, hv⟩, hl, hd⟩
    · refine Finset.mem_union_right _ (Finset.mem_union_right _ ?_)
      refine Finset.mem_image.mpr ⟨(p.2, p.1), ?_, rfl⟩
      rw [upPairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hv, hu⟩, hl, hd⟩
  · intro hp
    rw [adjPairs, Finset.mem_filter, Finset.mem_product]
    rcases Finset.mem_union.mp hp with hs | hp
    · rw [sibPairs, Finset.mem_filter, Finset.mem_product] at hs
      exact ⟨hs.1, hs.2.1, Or.inl ⟨hs.2.2.1, hs.2.2.2⟩⟩
    · rcases Finset.mem_union.mp hp with hu | hu
      · rw [upPairs, Finset.mem_filter, Finset.mem_product] at hu
        refine ⟨hu.1, ?_, Or.inr (Or.inl ⟨hu.2.1, hu.2.2⟩)⟩
        intro he
        rw [he] at hu
        omega
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
        rw [upPairs, Finset.mem_filter, Finset.mem_product] at hq
        simp only [Prod.fst_swap, Prod.snd_swap]
        refine ⟨⟨hq.1.2, hq.1.1⟩, ?_, Or.inr (Or.inr ⟨hq.2.1, hq.2.2⟩)⟩
        intro he
        rw [he] at hq
        omega

private theorem aux_len_sibPairs {x : Config N m} {p : Word N × Word N}
    (h : p ∈ sibPairs x) : p.1.length = p.2.length := by
  rw [sibPairs, Finset.mem_filter] at h
  exact h.2.2.1

private theorem aux_len_upPairs {x : Config N m} {p : Word N × Word N}
    (h : p ∈ upPairs x) : p.2.length = p.1.length + 1 := by
  rw [upPairs, Finset.mem_filter] at h
  exact h.2.1

/-- The three parts of the inventory are separated by the length pattern of the pair. -/
private theorem aux_disj_sib (x : Config N m) :
    Disjoint (sibPairs x) (upPairs x ∪ (upPairs x).image Prod.swap) := by
  refine Finset.disjoint_left.mpr ?_
  intro p hp hq
  have h1 := aux_len_sibPairs hp
  rcases Finset.mem_union.mp hq with h | h
  · have h2 := aux_len_upPairs h
    omega
  · obtain ⟨q, hqm, rfl⟩ := Finset.mem_image.mp h
    have h2 := aux_len_upPairs hqm
    simp only [Prod.fst_swap, Prod.snd_swap] at h1
    omega

private theorem aux_disj_up (x : Config N m) :
    Disjoint (upPairs x) ((upPairs x).image Prod.swap) := by
  refine Finset.disjoint_left.mpr ?_
  intro p hp hq
  have h1 := aux_len_upPairs hp
  obtain ⟨q, hqm, rfl⟩ := Finset.mem_image.mp hq
  have h2 := aux_len_upPairs hqm
  simp only [Prod.fst_swap, Prod.snd_swap] at h1
  omega

/-- `2 C(n,2) + n = n²`, the arithmetic behind "each cell contributes `C(N,2)` sibling
links". -/
private theorem aux_two_choose_two (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h1 : (k + 1).choose 2 = k.choose 1 + k.choose 2 := Nat.choose_succ_succ k 1
    have h2 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    rw [h1, Nat.choose_one_right, h2, ← ih]
    ring

/-- The sibling pairs are the off-diagonals of the deployed cells. -/
private theorem aux_sibPairs_eq (x : Config N m) :
    sibPairs x = x.D.biUnion (fun w => (cellW w).offDiag) := by
  ext p
  simp only [sibPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
    Finset.mem_offDiag, aux_mem_cellW, aux_mem_Sl]
  constructor
  · rintro ⟨⟨⟨hun, hup⟩, hvn, hvp⟩, hne, hlen, hdrop⟩
    exact ⟨p.1.dropLast, hup, ⟨hun, rfl⟩, ⟨hvn, hdrop.symm⟩, hne⟩
  · rintro ⟨w, hw, ⟨hun, rfl⟩, ⟨hvn, hvd⟩, hne⟩
    refine ⟨⟨⟨hun, hw⟩, hvn, by rw [hvd]; exact hw⟩, hne, ?_, hvd.symm⟩
    have h1 := List.length_pos_of_ne_nil hun
    have h2 := List.length_pos_of_ne_nil hvn
    have h3 := congrArg List.length hvd
    simp only [List.length_dropLast] at h3
    omega

private theorem aux_card_sibPairs (x : Config N m) :
    (sibPairs x).card = 2 * N.choose 2 * x.D.card := by
  have hdis : (↑x.D : Set (Word N)).PairwiseDisjoint (fun w : Word N => (cellW w).offDiag) := by
    intro u _ v _ huv
    refine Finset.disjoint_left.mpr ?_
    intro p hp hq
    exact Finset.disjoint_left.mp (cellW_disjoint huv) (Finset.mem_offDiag.mp hp).1
      (Finset.mem_offDiag.mp hq).1
  have hcard : ∀ w ∈ x.D, ((cellW w).offDiag).card = 2 * N.choose 2 := by
    intro w _
    rw [Finset.offDiag_card, card_cellW]
    exact Nat.sub_eq_of_eq_add (aux_two_choose_two N).symm
  rw [aux_sibPairs_eq, Finset.card_biUnion hdis, Finset.sum_congr rfl hcard,
    Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- Each of the `|D|` deployed cells contributes `C(N,2)` sibling links, i.e. `N(N-1)` ordered
sibling pairs. -/
theorem card_sibPairs {x : Config N m} (hx : x.WF) :
    (sibPairs x).card = 2 * N.choose 2 * x.D.card :=
  aux_card_sibPairs x

/-- The uplink pairs are the anchor/member incidences of the non-seed deployed cells. -/
private theorem aux_upPairs_eq {x : Config N m} (hx : x.WF) :
    upPairs x = (x.D.erase []).biUnion (fun u => ({u} : Finset (Word N)) ×ˢ cellW u) := by
  ext p
  simp only [upPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
    Finset.mem_erase, Finset.mem_singleton, aux_mem_cellW, aux_mem_Sl]
  constructor
  · rintro ⟨⟨⟨hun, hup⟩, hvn, hvp⟩, hlen, hd⟩
    exact ⟨p.1, ⟨hun, by rw [← hd]; exact hvp⟩, rfl, hvn, hd⟩
  · rintro ⟨w, ⟨hwn, hwD⟩, rfl, hvn, hvd⟩
    refine ⟨⟨⟨hwn, hx.2.2.1 _ hwD hwn⟩, hvn, by rw [hvd]; exact hwD⟩, ?_, hvd⟩
    have h1 := List.length_pos_of_ne_nil hvn
    have h2 := congrArg List.length hvd
    simp only [List.length_dropLast] at h2
    omega

/-- Each of the `|D| - 1` non-seed deployed cells contributes `N` uplinks. -/
theorem card_upPairs {x : Config N m} (hx : x.WF) :
    (upPairs x).card = N * (x.D.card - 1) := by
  have hdis : (↑(x.D.erase []) : Set (Word N)).PairwiseDisjoint
      (fun u : Word N => ({u} : Finset (Word N)) ×ˢ cellW u) := by
    intro u _ v _ huv
    refine Finset.disjoint_left.mpr ?_
    intro p hp hq
    have h1 := (Finset.mem_product.mp hp).1
    have h2 := (Finset.mem_product.mp hq).1
    rw [Finset.mem_singleton] at h1 h2
    exact huv (h1.symm.trans h2)
  have hcard : ∀ u ∈ x.D.erase ([] : Word N),
      ((({u} : Finset (Word N)) ×ˢ cellW u).card) = N := by
    intro u _
    rw [Finset.card_product, Finset.card_singleton, card_cellW, one_mul]
  rw [aux_upPairs_eq hx, Finset.card_biUnion hdis, Finset.sum_congr rfl hcard,
    Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hx.1, Nat.mul_comm]

/-- The ordered inventory is twice `C(N,2)|D|` plus twice the uplink count; in particular it
is even, which is what makes the halving in `L` honest. -/
private theorem aux_card_adjPairs (x : Config N m) :
    (adjPairs x).card = 2 * (N.choose 2 * x.D.card + (upPairs x).card) := by
  rw [adjPairs_eq, Finset.card_union_of_disjoint (aux_disj_sib x),
    Finset.card_union_of_disjoint (aux_disj_up x),
    Finset.card_image_of_injective _ Prod.swap_injective, aux_card_sibPairs x]
  ring

/-- Adjacency is symmetric, so the ordered count is twice `L(x)`. -/
theorem two_mul_L (x : Config N m) : 2 * L x = (adjPairs x).card := by
  rw [L, aux_card_adjPairs x, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-- **Provisioned links.** `L(x) = C(N,2)|D| + N(|D| - 1)`. -/
theorem card_L {x : Config N m} (hx : x.WF) :
    L x = N.choose 2 * x.D.card + N * (x.D.card - 1) := by
  have h2 := two_mul_L x
  rw [aux_card_adjPairs x, card_upPairs hx] at h2
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

/-- Provisioned links in profile form: `L(x) = (C(N,2) + N) ∑_t M0_t - N`. -/
theorem card_L_profile {x : Config N m} (hx : x.WF) :
    L x = (N.choose 2 + N) * (∑ t ∈ Finset.Icc 1 m, M0 x t) - N := by
  rw [sum_M0 hx, card_L hx]
  obtain ⟨e, he⟩ : ∃ e, x.D.card = e + 1 := by
    have hpos : 0 < x.D.card := Finset.card_pos.mpr ⟨[], hx.1⟩
    exact ⟨x.D.card - 1, by omega⟩
  rw [he]
  simp only [Nat.add_sub_cancel]
  have hle : N ≤ (N.choose 2 + N) * (e + 1) := by
    calc N = N * 1 := (Nat.mul_one N).symm
      _ ≤ (N.choose 2 + N) * (e + 1) :=
        Nat.mul_le_mul (Nat.le_add_left N _) (Nat.succ_le_succ (Nat.zero_le e))
  rw [eq_comm, Nat.sub_eq_iff_eq_add hle]
  ring

/-! ## (iii) Message proxies -/

/-- The full-occupancy hierarchical-PBFT proxy `(N+1)|Sl(x)|` of Proposition thm:complexity. -/
def Cfull (x : Config N m) : ℕ := (N + 1) * x.Sl.card

/-- The occupancy-refined proxy: each cell contributes the PBFT-scale square of its live
membership plus one aggregation message per participant. -/
def Cload (x : Config N m) : ℕ := ∑ w ∈ x.D, (occ x w ^ 2 + occ x w)

/-- The full-occupancy proxy evaluates to `(N+1) N |D|`. -/
theorem Cfull_eq {x : Config N m} (hx : x.WF) : Cfull x = (N + 1) * N * x.D.card := by
  simp only [Cfull]
  rw [card_Sl hx, ← Nat.mul_assoc]

/-- The full-occupancy proxy in profile form: `(N+1) N ∑_t M0_t`. -/
theorem Cfull_profile {x : Config N m} (hx : x.WF) :
    Cfull x = (N + 1) * N * ∑ t ∈ Finset.Icc 1 m, M0 x t := by
  rw [Cfull_eq hx, sum_M0 hx]

/-- `C_load(x) = ∑_t ∑_k (k² + k) o_t(k)`, the paper's display. -/
theorem Cload_hist {x : Config N m} (hx : x.WF) :
    Cload x = ∑ t ∈ Finset.Icc 1 m, ∑ k ∈ Finset.range (N + 1), (k ^ 2 + k) * o x t k := by
  simp only [Cload]
  rw [← sum_tierCells hx (fun w => occ x w ^ 2 + occ x w)]
  exact (Finset.sum_congr rfl fun t _ => aux_hist_sum x t (fun k => k ^ 2 + k)).symm

/-- At full occupancy the refined proxy collapses to the full-occupancy proxy. -/
theorem Cload_full {x : Config N m} (hx : x.WF) (hfull : x.Sl ⊆ x.μ) :
    Cload x = (N + 1) * N * x.D.card := by
  have hocc : ∀ w ∈ x.D, occ x w = N := by
    intro w hw
    have hsub : ∀ v ∈ cellW w, v ∈ x.μ := by
      intro v hv
      obtain ⟨hvn, hvd⟩ := aux_mem_cellW.mp hv
      exact hfull (aux_mem_Sl.mpr ⟨hvn, by rw [hvd]; exact hw⟩)
    simp only [occ]
    rw [Finset.filter_true_of_mem hsub, card_cellW]
  simp only [Cload]
  rw [Finset.sum_congr rfl (fun w hw => by rw [hocc w hw] :
    ∀ w ∈ x.D, occ x w ^ 2 + occ x w = N ^ 2 + N), Finset.sum_const, smul_eq_mul]
  ring

/-! ## `O(1)` maintenance of the profile under the generators

Each bookkeeping letter moves the indicators by a constant and edits the histograms in at
most two bins at fixed tiers; the affine indicators above are therefore refreshed from the
update rather than recomputed from the configuration. -/

/-- A `join` leaves `|D|` fixed and raises `|μ|` by one. -/
theorem card_join {x y : Config N m} {s : Word N} (h : join s x = some y) :
    y.D.card = x.D.card ∧ y.μ.card = x.μ.card + 1 := by
  unfold join at h
  split at h
  · rename_i hg
    cases h
    exact ⟨rfl, Finset.card_insert_of_notMem hg.2.1⟩
  · cases h

/-- A `leave` leaves `|D|` fixed and lowers `|μ|` by one. -/
theorem card_leave {x y : Config N m} {s : Word N} (h : leave s x = some y) :
    y.D.card = x.D.card ∧ y.μ.card + 1 = x.μ.card := by
  unfold leave at h
  split at h
  · rename_i hg
    cases h
    exact ⟨rfl, Finset.card_erase_add_one hg⟩
  · cases h

/-- A `spawn` raises `|D|` by one and leaves `|μ|` fixed. -/
theorem card_spawn {x y : Config N m} {a : Word N} (h : spawn a x = some y) :
    y.D.card = x.D.card + 1 ∧ y.μ.card = x.μ.card := by
  unfold spawn at h
  split at h
  · rename_i hg
    cases h
    exact ⟨Finset.card_insert_of_notMem hg.2.1, rfl⟩
  · cases h

/-- A `retract` lowers `|D|` by one and leaves `|μ|` fixed. -/
theorem card_retract {x y : Config N m} {a : Word N} (h : retract a x = some y) :
    y.D.card + 1 = x.D.card ∧ y.μ.card = x.μ.card := by
  unfold retract at h
  split at h
  · rename_i hg
    cases h
    exact ⟨Finset.card_erase_add_one hg.1, rfl⟩
  · cases h

/-- The three components a successful `graft` produces. -/
private theorem aux_graft_parts {x y : Config N m} {a b : Word N} (h : graft a b x = some y) :
    y.D = x.D.image (subst false a b) ∧ y.μ = x.μ.image (subst true a b) := by
  unfold graft at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

/-- An equal-tier `graft` changes neither `|D|` nor `|μ|` (Theorem thm:graft-iso(iii)). -/
theorem card_graft {x y : Config N m} {a b : Word N} (hx : x.WF) (hlen : a.length = b.length)
    (h : graft a b x = some y) : y.D.card = x.D.card ∧ y.μ.card = x.μ.card := by
  obtain ⟨hD, hM⟩ := aux_graft_parts h
  obtain ⟨hD', hM'⟩ := aux_graft_parts (graft_graft hx h)
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · rw [hD]; exact Finset.card_image_le
  · rw [hD']; exact Finset.card_image_le
  · rw [hM]; exact Finset.card_image_le
  · rw [hM']; exact Finset.card_image_le

/-- `disable` moves no bin: it rewrites `ζ` only, so `D` and `μ` (hence every indicator above)
are untouched. -/
theorem disable_D_mu {x y : Config N m} {s : Word N} (h : disable s x = some y) :
    y.D = x.D ∧ y.μ = x.μ := by
  unfold disable at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

/-- `enable` moves no bin, for the same reason. -/
theorem enable_D_mu {x y : Config N m} {s : Word N} (h : enable s x = some y) :
    y.D = x.D ∧ y.μ = x.μ := by
  unfold enable at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

/-! ### The one-bin edits

`occ` and `kappa` are the same counting functional applied to `μ` and to `D`; the four
lemmas below are the two `insert`/`erase` edits of that functional, stated once. -/

private theorem aux_cnt_insert {S : Finset (Word N)} {a : Word N} (ha : a ≠ []) (haS : a ∉ S) :
    ((cellW a.dropLast).filter (fun s => s ∈ insert a S)).card
      = ((cellW a.dropLast).filter (fun s => s ∈ S)).card + 1 := by
  have hmem : a ∈ cellW a.dropLast := aux_mem_cellW.mpr ⟨ha, rfl⟩
  have hset : (cellW a.dropLast).filter (fun s => s ∈ insert a S)
      = insert a ((cellW a.dropLast).filter (fun s => s ∈ S)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hv, hv2 | hv2⟩
      · exact Or.inl hv2
      · exact Or.inr ⟨hv, hv2⟩
    · rintro (rfl | ⟨hv, hv2⟩)
      · exact ⟨hmem, Or.inl rfl⟩
      · exact ⟨hv, Or.inr hv2⟩
  rw [hset, Finset.card_insert_of_notMem (by simp [haS])]

private theorem aux_cnt_insert_other {S : Finset (Word N)} {a w : Word N}
    (hw : w ≠ a.dropLast) :
    ((cellW w).filter (fun s => s ∈ insert a S)).card
      = ((cellW w).filter (fun s => s ∈ S)).card := by
  congr 1
  refine Finset.filter_congr ?_
  intro v hv
  have hva : v ≠ a := by
    rintro rfl
    exact hw ((aux_mem_cellW.mp hv).2).symm
  simp [Finset.mem_insert, hva]

private theorem aux_cnt_erase {S : Finset (Word N)} {a : Word N} (ha : a ≠ []) (haS : a ∈ S) :
    ((cellW a.dropLast).filter (fun s => s ∈ S.erase a)).card + 1
      = ((cellW a.dropLast).filter (fun s => s ∈ S)).card := by
  have hmem : a ∈ cellW a.dropLast := aux_mem_cellW.mpr ⟨ha, rfl⟩
  have hset : (cellW a.dropLast).filter (fun s => s ∈ S.erase a)
      = ((cellW a.dropLast).filter (fun s => s ∈ S)).erase a := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hv, hv1, hv2⟩
      exact ⟨hv1, hv, hv2⟩
    · rintro ⟨hv1, hv, hv2⟩
      exact ⟨hv, hv1, hv2⟩
  rw [hset]
  exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hmem, haS⟩)

private theorem aux_cnt_erase_other {S : Finset (Word N)} {a w : Word N}
    (hw : w ≠ a.dropLast) :
    ((cellW w).filter (fun s => s ∈ S.erase a)).card
      = ((cellW w).filter (fun s => s ∈ S)).card := by
  congr 1
  refine Finset.filter_congr ?_
  intro v hv
  have hva : v ≠ a := by
    rintro rfl
    exact hw ((aux_mem_cellW.mp hv).2).symm
  simp [Finset.mem_erase, hva]

/-- The occupancy bin edited by a `join` is the one of the cell `pre(s)` hosting `s`; every
other cell keeps its occupancy. This is the one two-bin transfer in a single `o_t`. -/
theorem occ_join {x y : Config N m} {s : Word N} (hx : x.WF) (h : join s x = some y) :
    occ y s.dropLast = occ x s.dropLast + 1 ∧ ∀ w, w ≠ s.dropLast → occ y w = occ x w := by
  unfold join at h
  split at h
  · rename_i hg
    cases h
    have hsn : s ≠ [] := (aux_mem_Sl.mp hg.1).1
    exact ⟨aux_cnt_insert hsn hg.2.1, fun w hw => aux_cnt_insert_other hw⟩
  · cases h

/-- The occupancy bin edited by a `leave`. -/
theorem occ_leave {x y : Config N m} {s : Word N} (hx : x.WF) (h : leave s x = some y) :
    occ y s.dropLast + 1 = occ x s.dropLast ∧ ∀ w, w ≠ s.dropLast → occ y w = occ x w := by
  unfold leave at h
  split at h
  · rename_i hg
    cases h
    have hsn : s ≠ [] := (aux_mem_Sl.mp (hx.2.2.2.1 hg)).1
    exact ⟨aux_cnt_erase hsn hg, fun w hw => aux_cnt_erase_other hw⟩
  · cases h

/-- A `spawn a` edits exactly one anchoring bin, that of the parent cell `pre(a)`. -/
theorem kappa_spawn {x y : Config N m} {a : Word N} (hx : x.WF) (h : spawn a x = some y) :
    kappa y a.dropLast = kappa x a.dropLast + 1 ∧
      ∀ w, w ≠ a.dropLast → kappa y w = kappa x w := by
  unfold spawn at h
  split at h
  · rename_i hg
    cases h
    have han : a ≠ [] := (aux_mem_Sl.mp hg.1).1
    exact ⟨aux_cnt_insert han hg.2.1, fun w hw => aux_cnt_insert_other hw⟩
  · cases h

/-- A `retract a` edits exactly one anchoring bin, that of the parent cell `pre(a)`. -/
theorem kappa_retract {x y : Config N m} {a : Word N} (hx : x.WF) (h : retract a x = some y) :
    kappa y a.dropLast + 1 = kappa x a.dropLast ∧
      ∀ w, w ≠ a.dropLast → kappa y w = kappa x w := by
  unfold retract at h
  split at h
  · rename_i hg
    cases h
    exact ⟨aux_cnt_erase hg.2.1 hg.1, fun w hw => aux_cnt_erase_other hw⟩
  · cases h

/-- The cell a `spawn a` creates arrives at the empty bin: it has no occupied member and no
deployed child. Together with `kappa_spawn` this is the paper's "one two-bin transfer in
`h_{|a|}` plus one bin at `(o_{|a|+1}(0), h_{|a|+1}(0))`". -/
theorem occ_kappa_spawn_new {x y : Config N m} {a : Word N} (hx : x.WF)
    (h : spawn a x = some y) : occ y a = 0 ∧ kappa y a = 0 := by
  unfold spawn at h
  split at h
  · rename_i hg
    cases h
    constructor
    · show ((cellW a).filter (fun s => s ∈ x.μ)).card = 0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv hvm
      obtain ⟨hvn, hvd⟩ := aux_mem_cellW.mp hv
      exact hg.2.1 (by rw [← hvd]; exact (aux_mem_Sl.mp (hx.2.2.2.1 hvm)).2)
    · show ((cellW a).filter (fun s => s ∈ insert a x.D)).card = 0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv hvm
      obtain ⟨hvn, hvd⟩ := aux_mem_cellW.mp hv
      rcases Finset.mem_insert.mp hvm with he | hvD
      · exact aux_dropLast_ne hvn (by rw [hvd, he])
      · exact hg.2.1 (by rw [← hvd]; exact hx.2.2.1 v hvD hvn)
  · cases h

/-- A `spawn` adds exactly `N` slots: the slot count is refreshed from the update. -/
theorem card_Sl_spawn {x y : Config N m} {a : Word N} (hx : x.WF) (h : spawn a x = some y) :
    y.Sl.card = x.Sl.card + N := by
  unfold spawn at h
  split at h
  · rename_i hg
    cases h
    have hdis : Disjoint (cellW a) (x.D.biUnion cellW) := by
      refine Finset.disjoint_left.mpr ?_
      intro v hv hvS
      obtain ⟨hvn, hvd⟩ := aux_mem_cellW.mp hv
      obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hvS
      exact hg.2.1 (by rw [← hvd, (aux_mem_cellW.mp hvw).2]; exact hw)
    show ((insert a x.D).biUnion cellW).card = (x.D.biUnion cellW).card + N
    rw [Finset.biUnion_insert, Finset.card_union_of_disjoint hdis, card_cellW]
    exact Nat.add_comm _ _
  · cases h

/-- A `retract` removes exactly `N` slots. -/
theorem card_Sl_retract {x y : Config N m} {a : Word N} (hx : x.WF) (h : retract a x = some y) :
    y.Sl.card + N = x.Sl.card := by
  unfold retract at h
  split at h
  · rename_i hg
    cases h
    have hdis : Disjoint (cellW a) ((x.D.erase a).biUnion cellW) := by
      refine Finset.disjoint_left.mpr ?_
      intro v hv hvS
      obtain ⟨hvn, hvd⟩ := aux_mem_cellW.mp hv
      obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hvS
      exact (Finset.mem_erase.mp hw).1 (((aux_mem_cellW.mp hvw).2).symm.trans hvd)
    have hsplit : (x.D.biUnion cellW).card = N + ((x.D.erase a).biUnion cellW).card := by
      conv_lhs => rw [← Finset.insert_erase hg.1]
      rw [Finset.biUnion_insert, Finset.card_union_of_disjoint hdis, card_cellW]
    show ((x.D.erase a).biUnion cellW).card + N = (x.D.biUnion cellW).card
    rw [hsplit]
    exact Nat.add_comm _ _
  · cases h

/-! ### Equal-tier indicator invariance (Theorem thm:graft-iso(iii)) -/

/-- An equal-tier graft preserves the slot count. -/
theorem graft_card_Sl {x y : Config N m} {a b : Word N} (hx : x.WF) (hlen : a.length = b.length)
    (h : graft a b x = some y) : y.Sl.card = x.Sl.card := by
  rw [card_Sl (wf_graft hx h), card_Sl hx, (card_graft hx hlen h).1]

/-- An equal-tier graft preserves the provisioned link count. -/
theorem graft_L {x y : Config N m} {a b : Word N} (hx : x.WF) (hlen : a.length = b.length)
    (h : graft a b x = some y) : L y = L x := by
  rw [card_L (wf_graft hx h), card_L hx, (card_graft hx hlen h).1]

/-- An equal-tier graft preserves the full-occupancy message proxy. -/
theorem graft_Cfull {x y : Config N m} {a b : Word N} (hx : x.WF) (hlen : a.length = b.length)
    (h : graft a b x = some y) : Cfull y = Cfull x := by
  rw [Cfull_eq (wf_graft hx h), Cfull_eq hx, (card_graft hx hlen h).1]

end Kpi

end HSFN
