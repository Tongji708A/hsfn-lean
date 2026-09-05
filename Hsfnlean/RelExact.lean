/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Basic
import Hsfnlean.Calculus

/-!
# Reliability is not a function of the tier profile
(Proposition prop:rel-exact, items 1 and 2)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

The reliability model of prop:rel-exact, restricted to deployed cells
(Remark rem:comm-abstraction): every deployed cell fails internally with probability `q`,
independently of all the others, and a cell is *faulty* iff either its internal consensus
fails or at least `⌈N/2⌉` of its deployed child cells are faulty (a childless deployed cell
is faulty iff its internal consensus fails). `R(x)` is the probability that the seed cell
`[]` is not faulty.

## What this file states

* `pSeedFail` / `Rel` — the model itself, read as a finite sum over the internal-failure
  patterns `S ⊆ D` weighted by `q ^ |S| * (1 - q) ^ (|D| - |S|)`. This is the definition of
  `R(x)`; nothing about it is a recursion.
* `pFailW` — item 2, the bottom-up recursion
  `p w = q + (1 - q) * Pr[at least ⌈N/2⌉ of w's deployed children are faulty]`,
  with the inner probability the Poisson binomial tail `pbGE` (the children of a cell need
  *not* have equal failure probabilities; in the witness below they do not).
* `step` — the homogeneous specialization `F_c(p) = q + (1-q) Pr[Bin(c,p) ≥ ⌈N/2⌉]`, written
  as a `Finset.sum` over `Finset.Ico ⌈N/2⌉ (c+1)`, with `pFailW_of_homogeneous` the bridge to
  the recursion. It does *not* suffice for the witness: a spread tier-2 branch has children of
  three different failure probabilities.
* `exact_recursion` — item 2's claim proper: the recursion computes `R(x)` exactly, on every
  well-formed configuration.
* `faultyB_fuel_stable`, `faultyB_seed_stable` — adequacy of the fuel bound: on a well-formed
  configuration the depth-`m` resolution of the fault predicate is already its fixed point, so
  `Rel` is the paper's `R(x)` and not a truncation of it.
* `xS`, `xC` and `Rrec_spread`, `Rrec_conc`, `Rrec_ne`, `Rrec_spread_round`,
  `Rrec_conc_round` — item 1's witness pair at `N = 3`, `q = 1/5`, all cells deployed
  through tier 3 (`1 + 3 + 9`) and three tier-3 cells fully expanded (`9` tier-4 cells),
  all slots occupied. The exact values are
  `R_spread = 1484502599319552 / 2384185791015625 = 0.6226455…` (the three heavy cells one
  per tier-2 branch) and
  `R_conc = 1478585883901952 / 2384185791015625 = 0.6201638…` (all three under one branch),
  matching the paper's `0.6226` and `0.6202`.
* `profile_eq`, `tierCount_spread`, `tierCount_conc`, `occProfile_eq`, `occ_eq` — the two
  configurations have equal per-tier cell counts `(1,3,9,9)`, equal per-tier child-count
  (anchoring) histograms `h_t` and equal per-tier occupancy histograms `o_t`. The whole tier
  profile `{M0_t, o_t, h_t}` of the paper is therefore shared by the pair.
* `profile_blind`, `no_profile_formula`, `no_affine_profile_formula`,
  `no_affine_tier_formula` — item 1's conclusion: no function whatsoever of the *full* tier
  profile (both histogram families, hence also the cell counts) computes `R`, a fortiori no
  affine one.

Tier convention: a cell's tier is `w.length + 1`, so the seed `[]` sits at index `t = 0` in
every per-tier quantity below and the paper's tiers 1, 2, 3, 4 are `t = 0, 1, 2, 3`.

## What this file does NOT formalize

* The `O(N |D|)` arithmetic-operation cost of item 2 and the `O(N m)` incremental
  re-evaluation cost after a generator: no cost model is present here.
* Item 3 of prop:rel-exact (the monotone interval bounds from the profile alone); that is a
  separate statement about the maps `F_k` and is out of scope here.
* The link between this finite model and the level iterations of thm:security and
  prop:threshold-b (`Hsfnlean.Threshold`); no bridge is asserted.
* The `N = 4`, `q = 0.125` companion pair of item 1 (`0.6737` versus `0.6691`). The same
  definitions express it; only the `N = 3` pair is stated.
* Any measure-theoretic probability space. The independent internal failures are encoded
  directly as the finite weighted sum `pSeedFail` over `Finset.powerset`, and `q` is an
  arbitrary rational: no hypothesis `0 ≤ q ≤ 1` is imposed.
* The paper's design rule that "the balanced allocation is the more reliable" in general.
  Only the pinned pair is proved (`Rel_conc_lt_spread`); no monotonicity theorem over
  allocations is stated or proved.
* Any claim that this witness pair is minimal, or that the profile determines `R` on any
  restricted class of configurations.
* Communication, latency and the protocol layer (Remark rem:comm-abstraction).
-/

namespace HSFN

namespace RelExact

open Calc

variable {N m : ℕ}

/-! ## The quorum and the Poisson binomial tail -/

/-- The fixed fault quorum `⌈N/2⌉` of prop:rel-exact. -/
def quorum (N : ℕ) : ℕ := (N + 1) / 2

theorem quorum_eq_ceil (N : ℕ) : (quorum N : ℤ) = ⌈(N : ℚ) / 2⌉ := by
  have h1 : N ≤ 2 * quorum N := by unfold quorum; omega
  have h2 : 2 * quorum N ≤ N + 1 := by unfold quorum; omega
  have h1' : (N : ℚ) ≤ 2 * (quorum N : ℚ) := by exact_mod_cast h1
  have h2' : 2 * (quorum N : ℚ) ≤ (N : ℚ) + 1 := by exact_mod_cast h2
  symm
  rw [Int.ceil_eq_iff]
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

theorem quorum_three : quorum 3 = 2 := rfl

theorem quorum_four : quorum 4 = 2 := rfl

/-- `pbGE k ps` is the probability that at least `k` of independent indicators with success
probabilities `ps` succeed: the upper tail of the Poisson binomial distribution, obtained by
conditioning on the first indicator. -/
def pbGE : ℕ → List ℚ → ℚ
  | 0, _ => 1
  | _ + 1, [] => 0
  | k + 1, p :: ps => p * pbGE k ps + (1 - p) * pbGE (k + 1) ps

/-- The same tail written as a sum over the subsets of indicators that succeed. This is the
statement that `pbGE` really is the Poisson binomial tail and not merely some recursion. -/
def pbGEsub (k : ℕ) (ps : List ℚ) : ℚ :=
  ∑ S ∈ (Finset.range ps.length).powerset.filter (fun S => k ≤ S.card),
    ∏ i ∈ Finset.range ps.length, (if i ∈ S then ps.getD i 0 else 1 - ps.getD i 0)

private theorem aux_prod_ite {α : Type*} [DecidableEq α] (T S : Finset α) (hS : S ⊆ T)
    (f g : α → ℚ) :
    ∏ i ∈ T, (if i ∈ S then f i else g i) = (∏ i ∈ S, f i) * ∏ i ∈ T \ S, g i := by
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun i => i ∈ S)]
  have e1 : T.filter (fun i => i ∈ S) = S := by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hS]
  have e2 : T.filter (fun i => ¬ i ∈ S) = T \ S := (Finset.sdiff_eq_filter T S).symm
  rw [e1, e2]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => if_pos hi
  · exact Finset.prod_congr rfl fun i hi => if_neg (Finset.mem_sdiff.mp hi).2

private theorem aux_pbGE_zero (l : List ℚ) : pbGE 0 l = 1 := by
  cases l <;> rfl

private theorem aux_pbGE_snoc (p : ℚ) :
    ∀ (ps : List ℚ) (k : ℕ),
      pbGE (k + 1) (ps ++ [p]) = p * pbGE k ps + (1 - p) * pbGE (k + 1) ps := by
  intro ps
  induction ps with
  | nil => intro k; simp [pbGE]
  | cons a as ih =>
    intro k
    cases k with
    | zero =>
      rw [List.cons_append]
      show a * pbGE 0 (as ++ [p]) + (1 - a) * pbGE 1 (as ++ [p])
        = p * pbGE 0 (a :: as) + (1 - p) * pbGE 1 (a :: as)
      show a * pbGE 0 (as ++ [p]) + (1 - a) * pbGE 1 (as ++ [p])
        = p * pbGE 0 (a :: as) + (1 - p) * (a * pbGE 0 as + (1 - a) * pbGE 1 as)
      rw [ih 0, aux_pbGE_zero (as ++ [p]), aux_pbGE_zero (a :: as), aux_pbGE_zero as]
      ring
    | succ j =>
      rw [List.cons_append]
      show a * pbGE (j + 1) (as ++ [p]) + (1 - a) * pbGE (j + 1 + 1) (as ++ [p])
        = p * pbGE (j + 1) (a :: as) + (1 - p) * pbGE (j + 1 + 1) (a :: as)
      rw [ih j, ih (j + 1)]
      show a * (p * pbGE j as + (1 - p) * pbGE (j + 1) as)
          + (1 - a) * (p * pbGE (j + 1) as + (1 - p) * pbGE (j + 1 + 1) as)
        = p * (a * pbGE j as + (1 - a) * pbGE (j + 1) as)
          + (1 - p) * (a * pbGE (j + 1) as + (1 - a) * pbGE (j + 1 + 1) as)
      ring

private theorem aux_pbGEsub_zero (ps : List ℚ) : pbGEsub 0 ps = 1 := by
  have h : ∀ S ∈ (Finset.range ps.length).powerset,
      (∏ i ∈ Finset.range ps.length, (if i ∈ S then ps.getD i 0 else 1 - ps.getD i 0))
        = (∏ i ∈ S, ps.getD i 0) * ∏ i ∈ Finset.range ps.length \ S, (1 - ps.getD i 0) :=
    fun S hS => aux_prod_ite _ _ (Finset.mem_powerset.mp hS) _ _
  have hfil : (Finset.range ps.length).powerset.filter (fun S => 0 ≤ S.card)
      = (Finset.range ps.length).powerset := by
    apply Finset.filter_true_of_mem
    intro S _
    exact Nat.zero_le _
  unfold pbGEsub
  rw [hfil, Finset.sum_congr rfl h, ← Finset.prod_add]
  simp

private theorem aux_pbGEsub_nil (k : ℕ) : pbGEsub (k + 1) [] = 0 := by
  simp [pbGEsub]

private theorem aux_pbGEsub_snoc (p : ℚ) (ps : List ℚ) (k : ℕ) :
    pbGEsub (k + 1) (ps ++ [p]) = p * pbGEsub k ps + (1 - p) * pbGEsub (k + 1) ps := by
  unfold pbGEsub
  simp only [List.length_append, List.length_cons, List.length_nil, Finset.sum_filter,
    Nat.zero_add]
  set n := ps.length with hn
  have hget : ∀ i ∈ Finset.range n, (ps ++ [p]).getD i 0 = ps.getD i 0 := by
    intro i hi
    exact List.getD_append _ _ _ _ (by simpa [hn] using Finset.mem_range.mp hi)
  have hgetn : (ps ++ [p]).getD n 0 = p := by
    rw [List.getD_append_right _ _ _ _ (by simp [hn])]
    simp [hn]
  have hsplit : ∀ F : Finset ℕ → ℚ,
      ∑ S ∈ (Finset.range (n + 1)).powerset, F S
        = (∑ t ∈ (Finset.range n).powerset, F t)
            + ∑ t ∈ (Finset.range n).powerset, F (insert n t) := by
    intro F
    rw [Finset.range_add_one, Finset.sum_powerset_insert Finset.notMem_range_self]
  rw [hsplit]
  have hA : ∀ t ∈ (Finset.range n).powerset,
      (if k + 1 ≤ t.card then
        ∏ i ∈ Finset.range (n + 1),
          (if i ∈ t then (ps ++ [p]).getD i 0 else 1 - (ps ++ [p]).getD i 0) else 0)
      = (1 - p) * (if k + 1 ≤ t.card then
          ∏ i ∈ Finset.range n, (if i ∈ t then ps.getD i 0 else 1 - ps.getD i 0) else 0) := by
    intro t ht
    have htn : n ∉ t := fun h => Finset.notMem_range_self (Finset.mem_powerset.mp ht h)
    have hprod : (∏ i ∈ Finset.range (n + 1),
        (if i ∈ t then (ps ++ [p]).getD i 0 else 1 - (ps ++ [p]).getD i 0))
        = (1 - p) * ∏ i ∈ Finset.range n,
            (if i ∈ t then ps.getD i 0 else 1 - ps.getD i 0) := by
      rw [Finset.prod_range_succ,
        Finset.prod_congr rfl (fun i hi => by rw [hget i hi]), if_neg htn, hgetn]
      ring
    rw [hprod]
    split <;> ring
  have hB : ∀ t ∈ (Finset.range n).powerset,
      (if k + 1 ≤ (insert n t).card then
        ∏ i ∈ Finset.range (n + 1),
          (if i ∈ insert n t then (ps ++ [p]).getD i 0 else 1 - (ps ++ [p]).getD i 0) else 0)
      = p * (if k ≤ t.card then
          ∏ i ∈ Finset.range n, (if i ∈ t then ps.getD i 0 else 1 - ps.getD i 0) else 0) := by
    intro t ht
    have htn : n ∉ t := fun h => Finset.notMem_range_self (Finset.mem_powerset.mp ht h)
    have hiff : (k + 1 ≤ (insert n t).card) ↔ (k ≤ t.card) := by
      rw [Finset.card_insert_of_notMem htn]
      omega
    have hin : ∀ i ∈ Finset.range n,
        (if i ∈ insert n t then (ps ++ [p]).getD i 0 else 1 - (ps ++ [p]).getD i 0)
          = (if i ∈ t then ps.getD i 0 else 1 - ps.getD i 0) := by
      intro i hi
      have hine : i ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hi)
      by_cases hit : i ∈ t
      · rw [if_pos (Finset.mem_insert_of_mem hit), if_pos hit, hget i hi]
      · rw [if_neg (by simp [Finset.mem_insert, hine, hit]), if_neg hit, hget i hi]
    have hprod : (∏ i ∈ Finset.range (n + 1),
        (if i ∈ insert n t then (ps ++ [p]).getD i 0 else 1 - (ps ++ [p]).getD i 0))
        = p * ∏ i ∈ Finset.range n,
            (if i ∈ t then ps.getD i 0 else 1 - ps.getD i 0) := by
      rw [Finset.prod_range_succ, Finset.prod_congr rfl hin,
        if_pos (Finset.mem_insert_self n t), hgetn]
      ring
    simp only [hiff, hprod]
    split <;> ring
  rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem pbGE_eq_pbGEsub (k : ℕ) (ps : List ℚ) : pbGE k ps = pbGEsub k ps := by
  induction ps using List.reverseRecOn generalizing k with
  | nil =>
    cases k with
    | zero => simp [aux_pbGE_zero, pbGEsub]
    | succ k => rw [aux_pbGEsub_nil]; rfl
  | append_singleton as a ih =>
    cases k with
    | zero => rw [aux_pbGEsub_zero, aux_pbGE_zero]
    | succ k => rw [aux_pbGE_snoc, aux_pbGEsub_snoc, ih, ih]

/-- Homogeneous children: the Poisson binomial tail degenerates to the binomial tail
`Pr[Bin(n, p) ≥ k]`, the function `F_k` of prop:rel-exact(iii). -/
theorem pbGE_replicate (k n : ℕ) (p : ℚ) :
    pbGE k (List.replicate n p) =
      ∑ i ∈ Finset.Ico k (n + 1), (n.choose i : ℚ) * p ^ i * (1 - p) ^ (n - i) := by
  have hgd : ∀ i ∈ Finset.range n, (List.replicate n p).getD i 0 = p := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    simp [List.getD_eq_getElem?_getD, hi']
  have hterm : ∀ S ∈ (Finset.range n).powerset,
      (∏ i ∈ Finset.range n, (if i ∈ S then (List.replicate n p).getD i 0
        else 1 - (List.replicate n p).getD i 0)) = p ^ S.card * (1 - p) ^ (n - S.card) := by
    intro S hS
    have hSsub := Finset.mem_powerset.mp hS
    have e : ∀ i ∈ Finset.range n,
        (if i ∈ S then (List.replicate n p).getD i 0 else 1 - (List.replicate n p).getD i 0)
          = (if i ∈ S then p else 1 - p) := by
      intro i hi
      rw [hgd i hi]
    rw [Finset.prod_congr rfl e, aux_prod_ite _ _ hSsub, Finset.prod_const, Finset.prod_const,
      Finset.card_sdiff, Finset.inter_eq_left.mpr hSsub, Finset.card_range]
  have hfil : (Finset.range (n + 1)).filter (fun j => k ≤ j) = Finset.Ico k (n + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [pbGE_eq_pbGEsub]
  unfold pbGEsub
  rw [List.length_replicate]
  simp only [Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun S hS => by rw [hterm S hS]), Finset.sum_powerset,
    Finset.card_range]
  have hinner : ∀ j ∈ Finset.range (n + 1),
      (∑ S ∈ Finset.powersetCard j (Finset.range n),
        (if k ≤ S.card then p ^ S.card * (1 - p) ^ (n - S.card) else 0))
        = (if k ≤ j then (n.choose j : ℚ) * p ^ j * (1 - p) ^ (n - j) else 0) := by
    intro j _
    rw [Finset.sum_congr rfl (fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2]),
      Finset.sum_const, Finset.card_powersetCard, Finset.card_range, nsmul_eq_mul]
    split <;> ring
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, hfil]

/-- The homogeneous one-level map `F_c(p) = q + (1 - q) Pr[Bin(c, p) ≥ ⌈N/2⌉]` of
prop:rel-exact, the special case of the recursion in which all `c` deployed children carry
one and the same failure probability. It is *not* enough for the witness pair below: a spread
tier-2 branch has children of failure probabilities `(177/625, 1/5, 1/5)`, so the general
Poisson binomial tail `pbGE` is what the recursion is stated with. -/
def step (q : ℚ) (N c : ℕ) (p : ℚ) : ℚ :=
  q + (1 - q) *
    ∑ i ∈ Finset.Ico (quorum N) (c + 1), (c.choose i : ℚ) * p ^ i * (1 - p) ^ (c - i)

/-! ## The cell tree of a configuration -/

/-- The deployed child cells of `w` in the deployed set `D`. -/
def childList (D : Finset (Word N)) (w : Word N) : List (Word N) :=
  (List.finRange N).filterMap fun d => if w ++ [d] ∈ D then some (w ++ [d]) else none

/-- The number of deployed child cells of `w`, the quantity `c` of prop:rel-exact. -/
def childCount (D : Finset (Word N)) (w : Word N) : ℕ := (childList D w).length

theorem mem_childList {D : Finset (Word N)} {w v : Word N} :
    v ∈ childList D w ↔ v ∈ D ∧ ∃ d : Fin N, v = w ++ [d] := by
  simp only [childList, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨d, hd⟩
    by_cases h : w ++ [d] ∈ D
    · rw [if_pos h] at hd
      cases hd
      exact ⟨h, d, rfl⟩
    · rw [if_neg h] at hd
      exact absurd hd (by simp)
  · rintro ⟨hv, d, rfl⟩
    exact ⟨d, by rw [if_pos hv]⟩

theorem childCount_le (D : Finset (Word N)) (w : Word N) : childCount D w ≤ N := by
  have h := List.length_filterMap_le
    (fun d : Fin N => if w ++ [d] ∈ D then some (w ++ [d]) else none) (List.finRange N)
  simpa [childCount, childList] using h

/-! ## Item 2: the bottom-up recursion -/

/-- The bottom-up recursion of prop:rel-exact(ii),
`p w = q + (1 - q) Pr[∑ over the deployed children w d of X_{w d} ≥ ⌈N/2⌉]`,
evaluated with a fuel bound `f` on the remaining depth. A cell with no deployed children
gets `p w = q`, since `pbGE k [] = 0` for `k ≥ 1`. -/
def pFailW (q : ℚ) (N : ℕ) (D : Finset (Word N)) : ℕ → Word N → ℚ
  | 0, _ => q
  | f + 1, w => q + (1 - q) * pbGE (quorum N) ((childList D w).map fun v => pFailW q N D f v)

/-- Once the fuel exceeds the remaining depth, the recursion has bottomed out. -/
private theorem aux_pFailW_zero (q : ℚ) (N : ℕ) (D : Finset (Word N)) (w : Word N) :
    pFailW q N D 0 w = q := rfl

private theorem aux_pFailW_succ (q : ℚ) (N : ℕ) (D : Finset (Word N)) (f : ℕ) (w : Word N) :
    pFailW q N D (f + 1) w
      = q + (1 - q) * pbGE (quorum N) ((childList D w).map fun v => pFailW q N D f v) := rfl

private theorem aux_quorum_pos {N : ℕ} (hN : 1 ≤ N) : ∃ j, quorum N = j + 1 :=
  ⟨quorum N - 1, by unfold quorum; omega⟩

theorem pFailW_fuel_stable (q : ℚ) (N : ℕ) (hN : 1 ≤ N) (D : Finset (Word N)) (f : ℕ)
    (w : Word N) (h : ∀ v ∈ D, v.length ≤ w.length + f) :
    pFailW q N D (f + 1) w = pFailW q N D f w := by
  induction f generalizing w with
  | zero =>
    obtain ⟨j, hj⟩ := aux_quorum_pos hN
    have hnil : childList D w = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro v hv
      obtain ⟨hvD, d, rfl⟩ := mem_childList.mp hv
      have hlen := h _ hvD
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    rw [aux_pFailW_succ, aux_pFailW_zero, hnil, hj]
    simp [pbGE]
  | succ f ih =>
    have hmap : ((childList D w).map fun v => pFailW q N D (f + 1) v)
        = ((childList D w).map fun v => pFailW q N D f v) := by
      apply List.map_congr_left
      intro v hv
      obtain ⟨hvD, d, rfl⟩ := mem_childList.mp hv
      refine ih _ (fun u hu => ?_)
      have hlen := h u hu
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [aux_pFailW_succ, aux_pFailW_succ, hmap]

/-- A childless deployed cell fails exactly when its internal consensus fails. -/
theorem pFailW_of_childList_nil (q : ℚ) (N : ℕ) (hN : 1 ≤ N) (D : Finset (Word N)) (f : ℕ)
    (w : Word N) (h : childList D w = []) : pFailW q N D f w = q := by
  cases f with
  | zero => exact aux_pFailW_zero q N D w
  | succ f =>
    obtain ⟨j, hj⟩ := aux_quorum_pos hN
    rw [aux_pFailW_succ, h, hj]
    simp [pbGE]

/-- When all deployed children of `w` share one failure probability `p`, the recursion step
at `w` is the homogeneous map `F_c` with `c = childCount D w`. This is the bridge between the
recursion of item 2 and the maps `F_k` the paper's item 3 is phrased with. -/
theorem pFailW_of_homogeneous (q : ℚ) (N : ℕ) (D : Finset (Word N)) (f : ℕ) (w : Word N)
    (p : ℚ) (h : ∀ v ∈ childList D w, pFailW q N D f v = p) :
    pFailW q N D (f + 1) w = step q N (childCount D w) p := by
  have hmap : ((childList D w).map fun v => pFailW q N D f v)
      = List.replicate (childCount D w) p :=
    List.map_eq_replicate_iff.mpr h
  rw [aux_pFailW_succ, hmap, pbGE_replicate, step]

/-- `F_3(1/5) = 177/625`: a fully expanded tier-3 cell of the witness pair. -/
theorem step_heavy : step (1 / 5) 3 3 (1 / 5) = 177 / 625 := by
  rw [step, show Finset.Ico (quorum 3) (3 + 1) = ({2, 3} : Finset ℕ) from rfl,
    Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3)]
  norm_num [show Nat.choose 3 2 = 3 from rfl, show Nat.choose 3 3 = 1 from rfl]

/-- `F_3(177/625) = 434746261/1220703125`: the loaded tier-2 branch of the concentrated
deployment, whose three children are all heavy. The spread deployment has no such
homogeneous branch, which is exactly why the two shapes differ. -/
theorem step_branch_conc : step (1 / 5) 3 3 (177 / 625) = 434746261 / 1220703125 := by
  rw [step, show Finset.Ico (quorum 3) (3 + 1) = ({2, 3} : Finset ℕ) from rfl,
    Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3)]
  norm_num [show Nat.choose 3 2 = 3 from rfl, show Nat.choose 3 3 = 1 from rfl]

/-! ## The model itself: independent internal failures -/

/-- The weight of the internal-failure pattern `S ⊆ D`: the cells in `S` fail internally,
those in `D \ S` do not, independently, each with probability `q`. -/
def patWeight (q : ℚ) (D S : Finset (Word N)) : ℚ := q ^ S.card * (1 - q) ^ (D.card - S.card)

/-- The weights of the internal-failure patterns sum to one. -/
theorem sum_patWeight (q : ℚ) (D : Finset (Word N)) :
    ∑ S ∈ D.powerset, patWeight q D S = 1 := by
  have h : ∀ S ∈ D.powerset,
      patWeight q D S = (∏ _i ∈ S, q) * ∏ _i ∈ D \ S, (1 - q) := by
    intro S hS
    rw [Finset.prod_const, Finset.prod_const, Finset.card_sdiff,
      Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hS)]
    rfl
  rw [Finset.sum_congr rfl h, ← Finset.prod_add]
  simp

/-- Faultiness of the cell `w` under the internal-failure pattern `S`: either the internal
consensus of `w` fails (`w ∈ S`), or at least `⌈N/2⌉` of its deployed children are faulty.
Resolved to depth `f`. -/
def faultyB (N : ℕ) (D S : Finset (Word N)) : ℕ → Word N → Bool
  | 0, w => decide (w ∈ S)
  | f + 1, w =>
      decide (w ∈ S) ||
        decide (quorum N ≤ (childList D w).countP fun v => faultyB N D S f v)

/-- The complement of `R(x)`: the probability that the seed cell is faulty, as the total
weight of the internal-failure patterns under which it is. -/
def pSeedFail (q : ℚ) (N m : ℕ) (x : Config N m) : ℚ :=
  ∑ S ∈ x.D.powerset, if faultyB N x.D S m [] then patWeight q x.D S else 0

/-- The reliability `R(x)` of prop:rel-exact: the probability that the seed cell is not
faulty. This is the definition; the recursion below is a theorem about it. -/
def Rel (q : ℚ) (N m : ℕ) (x : Config N m) : ℚ := 1 - pSeedFail q N m x

/-- The value produced by the bottom-up recursion of item 2, run from the seed with fuel `m`
(every deployed cell of a well-formed configuration is within `m` of the seed). -/
def Rrec (q : ℚ) (N m : ℕ) (x : Config N m) : ℚ := 1 - pFailW q N x.D m []

/-! ### The independence machinery behind item 2

`aux_E q T g` is the expectation of `g` under the product measure in which each cell of `T`
fails internally with probability `q`; `aux_cone D w` is the subtree of `w`. The recursion is
proved exact by splitting that expectation at the seed's own coin and across the pairwise
disjoint cones of its deployed children. -/

private theorem aux_prefix_mem {D : Finset (Word N)}
    (hp : ∀ u ∈ D, u ≠ [] → u.dropLast ∈ D) {v w : Word N} (hw : w ∈ D) (hv : v <+: w) :
    v ∈ D := by
  obtain ⟨t, rfl⟩ := hv
  revert hw
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t d ih =>
    intro hw
    apply ih
    have h2 := hp (v ++ (t ++ [d])) hw (by simp)
    simpa [← List.append_assoc] using h2

/-- The deployed cells in the subtree rooted at `w`. -/
private def aux_cone (D : Finset (Word N)) (w : Word N) : Finset (Word N) :=
  D.filter fun v => w <+: v

private theorem aux_mem_cone {D : Finset (Word N)} {w v : Word N} :
    v ∈ aux_cone D w ↔ v ∈ D ∧ w <+: v := Finset.mem_filter

private theorem aux_cone_self {D : Finset (Word N)} {w : Word N} (hw : w ∈ D) :
    w ∈ aux_cone D w := aux_mem_cone.mpr ⟨hw, List.prefix_rfl⟩

private theorem aux_cone_mono {D : Finset (Word N)} {w v : Word N} (h : w <+: v) :
    aux_cone D v ⊆ aux_cone D w := fun _u hu =>
  aux_mem_cone.mpr ⟨(aux_mem_cone.mp hu).1, h.trans (aux_mem_cone.mp hu).2⟩

private theorem aux_cone_nil (D : Finset (Word N)) : aux_cone D [] = D :=
  Finset.filter_true_of_mem fun _ _ => List.nil_prefix

/-- The union of the subtrees rooted at the cells of a list. -/
private def aux_bigU (D : Finset (Word N)) : List (Word N) → Finset (Word N)
  | [] => ∅
  | v :: vs => aux_cone D v ∪ aux_bigU D vs

private theorem aux_mem_bigU {D : Finset (Word N)} {L : List (Word N)} {u : Word N} :
    u ∈ aux_bigU D L ↔ ∃ v ∈ L, u ∈ aux_cone D v := by
  induction L with
  | nil => simp [aux_bigU]
  | cons a as ih =>
    show u ∈ aux_cone D a ∪ aux_bigU D as ↔ _
    rw [Finset.mem_union, ih]
    constructor
    · rintro (h | ⟨v, hv, h⟩)
      · exact ⟨a, by simp, h⟩
      · exact ⟨v, by simp [hv], h⟩
    · rintro ⟨v, hv, h⟩
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact Or.inl h
      · exact Or.inr ⟨v, hv', h⟩

private theorem aux_cone_subset_bigU {D : Finset (Word N)} {L : List (Word N)} {v : Word N}
    (hv : v ∈ L) : aux_cone D v ⊆ aux_bigU D L :=
  fun _ hu => aux_mem_bigU.mpr ⟨v, hv, hu⟩

private theorem aux_bigU_disjoint {D A : Finset (Word N)} {L : List (Word N)}
    (h : ∀ v ∈ L, Disjoint A (aux_cone D v)) : Disjoint A (aux_bigU D L) := by
  refine Finset.disjoint_left.mpr fun u hu hu' => ?_
  obtain ⟨v, hv, hv'⟩ := aux_mem_bigU.mp hu'
  exact Finset.disjoint_left.mp (h v hv) hu hv'

/-- The weight of the internal-failure pattern `S` inside the cell set `T`. -/
private def aux_wt (q : ℚ) (T S : Finset (Word N)) : ℚ :=
  ∏ v ∈ T, if v ∈ S then q else 1 - q

/-- The expectation of `g` over the internal-failure patterns of the cell set `T`. -/
private def aux_E (q : ℚ) (T : Finset (Word N)) (g : Finset (Word N) → ℚ) : ℚ :=
  ∑ S ∈ T.powerset, aux_wt q T S * g S

private theorem aux_wt_eq_patWeight (q : ℚ) (D S : Finset (Word N)) (hS : S ⊆ D) :
    aux_wt q D S = patWeight q D S := by
  unfold aux_wt patWeight
  rw [aux_prod_ite D S hS, Finset.prod_const, Finset.prod_const, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hS]

private theorem aux_E_congr (q : ℚ) (T : Finset (Word N)) (g₁ g₂ : Finset (Word N) → ℚ)
    (h : ∀ S, g₁ S = g₂ S) : aux_E q T g₁ = aux_E q T g₂ := by
  unfold aux_E
  exact Finset.sum_congr rfl fun S _ => by rw [h S]

private theorem aux_E_add (q : ℚ) (T : Finset (Word N)) (g₁ g₂ : Finset (Word N) → ℚ) :
    aux_E q T (fun S => g₁ S + g₂ S) = aux_E q T g₁ + aux_E q T g₂ := by
  unfold aux_E
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => by ring

private theorem aux_E_sub (q : ℚ) (T : Finset (Word N)) (g₁ g₂ : Finset (Word N) → ℚ) :
    aux_E q T (fun S => g₁ S - g₂ S) = aux_E q T g₁ - aux_E q T g₂ := by
  unfold aux_E
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun S _ => by ring

private theorem aux_E_one (q : ℚ) (T : Finset (Word N)) :
    aux_E q T (fun _ => (1 : ℚ)) = 1 := by
  unfold aux_E aux_wt
  have h : ∀ S ∈ T.powerset,
      (∏ v ∈ T, if v ∈ S then q else 1 - q) * 1
        = (∏ _v ∈ S, q) * ∏ _v ∈ T \ S, (1 - q) := by
    intro S hS
    rw [mul_one, aux_prod_ite T S (Finset.mem_powerset.mp hS)]
  rw [Finset.sum_congr rfl h, ← Finset.prod_add]
  simp

private theorem aux_E_empty (q : ℚ) (g : Finset (Word N) → ℚ) :
    aux_E q ∅ g = g ∅ := by
  unfold aux_E aux_wt
  simp

private theorem aux_E_point (q : ℚ) (w : Word N) (g : Finset (Word N) → ℚ) :
    aux_E q ({w} : Finset (Word N)) g = (1 - q) * g ∅ + q * g {w} := by
  unfold aux_E aux_wt
  rw [show ({w} : Finset (Word N)) = insert w ∅ from rfl,
    Finset.sum_powerset_insert (by simp)]
  simp

private theorem aux_E_split (q : ℚ) (A B : Finset (Word N)) (hAB : Disjoint A B)
    (g₁ g₂ : Finset (Word N) → ℚ)
    (h₁ : ∀ S, g₁ (S ∩ A) = g₁ S) (h₂ : ∀ S, g₂ (S ∩ B) = g₂ S) :
    aux_E q (A ∪ B) (fun S => g₁ S * g₂ S) = aux_E q A g₁ * aux_E q B g₂ := by
  have hwtA : ∀ S : Finset (Word N), aux_wt q A (S ∩ A) = aux_wt q A S := by
    intro S
    exact Finset.prod_congr rfl fun v hv => by simp [Finset.mem_inter, hv]
  have hwtB : ∀ S : Finset (Word N), aux_wt q B (S ∩ B) = aux_wt q B S := by
    intro S
    exact Finset.prod_congr rfl fun v hv => by simp [Finset.mem_inter, hv]
  have key : (∑ S ∈ (A ∪ B).powerset, aux_wt q (A ∪ B) S * (g₁ S * g₂ S))
      = ∑ t ∈ A.powerset ×ˢ B.powerset,
          (aux_wt q A t.1 * g₁ t.1) * (aux_wt q B t.2 * g₂ t.2) := by
    refine Finset.sum_nbij' (fun S => (S ∩ A, S ∩ B)) (fun t => t.1 ∪ t.2) ?_ ?_ ?_ ?_ ?_
    · intro S _
      simp only [Finset.mem_product, Finset.mem_powerset]
      exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
    · intro t ht
      simp only [Finset.mem_product, Finset.mem_powerset] at ht
      exact Finset.mem_powerset.mpr
        (Finset.union_subset (ht.1.trans Finset.subset_union_left)
          (ht.2.trans Finset.subset_union_right))
    · intro S hS
      have hSsub := Finset.mem_powerset.mp hS
      rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hSsub]
    · intro t ht
      simp only [Finset.mem_product, Finset.mem_powerset] at ht
      have e1 : (t.1 ∪ t.2) ∩ A = t.1 := by
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr ht.1,
          Finset.disjoint_iff_inter_eq_empty.mp
            (Finset.disjoint_of_subset_left ht.2 hAB.symm), Finset.union_empty]
      have e2 : (t.1 ∪ t.2) ∩ B = t.2 := by
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr ht.2,
          Finset.disjoint_iff_inter_eq_empty.mp
            (Finset.disjoint_of_subset_left ht.1 hAB), Finset.empty_union]
      rw [e1, e2]
    · intro S _
      have e0 : aux_wt q (A ∪ B) S = aux_wt q A S * aux_wt q B S := Finset.prod_union hAB
      dsimp only
      rw [hwtA S, hwtB S, h₁ S, h₂ S, e0]
      ring
  unfold aux_E
  rw [key, Finset.sum_product, Finset.sum_mul_sum]

private theorem aux_E_marginal (q : ℚ) (D T : Finset (Word N)) (hT : T ⊆ D)
    (g : Finset (Word N) → ℚ) (hg : ∀ S, g (S ∩ T) = g S) :
    aux_E q D g = aux_E q T g := by
  have hun : T ∪ (D \ T) = D := Finset.union_sdiff_of_subset hT
  have hdis : Disjoint T (D \ T) := Finset.disjoint_sdiff
  have h1 : aux_E q D g = aux_E q (T ∪ (D \ T)) (fun S => g S * (fun _ => (1 : ℚ)) S) := by
    rw [hun]
    exact aux_E_congr q D g _ fun S => by ring
  rw [h1, aux_E_split q T (D \ T) hdis g (fun _ => (1 : ℚ)) hg (fun _ => rfl),
    aux_E_one]
  ring

private theorem aux_faultyB_zero (N : ℕ) (D S : Finset (Word N)) (w : Word N) :
    faultyB N D S 0 w = decide (w ∈ S) := rfl

private theorem aux_faultyB_succ (N : ℕ) (D S : Finset (Word N)) (f : ℕ) (w : Word N) :
    faultyB N D S (f + 1) w =
      (decide (w ∈ S) ||
        decide (quorum N ≤ (childList D w).countP fun v => faultyB N D S f v)) := rfl

private theorem aux_faultyB_restrict (N : ℕ) (D : Finset (Word N))
    (_hp : ∀ u ∈ D, u ≠ [] → u.dropLast ∈ D) (S : Finset (Word N)) :
    ∀ (f : ℕ) (T : Finset (Word N)) (w : Word N), w ∈ D → aux_cone D w ⊆ T →
      faultyB N D (S ∩ T) f w = faultyB N D S f w := by
  intro f
  induction f with
  | zero =>
    intro T w hw hsub
    have hwT : w ∈ T := hsub (aux_cone_self hw)
    rw [aux_faultyB_zero, aux_faultyB_zero]
    simp [Finset.mem_inter, hwT]
  | succ f ih =>
    intro T w hw hsub
    have hwT : w ∈ T := hsub (aux_cone_self hw)
    have hcount : ((childList D w).countP fun v => faultyB N D (S ∩ T) f v)
        = ((childList D w).countP fun v => faultyB N D S f v) := by
      refine List.countP_congr fun v hv => ?_
      obtain ⟨hvD, d, rfl⟩ := mem_childList.mp hv
      rw [ih T (w ++ [d]) hvD
        ((aux_cone_mono (List.prefix_append w [d])).trans hsub)]
    rw [aux_faultyB_succ, aux_faultyB_succ, hcount]
    simp [Finset.mem_inter, hwT]

private theorem aux_pbGE_cons (k : ℕ) (p : ℚ) (ps : List ℚ) :
    pbGE (k + 1) (p :: ps) = p * pbGE k ps + (1 - p) * pbGE (k + 1) ps := rfl

private theorem aux_pb (q : ℚ) (N : ℕ) (D : Finset (Word N))
    (hp : ∀ u ∈ D, u ≠ [] → u.dropLast ∈ D) (f : ℕ) :
    ∀ L : List (Word N), (∀ v ∈ L, v ∈ D) →
      L.Pairwise (fun a b => Disjoint (aux_cone D a) (aux_cone D b)) →
      (∀ v ∈ L, aux_E q (aux_cone D v) (fun S => if faultyB N D S f v then (1 : ℚ) else 0)
          = pFailW q N D f v) →
      ∀ k : ℕ,
        aux_E q (aux_bigU D L)
            (fun S => if k ≤ L.countP (fun v => faultyB N D S f v) then (1 : ℚ) else 0)
          = pbGE k (L.map fun v => pFailW q N D f v) := by
  intro L
  induction L with
  | nil =>
    intro _ _ _ k
    show aux_E q ∅ _ = _
    rw [aux_E_empty]
    cases k with
    | zero => rw [aux_pbGE_zero]; simp
    | succ j => simp [pbGE]
  | cons v L' ih =>
    intro hLD hpair hval k
    have hvD : v ∈ D := hLD v (by simp)
    have hLD' : ∀ u ∈ L', u ∈ D := fun u hu => hLD u (by simp [hu])
    have hpc := List.pairwise_cons.mp hpair
    have hpair' : L'.Pairwise (fun a b => Disjoint (aux_cone D a) (aux_cone D b)) := hpc.2
    have hval' : ∀ u ∈ L',
        aux_E q (aux_cone D u) (fun S => if faultyB N D S f u then (1 : ℚ) else 0)
          = pFailW q N D f u := fun u hu => hval u (by simp [hu])
    have hdis : Disjoint (aux_cone D v) (aux_bigU D L') :=
      aux_bigU_disjoint fun u hu => hpc.1 u hu
    have hres1 : ∀ S : Finset (Word N),
        (if faultyB N D (S ∩ aux_cone D v) f v then (1 : ℚ) else 0)
          = (if faultyB N D S f v then (1 : ℚ) else 0) := fun S => by
      rw [aux_faultyB_restrict N D hp S f (aux_cone D v) v hvD (Finset.Subset.refl _)]
    have hres1' : ∀ S : Finset (Word N),
        (if faultyB N D (S ∩ aux_cone D v) f v then (0 : ℚ) else 1)
          = (if faultyB N D S f v then (0 : ℚ) else 1) := fun S => by
      rw [aux_faultyB_restrict N D hp S f (aux_cone D v) v hvD (Finset.Subset.refl _)]
    have hcount : ∀ S : Finset (Word N),
        (L'.countP fun u => faultyB N D (S ∩ aux_bigU D L') f u)
          = L'.countP fun u => faultyB N D S f u := fun S => by
      refine List.countP_congr fun u hu => ?_
      rw [aux_faultyB_restrict N D hp S f (aux_bigU D L') u (hLD' u hu)
        (aux_cone_subset_bigU hu)]
    have hneg : aux_E q (aux_cone D v) (fun S => if faultyB N D S f v then (0 : ℚ) else 1)
        = 1 - pFailW q N D f v := by
      have h1 : aux_E q (aux_cone D v) (fun S => if faultyB N D S f v then (0 : ℚ) else 1)
          = aux_E q (aux_cone D v)
              (fun S => (fun _ => (1 : ℚ)) S - (if faultyB N D S f v then (1 : ℚ) else 0)) :=
        aux_E_congr q _ _ _ fun S => by split <;> ring
      rw [h1, aux_E_sub, aux_E_one, hval v (by simp)]
    cases k with
    | zero =>
      rw [aux_pbGE_zero]
      have h0 : aux_E q (aux_bigU D (v :: L'))
          (fun S => if 0 ≤ (v :: L').countP (fun u => faultyB N D S f u) then (1 : ℚ) else 0)
          = aux_E q (aux_bigU D (v :: L')) (fun _ => (1 : ℚ)) :=
        aux_E_congr q _ _ _ fun S => by simp
      rw [h0, aux_E_one]
    | succ j =>
      have hsum : aux_E q (aux_bigU D (v :: L'))
          (fun S => if j + 1 ≤ (v :: L').countP (fun u => faultyB N D S f u)
            then (1 : ℚ) else 0)
          = aux_E q (aux_bigU D (v :: L'))
            (fun S =>
              (if faultyB N D S f v then (1 : ℚ) else 0)
                  * (if j ≤ L'.countP (fun u => faultyB N D S f u) then (1 : ℚ) else 0)
                + (if faultyB N D S f v then (0 : ℚ) else 1)
                  * (if j + 1 ≤ L'.countP (fun u => faultyB N D S f u)
                      then (1 : ℚ) else 0)) := by
        refine aux_E_congr q _ _ _ fun S => ?_
        rw [List.countP_cons]
        by_cases hv : faultyB N D S f v = true
        · rw [hv]
          simp
        · have hv' : faultyB N D S f v = false := by simpa using hv
          rw [hv']
          simp
      rw [hsum]
      show aux_E q (aux_cone D v ∪ aux_bigU D L') _ = _
      rw [aux_E_add q (aux_cone D v ∪ aux_bigU D L')
          (fun S => (if faultyB N D S f v then (1 : ℚ) else 0)
            * (if j ≤ L'.countP (fun u => faultyB N D S f u) then (1 : ℚ) else 0))
          (fun S => (if faultyB N D S f v then (0 : ℚ) else 1)
            * (if j + 1 ≤ L'.countP (fun u => faultyB N D S f u) then (1 : ℚ) else 0)),
        aux_E_split q (aux_cone D v) (aux_bigU D L') hdis
          (fun S => if faultyB N D S f v then (1 : ℚ) else 0)
          (fun S => if j ≤ L'.countP (fun u => faultyB N D S f u) then (1 : ℚ) else 0)
          hres1 (fun S => by rw [hcount S]),
        aux_E_split q (aux_cone D v) (aux_bigU D L') hdis
          (fun S => if faultyB N D S f v then (0 : ℚ) else 1)
          (fun S => if j + 1 ≤ L'.countP (fun u => faultyB N D S f u) then (1 : ℚ) else 0)
          hres1' (fun S => by rw [hcount S]),
        hval v (by simp), hneg, ih hLD' hpair' hval' j, ih hLD' hpair' hval' (j + 1),
        List.map_cons, aux_pbGE_cons]

private theorem aux_key (q : ℚ) (N : ℕ) (D : Finset (Word N))
    (hp : ∀ u ∈ D, u ≠ [] → u.dropLast ∈ D) :
    ∀ (f : ℕ) (w : Word N), w ∈ D →
      aux_E q (aux_cone D w) (fun S => if faultyB N D S f w then (1 : ℚ) else 0)
        = pFailW q N D f w := by
  intro f
  induction f with
  | zero =>
    intro w hw
    have hsub : ({w} : Finset (Word N)) ⊆ aux_cone D w :=
      Finset.singleton_subset_iff.mpr (aux_cone_self hw)
    have hg : ∀ S : Finset (Word N),
        (if faultyB N D (S ∩ {w}) 0 w then (1 : ℚ) else 0)
          = (if faultyB N D S 0 w then (1 : ℚ) else 0) := by
      intro S
      rw [aux_faultyB_zero, aux_faultyB_zero]
      simp
    rw [aux_E_marginal q (aux_cone D w) {w} hsub _ hg, aux_E_point, aux_pFailW_zero]
    simp [aux_faultyB_zero]
  | succ f ih =>
    intro w hw
    have hLD : ∀ v ∈ childList D w, v ∈ D := fun v hv => (mem_childList.mp hv).1
    have hwU : w ∉ aux_bigU D (childList D w) := by
      intro hmem
      obtain ⟨u, hu, huw⟩ := aux_mem_bigU.mp hmem
      obtain ⟨_, d, rfl⟩ := mem_childList.mp hu
      have hlen := (aux_mem_cone.mp huw).2.length_le
      simp at hlen
    have hdisj : Disjoint ({w} : Finset (Word N)) (aux_bigU D (childList D w)) :=
      Finset.disjoint_singleton_left.mpr hwU
    have hdecomp : aux_cone D w = {w} ∪ aux_bigU D (childList D w) := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro u hu
        obtain ⟨huD, hpre⟩ := aux_mem_cone.mp hu
        rcases eq_or_ne u w with rfl | hne
        · exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
        · obtain ⟨t, rfl⟩ := hpre
          cases t with
          | nil => simp at hne
          | cons d t' =>
            have hpd : w ++ [d] <+: w ++ d :: t' := ⟨t', by simp⟩
            have hchild : w ++ [d] ∈ D := aux_prefix_mem hp huD hpd
            refine Finset.mem_union_right _
              (aux_cone_subset_bigU (mem_childList.mpr ⟨hchild, d, rfl⟩) ?_)
            exact aux_mem_cone.mpr ⟨huD, hpd⟩
      · refine Finset.union_subset ?_ ?_
        · exact Finset.singleton_subset_iff.mpr (aux_cone_self hw)
        · intro u hu
          obtain ⟨z, hz, hzu⟩ := aux_mem_bigU.mp hu
          obtain ⟨_, d, rfl⟩ := mem_childList.mp hz
          exact aux_cone_mono (List.prefix_append w [d]) hzu
    have hnodup : (childList D w).Nodup := by
      rw [childList]
      refine List.Nodup.filterMap ?_ (List.nodup_finRange N)
      intro a a' b hb hb'
      simp only [Option.mem_def] at hb hb'
      have h1 : w ++ [a] = b := by
        by_cases ha : w ++ [a] ∈ D
        · rw [if_pos ha] at hb
          exact Option.some_inj.mp hb
        · rw [if_neg ha] at hb
          exact absurd hb (by simp)
      have h2 : w ++ [a'] = b := by
        by_cases ha : w ++ [a'] ∈ D
        · rw [if_pos ha] at hb'
          exact Option.some_inj.mp hb'
        · rw [if_neg ha] at hb'
          exact absurd hb' (by simp)
      have h3 : w ++ [a] = w ++ [a'] := h1.trans h2.symm
      simpa using h3
    have hpair : (childList D w).Pairwise
        (fun a b => Disjoint (aux_cone D a) (aux_cone D b)) := by
      refine hnodup.imp_of_mem ?_
      intro a b ha hb hne
      obtain ⟨_, d, rfl⟩ := mem_childList.mp ha
      obtain ⟨_, e, rfl⟩ := mem_childList.mp hb
      refine Finset.disjoint_left.mpr fun z hz hz' => ?_
      have p1 := (aux_mem_cone.mp hz).2
      have p2 := (aux_mem_cone.mp hz').2
      refine hne ?_
      rcases List.prefix_or_prefix_of_prefix p1 p2 with h | h
      · exact h.eq_of_length (by simp)
      · exact (h.eq_of_length (by simp)).symm
    have hpb := aux_pb q N D hp f (childList D w) hLD hpair
      (fun v hv => ih v (hLD v hv)) (quorum N)
    have hind : aux_E q (aux_cone D w)
        (fun S => if faultyB N D S (f + 1) w then (1 : ℚ) else 0)
        = aux_E q (aux_cone D w)
          (fun S =>
            (if w ∈ S then (1 : ℚ) else 0) * (fun _ => (1 : ℚ)) S
              + (if w ∈ S then (0 : ℚ) else 1)
                * (if quorum N ≤ (childList D w).countP (fun v => faultyB N D S f v)
                    then (1 : ℚ) else 0)) := by
      refine aux_E_congr q _ _ _ fun S => ?_
      rw [aux_faultyB_succ]
      by_cases hS : w ∈ S
      · simp [hS]
      · simp [hS]
    have hA2 : ∀ S : Finset (Word N),
        (fun _ => (1 : ℚ)) (S ∩ aux_bigU D (childList D w)) = (fun _ => (1 : ℚ)) S :=
      fun _ => rfl
    have hA1 : ∀ S : Finset (Word N),
        (if w ∈ S ∩ ({w} : Finset (Word N)) then (1 : ℚ) else 0)
          = (if w ∈ S then (1 : ℚ) else 0) := fun S => by simp
    have hB1 : ∀ S : Finset (Word N),
        (if w ∈ S ∩ ({w} : Finset (Word N)) then (0 : ℚ) else 1)
          = (if w ∈ S then (0 : ℚ) else 1) := fun S => by simp
    have hB2 : ∀ S : Finset (Word N),
        (if quorum N ≤ (childList D w).countP
            (fun v => faultyB N D (S ∩ aux_bigU D (childList D w)) f v) then (1 : ℚ) else 0)
          = (if quorum N ≤ (childList D w).countP (fun v => faultyB N D S f v)
              then (1 : ℚ) else 0) := fun S => by
      have : ((childList D w).countP
          fun v => faultyB N D (S ∩ aux_bigU D (childList D w)) f v)
          = (childList D w).countP fun v => faultyB N D S f v := by
        refine List.countP_congr fun v hv => ?_
        rw [aux_faultyB_restrict N D hp S f (aux_bigU D (childList D w)) v (hLD v hv)
          (aux_cone_subset_bigU hv)]
      rw [this]
    rw [hind, hdecomp,
      aux_E_add q ({w} ∪ aux_bigU D (childList D w))
        (fun S => (if w ∈ S then (1 : ℚ) else 0) * (fun _ => (1 : ℚ)) S)
        (fun S => (if w ∈ S then (0 : ℚ) else 1)
          * (if quorum N ≤ (childList D w).countP (fun v => faultyB N D S f v)
              then (1 : ℚ) else 0)),
      aux_E_split q {w} (aux_bigU D (childList D w)) hdisj
        (fun S => if w ∈ S then (1 : ℚ) else 0) (fun _ => (1 : ℚ)) hA1 hA2,
      aux_E_split q {w} (aux_bigU D (childList D w)) hdisj
        (fun S => if w ∈ S then (0 : ℚ) else 1)
        (fun S => if quorum N ≤ (childList D w).countP (fun v => faultyB N D S f v)
            then (1 : ℚ) else 0) hB1 hB2,
      aux_E_one, aux_E_point, aux_E_point, hpb, aux_pFailW_succ]
    simp

set_option linter.unusedVariables false in
/-- **Item 2, exact evaluation.** The bottom-up recursion computes `R(x)` exactly on every
well-formed configuration. -/
theorem exact_recursion (q : ℚ) (N m : ℕ) (hN : 1 ≤ N) (x : Config N m) (hx : x.WF) :
    Rel q N m x = Rrec q N m x := by
  have hfail : pSeedFail q N m x
      = aux_E q x.D (fun S => if faultyB N x.D S m [] then (1 : ℚ) else 0) := by
    unfold pSeedFail aux_E
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [← aux_wt_eq_patWeight q x.D S (Finset.mem_powerset.mp hS)]
    dsimp only
    by_cases hb : faultyB N x.D S m [] = true
    · rw [if_pos hb, if_pos hb]
      ring
    · rw [if_neg hb, if_neg hb]
      ring
  have hk := aux_key q N x.D hx.2.2.1 m [] hx.1
  rw [aux_cone_nil] at hk
  rw [Rel, Rrec, hfail, hk]

/-- The fault predicate has bottomed out once the fuel exceeds the remaining depth: a cell
with no deployed children is faulty iff its internal consensus fails, so resolving one level
deeper changes nothing. -/
theorem faultyB_fuel_stable (N : ℕ) (hN : 1 ≤ N) (D S : Finset (Word N)) (f : ℕ)
    (w : Word N) (h : ∀ v ∈ D, v.length ≤ w.length + f) :
    faultyB N D S (f + 1) w = faultyB N D S f w := by
  induction f generalizing w with
  | zero =>
    obtain ⟨j, hj⟩ := aux_quorum_pos hN
    have hnil : childList D w = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro v hv
      obtain ⟨hvD, d, rfl⟩ := mem_childList.mp hv
      have hlen := h _ hvD
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    rw [aux_faultyB_succ, aux_faultyB_zero, hnil, hj]
    simp
  | succ f ih =>
    have hcount : ((childList D w).countP fun v => faultyB N D S (f + 1) v)
        = ((childList D w).countP fun v => faultyB N D S f v) := by
      refine List.countP_congr fun v hv => ?_
      obtain ⟨hvD, d, rfl⟩ := mem_childList.mp hv
      rw [ih (w ++ [d]) (fun u hu => ?_)]
      have hlen := h u hu
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [aux_faultyB_succ, aux_faultyB_succ, hcount]

/-- **Adequacy of the fuel bound in `pSeedFail`.** On a well-formed configuration the
depth-`m` resolution of `faultyB` at the seed is already the fixed point: no amount of extra
fuel changes it. So `Rel` really is the paper's `R(x)` and not a depth-`m` truncation of
it. -/
theorem faultyB_seed_stable {N m : ℕ} (hN : 1 ≤ N) (x : Config N m) (hx : x.WF)
    (S : Finset (Word N)) (f : ℕ) (hf : m ≤ f) :
    faultyB N x.D S f [] = faultyB N x.D S m [] := by
  induction f, hf using Nat.le_induction with
  | base => rfl
  | succ f hf ih =>
    rw [faultyB_fuel_stable N hN x.D S f [] (fun v hv => ?_), ih]
    have := hx.2.1 v hv
    simp only [List.length_nil, Nat.zero_add]
    omega

/-! ## The tier profile -/

/-- The deployed cells at index `t`, that is of tier `t + 1`. -/
def tierCells (D : Finset (Word N)) (t : ℕ) : Finset (Word N) := D.filter fun w => w.length = t

/-- The per-tier cell count. -/
def tierCount (D : Finset (Word N)) (t : ℕ) : ℕ := (tierCells D t).card

/-- The tier profile at index `t`: the multiset of deployed-child counts of the cells of that
tier. Its cardinality is the per-tier cell count, so this single datum carries both halves of
the profile of prop:rel-exact. -/
def profile (D : Finset (Word N)) (t : ℕ) : Multiset ℕ := (tierCells D t).val.map (childCount D)

theorem tierCount_eq_card_profile (D : Finset (Word N)) (t : ℕ) :
    tierCount D t = Multiset.card (profile D t) := by
  rw [profile, Multiset.card_map]
  rfl

/-- The per-tier occupancy histogram `o_t` of prop:kpi-affine, read as a multiset: over the
deployed cells of tier `t + 1`, the number of their `N` member slots that are occupied. -/
def occProfile (x : Config N m) (t : ℕ) : Multiset ℕ :=
  (tierCells x.D t).val.map fun w => (cellW w ∩ x.μ).card

/-- The per-tier occupied-slot total `M1(o_t)`: how many occupied slots sit at each tier. -/
def occCount (x : Config N m) (t : ℕ) : ℕ := (x.μ.filter fun s => s.length = t).card

/-! ## Item 1: the witness pair at `N = 3`, `q = 1/5`

All cells are deployed through tier 3 (`1 + 3 + 9` cells) and three tier-3 cells are fully
expanded (`9` tier-4 cells). In `Dspread` the three heavy cells are `[d, 0]` for `d : Fin 3`,
one per tier-2 branch; in `Dconc` they are `[0, e]` for `e : Fin 3`, all three under the
branch `[0]`. Every slot is occupied and nothing is decommissioned. -/

/-- All cells through tier 3: the seed, the three tier-2 cells and the nine tier-3 cells. -/
def baseD : Finset (Word 3) :=
  {[]} ∪ (Finset.univ.image fun d : Fin 3 => [d]) ∪
    (Finset.univ.image fun p : Fin 3 × Fin 3 => [p.1, p.2])

/-- The spread deployment: the three heavy tier-3 cells are `[0,0]`, `[1,0]`, `[2,0]`, one
per tier-2 branch. -/
def Dspread : Finset (Word 3) :=
  baseD ∪ Finset.univ.image fun p : Fin 3 × Fin 3 => [p.1, 0, p.2]

/-- The concentrated deployment: the three heavy tier-3 cells are `[0,0]`, `[0,1]`, `[0,2]`,
all under the tier-2 branch `[0]`. -/
def Dconc : Finset (Word 3) :=
  baseD ∪ Finset.univ.image fun p : Fin 3 × Fin 3 => [0, p.1, p.2]

/-- The spread configuration, fully occupied. -/
def xS : Config 3 4 := ⟨Dspread, Dspread.biUnion cellW, ∅⟩

/-- The concentrated configuration, fully occupied. -/
def xC : Config 3 4 := ⟨Dconc, Dconc.biUnion cellW, ∅⟩

theorem xS_wf : xS.WF := by
  refine ⟨by decide, by decide, by decide, Finset.Subset.refl _, ?_, ?_⟩
  · exact Finset.empty_subset _
  · rw [show xS.ζ = (⊥ : Finset (Word 3)) from rfl]
    exact disjoint_bot_left

theorem xC_wf : xC.WF := by
  refine ⟨by decide, by decide, by decide, Finset.Subset.refl _, ?_, ?_⟩
  · exact Finset.empty_subset _
  · rw [show xC.ζ = (⊥ : Finset (Word 3)) from rfl]
    exact disjoint_bot_left

/-- Both configurations have every slot occupied. -/
theorem xS_full : xS.μ = xS.Sl := rfl

theorem xC_full : xC.μ = xC.Sl := rfl

theorem card_Dspread : Dspread.card = 22 := by decide

theorem card_Dconc : Dconc.card = 22 := by decide

/-! ### The intermediate values of the recursion -/

/-- A heavy tier-3 cell (three deployed children, each of failure probability `q = 1/5`):
`1/5 + (4/5) * Pr[Bin(3, 1/5) ≥ 2] = 177/625 = 0.2832`. -/
private theorem aux_pbGE2_three (a b c : ℚ) :
    pbGE 2 [a, b, c] = a * (b + (1 - b) * c) + (1 - a) * (b * c) := by
  simp only [pbGE]
  ring

private theorem aux_cl_S3 : ∀ d e : Fin 3, childList Dspread [d, 0, e] = [] := by decide

private theorem aux_cl_S2h : ∀ d : Fin 3,
    childList Dspread [d, 0] = [[d, 0, 0], [d, 0, 1], [d, 0, 2]] := by decide

private theorem aux_cl_S2l1 : ∀ d : Fin 3, childList Dspread [d, 1] = [] := by decide

private theorem aux_cl_S2l2 : ∀ d : Fin 3, childList Dspread [d, 2] = [] := by decide

private theorem aux_cl_S1 : ∀ d : Fin 3,
    childList Dspread [d] = [[d, 0], [d, 1], [d, 2]] := by decide

private theorem aux_cl_S0 : childList Dspread [] = [[0], [1], [2]] := by decide

private theorem aux_pfS3 (f : ℕ) (d e : Fin 3) :
    pFailW (1 / 5) 3 Dspread f [d, 0, e] = 1 / 5 :=
  pFailW_of_childList_nil _ _ (by norm_num) _ _ _ (aux_cl_S3 d e)

private theorem aux_pfS2l1 (f : ℕ) (d : Fin 3) :
    pFailW (1 / 5) 3 Dspread f [d, 1] = 1 / 5 :=
  pFailW_of_childList_nil _ _ (by norm_num) _ _ _ (aux_cl_S2l1 d)

private theorem aux_pfS2l2 (f : ℕ) (d : Fin 3) :
    pFailW (1 / 5) 3 Dspread f [d, 2] = 1 / 5 :=
  pFailW_of_childList_nil _ _ (by norm_num) _ _ _ (aux_cl_S2l2 d)

private theorem aux_pfS2h (f : ℕ) (d : Fin 3) :
    pFailW (1 / 5) 3 Dspread (f + 1) [d, 0] = 177 / 625 := by
  have hhom : ∀ v ∈ childList Dspread [d, 0], pFailW (1 / 5) 3 Dspread f v = 1 / 5 := by
    rw [aux_cl_S2h d]
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact aux_pfS3 f d 0
    · exact aux_pfS3 f d 1
    · exact aux_pfS3 f d 2
  have hc : childCount Dspread [d, 0] = 3 := by
    rw [childCount, aux_cl_S2h d]
    rfl
  rw [pFailW_of_homogeneous (1 / 5) 3 Dspread f [d, 0] (1 / 5) hhom, hc, step_heavy]

private theorem aux_pfS1 (f : ℕ) (d : Fin 3) :
    pFailW (1 / 5) 3 Dspread (f + 2) [d] = 23789 / 78125 := by
  rw [aux_pFailW_succ, aux_cl_S1 d]
  simp only [List.map_cons, List.map_nil]
  rw [aux_pfS2h f d, aux_pfS2l1 (f + 1) d, aux_pfS2l2 (f + 1) d, quorum_three,
    aux_pbGE2_three]
  norm_num

private theorem aux_pfS0 (f : ℕ) :
    pFailW (1 / 5) 3 Dspread (f + 3) [] = 899683191696073 / 2384185791015625 := by
  rw [aux_pFailW_succ, aux_cl_S0]
  simp only [List.map_cons, List.map_nil]
  rw [aux_pfS1 f 0, aux_pfS1 f 1, aux_pfS1 f 2, quorum_three, aux_pbGE2_three]
  norm_num

theorem pFail_heavy : pFailW (1 / 5) 3 Dspread 1 [0, 0] = 177 / 625 := aux_pfS2h 0 0

/-- A light tier-3 cell has no deployed children, so it fails only internally. -/
theorem pFail_light : pFailW (1 / 5) 3 Dspread 1 [0, 1] = 1 / 5 := aux_pfS2l1 1 0

/-- A spread tier-2 branch, with children of failure probabilities `(177/625, 1/5, 1/5)`:
a genuinely Poisson binomial, not a binomial, tail. -/
theorem pFail_branch_spread : pFailW (1 / 5) 3 Dspread 2 [0] = 23789 / 78125 := aux_pfS1 0 0

/-- The loaded tier-2 branch of the concentrated deployment, three heavy children. -/
private theorem aux_cl_C3 : ∀ e f : Fin 3, childList Dconc [0, e, f] = [] := by decide

private theorem aux_cl_C2h : ∀ e : Fin 3,
    childList Dconc [0, e] = [[0, e, 0], [0, e, 1], [0, e, 2]] := by decide

private theorem aux_cl_C2l1 : ∀ e : Fin 3, childList Dconc [1, e] = [] := by decide

private theorem aux_cl_C2l2 : ∀ e : Fin 3, childList Dconc [2, e] = [] := by decide

private theorem aux_cl_C1 : ∀ d : Fin 3,
    childList Dconc [d] = [[d, 0], [d, 1], [d, 2]] := by decide

private theorem aux_cl_C0 : childList Dconc [] = [[0], [1], [2]] := by decide

private theorem aux_pfC3 (f : ℕ) (e g : Fin 3) :
    pFailW (1 / 5) 3 Dconc f [0, e, g] = 1 / 5 :=
  pFailW_of_childList_nil _ _ (by norm_num) _ _ _ (aux_cl_C3 e g)

private theorem aux_pfC2l1 (f : ℕ) (e : Fin 3) :
    pFailW (1 / 5) 3 Dconc f [1, e] = 1 / 5 :=
  pFailW_of_childList_nil _ _ (by norm_num) _ _ _ (aux_cl_C2l1 e)

private theorem aux_pfC2l2 (f : ℕ) (e : Fin 3) :
    pFailW (1 / 5) 3 Dconc f [2, e] = 1 / 5 :=
  pFailW_of_childList_nil _ _ (by norm_num) _ _ _ (aux_cl_C2l2 e)

private theorem aux_pfC2h (f : ℕ) (e : Fin 3) :
    pFailW (1 / 5) 3 Dconc (f + 1) [0, e] = 177 / 625 := by
  have hhom : ∀ v ∈ childList Dconc [0, e], pFailW (1 / 5) 3 Dconc f v = 1 / 5 := by
    rw [aux_cl_C2h e]
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact aux_pfC3 f e 0
    · exact aux_pfC3 f e 1
    · exact aux_pfC3 f e 2
  have hc : childCount Dconc [0, e] = 3 := by
    rw [childCount, aux_cl_C2h e]
    rfl
  rw [pFailW_of_homogeneous (1 / 5) 3 Dconc f [0, e] (1 / 5) hhom, hc, step_heavy]

private theorem aux_pfC1h (f : ℕ) :
    pFailW (1 / 5) 3 Dconc (f + 2) [0] = 434746261 / 1220703125 := by
  have hhom : ∀ v ∈ childList Dconc [0], pFailW (1 / 5) 3 Dconc (f + 1) v = 177 / 625 := by
    rw [aux_cl_C1 0]
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact aux_pfC2h f 0
    · exact aux_pfC2h f 1
    · exact aux_pfC2h f 2
  have hc : childCount Dconc [0] = 3 := by
    rw [childCount, aux_cl_C1 0]
    rfl
  rw [pFailW_of_homogeneous (1 / 5) 3 Dconc (f + 1) [0] (177 / 625) hhom, hc,
    step_branch_conc]

private theorem aux_pfC1l1 (f : ℕ) : pFailW (1 / 5) 3 Dconc (f + 2) [1] = 177 / 625 := by
  have hhom : ∀ v ∈ childList Dconc [1], pFailW (1 / 5) 3 Dconc (f + 1) v = 1 / 5 := by
    rw [aux_cl_C1 1]
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact aux_pfC2l1 (f + 1) 0
    · exact aux_pfC2l1 (f + 1) 1
    · exact aux_pfC2l1 (f + 1) 2
  have hc : childCount Dconc [1] = 3 := by
    rw [childCount, aux_cl_C1 1]
    rfl
  rw [pFailW_of_homogeneous (1 / 5) 3 Dconc (f + 1) [1] (1 / 5) hhom, hc, step_heavy]

private theorem aux_pfC1l2 (f : ℕ) : pFailW (1 / 5) 3 Dconc (f + 2) [2] = 177 / 625 := by
  have hhom : ∀ v ∈ childList Dconc [2], pFailW (1 / 5) 3 Dconc (f + 1) v = 1 / 5 := by
    rw [aux_cl_C1 2]
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact aux_pfC2l2 (f + 1) 0
    · exact aux_pfC2l2 (f + 1) 1
    · exact aux_pfC2l2 (f + 1) 2
  have hc : childCount Dconc [2] = 3 := by
    rw [childCount, aux_cl_C1 2]
    rfl
  rw [pFailW_of_homogeneous (1 / 5) 3 Dconc (f + 1) [2] (1 / 5) hhom, hc, step_heavy]

private theorem aux_pfC0 (f : ℕ) :
    pFailW (1 / 5) 3 Dconc (f + 3) [] = 905599907113673 / 2384185791015625 := by
  rw [aux_pFailW_succ, aux_cl_C0]
  simp only [List.map_cons, List.map_nil]
  rw [aux_pfC1h f, aux_pfC1l1 f, aux_pfC1l2 f, quorum_three, aux_pbGE2_three]
  norm_num

theorem pFail_branch_conc_heavy :
    pFailW (1 / 5) 3 Dconc 2 [0] = 434746261 / 1220703125 := aux_pfC1h 0

/-- The two empty tier-2 branches of the concentrated deployment, three light children. -/
theorem pFail_branch_conc_light : pFailW (1 / 5) 3 Dconc 2 [1] = 177 / 625 := aux_pfC1l1 0

/-! ### The two reliabilities -/

/-- `R = 1484502599319552 / 2384185791015625 = 0.6226455…`, the paper's `0.6226`. -/
theorem Rrec_spread : Rrec (1 / 5) 3 4 xS = 1484502599319552 / 2384185791015625 := by
  have h : pFailW (1 / 5) 3 Dspread 4 [] = 899683191696073 / 2384185791015625 := aux_pfS0 1
  show (1 : ℚ) - pFailW (1 / 5) 3 Dspread 4 [] = 1484502599319552 / 2384185791015625
  rw [h]
  norm_num

/-- `R = 1478585883901952 / 2384185791015625 = 0.6201638…`, the paper's `0.6202`. -/
theorem Rrec_conc : Rrec (1 / 5) 3 4 xC = 1478585883901952 / 2384185791015625 := by
  have h : pFailW (1 / 5) 3 Dconc 4 [] = 905599907113673 / 2384185791015625 := aux_pfC0 1
  show (1 : ℚ) - pFailW (1 / 5) 3 Dconc 4 [] = 1478585883901952 / 2384185791015625
  rw [h]
  norm_num

theorem Rrec_spread_round : |Rrec (1 / 5) 3 4 xS - 6226 / 10000| < 1 / 10000 := by
  rw [Rrec_spread, abs_lt]
  norm_num

theorem Rrec_conc_round : |Rrec (1 / 5) 3 4 xC - 6202 / 10000| < 1 / 10000 := by
  rw [Rrec_conc, abs_lt]
  norm_num

/-- The two configurations do not have the same reliability. -/
theorem Rrec_ne : Rrec (1 / 5) 3 4 xS ≠ Rrec (1 / 5) 3 4 xC := by
  rw [Rrec_spread, Rrec_conc]
  norm_num

/-- The balanced allocation is the more reliable one, the design rule the profile cannot
see. -/
theorem Rrec_conc_lt_spread : Rrec (1 / 5) 3 4 xC < Rrec (1 / 5) 3 4 xS := by
  rw [Rrec_spread, Rrec_conc]
  norm_num

/-- The same two values for the model itself, through `exact_recursion`. -/
theorem Rel_spread : Rel (1 / 5) 3 4 xS = 1484502599319552 / 2384185791015625 := by
  rw [exact_recursion (1 / 5) 3 4 (by norm_num) xS xS_wf, Rrec_spread]

theorem Rel_conc : Rel (1 / 5) 3 4 xC = 1478585883901952 / 2384185791015625 := by
  rw [exact_recursion (1 / 5) 3 4 (by norm_num) xC xC_wf, Rrec_conc]

theorem Rel_ne : Rel (1 / 5) 3 4 xS ≠ Rel (1 / 5) 3 4 xC := by
  rw [Rel_spread, Rel_conc]
  norm_num

/-- The paper's design rule, on the model itself: the balanced allocation is the more
reliable member of the pinned pair. -/
theorem Rel_conc_lt_spread : Rel (1 / 5) 3 4 xC < Rel (1 / 5) 3 4 xS := by
  rw [Rel_spread, Rel_conc]
  norm_num

/-! ### Yet the profiles agree -/

/-- Per-tier cell counts `(1, 3, 9, 9)`, and nothing below tier 4. -/
private theorem aux_len_spread : ∀ w ∈ Dspread, w.length ≤ 3 := by decide

private theorem aux_len_conc : ∀ w ∈ Dconc, w.length ≤ 3 := by decide

private theorem aux_tc_empty_S (n : ℕ) : tierCells Dspread (n + 4) = ∅ := by
  rw [tierCells, Finset.filter_eq_empty_iff]
  intro w hw
  have h := aux_len_spread w hw
  omega

private theorem aux_tc_empty_C (n : ℕ) : tierCells Dconc (n + 4) = ∅ := by
  rw [tierCells, Finset.filter_eq_empty_iff]
  intro w hw
  have h := aux_len_conc w hw
  omega

theorem tierCount_spread (t : ℕ) : tierCount Dspread t = [1, 3, 9, 9].getD t 0 := by
  match t with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | (n + 4) =>
    rw [tierCount, aux_tc_empty_S n, Finset.card_empty]
    simp

theorem tierCount_conc (t : ℕ) : tierCount Dconc t = [1, 3, 9, 9].getD t 0 := by
  match t with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | (n + 4) =>
    rw [tierCount, aux_tc_empty_C n, Finset.card_empty]
    simp

/-- The tier-2 anchoring histogram: three cells, three children each. -/
theorem profile_spread_one : profile Dspread 1 = {3, 3, 3} := by decide

/-- The tier-3 anchoring histogram: three heavy cells and six childless ones, in both
deployments. -/
theorem profile_spread_two : profile Dspread 2 = {3, 3, 3, 0, 0, 0, 0, 0, 0} := by decide

theorem profile_conc_two : profile Dconc 2 = {3, 3, 3, 0, 0, 0, 0, 0, 0} := by decide

/-- **The two deployments have the same tier profile at every tier.** -/
theorem profile_eq (t : ℕ) : profile Dspread t = profile Dconc t := by
  match t with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | (n + 4) =>
    rw [profile, profile, aux_tc_empty_S n, aux_tc_empty_C n]
    simp

/-- **and the same per-tier occupancy histogram**: every deployed cell of either
configuration has all three of its member slots occupied. -/
theorem occProfile_eq (t : ℕ) : occProfile xS t = occProfile xC t := by
  match t with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | (n + 4) =>
    show (tierCells Dspread (n + 4)).val.map _ = (tierCells Dconc (n + 4)).val.map _
    rw [aux_tc_empty_S n, aux_tc_empty_C n]
    simp

/-- and hence the same number of occupied slots at each tier. -/
private theorem aux_len_mu_S : ∀ s ∈ xS.μ, s.length ≤ 4 := by decide

private theorem aux_len_mu_C : ∀ s ∈ xC.μ, s.length ≤ 4 := by decide

theorem occ_eq (t : ℕ) : occCount xS t = occCount xC t := by
  match t with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | (n + 5) =>
    have hS : xS.μ.filter (fun s => s.length = n + 5) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro w hw
      have h := aux_len_mu_S w hw
      omega
    have hC : xC.μ.filter (fun s => s.length = n + 5) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro w hw
      have h := aux_len_mu_C w hw
      omega
    rw [occCount, occCount, hS, hC]

/-! ## Item 1: the conclusion -/

/-- **Item 1, the witness pair.** Two well-formed, fully occupied configurations agreeing on
the whole tier profile — the anchoring histograms `h_t` (whose cardinalities are the cell
counts `M0_t`) and the occupancy histograms `o_t` — yet of different reliability. -/
theorem profile_blind :
    ∃ x y : Config 3 4,
      x.WF ∧ y.WF ∧ x.μ = x.Sl ∧ y.μ = y.Sl ∧
        (∀ t, profile x.D t = profile y.D t) ∧
        (∀ t, occProfile x t = occProfile y t) ∧
        (∀ t, occCount x t = occCount y t) ∧
        Rel (1 / 5) 3 4 x ≠ Rel (1 / 5) 3 4 y :=
  ⟨xS, xC, xS_wf, xC_wf, xS_full, xC_full, profile_eq, occProfile_eq, occ_eq, Rel_ne⟩

/-- **Item 1, no profile formula.** No function whatsoever of the *full* tier profile — the
anchoring histograms and the occupancy histograms together, hence also the per-tier cell
counts, which are their cardinalities — computes the reliability, even on the well-formed
fully occupied configurations of one fixed family member at one fixed `q`. -/
theorem no_profile_formula :
    ¬ ∃ F : (ℕ → Multiset ℕ) → (ℕ → Multiset ℕ) → ℚ,
        ∀ x : Config 3 4, x.WF → x.μ = x.Sl →
          Rel (1 / 5) 3 4 x = F (profile x.D) (occProfile x) := by
  rintro ⟨F, hF⟩
  have h1 := hF xS xS_wf xS_full
  have h2 := hF xC xC_wf xC_full
  have hp : profile xS.D = profile xC.D := funext profile_eq
  have ho : occProfile xS = occProfile xC := funext occProfile_eq
  exact Rel_ne (by rw [h1, h2, hp, ho])

/-- **Item 1, a fortiori not affine.** The reliability is not an affine functional of the
tier profile: no constant plus a weighted sum of the histogram bins `h_t(k)` and `o_t(k)`
reproduces it. This is the sense in which prop:kpi-affine's four indicators, all affine in the
profile, have no reliability counterpart. -/
theorem no_affine_profile_formula :
    ¬ ∃ (c : ℚ) (α β : ℕ → ℕ → ℚ),
        ∀ x : Config 3 4, x.WF → x.μ = x.Sl →
          Rel (1 / 5) 3 4 x =
            c + ∑ t ∈ Finset.range 4, ∑ k ∈ Finset.range 4,
              (α t k * ((profile x.D t).count k : ℚ) + β t k * ((occProfile x t).count k : ℚ)) := by
  rintro ⟨c, α, β, h⟩
  have h1 := h xS xS_wf xS_full
  have h2 := h xC xC_wf xC_full
  have hp : ∀ t, profile xS.D t = profile xC.D t := profile_eq
  have ho : ∀ t, occProfile xS t = occProfile xC t := occProfile_eq
  have hterm : ∀ t ∈ Finset.range 4,
      (∑ k ∈ Finset.range 4, (α t k * ((profile xS.D t).count k : ℚ)
          + β t k * ((occProfile xS t).count k : ℚ)))
        = ∑ k ∈ Finset.range 4, (α t k * ((profile xC.D t).count k : ℚ)
          + β t k * ((occProfile xC t).count k : ℚ)) := by
    intro t _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hp t, ho t]
  exact Rel_ne (by rw [h1, h2, Finset.sum_congr rfl hterm])

/-- In particular the reliability is not an affine function of the per-tier cell counts
alone. -/
theorem no_affine_tier_formula :
    ¬ ∃ (c : ℚ) (a : ℕ → ℚ),
        ∀ x : Config 3 4, x.WF → x.μ = x.Sl →
          Rel (1 / 5) 3 4 x = c + ∑ t ∈ Finset.range 4, a t * (tierCount x.D t : ℚ) := by
  rintro ⟨c, a, h⟩
  have h1 := h xS xS_wf xS_full
  have h2 := h xC xC_wf xC_full
  have ht : ∀ t, tierCount xS.D t = tierCount xC.D t := fun t => by
    rw [show tierCount xS.D t = tierCount Dspread t from rfl, tierCount_spread,
      show tierCount xC.D t = tierCount Dconc t from rfl, tierCount_conc]
  have hterm : ∀ t ∈ Finset.range 4,
      a t * (tierCount xS.D t : ℚ) = a t * (tierCount xC.D t : ℚ) := by
    intro t _
    rw [ht t]
  exact Rel_ne (by rw [h1, h2, Finset.sum_congr rfl hterm])

end RelExact

end HSFN
