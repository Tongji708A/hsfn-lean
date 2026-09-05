/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Threshold
import Hsfnlean.ThresholdMono

/-!
# Failure recursion along the cell tree (Theorem thm:security)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409),
Section "Faulty Probability Determined (FPD) Model", Theorem `thm:security`
("Failure recursion"), together with the displays `eq:P-leaf`, `eq:P-intermediate`
and `eq:P-root`.

Setting: a cell tree of depth `m` in which every cell has `N` members and every
cell at level `k` (`k = 1` the root, `k = m` the leaves) has `b k` children for
`1 ≤ k < m`. With `q := P m` the internal failure probability of a cell
(`eq:P-leaf`, recorded here as `leafQ`) and with `S` and `f` the binomial-tail map
and the level map of `Hsfnlean.Threshold`, the level failure probabilities of the
paper are characterised by

* `P m = q`                       (the leaves),
* `P k = f (b k) q (P (k+1))`     for `1 ≤ k < m`,

and the theorem then reads `P 1 = f_{b 1} ∘ f_{b 2} ∘ ⋯ ∘ f_{b (m-1)} (q)`, with
overall consensus success rate `1 - P 1`. Item (i) (HSFN, `b k = N`) and item (ii)
(dense variant, `b 1 = N` and `b k = 2N-2` for `1 < k < m`) are the two instances.

Scope: this file formalises the **deterministic level recursion** only. `levelP`
is defined by downward recursion, `levelP_top` / `levelP_step` are its defining
equations, `levelP_unique` says nothing else satisfies them, and the remaining
statements are the composition identity, the two instances, the explicit displays
`eq:P-intermediate` / `eq:P-root`, and monotonicity in the leaf value.

**Deliberately out of scope**: the probabilistic content of `thm:security`, that is,
the independence argument identifying `P k` with the failure probability of a
level-`k` cell in the FPD model. Nothing here is stated about a probability space;
`S b x = P[Bin(b,x) ≤ ⌈b/2⌉ - 1]` is used purely as the real polynomial `binTail`,
and `leafQ` records the right-hand side of `eq:P-leaf` as a definition rather than
deriving it from the PBFT fault event. Consequently the paper's hypothesis
`b k ≥ 1` plays no role here: every statement below is an identity of real
algebra, valid for an arbitrary profile `b : ℕ → ℕ`.
-/

namespace HSFN

open Finset

noncomputable section

/-! ### The leaf value `eq:P-leaf` -/

/-- The internal failure probability of a single cell of size `N = n + 1`
(`eq:P-leaf`): the cell fails when more than `⌊(N-1)/3⌋ = n/3` of its `N` members
are faulty, each member failing independently with probability `Pf`. Written
subtraction-free through `N = n + 1`, so that the PBFT tolerance `⌊(N-1)/3⌋` is
`n / 3` and the sum of `eq:P-leaf` runs over `range (n / 3 + 1)`. -/
def leafQ (n : ℕ) (Pf : ℝ) : ℝ := 1 - binTail (n + 1) (n / 3 + 1) Pf

/-- `eq:P-leaf` written out:
`P_m = 1 - ∑_{i=0}^{⌊(N-1)/3⌋} C(N,i) (1-P_f)^{N-i} P_f^i` for `N = n + 1`. -/
theorem leafQ_eq (n : ℕ) (Pf : ℝ) :
    leafQ n Pf =
      1 - ∑ i ∈ range (n / 3 + 1),
            ((n + 1).choose i : ℝ) * Pf ^ i * (1 - Pf) ^ (n + 1 - i) := by
  simp only [leafQ, binTail]

/-- The leaf value of `eq:P-leaf` is a legitimate leaf failure probability. -/
theorem leafQ_mem_unit (n : ℕ) {Pf : ℝ} (h0 : 0 ≤ Pf) (h1 : Pf ≤ 1) :
    leafQ n Pf ∈ Set.Icc (0 : ℝ) 1 := by
  have hle : binTail (n + 1) (n / 3 + 1) Pf ≤ 1 :=
    binTail_le_one (b := n + 1) (k := n / 3 + 1) h0 h1
  have hge : 0 ≤ binTail (n + 1) (n / 3 + 1) Pf :=
    binTail_nonneg (b := n + 1) (k := n / 3 + 1) h0 h1
  constructor
  · simp only [leafQ]
    linarith
  · simp only [leafQ]
    linarith

/-! ### The level recursion -/

/-- Auxiliary downward recursion: `levelStep b q j k` is the failure probability of
a level-`k` cell of a cell tree with `j` further levels below it, i.e. of depth
`m = k + j`. With no level below (`j = 0`) the cell is a leaf and fails with
probability `q`; otherwise it fails through `f (b k) q` applied to the value one
level down. -/
def levelStep (b : ℕ → ℕ) (q : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => q
  | j + 1, k => f (b k) q (levelStep b q j (k + 1))

/-- The level failure probabilities `P_k` of a depth-`m` cell tree with branching
profile `b` and leaf value `q` (Theorem thm:security). Characterised by
`levelP b q m m = q` and `levelP b q m k = f (b k) q (levelP b q m (k+1))` for
`k < m`; see `levelP_top`, `levelP_step` and `levelP_unique`. -/
def levelP (b : ℕ → ℕ) (q : ℝ) (m : ℕ) : ℕ → ℝ := fun k => levelStep b q (m - k) k

/-- Leaf level: `P_m = q` (`eq:P-leaf` supplies the value of `q`). -/
theorem levelP_top (b : ℕ → ℕ) (q : ℝ) (m : ℕ) : levelP b q m m = q := by
  simp only [levelP, Nat.sub_self, levelStep]

/-- **The recursion of Theorem thm:security**: `P_k = f_{b_k}(P_{k+1})` for `k < m`. -/
theorem levelP_step (b : ℕ → ℕ) (q : ℝ) {m k : ℕ} (hk : k < m) :
    levelP b q m k = f (b k) q (levelP b q m (k + 1)) := by
  obtain ⟨j, hj⟩ : ∃ j, m - k = j + 1 := ⟨m - k - 1, by omega⟩
  have h2 : m - (k + 1) = j := by omega
  simp only [levelP, hj, h2, levelStep]

/-- The two equations of Theorem thm:security determine the level probabilities:
any `P` with `P m = q` and `P k = f (b k) q (P (k+1))` for `k < m` agrees with
`levelP` on `{k | k ≤ m}`. -/
theorem levelP_unique (b : ℕ → ℕ) (q : ℝ) (m : ℕ) (P : ℕ → ℝ) (hm : P m = q)
    (hrec : ∀ k, k < m → P k = f (b k) q (P (k + 1))) :
    ∀ k, k ≤ m → P k = levelP b q m k := by
  have key : ∀ d k, m - k = d → k ≤ m → P k = levelP b q m k := by
    intro d
    induction d with
    | zero =>
      intro k hd hk
      have hkm : k = m := by omega
      subst hkm
      rw [hm, levelP_top]
    | succ d ih =>
      intro k hd hk
      have hkm : k < m := by omega
      rw [hrec k hkm, ih (k + 1) (by omega) (by omega), levelP_step b q hkm]
  intro k hk
  exact key (m - k) k rfl hk

/-- The overall consensus success rate `1 - P_1` of Theorem thm:security. -/
def successRate (b : ℕ → ℕ) (q : ℝ) (m : ℕ) : ℝ := 1 - levelP b q m 1

/-! ### (a) The composition identity -/

/-- **Composition identity, general form.** For a cell tree of depth `m = k + j`,
the level-`k` failure probability is the composite
`f_{b_k} ∘ f_{b_{k+1}} ∘ ⋯ ∘ f_{b_{k+j-1}}` applied to `q`, realised as a
`List.foldr` over `List.range' k j = [k, k+1, …, k+j-1]`. -/
theorem levelP_eq_foldr (b : ℕ → ℕ) (q : ℝ) (k j : ℕ) :
    levelP b q (k + j) k = (List.range' k j).foldr (fun i x => f (b i) q x) q := by
  induction j generalizing k with
  | zero =>
    show levelP b q k k = q
    exact levelP_top b q k
  | succ j ih =>
    have hk : k < k + (j + 1) := by omega
    rw [levelP_step b q hk]
    have hm : k + (j + 1) = k + 1 + j := by omega
    rw [hm, ih (k + 1)]
    rfl

/-- **Composition identity at the root** (Theorem thm:security):
`P_1 = f_{b_1} ∘ f_{b_2} ∘ ⋯ ∘ f_{b_{m-1}}(q)` for a tree of depth `m = h + 1`,
the composite being the fold over `List.range' 1 h = [1, 2, …, m-1]`. -/
theorem levelP_one_eq_foldr (b : ℕ → ℕ) (q : ℝ) (h : ℕ) :
    levelP b q (h + 1) 1 = (List.range' 1 h).foldr (fun i x => f (b i) q x) q := by
  have hkey := levelP_eq_foldr b q 1 h
  have hm : 1 + h = h + 1 := by omega
  rwa [hm] at hkey

/-! ### (b) The HSFN instance, Theorem thm:security (i) -/

/-- The level probabilities of a tree with constant branching profile are iterates
of the single map `f N q`. -/
private theorem aux_levelP_const (b : ℕ → ℕ) (N : ℕ) (hb : ∀ k, b k = N) (q : ℝ) :
    ∀ j k, levelP b q (k + j) k = (f N q)^[j] q := by
  intro j
  induction j with
  | zero =>
    intro k
    show levelP b q k k = q
    exact levelP_top b q k
  | succ j ih =>
    intro k
    have hk : k < k + (j + 1) := by omega
    rw [levelP_step b q hk, hb k]
    have hm : k + (j + 1) = k + 1 + j := by omega
    rw [hm, ih (k + 1), ← Function.iterate_succ_apply' (f N q) j q]

/-- **HSFN** (Theorem thm:security (i)): every interior cell of the HSFN cell tree
has exactly `N` children, so with depth `m = h + 1` the root failure probability is
the `(m-1)`-fold iterate `P_1^{II} = f_N^{m-1}(q)`.
(Instance: `b = fun _ => N` satisfies the hypothesis.) -/
theorem levelP_const (b : ℕ → ℕ) (N : ℕ) (hb : ∀ k, b k = N) (q : ℝ) (h : ℕ) :
    levelP b q (h + 1) 1 = (f N q)^[h] q := by
  have hkey := aux_levelP_const b N hb q h 1
  have hm : 1 + h = h + 1 := by omega
  rwa [hm] at hkey

/-! ### (c) The dense-variant instance, Theorem thm:security (ii) -/

/-- Below the root, all branchings of the dense variant equal `c`, so the level
probabilities there are iterates of the single map `f c q`. -/
private theorem aux_levelP_dense (b : ℕ → ℕ) (c : ℕ) (q : ℝ) (m : ℕ)
    (hb : ∀ k, 1 < k → k < m → b k = c) :
    ∀ j k, 1 < k → k + j = m → levelP b q m k = (f c q)^[j] q := by
  intro j
  induction j with
  | zero =>
    intro k hk hkm
    have hkm' : k = m := by omega
    subst hkm'
    simpa using levelP_top b q k
  | succ j ih =>
    intro k hk hkm
    have hklt : k < m := by omega
    rw [levelP_step b q hklt, hb k hk hklt,
      ih (k + 1) (by omega) (by omega), ← Function.iterate_succ_apply' (f c q) j q]

/-- **Dense variant** (Theorem thm:security (ii)): the dense-variant cell tree has
`N` children at the root and `2N-2` children below it, written subtraction-free
through the cell size `N = n + 1` (so that `2N-2 = 2n`). For depth `m = h + 2 ≥ 2`,
`P_1^{(N,m)} = f_N(f_{2N-2}^{m-2}(q))`.
(Instance: `n = 2`, i.e. `N = 3` and `2N-2 = 4`, with
`b = fun k => if k = 1 then 3 else 4`.) -/
theorem levelP_dense (b : ℕ → ℕ) (n : ℕ) (q : ℝ) (h : ℕ)
    (hb1 : b 1 = n + 1) (hb : ∀ k, 1 < k → k < h + 2 → b k = 2 * n) :
    levelP b q (h + 2) 1 = f (n + 1) q ((f (2 * n) q)^[h] q) := by
  have h1 : (1 : ℕ) < h + 2 := by omega
  rw [levelP_step b q h1, hb1,
    aux_levelP_dense b (2 * n) q (h + 2) hb h (1 + 1) (by omega) (by omega)]

/-- Depth `m = 1`: `P_1 = q`, the degenerate case recorded in Theorem thm:security (ii). -/
theorem levelP_depth_one (b : ℕ → ℕ) (q : ℝ) : levelP b q 1 1 = q :=
  levelP_top b q 1

/-! ### The explicit displays `eq:P-intermediate` and `eq:P-root` -/

/-- The interior branching `b = 2N-2` of the dense variant has `⌈b/2⌉ = N - 1`, so
the tail `S_{2N-2}` runs over `i = 0, …, N-2` (written subtraction-free through
`N = n + 1`, `2N-2 = 2n`). -/
theorem half_two_mul (n : ℕ) : half (2 * n) = n := by
  unfold half
  omega

/-- The root branching `b = N` has `⌈N/2⌉ - 1 = ⌊(N-1)/2⌋`, so the tail `S_N` runs
over `i = 0, …, ⌊(N-1)/2⌋` (written subtraction-free through `N = n + 1`). -/
theorem half_succ (n : ℕ) : half (n + 1) = n / 2 + 1 := by
  unfold half
  omega

/-- **`eq:P-intermediate`**: for an interior level `1 < k < m` of the dense variant,
with `N = n + 1` (so `2N-2 = 2n`),
`P_k = 1 - (1 - P_m) ∑_{i=0}^{N-2} C(2N-2, i) (1 - P_{k+1})^{2N-2-i} P_{k+1}^i`. -/
theorem f_dense_explicit (n : ℕ) (q x : ℝ) :
    f (2 * n) q x =
      1 - (1 - q) * ∑ i ∈ range n,
            ((2 * n).choose i : ℝ) * x ^ i * (1 - x) ^ (2 * n - i) := by
  simp only [f, S, binTail, half_two_mul]

/-- **`eq:P-root`**: at the root of the dense variant, with `N = n + 1`,
`P_1^{(N,m)} = 1 - (1 - P_m) ∑_{i=0}^{⌊(N-1)/2⌋} C(N, i) (1 - P_2)^{N-i} P_2^i`. -/
theorem f_root_explicit (n : ℕ) (q x : ℝ) :
    f (n + 1) q x =
      1 - (1 - q) * ∑ i ∈ range (n / 2 + 1),
            ((n + 1).choose i : ℝ) * x ^ i * (1 - x) ^ (n + 1 - i) := by
  simp only [f, S, binTail, half_succ]

/-- The dense-variant recursion in the explicit form of `eq:P-intermediate`: at an
interior level `k < m` whose branching is `b k = 2N-2 = 2n`. -/
theorem levelP_step_dense_explicit (b : ℕ → ℕ) (n : ℕ) (q : ℝ) {m k : ℕ} (hk : k < m)
    (hbk : b k = 2 * n) :
    levelP b q m k =
      1 - (1 - q) * ∑ i ∈ range n,
            ((2 * n).choose i : ℝ) * levelP b q m (k + 1) ^ i *
              (1 - levelP b q m (k + 1)) ^ (2 * n - i) := by
  rw [levelP_step b q hk, hbk, f_dense_explicit]

/-- The dense-variant root in the explicit form of `eq:P-root`: the root has
`b 1 = N = n + 1` children, so
`P_1^{(N,m)} = 1 - (1 - P_m) ∑_{i=0}^{⌊(N-1)/2⌋} C(N,i) (1 - P_2)^{N-i} P_2^i`,
the tail running over `range (n / 2 + 1)` by `half_succ`. -/
theorem levelP_root_explicit (b : ℕ → ℕ) (n : ℕ) (q : ℝ) {m : ℕ} (hm : 1 < m)
    (hb1 : b 1 = n + 1) :
    levelP b q m 1 =
      1 - (1 - q) * ∑ i ∈ range (n / 2 + 1),
            ((n + 1).choose i : ℝ) * levelP b q m 2 ^ i *
              (1 - levelP b q m 2) ^ (n + 1 - i) := by
  have h2 : (1 : ℕ) + 1 = 2 := rfl
  rw [levelP_step b q hm, h2, hb1, f_root_explicit]

/-! ### (d) Monotonicity in the leaf value -/

/-- `f_b(x)` is nondecreasing in the leaf value `q` on `[0,1]`, since
`f b q x = 1 - (1 - q) S_b(x)` and `S_b(x) ≥ 0`. -/
theorem f_mono_q (b : ℕ) {q q' x : ℝ} (hqq : q ≤ q') (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    f b q x ≤ f b q' x := by
  have hS : 0 ≤ S b x := binTail_nonneg (b := b) (k := half b) hx0 hx1
  simp only [f]
  nlinarith

/-- Every value of the auxiliary recursion lies in `[0,1]`. -/
private theorem aux_levelStep_mem_unit (b : ℕ → ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ j k, levelStep b q j k ∈ Set.Icc (0 : ℝ) 1 := by
  intro j
  induction j with
  | zero => intro k; exact ⟨hq0, hq1⟩
  | succ j ih =>
    intro k
    have h := ih (k + 1)
    show f (b k) q (levelStep b q j (k + 1)) ∈ Set.Icc (0 : ℝ) 1
    exact ⟨le_trans hq0 (q_le_f hq1 h.1 h.2), f_le_one hq0 hq1 h.1 h.2⟩

/-- Every level probability is again a probability: `P_k ∈ [0,1]` whenever `q ∈ [0,1]`. -/
theorem levelP_mem_unit (b : ℕ → ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m k : ℕ) :
    levelP b q m k ∈ Set.Icc (0 : ℝ) 1 :=
  aux_levelStep_mem_unit b hq0 hq1 (m - k) k

/-- The auxiliary recursion is nondecreasing in the leaf value. -/
private theorem aux_levelStep_mono (b : ℕ → ℕ) {q q' : ℝ} (hq0 : 0 ≤ q) (hqq : q ≤ q')
    (hq1 : q' ≤ 1) : ∀ j k, levelStep b q j k ≤ levelStep b q' j k := by
  have hq0' : 0 ≤ q' := le_trans hq0 hqq
  have hq1' : q ≤ 1 := le_trans hqq hq1
  intro j
  induction j with
  | zero => intro k; exact hqq
  | succ j ih =>
    intro k
    have hx := aux_levelStep_mem_unit b hq0 hq1' j (k + 1)
    have hy := aux_levelStep_mem_unit b hq0' hq1 j (k + 1)
    have h1 : f (b k) q (levelStep b q j (k + 1)) ≤ f (b k) q' (levelStep b q j (k + 1)) :=
      f_mono_q (b k) hqq hx.1 hx.2
    have h2 : f (b k) q' (levelStep b q j (k + 1)) ≤ f (b k) q' (levelStep b q' j (k + 1)) :=
      f_monotoneOn (q := q') (b k) hq1 hx hy (ih (k + 1))
    show f (b k) q (levelStep b q j (k + 1)) ≤ f (b k) q' (levelStep b q' j (k + 1))
    exact le_trans h1 h2

/-- **Monotonicity in the leaf value, all levels**: raising the internal failure
probability `q` of `eq:P-leaf` raises every level failure probability. (Uses
`f_monotoneOn` in `x` together with `f_mono_q` in `q`.) -/
theorem levelP_mono_leaf (b : ℕ → ℕ) {q q' : ℝ} (hq0 : 0 ≤ q) (hqq : q ≤ q')
    (hq1 : q' ≤ 1) (m k : ℕ) :
    levelP b q m k ≤ levelP b q' m k :=
  aux_levelStep_mono b hq0 hqq hq1 (m - k) k

/-- **Monotonicity in the leaf value at the root**: `0 ≤ q ≤ q' ≤ 1` implies
`P_1(q) ≤ P_1(q')`. -/
theorem levelP_one_mono_leaf (b : ℕ → ℕ) {q q' : ℝ} (hq0 : 0 ≤ q) (hqq : q ≤ q')
    (hq1 : q' ≤ 1) (m : ℕ) :
    levelP b q m 1 ≤ levelP b q' m 1 :=
  levelP_mono_leaf b hq0 hqq hq1 m 1

/-- The consensus success rate `1 - P_1` is nonincreasing in the leaf value. -/
theorem successRate_antitone_leaf (b : ℕ → ℕ) {q q' : ℝ} (hq0 : 0 ≤ q) (hqq : q ≤ q')
    (hq1 : q' ≤ 1) (m : ℕ) :
    successRate b q' m ≤ successRate b q m := by
  have h := levelP_one_mono_leaf b hq0 hqq hq1 m
  simp only [successRate]
  linarith

/-! ### Non-vacuity of the two instances -/

/-- The hypothesis of `levelP_const` is satisfiable: the uniformly `N`-ary HSFN cell
tree is a witness, giving `P_1^{II} = f_N^{m-1}(q)` at depth `m = h + 1`. -/
theorem levelP_hsfn (N : ℕ) (q : ℝ) (h : ℕ) :
    levelP (fun _ => N) q (h + 1) 1 = (f N q)^[h] q :=
  levelP_const _ N (fun _ => rfl) q h

/-- The hypotheses of `levelP_dense` are jointly satisfiable: at cell size `N = 3`
(`n = 2`, interior branching `2N-2 = 4`) the profile `b 1 = 3`, `b k = 4` for `k > 1`
is a witness, giving `P_1^{(3,m)} = f_3(f_4^{m-2}(q))` at depth `m = h + 2`. -/
theorem levelP_dense_witness (q : ℝ) (h : ℕ) :
    levelP (fun k => if k = 1 then 3 else 4) q (h + 2) 1 = f 3 q ((f 4 q)^[h] q) := by
  have := levelP_dense (fun k => if k = 1 then 3 else 4) 2 q h (by norm_num)
    (fun k hk _ => by simp [Nat.ne_of_gt hk])
  simpa using this


end

end HSFN

