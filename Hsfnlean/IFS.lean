/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Mathlib

/-!
# The corner iterated function system in barycentric coordinates
(Theorem thm:dim-II: geometric hypotheses, and the **upper** dimension bound only)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409),
Section subsec:dimension, Theorem thm:dim-II and Fig. fig:barycentric-ifs.

The paper realizes each cell of the HSFN as a half-scale corner copy of its parent
simplex: with seed simplex `Δ_N = conv{p_1, …, p_N} ⊂ ℝ^{N-1}`, the corner similitude
of ratio `1/2` fixing `p_i` is `f_i(x) = p_i + (1/2)(x - p_i)`.  Read in barycentric
coordinates `λ = (λ_1, …, λ_N)` with `∑_k λ_k = 1`, that map becomes

  `f_i : λ ↦ (1/2) • (λ + e_i)`,

which is `fBary i` below, acting on the barycentric simplex `simplex N`.

## What is proved here

* (a) `fBary i` maps `Δ_N` into itself, with image exactly the corner half
  `{λ ∈ Δ_N : 1/2 ≤ λ i}`  (`fBary_mem_simplex`, `fBary_image_simplex`), and fixes the
  vertex `e_i`, the barycentric image of `p_i` (`fBary_fixed`);
* (b) each `f_i` is a similarity of ratio `1/2`: it halves both the ℓ¹ distance and the
  sup distance on coordinates (`nrm1_fBary_sub`, `norm_fBary_sub`), hence is a
  contraction of ratio `1/2` (`fBary_lipschitz`), and a word `w` of length `t` contracts
  by `2^{-t}` (`fList_lipschitz`);
* (c) the open set condition as the paper checks it: for `i ≠ j` no point of `Δ_N` has
  both `λ i > 1/2` and `λ j > 1/2` (`not_half_lt_of_ne`), so with `U` the (relative)
  interior of `Δ_N` one has `f_i(U) ⊆ U` and `f_i(U) ∩ f_j(U) = ∅`
  (`fBary_image_interior_subset`, `fBary_image_interior_disjoint`).  `U` is taken to be
  `simplexInt N`, the interior *relative to the affine hyperplane* `∑_k λ_k = 1`, which is
  what the paper's `U = int Δ_N ⊂ ℝ^{N-1}` means; the ambient interior of `Δ_N` inside
  `Fin N → ℝ` is empty, so an ambient `interior` would make (c) vacuous.  That `U` is
  genuinely open in that hyperplane, and genuinely nonempty, is recorded separately
  (`simplexInt_relatively_open`, `center_mem_simplexInt`), so that the disjointness
  statement is not a statement about the empty set;
* (d) the Moran equation `N · (1/2)^s = 1` has the unique real solution
  `s = log₂ N` (`moran_iff`, with `(1/2)^s` read as `Real.rpow`);
* (e) a set `attractor N` is *defined* as the nested intersection
  `⋂_t ⋃_{|w| = t} f_w(Δ_N)` of the stage sets (`stage`, `cell`, `fList`), and is shown
  to be compact (`isCompact_attractor`), nonempty for `N ≥ 1` (`attractor_nonempty`),
  contained in `Δ_N` (`attractor_subset_simplex`), to contain every barycentric vertex
  `e_i` (`vtx_mem_attractor`) and to satisfy `f_i(attractor N) ⊆ attractor N`
  (`fBary_image_attractor_subset`);
* (f) the **upper** Hausdorff-dimension bound for that set,

    `dimH (attractor N) ≤ log₂ N`   (`dimH_attractor_le`, for `N ≥ 2`),

  proved from the covering estimate rather than quoted: at stage `t` the `N^t` cells
  `f_w(Δ_N)` cover `attractor N` and each has diameter at most `2^{-t}`
  (`ediam_cell_le`, from (b) and `ediam_simplex_le_one`), so the stage-`t` Hausdorff sum
  for the exponent `log₂ N` is `N^t · (2^{-t})^{log₂ N} = 1` (`stage_sum_le_one`); feeding
  this to `MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum` gives
  `μH[log₂ N] (attractor N) ≤ 1` (`hausdorffMeasure_attractor_le_one`), and a finite
  Hausdorff measure at exponent `log₂ N` bounds the dimension by `log₂ N`.

## What is **not** proved here

The label thm:dim-II is therefore only **partly** discharged in this development.  The
following parts of that theorem are cited from the literature (Hutchinson 1981; Falconer;
Edgar) and are *not* formalized anywhere in this file:

* **The lower bound `log₂ N ≤ dimH 𝒮Δ_N`, hence the equality in thm:dim-II, is not
  proved.**  The standard route is the mass distribution principle: put the self-similar
  Bernoulli measure of weights `1/N` on the attractor and use the open set condition (c)
  to show it is Ahlfors-regular of exponent `log₂ N`.  mathlib does not package a mass
  distribution / Frostman principle, nor the self-similar measure of an IFS, so this half
  is out of reach without building that theory.  Consequently item (c) above, though
  proved, is *never used* below: it is recorded because it is the hypothesis the cited
  theorem needs.
* **`attractor N` is not proved to be Hutchinson's attractor.**  It is a definition (a
  nested intersection), not a characterization: only the inclusion
  `⋃_i f_i(attractor N) ⊆ attractor N` is proved (`fBary_image_attractor_subset`); the
  reverse inclusion, i.e. the fixed-point equation `A = ⋃_i f_i(A)`, and the uniqueness of
  a nonempty compact set with that property, are not proved here.  So `dimH_attractor_le`
  is an honest theorem about the set defined below, and it is only the *cited* theory that
  identifies that set with the paper's `𝒮Δ_N`.
* The identification of `𝒮Δ_N` with the closure of the realized node positions, and the
  tier-`t` cell/word bijection with the `N^{t-1}` cells of thm:unified-count, are not
  formalized.
* The box/similarity dimension `dim_S` of thm:dim-II is not formalized; nothing below
  mentions box dimension.  `moranDim N` is the *similarity exponent* `log₂ N` as a real
  number, defined and shown to solve the Moran equation; naming it a "dimension" is
  shorthand for that, not a proved dimension statement.

The statements (a)–(d) are frozen; only their proofs are to be supplied.
-/

namespace HSFN.IFS

open Finset

noncomputable section

variable {N : ℕ}

/-- The `i`-th barycentric vertex `e_i`, the coordinate vector of the seed vertex `p_i`. -/
def vtx (i : Fin N) : Fin N → ℝ := Pi.single i 1

/-- The barycentric simplex `Δ_N = {λ : 0 ≤ λ_k for all k, ∑_k λ_k = 1}`
(Definition def:simplex read in barycentric coordinates). -/
def simplex (N : ℕ) : Set (Fin N → ℝ) := {l | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1}

/-- The relative interior `int Δ_N = {λ : 0 < λ_k for all k, ∑_k λ_k = 1}`, the open set
`U` used for the open set condition in the proof of Theorem thm:dim-II. -/
def simplexInt (N : ℕ) : Set (Fin N → ℝ) := {l | (∀ i, 0 < l i) ∧ ∑ i, l i = 1}

/-- The corner similitude `f_i` of ratio `1/2` fixing the vertex `p_i`, in barycentric
coordinates: `f_i(λ) = (1/2) • (λ + e_i)` (Theorem thm:dim-II, dimension paragraph). -/
def fBary (i : Fin N) (l : Fin N → ℝ) : Fin N → ℝ := (1 / 2 : ℝ) • (l + vtx i)

/-- The ℓ¹ norm on barycentric coordinate vectors, `‖λ‖₁ = ∑_k |λ_k|`. -/
def nrm1 (l : Fin N → ℝ) : ℝ := ∑ i, |l i|

/-- Coordinatewise formula for the corner map. -/
theorem fBary_apply (i : Fin N) (l : Fin N → ℝ) (k : Fin N) :
    fBary i l k = (l k + (if k = i then 1 else 0)) / 2 := by
  simp only [fBary, Pi.smul_apply, Pi.add_apply, smul_eq_mul, vtx, Pi.single_apply]
  ring

/-- The barycentric vertices lie in the simplex. -/
theorem vtx_mem_simplex (i : Fin N) : vtx i ∈ simplex N := by
  refine ⟨fun k => ?_, ?_⟩
  · simp only [vtx, Pi.single_apply]
    split_ifs <;> norm_num
  · simp [vtx]

/-- The vertex `p_i` is the fixed point of the corner similitude `f_i`. -/
theorem fBary_fixed (i : Fin N) : fBary i (vtx i) = vtx i := by
  funext k
  rw [fBary_apply]
  simp only [vtx, Pi.single_apply]
  split_ifs <;> norm_num

/-! ### (a) The corner map preserves the simplex, with image the corner half -/

/-- Auxiliary: the corner map turns the coordinate sum `S` into `(S + 1) / 2`. -/
theorem aux_sum_fBary (i : Fin N) (l : Fin N → ℝ) :
    ∑ k, fBary i l k = ((∑ k, l k) + 1) / 2 := by
  have h : ∑ k, fBary i l k = ∑ k, ((l k + (if k = i then (1 : ℝ) else 0)) / 2) :=
    Finset.sum_congr rfl fun k _ => fBary_apply i l k
  rw [h, ← Finset.sum_div, Finset.sum_add_distrib]
  congr 2
  simp

/-- `f_i` maps `Δ_N` into itself. -/
theorem fBary_mem_simplex {i : Fin N} {l : Fin N → ℝ} (hl : l ∈ simplex N) :
    fBary i l ∈ simplex N := by
  obtain ⟨h0, h1⟩ := hl
  refine ⟨fun k => ?_, ?_⟩
  · rw [fBary_apply]
    have hk := h0 k
    split_ifs <;> linarith
  · rw [aux_sum_fBary, h1]
    norm_num

/-- Every point of the image satisfies `λ i ≥ 1/2`. -/
theorem half_le_fBary {i : Fin N} {l : Fin N → ℝ} (hl : l ∈ simplex N) :
    (1 / 2 : ℝ) ≤ fBary i l i := by
  rw [fBary_apply, if_pos rfl]
  have := hl.1 i
  linarith

/-- The image of the simplex under `f_i` is exactly the corner half
`f_i(Δ_N) = {λ ∈ Δ_N : λ_i ≥ 1/2}` (Theorem thm:dim-II, dimension paragraph). -/
theorem fBary_image_simplex (i : Fin N) :
    fBary i '' simplex N = {l ∈ simplex N | (1 / 2 : ℝ) ≤ l i} := by
  ext x
  simp only [Set.mem_image, Set.mem_sep_iff]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨fBary_mem_simplex hl, half_le_fBary hl⟩
  · rintro ⟨hx, hxi⟩
    obtain ⟨h0, h1⟩ := hx
    refine ⟨fun k => 2 * x k - (if k = i then 1 else 0), ⟨fun k => ?_, ?_⟩, ?_⟩
    · show (0 : ℝ) ≤ 2 * x k - (if k = i then 1 else 0)
      by_cases hk : k = i
      · subst hk
        rw [if_pos rfl]
        linarith
      · rw [if_neg hk]
        have := h0 k
        linarith
    · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h1]
      norm_num
    · funext k
      rw [fBary_apply]
      split_ifs <;> ring

/-! ### (b) The corner maps are similarities of ratio `1/2` -/

/-- Auxiliary: the corner map is affine, so differences scale by exactly `1/2`. -/
theorem aux_fBary_sub (i : Fin N) (l l' : Fin N → ℝ) :
    fBary i l - fBary i l' = (1 / 2 : ℝ) • (l - l') := by
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, fBary_apply]
  ring

/-- `f_i` halves the ℓ¹ distance between barycentric coordinate vectors: it is a
similarity of ratio `1/2`. -/
theorem nrm1_fBary_sub (i : Fin N) (l l' : Fin N → ℝ) :
    nrm1 (fBary i l - fBary i l') = (1 / 2 : ℝ) * nrm1 (l - l') := by
  rw [aux_fBary_sub, nrm1, nrm1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  norm_num

/-- `f_i` also halves the sup distance (the ambient norm on `Fin N → ℝ`). -/
theorem norm_fBary_sub (i : Fin N) (l l' : Fin N → ℝ) :
    ‖fBary i l - fBary i l'‖ = (1 / 2 : ℝ) * ‖l - l'‖ := by
  rw [aux_fBary_sub, norm_smul]
  norm_num

/-- Consequently `f_i` is a contraction of ratio `1/2`, the contraction hypothesis of the
iterated function system `{f_1, …, f_N}`. -/
theorem fBary_lipschitz (i : Fin N) : LipschitzWith (1 / 2 : NNReal) (fBary i) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, norm_fBary_sub]
  norm_num

/-! ### (c) The open set condition -/

/-- The relative interior of the simplex sits inside the simplex. -/
theorem simplexInt_subset_simplex : simplexInt N ⊆ simplex N := by
  intro l hl
  exact ⟨fun i => (hl.1 i).le, hl.2⟩

/-- Non-vacuity of the open set `U = int Δ_N`: for `N ≥ 1` the barycentre lies in `U`,
so the open set condition below is not a statement about the empty set. -/
theorem center_mem_simplexInt (hN : 0 < N) :
    (fun _ : Fin N => ((N : ℝ))⁻¹) ∈ simplexInt N := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  refine ⟨fun _ => inv_pos.mpr hN', ?_⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- `U = int Δ_N` is an *open* set in the sense the open set condition needs: it is the
trace on the affine hyperplane `∑_k λ_k = 1` of an open subset of the ambient coordinate
space, i.e. it is open in the relative topology of that hyperplane. -/
theorem simplexInt_relatively_open (N : ℕ) :
    ∃ V : Set (Fin N → ℝ), IsOpen V ∧ simplexInt N = V ∩ {l | ∑ i, l i = 1} := by
  refine ⟨Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ),
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi, ?_⟩
  ext l
  simp only [simplexInt, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ,
    Set.mem_Ioi, forall_true_left]

/-- The barycentric obstruction behind the open set condition: under `∑_k λ_k = 1` with
all `λ_k ≥ 0`, two distinct coordinates cannot both exceed `1/2`. -/
theorem not_half_lt_of_ne {i j : Fin N} (hij : i ≠ j) {l : Fin N → ℝ}
    (hl : l ∈ simplex N) : ¬ ((1 / 2 : ℝ) < l i ∧ (1 / 2 : ℝ) < l j) := by
  rintro ⟨hi, hj⟩
  obtain ⟨h0, h1⟩ := hl
  have hle : ∑ k ∈ ({i, j} : Finset (Fin N)), l k ≤ ∑ k, l k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => h0 k
  rw [Finset.sum_pair hij, h1] at hle
  linarith

/-- `f_i(U) ⊆ U` for `U = int Δ_N`. -/
theorem fBary_image_interior_subset (i : Fin N) :
    fBary i '' simplexInt N ⊆ simplexInt N := by
  rintro x ⟨l, hl, rfl⟩
  obtain ⟨h0, h1⟩ := hl
  refine ⟨fun k => ?_, ?_⟩
  · rw [fBary_apply]
    have hk := h0 k
    split_ifs <;> linarith
  · rw [aux_sum_fBary, h1]
    norm_num

/-- Points of `f_i(U)` have `λ_i > 1/2`, for `U = int Δ_N`. -/
theorem half_lt_fBary_of_mem_interior {i : Fin N} {l : Fin N → ℝ} (hl : l ∈ simplexInt N) :
    (1 / 2 : ℝ) < fBary i l i := by
  rw [fBary_apply, if_pos rfl]
  have := hl.1 i
  linarith

/-- The open set condition of Theorem thm:dim-II: with `U = int Δ_N`, the images
`f_i(U)` are pairwise disjoint. -/
theorem fBary_image_interior_disjoint {i j : Fin N} (hij : i ≠ j) :
    Disjoint (fBary i '' simplexInt N) (fBary j '' simplexInt N) := by
  rw [Set.disjoint_left]
  rintro x hxi hxj
  obtain ⟨l, hl, rfl⟩ := hxi
  obtain ⟨l', hl', he⟩ := hxj
  have hxs : fBary i l ∈ simplex N :=
    simplexInt_subset_simplex (fBary_image_interior_subset i ⟨l, hl, rfl⟩)
  have h1 : (1 / 2 : ℝ) < fBary i l i := half_lt_fBary_of_mem_interior hl
  have h2 : (1 / 2 : ℝ) < fBary i l j := by
    rw [← he]
    exact half_lt_fBary_of_mem_interior hl'
  exact not_half_lt_of_ne hij hxs ⟨h1, h2⟩

/-! ### (d) The Moran equation -/

/-- The similarity dimension of the corner system: the solution `log₂ N` of the Moran
equation `N · (1/2)^s = 1` (Theorem thm:dim-II). -/
def moranDim (N : ℕ) : ℝ := Real.logb 2 N

/-- The Moran equation `N · (1/2)^s = 1` for `N ≥ 2` has the unique real solution
`s = log₂ N`; here `(1/2)^s` is `Real.rpow`. -/
theorem moran_iff (hN : 2 ≤ N) (s : ℝ) :
    (N : ℝ) * (1 / 2 : ℝ) ^ s = 1 ↔ s = Real.logb 2 N := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have h2s : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hhalf : (1 / 2 : ℝ) ^ s = ((2 : ℝ) ^ s)⁻¹ := by
    rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
  have key : ((2 : ℝ) ^ s = (N : ℝ)) ↔ s = Real.logb 2 N := by
    rw [← Real.logb_eq_iff_rpow_eq (b := 2) (by norm_num) (by norm_num) hNpos]
    exact eq_comm
  rw [← key, hhalf]
  constructor
  · intro h
    have h' := congrArg (fun t : ℝ => t * (2 : ℝ) ^ s) h
    simp only [mul_assoc, inv_mul_cancel₀ h2s.ne', mul_one, one_mul] at h'
    exact h'.symm
  · intro h
    rw [← h, mul_inv_cancel₀ h2s.ne']

/-- The similarity dimension solves the Moran equation. -/
theorem moran_moranDim (hN : 2 ≤ N) : (N : ℝ) * (1 / 2 : ℝ) ^ moranDim N = 1 := by
  rw [moranDim]
  exact (moran_iff hN _).mpr rfl

/-- `log₂ N = log N / log 2`, the form displayed in Theorem thm:dim-II. -/
theorem moranDim_eq (N : ℕ) : moranDim N = Real.log N / Real.log 2 := by
  rw [moranDim, Real.logb]

/-! ### (e) The attractor of the corner system and the upper bound on its dimension -/

open scoped ENNReal NNReal Topology MeasureTheory

/-- `f_w = f_{w_1} ∘ ⋯ ∘ f_{w_t}`, the corner maps of a word composed left to right
(the first letter is applied last). -/
def fList : List (Fin N) → (Fin N → ℝ) → (Fin N → ℝ)
  | [], l => l
  | i :: w, l => fBary i (fList w l)

@[simp] theorem fList_nil (l : Fin N → ℝ) : fList ([] : List (Fin N)) l = l := rfl

@[simp] theorem fList_cons (i : Fin N) (w : List (Fin N)) (l : Fin N → ℝ) :
    fList (i :: w) l = fBary i (fList w l) := rfl

/-- Words compose: `f_{vw} = f_v ∘ f_w`. -/
theorem fList_append (v w : List (Fin N)) (l : Fin N → ℝ) :
    fList (v ++ w) l = fList v (fList w l) := by
  induction v with
  | nil => rfl
  | cons i v ih => simp only [List.cons_append, fList_cons, ih]

/-- A word of length `t` contracts by exactly the factor `2^{-t}`; this is the iterated
form of `fBary_lipschitz`. -/
theorem fList_lipschitz (w : List (Fin N)) :
    LipschitzWith ((1 / 2 : NNReal) ^ w.length) (fList w) := by
  induction w with
  | nil =>
      have h : fList ([] : List (Fin N)) = id := funext fun _ => rfl
      simpa [h] using LipschitzWith.id (α := Fin N → ℝ)
  | cons i v ih =>
      have h := (fBary_lipschitz i).comp ih
      rw [List.length_cons, pow_succ, mul_comm]
      exact h

/-- `f_w` maps the simplex into itself. -/
theorem fList_mem_simplex (w : List (Fin N)) {l : Fin N → ℝ} (hl : l ∈ simplex N) :
    fList w l ∈ simplex N := by
  induction w with
  | nil => exact hl
  | cons i v ih => exact fBary_mem_simplex ih

/-- The tier-`t` cell indexed by the word `w ∈ {1,…,N}^t`, namely `f_w(Δ_N)`. -/
def cell {N : ℕ} (t : ℕ) (w : Fin t → Fin N) : Set (Fin N → ℝ) :=
  fList (List.ofFn w) '' simplex N

/-- Stage `t` of the iteration, `⋃_{|w| = t} f_w(Δ_N)`: the union of the `N^t` tier-`t`
cells. -/
def stage (N t : ℕ) : Set (Fin N → ℝ) := ⋃ w : Fin t → Fin N, cell t w

/-- The attractor `𝒮Δ_N` of the corner system, built as the nested intersection of the
stages `⋃_{|w| = t} f_w(Δ_N)`. -/
def attractor (N : ℕ) : Set (Fin N → ℝ) := ⋂ t, stage N t

theorem cell_subset_simplex {t : ℕ} (w : Fin t → Fin N) : cell t w ⊆ simplex N := by
  rintro x ⟨l, hl, rfl⟩
  exact fList_mem_simplex _ hl

/-- Dropping the last letter of a word enlarges the cell. -/
theorem cell_succ_subset {t : ℕ} (w : Fin (t + 1) → Fin N) :
    cell (t + 1) w ⊆ cell t (fun i => w i.castSucc) := by
  rintro x ⟨l, hl, rfl⟩
  have hof : List.ofFn w
      = (List.ofFn fun i : Fin t => w i.castSucc) ++ [w (Fin.last t)] := by
    rw [List.ofFn_succ']
    simp
  refine ⟨fList [w (Fin.last t)] l, fList_mem_simplex _ hl, ?_⟩
  rw [hof, fList_append]

theorem stage_succ_subset (N t : ℕ) : stage N (t + 1) ⊆ stage N t := by
  intro x hx
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨_, cell_succ_subset w hw⟩

theorem stage_zero (N : ℕ) : stage N 0 = simplex N := by
  ext x
  simp [stage, cell]

/-- `Δ_N` is the standard simplex of mathlib, read in these coordinates. -/
theorem simplex_eq_stdSimplex (N : ℕ) : simplex N = stdSimplex ℝ (Fin N) := rfl

theorem isCompact_simplex (N : ℕ) : IsCompact (simplex N) := by
  rw [simplex_eq_stdSimplex]
  exact isCompact_stdSimplex ℝ (Fin N)

theorem isCompact_cell {t : ℕ} (w : Fin t → Fin N) : IsCompact (cell t w) :=
  (isCompact_simplex N).image (fList_lipschitz _).continuous

theorem isCompact_stage (N t : ℕ) : IsCompact (stage N t) :=
  isCompact_iUnion fun w => isCompact_cell w

theorem simplex_nonempty (hN : 0 < N) : (simplex N).Nonempty :=
  ⟨_, simplexInt_subset_simplex (center_mem_simplexInt hN)⟩

theorem stage_nonempty (hN : 0 < N) (t : ℕ) : (stage N t).Nonempty := by
  obtain ⟨l, hl⟩ := simplex_nonempty hN
  exact ⟨_, Set.mem_iUnion.2 ⟨fun _ => ⟨0, hN⟩, ⟨l, hl, rfl⟩⟩⟩

theorem attractor_subset_stage (N t : ℕ) : attractor N ⊆ stage N t :=
  Set.iInter_subset _ t

theorem attractor_subset_simplex (N : ℕ) : attractor N ⊆ simplex N := by
  have := attractor_subset_stage N 0
  rwa [stage_zero] at this

/-- The attractor is compact. -/
theorem isCompact_attractor (N : ℕ) : IsCompact (attractor N) :=
  (isCompact_stage N 0).of_isClosed_subset
    (isClosed_iInter fun t => (isCompact_stage N t).isClosed)
    (attractor_subset_stage N 0)

/-- The attractor is nonempty (Cantor's intersection theorem on the nested stages). -/
theorem attractor_nonempty (hN : 0 < N) : (attractor N).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
    (fun t => stage_succ_subset N t) (fun t => stage_nonempty hN t)
    (isCompact_stage N 0) (fun t => (isCompact_stage N t).isClosed)

/-- Iterating the corner map `f_i` fixes its vertex `e_i`. -/
theorem fList_replicate_vtx (i : Fin N) (t : ℕ) :
    fList (List.replicate t i) (vtx i) = vtx i := by
  induction t with
  | zero => rfl
  | succ t ih => rw [List.replicate_succ, fList_cons, ih, fBary_fixed]

/-- Each barycentric vertex `e_i` lies in the attractor; in particular the attractor is
nonempty whenever `N ≥ 1`, and it contains the realized seed positions. -/
theorem vtx_mem_attractor (i : Fin N) : vtx i ∈ attractor N := by
  refine Set.mem_iInter.2 fun t => Set.mem_iUnion.2 ⟨fun _ => i, vtx i, vtx_mem_simplex i, ?_⟩
  have hof : List.ofFn (fun _ : Fin t => i) = List.replicate t i := by simp
  rw [hof, fList_replicate_vtx]

/-- One half of Hutchinson invariance: the attractor is carried into itself by every corner
map.  (The reverse inclusion `𝒮Δ_N ⊆ ⋃_i f_i(𝒮Δ_N)` is *not* proved here.) -/
theorem fBary_image_attractor_subset (i : Fin N) :
    fBary i '' attractor N ⊆ attractor N := by
  rintro x ⟨l, hl, rfl⟩
  refine Set.mem_iInter.2 fun t => ?_
  cases t with
  | zero =>
      rw [stage_zero]
      exact fBary_mem_simplex (attractor_subset_simplex N hl)
  | succ t =>
      obtain ⟨w, y, hy, hyw⟩ := Set.mem_iUnion.1 (attractor_subset_stage N t hl)
      refine Set.mem_iUnion.2 ⟨Fin.cons i w, y, hy, ?_⟩
      have hof : List.ofFn (Fin.cons i w : Fin (t + 1) → Fin N) = i :: List.ofFn w := by
        rw [List.ofFn_succ]
        simp
      rw [hof, fList_cons, hyw]

/-! #### The covering estimate -/

theorem le_one_of_mem_simplex {l : Fin N → ℝ} (hl : l ∈ simplex N) (k : Fin N) : l k ≤ 1 := by
  obtain ⟨h0, h1⟩ := hl
  calc l k ≤ ∑ i, l i := Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ k)
    _ = 1 := h1

/-- In the sup metric the simplex has diameter at most `1`. -/
theorem ediam_simplex_le_one (N : ℕ) : Metric.ediam (simplex N) ≤ 1 := by
  refine Metric.ediam_le fun x hx y hy => edist_pi_le_iff.2 fun i => ?_
  have hx0 := hx.1 i
  have hy0 := hy.1 i
  have hx1 := le_one_of_mem_simplex hx i
  have hy1 := le_one_of_mem_simplex hy i
  have hd : dist (x i) (y i) ≤ 1 := by
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  calc edist (x i) (y i) = ENNReal.ofReal (dist (x i) (y i)) := edist_dist _ _
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hd
    _ = 1 := ENNReal.ofReal_one

/-- A tier-`t` cell has diameter at most `2^{-t}`: the covering estimate behind the
dimension bound. -/
theorem ediam_cell_le {t : ℕ} (w : Fin t → Fin N) :
    Metric.ediam (cell t w) ≤ (1 / 2 : ℝ≥0∞) ^ t := by
  have h := (fList_lipschitz (List.ofFn w)).ediam_image_le (simplex N)
  rw [List.length_ofFn] at h
  refine h.trans ?_
  have h1 : (((1 / 2 : NNReal) ^ t : NNReal) : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) ^ t := by
    push_cast
    norm_num
  rw [h1]
  calc (1 / 2 : ℝ≥0∞) ^ t * Metric.ediam (simplex N)
      ≤ (1 / 2 : ℝ≥0∞) ^ t * 1 := mul_le_mul' le_rfl (ediam_simplex_le_one N)
    _ = (1 / 2 : ℝ≥0∞) ^ t := mul_one _

/-! #### The Hausdorff dimension upper bound -/

theorem moranDim_nonneg (hN : 2 ≤ N) : 0 ≤ moranDim N := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact Real.logb_nonneg (by norm_num) (by linarith)

/-- The scalar identity behind the covering sum, read in `ℝ≥0∞`:
`(1/2)^{log₂ N} = 1/N`. -/
theorem rpow_half_moranDim (hN : 2 ≤ N) :
    (1 / 2 : ℝ≥0∞) ^ (moranDim N) = ((N : ℝ≥0∞))⁻¹ := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hx : (1 / 2 : ℝ) ^ (moranDim N) = ((N : ℝ))⁻¹ := by
    have h := moran_moranDim hN
    rw [inv_eq_one_div, eq_div_iff (ne_of_gt hNpos)]
    linear_combination h
  have hc : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hc, ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hx,
    ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]

/-- The stage-`t` covering sum for the exponent `log₂ N` is at most `1`: there are `N^t`
cells, each of diameter at most `2^{-t}`, and `N^t · (2^{-t})^{log₂ N} = 1`. -/
theorem stage_sum_le_one (hN : 2 ≤ N) (t : ℕ) :
    ∑ w : Fin t → Fin N, Metric.ediam (cell t w) ^ (moranDim N) ≤ 1 := by
  have hd0 : 0 ≤ moranDim N := moranDim_nonneg hN
  have hterm : ∀ w : Fin t → Fin N,
      Metric.ediam (cell t w) ^ (moranDim N) ≤ ((1 / 2 : ℝ≥0∞) ^ t) ^ (moranDim N) :=
    fun w => ENNReal.rpow_le_rpow (ediam_cell_le w) hd0
  refine (Finset.sum_le_sum fun w _ => hterm w).trans ?_
  have hpow : ((1 / 2 : ℝ≥0∞) ^ t) ^ (moranDim N) = ((N : ℝ≥0∞))⁻¹ ^ t := by
    rw [← ENNReal.rpow_natCast (1 / 2 : ℝ≥0∞) t, ← ENNReal.rpow_mul, mul_comm,
      ENNReal.rpow_mul, rpow_half_moranDim hN, ENNReal.rpow_natCast]
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by
    simpa using (by omega : N ≠ 0)
  have hcard : ((Fintype.card (Fin t → Fin N) : ℕ) : ℝ≥0∞) = (N : ℝ≥0∞) ^ t := by
    simp
  rw [Finset.sum_const, Finset.card_univ, hpow, nsmul_eq_mul, hcard, ← mul_pow,
    ENNReal.mul_inv_cancel hN0 (ENNReal.natCast_ne_top N), one_pow]

/-- The covering estimate: the `log₂ N`-dimensional Hausdorff measure of the attractor is
at most `1`, hence finite. -/
theorem hausdorffMeasure_attractor_le_one (hN : 2 ≤ N) :
    MeasureTheory.Measure.hausdorffMeasure (moranDim N) (attractor N) ≤ 1 := by
  have hhalf : (1 / 2 : ℝ≥0∞) < 1 := by
    simp
  have htend : Filter.Tendsto (fun t : ℕ => (1 / 2 : ℝ≥0∞) ^ t) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hhalf
  have hcov := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum
    (X := Fin N → ℝ) (moranDim N) (attractor N)
    (l := Filter.atTop) (fun t : ℕ => (1 / 2 : ℝ≥0∞) ^ t) htend
    (fun (t : ℕ) (w : Fin t → Fin N) => cell t w)
    (Filter.Eventually.of_forall fun _ w => ediam_cell_le w)
    (Filter.Eventually.of_forall fun t => attractor_subset_stage N t)
  refine hcov.trans ?_
  refine (Filter.liminf_le_liminf
    (Filter.Eventually.of_forall fun t => stage_sum_le_one hN t)).trans ?_
  simp

/-- **Upper bound of Theorem thm:dim-II.**  The attractor `𝒮Δ_N` of the corner system has
Hausdorff dimension at most the similarity dimension `log₂ N`.  Only the upper bound is
proved here; see the module header for what is missing. -/
theorem dimH_attractor_le (hN : 2 ≤ N) :
    dimH (attractor N) ≤ ENNReal.ofReal (moranDim N) := by
  have hd0 : 0 ≤ moranDim N := moranDim_nonneg hN
  have hne : MeasureTheory.Measure.hausdorffMeasure
      (((moranDim N).toNNReal : ℝ≥0) : ℝ) (attractor N) ≠ ⊤ := by
    rw [Real.coe_toNNReal _ hd0]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (hausdorffMeasure_attractor_le_one hN)
  exact dimH_le_of_hausdorffMeasure_ne_top hne

end

#print axioms HSFN.IFS.fBary_apply
#print axioms HSFN.IFS.vtx_mem_simplex
#print axioms HSFN.IFS.fBary_fixed
#print axioms HSFN.IFS.fBary_mem_simplex
#print axioms HSFN.IFS.half_le_fBary
#print axioms HSFN.IFS.fBary_image_simplex
#print axioms HSFN.IFS.nrm1_fBary_sub
#print axioms HSFN.IFS.norm_fBary_sub
#print axioms HSFN.IFS.fBary_lipschitz
#print axioms HSFN.IFS.simplexInt_subset_simplex
#print axioms HSFN.IFS.center_mem_simplexInt
#print axioms HSFN.IFS.simplexInt_relatively_open
#print axioms HSFN.IFS.not_half_lt_of_ne
#print axioms HSFN.IFS.fBary_image_interior_subset
#print axioms HSFN.IFS.half_lt_fBary_of_mem_interior
#print axioms HSFN.IFS.fBary_image_interior_disjoint
#print axioms HSFN.IFS.moran_iff
#print axioms HSFN.IFS.moran_moranDim
#print axioms HSFN.IFS.moranDim_eq
#print axioms HSFN.IFS.fList_append
#print axioms HSFN.IFS.fList_lipschitz
#print axioms HSFN.IFS.fList_mem_simplex
#print axioms HSFN.IFS.cell_subset_simplex
#print axioms HSFN.IFS.cell_succ_subset
#print axioms HSFN.IFS.stage_succ_subset
#print axioms HSFN.IFS.stage_zero
#print axioms HSFN.IFS.simplex_eq_stdSimplex
#print axioms HSFN.IFS.isCompact_simplex
#print axioms HSFN.IFS.isCompact_cell
#print axioms HSFN.IFS.isCompact_stage
#print axioms HSFN.IFS.simplex_nonempty
#print axioms HSFN.IFS.stage_nonempty
#print axioms HSFN.IFS.attractor_subset_stage
#print axioms HSFN.IFS.attractor_subset_simplex
#print axioms HSFN.IFS.isCompact_attractor
#print axioms HSFN.IFS.attractor_nonempty
#print axioms HSFN.IFS.fList_replicate_vtx
#print axioms HSFN.IFS.vtx_mem_attractor
#print axioms HSFN.IFS.fBary_image_attractor_subset
#print axioms HSFN.IFS.le_one_of_mem_simplex
#print axioms HSFN.IFS.ediam_simplex_le_one
#print axioms HSFN.IFS.ediam_cell_le
#print axioms HSFN.IFS.moranDim_nonneg
#print axioms HSFN.IFS.rpow_half_moranDim
#print axioms HSFN.IFS.stage_sum_le_one
#print axioms HSFN.IFS.hausdorffMeasure_attractor_le_one
#print axioms HSFN.IFS.dimH_attractor_le

end HSFN.IFS

