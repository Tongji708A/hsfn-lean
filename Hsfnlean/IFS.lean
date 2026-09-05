/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Mathlib

/-!
# The corner iterated function system in barycentric coordinates
(Theorem thm:dim-II, geometric core)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409),
Section subsec:dimension, Theorem thm:dim-II and Fig. fig:barycentric-ifs.

The paper realizes each cell of the HSFN as a half-scale corner copy of its parent
simplex: with seed simplex `Δ_N = conv{p_1, …, p_N} ⊂ ℝ^{N-1}`, the corner similitude
of ratio `1/2` fixing `p_i` is `f_i(x) = p_i + (1/2)(x - p_i)`.  Read in barycentric
coordinates `λ = (λ_1, …, λ_N)` with `∑_k λ_k = 1`, that map becomes

  `f_i : λ ↦ (1/2) • (λ + e_i)`,

which is `fBary i` below, acting on the barycentric simplex `simplex N`.  This file
formalizes exactly the four geometric facts the proof of Theorem thm:dim-II checks in
barycentric coordinates, namely the hypotheses under which Moran–Hutchinson applies:

* (a) `fBary i` maps `Δ_N` into itself, with image exactly the corner half
  `{λ ∈ Δ_N : 1/2 ≤ λ i}`  (`fBary_mem_simplex`, `fBary_image_simplex`), and fixes the
  vertex `e_i`, the barycentric image of `p_i` (`fBary_fixed`);
* (b) each `f_i` is a similarity of ratio `1/2`: it halves both the ℓ¹ distance and the
  sup distance on coordinates (`nrm1_fBary_sub`, `norm_fBary_sub`), hence is a
  contraction of ratio `1/2` (`fBary_lipschitz`);
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
  `s = log₂ N` (`moran_iff`, with `(1/2)^s` read as `Real.rpow`).

**Not formalized here, and cited rather than proved.**  Items (a)–(d) are precisely the
geometric hypotheses of the Moran–Hutchinson theorem (Hutchinson 1981; Falconer;
Edgar).  The conclusion of Theorem thm:dim-II itself — that the attractor
`𝒮Δ_N` of `{f_1, …, f_N}` exists, that it is the closure of the realized node
positions, and that `dim_H 𝒮Δ_N = dim_S 𝒮Δ_N = log₂ N` — is **not** proved in this
development; it is quoted from the literature.  Nothing below mentions Hausdorff
dimension, self-similar attractors, or the tier-`t` cell/word bijection.
The statements below are frozen; only the proofs are to be supplied.
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

end HSFN.IFS

