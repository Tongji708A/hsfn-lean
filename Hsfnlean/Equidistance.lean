/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Mathlib

/-!
# Equidistance prices dimension (Lemma lem:equidistance)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409),
Section "Preliminaries / Simplex and Simplex Network", Lemma `lem:equidistance`.

The paper's statement: *in `ℝ^d` there are at most `d+1` points with pairwise equal
distances; consequently `N` pairwise-equidistant points exist in `ℝ^d` only if
`d ≥ N-1`.* Its proof is Schoenberg's Gram criterion in the equilateral case: put
`v i = p i - p (last)`; then `⟪v i, v i⟫ = 1` and `⟪v i, v j⟫ = 1/2` for `i ≠ j`, so
the Gram matrix is `G = (1/2)(I + J)`, whose eigenvalues are `1/2` (multiplicity
`N-2`) and `N/2`, all positive; `G` is therefore positive definite and the `v i` are
linearly independent, which forces `d ≥ N-1`.

This file formalizes exactly that pair of claims, in a general real inner product
space and then specialized to `EuclideanSpace ℝ (Fin d)`:

* `HSFN.Equidistance.gram_eq`, `gram_posDef` — the Gram matrix `(1/2)(I + J)` and its
  positive definiteness (the engine of the paper's proof);
* `HSFN.Equidistance.linearIndependent_diffVec` (clause (a)) — the `n` difference
  vectors of `n+1` pairwise-equidistant points are linearly independent;
* `HSFN.Equidistance.card_le_finrank_succ`, `card_le_dim_succ` (clause (b)) — `n`
  pairwise-equidistant points force `n ≤ finrank + 1`, i.e. `d ≥ N-1`, written
  subtraction-free as `N ≤ d + 1`.

Deliberately *not* formalized here (out of scope by design): the converse existence
direction of the paper's "if and only if" (the regular `(N-1)`-simplex realizes
equality in `ℝ^{N-1}`), the eigenvalue multiplicities of `G`, and the
uniqueness-up-to-similarity clause with its `K_N` one-skeleton.

Everything stated below is proved; the file contains no `sorry` and no new axiom.
-/

open scoped InnerProductSpace
open scoped Matrix

namespace HSFN.Equidistance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A family of points is *equidistant with common distance `r`* when every two
distinct members are at distance `r`. This is the metric form of peer equality:
`N` participants, each at the same distance from each other, none privileged. -/
def Equidistant {ι : Type*} (p : ι → E) (r : ℝ) : Prop :=
  ∀ i j : ι, i ≠ j → dist (p i) (p j) = r

omit [InnerProductSpace ℝ E] in
/-- Equidistance restated with the norm of a difference, matching `‖p i - p j‖ = r`
as written in the paper. -/
theorem norm_sub_of_equidistant {ι : Type*} {p : ι → E} {r : ℝ} (hp : Equidistant p r)
    {i j : ι} (hij : i ≠ j) : ‖p i - p j‖ = r := by
  rw [← dist_eq_norm]
  exact hp i j hij

/-- The `n` difference vectors of an `(n+1)`-point configuration, based at the last
point: `v i = p i - p (last)` in the notation of the paper's proof. -/
def diffVec {n : ℕ} (p : Fin (n + 1) → E) (i : Fin n) : E :=
  p i.castSucc - p (Fin.last n)

omit [InnerProductSpace ℝ E] in
/-- Auxiliary: each difference vector of a unit-distance configuration is a unit
vector, since `i.castSucc ≠ Fin.last n`. -/
theorem aux_norm_diffVec {n : ℕ} {p : Fin (n + 1) → E} (hp : Equidistant p 1)
    (i : Fin n) : ‖diffVec p i‖ = 1 :=
  norm_sub_of_equidistant hp (Fin.castSucc_lt_last i).ne

/-- Diagonal Gram entry: `⟪v i, v i⟫ = 1` for a unit-distance configuration. -/
theorem inner_diffVec_self {n : ℕ} {p : Fin (n + 1) → E} (hp : Equidistant p 1)
    (i : Fin n) : ⟪diffVec p i, diffVec p i⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq, aux_norm_diffVec hp i, one_pow]

/-- Off-diagonal Gram entry: `2⟪v i, v j⟫ = ‖v i‖² + ‖v j‖² - ‖v i - v j‖² = 1`
for `i ≠ j` in a unit-distance configuration. -/
theorem inner_diffVec_ne {n : ℕ} {p : Fin (n + 1) → E} (hp : Equidistant p 1)
    {i j : Fin n} (hij : i ≠ j) : ⟪diffVec p i, diffVec p j⟫_ℝ = 2⁻¹ := by
  have hx : ‖diffVec p i‖ = 1 := aux_norm_diffVec hp i
  have hy : ‖diffVec p j‖ = 1 := aux_norm_diffVec hp j
  have hsub : diffVec p i - diffVec p j = p i.castSucc - p j.castSucc := by
    simp only [diffVec]
    abel
  have hxy : ‖diffVec p i - diffVec p j‖ = 1 := by
    rw [hsub]
    exact norm_sub_of_equidistant hp (fun h => hij (Fin.castSucc_injective n h))
  have h := norm_sub_sq_real (diffVec p i) (diffVec p j)
  rw [hx, hy, hxy] at h
  norm_num at h
  linarith

/-- The Gram matrix of the difference vectors `v 0, …, v (n-1)`. -/
noncomputable def gram {n : ℕ} (p : Fin (n + 1) → E) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ⟪diffVec p i, diffVec p j⟫_ℝ

/-- The paper's Gram identity: `G = ½(I + J)` with `J` the all-ones matrix. -/
theorem gram_eq {n : ℕ} {p : Fin (n + 1) → E} (hp : Equidistant p 1) :
    gram p = (2⁻¹ : ℝ) • (1 + Matrix.of fun _ _ : Fin n => (1 : ℝ)) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp only [gram, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply_eq, smul_eq_mul, inner_diffVec_self hp]
    norm_num
  · simp only [gram, Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply_ne h, smul_eq_mul, inner_diffVec_ne hp h]
    norm_num

/-- The quadratic form of `G = ½(I + J)`: for every coefficient vector `c`,
`cᵀGc = ½(∑ᵢ cᵢ)² + ½ ∑ᵢ cᵢ²`. This is the identity behind the eigenvalues `½`
(multiplicity `n-1` here, `N-2` in the paper's indexing) and `(n+1)/2`. -/
theorem gram_quadratic {n : ℕ} {p : Fin (n + 1) → E} (hp : Equidistant p 1)
    (c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * ⟪diffVec p i, diffVec p j⟫_ℝ
      = 2⁻¹ * (∑ i, c i) ^ 2 + 2⁻¹ * ∑ i, c i ^ 2 := by
  have key : ∀ i j : Fin n,
      ⟪diffVec p i, diffVec p j⟫_ℝ = 2⁻¹ + (if i = j then (2⁻¹ : ℝ) else 0) := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [inner_diffVec_self hp]
      norm_num
    · rw [inner_diffVec_ne hp h]
      simp [h]
  have inner_step : ∀ i : Fin n,
      ∑ j, c i * c j * (2⁻¹ + (if i = j then (2⁻¹ : ℝ) else 0))
        = 2⁻¹ * (c i * ∑ j, c j) + 2⁻¹ * c i ^ 2 := by
    intro i
    have hterm : ∀ j : Fin n,
        c i * c j * (2⁻¹ + (if i = j then (2⁻¹ : ℝ) else 0))
          = 2⁻¹ * (c i * c j) + (if i = j then 2⁻¹ * c i ^ 2 else 0) := by
      intro j
      split_ifs with h
      · subst h
        ring
      · ring
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq]
    simp
  simp_rw [key]
  rw [Finset.sum_congr rfl fun i _ => inner_step i, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The same quadratic form read as a squared norm:
`‖∑ᵢ cᵢ vᵢ‖² = ½(∑ᵢ cᵢ)² + ½ ∑ᵢ cᵢ²`, which is `> 0` unless every `cᵢ = 0`. -/
theorem norm_sq_combination {n : ℕ} {p : Fin (n + 1) → E} (hp : Equidistant p 1)
    (c : Fin n → ℝ) :
    ‖∑ i, c i • diffVec p i‖ ^ 2 = 2⁻¹ * (∑ i, c i) ^ 2 + 2⁻¹ * ∑ i, c i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right, ← mul_assoc]
  exact gram_quadratic hp c

/-- Auxiliary: the sum of squares of a nonzero real vector is positive. -/
theorem aux_sum_sq_pos {n : ℕ} {c : Fin n → ℝ} (hc : c ≠ 0) : 0 < ∑ i, c i ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := Function.ne_iff.mp hc
  refine Finset.sum_pos' (fun j _ => sq_nonneg (c j)) ⟨i, Finset.mem_univ i, ?_⟩
  positivity

/-- `G` is positive definite (the engine of the paper's proof of Lemma
`lem:equidistance`). The paper reads positive definiteness off the eigenvalues `1/2`
(multiplicity `N-2`) and `N/2` of `G = (1/2)(I + J)`; here it is obtained equivalently
and directly from `gram_quadratic`, i.e. from
`cᵀGc = (1/2)(∑ᵢ cᵢ)² + (1/2)∑ᵢ cᵢ² > 0` for `c ≠ 0`. The eigenvalues themselves are
not computed in this file. -/
theorem gram_posDef {n : ℕ} {p : Fin (n + 1) → E} (hp : Equidistant p 1) :
    (gram p).PosDef := by
  have hherm : (gram p).IsHermitian := by
    show Matrix.conjTranspose (gram p) = gram p
    ext i j
    simp only [Matrix.conjTranspose_apply, gram, Matrix.of_apply, star_trivial]
    exact real_inner_comm _ _
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun x hx => ?_
  have hval : star x ⬝ᵥ (gram p *ᵥ x)
      = ∑ i, ∑ j, x i * x j * ⟪diffVec p i, diffVec p j⟫_ℝ := by
    simp only [dotProduct, Matrix.mulVec, gram, Matrix.of_apply, Pi.star_apply, star_trivial,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hval, gram_quadratic hp x]
  have h1 : (0 : ℝ) ≤ (∑ i, x i) ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) < ∑ i, x i ^ 2 := aux_sum_sq_pos hx
  linarith

/-- **Lemma lem:equidistance, clause (a).** The `n` difference vectors
`v i = p i - p (last)` of `n+1` pairwise unit-distance points are linearly
independent. -/
theorem linearIndependent_diffVec {n : ℕ} {p : Fin (n + 1) → E} (hp : Equidistant p 1) :
    LinearIndependent ℝ (diffVec p) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 : ‖∑ i, c i • diffVec p i‖ ^ 2 = 0 := by rw [hc]; simp
  rw [norm_sq_combination hp] at h0
  by_contra hi
  have hcne : c ≠ 0 := fun h => hi (by rw [h]; rfl)
  have h1 : (0 : ℝ) ≤ 2⁻¹ * (∑ i, c i) ^ 2 := by positivity
  have h2 : (0 : ℝ) < 2⁻¹ * ∑ i, c i ^ 2 := by
    have := aux_sum_sq_pos hcne
    linarith
  linarith

/-- Clause (a) at an arbitrary positive common distance `r` (the unit-distance case
rescaled). -/
theorem linearIndependent_diffVec_of_pos {n : ℕ} {r : ℝ} (hr : 0 < r)
    {p : Fin (n + 1) → E} (hp : Equidistant p r) : LinearIndependent ℝ (diffVec p) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hq : Equidistant (fun i => r⁻¹ • p i) 1 := by
    intro i j hij
    rw [dist_eq_norm, ← smul_sub, norm_smul, ← dist_eq_norm, hp i j hij,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    field_simp
  have hd : ∀ i : Fin n, diffVec (fun i => r⁻¹ • p i) i = r⁻¹ • diffVec p i := by
    intro i
    simp only [diffVec, smul_sub]
  have h1 := linearIndependent_diffVec hq
  rw [Fintype.linearIndependent_iff] at h1 ⊢
  intro c hc i
  have hsum : ∑ i, (r * c i) • diffVec (fun i => r⁻¹ • p i) i = 0 := by
    rw [← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hd j, smul_smul]
    congr 1
    field_simp
  have := h1 (fun i => r * c i) hsum i
  simpa [hr0] using this

/-- **Lemma lem:equidistance, clause (b).** In a finite-dimensional real inner
product space, `n` points at pairwise distance `r > 0` force `n ≤ finrank + 1`:
equality among peers is at most `dim + 1` peers. -/
theorem card_le_finrank_succ [FiniteDimensional ℝ E] {n : ℕ} {r : ℝ} (hr : 0 < r)
    {p : Fin n → E} (hp : Equidistant p r) : n ≤ Module.finrank ℝ E + 1 := by
  cases n with
  | zero => simp
  | succ k =>
    have h := (linearIndependent_diffVec_of_pos hr hp).fintype_card_le_finrank
    simp only [Fintype.card_fin] at h
    omega

/-- **Lemma lem:equidistance, clause (b) in `ℝ^d`.** There are at most `d+1` points
in `ℝ^d` with pairwise equal (positive) distances; equivalently `N` pairwise
equidistant points exist in `ℝ^d` only when `d ≥ N-1`, written subtraction-free as
`N ≤ d + 1`. -/
theorem card_le_dim_succ {d n : ℕ} {r : ℝ} (hr : 0 < r)
    {p : Fin n → EuclideanSpace ℝ (Fin d)} (hp : Equidistant p r) : n ≤ d + 1 := by
  have h := card_le_finrank_succ hr hp
  rwa [finrank_euclideanSpace_fin] at h

/-- The dimension price of flat equality, in the form used in the introduction: a
cell of `N` mutually equidistant peers cannot be realized in `ℝ^d` unless the
ambient dimension satisfies `N ≤ d + 1`; hence `N` peers cost `N-1` dimensions. -/
theorem dimension_price_of_equality {N d : ℕ} {r : ℝ} (hr : 0 < r)
    (h : ∃ p : Fin N → EuclideanSpace ℝ (Fin d), Equidistant p r) : N ≤ d + 1 := by
  obtain ⟨p, hp⟩ := h
  exact card_le_dim_succ hr hp

end HSFN.Equidistance
