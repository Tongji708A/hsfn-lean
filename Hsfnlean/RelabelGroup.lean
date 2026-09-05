/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Relabel

/-!
# The relabeling group (Lemma lem:dup-digit(ii), group structure)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409),
Lemma `lem:dup-digit`(ii) and its "Classical counterpart" paragraph: the
relabelings of part (ii) are the automorphisms of the rooted `N`-ary tree, the
iterated wreath product of copies of `S_N`; what differs is the marking, which
cuts every non-root factor to `Stab_{S_N}(0) ≅ S_{N-1}`.

`Hsfnlean.Relabel` builds, from a family `τ : List (Fin N) → Equiv.Perm (Fin N)`
of cell-wise digit permutations, the bijection `relabelAddr τ` of `Addr N m`,
shows it is a graph automorphism, and shows it preserves the marking when every
non-root `τ w` fixes the digit `0`. This file adds the group layer:

* `relabelOne`, `relabelComp` — the unit and the **wreath-product multiplication**
  `(relabelComp τ σ) w = τ (relabel σ w) * σ w`, obtained by unwinding
  `relabelAux` (`relabel_comp` : `relabel τ ∘ relabel σ = relabel (relabelComp τ σ)`);
* `relabelPerm` — the induced element of `Equiv.Perm (Addr N m)`, with
  `relabelPerm τ * relabelPerm σ = relabelPerm (relabelComp τ σ)`;
* `relabelSubgroup` — the induced permutations form a subgroup of
  `Equiv.Perm (Addr N m)`, closed under composition and inverses;
* `relabelIso` — each such permutation is an automorphism of `graph N m`,
  packaged as a `SimpleGraph.Iso`, the composition law being the same one;
* `FixesZero`, `markedRelabelSubgroup` — the marked layer: the families whose
  non-root factors lie in `Stab_{S_N}(0) ≅ S_{N-1}` form a subgroup, and
  `mem_markedRelabelSubgroup_iff` is the paper's *if and only if*: a relabeling
  preserves the marking exactly when it comes from such a family. The inclusion
  `markedRelabelSubgroup < relabelSubgroup` is strict, which is the lemma's
  closing remark that the marking is **not** a graph invariant.

The index range of the paper's families is `w = ε` (the virtual root,
unconstrained) together with the nonempty `w` of length `< m`: those are exactly
the words whose local permutation acts on an address of `Addr N m`. `FixesZero`
uses that range verbatim.

## What is *not* formalized here

* The abstract identification of `relabelSubgroup N m` with the depth-`m`
  iterated permutational wreath product `S_N ≀ ⋯ ≀ S_N` is **not** proved. What is
  proved is the multiplication law (`relabelComp`, `relabelPerm_mul`), which is
  the wreath law, and that the image is a subgroup. Note that
  `τ ↦ relabelPerm τ` is *not* injective — families agreeing on all words of
  length `< m` induce the same permutation — so `relabelSubgroup N m` is a
  quotient of the family group, and an isomorphism statement would first have to
  cut the index set down to `{w : w.length < m}`.
* It is **not** proved that `relabelSubgroup N m` is *all* of
  `(graph N m).Aut`; only that every one of its elements is an automorphism
  (`adj_iff_of_mem_relabelSubgroup`, `relabelIso`). The paper likewise only
  asserts the relabelings *are* automorphisms, of the rooted `N`-ary tree.
* `Stab_{S_N}(0) ≅ S_{N-1}` is proved as `Nonempty (… ≃* Equiv.Perm (Fin (N-1)))`,
  i.e. as existence of an isomorphism; no canonical map is exported.
* Part (i) of `lem:dup-digit` (the geometric co-location statement about the
  realization `ι`) is outside this file; only the combinatorial marking `IsMark`
  of `Hsfnlean.Family` is used.

The statements below are frozen; only the proofs are to be supplied.
-/

namespace HSFN

variable {N m : ℕ}

/-! ## The wreath-product group law on families of digit permutations -/

/-- The identity family: the trivial digit permutation at every word. -/
def relabelOne : List (Fin N) → Equiv.Perm (Fin N) := fun _ => 1

/-- The **wreath-product multiplication** of two families, read off from
`relabelAux`: the digit following the prefix `w` is first moved by `σ w`, and the
outer family then acts at the *already relabeled* prefix `relabel σ w`. With the
`Equiv.Perm` convention `(f * g) x = f (g x)`, this is
`relabelComp τ σ w = τ (relabel σ w) * σ w`. -/
def relabelComp (τ σ : List (Fin N) → Equiv.Perm (Fin N)) :
    List (Fin N) → Equiv.Perm (Fin N) :=
  fun w => τ (relabel σ w) * σ w

private theorem aux_relabelAux_relabelOne (pre l : List (Fin N)) :
    relabelAux (relabelOne (N := N)) pre l = l := by
  induction l generalizing pre with
  | nil => rfl
  | cons d rest ih => simp [relabelAux, relabelOne, ih]

/-- The identity family induces the identity relabeling of words. -/
theorem relabel_relabelOne (a : List (Fin N)) : relabel (relabelOne (N := N)) a = a := by
  exact aux_relabelAux_relabelOne [] a

/-- The identity family induces the identity map of addresses. -/
theorem relabelAddr_relabelOne (a : Addr N m) :
    relabelAddr (relabelOne (N := N)) a = a := by
  apply Addr.ext
  exact relabel_relabelOne a.1

/-- (a) `relabelAddr` of the identity family is the identity map. -/
theorem relabelAddr_relabelOne_eq_id :
    relabelAddr (N := N) (m := m) relabelOne = id := by
  funext a
  exact relabelAddr_relabelOne a

private theorem aux_relabelAux_concat (σ : List (Fin N) → Equiv.Perm (Fin N))
    (pre l : List (Fin N)) (d : Fin N) :
    relabelAux σ pre (l ++ [d]) = relabelAux σ pre l ++ [σ (pre ++ l) d] := by
  induction l generalizing pre with
  | nil => simp [relabelAux]
  | cons e rest ih => simp [relabelAux, ih (pre ++ [e])]

private theorem aux_relabel_concat (σ : List (Fin N) → Equiv.Perm (Fin N))
    (l : List (Fin N)) (d : Fin N) :
    relabel σ (l ++ [d]) = relabel σ l ++ [σ l d] := by
  have h := aux_relabelAux_concat σ [] l d
  simpa [relabel] using h

private theorem aux_relabelAux_comp (τ σ : List (Fin N) → Equiv.Perm (Fin N))
    (pre l : List (Fin N)) :
    relabelAux τ (relabel σ pre) (relabelAux σ pre l)
      = relabelAux (relabelComp τ σ) pre l := by
  induction l generalizing pre with
  | nil => rfl
  | cons d rest ih =>
    have hpre : relabel σ pre ++ [σ pre d] = relabel σ (pre ++ [d]) :=
      (aux_relabel_concat σ pre d).symm
    simp only [relabelAux]
    rw [hpre, ih (pre ++ [d])]
    rfl

/-- (b) **Composition law on words** (the wreath-product multiplication):
relabeling by `σ` and then by `τ` is relabeling by `relabelComp τ σ`. -/
theorem relabel_comp (τ σ : List (Fin N) → Equiv.Perm (Fin N)) (a : List (Fin N)) :
    relabel τ (relabel σ a) = relabel (relabelComp τ σ) a := by
  have h := aux_relabelAux_comp τ σ [] a
  have h0 : relabel σ ([] : List (Fin N)) = [] := rfl
  rw [h0] at h
  exact h

/-- (b) **Composition law on addresses**. -/
theorem relabelAddr_comp (τ σ : List (Fin N) → Equiv.Perm (Fin N)) (a : Addr N m) :
    relabelAddr τ (relabelAddr σ a) = relabelAddr (relabelComp τ σ) a := by
  apply Addr.ext
  exact relabel_comp τ σ a.1

/-- (b) **Composition law**, stated for the maps themselves. -/
theorem relabelAddr_comp_eq (τ σ : List (Fin N) → Equiv.Perm (Fin N)) :
    relabelAddr (m := m) τ ∘ relabelAddr (m := m) σ
      = relabelAddr (m := m) (relabelComp τ σ) := by
  funext a
  exact relabelAddr_comp τ σ a

/-- The wreath multiplication is associative. -/
theorem relabelComp_assoc (τ σ ρ : List (Fin N) → Equiv.Perm (Fin N)) :
    relabelComp (relabelComp τ σ) ρ = relabelComp τ (relabelComp σ ρ) := by
  funext w
  show τ (relabel σ (relabel ρ w)) * σ (relabel ρ w) * ρ w
      = τ (relabel (relabelComp σ ρ) w) * (σ (relabel ρ w) * ρ w)
  rw [relabel_comp, mul_assoc]

/-- The identity family is a right unit for the wreath multiplication. -/
theorem relabelComp_one_right (τ : List (Fin N) → Equiv.Perm (Fin N)) :
    relabelComp τ relabelOne = τ := by
  funext w
  show τ (relabel relabelOne w) * relabelOne w = τ w
  rw [relabel_relabelOne]
  exact mul_one _

/-- The identity family is a left unit for the wreath multiplication. -/
theorem relabelComp_one_left (τ : List (Fin N) → Equiv.Perm (Fin N)) :
    relabelComp relabelOne τ = τ := by
  funext w
  show relabelOne (relabel τ w) * τ w = τ w
  exact one_mul _

private theorem aux_exists_relabelComp_left_inv (τ : List (Fin N) → Equiv.Perm (Fin N)) :
    ∃ σ : List (Fin N) → Equiv.Perm (Fin N), relabelComp σ τ = relabelOne := by
  classical
  refine ⟨fun v => (τ (Function.invFun (relabel τ) v))⁻¹, ?_⟩
  funext w
  show (τ (Function.invFun (relabel τ) (relabel τ w)))⁻¹ * τ w = relabelOne w
  rw [Function.leftInverse_invFun (relabel_injective τ) w]
  exact inv_mul_cancel _

/-- Every family has a two-sided inverse family for the wreath multiplication.
Unfolding `relabelComp σ τ = relabelOne` gives the paper's formula for the
inverse family, `σ (relabel τ w) = (τ w)⁻¹`, i.e. `τ'_{φ(w)} = τ_w⁻¹`. -/
theorem exists_relabelComp_inv (τ : List (Fin N) → Equiv.Perm (Fin N)) :
    ∃ σ : List (Fin N) → Equiv.Perm (Fin N),
      relabelComp σ τ = relabelOne ∧ relabelComp τ σ = relabelOne := by
  obtain ⟨σ, hσ⟩ := aux_exists_relabelComp_left_inv τ
  obtain ⟨ρ, hρ⟩ := aux_exists_relabelComp_left_inv σ
  refine ⟨σ, hσ, ?_⟩
  have h1 : relabelComp σ (relabelComp τ σ) = σ := by
    rw [← relabelComp_assoc, hσ, relabelComp_one_left]
  have h2 : relabelComp ρ (relabelComp σ (relabelComp τ σ)) = relabelOne := by
    rw [h1, hρ]
  rw [← relabelComp_assoc, hρ, relabelComp_one_left] at h2
  exact h2

/-! ## The induced permutations of the address set -/

/-- The permutation of `Addr N m` induced by a family of cell-wise digit
permutations (Lemma lem:dup-digit(ii)). -/
noncomputable def relabelPerm (τ : List (Fin N) → Equiv.Perm (Fin N)) : Equiv.Perm (Addr N m) :=
  Equiv.ofBijective (relabelAddr (m := m) τ) (relabelAddr_bijective τ)

@[simp] theorem relabelPerm_apply (τ : List (Fin N) → Equiv.Perm (Fin N)) (a : Addr N m) :
    relabelPerm τ a = relabelAddr τ a := by
  rfl

/-- (c) The identity family induces the identity permutation. -/
theorem relabelPerm_one : relabelPerm (N := N) (m := m) relabelOne = 1 := by
  ext a
  simp [relabelAddr_relabelOne]

/-- (c) **Closure under composition**: the product of two induced permutations is
the permutation induced by the wreath product of the two families. -/
theorem relabelPerm_mul (τ σ : List (Fin N) → Equiv.Perm (Fin N)) :
    relabelPerm (m := m) τ * relabelPerm (m := m) σ
      = relabelPerm (m := m) (relabelComp τ σ) := by
  ext a
  simp [Equiv.Perm.mul_apply, relabelAddr_comp]

/-- (c) **Closure under inverses**: the inverse of an induced permutation is
induced by a family. -/
theorem exists_relabelPerm_inv (τ : List (Fin N) → Equiv.Perm (Fin N)) :
    ∃ σ : List (Fin N) → Equiv.Perm (Fin N),
      (relabelPerm (m := m) τ)⁻¹ = relabelPerm (m := m) σ := by
  obtain ⟨σ, h1, -⟩ := exists_relabelComp_inv τ
  refine ⟨σ, ?_⟩
  have h : relabelPerm (m := m) σ * relabelPerm (m := m) τ = 1 := by
    rw [relabelPerm_mul, h1, relabelPerm_one]
  exact inv_eq_of_mul_eq_one_left h

/-- (c) **The relabelings form a subgroup of `Equiv.Perm (Addr N m)`**: the image
of the family construction is closed under composition and inverses. This is the
depth-`m` iterated wreath product of copies of `S_N` acting on the address set. -/
def relabelSubgroup (N m : ℕ) : Subgroup (Equiv.Perm (Addr N m)) where
  carrier := Set.range (fun τ : List (Fin N) → Equiv.Perm (Fin N) => relabelPerm (m := m) τ)
  mul_mem' := by
    rintro a b ⟨τ, rfl⟩ ⟨σ, rfl⟩
    exact ⟨relabelComp τ σ, (relabelPerm_mul τ σ).symm⟩
  one_mem' := by
    exact ⟨relabelOne, relabelPerm_one⟩
  inv_mem' := by
    rintro a ⟨τ, rfl⟩
    obtain ⟨σ, hσ⟩ := exists_relabelPerm_inv (m := m) τ
    exact ⟨σ, hσ.symm⟩

theorem mem_relabelSubgroup_iff (f : Equiv.Perm (Addr N m)) :
    f ∈ relabelSubgroup N m ↔ ∃ τ : List (Fin N) → Equiv.Perm (Fin N), relabelPerm τ = f := by
  exact Iff.rfl

/-! ## The relabelings are graph automorphisms -/

/-- (d) Each induced permutation preserves and reflects adjacency
(Lemma lem:dup-digit(ii)). -/
theorem adj_relabelPerm_iff (τ : List (Fin N) → Equiv.Perm (Fin N)) (u v : Addr N m) :
    (graph N m).Adj (relabelPerm τ u) (relabelPerm τ v) ↔ (graph N m).Adj u v := by
  simp only [relabelPerm_apply]
  exact adj_relabelAddr_iff τ u v

/-- (d) The relabeling packaged as an automorphism of the HSFN graph. -/
noncomputable def relabelIso (τ : List (Fin N) → Equiv.Perm (Fin N)) : graph N m ≃g graph N m where
  toEquiv := relabelPerm τ
  map_rel_iff' := by
    intro a b
    exact adj_relabelPerm_iff τ a b

@[simp] theorem relabelIso_apply (τ : List (Fin N) → Equiv.Perm (Fin N)) (a : Addr N m) :
    relabelIso τ a = relabelAddr τ a := by
  rfl

/-- (d) The automorphisms compose by the same wreath-product law. -/
theorem relabelIso_comp (τ σ : List (Fin N) → Equiv.Perm (Fin N)) :
    (relabelIso (m := m) τ).comp (relabelIso (m := m) σ)
      = relabelIso (m := m) (relabelComp τ σ) := by
  ext a
  simp [relabelAddr_comp]

/-- (d) The identity family induces the identity automorphism. -/
theorem relabelIso_relabelOne :
    relabelIso (N := N) (m := m) relabelOne = SimpleGraph.Iso.refl := by
  ext a
  simp [relabelAddr_relabelOne]

/-- (c)+(d) Every element of the relabeling subgroup is an automorphism of
`graph N m`. -/
theorem adj_iff_of_mem_relabelSubgroup {f : Equiv.Perm (Addr N m)}
    (hf : f ∈ relabelSubgroup N m) (u v : Addr N m) :
    (graph N m).Adj (f u) (f v) ↔ (graph N m).Adj u v := by
  obtain ⟨τ, rfl⟩ := hf
  exact adj_relabelPerm_iff τ u v

/-! ## The marked layer: `Stab_{S_N}(0)` in every non-root factor -/

/-- A family whose every non-root member acting on `Addr N m` fixes the digit
`0`, i.e. lies in `Stab_{S_N}(0) ≅ S_{N-1}`. The index range is the paper's:
`w ≠ ε` with `|w| < m`, the words carrying a local permutation that acts on an
address of `Addr N m`; the root permutation `τ []` is unconstrained, because the
tier-1 cell carries no mark. -/
def FixesZero (hN : 0 < N) (m : ℕ) (τ : List (Fin N) → Equiv.Perm (Fin N)) : Prop :=
  ∀ w : List (Fin N), w ≠ [] → w.length < m → τ w ⟨0, hN⟩ = ⟨0, hN⟩

/-- `FixesZero` is membership of every non-root factor in `Stab_{S_N}(0)`,
the paper's phrasing. -/
theorem fixesZero_iff_mem_stabilizer (hN : 0 < N)
    (τ : List (Fin N) → Equiv.Perm (Fin N)) :
    FixesZero hN m τ ↔
      ∀ w : List (Fin N), w ≠ [] → w.length < m →
        τ w ∈ MulAction.stabilizer (Equiv.Perm (Fin N)) (⟨0, hN⟩ : Fin N) := by
  constructor
  · intro h w hw hwm
    rw [MulAction.mem_stabilizer_iff]
    exact h w hw hwm
  · intro h w hw hwm
    have hs := h w hw hwm
    rw [MulAction.mem_stabilizer_iff] at hs
    exact hs

/-- `Stab_{S_N}(0) ≅ S_{N-1}`, the identification named in Lemma
lem:dup-digit(ii) and in its "Classical counterpart" paragraph. -/
theorem nonempty_stabilizer_mulEquiv (hN : 0 < N) :
    Nonempty (MulAction.stabilizer (Equiv.Perm (Fin N)) (⟨0, hN⟩ : Fin N)
      ≃* Equiv.Perm (Fin (N - 1))) := by
  classical
  have hcard : Fintype.card { x : Fin N // x ≠ (⟨0, hN⟩ : Fin N) } = N - 1 := by
    simp [Fintype.card_subtype_compl]
  let e : { x : Fin N // x ≠ (⟨0, hN⟩ : Fin N) } ≃ Fin (N - 1) :=
    Fintype.equivFinOfCardEq hcard
  let F : Equiv.Perm { x : Fin N // x ≠ (⟨0, hN⟩ : Fin N) } →*
      MulAction.stabilizer (Equiv.Perm (Fin N)) (⟨0, hN⟩ : Fin N) :=
    Equiv.Perm.ofSubtype.codRestrict _ (fun f => by
      rw [MulAction.mem_stabilizer_iff]
      show Equiv.Perm.ofSubtype f (⟨0, hN⟩ : Fin N) = (⟨0, hN⟩ : Fin N)
      exact Equiv.Perm.ofSubtype_apply_of_not_mem f (by simp))
  have hFinj : Function.Injective F := by
    intro f g h
    exact Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h)
  have hFsurj : Function.Surjective F := by
    rintro ⟨g, hg⟩
    rw [MulAction.mem_stabilizer_iff] at hg
    have hg0 : g (⟨0, hN⟩ : Fin N) = (⟨0, hN⟩ : Fin N) := hg
    have hstab : ∀ x : Fin N, (g x ≠ (⟨0, hN⟩ : Fin N)) ↔ (x ≠ (⟨0, hN⟩ : Fin N)) := by
      intro x
      constructor
      · intro hx hxe
        exact hx (by rw [hxe, hg0])
      · intro hx hgx
        exact hx (g.injective (hgx.trans hg0.symm))
    refine ⟨Equiv.Perm.subtypePerm g hstab, ?_⟩
    apply Subtype.ext
    refine Equiv.Perm.ofSubtype_subtypePerm hstab ?_
    intro x hx hxe
    exact hx (by rw [hxe, hg0])
  exact ⟨(MulEquiv.ofBijective F ⟨hFinj, hFsurj⟩).symm.trans e.permCongrHom⟩

theorem fixesZero_relabelOne (hN : 0 < N) : FixesZero hN m (relabelOne (N := N)) := by
  intro w _ _
  rfl

private theorem aux_length_relabel (σ : List (Fin N) → Equiv.Perm (Fin N))
    (l : List (Fin N)) : (relabel σ l).length = l.length :=
  length_relabelAux σ [] l

private theorem aux_relabel_ne_nil (σ : List (Fin N) → Equiv.Perm (Fin N))
    {l : List (Fin N)} (hl : l ≠ []) : relabel σ l ≠ [] := by
  have hpos : 0 < (relabel σ l).length := by
    rw [aux_length_relabel]
    exact List.length_pos_of_ne_nil hl
  exact List.ne_nil_of_length_pos hpos

/-- The marked families are closed under the wreath multiplication. -/
theorem fixesZero_relabelComp (hN : 0 < N) {τ σ : List (Fin N) → Equiv.Perm (Fin N)}
    (hτ : FixesZero hN m τ) (hσ : FixesZero hN m σ) : FixesZero hN m (relabelComp τ σ) := by
  intro w hw hwm
  have hlen : (relabel σ w).length = w.length := aux_length_relabel σ w
  have hne : relabel σ w ≠ [] := aux_relabel_ne_nil σ hw
  have hlt : (relabel σ w).length < m := by rw [hlen]; exact hwm
  show τ (relabel σ w) (σ w ⟨0, hN⟩) = ⟨0, hN⟩
  rw [hσ w hw hwm, hτ (relabel σ w) hne hlt]

/-- The marked families are closed under inverses. -/
theorem exists_fixesZero_inv (hN : 0 < N) {τ : List (Fin N) → Equiv.Perm (Fin N)}
    (hτ : FixesZero hN m τ) :
    ∃ σ : List (Fin N) → Equiv.Perm (Fin N),
      FixesZero hN m σ ∧ relabelComp σ τ = relabelOne ∧ relabelComp τ σ = relabelOne := by
  obtain ⟨σ, h1, h2⟩ := exists_relabelComp_inv τ
  refine ⟨σ, ?_, h1, h2⟩
  intro v hv hvm
  have hsurj : relabel τ (relabel σ v) = v := by
    rw [relabel_comp, h2, relabel_relabelOne]
  have hlen : (relabel σ v).length = v.length := aux_length_relabel σ v
  have hne : relabel σ v ≠ [] := aux_relabel_ne_nil σ hv
  have hlt : (relabel σ v).length < m := by rw [hlen]; exact hvm
  have hkey : σ (relabel τ (relabel σ v)) * τ (relabel σ v) = 1 := congrFun h1 (relabel σ v)
  rw [hsurj] at hkey
  have hσv : σ v = (τ (relabel σ v))⁻¹ := eq_inv_of_mul_eq_one_left hkey
  rw [hσv]
  exact Equiv.Perm.inv_eq_iff_eq.mpr (hτ (relabel σ v) hne hlt).symm

/-- The **marked relabeling group**: the subgroup of `Equiv.Perm (Addr N m)`
induced by families whose non-root factors lie in `Stab_{S_N}(0) ≅ S_{N-1}`. -/
def markedRelabelSubgroup (hN : 0 < N) (m : ℕ) : Subgroup (Equiv.Perm (Addr N m)) where
  carrier := { f | ∃ τ : List (Fin N) → Equiv.Perm (Fin N),
    FixesZero hN m τ ∧ relabelPerm (m := m) τ = f }
  mul_mem' := by
    rintro a b ⟨τ, hτ, rfl⟩ ⟨σ, hσ, rfl⟩
    exact ⟨relabelComp τ σ, fixesZero_relabelComp hN hτ hσ, (relabelPerm_mul τ σ).symm⟩
  one_mem' := by
    exact ⟨relabelOne, fixesZero_relabelOne hN, relabelPerm_one⟩
  inv_mem' := by
    rintro a ⟨τ, hτ, rfl⟩
    obtain ⟨σ, hσ, hl, -⟩ := exists_fixesZero_inv hN hτ
    refine ⟨σ, hσ, ?_⟩
    have h : relabelPerm (m := m) σ * relabelPerm (m := m) τ = 1 := by
      rw [relabelPerm_mul, hl, relabelPerm_one]
    exact (inv_eq_of_mul_eq_one_left h).symm

theorem markedRelabelSubgroup_le_relabelSubgroup (hN : 0 < N) (m : ℕ) :
    markedRelabelSubgroup hN m ≤ relabelSubgroup N m := by
  rintro f ⟨τ, -, rfl⟩
  exact ⟨τ, rfl⟩

private theorem aux_relabelAux_congr (τ τ' : List (Fin N) → Equiv.Perm (Fin N)) (K : ℕ)
    (h : ∀ w : List (Fin N), w.length < K → τ w = τ' w) :
    ∀ pre l : List (Fin N), pre.length + l.length ≤ K →
      relabelAux τ pre l = relabelAux τ' pre l := by
  intro pre l
  induction l generalizing pre with
  | nil => intro _; rfl
  | cons d rest ih =>
    intro hle
    simp only [List.length_cons] at hle
    have hpre : pre.length < K := by omega
    have h2 : (pre ++ [d]).length + rest.length ≤ K := by
      simp only [List.length_append, List.length_singleton]
      omega
    simp only [relabelAux, h pre hpre, ih (pre ++ [d]) h2]

private theorem aux_relabelAddr_congr (τ τ' : List (Fin N) → Equiv.Perm (Fin N))
    (h : ∀ w : List (Fin N), w.length < m → τ w = τ' w) (a : Addr N m) :
    relabelAddr (m := m) τ a = relabelAddr (m := m) τ' a := by
  apply Addr.ext
  exact aux_relabelAux_congr τ τ' m h [] a.1 (by simpa using a.2.2)

private theorem aux_isMark_relabelAddr_iff_of_fixesZero (hN : 0 < N)
    (τ : List (Fin N) → Equiv.Perm (Fin N)) (hτ : FixesZero hN m τ) (a : Addr N m) :
    IsMark (relabelAddr τ a) ↔ IsMark a := by
  classical
  obtain ⟨τ', hτ'⟩ : ∃ τ' : List (Fin N) → Equiv.Perm (Fin N),
      ∀ w : List (Fin N), τ' w = if w.length < m then τ w else 1 :=
    ⟨_, fun _ => rfl⟩
  have hcongr : relabelAddr (m := m) τ a = relabelAddr (m := m) τ' a :=
    aux_relabelAddr_congr τ τ' (fun w hw => by rw [hτ' w, if_pos hw]) a
  rw [hcongr]
  refine isMark_relabelAddr_iff τ' hN ?_ a
  intro w hw
  by_cases hlt : w.length < m
  · rw [hτ' w, if_pos hlt]
    exact hτ w hw hlt
  · rw [hτ' w, if_neg hlt]
    rfl

/-- Every element of the marked relabeling group preserves the marking `M`
(Lemma lem:dup-digit(ii), the "if" direction). -/
theorem isMark_iff_of_mem_markedRelabelSubgroup (hN : 0 < N)
    {f : Equiv.Perm (Addr N m)} (hf : f ∈ markedRelabelSubgroup hN m) (a : Addr N m) :
    IsMark (f a) ↔ IsMark a := by
  obtain ⟨τ, hτ, rfl⟩ := hf
  rw [relabelPerm_apply]
  exact aux_isMark_relabelAddr_iff_of_fixesZero hN τ hτ a

/-- The "only if" direction of Lemma lem:dup-digit(ii). The hypothesis is the
paper's `φ(M) ⊆ M`, not the two-sided version: already the forward inclusion
forces every non-root local permutation to fix the digit `0`, at every word with
room for a marked child below it. -/
theorem fixesZero_of_mapsTo_isMark (hN : 0 < N)
    (τ : List (Fin N) → Equiv.Perm (Fin N))
    (h : ∀ a : Addr N m, IsMark a → IsMark (relabelAddr τ a))
    (w : List (Fin N)) (hw : w ≠ []) (hwm : w.length < m) :
    τ w ⟨0, hN⟩ = ⟨0, hN⟩ := by
  by_contra hcon
  obtain ⟨a, ha, hna⟩ := exists_mark_moved (m := m) τ hN hw hwm hcon
  exact hna (h a ha)

/-- **Lemma lem:dup-digit(ii), the marking clause, in the paper's `φ(M) ⊆ M`
form**: the forward inclusion already characterizes the marked families. -/
theorem mapsTo_isMark_relabelAddr_iff_fixesZero (hN : 0 < N)
    (τ : List (Fin N) → Equiv.Perm (Fin N)) :
    (∀ a : Addr N m, IsMark a → IsMark (relabelAddr τ a)) ↔ FixesZero hN m τ := by
  constructor
  · intro h w hw hwm
    exact fixesZero_of_mapsTo_isMark hN τ h w hw hwm
  · intro hτ a ha
    exact (aux_isMark_relabelAddr_iff_of_fixesZero hN τ hτ a).mpr ha

/-- **Lemma lem:dup-digit(ii), the marking clause, exactly as stated in the paper**:
`φ(M) = M` *if and only if* every non-root local permutation fixes the digit `0`.
Together with `mapsTo_isMark_relabelAddr_iff_fixesZero` this is the paper's
remark that `φ(M) ⊆ M` and `φ(M) = M` are equivalent for the injective `φ`. -/
theorem isMark_relabelAddr_iff_iff_fixesZero (hN : 0 < N)
    (τ : List (Fin N) → Equiv.Perm (Fin N)) :
    (∀ a : Addr N m, IsMark (relabelAddr τ a) ↔ IsMark a) ↔ FixesZero hN m τ := by
  constructor
  · intro h
    exact (mapsTo_isMark_relabelAddr_iff_fixesZero hN τ).mp fun a ha => (h a).mpr ha
  · intro hτ a
    exact aux_isMark_relabelAddr_iff_of_fixesZero hN τ hτ a

/-- **Lemma lem:dup-digit(ii) at group level**: inside the relabeling group, the
marked subgroup is exactly the stabilizer of the marking. -/
theorem mem_markedRelabelSubgroup_iff (hN : 0 < N) (f : Equiv.Perm (Addr N m)) :
    f ∈ markedRelabelSubgroup hN m ↔
      (f ∈ relabelSubgroup N m ∧ ∀ a : Addr N m, IsMark (f a) ↔ IsMark a) := by
  constructor
  · intro hf
    exact ⟨markedRelabelSubgroup_le_relabelSubgroup hN m hf,
      fun a => isMark_iff_of_mem_markedRelabelSubgroup hN hf a⟩
  · rintro ⟨hf, hmark⟩
    obtain ⟨τ, rfl⟩ := hf
    refine ⟨τ, ?_, rfl⟩
    refine (isMark_relabelAddr_iff_iff_fixesZero hN τ).mp ?_
    intro a
    have hm := hmark a
    rwa [relabelPerm_apply] at hm

/-- **The marking is not a graph invariant** (the closing remark of Lemma
lem:dup-digit): as soon as there is a digit other than `0` and a tier carrying a
mark, some relabeling automorphism of `graph N m` moves the marked set. -/
theorem exists_mem_relabelSubgroup_moving_mark (hN : 0 < N) (h2N : 2 ≤ N) (hm : 2 ≤ m) :
    ∃ f ∈ relabelSubgroup N m, ∃ a : Addr N m, IsMark a ∧ ¬ IsMark (f a) := by
  classical
  have h1N : 1 < N := h2N
  have hd : (⟨0, hN⟩ : Fin N) ≠ (⟨1, h1N⟩ : Fin N) := by
    simp [Fin.ext_iff]
  refine ⟨relabelPerm (m := m) (fun _ => Equiv.swap (⟨0, hN⟩ : Fin N) (⟨1, h1N⟩ : Fin N)),
    ⟨_, rfl⟩, ?_⟩
  have hw : ([(⟨0, hN⟩ : Fin N)] : List (Fin N)) ≠ [] := by simp
  have hwm : ([(⟨0, hN⟩ : Fin N)] : List (Fin N)).length < m := by
    simp only [List.length_singleton]
    omega
  have hτ : (fun _ : List (Fin N) => Equiv.swap (⟨0, hN⟩ : Fin N) (⟨1, h1N⟩ : Fin N))
      [(⟨0, hN⟩ : Fin N)] ⟨0, hN⟩ ≠ ⟨0, hN⟩ := by
    show Equiv.swap (⟨0, hN⟩ : Fin N) (⟨1, h1N⟩ : Fin N) ⟨0, hN⟩ ≠ ⟨0, hN⟩
    rw [Equiv.swap_apply_left]
    exact fun h => hd h.symm
  obtain ⟨a, ha, hna⟩ :=
    exists_mark_moved (m := m)
      (fun _ : List (Fin N) => Equiv.swap (⟨0, hN⟩ : Fin N) (⟨1, h1N⟩ : Fin N)) hN hw hwm hτ
  refine ⟨a, ha, ?_⟩
  rw [relabelPerm_apply]
  exact hna

/-- The same statement as a strict inclusion of groups: the marking cuts the
relabeling group down, so `markedRelabelSubgroup` is a *proper* subgroup. -/
theorem markedRelabelSubgroup_lt_relabelSubgroup (hN : 0 < N) (h2N : 2 ≤ N) (hm : 2 ≤ m) :
    markedRelabelSubgroup hN m < relabelSubgroup N m := by
  refine lt_of_le_of_ne (markedRelabelSubgroup_le_relabelSubgroup hN m) ?_
  intro heq
  obtain ⟨f, hf, a, ha, hna⟩ := exists_mem_relabelSubgroup_moving_mark (m := m) hN h2N hm
  have hfm : f ∈ markedRelabelSubgroup hN m := by
    rw [heq]
    exact hf
  exact hna ((isMark_iff_of_mem_markedRelabelSubgroup hN hfm a).mpr ha)

end HSFN
