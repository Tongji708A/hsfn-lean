/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Calculus

/-!
# The boundary edge-cut law of a graft (Lemma lem:edge-cut)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409),
Section "The Graft Laws", Lemma `lem:edge-cut` ("Boundary edge-cut law"), whose proof is
deferred to the operations-calculus appendix `app:calculus`.

The paper's statement, for `graft(a → b)` applicable at `x` with `|a| = |b|`, result `x'`, and
moved set the deployed cells of `cone(a)` (and their images in `cone(b)`):

* **(i) Node level.** In the state graph `G(x)` exactly `N` edges join the moved slots to the
  rest, namely the `N` uplinks from the cell `C(a)` into the anchor `a`; in `G(x')` the created
  boundary is likewise the `N` uplinks into `b`.
* **(ii) Cell level.** In the deployed-cell graph `Γ(x)` the graft cuts exactly `1 + σ_x(a)`
  edges, all incident to `a` (the parent edge `{a, pre(a)}` and the `σ_x(a)` sibling edges), and
  creates exactly `1 + σ_{x'}(b)` edges at `b`. Edges with both endpoints outside the moved set
  are equal in `Γ(x)` and `Γ(x')`, while the substitution maps the internal edges bijectively.

## What this file does

It carves the two boundaries out as `Finset`s of ordered pairs (moved endpoint, static endpoint)
and states the identities above.

* Node level (i) is formalized in full: `crossing_forces_uplink` (a crossing pair is forced to be
  an uplink `(a ++ [d], a)`), `cellW_subset_movedSlots` and `card_uplinks_into_anchor` (the
  converse and the count `N`), assembled into `boundaryPairs_eq` / `card_boundaryPairs` and
  transported to the target by `boundaryPairs_graft_eq` / `card_boundaryPairs_graft`.
  `sib_stays_moved` and `child_stays_moved` are the two prefix computations of the paper's proof:
  a sibling edge never crosses, and a child of a moved slot is moved.
* Cell level (ii) **is reached**, in this sense: `Γ(x)` is modelled by the word-level relation
  `AdjCell` on the deployed cells (vertex set `x.D`, the seed cell `[]` included, parent edges and
  deployed-sibling edges), the cut is `cellCutPairs`, and `cellCutPairs_eq`, `card_cellCutPairs`,
  `cellCutPairs_graft_eq`, `card_cellCutPairs_graft`, `cellsOutside_graft`,
  `adjCell_outside_graft`, `adjCell_moved_graft`, `movedCells_graft` and
  `substFalse_inj_on_movedCells` state its five assertions: the cut edge set, the count
  `1 + σ_x(a)`, the created edge set and its count `1 + σ_{x'}(b)`, invariance of the outside edges
  (over an outside vertex set that is itself unchanged), and the bijection on the internal ones —
  `movedCells_graft` supplying surjectivity of `a s ↦ b s` onto the moved cells of `x'` and
  `substFalse_inj_on_movedCells` its injectivity, with `card_movedCells_graft` the resulting count.
  `substTrue_inj_on_movedSlots` and `card_movedSlots_graft` are the same pair at the node level.

Two notes on how the counts are modelled. An edge is recorded as the *ordered* pair
`(moved endpoint, static endpoint)`; since a crossing edge has exactly one endpoint on each side
this loses nothing, and `Finset.card` of the pair set is the edge count. And `sigma` counts the
deployed sibling *cells* `pre(a)d ≠ a` rather than the digits `d`; the map `d ↦ pre(a)d` is
injective, so this is the paper's `σ_x(a)` verbatim.

## Out of scope here

* The isomorphism theorem `thm:graft-iso` itself. Only its suffix-covariance core, already proved
  in `Hsfnlean.Calculus` as `adjW_append_iff`, stands behind these statements.
* Indicator invariance at equal tier, the tier profile and the two-bin histogram transfer
  (`thm:graft-iso`(iii), `prop:kpi-affine`): nothing about `M0_t, o_t, h_t` is stated.
* The identification of `Γ(x) - ε` with the anchor overlay of `G(x)` (re-proved inside
  `prop:kpi-affine` in the paper): `AdjCell` is *defined* here by the parent/sibling clauses and
  is nowhere related to `AdjW` on the anchor slots.
* The selected-link mask `E`, the designated duplicates `M(x)`, the update cycle and
  `rem:graft-splice`.
* No claim is made about cross-tier grafts: the statements that mention `graft` and do not carry
  the hypothesis `a.length = b.length` are stated without it because they hold without it, not
  because the paper claims more.

The `aux_*` lemmas below re-derive, for use in this file, the `private` helpers of
`Hsfnlean.Calculus` (membership in `cellW` and `Sl`, the prefix bookkeeping, and the algebra of
`subst`); they are not new mathematics.
-/

namespace HSFN

namespace Calc

open Config

variable {N m : ℕ}

set_option linter.unusedVariables false

/-- Decidability of the two-clause word law, so that the boundary can be carved out of a
`Finset` by `Finset.filter`. -/
instance decidableAdjWEdgeCut : ∀ u v : Word N, Decidable (AdjW u v) := fun u v => by
  unfold AdjW; infer_instance

/-! ## Auxiliary facts re-derived from `Hsfnlean.Calculus` -/

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
  simp only [Sl, Finset.mem_biUnion, aux_mem_cellW]
  aesop

private theorem aux_dropLast_ne {w : Word N} (hw : w ≠ []) : w.dropLast ≠ w := by
  intro he
  have h1 := congrArg List.length he
  have h2 := List.length_pos_of_ne_nil hw
  simp only [List.length_dropLast] at h1
  omega

private theorem aux_parent_not_below {w : Word N} (hw : w ≠ []) : ¬ w <+: w.dropLast := by
  intro hp
  have h1 := hp.length_le
  have h2 := List.length_pos_of_ne_nil hw
  simp only [List.length_dropLast] at h1
  omega

private theorem aux_prefix_parent {a w : Word N} (hp : a <+: w) (hne : a ≠ w) :
    a <+: w.dropLast := by
  obtain ⟨t, rfl⟩ := hp
  have ht : t ≠ [] := by rintro rfl; simp at hne
  rw [List.dropLast_append_of_ne_nil ht]
  exact List.prefix_append _ _

private theorem aux_prefix_mem {x : Config N m} (hx : x.WF) {v w : Word N}
    (hw : w ∈ x.D) (hv : v <+: w) : v ∈ x.D := by
  obtain ⟨t, rfl⟩ := hv
  revert hw
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t d ih =>
    intro hw
    apply ih
    have hp := hx.2.2.1 (v ++ (t ++ [d])) hw (by simp)
    simpa [← List.append_assoc] using hp

private theorem aux_no_prefix {x : Config N m} (hx : x.WF) {b w : Word N}
    (hb : b ∉ x.D) (hw : w ∈ x.D) : ¬ b <+: w :=
  fun hp => hb (aux_prefix_mem hx hw hp)

private theorem aux_no_strict_prefix {x : Config N m} (hx : x.WF) {b w : Word N}
    (hb : b ∉ x.D) (hw : w ∈ x.Sl) : ¬ (b <+: w ∧ b ≠ w) := by
  rintro ⟨hp, hn⟩
  exact hb (aux_prefix_mem hx (aux_mem_Sl.mp hw).2 (aux_prefix_parent hp hn))

private theorem aux_card_cellW (a : Word N) : (cellW a).card = N := by
  unfold cellW
  rw [Finset.card_image_of_injective _ (fun d d' hd => by simpa using hd),
    Finset.card_univ, Fintype.card_fin]

private theorem aux_ne_append {p s : Word N} (hs : s ≠ []) : p ≠ p ++ s := by
  intro he
  have hl := congrArg List.length he
  have hsl := List.length_pos_of_ne_nil hs
  simp only [List.length_append] at hl
  omega

private theorem aux_subst_append (a b t : Word N) : subst false a b (a ++ t) = b ++ t := by
  simp [subst]

private theorem aux_subst_append_strict (a b t : Word N) (ht : t ≠ []) :
    subst true a b (a ++ t) = b ++ t := by
  simp [subst, aux_ne_append (p := a) ht]

private theorem aux_subst_self (a b : Word N) : subst true a b a = a := by simp [subst]

private theorem aux_subst_self_false (a b : Word N) : subst false a b a = b := by simp [subst]

private theorem aux_subst_not_prefix {a b w : Word N} (hp : ¬ a <+: w) :
    subst false a b w = w := by
  simp [subst, hp]

private theorem aux_subst_not_prefix_strict {a b w : Word N} (hp : ¬ (a <+: w ∧ a ≠ w)) :
    subst true a b w = w := by
  simp only [subst, Bool.true_eq_false, false_or, if_neg hp]

private theorem aux_subst_agree {a b w : Word N} (hw : a ≠ w) :
    subst true a b w = subst false a b w := by
  simp [subst, hw]

private theorem aux_subst_parent {a b w : Word N} (hw : a ≠ w) :
    (subst false a b w).dropLast = subst false a b w.dropLast := by
  by_cases hp : a <+: w
  · obtain ⟨t, rfl⟩ := hp
    have ht : t ≠ [] := by rintro rfl; simp at hw
    rw [aux_subst_append, List.dropLast_append_of_ne_nil ht,
      List.dropLast_append_of_ne_nil ht, aux_subst_append]
  · have hparent : ¬ a <+: w.dropLast := fun hh => hp (hh.trans w.dropLast_prefix)
    simp [subst, hp, hparent]

private theorem aux_subst_ne_nil {a b w : Word N} (hb : b ≠ []) (hw : w ≠ []) :
    subst false a b w ≠ [] := by
  unfold subst
  split <;> simp_all

/-- The guard and the effect of an applicable `graft`, unpacked once and for all. -/
private theorem aux_graft_spec {x x' : Config N m} {a b : Word N} (h : graft a b x = some x') :
    (a ∈ x.D ∧ a ∈ x.μ ∧ b ∈ x.μ ∧ b ∉ x.D ∧ b ≠ [] ∧ b.dropLast ∈ x.D ∧ ¬ a <+: b ∧
        (∀ w ∈ x.D, a <+: w → b.length + (w.length - a.length) + 1 ≤ m)) ∧
      x'.D = x.D.image (subst false a b) := by
  unfold graft at h
  split at h
  · rename_i hg
    refine ⟨hg, ?_⟩
    cases h
    rfl
  · cases h

/-! ## The moved set -/

/-- The **moved slots** of a graft at `a`: the slots of `x` having `a` as a *proper* prefix.
This is the paper's `Sl(x) ∩ cone(a) \ {a}` — the anchor slot `a` itself stays behind, which is
exactly why the boundary is nonempty. -/
def movedSlots (a : Word N) (x : Config N m) : Finset (Word N) :=
  x.Sl.filter fun u => a <+: u ∧ a ≠ u

/-- The **moved cells**: the deployed cells of `x` lying in `cone(a)`, the moved root cell `a`
included (the paper's moved set at the cell level). -/
def movedCells (a : Word N) (x : Config N m) : Finset (Word N) :=
  x.D.filter fun w => a <+: w

/-- The deployed sibling cells of `a`, i.e. `{pre(a)d ∈ D : pre(a)d ≠ a}`. -/
def sibCells (a : Word N) (x : Config N m) : Finset (Word N) :=
  (cellW a.dropLast).filter fun w => w ∈ x.D ∧ w ≠ a

/-- `σ_x(a)`, the number of deployed sibling cells of `a` (`a` itself excluded). -/
def sigma (a : Word N) (x : Config N m) : ℕ := (sibCells a x).card

theorem mem_movedSlots {x : Config N m} {a u : Word N} :
    u ∈ movedSlots a x ↔ u ∈ x.Sl ∧ a <+: u ∧ a ≠ u := by
  unfold movedSlots
  exact Finset.mem_filter

theorem mem_movedCells {x : Config N m} {a w : Word N} :
    w ∈ movedCells a x ↔ w ∈ x.D ∧ a <+: w := by
  unfold movedCells
  exact Finset.mem_filter

theorem mem_sibCells {x : Config N m} {a w : Word N} :
    w ∈ sibCells a x ↔ (∃ d : Fin N, w = a.dropLast ++ [d]) ∧ w ∈ x.D ∧ w ≠ a := by
  have hc : w ∈ cellW a.dropLast ↔ ∃ d : Fin N, w = a.dropLast ++ [d] := by
    simp only [cellW, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨d, hd⟩ => ⟨d, hd.symm⟩, fun ⟨d, hd⟩ => ⟨d, hd.symm⟩⟩
  unfold sibCells
  rw [Finset.mem_filter, hc]

/-! ## Node level (Lemma lem:edge-cut(i))

The state graph `G(x)` is the two-clause law `AdjW` of `Hsfnlean.Calculus` restricted to the
deployed slots `Sl(x)`; a *crossing edge* is a pair `{u, v}` with `u ∈ movedSlots a x` and
`v ∈ Sl(x) \ movedSlots a x`. -/

/-- If `a` is a prefix of the parent of a nonempty `v`, then `a` is a *proper* prefix of `v`. -/
private theorem aux_strict_of_prefix_dropLast {a v : Word N} (hv : v ≠ [])
    (hp : a <+: v.dropLast) : a <+: v ∧ a ≠ v := by
  refine ⟨hp.trans v.dropLast_prefix, ?_⟩
  rintro rfl
  have h1 := hp.length_le
  have h2 := List.length_pos_of_ne_nil hv
  simp only [List.length_dropLast] at h1
  omega

/-- **Sibling edges never cross** (first half of the paper's prefix computation): if `u` is a moved
slot and `v` is a slot adjacent to it by clause (S) — equal length, equal parent — then `v` is
moved as well. -/
theorem sib_stays_moved {x : Config N m} {a u v : Word N}
    (hu : u ∈ movedSlots a x) (hv : v ∈ x.Sl)
    (hlen : u.length = v.length) (hdl : u.dropLast = v.dropLast) :
    v ∈ movedSlots a x := by
  obtain ⟨huS, hup, hune⟩ := mem_movedSlots.mp hu
  have hvne : v ≠ [] := (aux_mem_Sl.mp hv).1
  have hpar : a <+: v.dropLast := by rw [← hdl]; exact aux_prefix_parent hup hune
  obtain ⟨h1, h2⟩ := aux_strict_of_prefix_dropLast hvne hpar
  exact mem_movedSlots.mpr ⟨hv, h1, h2⟩

/-- **Children of moved slots are moved** (the paper's "conversely if `w` is moved then so is
`wd`"): a slot `v` whose parent is a moved slot `u` is itself moved. -/
theorem child_stays_moved {x : Config N m} {a u v : Word N}
    (hu : u ∈ movedSlots a x) (hv : v ∈ x.Sl) (hne : v ≠ []) (hdl : v.dropLast = u) :
    v ∈ movedSlots a x := by
  obtain ⟨huS, hup, hune⟩ := mem_movedSlots.mp hu
  have hpar : a <+: v.dropLast := by rw [hdl]; exact hup
  obtain ⟨h1, h2⟩ := aux_strict_of_prefix_dropLast hne hpar
  exact mem_movedSlots.mpr ⟨hv, h1, h2⟩

/-- **(a) Only the uplinks into `a` cross.** If `u` is a moved slot, `v` is a slot outside the
moved set and `u` is adjacent to `v` in the state graph, then `v` is the anchor `a` and `u` is one
of the `N` members of the cell `C(a)`. (Instance of the hypotheses: `N = 5`, `m = 3`,
`D = {[], [4], [4,2], [4,4]}`, `a = [4,2]`, `u = [4,2,0]`, `v = [4,2]`.) -/
theorem crossing_forces_uplink {x : Config N m} {a u v : Word N}
    (hx : x.WF) (ha : a ∈ x.D)
    (hu : u ∈ movedSlots a x) (hv : v ∈ x.Sl \ movedSlots a x)
    (huv : AdjW u v) : v = a ∧ u ∈ cellW a := by
  obtain ⟨hvS, hvnm⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨huS, hup, hune⟩ := mem_movedSlots.mp hu
  obtain ⟨hne, hcase⟩ := huv
  rcases hcase with ⟨hlen, hdl⟩ | ⟨hlen, hdl⟩ | ⟨hlen, hdl⟩
  · exact absurd (sib_stays_moved hu hvS hlen hdl) hvnm
  · have hvne : v ≠ [] := by
      intro he; rw [he] at hlen; simp at hlen
    exact absurd (child_stays_moved hu hvS hvne hdl) hvnm
  · have hune' : u ≠ [] := by
      intro he; rw [he] at hlen; simp at hlen
    have hpar : a <+: v := by rw [← hdl]; exact aux_prefix_parent hup hune
    have hva : a = v := by
      by_contra hc
      exact hvnm (mem_movedSlots.mpr ⟨hvS, hpar, hc⟩)
    exact ⟨hva.symm, aux_mem_cellW.mpr ⟨hune', by rw [hdl]; exact hva.symm⟩⟩

/-- **(b), first half.** Every member of the cell `C(a)` is a moved slot. -/
theorem cellW_subset_movedSlots {x : Config N m} {a : Word N} (ha : a ∈ x.D) :
    cellW a ⊆ movedSlots a x := by
  intro u hu
  obtain ⟨hune, hdl⟩ := aux_mem_cellW.mp hu
  refine mem_movedSlots.mpr ⟨aux_mem_Sl.mpr ⟨hune, by rw [hdl]; exact ha⟩, ?_, ?_⟩
  · rw [← hdl]; exact u.dropLast_prefix
  · exact fun he => aux_dropLast_ne hune (hdl.trans he)

/-- Every member of `C(a)` is adjacent to the anchor `a` by clause (P). -/
private theorem aux_adjW_uplink {a u : Word N} (hu : u ∈ cellW a) : AdjW u a := by
  obtain ⟨hune, hdl⟩ := aux_mem_cellW.mp hu
  refine ⟨fun he => aux_dropLast_ne hune (hdl.trans he.symm), Or.inr (Or.inr ⟨?_, hdl⟩)⟩
  have h2 := List.length_pos_of_ne_nil hune
  have h3 : a.length = u.length - 1 := by rw [← hdl]; simp
  omega

/-- **(b), second half.** All `N` members of `C(a)` are adjacent to the anchor `a`: the uplinks
`{ad, a}` are exactly `N` edges. -/
theorem card_uplinks_into_anchor (a : Word N) :
    ((cellW a).filter fun u => AdjW u a).card = N := by
  rw [Finset.filter_true_of_mem fun u hu => aux_adjW_uplink hu, aux_card_cellW]

/-- The crossing edges of the state graph, recorded as ordered pairs
`(moved endpoint, static endpoint)`. -/
def boundaryPairs (a : Word N) (x : Config N m) : Finset (Word N × Word N) :=
  ((movedSlots a x) ×ˢ (x.Sl \ movedSlots a x)).filter fun p => AdjW p.1 p.2

/-- **Lemma lem:edge-cut(i), source side, as a set identity**: the boundary of the moved set is
exactly the `N` uplinks from `C(a)` into the anchor `a`. -/
theorem boundaryPairs_eq {x : Config N m} {a : Word N}
    (hx : x.WF) (ha : a ∈ x.D) (hane : a ≠ []) :
    boundaryPairs a x = (cellW a).image fun u => (u, a) := by
  have haSl : a ∈ x.Sl := aux_mem_Sl.mpr ⟨hane, hx.2.2.1 a ha hane⟩
  have hanm : a ∉ movedSlots a x := fun hm => (mem_movedSlots.mp hm).2.2 rfl
  ext p
  obtain ⟨u, v⟩ := p
  simp only [boundaryPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_image,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hu, hv⟩, hadj⟩
    obtain ⟨hva, hcell⟩ := crossing_forces_uplink hx ha hu hv hadj
    exact ⟨u, hcell, rfl, hva.symm⟩
  · rintro ⟨w, hw, rfl, rfl⟩
    exact ⟨⟨cellW_subset_movedSlots ha hw, Finset.mem_sdiff.mpr ⟨haSl, hanm⟩⟩,
      aux_adjW_uplink hw⟩

/-- **Lemma lem:edge-cut(i), source side, as a count**: exactly `N` edges join the moved slots to
the rest. -/
theorem card_boundaryPairs {x : Config N m} {a : Word N}
    (hx : x.WF) (ha : a ∈ x.D) (hane : a ≠ []) :
    (boundaryPairs a x).card = N := by
  rw [boundaryPairs_eq hx ha hane,
    Finset.card_image_of_injective _ (fun s t hst => by simpa using hst), aux_card_cellW]

/-- The slot set is transported by the strict prefix substitution. -/
private theorem aux_Sl_graft {x x' : Config N m} {a b : Word N} (hx : x.WF)
    (h : graft a b x = some x') : x'.Sl = x.Sl.image (subst true a b) := by
  obtain ⟨⟨ha, ham, hbm, hbd, hbn, hbp, hab, hfit⟩, hD⟩ := aux_graft_spec h
  have han : a ≠ [] := by rintro rfl; simp at hab
  ext u
  constructor
  · intro hu
    obtain ⟨hune, hdl⟩ := aux_mem_Sl.mp hu
    rw [hD, Finset.mem_image] at hdl
    obtain ⟨v, hv, hfv⟩ := hdl
    by_cases hp : a <+: v
    · obtain ⟨s, rfl⟩ := hp
      rw [aux_subst_append] at hfv
      have hsd : s ++ [u.getLast hune] ≠ [] := by simp
      refine Finset.mem_image.mpr ⟨a ++ (s ++ [u.getLast hune]), aux_mem_Sl.mpr ⟨by simp, ?_⟩, ?_⟩
      · rw [List.dropLast_append_of_ne_nil hsd, (by simp : (s ++ [u.getLast hune]).dropLast = s)]
        exact hv
      · rw [aux_subst_append_strict _ _ _ hsd, ← List.append_assoc, hfv]
        exact List.dropLast_append_getLast hune
    · rw [aux_subst_not_prefix hp] at hfv
      refine Finset.mem_image.mpr ⟨u, aux_mem_Sl.mpr ⟨hune, by rw [← hfv]; exact hv⟩, ?_⟩
      apply aux_subst_not_prefix_strict
      rintro ⟨hpu, hnu⟩
      exact hp (by rw [hfv]; exact aux_prefix_parent hpu hnu)
  · intro hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hvne, hvd⟩ := aux_mem_Sl.mp hv
    by_cases he : a = v
    · subst he
      rw [aux_subst_self]
      refine aux_mem_Sl.mpr ⟨hvne, ?_⟩
      rw [hD]
      exact Finset.mem_image.mpr
        ⟨a.dropLast, hvd, aux_subst_not_prefix (aux_parent_not_below hvne)⟩
    · rw [aux_subst_agree he]
      refine aux_mem_Sl.mpr ⟨aux_subst_ne_nil hbn hvne, ?_⟩
      rw [aux_subst_parent he, hD]
      exact Finset.mem_image.mpr ⟨v.dropLast, hvd, rfl⟩

/-- The moved slots of `x'` are the images of the moved slots of `x` under the strict prefix
substitution `a ↦ b` (the paper's "their images in `cone(b)`"). -/
theorem movedSlots_graft {x x' : Config N m} {a b : Word N}
    (hx : x.WF) (h : graft a b x = some x') :
    movedSlots b x' = (movedSlots a x).image (subst true a b) := by
  obtain ⟨⟨ha, ham, hbm, hbd, hbn, hbp, hab, hfit⟩, hD⟩ := aux_graft_spec h
  unfold movedSlots
  rw [aux_Sl_graft hx h, Finset.filter_image]
  refine congrArg (Finset.image (subst true a b)) (Finset.filter_congr ?_)
  intro v hv
  constructor
  · intro hbv
    by_contra hc
    rw [aux_subst_not_prefix_strict hc] at hbv
    exact aux_no_strict_prefix hx hbd hv hbv
  · rintro ⟨hpv, hnv⟩
    obtain ⟨s, rfl⟩ := hpv
    have hs : s ≠ [] := by rintro rfl; simp at hnv
    rw [aux_subst_append_strict _ _ _ hs]
    exact ⟨List.prefix_append _ _, aux_ne_append hs⟩

/-- The anchor `b` is a deployed cell of the result. -/
private theorem aux_b_mem_graft {x x' : Config N m} {a b : Word N}
    (h : graft a b x = some x') : b ∈ x'.D := by
  obtain ⟨⟨ha, ham, hbm, hbd, hbn, hbp, hab, hfit⟩, hD⟩ := aux_graft_spec h
  rw [hD]
  exact Finset.mem_image.mpr ⟨a, ha, aux_subst_self_false a b⟩

/-- **Lemma lem:edge-cut(i), target side**: in `G(x')` the created boundary is likewise the `N`
uplinks into `b`. -/
theorem boundaryPairs_graft_eq {x x' : Config N m} {a b : Word N}
    (hx : x.WF) (hab : a.length = b.length) (h : graft a b x = some x') :
    boundaryPairs b x' = (cellW b).image fun u => (u, b) :=
  boundaryPairs_eq (wf_graft hx h) (aux_b_mem_graft h) (aux_graft_spec h).1.2.2.2.2.1

/-- **Lemma lem:edge-cut(i), target side, as a count**: the created boundary has exactly `N`
edges. -/
theorem card_boundaryPairs_graft {x x' : Config N m} {a b : Word N}
    (hx : x.WF) (hab : a.length = b.length) (h : graft a b x = some x') :
    (boundaryPairs b x').card = N :=
  card_boundaryPairs (wf_graft hx h) (aux_b_mem_graft h) (aux_graft_spec h).1.2.2.2.2.1

/-! ## Cell level (Lemma lem:edge-cut(ii))

The deployed-cell graph `Γ(x)` has vertex set `D` (the seed cell `[]` is a vertex, the base case
that keeps the boundary law uniform), a *parent edge* between `w ≠ []` and `pre(w)`, and a
*sibling edge* between deployed sibling cells `wd, wd'`. -/

/-- Adjacency of the deployed-cell graph `Γ(x)`: both endpoints deployed and distinct, joined by a
parent edge or by a sibling edge. (Note that `u.dropLast = v.dropLast` with `u, v` nonempty already
forces `u.length = v.length`, so the third clause is siblinghood.) -/
def AdjCell (x : Config N m) (u v : Word N) : Prop :=
  u ∈ x.D ∧ v ∈ x.D ∧ u ≠ v ∧
    ((u ≠ [] ∧ u.dropLast = v) ∨ (v ≠ [] ∧ v.dropLast = u) ∨
      (u ≠ [] ∧ v ≠ [] ∧ u.dropLast = v.dropLast))

instance decidableAdjCell (x : Config N m) : ∀ u v : Word N, Decidable (AdjCell x u v) :=
  fun u v => by unfold AdjCell; infer_instance

/-- The edges of `Γ(x)` cut by the graft, as ordered pairs `(moved cell, static cell)`. -/
def cellCutPairs (a : Word N) (x : Config N m) : Finset (Word N × Word N) :=
  ((movedCells a x) ×ˢ (x.D \ movedCells a x)).filter fun p => AdjCell x p.1 p.2

/-- A deployed sibling cell of `a` other than `a` is not in the cone of `a`. -/
private theorem aux_sib_not_moved {a w : Word N} (hane : a ≠ [])
    (hw : ∃ d : Fin N, w = a.dropLast ++ [d]) (hwa : w ≠ a) : ¬ a <+: w := by
  intro hp
  rcases eq_or_ne a w with he | hne
  · exact hwa he.symm
  · obtain ⟨d, rfl⟩ := hw
    exact aux_parent_not_below hane (by simpa using aux_prefix_parent hp hne)

/-- **Lemma lem:edge-cut(ii), source side, as a set identity**: the cut edges are all incident to
the moved root cell `a`, namely the parent edge `{a, pre(a)}` together with the `σ_x(a)` sibling
edges at `a`. For `|a| = 1` the parent edge is the edge to the seed cell `[]`. -/
theorem cellCutPairs_eq {x : Config N m} {a : Word N}
    (hx : x.WF) (ha : a ∈ x.D) (hane : a ≠ []) :
    cellCutPairs a x = ({a} : Finset (Word N)) ×ˢ insert a.dropLast (sibCells a x) := by
  have hpar : a.dropLast ∈ x.D := hx.2.2.1 a ha hane
  ext p
  obtain ⟨u, v⟩ := p
  simp only [cellCutPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_insert, mem_movedCells, mem_sibCells, not_and]
  constructor
  · rintro ⟨⟨⟨huD, hup⟩, hvD, hvnm⟩, hadj⟩
    have hnv : ¬ a <+: v := hvnm hvD
    obtain ⟨-, -, hne, hcl⟩ := hadj
    rcases hcl with ⟨hun, hdl⟩ | ⟨hvn, hdl⟩ | ⟨hun, hvn, hdl⟩
    · have hau : a = u := by
        by_contra hc
        exact hnv (hdl ▸ aux_prefix_parent hup hc)
      exact ⟨hau.symm, Or.inl (by rw [hau]; exact hdl.symm)⟩
    · exact absurd (((by rw [hdl]; exact hup : a <+: v.dropLast)).trans v.dropLast_prefix) hnv
    · have hau : a = u := by
        by_contra hc
        exact hnv ((hdl ▸ aux_prefix_parent hup hc).trans v.dropLast_prefix)
      refine ⟨hau.symm, Or.inr ⟨⟨v.getLast hvn, ?_⟩, hvD, ?_⟩⟩
      · rw [hau, hdl]
        exact (List.dropLast_append_getLast hvn).symm
      · exact fun hva => hne (hau.symm.trans hva.symm)
  · rintro ⟨rfl, hcase⟩
    rcases hcase with rfl | ⟨⟨d, rfl⟩, hvD, hvne⟩
    · exact ⟨⟨⟨ha, List.prefix_refl _⟩, hpar, fun _ hp => aux_parent_not_below hane hp⟩,
        ha, hpar, Ne.symm (aux_dropLast_ne hane), Or.inl ⟨hane, rfl⟩⟩
    · refine ⟨⟨⟨ha, List.prefix_refl _⟩, hvD, ?_⟩,
        ha, hvD, Ne.symm hvne, Or.inr (Or.inr ⟨hane, by simp, by simp⟩)⟩
      exact fun _ hp => aux_sib_not_moved hane ⟨d, rfl⟩ hvne hp

/-- **Lemma lem:edge-cut(ii), source side, as a count**: the graft cuts exactly `1 + σ_x(a)` edges
of the deployed-cell graph. -/
theorem card_cellCutPairs {x : Config N m} {a : Word N}
    (hx : x.WF) (ha : a ∈ x.D) (hane : a ≠ []) :
    (cellCutPairs a x).card = 1 + sigma a x := by
  have hnm : a.dropLast ∉ sibCells a x := by
    intro hmem
    obtain ⟨⟨d, hd⟩, -, -⟩ := mem_sibCells.mp hmem
    have hl := congrArg List.length hd
    simp at hl
  rw [cellCutPairs_eq hx ha hane, Finset.card_product, Finset.card_singleton, one_mul,
    Finset.card_insert_of_notMem hnm, sigma, Nat.add_comm]

/-- **Lemma lem:edge-cut(ii), target side, as a set identity**: the created edges are all incident
to the arrived root cell `b`, namely the parent edge `{b, pre(b)}` together with the `σ_{x'}(b)`
sibling edges at `b`. -/
theorem cellCutPairs_graft_eq {x x' : Config N m} {a b : Word N}
    (hx : x.WF) (hab : a.length = b.length) (h : graft a b x = some x') :
    cellCutPairs b x' = ({b} : Finset (Word N)) ×ˢ insert b.dropLast (sibCells b x') :=
  cellCutPairs_eq (wf_graft hx h) (aux_b_mem_graft h) (aux_graft_spec h).1.2.2.2.2.1

/-- **Lemma lem:edge-cut(ii), target side**: the graft creates exactly `1 + σ_{x'}(b)` edges, all
incident to `b`. -/
theorem card_cellCutPairs_graft {x x' : Config N m} {a b : Word N}
    (hx : x.WF) (hab : a.length = b.length) (h : graft a b x = some x') :
    (cellCutPairs b x').card = 1 + sigma b x' :=
  card_cellCutPairs (wf_graft hx h) (aux_b_mem_graft h) (aux_graft_spec h).1.2.2.2.2.1

/-- **The outside vertices are the same set.** The cells outside the moved set of `x` are exactly
the cells outside the moved set of `x'` (the paper's "`D ∖ D_a` is unchanged"). Without this,
`adjCell_outside_graft` below would be a statement about two different vertex sets. -/
theorem cellsOutside_graft {x x' : Config N m} {a b : Word N}
    (hx : x.WF) (h : graft a b x = some x') :
    x'.D \ movedCells b x' = x.D \ movedCells a x := by
  obtain ⟨⟨ha, ham, hbm, hbd, hbn, hbp, hab, hfit⟩, hD⟩ := aux_graft_spec h
  ext w
  simp only [Finset.mem_sdiff, mem_movedCells, not_and]
  constructor
  · rintro ⟨hw, hnw⟩
    have hnb : ¬ b <+: w := fun hb => hnw hw hb
    rw [hD, Finset.mem_image] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hp : ¬ a <+: v := by
      intro hp
      obtain ⟨s, rfl⟩ := hp
      rw [aux_subst_append] at hnb
      exact hnb (List.prefix_append _ _)
    rw [aux_subst_not_prefix hp]
    exact ⟨hv, fun _ => hp⟩
  · rintro ⟨hw, hnw⟩
    have hna : ¬ a <+: w := fun hb => hnw hw hb
    refine ⟨?_, fun _ hb => aux_no_prefix hx hbd hw hb⟩
    rw [hD]
    exact Finset.mem_image.mpr ⟨w, hw, aux_subst_not_prefix hna⟩

/-- **Lemma lem:edge-cut(ii), outside edges are untouched**: an edge of `Γ` with both endpoints
outside the moved set — by `cellsOutside_graft` one and the same set before and after — is present
in `Γ(x)` iff it is present in `Γ(x')`. -/
theorem adjCell_outside_graft {x x' : Config N m} {a b u v : Word N}
    (hx : x.WF) (h : graft a b x = some x')
    (hu : u ∈ x.D \ movedCells a x) (hv : v ∈ x.D \ movedCells a x) :
    AdjCell x u v ↔ AdjCell x' u v := by
  obtain ⟨⟨ha, ham, hbm, hbd, hbn, hbp, hab, hfit⟩, hD⟩ := aux_graft_spec h
  have key : ∀ w : Word N, w ∈ x.D \ movedCells a x → w ∈ x.D ∧ w ∈ x'.D := by
    intro w hw
    rw [Finset.mem_sdiff, mem_movedCells] at hw
    have hna : ¬ a <+: w := fun hp => hw.2 ⟨hw.1, hp⟩
    refine ⟨hw.1, ?_⟩
    rw [hD]
    exact Finset.mem_image.mpr ⟨w, hw.1, aux_subst_not_prefix hna⟩
  obtain ⟨hu1, hu2⟩ := key u hu
  obtain ⟨hv1, hv2⟩ := key v hv
  unfold AdjCell
  constructor
  · rintro ⟨-, -, hrest⟩
    exact ⟨hu2, hv2, hrest⟩
  · rintro ⟨-, -, hrest⟩
    exact ⟨hu1, hv1, hrest⟩

/-- Parenthood below a fixed nonempty prefix reads on the suffix alone. -/
private theorem aux_dl_eq {p s t : Word N} (hp : p ≠ []) :
    (p ++ s).dropLast = p ++ t ↔ (s ≠ [] ∧ s.dropLast = t) := by
  by_cases hs : s = []
  · subst hs
    rw [List.append_nil]
    constructor
    · intro he
      exfalso
      have hl := congrArg List.length he
      have hpl := List.length_pos_of_ne_nil hp
      simp only [List.length_dropLast, List.length_append] at hl
      omega
    · rintro ⟨hne, -⟩
      exact absurd rfl hne
  · rw [List.dropLast_append_of_ne_nil hs]
    simp [hs]

/-- Siblinghood below a fixed nonempty prefix reads on the suffix alone. -/
private theorem aux_dl_eq_dl {p s t : Word N} (hp : p ≠ []) :
    (p ++ s).dropLast = (p ++ t).dropLast ↔
      ((s = [] ∧ t = []) ∨ (s ≠ [] ∧ t ≠ [] ∧ s.dropLast = t.dropLast)) := by
  by_cases hs : s = [] <;> by_cases ht : t = []
  · subst hs; subst ht; simp
  · subst hs
    rw [List.append_nil, List.dropLast_append_of_ne_nil ht]
    constructor
    · intro he
      exfalso
      have hl := congrArg List.length he
      have hpl := List.length_pos_of_ne_nil hp
      have htl := List.length_pos_of_ne_nil ht
      simp only [List.length_dropLast, List.length_append] at hl
      omega
    · rintro (⟨-, h1⟩ | ⟨h1, -, -⟩)
      · exact absurd h1 ht
      · exact absurd rfl h1
  · subst ht
    rw [List.append_nil, List.dropLast_append_of_ne_nil hs]
    constructor
    · intro he
      exfalso
      have hl := congrArg List.length he
      have hpl := List.length_pos_of_ne_nil hp
      have hsl := List.length_pos_of_ne_nil hs
      simp only [List.length_dropLast, List.length_append] at hl
      omega
    · rintro (⟨h1, -⟩ | ⟨-, h1, -⟩)
      · exact absurd h1 hs
      · exact absurd rfl h1
  · rw [List.dropLast_append_of_ne_nil hs, List.dropLast_append_of_ne_nil ht]
    simp [hs, ht]

/-- The structural half of `AdjCell` below a nonempty prefix depends only on the suffixes: this is
suffix covariance at the cell level, the companion of `Calc.adjW_append_iff`. -/
private theorem aux_adj_core {p q s t : Word N} (hp : p ≠ []) (hq : q ≠ []) :
    (p ++ s ≠ p ++ t ∧ ((p ++ s ≠ [] ∧ (p ++ s).dropLast = p ++ t) ∨
        (p ++ t ≠ [] ∧ (p ++ t).dropLast = p ++ s) ∨
        (p ++ s ≠ [] ∧ p ++ t ≠ [] ∧ (p ++ s).dropLast = (p ++ t).dropLast))) ↔
      (q ++ s ≠ q ++ t ∧ ((q ++ s ≠ [] ∧ (q ++ s).dropLast = q ++ t) ∨
        (q ++ t ≠ [] ∧ (q ++ t).dropLast = q ++ s) ∨
        (q ++ s ≠ [] ∧ q ++ t ≠ [] ∧ (q ++ s).dropLast = (q ++ t).dropLast))) := by
  rw [aux_dl_eq hp, aux_dl_eq hp, aux_dl_eq_dl hp, aux_dl_eq hq, aux_dl_eq hq, aux_dl_eq_dl hq]
  simp [hp, hq]

/-- **Lemma lem:edge-cut(ii), internal edges map bijectively**: on the moved cells the prefix
substitution preserves both the parent relation and siblinghood. -/
theorem adjCell_moved_graft {x x' : Config N m} {a b u v : Word N}
    (hx : x.WF) (h : graft a b x = some x')
    (hu : u ∈ movedCells a x) (hv : v ∈ movedCells a x) :
    AdjCell x u v ↔ AdjCell x' (subst false a b u) (subst false a b v) := by
  obtain ⟨⟨ha, ham, hbm, hbd, hbn, hbp, hab, hfit⟩, hD⟩ := aux_graft_spec h
  have han : a ≠ [] := by rintro rfl; simp at hab
  obtain ⟨hu1, hu2⟩ := mem_movedCells.mp hu
  obtain ⟨hv1, hv2⟩ := mem_movedCells.mp hv
  have hu' : subst false a b u ∈ x'.D := by
    rw [hD]; exact Finset.mem_image.mpr ⟨u, hu1, rfl⟩
  have hv' : subst false a b v ∈ x'.D := by
    rw [hD]; exact Finset.mem_image.mpr ⟨v, hv1, rfl⟩
  obtain ⟨s, rfl⟩ := hu2
  obtain ⟨t, rfl⟩ := hv2
  rw [aux_subst_append] at hu' hv'
  simp only [AdjCell, aux_subst_append]
  constructor
  · rintro ⟨-, -, hrest⟩
    exact ⟨hu', hv', (aux_adj_core han hbn).mp hrest⟩
  · rintro ⟨-, -, hrest⟩
    exact ⟨hu1, hv1, (aux_adj_core hbn han).mp hrest⟩

/-- The moved cells of `x'` are the images of the moved cells of `x`; together with
`adjCell_moved_graft` this is the bijection of the internal edges. -/
theorem movedCells_graft {x x' : Config N m} {a b : Word N}
    (hx : x.WF) (h : graft a b x = some x') :
    movedCells b x' = (movedCells a x).image (subst false a b) := by
  obtain ⟨⟨ha, ham, hbm, hbd, hbn, hbp, hab, hfit⟩, hD⟩ := aux_graft_spec h
  unfold movedCells
  rw [hD, Finset.filter_image]
  refine congrArg (Finset.image (subst false a b)) (Finset.filter_congr ?_)
  intro v hv
  constructor
  · intro hbv
    by_contra hc
    rw [aux_subst_not_prefix hc] at hbv
    exact aux_no_prefix hx hbd hv hbv
  · rintro ⟨s, rfl⟩
    rw [aux_subst_append]
    exact List.prefix_append _ _

/-! ## The transported sets are transported *bijectively*

`movedSlots_graft` and `movedCells_graft` above say the images fill the moved sets of `x'`;
the two injectivity lemmas here say nothing is folded together on the way, which is what turns
"maps the internal edges bijectively" of Lemma lem:edge-cut(ii) into an actual bijection. -/

/-- The prefix substitution is injective on the moved cells: `a s ↦ b s` cancels the new prefix. -/
theorem substFalse_inj_on_movedCells {x : Config N m} {a b u v : Word N}
    (hu : u ∈ movedCells a x) (hv : v ∈ movedCells a x)
    (he : subst false a b u = subst false a b v) : u = v := by
  obtain ⟨-, s, rfl⟩ := mem_movedCells.mp hu
  obtain ⟨-, t, rfl⟩ := mem_movedCells.mp hv
  rw [aux_subst_append, aux_subst_append] at he
  simpa using he

/-- The strict prefix substitution is injective on the moved slots. -/
theorem substTrue_inj_on_movedSlots {x : Config N m} {a b u v : Word N}
    (hu : u ∈ movedSlots a x) (hv : v ∈ movedSlots a x)
    (he : subst true a b u = subst true a b v) : u = v := by
  obtain ⟨-, ⟨s, rfl⟩, hune⟩ := mem_movedSlots.mp hu
  obtain ⟨-, ⟨t, rfl⟩, hvne⟩ := mem_movedSlots.mp hv
  have hs : s ≠ [] := by rintro rfl; simp at hune
  have ht : t ≠ [] := by rintro rfl; simp at hvne
  rw [aux_subst_append_strict _ _ _ hs, aux_subst_append_strict _ _ _ ht] at he
  simpa using he

/-- **The moved cells are in bijection with their images**, so the internal-edge correspondence of
`adjCell_moved_graft` is a bijection and the two cell counts agree. -/
theorem card_movedCells_graft {x x' : Config N m} {a b : Word N}
    (hx : x.WF) (h : graft a b x = some x') :
    (movedCells b x').card = (movedCells a x).card := by
  rw [movedCells_graft hx h]
  exact Finset.card_image_of_injOn fun u hu v hv he =>
    substFalse_inj_on_movedCells hu hv he

/-- **The moved slots are in bijection with their images** (Lemma lem:edge-cut(i), the moved set
and "their images in `cone(b)`" have the same size). -/
theorem card_movedSlots_graft {x x' : Config N m} {a b : Word N}
    (hx : x.WF) (h : graft a b x = some x') :
    (movedSlots b x').card = (movedSlots a x).card := by
  rw [movedSlots_graft hx h]
  exact Finset.card_image_of_injOn fun u hu v hv he =>
    substTrue_inj_on_movedSlots hu hv he

end Calc

end HSFN
