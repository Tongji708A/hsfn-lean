/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Calculus

/-!
# Graft is a prefix substitution and an isomorphism
(Theorem thm:graft-iso, items (i) and (ii))

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

`graft a b` moves the deployed cell tree rooted at the slot `a` to the vacant slot `b`
(Table tab:typing, Definition def:calc-state). This file states, on top of
`Hsfnlean.Calculus`, the two structural laws of that generator.

* **(i) Prefix substitution, zero renumbering.** The moved slots are re-addressed by
  `a ++ w ↦ b ++ w` for `w ≠ []`; the suffix `w` is untouched, so no digit below the
  substituted prefix changes (`subst_append_of_ne_nil`, `subst_drop_eq`). The designated
  duplicates travel with their cells: the marked set `M(x) = {w0 : w ∈ D \ {ε}}` of
  Definition def:calc-state (Lemma lem:dup-digit) satisfies
  `M(x') ∩ cone(b) = (a w ↦ b w) '' (M(x) ∩ cone(a))` on the strict cones
  (`graft_markedSet_cone`), because being marked is a property of the last digit alone
  (`isMarkW_append_iff`). Occupancy and decommission bits are transported verbatim
  (`graft_mem_mu_iff_moved`, `graft_mem_zeta_iff_moved`), are unchanged off the moved
  cone (`graft_mem_mu_iff_static`, `graft_mem_zeta_iff_static`), and the anchor `a` keeps
  its own bits (`graft_anchor_stays`, `graft_anchor_not_zeta`), which is the remaining
  case `s = a` of the trichotomy "strictly below `a` / equal to `a` / not below `a`".
* **(ii) Isomorphism on the moved set.** `subst true a b` is a bijection from the moved
  slots of `x` onto the moved slots of `x'` (`graft_bijOn_movedSlots`) which preserves and
  reflects the two-clause adjacency law of Theorem thm:adjacency-II
  (`graft_adjW_preserve`, `graft_adjW_reflect`, `graft_adjW_iff`), packaged as an
  adjacency-preserving equivalence in `graft_iso`. The mathematical content is the suffix
  covariance `Calc.adjW_append_iff` already proved in `Hsfnlean.Calculus`.

## Modelling choices

* The "moved slots" of the paper are the members of the deployed cells inside `cone(a)`.
  Since `D` is prefix-closed this is exactly `{s ∈ Sl(x) : a <+: s ∧ s ≠ a}`, the slots
  strictly below `a`; the slot `a` itself is a member of the static cell `C(pre a)` and
  stays behind (`subst_self_true`), matching the reading note on Table tab:typing.
* `movedSlotSet` and `markedSet` are `Set (Word N)` rather than `Finset (Word N)`, purely to
  avoid decidability side conditions; they are subsets of the finite `Sl(x)`.
* Adjacency is the word-level law `Calc.AdjW` (equal to the graph of `Hsfnlean.Basic` on
  addresses by `Calc.adjW_iff_adj`). The state graph `G(x)` of the paper is `AdjW`
  restricted to `Sl(x)`; the isomorphism is stated as a bijection of the two moved slot
  sets together with the adjacency equivalence, which is what "isomorphism of the induced
  subgraphs" unfolds to. `graft_iso` is not vacuous: `movedSlots_nonempty` shows the
  moved set of an applicable graft is nonempty, so the equivalence it exhibits is not the
  empty one, and `graft_hypotheses_satisfiable` exhibits a well-formed configuration on
  which a graft really is applicable, so the hypothesis `graft a b x = some x'` carried by
  every transport law of this file is itself satisfiable.
* `isMarkW` carries the lower tier bound `2 ≤ |s|` of the marking `M = {a0 : 1 ≤ |a|}` of
  Lemma lem:dup-digit but not its upper bound `|a| ≤ m-1`; on a configuration the upper
  bound is the depth clause of `Config.WF`, so `markedSet x` obeys it automatically.

## Where the paper is corrected

The displayed identity of Theorem thm:graft-iso(i), `M(x') ∩ cone(b) = {bw : aw ∈ M(x)}`,
is false as literally written, because `cone(a)` and `cone(b)` in the sense of
Section~sec:calculus contain their own apexes (`cone(a) = {aw : w ∈ Σ_N^*}`) while the
apexes do not move: the guards force `pre(b) ∈ D`, so `b` itself lies in `M(x')` whenever
`|b| ≥ 2` and `b` ends in the digit `0`, and this is independent of whether `a` lies in
`M(x)`; `a` meanwhile stays behind in the static cell `C(pre a)`. The intended range is
the one the same item states one clause earlier, `w ∈ Σ_N^+`. `graft_markedSet_cone` is
therefore stated on the strict cones `{u | b <+: u ∧ u ≠ b}` and `{u | a <+: u ∧ u ≠ a}`,
where it is true. The same reading of "moved" is used throughout (`movedSlotSet`), and it is
the reading that matches both `graft` in `Hsfnlean.Calculus` (`μ` and `ζ` move by
`subst true`, which fixes `a`) and the second reading note on Table tab:typing.

## Not formalized here

* Item (iii) of Theorem thm:graft-iso (indicator invariance at equal tier, the two-bin
  histogram transfer) and everything in Proposition prop:kpi-affine.
* Lemma lem:edge-cut (the boundary edge-cut counts `N` and `1 + σ`), the deployed-cell
  graph `Γ(x)`, and Remark rem:graft-splice.
* The `permute` generator, the derived operations, and the dense variant.
* No `SimpleGraph` object on `Word N` is built; adjacency is used through `AdjW`.

The statements are frozen; all of them are proved below (no `sorry`, no new axiom). The
private `aux_*` lemmas re-derive, for use here, the word combinatorics that
`Hsfnlean.Calculus` keeps private to its own file.
-/

namespace HSFN

namespace Calc

open Config

-- The frozen statements deliberately carry hypotheses that some proofs do not need:
-- `[NeZero N]` is part of every statement in the marking section and is inherited by the
-- transport lemmas, and `hx`/`h` are kept on `movedSlots_nonempty`, `graft_anchor_stays`
-- and `graft_injOn_movedSlots` because the paper speaks of an applicable graft throughout.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {N m : ℕ} {x x' : Config N m} {a b s t w : Word N}

/-! ### Private word and configuration combinatorics

These mirror the `private` helpers of `Hsfnlean.Calculus`, which are not visible outside
that file. -/

private theorem aux_mem_cellW' {v w : Word N} :
    v ∈ cellW w ↔ v ≠ [] ∧ v.dropLast = w := by
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨d, _, rfl⟩
    simp
  · rintro ⟨hv, rfl⟩
    exact Finset.mem_image.mpr
      ⟨v.getLast hv, Finset.mem_univ _, List.dropLast_append_getLast hv⟩

private theorem aux_mem_Sl' {x : Config N m} {w : Word N} :
    w ∈ x.Sl ↔ w ≠ [] ∧ w.dropLast ∈ x.D := by
  simp only [Sl, Finset.mem_biUnion, aux_mem_cellW']
  aesop

private theorem aux_append_ne (b t : Word N) (ht : t ≠ []) : b ++ t ≠ b := by
  intro he
  have h1 := congrArg List.length he
  have h2 := List.length_pos_of_ne_nil ht
  simp only [List.length_append] at h1
  omega

private theorem aux_subst_app (a b t : Word N) : subst false a b (a ++ t) = b ++ t := by
  simp [subst]

private theorem aux_subst_app_strict (a b t : Word N) (ht : t ≠ []) :
    subst true a b (a ++ t) = b ++ t := by
  have hn : a ≠ a ++ t := (aux_append_ne a t ht).symm
  simp [subst, hn]

private theorem aux_subst_id {strict : Bool} {a b w : Word N} (hp : ¬ a <+: w) :
    subst strict a b w = w := by
  simp [subst, hp]

private theorem aux_subst_id_strict {a b w : Word N} (h : ¬ (a <+: w ∧ a ≠ w)) :
    subst true a b w = w := by
  simp only [subst, Bool.true_eq_false, false_or, if_neg h]

private theorem aux_subst_inv {a b w : Word N} (hw : ¬ b <+: w) :
    subst false b a (subst false a b w) = w := by
  by_cases hp : a <+: w
  · obtain ⟨t, rfl⟩ := hp
    rw [aux_subst_app, aux_subst_app]
  · simp [subst, hp, hw]

private theorem aux_subst_inv_strict {a b w : Word N} (hw : ¬ (b <+: w ∧ b ≠ w)) :
    subst true b a (subst true a b w) = w := by
  by_cases hp : a <+: w ∧ a ≠ w
  · obtain ⟨hp, hn⟩ := hp
    obtain ⟨t, rfl⟩ := hp
    have ht : t ≠ [] := by rintro rfl; simp at hn
    rw [aux_subst_app_strict _ _ _ ht, aux_subst_app_strict _ _ _ ht]
  · rw [aux_subst_id_strict hp, aux_subst_id_strict hw]

private theorem aux_prefix_mem' {x : Config N m} (hx : x.WF) {v w : Word N}
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

private theorem aux_prefix_parent' {a w : Word N} (hp : a <+: w) (hne : a ≠ w) :
    a <+: w.dropLast := by
  obtain ⟨t, rfl⟩ := hp
  have ht : t ≠ [] := by rintro rfl; simp at hne
  rw [List.dropLast_append_of_ne_nil ht]
  exact List.prefix_append _ _

private theorem aux_no_prefix' {x : Config N m} (hx : x.WF) {b w : Word N}
    (hb : b ∉ x.D) (hw : w ∈ x.D) : ¬ b <+: w :=
  fun hp => hb (aux_prefix_mem' hx hw hp)

private theorem aux_no_strict_prefix' {x : Config N m} (hx : x.WF) {b w : Word N}
    (hb : b ∉ x.D) (hw : w ∈ x.Sl) : ¬ (b <+: w ∧ b ≠ w) := by
  rintro ⟨hp, hn⟩
  exact hb (aux_prefix_mem' hx (aux_mem_Sl'.mp hw).2 (aux_prefix_parent' hp hn))

/-- The guards and the three component sets of an applicable `graft`. -/
private theorem aux_graft_spec {x x' : Config N m} {a b : Word N}
    (h : graft a b x = some x') :
    a ∈ x.D ∧ a ∈ x.μ ∧ b ∈ x.μ ∧ b ∉ x.D ∧ b ≠ [] ∧ b.dropLast ∈ x.D ∧ ¬ a <+: b ∧
      x'.D = x.D.image (subst false a b) ∧ x'.μ = x.μ.image (subst true a b) ∧
      x'.ζ = x.ζ.image (subst true a b) := by
  unfold graft at h
  split at h
  · rename_i hg
    cases h
    exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1,
      hg.2.2.2.2.2.2.1, rfl, rfl, rfl⟩
  · cases h

/-- Deployed cells: `b ++ u` arrives iff `a ++ u` was there. -/
private theorem aux_graft_D_image {x : Config N m} {a b : Word N} (hx : x.WF)
    (hbd : b ∉ x.D) {u : Word N} :
    b ++ u ∈ x.D.image (subst false a b) ↔ a ++ u ∈ x.D := by
  constructor
  · intro hm
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hm
    have hi := congrArg (subst false b a) he
    rw [aux_subst_inv (aux_no_prefix' hx hbd hv), aux_subst_app b a u] at hi
    exact hi ▸ hv
  · intro hd
    exact Finset.mem_image.mpr ⟨a ++ u, hd, aux_subst_app a b u⟩

/-- Bits on the moved cone: `b ++ t` (with `t ≠ []`) carries the bit of `a ++ t`. -/
private theorem aux_graft_strict_image {x : Config N m} {a b : Word N} (hx : x.WF)
    (hbd : b ∉ x.D) {S : Finset (Word N)} (hS : S ⊆ x.Sl) {t : Word N} (ht : t ≠ []) :
    b ++ t ∈ S.image (subst true a b) ↔ a ++ t ∈ S := by
  constructor
  · intro hm
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hm
    have hi := congrArg (subst true b a) he
    rw [aux_subst_inv_strict (aux_no_strict_prefix' hx hbd (hS hv)),
      aux_subst_app_strict b a t ht] at hi
    exact hi ▸ hv
  · intro hd
    exact Finset.mem_image.mpr ⟨a ++ t, hd, aux_subst_app_strict a b t ht⟩

/-- Bits off the moved cone: a slot not below `a` keeps its bit and its address. -/
private theorem aux_graft_static_image {x : Config N m} {a b s : Word N} (hx : x.WF)
    (hbd : b ∉ x.D) {S : Finset (Word N)} (hS : S ⊆ x.Sl) (hsl : s ∈ x.Sl)
    (hpa : ¬ a <+: s) : s ∈ S.image (subst true a b) ↔ s ∈ S := by
  have hbs : subst true b a s = s := aux_subst_id_strict (aux_no_strict_prefix' hx hbd hsl)
  constructor
  · intro hm
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hm
    have hi := congrArg (subst true b a) he
    rw [aux_subst_inv_strict (aux_no_strict_prefix' hx hbd (hS hv)), hbs] at hi
    exact hi ▸ hv
  · intro hd
    exact Finset.mem_image.mpr ⟨s, hd, aux_subst_id hpa⟩

/-! ## (i) Prefix substitution and zero renumbering -/

/-- Re-addressing: a proper extension `a ++ w` of `a` is renamed to `b ++ w`, the suffix `w`
untouched (Theorem thm:graft-iso(i)). -/
theorem subst_append_of_ne_nil (a b w : Word N) (hw : w ≠ []) :
    subst true a b (a ++ w) = b ++ w :=
  aux_subst_app_strict a b w hw

/-- The root of the moved cone is renamed to the target site by the non-strict substitution,
which is the one `graft` applies to the deployed cells `D`. -/
theorem subst_self_false (a b : Word N) : subst false a b a = b := by
  simp [subst]

/-- The slot `a` itself stays behind: the strict substitution, which `graft` applies to the
occupancy and decommission markings, fixes `a` (reading note on Table tab:typing). -/
theorem subst_self_true (a b : Word N) : subst true a b a = a := by
  simp [subst]

/-- Zero renumbering: everything strictly below the substituted prefix is copied verbatim. -/
theorem subst_drop_eq (a b : Word N) (hp : a <+: s) (hne : s ≠ a) :
    (subst true a b s).drop b.length = s.drop a.length := by
  obtain ⟨u, rfl⟩ := hp
  have hu : u ≠ [] := by rintro rfl; simp at hne
  rw [aux_subst_app_strict a b u hu, List.drop_left, List.drop_left]

/-- The image of the strict cone of `a` is inside the strict cone of `b`, addresswise. -/
theorem subst_mem_cone (a b : Word N) (hp : a <+: s) (hne : s ≠ a) :
    b <+: subst true a b s ∧ subst true a b s ≠ b := by
  obtain ⟨u, rfl⟩ := hp
  have hu : u ≠ [] := by rintro rfl; simp at hne
  rw [aux_subst_app_strict a b u hu]
  exact ⟨List.prefix_append _ _, aux_append_ne b u hu⟩

/-- The address length changes by `|b| - |a|` and by nothing else; at equal tier
(`|a| = |b|`) the moved slots keep their tiers. -/
theorem subst_length_eq (a b : Word N) (hp : a <+: s) (hne : s ≠ a) :
    (subst true a b s).length + a.length = s.length + b.length := by
  obtain ⟨u, rfl⟩ := hp
  have hu : u ≠ [] := by rintro rfl; simp at hne
  rw [aux_subst_app_strict a b u hu]
  simp only [List.length_append]
  omega

/-! ## (i) The marking travels with the cells (Lemma lem:dup-digit) -/

variable [NeZero N]

/-- The address-level duplicate predicate: a slot is a designated co-located duplicate iff it
sits at tier at least `2` and its last digit is `0` (Definition def:calc-state, Lemma
lem:dup-digit). This is a property of the suffix alone, which is why it is graft-invariant. -/
def isMarkW (s : Word N) : Prop := 2 ≤ s.length ∧ s.getLast? = some 0

/-- The marked set `M(x) = {w0 : w ∈ D \ {ε}}` of Definition def:calc-state. -/
def markedSet (x : Config N m) : Set (Word N) :=
  (fun w => w ++ [(0 : Fin N)]) '' {w | w ∈ x.D ∧ w ≠ []}

/-- `M(x)` splits into the suffix condition `isMarkW` and the configuration condition
"the anchor is a deployed cell". -/
theorem mem_markedSet_iff : s ∈ markedSet x ↔ isMarkW s ∧ s.dropLast ∈ x.D := by
  constructor
  · rintro ⟨v, ⟨hv, hvn⟩, rfl⟩
    have hlv := List.length_pos_of_ne_nil hvn
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · simp
    · simpa using hv
  · rintro ⟨⟨hl, hg⟩, hd⟩
    have hdn : s.dropLast ≠ [] := by
      intro he
      have := congrArg List.length he
      simp only [List.length_dropLast, List.length_nil] at this
      omega
    exact ⟨s.dropLast, ⟨hd, hdn⟩, List.dropLast_append_getLast? (0 : Fin N) hg⟩

/-- Marked addresses are slots of the configuration. -/
theorem markedSet_subset_Sl (x : Config N m) : markedSet x ⊆ (x.Sl : Set (Word N)) := by
  intro u hu
  obtain ⟨hmk, hd⟩ := mem_markedSet_iff.mp hu
  have hl : 2 ≤ u.length := hmk.1
  have hun : u ≠ [] := by rintro rfl; simp at hl
  exact Finset.mem_coe.mpr (aux_mem_Sl'.mpr ⟨hun, hd⟩)

/-- **Marking transport, address level.** For a nonempty suffix `w` below nonempty prefixes,
being a designated duplicate does not see the prefix. -/
theorem isMarkW_append_iff (a b w : Word N) (ha : a ≠ []) (hb : b ≠ []) (hw : w ≠ []) :
    isMarkW (a ++ w) ↔ isMarkW (b ++ w) := by
  have hla := List.length_pos_of_ne_nil ha
  have hlb := List.length_pos_of_ne_nil hb
  have hlw := List.length_pos_of_ne_nil hw
  simp only [isMarkW, List.getLast?_append_of_ne_nil _ hw, List.length_append]
  constructor
  · rintro ⟨-, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨-, h2⟩
    exact ⟨by omega, h2⟩

/-- The same, read through `subst`. -/
theorem isMarkW_subst_iff (ha : a ≠ []) (hb : b ≠ []) (hp : a <+: s) (hne : s ≠ a) :
    isMarkW (subst true a b s) ↔ isMarkW s := by
  obtain ⟨u, rfl⟩ := hp
  have hu : u ≠ [] := by rintro rfl; simp at hne
  rw [aux_subst_app_strict a b u hu]
  exact isMarkW_append_iff b a u hb ha hu

/-- **Marking transport, configuration level.** A slot strictly below `a` is a designated
duplicate of `x` iff its image is a designated duplicate of the grafted configuration. -/
theorem graft_mem_markedSet_iff (hx : x.WF) (h : graft a b x = some x')
    (hp : a <+: s) (hne : s ≠ a) :
    subst true a b s ∈ markedSet x' ↔ s ∈ markedSet x := by
  obtain ⟨ha, -, -, hbd, hbn, -, hab, hD, -, -⟩ := aux_graft_spec h
  have han : a ≠ [] := by rintro rfl; exact hab List.nil_prefix
  obtain ⟨u, rfl⟩ := hp
  have hu : u ≠ [] := by rintro rfl; simp at hne
  rw [aux_subst_app_strict a b u hu, mem_markedSet_iff, mem_markedSet_iff,
    List.dropLast_append_of_ne_nil hu, List.dropLast_append_of_ne_nil hu, hD]
  constructor
  · rintro ⟨hmk, hdd⟩
    exact ⟨(isMarkW_append_iff b a u hbn han hu).mp hmk,
      (aux_graft_D_image hx hbd).mp hdd⟩
  · rintro ⟨hmk, hdd⟩
    exact ⟨(isMarkW_append_iff a b u han hbn hu).mp hmk,
      (aux_graft_D_image hx hbd).mpr hdd⟩

/-- `M(x') ∩ cone(b) = {b w : a w ∈ M(x)}`, the identity of Theorem thm:graft-iso(i), with
the cones read strictly (`w ≠ ε`): the anchors `a` and `b` are members of static cells and
are not part of the moved set. -/
theorem graft_markedSet_cone (hx : x.WF) (h : graft a b x = some x') :
    markedSet x' ∩ {u | b <+: u ∧ u ≠ b}
      = subst true a b '' (markedSet x ∩ {u | a <+: u ∧ u ≠ a}) := by
  ext u
  constructor
  · rintro ⟨hu, hpu, hnu⟩
    obtain ⟨v, rfl⟩ := hpu
    have hv : v ≠ [] := by rintro rfl; simp at hnu
    have hsub : subst true a b (a ++ v) = b ++ v := aux_subst_app_strict a b v hv
    refine ⟨a ++ v, ⟨?_, List.prefix_append _ _, aux_append_ne a v hv⟩, hsub⟩
    exact (graft_mem_markedSet_iff hx h (List.prefix_append a v)
      (aux_append_ne a v hv)).mp (by rwa [hsub])
  · rintro ⟨v, ⟨hv, hpv, hnv⟩, rfl⟩
    exact ⟨(graft_mem_markedSet_iff hx h hpv hnv).mpr hv, subst_mem_cone a b hpv hnv⟩

/-! ## (ii) The moved set and the graft isomorphism -/

/-- The moved slots of a graft at `a`: the members of the deployed cells inside `cone(a)`,
equivalently the slots strictly below `a` (Lemma lem:edge-cut, Theorem thm:graft-iso(ii)). -/
def movedSlotSet (a : Word N) (x : Config N m) : Set (Word N) :=
  {s | s ∈ x.Sl ∧ a <+: s ∧ s ≠ a}

theorem mem_movedSlots_iff :
    s ∈ movedSlotSet a x ↔ (a <+: s ∧ s ≠ a ∧ s.dropLast ∈ x.D) := by
  constructor
  · rintro ⟨hsl, hp, hn⟩
    exact ⟨hp, hn, (aux_mem_Sl'.mp hsl).2⟩
  · rintro ⟨hp, hn, hd⟩
    have hsn : s ≠ [] := by
      rintro rfl
      rw [List.prefix_nil] at hp
      exact hn hp.symm
    exact ⟨aux_mem_Sl'.mpr ⟨hsn, hd⟩, hp, hn⟩

/-- **Non-vacuity of the isomorphism.** An applicable graft always moves something: `a` is a
deployed cell, so all `N` members of `C(a)` are moved slots. Without this, `graft_iso` could
be read as an equivalence of two empty sets. -/
theorem movedSlots_nonempty (hx : x.WF) (h : graft a b x = some x') :
    (movedSlotSet a x).Nonempty := by
  obtain ⟨ha, -⟩ := aux_graft_spec h
  refine ⟨a ++ [(0 : Fin N)], mem_movedSlots_iff.mpr ⟨List.prefix_append _ _, ?_, ?_⟩⟩
  · exact aux_append_ne a [(0 : Fin N)] (by simp)
  · simpa using ha

/-- The re-addressing map sends moved slots to moved slots of the result. -/
theorem graft_mapsTo_movedSlots (hx : x.WF) (h : graft a b x = some x') :
    Set.MapsTo (subst true a b) (movedSlotSet a x) (movedSlotSet b x') := by
  obtain ⟨-, -, -, hbd, -, -, -, hD, -, -⟩ := aux_graft_spec h
  intro u hu
  obtain ⟨hpu, hnu, hdu⟩ := mem_movedSlots_iff.mp hu
  obtain ⟨v, rfl⟩ := hpu
  have hv : v ≠ [] := by rintro rfl; simp at hnu
  rw [List.dropLast_append_of_ne_nil hv] at hdu
  rw [aux_subst_app_strict a b v hv]
  refine mem_movedSlots_iff.mpr ⟨List.prefix_append _ _, aux_append_ne b v hv, ?_⟩
  rw [List.dropLast_append_of_ne_nil hv, hD]
  exact (aux_graft_D_image hx hbd).mpr hdu

theorem graft_injOn_movedSlots (hx : x.WF) (h : graft a b x = some x') :
    Set.InjOn (subst true a b) (movedSlotSet a x) := by
  intro u hu v hv he
  obtain ⟨hpu, hnu, -⟩ := mem_movedSlots_iff.mp hu
  obtain ⟨hpv, hnv, -⟩ := mem_movedSlots_iff.mp hv
  obtain ⟨p, rfl⟩ := hpu
  obtain ⟨q, rfl⟩ := hpv
  have hp : p ≠ [] := by rintro rfl; simp at hnu
  have hq : q ≠ [] := by rintro rfl; simp at hnv
  rw [aux_subst_app_strict a b p hp, aux_subst_app_strict a b q hq] at he
  rw [List.append_cancel_left he]

theorem graft_surjOn_movedSlots (hx : x.WF) (h : graft a b x = some x') :
    Set.SurjOn (subst true a b) (movedSlotSet a x) (movedSlotSet b x') := by
  obtain ⟨-, -, -, hbd, -, -, -, hD, -, -⟩ := aux_graft_spec h
  intro u hu
  obtain ⟨hpu, hnu, hdu⟩ := mem_movedSlots_iff.mp hu
  obtain ⟨v, rfl⟩ := hpu
  have hv : v ≠ [] := by rintro rfl; simp at hnu
  rw [List.dropLast_append_of_ne_nil hv, hD] at hdu
  refine ⟨a ++ v, mem_movedSlots_iff.mpr ⟨List.prefix_append _ _, aux_append_ne a v hv, ?_⟩,
    aux_subst_app_strict a b v hv⟩
  rw [List.dropLast_append_of_ne_nil hv]
  exact (aux_graft_D_image hx hbd).mp hdu

/-- **The moved set arrives whole.** `a w ↦ b w` is a bijection from the moved slots of `x`
onto the moved slots of `x'`. -/
theorem graft_bijOn_movedSlots (hx : x.WF) (h : graft a b x = some x') :
    Set.BijOn (subst true a b) (movedSlotSet a x) (movedSlotSet b x') :=
  ⟨graft_mapsTo_movedSlots hx h, graft_injOn_movedSlots hx h, graft_surjOn_movedSlots hx h⟩

/-- **Suffix covariance on the moved set** (Theorem thm:graft-iso(ii)): both clauses of the
two-clause law of Theorem thm:adjacency-II depend only on the suffixes, hence are invariant
under replacing the prefix `a` by `b`. This is `Calc.adjW_append_iff` read on `subst`. -/
theorem graft_adjW_iff (hs : s ∈ movedSlotSet a x) (ht : t ∈ movedSlotSet a x) :
    AdjW s t ↔ AdjW (subst true a b s) (subst true a b t) := by
  obtain ⟨hps, hns, -⟩ := mem_movedSlots_iff.mp hs
  obtain ⟨hpt, hnt, -⟩ := mem_movedSlots_iff.mp ht
  obtain ⟨p, rfl⟩ := hps
  obtain ⟨q, rfl⟩ := hpt
  have hp : p ≠ [] := by rintro rfl; simp at hns
  have hq : q ≠ [] := by rintro rfl; simp at hnt
  rw [aux_subst_app_strict a b p hp, aux_subst_app_strict a b q hq]
  exact adjW_append_iff a b p q hp hq

/-- Edges go to edges. -/
theorem graft_adjW_preserve (hs : s ∈ movedSlotSet a x) (ht : t ∈ movedSlotSet a x)
    (hadj : AdjW s t) : AdjW (subst true a b s) (subst true a b t) :=
  (graft_adjW_iff hs ht).mp hadj

/-- Non-edges go to non-edges: the map reflects adjacency. -/
theorem graft_adjW_reflect (hs : s ∈ movedSlotSet a x) (ht : t ∈ movedSlotSet a x)
    (hadj : AdjW (subst true a b s) (subst true a b t)) : AdjW s t :=
  (graft_adjW_iff hs ht).mpr hadj

/-- **Theorem thm:graft-iso(ii), packaged.** The re-addressing `a w ↦ b w` is an isomorphism
from the subgraph of `G(x)` induced on the moved slots onto the subgraph of `G(x')` induced
on their images: an equivalence of the two slot sets, given by `subst true a b`, under which
adjacency holds on one side exactly when it holds on the other. -/
theorem graft_iso (hx : x.WF) (h : graft a b x = some x') :
    ∃ e : ↥(movedSlotSet a x) ≃ ↥(movedSlotSet b x'),
      (∀ u : ↥(movedSlotSet a x), (e u : Word N) = subst true a b (u : Word N)) ∧
      (∀ u v : ↥(movedSlotSet a x),
        AdjW (u : Word N) (v : Word N) ↔ AdjW (e u : Word N) (e v : Word N)) := by
  refine ⟨Set.BijOn.equiv _ (graft_bijOn_movedSlots hx h), fun u => rfl, fun u v => ?_⟩
  exact graft_adjW_iff u.2 v.2

/-! ## (i) Occupancy and decommission bits transport verbatim -/

/-- Occupancy of a moved slot is carried to the image slot and to nothing else. -/
theorem graft_mem_mu_iff_moved (hx : x.WF) (h : graft a b x = some x')
    (hp : a <+: s) (hne : s ≠ a) :
    s ∈ x.μ ↔ subst true a b s ∈ x'.μ := by
  obtain ⟨-, -, -, hbd, -, -, -, -, hM, -⟩ := aux_graft_spec h
  obtain ⟨u, rfl⟩ := hp
  have hu : u ≠ [] := by rintro rfl; simp at hne
  rw [aux_subst_app_strict a b u hu, hM]
  exact (aux_graft_strict_image hx hbd hx.2.2.2.1 hu).symm

/-- Decommission bits of moved slots are carried the same way. -/
theorem graft_mem_zeta_iff_moved (hx : x.WF) (h : graft a b x = some x')
    (hp : a <+: s) (hne : s ≠ a) :
    s ∈ x.ζ ↔ subst true a b s ∈ x'.ζ := by
  obtain ⟨-, -, -, hbd, -, -, -, -, -, hZ⟩ := aux_graft_spec h
  obtain ⟨u, rfl⟩ := hp
  have hu : u ≠ [] := by rintro rfl; simp at hne
  rw [aux_subst_app_strict a b u hu, hZ]
  exact (aux_graft_strict_image hx hbd hx.2.2.2.2.1 hu).symm

/-- Slots outside the moved cone keep their occupancy bit, address included. -/
theorem graft_mem_mu_iff_static (hx : x.WF) (h : graft a b x = some x')
    (hs : s ∈ x.Sl) (hp : ¬ a <+: s) :
    s ∈ x.μ ↔ s ∈ x'.μ := by
  obtain ⟨-, -, -, hbd, -, -, -, -, hM, -⟩ := aux_graft_spec h
  rw [hM]
  exact (aux_graft_static_image hx hbd hx.2.2.2.1 hs hp).symm

/-- Slots outside the moved cone keep their decommission bit. -/
theorem graft_mem_zeta_iff_static (hx : x.WF) (h : graft a b x = some x')
    (hs : s ∈ x.Sl) (hp : ¬ a <+: s) :
    s ∈ x.ζ ↔ s ∈ x'.ζ := by
  obtain ⟨-, -, -, hbd, -, -, -, -, -, hZ⟩ := aux_graft_spec h
  rw [hZ]
  exact (aux_graft_static_image hx hbd hx.2.2.2.2.1 hs hp).symm

/-- The anchor `a` stays behind with its participant: it is a slot of the static cell
`C(pre a)` and remains occupied after the graft. -/
theorem graft_anchor_stays (hx : x.WF) (h : graft a b x = some x') : a ∈ x'.μ := by
  obtain ⟨-, ham, -, -, -, -, -, -, hM, -⟩ := aux_graft_spec h
  rw [hM]
  exact Finset.mem_image.mpr ⟨a, ham, subst_self_true a b⟩

/-- The anchor's decommission bit stays put too, completing the case `s = a` left open by
the "moved" and "static" transport lemmas: `a` is occupied by the guards, hence outside `ζ`
by the disjointness clause of `Config.WF`, and nothing is re-addressed onto `a`. -/
theorem graft_anchor_not_zeta (hx : x.WF) (h : graft a b x = some x') :
    a ∉ x.ζ ∧ a ∉ x'.ζ := by
  obtain ⟨ha, ham, -, hbd, -, -, -, -, -, hZ⟩ := aux_graft_spec h
  have hz : a ∉ x.ζ := fun hzz =>
    Finset.disjoint_left.mp hx.2.2.2.2.2 hzz (Finset.mem_union_left _ ham)
  refine ⟨hz, ?_⟩
  rw [hZ]
  intro hm
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hm
  have hi := congrArg (subst true b a) he
  rw [aux_subst_inv_strict (aux_no_strict_prefix' hx hbd (hx.2.2.2.2.1 hu)),
    aux_subst_id (aux_no_prefix' hx hbd ha)] at hi
  exact hz (hi ▸ hu)

/-- Deployed cells transport by the non-strict substitution, bijectively on the cone of `a`
(Theorem thm:graft-iso(i): every deployed `a w` is replaced by `b w`). -/
theorem graft_mem_D_iff_moved (hx : x.WF) (h : graft a b x = some x') (hp : a <+: w) :
    w ∈ x.D ↔ subst false a b w ∈ x'.D := by
  obtain ⟨-, -, -, hbd, -, -, -, hD, -, -⟩ := aux_graft_spec h
  obtain ⟨u, rfl⟩ := hp
  rw [aux_subst_app a b u, hD]
  exact (aux_graft_D_image hx hbd).symm

/-- Deployed cells outside both cones are untouched. The hypothesis `¬ b <+: w` is vacuous
on the left (no deployed cell of `x` has the vacant slot `b` as a prefix, `D` being
prefix-closed with `b ∉ D`); it is what excludes, on the right, the cells that have just
arrived at `b`. -/
theorem graft_mem_D_iff_static (hx : x.WF) (h : graft a b x = some x')
    (hpa : ¬ a <+: w) (hpb : ¬ b <+: w) :
    w ∈ x.D ↔ w ∈ x'.D := by
  obtain ⟨-, -, -, hbd, -, -, -, hD, -, -⟩ := aux_graft_spec h
  rw [hD]
  constructor
  · intro hw
    exact Finset.mem_image.mpr ⟨w, hw, aux_subst_id hpa⟩
  · intro hw
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hw
    have hi := congrArg (subst false b a) he
    rw [aux_subst_inv (aux_no_prefix' hx hbd hu), aux_subst_id hpb] at hi
    exact hi ▸ hu

/-! ## The hypotheses of this file are satisfiable -/

/-- **Non-vacuity of the graft hypotheses.** Every transport law above is conditioned on
`x.WF` together with `graft a b x = some x'`. This witness rules out the reading in which
that pair of hypotheses is unsatisfiable and all of the above is vacuously true. At `N = 3`,
`m = 2` take `D = {ε, 0}`, `μ = {0, 2}`, `ζ = ∅`: the guards of Table tab:typing hold for
`graft(0 → 2)` — `0` is a deployed and occupied cell, `2` is an occupied slot of the seed
cell that carries no cell of its own, its parent `ε` is deployed, `0` is not a prefix of
`2`, and the moved cell fits below tier `m`. Combined with `movedSlots_nonempty` this makes
`graft_iso` an isomorphism between two genuinely nonempty vertex sets. -/
theorem graft_hypotheses_satisfiable :
    ∃ y y' : Config 3 2, y.WF ∧ graft [0] [2] y = some y' := by
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp
    (show (graft ([0] : Word 3) [2] (⟨{[], [0]}, {[0], [2]}, ∅⟩ : Config 3 2)).isSome by decide)
  exact ⟨_, y', by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide, hy'⟩

end Calc

end HSFN
