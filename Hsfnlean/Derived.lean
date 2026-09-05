/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Calculus

/-!
# Derived operations: the swap is three grafts
(Section "Derived operations" of the calculus section; Lemma lem:bridge(ii);
row "Load-balancing swap" of Table tab:opdict)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

The paper defines, for a staging slot `c` (occupied, cell-free, deep enough),

  `swap(a,b;c) = graft(c → b) ∘ graft(b → a) ∘ graft(a → c)`,

and asserts (Lemma lem:bridge(ii)) that its boundary shadow is the transposition `τ_{a,b}`
of the two cones, restricted to the complement of `cone(c)`. This module formalizes the
*address-level* content of that definition, which is what the composite of three prefix
substitutions literally is.

* `swapW a b c` is the composite of the three non-strict prefix substitutions `a ↦ c`,
  `b ↦ a`, `c ↦ b`, applied in the order in which the paper composes the three grafts
  (right to left: `a → c` first). It is exactly the map `Calc.graft` applies to the
  deployed-cell set `D`.
* `swapWμ a b c` is the same composite of the *strict* substitutions, which is the map
  `Calc.graft` applies to the occupancy set `μ` and the decommission set `ζ`. The two differ
  at the anchor word itself: the cell tree at `a` moves, while the slot `a` stays behind
  (`swapWμ_anchor_left`). That is the paper's remark that the grafts move structure while a
  separate occupancy exchange moves custodianship.
* `swap_three_grafts` states that under the guards of `Calc.graft` the three-letter word is
  defined at a configuration `x`, and identifies the three components of the result as the
  images of the components of `x` under those two composites.
* `swap_cone_exchange` is the cone-exchange reading of Lemma lem:bridge(ii) at the level of
  deployed cells: `cone(a)` and `cone(b)` are exchanged verbatim and everything having none
  of `a`, `b`, `c` as a prefix is fixed.
* `swapW_involutive` is involutivity of the transposition, valid exactly off `cone(c)`
  ("one swap is available only off its staging cone").
* `swapWitness_defined` and `swapWitness2_exchange` check, on explicit configurations, that
  the guard hypotheses of `swap_three_grafts` are jointly satisfiable and that the resulting
  word really moves deployed cells, so that nothing above is vacuously true.

## What this module does NOT formalize

* No boundary. Lemma lem:bridge(ii) is a statement about the boundary shadow in the Cuntz
  inverse monoid `C_N` acting on `∂T = Σ_N^ω`. Here everything is finite words; the Cantor
  space, `C_N`, the Higman–Thompson group `V_N` (Lemma lem:transp-gen,
  Theorem thm:vn-identification) and the join of two staged swaps (Lemma lem:bridge(iii))
  are all out of scope.
* No participants. The paper's `swap(a,b)` also performs the four-letter occupancy exchange
  `join join leave leave` and moves participant identity, which is protocol metadata riding
  on the occupancy marking. `Calc.Config` records only which slots are occupied, so the
  exchange of participants is not modelled at all; only the three grafts are.
* No graph-level claim. That the moved subnetwork arrives isomorphic
  (Theorem thm:graft-iso(ii)) is `Calc.adjW_append_iff`, not re-stated here.
* No existence of a staging slot. The paper notes that when no suitable `c` exists,
  `spawn` and `join` create one at the frontier; here `c` is always a hypothesis, never
  constructed.

The statements below are frozen; only the proofs are to be supplied.
-/

namespace HSFN

namespace Calc

variable {N m : ℕ}

/-! ## Incomparability -/

/-- Two words are *incomparable* when neither is a prefix of the other. This is the paper's
hypothesis on `a`, `b` in Lemma lem:bridge and in the definition of the transposition
`τ_{a,b}` of the two cones. -/
def SwapIncomp (u v : Word N) : Prop := ¬ u <+: v ∧ ¬ v <+: u

/-- The three words `a`, `b`, `c` are pairwise incomparable: the exact hypothesis of
Lemma lem:bridge(ii), where `c` is a staging address "incomparable to both `a` and `b`". -/
def SwapIncomp3 (a b c : Word N) : Prop :=
  SwapIncomp a b ∧ SwapIncomp a c ∧ SwapIncomp b c

/-- An incomparable pair consists of nonempty words, since `[]` is a prefix of everything. -/
theorem ne_nil_of_swapIncomp {u v : Word N} (h : SwapIncomp u v) : u ≠ [] ∧ v ≠ [] := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact h.1 List.nil_prefix
  · rintro rfl
    exact h.2 List.nil_prefix

/-! ## The address action of the derived swap

`swap(a,b;c) = graft(c → b) ∘ graft(b → a) ∘ graft(a → c)`, composed right to left. -/

/-- The action of the derived word `swap(a,b;c)` on deployed-cell addresses: the composite of
the three non-strict prefix substitutions, applied in the order in which the paper composes
the three grafts (rightmost graft first). This is the map `graft` applies to `D`. -/
def swapW (a b c : Word N) (w : Word N) : Word N :=
  subst false c b (subst false b a (subst false a c w))

/-- The action of the derived word `swap(a,b;c)` on occupied and decommissioned slots: the
same composite, with the *strict* substitutions that `graft` applies to `μ` and `ζ`. -/
def swapWμ (a b c : Word N) (w : Word N) : Word N :=
  subst true c b (subst true b a (subst true a c w))

/-! ### Word-level toolbox

`Calculus.lean` proves these facts about `subst` for its own use, but as `private` lemmas;
they are re-derived here (same proofs) because this file needs them again. -/

/-- A substitution whose anchor is not a prefix of the argument is the identity there. -/
private theorem aux_fix {s : Bool} {a b w : Word N} (h : ¬ a <+: w) : subst s a b w = w := by
  simp [subst, h]

/-- The non-strict substitution on the cone of its anchor. -/
private theorem aux_app (a b t : Word N) : subst false a b (a ++ t) = b ++ t := by
  simp [subst]

/-- The strict substitution on the cone of its anchor, minus the anchor itself. -/
private theorem aux_app_strict (a b t : Word N) (ht : t ≠ []) :
    subst true a b (a ++ t) = b ++ t := by
  have hn : a ≠ a ++ t := by
    intro he
    have h1 := congrArg List.length he
    have h2 := List.length_pos_of_ne_nil ht
    simp only [List.length_append] at h1
    omega
  simp [subst, hn]

/-- The non-strict substitution moves its own anchor. -/
private theorem aux_anchor (a b : Word N) : subst false a b a = b := by
  simp [subst]

/-- The strict substitution fixes its own anchor: the slot `a` stays behind. -/
private theorem aux_anchor_strict (a b : Word N) : subst true a b a = a := by
  simp [subst]

/-- Two prefixes of a common word are comparable, so an incomparable pair stays incomparable
after the second word is extended. -/
private theorem aux_npa {u v : Word N} (h1 : ¬ u <+: v) (h2 : ¬ v <+: u) (w : Word N) :
    ¬ u <+: v ++ w := by
  intro hp
  rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append v w) with h | h
  · exact h1 h
  · exact h2 h

/-! ### (a) The exchange law on words (pure list arithmetic)

Concrete instance of the hypotheses: `N = 3`, `a = [0]`, `b = [1]`, `c = [2]`. -/

/-- The cone at `a` arrives verbatim at `b`: `a w ↦ b w`, the suffix untouched. -/
theorem swapW_append_left {a b c : Word N} (h : SwapIncomp3 a b c) (w : Word N) :
    swapW a b c (a ++ w) = b ++ w := by
  unfold swapW
  rw [aux_app, aux_fix (aux_npa h.2.2.1 h.2.2.2 w), aux_app]

/-- The cone at `b` arrives verbatim at `a`: `b w ↦ a w`, the suffix untouched. -/
theorem swapW_append_right {a b c : Word N} (h : SwapIncomp3 a b c) (w : Word N) :
    swapW a b c (b ++ w) = a ++ w := by
  unfold swapW
  rw [aux_fix (aux_npa h.1.1 h.1.2 w), aux_app, aux_fix (aux_npa h.2.1.2 h.2.1.1 w)]

/-- The slot-level exchange, for the slots strictly below the anchor `a`. -/
theorem swapWμ_append_left {a b c : Word N} (h : SwapIncomp3 a b c) {w : Word N} (hw : w ≠ []) :
    swapWμ a b c (a ++ w) = b ++ w := by
  unfold swapWμ
  rw [aux_app_strict _ _ _ hw, aux_fix (aux_npa h.2.2.1 h.2.2.2 w), aux_app_strict _ _ _ hw]

/-- The slot-level exchange, for the slots strictly below the anchor `b`. -/
theorem swapWμ_append_right {a b c : Word N} (h : SwapIncomp3 a b c) {w : Word N} (hw : w ≠ []) :
    swapWμ a b c (b ++ w) = a ++ w := by
  unfold swapWμ
  rw [aux_fix (aux_npa h.1.1 h.1.2 w), aux_app_strict _ _ _ hw,
    aux_fix (aux_npa h.2.1.2 h.2.1.1 w)]

/-- The anchor slot `a` itself stays behind: the grafts move the cell tree at `a`, not the
occupancy of the slot `a`. This is why the paper needs the separate four-letter occupancy
exchange, which this module does not model. -/
theorem swapWμ_anchor_left {a b c : Word N} (h : SwapIncomp3 a b c) :
    swapWμ a b c a = a := by
  unfold swapWμ
  rw [aux_anchor_strict, aux_fix h.1.2, aux_fix h.2.1.2]

/-- Likewise at the anchor `b`. -/
theorem swapWμ_anchor_right {a b c : Word N} (h : SwapIncomp3 a b c) :
    swapWμ a b c b = b := by
  unfold swapWμ
  rw [aux_fix h.1.1, aux_anchor_strict, aux_fix h.2.2.2]

/-- Everything outside the three cones is fixed. No incomparability hypothesis is needed in
this direction: having none of `a`, `b`, `c` as a prefix already defeats all three
substitutions. -/
theorem swapW_of_not_prefix {a b c s : Word N}
    (ha : ¬ a <+: s) (hb : ¬ b <+: s) (hc : ¬ c <+: s) :
    swapW a b c s = s := by
  unfold swapW
  rw [aux_fix ha, aux_fix hb, aux_fix hc]

/-- The strict form of the previous statement. -/
theorem swapWμ_of_not_prefix {a b c s : Word N}
    (ha : ¬ a <+: s) (hb : ¬ b <+: s) (hc : ¬ c <+: s) :
    swapWμ a b c s = s := by
  unfold swapWμ
  rw [aux_fix ha, aux_fix hb, aux_fix hc]

/-! ### (c) Involutivity off the staging cone -/

/-- On the staging cone itself the composite is *not* the transposition: it drops the
`c`-cone onto `b`. Nothing in the configuration is ever addressed there (the guard `c ∉ D`
of the first graft keeps `cone(c)` free of deployed cells), which is exactly why Lemma
lem:bridge(ii) restricts the shadow to `∂T \ cone(c)`. Stated so that the restriction in
`swapW_involutive` is visibly necessary rather than a convenience. -/
theorem swapW_append_staging {a b c : Word N} (h : SwapIncomp3 a b c) (w : Word N) :
    swapW a b c (c ++ w) = b ++ w := by
  unfold swapW
  rw [aux_fix (aux_npa h.2.1.1 h.2.1.2 w), aux_fix (aux_npa h.2.2.1 h.2.2.2 w), aux_app]

/-- `swap(a,b;c)` is an involution on the words having no `c`-prefix: the transposition
`τ_{a,b}` restricted to `∂T \ cone(c)` of Lemma lem:bridge(ii), read on finite words. The
hypothesis `¬ c <+: s` is essential and not decoration: `swapW a b c (c ++ w) = b ++ w`,
which a second application sends to `a ++ w ≠ c ++ w`. -/
theorem swapW_involutive {a b c : Word N} (h : SwapIncomp3 a b c) {s : Word N}
    (hs : ¬ c <+: s) : swapW a b c (swapW a b c s) = s := by
  by_cases ha : a <+: s
  · obtain ⟨t, rfl⟩ := ha
    rw [swapW_append_left h, swapW_append_right h]
  · by_cases hb : b <+: s
    · obtain ⟨t, rfl⟩ := hb
      rw [swapW_append_right h, swapW_append_left h]
    · rw [swapW_of_not_prefix ha hb hs, swapW_of_not_prefix ha hb hs]

/-- The same, for the strict (slot) action. -/
theorem swapWμ_involutive {a b c : Word N} (h : SwapIncomp3 a b c) {s : Word N}
    (hs : ¬ c <+: s) : swapWμ a b c (swapWμ a b c s) = s := by
  by_cases ha : a <+: s
  · obtain ⟨t, rfl⟩ := ha
    rcases eq_or_ne t [] with rfl | ht
    · rw [List.append_nil, swapWμ_anchor_left h, swapWμ_anchor_left h]
    · rw [swapWμ_append_left h ht, swapWμ_append_right h ht]
  · by_cases hb : b <+: s
    · obtain ⟨t, rfl⟩ := hb
      rcases eq_or_ne t [] with rfl | ht
      · rw [List.append_nil, swapWμ_anchor_right h, swapWμ_anchor_right h]
      · rw [swapWμ_append_right h ht, swapWμ_append_left h ht]
    · rw [swapWμ_of_not_prefix ha hb hs, swapWμ_of_not_prefix ha hb hs]

/-! ### Configuration-level toolbox

Again re-derivations of `private` lemmas of `Calculus.lean`, plus the two case analyses that
drive the guard bookkeeping below. -/

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
  simp only [Config.Sl, Finset.mem_biUnion, aux_mem_cellW']
  aesop

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

private theorem aux_parent_not_below' {w : Word N} (hw : w ≠ []) : ¬ w <+: w.dropLast := by
  intro hp
  have h1 := hp.length_le
  have h2 := List.length_pos_of_ne_nil hw
  simp only [List.length_dropLast] at h1
  omega

/-- The three ways a word can meet the first two substitutions of the composite. -/
private theorem aux_fD_cases {a b c : Word N} (h : SwapIncomp3 a b c) (v : Word N) :
    (∃ t, v = a ++ t ∧ subst false b a (subst false a c v) = c ++ t) ∨
      (∃ u, v = b ++ u ∧ subst false b a (subst false a c v) = a ++ u) ∨
      (¬ a <+: v ∧ ¬ b <+: v ∧ subst false b a (subst false a c v) = v) := by
  by_cases hp : a <+: v
  · obtain ⟨t, rfl⟩ := hp
    exact Or.inl ⟨t, rfl, by rw [aux_app, aux_fix (aux_npa h.2.2.1 h.2.2.2 t)]⟩
  · by_cases hq : b <+: v
    · obtain ⟨u, rfl⟩ := hq
      exact Or.inr (Or.inl ⟨u, rfl, by rw [aux_fix hp, aux_app]⟩)
    · exact Or.inr (Or.inr ⟨hp, hq, by rw [aux_fix hp, aux_fix hq]⟩)

/-- The three ways a word off the staging cone can meet the full composite. -/
private theorem aux_swapW_cases {a b c : Word N} (h : SwapIncomp3 a b c) {v : Word N}
    (hv : ¬ c <+: v) :
    (∃ t, v = a ++ t ∧ swapW a b c v = b ++ t) ∨
      (∃ u, v = b ++ u ∧ swapW a b c v = a ++ u) ∨
      (¬ a <+: v ∧ ¬ b <+: v ∧ swapW a b c v = v) := by
  by_cases hp : a <+: v
  · obtain ⟨t, rfl⟩ := hp
    exact Or.inl ⟨t, rfl, swapW_append_left h t⟩
  · by_cases hq : b <+: v
    · obtain ⟨u, rfl⟩ := hq
      exact Or.inr (Or.inl ⟨u, rfl, swapW_append_right h u⟩)
    · exact Or.inr (Or.inr ⟨hp, hq, swapW_of_not_prefix hp hq hv⟩)

/-- The two-graft fragment in the explicit form the three-graft proof needs. -/
private theorem aux_two_grafts {x : Config N m} {a b c : Word N}
    (hx : x.WF) (hinc : SwapIncomp3 a b c)
    (haD : a ∈ x.D) (haμ : a ∈ x.μ) (hbD : b ∈ x.D) (hbμ : b ∈ x.μ)
    (hcμ : c ∈ x.μ) (hcD : c ∉ x.D)
    (hdepth_ac : ∀ w ∈ x.D, a <+: w → c.length + (w.length - a.length) + 1 ≤ m)
    (hdepth_ba : ∀ w ∈ x.D, b <+: w → a.length + (w.length - b.length) + 1 ≤ m) :
    (graft a c x).bind (graft b a) =
      some ⟨x.D.image (fun w => subst false b a (subst false a c w)),
        x.μ.image (fun w => subst true b a (subst true a c w)),
        x.ζ.image (fun w => subst true b a (subst true a c w))⟩ := by
  obtain ⟨hane, hbne⟩ := ne_nil_of_swapIncomp hinc.1
  obtain ⟨hcne, hcpar⟩ := aux_mem_Sl'.mp (hx.2.2.2.1 hcμ)
  have hg1 : graft a c x = some ⟨x.D.image (subst false a c), x.μ.image (subst true a c),
      x.ζ.image (subst true a c)⟩ := by
    unfold graft
    rw [if_pos ⟨haD, haμ, hcμ, hcD, hcne, hcpar, hinc.2.1.1, hdepth_ac⟩]
  have hbD1 : b ∈ x.D.image (subst false a c) :=
    Finset.mem_image.mpr ⟨b, hbD, aux_fix hinc.1.1⟩
  have hbμ1 : b ∈ x.μ.image (subst true a c) :=
    Finset.mem_image.mpr ⟨b, hbμ, aux_fix hinc.1.1⟩
  have haμ1 : a ∈ x.μ.image (subst true a c) :=
    Finset.mem_image.mpr ⟨a, haμ, aux_anchor_strict a c⟩
  have haD1 : a ∉ x.D.image (subst false a c) := by
    intro hm
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hm
    by_cases hp : a <+: v
    · obtain ⟨t, rfl⟩ := hp
      rw [aux_app] at he
      exact hinc.2.1.2 (he ▸ List.prefix_append c t)
    · rw [aux_fix hp] at he
      subst he
      exact hp (List.prefix_refl _)
  have hapar1 : a.dropLast ∈ x.D.image (subst false a c) :=
    Finset.mem_image.mpr ⟨a.dropLast, hx.2.2.1 a haD hane,
      aux_fix (aux_parent_not_below' hane)⟩
  have hfit1 : ∀ w ∈ x.D.image (subst false a c), b <+: w →
      a.length + (w.length - b.length) + 1 ≤ m := by
    intro w hw hbw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    by_cases hp : a <+: v
    · obtain ⟨t, rfl⟩ := hp
      rw [aux_app] at hbw
      exact absurd hbw (aux_npa hinc.2.2.1 hinc.2.2.2 t)
    · rw [aux_fix hp] at hbw ⊢
      exact hdepth_ba v hv hbw
  rw [hg1, Option.bind_some]
  unfold graft
  rw [if_pos ⟨hbD1, hbμ1, haμ1, haD1, hane, hapar1, hinc.1.2, hfit1⟩]
  simp only [Finset.image_image]
  rfl

/-! ### (b) The composite is a defined calculus word

The hypotheses are read off the guards of `Calc.graft`, one graft at a time.

* `graft a c` needs `a ∈ D`, `a ∈ μ`, `c ∈ μ`, `c ∉ D`, `c ≠ []`, `pre c ∈ D`, `¬ a <+: c`
  and the depth fit `hdepth_ac`. Nonemptiness of `c` and `pre c ∈ D` follow from `x.WF`
  together with `c ∈ x.μ`; `¬ a <+: c` is part of `SwapIncomp3`.
* `graft b a` needs `b` deployed and occupied in the first result, and the anchor `a`
  occupied but cell-free there. The slot `a` survives the first graft occupied, since
  `subst true a c a = a` (the strict substitution fixes its own anchor), and is vacated of
  its cell by that graft, since `subst false a c a = c` and no other image can equal `a`.
  So nothing is needed beyond `b ∈ D`, `b ∈ μ` and the depth fit `hdepth_ba`.
* `graft c b` needs `c` deployed (it is, as the image of `a`), `b` occupied and cell-free at
  that stage, and the depth fit `hdepth_ab`, which is `hdepth_ac` with the staging target `c`
  replaced by the final target `b`.

Concrete instance of all hypotheses: `N = 3`, `m = 3`,
`x = ⟨{[], [0], [1]}, {[0], [1], [2]}, ∅⟩`, `a = [0]`, `b = [1]`, `c = [2]`. Then `x.WF`
holds, `a, b ∈ x.D ∩ x.μ`, `c ∈ x.μ \ x.D`, the three words are pairwise incomparable, and
all three depth fits read `2 ≤ 3`. That instance is discharged in `swapWitness_defined`
below, and `swapWitness2_exchange` gives one on which the word is not the identity. -/
theorem swap_three_grafts {x : Config N m} {a b c : Word N}
    (hx : x.WF) (hinc : SwapIncomp3 a b c)
    (haD : a ∈ x.D) (haμ : a ∈ x.μ) (hbD : b ∈ x.D) (hbμ : b ∈ x.μ)
    (hcμ : c ∈ x.μ) (hcD : c ∉ x.D)
    (hdepth_ac : ∀ w ∈ x.D, a <+: w → c.length + (w.length - a.length) + 1 ≤ m)
    (hdepth_ba : ∀ w ∈ x.D, b <+: w → a.length + (w.length - b.length) + 1 ≤ m)
    (hdepth_ab : ∀ w ∈ x.D, a <+: w → b.length + (w.length - a.length) + 1 ≤ m) :
    ∃ x' : Config N m,
      ((graft a c x).bind (graft b a)).bind (graft c b) = some x' ∧
        x'.D = x.D.image (swapW a b c) ∧
        x'.μ = x.μ.image (swapWμ a b c) ∧
        x'.ζ = x.ζ.image (swapWμ a b c) := by
  obtain ⟨hane, hbne⟩ := ne_nil_of_swapIncomp hinc.1
  have h₂ := aux_two_grafts hx hinc haD haμ hbD hbμ hcμ hcD hdepth_ac hdepth_ba
  -- the guards of the third graft, read on the two-graft result
  have hcD2 : c ∈ x.D.image (fun w => subst false b a (subst false a c w)) :=
    Finset.mem_image.mpr ⟨a, haD, by
      show subst false b a (subst false a c a) = c
      rw [aux_anchor, aux_fix hinc.2.2.1]⟩
  have hcμ2 : c ∈ x.μ.image (fun w => subst true b a (subst true a c w)) :=
    Finset.mem_image.mpr ⟨c, hcμ, by
      show subst true b a (subst true a c c) = c
      rw [aux_fix hinc.2.1.1, aux_fix hinc.2.2.1]⟩
  have hbμ2 : b ∈ x.μ.image (fun w => subst true b a (subst true a c w)) :=
    Finset.mem_image.mpr ⟨b, hbμ, by
      show subst true b a (subst true a c b) = b
      rw [aux_fix hinc.1.1, aux_anchor_strict]⟩
  have hbD2 : b ∉ x.D.image (fun w => subst false b a (subst false a c w)) := by
    intro hm
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hm
    rcases aux_fD_cases hinc v with ⟨t, rfl, hf⟩ | ⟨u, rfl, hf⟩ | ⟨h1, h2, hf⟩
    · simp only [hf] at he
      exact hinc.2.2.2 (he ▸ List.prefix_append c t)
    · simp only [hf] at he
      exact hinc.1.1 (he ▸ List.prefix_append a u)
    · simp only [hf] at he
      subst he
      exact h2 (List.prefix_refl _)
  have hbpar2 : b.dropLast ∈ x.D.image (fun w => subst false b a (subst false a c w)) :=
    Finset.mem_image.mpr ⟨b.dropLast, hx.2.2.1 b hbD hbne, by
      show subst false b a (subst false a c b.dropLast) = b.dropLast
      rw [aux_fix (fun hp => hinc.1.1 (hp.trans b.dropLast_prefix)),
        aux_fix (aux_parent_not_below' hbne)]⟩
  have hfit2 : ∀ w ∈ x.D.image (fun w => subst false b a (subst false a c w)), c <+: w →
      b.length + (w.length - c.length) + 1 ≤ m := by
    intro w hw hcw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    rcases aux_fD_cases hinc v with ⟨t, rfl, hf⟩ | ⟨u, rfl, hf⟩ | ⟨h1, h2, hf⟩
    · have hfit := hdepth_ab (a ++ t) hv (List.prefix_append a t)
      simp only [hf, List.length_append, Nat.add_sub_cancel_left] at hfit ⊢
      exact hfit
    · exfalso
      simp only [hf] at hcw
      exact aux_npa hinc.2.1.2 hinc.2.1.1 u hcw
    · exfalso
      simp only [hf] at hcw
      exact hcD (aux_prefix_mem' hx hv hcw)
  refine ⟨⟨x.D.image (swapW a b c), x.μ.image (swapWμ a b c), x.ζ.image (swapWμ a b c)⟩,
    ?_, rfl, rfl, rfl⟩
  rw [h₂, Option.bind_some]
  unfold graft
  rw [if_pos ⟨hcD2, hcμ2, hbμ2, hbD2, hbne, hbpar2, hinc.2.2.2, hfit2⟩]
  simp only [Finset.image_image]
  rfl

/-- The two-graft fragment, stated separately: the first two grafts of the word are already
defined, the staging cone `c` holding the cell tree of `a` while the cell tree of `b` moves
onto the vacated anchor `a`. -/
theorem swap_two_grafts {x : Config N m} {a b c : Word N}
    (hx : x.WF) (hinc : SwapIncomp3 a b c)
    (haD : a ∈ x.D) (haμ : a ∈ x.μ) (hbD : b ∈ x.D) (hbμ : b ∈ x.μ)
    (hcμ : c ∈ x.μ) (hcD : c ∉ x.D)
    (hdepth_ac : ∀ w ∈ x.D, a <+: w → c.length + (w.length - a.length) + 1 ≤ m)
    (hdepth_ba : ∀ w ∈ x.D, b <+: w → a.length + (w.length - b.length) + 1 ≤ m) :
    ∃ x₂ : Config N m,
      (graft a c x).bind (graft b a) = some x₂ ∧
        x₂.D = x.D.image (fun w => subst false b a (subst false a c w)) ∧
        x₂.μ = x.μ.image (fun w => subst true b a (subst true a c w)) ∧
        x₂.ζ = x.ζ.image (fun w => subst true b a (subst true a c w)) :=
  ⟨_, aux_two_grafts hx hinc haD haμ hbD hbμ hcμ hcD hdepth_ac hdepth_ba, rfl, rfl, rfl⟩

/-- **Cone exchange (Lemma lem:bridge(ii) read on deployed cells).** Under the guards above
the three-graft word exchanges the two cones verbatim and fixes every deployed cell having
none of `a`, `b`, `c` as a prefix, in both directions. -/
theorem swap_cone_exchange {x x' : Config N m} {a b c : Word N}
    (hx : x.WF) (hinc : SwapIncomp3 a b c)
    (haD : a ∈ x.D) (haμ : a ∈ x.μ) (hbD : b ∈ x.D) (hbμ : b ∈ x.μ)
    (hcμ : c ∈ x.μ) (hcD : c ∉ x.D)
    (hdepth_ac : ∀ w ∈ x.D, a <+: w → c.length + (w.length - a.length) + 1 ≤ m)
    (hdepth_ba : ∀ w ∈ x.D, b <+: w → a.length + (w.length - b.length) + 1 ≤ m)
    (hdepth_ab : ∀ w ∈ x.D, a <+: w → b.length + (w.length - a.length) + 1 ≤ m)
    (hx' : ((graft a c x).bind (graft b a)).bind (graft c b) = some x') :
    (∀ w : Word N, a ++ w ∈ x.D ↔ b ++ w ∈ x'.D) ∧
      (∀ w : Word N, b ++ w ∈ x.D ↔ a ++ w ∈ x'.D) ∧
      (∀ s ∈ x.D, ¬ a <+: s → ¬ b <+: s → ¬ c <+: s → s ∈ x'.D) ∧
      (∀ s ∈ x'.D, ¬ a <+: s → ¬ b <+: s → ¬ c <+: s → s ∈ x.D) := by
  obtain ⟨x'', hcomp, hD, -, -⟩ :=
    swap_three_grafts hx hinc haD haμ hbD hbμ hcμ hcD hdepth_ac hdepth_ba hdepth_ab
  have hxx : x' = x'' := Option.some.inj (hx'.symm.trans hcomp)
  subst hxx
  have hnc : ∀ v ∈ x.D, ¬ c <+: v := fun v hv hp => hcD (aux_prefix_mem' hx hv hp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w
    constructor
    · intro hw
      rw [hD]
      exact Finset.mem_image.mpr ⟨a ++ w, hw, swapW_append_left hinc w⟩
    · intro hw
      rw [hD] at hw
      obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hw
      rcases aux_swapW_cases hinc (hnc v hv) with ⟨t, rfl, hf⟩ | ⟨u, rfl, hf⟩ | ⟨h1, h2, hf⟩
      · rw [hf] at he
        obtain rfl : t = w := List.append_cancel_left he
        exact hv
      · rw [hf] at he
        exact absurd (he ▸ List.prefix_append a u) (aux_npa hinc.1.1 hinc.1.2 w)
      · rw [hf] at he
        subst he
        exact absurd (List.prefix_append b w) h2
  · intro w
    constructor
    · intro hw
      rw [hD]
      exact Finset.mem_image.mpr ⟨b ++ w, hw, swapW_append_right hinc w⟩
    · intro hw
      rw [hD] at hw
      obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hw
      rcases aux_swapW_cases hinc (hnc v hv) with ⟨t, rfl, hf⟩ | ⟨u, rfl, hf⟩ | ⟨h1, h2, hf⟩
      · rw [hf] at he
        exact absurd (he ▸ List.prefix_append b t) (aux_npa hinc.1.2 hinc.1.1 w)
      · rw [hf] at he
        obtain rfl : u = w := List.append_cancel_left he
        exact hv
      · rw [hf] at he
        subst he
        exact absurd (List.prefix_append a w) h1
  · intro s hs ha hb hc
    rw [hD]
    exact Finset.mem_image.mpr ⟨s, hs, swapW_of_not_prefix ha hb hc⟩
  · intro s hs ha hb _
    rw [hD] at hs
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hs
    rcases aux_swapW_cases hinc (hnc v hv) with ⟨t, rfl, hf⟩ | ⟨u, rfl, hf⟩ | ⟨h1, h2, hf⟩
    · rw [hf] at he
      exact absurd (he ▸ List.prefix_append b t) hb
    · rw [hf] at he
      exact absurd (he ▸ List.prefix_append a u) ha
    · rw [hf] at he
      subst he
      exact hv

/-- The staging cone is empty again in the result: the parked cell tree has been handed on
to `b`. This is the sense in which the derived word is a transposition of the two cones and
not merely a relocation of one of them. -/
theorem swap_staging_cone_empty {x x' : Config N m} {a b c : Word N}
    (hx : x.WF) (hinc : SwapIncomp3 a b c)
    (haD : a ∈ x.D) (haμ : a ∈ x.μ) (hbD : b ∈ x.D) (hbμ : b ∈ x.μ)
    (hcμ : c ∈ x.μ) (hcD : c ∉ x.D)
    (hdepth_ac : ∀ w ∈ x.D, a <+: w → c.length + (w.length - a.length) + 1 ≤ m)
    (hdepth_ba : ∀ w ∈ x.D, b <+: w → a.length + (w.length - b.length) + 1 ≤ m)
    (hdepth_ab : ∀ w ∈ x.D, a <+: w → b.length + (w.length - a.length) + 1 ≤ m)
    (hx' : ((graft a c x).bind (graft b a)).bind (graft c b) = some x') :
    ∀ s ∈ x'.D, ¬ c <+: s := by
  obtain ⟨x'', hcomp, hD, -, -⟩ :=
    swap_three_grafts hx hinc haD haμ hbD hbμ hcμ hcD hdepth_ac hdepth_ba hdepth_ab
  have hxx : x' = x'' := Option.some.inj (hx'.symm.trans hcomp)
  subst hxx
  have hnc : ∀ v ∈ x.D, ¬ c <+: v := fun v hv hp => hcD (aux_prefix_mem' hx hv hp)
  intro s hs
  rw [hD] at hs
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hs
  rcases aux_swapW_cases hinc (hnc v hv) with ⟨t, rfl, hf⟩ | ⟨u, rfl, hf⟩ | ⟨h1, h2, hf⟩
  · rw [hf] at he
    exact he ▸ aux_npa hinc.2.2.2 hinc.2.2.1 t
  · rw [hf] at he
    exact he ▸ aux_npa hinc.2.1.2 hinc.2.1.1 u
  · rw [hf] at he
    exact he ▸ hnc v hv

/-! ### Non-vacuity of the guard bookkeeping

The concrete instances promised above are checked here rather than merely asserted, so that
`swap_three_grafts` cannot be satisfied vacuously. -/

/-- The minimal witness: `N = 3`, `m = 3`, two deployed leaf cells `[0]`, `[1]` and a free
occupied staging slot `[2]`. -/
def swapWitness : Config 3 3 := ⟨{[], [0], [1]}, {[0], [1], [2]}, ∅⟩

theorem swapWitness_wf : swapWitness.WF := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  exact Finset.disjoint_left.mpr (by decide)

/-- Every hypothesis of `swap_three_grafts` is simultaneously satisfiable: the three-graft
word is defined at `swapWitness` with `a = [0]`, `b = [1]`, `c = [2]`. -/
theorem swapWitness_defined :
    ∃ x' : Config 3 3,
      ((graft [0] [2] swapWitness).bind (graft [1] [0])).bind (graft [2] [1]) = some x' ∧
        x'.D = swapWitness.D.image (swapW [0] [1] [2]) ∧
        x'.μ = swapWitness.μ.image (swapWμ [0] [1] [2]) ∧
        x'.ζ = swapWitness.ζ.image (swapWμ [0] [1] [2]) :=
  swap_three_grafts (a := [0]) (b := [1]) (c := [2]) swapWitness_wf
    ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/-- A nondegenerate witness. On `swapWitness` both cones are single leaf cells, so the swap
happens to act as the identity on `D`; here the cone at `a = [0]` carries the child cell
`[0,1]`, and the swap genuinely moves it. -/
def swapWitness2 : Config 3 3 := ⟨{[], [0], [1], [0,1]}, {[0], [1], [2]}, ∅⟩

theorem swapWitness2_wf : swapWitness2.WF := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  exact Finset.disjoint_left.mpr (by decide)

/-- The swap moves structure: at `swapWitness2` the three-graft word is defined and carries
the child cell `[0,1]` of the cone at `[0]` over to `[1,1]` in the cone at `[1]`, so the
deployed-cell set really changes. -/
theorem swapWitness2_exchange :
    ∃ x' : Config 3 3,
      ((graft [0] [2] swapWitness2).bind (graft [1] [0])).bind (graft [2] [1]) = some x' ∧
        x'.D = ({[], [1], [0], [1,1]} : Finset (Word 3)) ∧
        x'.D ≠ swapWitness2.D := by
  obtain ⟨x', h, hD, -, -⟩ :=
    swap_three_grafts (a := [0]) (b := [1]) (c := [2]) swapWitness2_wf
      ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hD' : x'.D = ({[], [1], [0], [1,1]} : Finset (Word 3)) := by rw [hD]; decide
  exact ⟨x', h, hD', by rw [hD']; decide⟩

end Calc

end HSFN
