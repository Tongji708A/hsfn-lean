/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Calculus

/-!
# Footprints, footprint-disjoint commutation and the guard-read counterexample
(Table tab:typing footprint column, Proposition prop:commute and the paragraph
"Guard reads are load-bearing")

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

Table tab:typing charges to the *footprint* of a generator every address whose state the
generator reads (guard reads included) or writes. Proposition prop:commute says that two
generators with disjoint footprints commute as partial maps, i.e. the two composites have the
same domain and agree on it; on `Option`-valued partial maps that is exactly the equation
`(g x).bind h = (h x).bind g`. The paragraph after the proposition shows that the criterion
would be *unsound* if only written attributes were charged: `graft (a → b)` and `leave b`
write disjoint attributes, yet they do not commute, because the graft guard *reads* the
occupancy of `b`.

What this file contains.

* `fp`, the address-level footprint of each generator, transcribed from the footprint column
  of Table tab:typing. Cones are infinite as sets of words, so `fp` is a predicate on
  `Word N` rather than a `Finset`; `fpDisjoint` is disjointness of two such predicates.
* `wfp`, the *write* footprint, at the finer granularity of (address, attribute) pairs that
  the paper's "their written attributes are disjoint" argument needs, together with
  `wfp_sound`, which pins `wfp` down by requiring that a generator change no membership bit
  outside it (this is what stops `wfp` from being made small by fiat).
* `book_comm`, Proposition prop:commute for the six bookkeeping letters, together with
  `book_comm_witness`, a concrete pair of footprint-disjoint letters that are both applicable
  at a well-formed configuration (so the hypothesis of `book_comm` is satisfiable and the
  conclusion is not an equality of two undefined composites).
* `ceX`, `ceA`, `ceB` and the theorems `ce_leave_then_graft`, `ce_graft_then_leave`,
  `ce_noncommute`, `write_footprint_criterion_unsound`: a concrete `N = 3`, `m = 3` witness
  that the write-set-only criterion is unsound.

What this file does NOT formalize.

* The `permute` letter of Table tab:typing is absent from `Hsfnlean.Calculus`, hence absent
  here; its footprint row `cone(w)` is not modelled.
* Proposition prop:commute is stated here only for pairs of the six bookkeeping letters.
  Pairs involving `graft` (graft/graft and graft/bookkeeping) are not stated; about `graft`
  this file proves only the negative result of the "guard reads" paragraph.
* `fp` is transcribed from the footprint column of Table tab:typing rather than computed
  from the guards. For the six bookkeeping letters the transcription is nevertheless
  justified inside the proof of `book_comm`: `aux_guard_mono` shows the guard depends only on
  the restriction of the configuration to `fp`, and `aux_act_agree` shows the effect changes
  no membership bit outside `fp`. For `graft` no such completeness statement is proved here;
  the `graft` row of `fp` is used only negatively, in `fp_graft_leave_not_disjoint`.
  `wfp_sound` supplies the corresponding write-side guarantee for all seven letters.
* "The stranded arriving subtree is a protocol-layer concern" is prose about the execution
  model and is not a formal claim; we only exhibit that the second order is defined.
-/

namespace HSFN

namespace Calc

variable {N m : ℕ}

/-! ## Generators as letters -/

/-- The seven generators of `Hsfnlean.Calculus` as a datatype of letters (the eighth generator
of Table tab:typing, `permute`, is out of scope). -/
inductive Gen (N : ℕ) where
  | spawn (a : Word N)
  | retract (a : Word N)
  | join (s : Word N)
  | leave (s : Word N)
  | disable (s : Word N)
  | enable (s : Word N)
  | graft (a b : Word N)

/-- The partial map a letter denotes. -/
def Gen.run : Gen N → Config N m → Option (Config N m)
  | .spawn a => _root_.HSFN.Calc.spawn a
  | .retract a => _root_.HSFN.Calc.retract a
  | .join s => _root_.HSFN.Calc.join s
  | .leave s => _root_.HSFN.Calc.leave s
  | .disable s => _root_.HSFN.Calc.disable s
  | .enable s => _root_.HSFN.Calc.enable s
  | .graft a b => _root_.HSFN.Calc.graft a b

/-- The six bookkeeping letters, i.e. the generators other than `graft` (and `permute`):
they change `D`, `μ`, `ζ` without relocating any address. -/
inductive Book (N : ℕ) where
  | spawn (a : Word N)
  | retract (a : Word N)
  | join (s : Word N)
  | leave (s : Word N)
  | disable (s : Word N)
  | enable (s : Word N)

/-- A bookkeeping letter read as a generator. -/
def Book.toGen : Book N → Gen N
  | .spawn a => .spawn a
  | .retract a => .retract a
  | .join s => .join s
  | .leave s => .leave s
  | .disable s => .disable s
  | .enable s => .enable s

/-- The partial map a bookkeeping letter denotes. -/
def Book.run (g : Book N) (x : Config N m) : Option (Config N m) := Gen.run g.toGen x

/-! ## Footprints (Table tab:typing, footprint column)

`cone(a) = {a w : w ∈ Σ_N^*}` is infinite as a set of words, so the footprint is a predicate
on `Word N`. `List.IsPrefix` (`a <+: w`) is membership of `w` in `cone(a)`, and
`List.dropLast` is the paper's `pre`. -/

/-- The footprint of a generator: every address whose state the generator reads (guards
included) or writes, exactly as the footprint column of Table tab:typing lists it.

* `spawn a`  : `{pre a, a} ∪ C(a)`
* `retract a`: `{a} ∪ C(a)`
* `join s`   : `{pre s, s}`
* `leave s`  : `{s}`
* `disable s`: `{pre s, s}`
* `enable s` : `{s}`
* `graft a b`: `cone a ∪ cone b ∪ {pre b}` -/
def fp : Gen N → Word N → Prop
  | .spawn a, w => w = a.dropLast ∨ w = a ∨ w ∈ cellW a
  | .retract a, w => w = a ∨ w ∈ cellW a
  | .join s, w => w = s.dropLast ∨ w = s
  | .leave s, w => w = s
  | .disable s, w => w = s.dropLast ∨ w = s
  | .enable s, w => w = s
  | .graft a b, w => a <+: w ∨ b <+: w ∨ w = b.dropLast

/-- Two letters have disjoint footprints. -/
def fpDisjoint (g h : Gen N) : Prop := ∀ w : Word N, fp g w → fp h w → False

theorem fpDisjoint_symm {g h : Gen N} (hgh : fpDisjoint g h) : fpDisjoint h g :=
  fun w hw hw' => hgh w hw' hw

/-! ## Proposition prop:commute for the bookkeeping letters

"`ω₁ ω₂ = ω₂ ω₁` as partial maps, in that the two composites have the same domain and agree
on it": for `Option`-valued partial maps this is literally equality of the two composites,
since `(g x).bind h = none` says the composite is undefined at `x`. -/

/-! ### Slot membership, re-derived

`Hsfnlean.Calculus` keeps its analogues of the next two lemmas `private`, so they are
re-proved here. -/

private theorem aux_cellW_iff {v w : Word N} : v ∈ cellW w ↔ v ≠ [] ∧ v.dropLast = w := by
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨d, _, rfl⟩
    simp
  · rintro ⟨hv, rfl⟩
    exact Finset.mem_image.mpr
      ⟨v.getLast hv, Finset.mem_univ _, List.dropLast_append_getLast hv⟩

private theorem aux_Sl_iff {x : Config N m} {w : Word N} :
    w ∈ x.Sl ↔ w ≠ [] ∧ w.dropLast ∈ x.D := by
  simp only [Config.Sl, Finset.mem_biUnion, aux_cellW_iff]
  aesop

/-! ### Guard locality and effect locality (the two facts the paper's proof uses) -/

/-- The guard of a bookkeeping letter, split off from `Hsfnlean.Calculus`'s `if`. -/
private def aux_guard : Book N → Config N m → Prop
  | .spawn a, x => a ∈ x.Sl ∧ a ∉ x.D ∧ a ∉ x.ζ ∧ a.length + 1 ≤ m
  | .retract a, x => a ∈ x.D ∧ a ≠ [] ∧ Disjoint (cellW a) (x.D ∪ x.μ ∪ x.ζ)
  | .join s, x => s ∈ x.Sl ∧ s ∉ x.μ ∧ s ∉ x.ζ
  | .leave s, x => s ∈ x.μ
  | .disable s, x => s ∈ x.Sl ∧ s ∉ x.μ ∧ s ∉ x.D ∧ s ∉ x.ζ
  | .enable s, x => s ∈ x.ζ

/-- The effect of a bookkeeping letter, split off from `Hsfnlean.Calculus`'s `if`. -/
private def aux_act : Book N → Config N m → Config N m
  | .spawn a, x => ⟨insert a x.D, x.μ, x.ζ⟩
  | .retract a, x => ⟨x.D.erase a, x.μ, x.ζ⟩
  | .join s, x => ⟨x.D, insert s x.μ, x.ζ⟩
  | .leave s, x => ⟨x.D, x.μ.erase s, x.ζ⟩
  | .disable s, x => ⟨x.D, x.μ, insert s x.ζ⟩
  | .enable s, x => ⟨x.D, x.μ, x.ζ.erase s⟩

/-- The single address a bookkeeping letter is parameterized by. -/
private def aux_site : Book N → Word N
  | .spawn a => a
  | .retract a => a
  | .join s => s
  | .leave s => s
  | .disable s => s
  | .enable s => s

private theorem aux_site_mem_fp (g : Book N) : fp g.toGen (aux_site g) := by
  cases g <;> simp [aux_site, fp, Book.toGen]

private theorem aux_run_pos (g : Book N) (x : Config N m) (hg : aux_guard g x) :
    g.run x = some (aux_act g x) := by
  cases g <;> simp only [aux_guard] at hg <;>
    simp only [Book.run, Book.toGen, Gen.run, aux_act, spawn, retract, join, leave, disable,
      enable, if_pos hg]

private theorem aux_run_neg (g : Book N) (x : Config N m) (hg : ¬ aux_guard g x) :
    g.run x = none := by
  cases g <;> simp only [aux_guard] at hg <;>
    simp only [Book.run, Book.toGen, Gen.run, spawn, retract, join, leave, disable,
      enable, if_neg hg]

/-- Two configurations agree, address by address, on all three membership bits, over a set
`S` of addresses. -/
private def aux_agree (S : Word N → Prop) (x y : Config N m) : Prop :=
  ∀ w, S w → ((w ∈ x.D ↔ w ∈ y.D) ∧ (w ∈ x.μ ↔ w ∈ y.μ) ∧ (w ∈ x.ζ ↔ w ∈ y.ζ))

private theorem aux_agree_symm {S : Word N → Prop} {x y : Config N m} (h : aux_agree S x y) :
    aux_agree S y x :=
  fun w hw => ⟨(h w hw).1.symm, (h w hw).2.1.symm, (h w hw).2.2.symm⟩

/-- **Effect locality**: a bookkeeping letter changes no membership bit outside its
footprint. -/
private theorem aux_act_agree (g : Book N) (x : Config N m) :
    aux_agree (fun w => ¬ fp g.toGen w) (aux_act g x) x := by
  intro w hw
  cases g <;>
    simp_all [aux_act, fp, Book.toGen, Finset.mem_insert, Finset.mem_erase]

/-- **Guard locality**: applicability of a bookkeeping letter depends only on the restriction
of the configuration to its footprint. -/
private theorem aux_guard_mono (g : Book N) {x y : Config N m}
    (hag : aux_agree (fp g.toGen) x y) (hg : aux_guard g x) : aux_guard g y := by
  cases g with
  | spawn a =>
      obtain ⟨h1, h2, h3, h4⟩ := hg
      have ka := hag a (Or.inr (Or.inl rfl))
      have kp := hag a.dropLast (Or.inl rfl)
      obtain ⟨hne, hd⟩ := aux_Sl_iff.mp h1
      exact ⟨aux_Sl_iff.mpr ⟨hne, kp.1.mp hd⟩, fun hc => h2 (ka.1.mpr hc),
        fun hc => h3 (ka.2.2.mpr hc), h4⟩
  | retract a =>
      obtain ⟨h1, h2, h3⟩ := hg
      refine ⟨(hag a (Or.inl rfl)).1.mp h1, h2, ?_⟩
      rw [Finset.disjoint_left] at h3 ⊢
      intro w hw hm
      refine h3 hw ?_
      have k := hag w (Or.inr hw)
      simp only [Finset.mem_union] at hm ⊢
      tauto
  | join s =>
      obtain ⟨h1, h2, h3⟩ := hg
      have ks := hag s (Or.inr rfl)
      have kp := hag s.dropLast (Or.inl rfl)
      obtain ⟨hne, hd⟩ := aux_Sl_iff.mp h1
      exact ⟨aux_Sl_iff.mpr ⟨hne, kp.1.mp hd⟩, fun hc => h2 (ks.2.1.mpr hc),
        fun hc => h3 (ks.2.2.mpr hc)⟩
  | leave s => exact (hag s rfl).2.1.mp hg
  | disable s =>
      obtain ⟨h1, h2, h3, h4⟩ := hg
      have ks := hag s (Or.inr rfl)
      have kp := hag s.dropLast (Or.inl rfl)
      obtain ⟨hne, hd⟩ := aux_Sl_iff.mp h1
      exact ⟨aux_Sl_iff.mpr ⟨hne, kp.1.mp hd⟩, fun hc => h2 (ks.2.1.mpr hc),
        fun hc => h3 (ks.1.mpr hc), fun hc => h4 (ks.2.2.mpr hc)⟩
  | enable s => exact (hag s rfl).2.2.mp hg

/-- Guard stability: a footprint-disjoint letter does not change another letter's guard. -/
private theorem aux_guard_stable {g h : Book N} (hgh : fpDisjoint g.toGen h.toGen)
    (x : Config N m) : aux_guard h (aux_act g x) ↔ aux_guard h x := by
  have hag : aux_agree (fp h.toGen) (aux_act g x) x :=
    fun w hw => aux_act_agree g x w (fun hc => hgh w hc hw)
  exact ⟨aux_guard_mono h hag, aux_guard_mono h (aux_agree_symm hag)⟩

/-- The effects of two letters acting at distinct addresses commute. -/
private theorem aux_act_comm {g h : Book N} (hs : aux_site g ≠ aux_site h) (x : Config N m) :
    aux_act h (aux_act g x) = aux_act g (aux_act h x) := by
  have hs' := Ne.symm hs
  cases g <;> cases h <;>
    simp_all [aux_act, aux_site, Finset.insert_comm, Finset.erase_right_comm,
      Finset.erase_insert_of_ne]

/-- **Proposition prop:commute** (six bookkeeping letters). Two bookkeeping generators whose
footprints (Table tab:typing, guard reads included) are disjoint commute as partial maps: the
two composites are defined on the same configurations and agree there. No well-formedness
hypothesis is needed: guard locality and effect locality hold on every `Config`. -/
theorem book_comm {x : Config N m} {g h : Book N}
    (hgh : fpDisjoint g.toGen h.toGen) :
    (g.run x).bind (Book.run h) = (h.run x).bind (Book.run g) := by
  have hsite : aux_site g ≠ aux_site h := by
    intro he
    refine hgh (aux_site h) ?_ (aux_site_mem_fp h)
    rw [← he]
    exact aux_site_mem_fp g
  by_cases hg : aux_guard g x
  · by_cases hh : aux_guard h x
    · rw [aux_run_pos g x hg, aux_run_pos h x hh]
      simp only [Option.bind]
      rw [aux_run_pos h _ ((aux_guard_stable hgh x).mpr hh),
        aux_run_pos g _ ((aux_guard_stable (fpDisjoint_symm hgh) x).mpr hg),
        aux_act_comm hsite x]
    · rw [aux_run_pos g x hg, aux_run_neg h x hh]
      simp only [Option.bind]
      exact aux_run_neg h _ (fun hc => hh ((aux_guard_stable hgh x).mp hc))
  · by_cases hh : aux_guard h x
    · rw [aux_run_pos h x hh, aux_run_neg g x hg]
      simp only [Option.bind]
      exact (aux_run_neg g _
        (fun hc => hg ((aux_guard_stable (fpDisjoint_symm hgh) x).mp hc))).symm
    · rw [aux_run_neg g x hg, aux_run_neg h x hh]
      rfl

/-! ## Written attributes

The "Guard reads are load-bearing" paragraph compares footprints with *written attributes*:
the graft "rewrites cell structure and transported bits inside the two cones and never touches
`μ(b)`", while the leave "rewrites exactly `μ(b)`". Written attributes are therefore finer
than addresses — the graft does write the `D`-bit of `b` — so the write footprint is a
predicate on pairs (address, attribute). -/

/-- The three membership bits a configuration stores at an address. -/
inductive Attr where
  | dep
  | occ
  | dec
  deriving DecidableEq

/-- The bit stored at address `w` under attribute `t`. -/
def Config.bit (x : Config N m) (w : Word N) : Attr → Prop
  | .dep => w ∈ x.D
  | .occ => w ∈ x.μ
  | .dec => w ∈ x.ζ

/-- The *write* footprint: the (address, attribute) pairs whose membership bit the effect
column of Table tab:typing can change. For `graft (a → b)` the substitution rewrites the
`D`-bits throughout `cone a ∪ cone b` and transports the occupancy and decommission bits of
the slots *strictly* below `a` to those strictly below `b`; the anchors `a` and `b` keep their
own occupancy and decommission bits, which is the disjointness the paper's counterexample
turns on. -/
def wfp : Gen N → Word N → Attr → Prop
  | .spawn a, w, t => w = a ∧ t = Attr.dep
  | .retract a, w, t => w = a ∧ t = Attr.dep
  | .join s, w, t => w = s ∧ t = Attr.occ
  | .leave s, w, t => w = s ∧ t = Attr.occ
  | .disable s, w, t => w = s ∧ t = Attr.dec
  | .enable s, w, t => w = s ∧ t = Attr.dec
  | .graft a b, w, t =>
      ((a <+: w ∨ b <+: w) ∧ t = Attr.dep) ∨
        (((a <+: w ∧ w ≠ a) ∨ (b <+: w ∧ w ≠ b)) ∧ (t = Attr.occ ∨ t = Attr.dec))

/-! ### Prefix substitution, re-derived

`Hsfnlean.Calculus` keeps its `subst` lemmas `private`; the four facts needed below are
re-proved here. -/

private theorem aux_subst_append (a b s : Word N) : subst false a b (a ++ s) = b ++ s := by
  simp [subst]

private theorem aux_append_ne {b s : Word N} (hs : s ≠ []) : b ++ s ≠ b := by
  intro he
  have h1 := congrArg List.length he
  simp only [List.length_append] at h1
  exact hs (List.eq_nil_of_length_eq_zero (by omega))

private theorem aux_subst_append_strict (a b : Word N) {s : Word N} (hs : s ≠ []) :
    subst true a b (a ++ s) = b ++ s := by
  have hn : a ≠ a ++ s := fun he => aux_append_ne hs he.symm
  simp [subst, hn]

private theorem aux_subst_id (strict : Bool) {a b w : Word N} (hw : ¬ a <+: w) :
    subst strict a b w = w := by
  simp [subst, hw]

private theorem aux_subst_true_id {a b w : Word N} (hw : ¬ (a <+: w ∧ a ≠ w)) :
    subst true a b w = w := by
  simp only [subst, Bool.true_eq_false, false_or, if_neg hw]

/-- `wfp` is a genuine over-approximation of what a generator writes: outside it, every
membership bit is unchanged. This is what forbids shrinking `wfp` by fiat. -/
theorem wfp_sound {x y : Config N m} {g : Gen N} (h : g.run x = some y)
    {w : Word N} {t : Attr} (hw : ¬ wfp g w t) : (y.bit w t ↔ x.bit w t) := by
  cases g with
  | spawn a =>
      simp only [Gen.run, spawn] at h
      split at h
      · cases h
        cases t <;> simp_all [Config.bit, wfp, Finset.mem_insert]
      · cases h
  | retract a =>
      simp only [Gen.run, retract] at h
      split at h
      · cases h
        cases t <;> simp_all [Config.bit, wfp, Finset.mem_erase]
      · cases h
  | join s =>
      simp only [Gen.run, join] at h
      split at h
      · cases h
        cases t <;> simp_all [Config.bit, wfp, Finset.mem_insert]
      · cases h
  | leave s =>
      simp only [Gen.run, leave] at h
      split at h
      · cases h
        cases t <;> simp_all [Config.bit, wfp, Finset.mem_erase]
      · cases h
  | disable s =>
      simp only [Gen.run, disable] at h
      split at h
      · cases h
        cases t <;> simp_all [Config.bit, wfp, Finset.mem_insert]
      · cases h
  | enable s =>
      simp only [Gen.run, enable] at h
      split at h
      · cases h
        cases t <;> simp_all [Config.bit, wfp, Finset.mem_erase]
      · cases h
  | graft a b =>
      simp only [Gen.run, graft] at h
      split at h
      · cases h
        cases t
        · have hna : ¬ a <+: w := fun hp => hw (Or.inl ⟨Or.inl hp, rfl⟩)
          have hnb : ¬ b <+: w := fun hp => hw (Or.inl ⟨Or.inr hp, rfl⟩)
          simp only [Config.bit]
          constructor
          · intro hm
            obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hm
            by_cases hp : a <+: v
            · obtain ⟨s, rfl⟩ := hp
              rw [aux_subst_append] at he
              exact absurd (he ▸ List.prefix_append b s) hnb
            · rw [aux_subst_id false hp] at he
              exact he ▸ hv
          · intro hm
            exact Finset.mem_image.mpr ⟨w, hm, aux_subst_id false hna⟩
        · have hna : ¬ (a <+: w ∧ w ≠ a) := fun hp => hw (Or.inr ⟨Or.inl hp, Or.inl rfl⟩)
          have hnb : ¬ (b <+: w ∧ w ≠ b) := fun hp => hw (Or.inr ⟨Or.inr hp, Or.inl rfl⟩)
          simp only [Config.bit]
          constructor
          · intro hm
            obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hm
            by_cases hp : a <+: v ∧ a ≠ v
            · obtain ⟨hp1, hp2⟩ := hp
              obtain ⟨s, rfl⟩ := hp1
              have hs : s ≠ [] := fun hnil => hp2 (by simp [hnil])
              rw [aux_subst_append_strict a b hs] at he
              exact absurd ⟨he ▸ List.prefix_append b s, he ▸ aux_append_ne hs⟩ hnb
            · rw [aux_subst_true_id hp] at he
              exact he ▸ hv
          · intro hm
            exact Finset.mem_image.mpr
              ⟨w, hm, aux_subst_true_id (fun hc => hna ⟨hc.1, Ne.symm hc.2⟩)⟩
        · have hna : ¬ (a <+: w ∧ w ≠ a) := fun hp => hw (Or.inr ⟨Or.inl hp, Or.inr rfl⟩)
          have hnb : ¬ (b <+: w ∧ w ≠ b) := fun hp => hw (Or.inr ⟨Or.inr hp, Or.inr rfl⟩)
          simp only [Config.bit]
          constructor
          · intro hm
            obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hm
            by_cases hp : a <+: v ∧ a ≠ v
            · obtain ⟨hp1, hp2⟩ := hp
              obtain ⟨s, rfl⟩ := hp1
              have hs : s ≠ [] := fun hnil => hp2 (by simp [hnil])
              rw [aux_subst_append_strict a b hs] at he
              exact absurd ⟨he ▸ List.prefix_append b s, he ▸ aux_append_ne hs⟩ hnb
            · rw [aux_subst_true_id hp] at he
              exact he ▸ hv
          · intro hm
            exact Finset.mem_image.mpr
              ⟨w, hm, aux_subst_true_id (fun hc => hna ⟨hc.1, Ne.symm hc.2⟩)⟩
      · cases h

/-- Two letters write disjoint attributes. -/
def wfpDisjoint (g h : Gen N) : Prop := ∀ (w : Word N) (t : Attr), wfp g w t → wfp h w t → False

/-! ## Guard reads are load-bearing

`graft (a → b)` and `leave b` write disjoint attributes (`wfp_graft_leave_disjoint`) but have
overlapping footprints (`fp_graft_leave_not_disjoint`, the overlap being `b` itself, read by
the graft guard `b ∈ μ`), and they do not commute (`ce_noncommute`). -/

/-- The written attributes of `graft (a → b)` and of `leave b` are disjoint: the graft
never touches `μ(b)`. The hypothesis `¬ a <+: b` is the guard `a ⋠ b` of Table tab:typing
("the target may not lie in the moved cone"), and it is needed, not cosmetic: were `b`
strictly below `a`, the graft would *transport* the occupancy bit of `b` and the two
written attribute sets would overlap at `(b, occ)` after all. It holds at the witness
below, since `ceA = 0` is not a prefix of `ceB = 10`. -/
theorem wfp_graft_leave_disjoint {a b : Word N} (hab : ¬ a <+: b) :
    wfpDisjoint (Gen.graft a b) (Gen.leave b) := by
  rintro w t hg ⟨rfl, rfl⟩
  rcases hg with ⟨-, hd⟩ | ⟨hc, -⟩
  · exact absurd hd (by simp)
  · rcases hc with ⟨hp, -⟩ | ⟨-, hne⟩
    · exact hab hp
    · exact hne rfl

/-- The footprints of `graft (a → b)` and of `leave b` are never disjoint: the address `b`
lies in both, being read by the graft guard `b ∈ μ`. -/
theorem fp_graft_leave_not_disjoint (a b : Word N) :
    ¬ fpDisjoint (Gen.graft a b) (Gen.leave b) :=
  fun hd => hd b (Or.inr (Or.inl (List.prefix_refl b))) rfl

/-! ### The concrete counterexample, `N = 3`, `m = 3`

`D = {ε, 0, 1}` (prefix-closed, all deployed cells of depth `≤ 1`), so the slots are
`{0,1,2} ∪ {00,01,02} ∪ {10,11,12}`. Both `a = 0` (a deployed cell root) and `b = 10`
(a cell-free slot whose parent cell `1` is deployed) are occupied, and nothing is
decommissioned. `graft (0 → 10)` is applicable at `x`: `10 ∉ D`, `pre(10) = 1 ∈ D`,
`0` is not a prefix of `10`, and the depth fit holds since the only deployed cell in
`cone(0)` is `0` itself, giving `|10| + 0 + 1 = 3 ≤ m`. -/

/-- The witness configuration `({ε, 0, 1}, {0, 10}, ∅)` of `F(3,3)`. -/
def ceX : Config 3 3 := ⟨{[], [0], [1]}, {[0], [1, 0]}, ∅⟩

/-- The moved cell root `a = 0`. -/
def ceA : Word 3 := [0]

/-- The target site `b = 10`, an occupied, cell-free slot. -/
def ceB : Word 3 := [1, 0]

theorem ce_wf : (ceX : Config 3 3).WF := by
  unfold Config.WF
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  simp [ceX]

/-- **`book_comm` is not vacuous.** Its hypothesis is satisfiable by two letters that are
simultaneously applicable at a well-formed configuration: `join 1` has footprint `{ε, 1}`,
`leave 0` has footprint `{0}`, these are disjoint, and at `ceX` both composites are defined
(so the equation of `book_comm` is not an equality of two `none`s). -/
theorem book_comm_witness :
    fpDisjoint (Book.join ([1] : Word 3)).toGen (Book.leave ([0] : Word 3)).toGen ∧
      ((Book.join ([1] : Word 3)).run (ceX : Config 3 3)).bind
        (Book.run (Book.leave ([0] : Word 3))) ≠ none := by
  constructor
  · intro w h1 h2
    simp only [Book.toGen, fp] at h1 h2
    subst h2
    revert h1
    decide
  · have h1 : (Book.join ([1] : Word 3)).run (ceX : Config 3 3)
        = some ⟨ceX.D, insert [1] ceX.μ, ceX.ζ⟩ := by
      simp only [Book.run, Book.toGen, Gen.run, join]
      rw [if_pos (by decide)]
    rw [h1]
    simp only [Option.bind, Book.run, Book.toGen, Gen.run, leave]
    rw [if_pos (by decide)]
    exact Option.some_ne_none _

/-- `graft (a → b)` alone is applicable at the witness configuration. -/
theorem ce_graft_defined : graft ceA ceB ceX ≠ none := by
  unfold graft
  split
  · exact Option.some_ne_none _
  · rename_i hc
    exact absurd (by decide) hc

/-- `leave b` alone is applicable at the witness configuration. -/
theorem ce_leave_defined : leave ceB ceX ≠ none := by
  unfold leave
  split
  · exact Option.some_ne_none _
  · rename_i hc
    exact absurd (by decide) hc

/-- **Guard reads are load-bearing, first half.** After `leave b` the graft guard `b ∈ μ`
has been destroyed, so the composite `graft (a → b) ∘ leave b` is undefined. -/
theorem ce_leave_then_graft : (leave ceB ceX).bind (graft ceA ceB) = none := by
  have h1 : leave ceB ceX = some ⟨ceX.D, ceX.μ.erase ceB, ceX.ζ⟩ := by
    unfold leave
    split
    · rfl
    · rename_i hc
      exact absurd (by decide) hc
  rw [h1]
  simp only [Option.bind]
  unfold graft
  split
  · rename_i hc
    exact absurd hc (by decide)
  · rfl

/-- **Guard reads are load-bearing, second half.** The other order is defined: the graft
arrives first and the departure then strands the arriving subtree on a vacated anchor. -/
theorem ce_graft_then_leave : (graft ceA ceB ceX).bind (leave ceB) ≠ none := by
  have h1 : graft ceA ceB ceX = some ⟨ceX.D.image (subst false ceA ceB),
      ceX.μ.image (subst true ceA ceB), ceX.ζ.image (subst true ceA ceB)⟩ := by
    unfold graft
    split
    · rfl
    · rename_i hc
      exact absurd (by decide) hc
  rw [h1]
  simp only [Option.bind]
  unfold leave
  split
  · exact Option.some_ne_none _
  · rename_i hc
    exact absurd (by decide) hc

/-- The two composites differ, so `graft (a → b)` and `leave b` do not commute as partial
maps: they do not even have the same domain. -/
theorem ce_noncommute :
    (leave ceB ceX).bind (graft ceA ceB) ≠ (graft ceA ceB ceX).bind (leave ceB) := by
  intro h
  apply ce_graft_then_leave
  rw [← h]
  exact ce_leave_then_graft

/-- **A write-set-only commutation criterion is unsound.** There are a well-formed
configuration and two generators with disjoint *written* attributes whose composites in the
two orders differ. Hence the footprint of Table tab:typing must charge guard reads, as
Proposition prop:commute requires. -/
theorem write_footprint_criterion_unsound :
    ∃ (x : Config 3 3) (a b : Word 3),
      x.WF ∧ wfpDisjoint (Gen.graft a b) (Gen.leave b) ∧
        (leave b x).bind (graft a b) ≠ (graft a b x).bind (leave b) :=
  ⟨ceX, ceA, ceB, ce_wf, wfp_graft_leave_disjoint (by decide), ce_noncommute⟩


end Calc

end HSFN
