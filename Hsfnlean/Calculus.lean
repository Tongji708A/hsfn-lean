/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Basic

/-!
# The operations calculus: configurations, generators, invariants, inverses
(Definition def:calc-state, Table tab:typing, Theorem thm:rep-tree(i), Theorem thm:graft-iso(ii),
Proposition prop:commute for the bookkeeping letters)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
A configuration is a triple `(D, μ, ζ)` of finite word sets: deployed cells (prefix-closed,
containing the virtual root `[]`, of length at most `m-1`), occupied slots and decommissioned
slots. The generators are partial maps, encoded as `Option`-valued functions whose guards are
the preconditions of Table tab:typing. This module proves that every generator preserves
well-formedness, that the generators pair into exact inverses, that the two-clause adjacency
law is suffix-covariant (the core of the graft isomorphism), and that footprint-disjoint
bookkeeping letters commute. The statements below are frozen; only the proofs are to be
supplied.
-/

namespace HSFN

namespace Calc

variable {N m : ℕ}

/-- Words over the digit alphabet. -/
abbrev Word (N : ℕ) := List (Fin N)

/-- The `N` member slots of the cell spawned at `w`. -/
def cellW (w : Word N) : Finset (Word N) := Finset.univ.image fun d : Fin N => w ++ [d]

/-- A configuration `(D, μ, ζ)`. -/
structure Config (N m : ℕ) where
  D : Finset (Word N)
  μ : Finset (Word N)
  ζ : Finset (Word N)

namespace Config

/-- The slot set `Sl(x) = ⋃_{w ∈ D} cell(w)`. -/
def Sl (x : Config N m) : Finset (Word N) := x.D.biUnion cellW

/-- Well-formedness: `[] ∈ D`, deployed cells fit below tier `m`, `D` is prefix-closed,
`μ, ζ ⊆ Sl`, and `ζ` is disjoint from `μ ∪ D`. -/
def WF (x : Config N m) : Prop :=
  [] ∈ x.D ∧ (∀ w ∈ x.D, w.length + 1 ≤ m) ∧ (∀ w ∈ x.D, w ≠ [] → w.dropLast ∈ x.D) ∧
    x.μ ⊆ x.Sl ∧ x.ζ ⊆ x.Sl ∧ Disjoint x.ζ (x.μ ∪ x.D)

end Config

open Config

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
  have := congrArg List.length he
  have := List.length_pos_of_ne_nil hw
  simp only [List.length_dropLast] at *
  omega

/-- The seed configuration `({[]}, ∅, ∅)`. -/
def seed (N m : ℕ) : Config N m := ⟨{[]}, ∅, ∅⟩

theorem seed_wf (hm : 1 ≤ m) : (seed N m).WF := by
  simpa [WF, seed] using (show 0 < m by omega)

/-- `spawn a`: deploy the cell at the slot `a` (vacant of cell, enabled, room below). -/
def spawn (a : Word N) (x : Config N m) : Option (Config N m) :=
  if a ∈ x.Sl ∧ a ∉ x.D ∧ a ∉ x.ζ ∧ a.length + 1 ≤ m then some ⟨insert a x.D, x.μ, x.ζ⟩ else none

/-- `retract a`: remove the cell at `a` when it is empty, childless and undecommissioned. -/
def retract (a : Word N) (x : Config N m) : Option (Config N m) :=
  if a ∈ x.D ∧ a ≠ [] ∧ Disjoint (cellW a) (x.D ∪ x.μ ∪ x.ζ) then some ⟨x.D.erase a, x.μ, x.ζ⟩
  else none

/-- `join s`: a participant occupies the vacant enabled slot `s`. -/
def join (s : Word N) (x : Config N m) : Option (Config N m) :=
  if s ∈ x.Sl ∧ s ∉ x.μ ∧ s ∉ x.ζ then some ⟨x.D, insert s x.μ, x.ζ⟩ else none

/-- `leave s`: the participant at `s` departs. -/
def leave (s : Word N) (x : Config N m) : Option (Config N m) :=
  if s ∈ x.μ then some ⟨x.D, x.μ.erase s, x.ζ⟩ else none

/-- `disable s`: decommission a vacant, childless, enabled slot. -/
def disable (s : Word N) (x : Config N m) : Option (Config N m) :=
  if s ∈ x.Sl ∧ s ∉ x.μ ∧ s ∉ x.D ∧ s ∉ x.ζ then some ⟨x.D, x.μ, insert s x.ζ⟩ else none

/-- `enable s`: re-enable a decommissioned slot. -/
def enable (s : Word N) (x : Config N m) : Option (Config N m) :=
  if s ∈ x.ζ then some ⟨x.D, x.μ, x.ζ.erase s⟩ else none

/-- Prefix substitution `a ↦ b` on the words having `a` as a prefix (strict when `strict = true`). -/
def subst (strict : Bool) (a b w : Word N) : Word N :=
  if a <+: w ∧ (strict = false ∨ a ≠ w) then b ++ w.drop a.length else w

/-- `graft a b`: move the cell tree rooted at `a` to `b` (Table tab:typing). The deployed cells
`a w` become `b w` (including `a` itself); occupancy and decommission bits move for the slots
strictly below `a`, while the slot `a` stays behind. -/
def graft (a b : Word N) (x : Config N m) : Option (Config N m) :=
  if a ∈ x.D ∧ a ∈ x.μ ∧ b ∈ x.μ ∧ b ∉ x.D ∧ b ≠ [] ∧ b.dropLast ∈ x.D ∧ ¬ a <+: b ∧
      (∀ w ∈ x.D, a <+: w → b.length + (w.length - a.length) + 1 ≤ m)
  then some ⟨x.D.image (subst false a b), x.μ.image (subst true a b), x.ζ.image (subst true a b)⟩
  else none

/-! ## Well-formedness is an invariant (Definition def:calc-state, reading note one) -/

theorem wf_spawn {x y : Config N m} {a : Word N} (hx : x.WF) (h : spawn a x = some y) : y.WF := by
  unfold spawn at h
  split at h
  · rename_i hg
    cases h
    have ha := aux_mem_Sl.mp hg.1
    rcases hx with ⟨hr, hl, hp, hm, hz, hd⟩
    simp only [WF, Finset.mem_insert, Sl, Finset.biUnion_insert]
    refine ⟨Or.inr hr, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw
      rcases hw with rfl | hw
      · exact hg.2.2.2
      · exact hl w hw
    · intro w hw hn
      rcases hw with rfl | hw
      · exact Or.inr ha.2
      · exact Or.inr (hp w hw hn)
    · exact hm.trans Finset.subset_union_right
    · exact hz.trans Finset.subset_union_right
    · rw [Finset.disjoint_left] at hd ⊢
      simp only [Finset.mem_union, Finset.mem_insert] at hd ⊢
      aesop
  · cases h

theorem wf_retract {x y : Config N m} {a : Word N} (hx : x.WF) (h : retract a x = some y) : y.WF := by
  unfold retract at h
  split at h
  · rename_i hg
    cases h
    rcases hx with ⟨hr, hl, hp, hm, hz, hd⟩
    have hc := Finset.disjoint_left.mp hg.2.2
    refine ⟨Finset.mem_erase.mpr ⟨Ne.symm hg.2.1, hr⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw
      exact hl w (Finset.mem_of_mem_erase hw)
    · intro w hw hn
      refine Finset.mem_erase.mpr ⟨?_, hp w (Finset.mem_of_mem_erase hw) hn⟩
      intro he
      exact hc (aux_mem_cellW.mpr ⟨hn, he⟩)
        (by simp [Finset.mem_of_mem_erase hw])
    · intro w hw
      have hs := aux_mem_Sl.mp (hm hw)
      refine aux_mem_Sl.mpr ⟨hs.1, Finset.mem_erase.mpr ⟨?_, hs.2⟩⟩
      intro he
      exact hc (aux_mem_cellW.mpr ⟨hs.1, he⟩) (by simp [hw])
    · intro w hw
      have hs := aux_mem_Sl.mp (hz hw)
      refine aux_mem_Sl.mpr ⟨hs.1, Finset.mem_erase.mpr ⟨?_, hs.2⟩⟩
      intro he
      exact hc (aux_mem_cellW.mpr ⟨hs.1, he⟩) (by simp [hw])
    · exact hd.mono_right (Finset.union_subset_union_right (Finset.erase_subset _ _))
  · cases h

theorem wf_join {x y : Config N m} {s : Word N} (hx : x.WF) (h : join s x = some y) : y.WF := by
  unfold join at h
  split at h
  · rename_i hg
    cases h
    rcases hx with ⟨hr, hl, hp, hm, hz, hd⟩
    refine ⟨hr, hl, hp, Finset.insert_subset hg.1 hm, hz, ?_⟩
    simpa only [Finset.insert_union, Finset.disjoint_insert_right] using ⟨hg.2.2, hd⟩
  · cases h

theorem wf_leave {x y : Config N m} {s : Word N} (hx : x.WF) (h : leave s x = some y) : y.WF := by
  unfold leave at h
  split at h
  · cases h
    rcases hx with ⟨hr, hl, hp, hm, hz, hd⟩
    exact ⟨hr, hl, hp, (Finset.erase_subset _ _).trans hm, hz,
      hd.mono_right (Finset.union_subset_union_left (Finset.erase_subset _ _))⟩
  · cases h

theorem wf_disable {x y : Config N m} {s : Word N} (hx : x.WF) (h : disable s x = some y) : y.WF := by
  unfold disable at h
  split at h
  · rename_i hg
    cases h
    rcases hx with ⟨hr, hl, hp, hm, hz, hd⟩
    refine ⟨hr, hl, hp, hm, Finset.insert_subset hg.1 hz, ?_⟩
    exact Finset.disjoint_insert_left.mpr ⟨by simpa using ⟨hg.2.1, hg.2.2.1⟩, hd⟩
  · cases h

theorem wf_enable {x y : Config N m} {s : Word N} (hx : x.WF) (h : enable s x = some y) : y.WF := by
  unfold enable at h
  split at h
  · cases h
    rcases hx with ⟨hr, hl, hp, hm, hz, hd⟩
    exact ⟨hr, hl, hp, hm, (Finset.erase_subset _ _).trans hz,
      hd.mono_left (Finset.erase_subset _ _)⟩
  · cases h

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

private theorem aux_prefix_parent {a w : Word N} (hp : a <+: w) (hne : a ≠ w) :
    a <+: w.dropLast := by
  obtain ⟨t, rfl⟩ := hp
  have ht : t ≠ [] := by rintro rfl; simp at hne
  rw [List.dropLast_append_of_ne_nil ht]
  exact List.prefix_append _ _

private theorem aux_no_prefix {x : Config N m} (hx : x.WF) {b w : Word N}
    (hb : b ∉ x.D) (hw : w ∈ x.D) : ¬ b <+: w :=
  fun hp => hb (aux_prefix_mem hx hw hp)

private theorem aux_no_strict_prefix {x : Config N m} (hx : x.WF) {b w : Word N}
    (hb : b ∉ x.D) (hw : w ∈ x.Sl) : ¬ (b <+: w ∧ b ≠ w) := by
  rintro ⟨hp, hn⟩
  exact hb (aux_prefix_mem hx (aux_mem_Sl.mp hw).2 (aux_prefix_parent hp hn))

private theorem aux_subst_append (a b t : Word N) :
    subst false a b (a ++ t) = b ++ t := by
  simp [subst]

private theorem aux_subst_append_strict (a b t : Word N) (ht : t ≠ []) :
    subst true a b (a ++ t) = b ++ t := by
  have hn : a ≠ a ++ t := by
    intro he
    have := congrArg List.length he
    have := List.length_pos_of_ne_nil ht
    simp only [List.length_append] at *
    omega
  simp [subst, hn]

private theorem aux_subst_inverse {a b w : Word N} (hw : ¬ b <+: w) :
    subst false b a (subst false a b w) = w := by
  by_cases hp : a <+: w
  · obtain ⟨t, rfl⟩ := hp
    rw [aux_subst_append, aux_subst_append]
  · simp [subst, hp, hw]

private theorem aux_subst_inverse_strict {a b w : Word N}
    (hw : ¬ (b <+: w ∧ b ≠ w)) :
    subst true b a (subst true a b w) = w := by
  by_cases hp : a <+: w ∧ a ≠ w
  · obtain ⟨hp, hn⟩ := hp
    obtain ⟨t, rfl⟩ := hp
    have ht : t ≠ [] := by rintro rfl; simp at hn
    rw [aux_subst_append_strict _ _ _ ht, aux_subst_append_strict _ _ _ ht]
  · simp only [subst, Bool.true_eq_false, false_or, if_neg hp, if_neg hw]

private theorem aux_parent_not_below {w : Word N} (hw : w ≠ []) :
    ¬ w <+: w.dropLast := by
  intro hp
  have := hp.length_le
  have := List.length_pos_of_ne_nil hw
  simp only [List.length_dropLast] at *
  omega

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

private theorem aux_subst_slot {x : Config N m} (hx : x.WF) {a b w : Word N}
    (ha : a ∈ x.D) (han : a ≠ []) (hbn : b ≠ []) (hw : w ∈ x.Sl) :
    subst true a b w ≠ [] ∧
      (subst true a b w).dropLast ∈ x.D.image (subst false a b) := by
  by_cases he : a = w
  · subst w
    have hs : subst true a b a = a := by simp [subst]
    rw [hs]
    refine ⟨han, Finset.mem_image.mpr ⟨a.dropLast, hx.2.2.1 a ha han, ?_⟩⟩
    simp [subst, aux_parent_not_below han]
  · rw [aux_subst_agree he]
    obtain ⟨hwn, hwp⟩ := aux_mem_Sl.mp hw
    exact ⟨aux_subst_ne_nil hbn hwn, Finset.mem_image.mpr
      ⟨w.dropLast, hwp, (aux_subst_parent he).symm⟩⟩

theorem wf_graft {x y : Config N m} {a b : Word N} (hx : x.WF) (h : graft a b x = some y) : y.WF := by
  unfold graft at h
  split at h
  · rename_i hg
    cases h
    rcases hg with ⟨ha, ham, hbm, hbd, hbn, hbp, hab, hfit⟩
    have han : a ≠ [] := by rintro rfl; simp at hab
    have hbparent : ¬ a <+: b.dropLast := fun hp => hab (hp.trans b.dropLast_prefix)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨[], hx.1, by simp [subst, han]⟩
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      by_cases hp : a <+: v
      · simpa [subst, hp] using hfit v hv hp
      · simpa [subst, hp] using hx.2.1 v hv
    · intro w hw hwn
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      by_cases he : a = v
      · subst v
        simpa [subst] using
          (Finset.mem_image.mpr ⟨b.dropLast, hbp, by simp [subst, hbparent]⟩ :
            b.dropLast ∈ x.D.image (subst false a b))
      · rw [aux_subst_parent he]
        have hvn : v ≠ [] := by
          rintro rfl
          simp [subst, han] at hwn
        exact Finset.mem_image.mpr ⟨v.dropLast, hx.2.2.1 v hv hvn, rfl⟩
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact aux_mem_Sl.mpr (aux_subst_slot hx ha han hbn (hx.2.2.2.1 hv))
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact aux_mem_Sl.mpr (aux_subst_slot hx ha han hbn (hx.2.2.2.2.1 hv))
    · refine Finset.disjoint_left.mpr ?_
      intro w hw hwother
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      have hvS := hx.2.2.2.2.1 hv
      have hvdis := Finset.disjoint_left.mp hx.2.2.2.2.2 hv
      rcases Finset.mem_union.mp hwother with hm | hd
      · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hm
        have hi := congrArg (subst true b a) he
        rw [aux_subst_inverse_strict (aux_no_strict_prefix hx hbd (hx.2.2.2.1 hu)),
          aux_subst_inverse_strict (aux_no_strict_prefix hx hbd hvS)] at hi
        exact hvdis (Finset.mem_union_left _ (hi ▸ hu))
      · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hd
        have hva : a ≠ v := by
          rintro rfl
          exact hvdis (Finset.mem_union_right _ ha)
        have hvb : b ≠ v := by
          rintro rfl
          exact hvdis (Finset.mem_union_left _ hbm)
        have hnb : ¬ b <+: v := fun hp => aux_no_strict_prefix hx hbd hvS ⟨hp, hvb⟩
        rw [aux_subst_agree hva] at he
        have hi := congrArg (subst false b a) he
        rw [aux_subst_inverse (aux_no_prefix hx hbd hu), aux_subst_inverse hnb] at hi
        exact hvdis (Finset.mem_union_right _ (hi ▸ hu))
  · cases h

/-! ## Exact inverse pairs (Theorem thm:rep-tree(i)) -/

private theorem aux_cell_disjoint {x : Config N m} (hx : x.WF) {a : Word N}
    (ha : a ∉ x.D) : Disjoint (cellW a) (x.D ∪ x.μ ∪ x.ζ) := by
  refine Finset.disjoint_left.mpr ?_
  intro w hw hwx
  obtain ⟨hn, he⟩ := aux_mem_cellW.mp hw
  have hd : w ∈ x.D → a ∈ x.D := fun h => he ▸ hx.2.2.1 w h hn
  have hm : w ∈ x.μ → a ∈ x.D := fun h => he ▸ (aux_mem_Sl.mp (hx.2.2.2.1 h)).2
  have hz : w ∈ x.ζ → a ∈ x.D := fun h => he ▸ (aux_mem_Sl.mp (hx.2.2.2.2.1 h)).2
  simp only [Finset.mem_union] at hwx
  aesop

theorem retract_spawn {x y : Config N m} {a : Word N} (hx : x.WF) (h : spawn a x = some y) :
    retract a y = some x := by
  unfold spawn at h
  split at h
  · rename_i hg
    cases h
    have ha := aux_mem_Sl.mp hg.1
    have hc := aux_cell_disjoint hx hg.2.1
    have hself : a ∉ cellW a := by
      exact fun hm => aux_dropLast_ne ha.1 (aux_mem_cellW.mp hm).2
    have hd : Disjoint (cellW a) (insert a x.D ∪ x.μ ∪ x.ζ) := by
      simpa only [Finset.insert_union, Finset.disjoint_insert_right] using ⟨hself, hc⟩
    unfold retract
    rw [if_pos ⟨by simp, ha.1, hd⟩]
    simp only [Finset.erase_insert hg.2.1]
  · cases h

theorem spawn_retract {x y : Config N m} {a : Word N} (hx : x.WF) (h : retract a x = some y) :
    spawn a y = some x := by
  unfold retract at h
  split at h
  · rename_i hg
    cases h
    have hs : a ∈ (Config.mk (x.D.erase a) x.μ x.ζ : Config N m).Sl :=
      aux_mem_Sl.mpr ⟨hg.2.1, Finset.mem_erase.mpr
        ⟨aux_dropLast_ne hg.2.1, hx.2.2.1 a hg.1 hg.2.1⟩⟩
    have hz : a ∉ x.ζ := fun hz =>
      Finset.disjoint_left.mp hx.2.2.2.2.2 hz (Finset.mem_union_right _ hg.1)
    simp [spawn, hs, hz, hx.2.1 a hg.1, Finset.insert_erase hg.1]
  · cases h

theorem leave_join {x y : Config N m} {s : Word N} (h : join s x = some y) : leave s y = some x := by
  unfold join at h
  split at h
  · rename_i hg
    cases h
    simp [leave, Finset.erase_insert hg.2.1]
  · cases h

theorem join_leave {x y : Config N m} {s : Word N} (hx : x.WF) (h : leave s x = some y) :
    join s y = some x := by
  unfold leave at h
  split at h
  · rename_i hg
    cases h
    have hs := hx.2.2.2.1 hg
    have hz : s ∉ x.ζ := fun hz =>
      Finset.disjoint_left.mp hx.2.2.2.2.2 hz (Finset.mem_union_left _ hg)
    simpa [join, Sl, hz, Finset.insert_erase hg] using hs
  · cases h

theorem enable_disable {x y : Config N m} {s : Word N} (h : disable s x = some y) :
    enable s y = some x := by
  unfold disable at h
  split at h
  · rename_i hg
    cases h
    simp [enable, Finset.erase_insert hg.2.2.2]
  · cases h

theorem disable_enable {x y : Config N m} {s : Word N} (hx : x.WF) (h : enable s x = some y) :
    disable s y = some x := by
  unfold enable at h
  split at h
  · rename_i hg
    cases h
    have hs := hx.2.2.2.2.1 hg
    have hd := Finset.disjoint_left.mp hx.2.2.2.2.2 hg
    have hm : s ∉ x.μ := fun h => hd (Finset.mem_union_left _ h)
    have hc : s ∉ x.D := fun h => hd (Finset.mem_union_right _ h)
    simpa [disable, Sl, hm, hc, Finset.insert_erase hg] using hs
  · cases h

private theorem aux_image_inverse {s : Finset (Word N)} {f g : Word N → Word N}
    (hi : ∀ w ∈ s, g (f w) = w) : (s.image f).image g = s := by
  rw [Finset.image_image]
  calc
    s.image (g ∘ f) = s.image id := Finset.image_congr hi
    _ = s := Finset.image_id

theorem graft_graft {x y : Config N m} {a b : Word N} (hx : x.WF) (h : graft a b x = some y) :
    graft b a y = some x := by
  unfold graft at h
  split at h
  · rename_i hg
    cases h
    rcases hg with ⟨ha, ham, hbm, hbd, hbn, hbp, hab, hfit⟩
    have han : a ≠ [] := by rintro rfl; simp at hab
    have hba : ¬ b <+: a := aux_no_prefix hx hbd ha
    have hD : (x.D.image (subst false a b)).image (subst false b a) = x.D :=
      aux_image_inverse fun w hw => aux_subst_inverse (aux_no_prefix hx hbd hw)
    have hM : (x.μ.image (subst true a b)).image (subst true b a) = x.μ :=
      aux_image_inverse fun w hw =>
        aux_subst_inverse_strict (aux_no_strict_prefix hx hbd (hx.2.2.2.1 hw))
    have hZ : (x.ζ.image (subst true a b)).image (subst true b a) = x.ζ :=
      aux_image_inverse fun w hw =>
        aux_subst_inverse_strict (aux_no_strict_prefix hx hbd (hx.2.2.2.2.1 hw))
    unfold graft
    rw [if_pos ?_]
    · change some (Config.mk _ _ _) = some x
      rw [hD, hM, hZ]
    · refine ⟨?_, ?_, ?_, ?_, han, ?_, hba, ?_⟩
      · exact Finset.mem_image.mpr ⟨a, ha, by simp [subst]⟩
      · exact Finset.mem_image.mpr ⟨b, hbm, by simp [subst, hab]⟩
      · exact Finset.mem_image.mpr ⟨a, ham, by simp [subst]⟩
      · intro hm
        obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hm
        by_cases hp : a <+: w
        · obtain ⟨t, rfl⟩ := hp
          rw [aux_subst_append] at he
          exact hba (he ▸ List.prefix_append b t)
        · have he' : w = a := by simpa [subst, hp] using he
          subst w
          exact hp (List.prefix_refl _)
      · exact Finset.mem_image.mpr ⟨a.dropLast, hx.2.2.1 a ha han,
          by simp [subst, aux_parent_not_below han]⟩
      · intro w hw hp
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        by_cases hap : a <+: v
        · obtain ⟨t, rfl⟩ := hap
          rw [aux_subst_append]
          have hl := hx.2.1 (a ++ t) hv
          simpa only [List.length_append, Nat.add_sub_cancel_left] using hl
        · have hbp' : b <+: v := by simpa [subst, hap] using hp
          exact (aux_no_prefix hx hbd hv hbp').elim
  · cases h

/-! ## Suffix covariance of the two-clause law (Theorem thm:graft-iso(ii)) -/

/-- Adjacency on words: the two-clause law read on `List (Fin N)`. -/
def AdjW (u v : Word N) : Prop :=
  u ≠ v ∧ ((u.length = v.length ∧ u.dropLast = v.dropLast) ∨
    (v.length = u.length + 1 ∧ v.dropLast = u) ∨ (u.length = v.length + 1 ∧ u.dropLast = v))

/-- The word-level law agrees with the graph of `Basic.lean` on addresses. -/
theorem adjW_iff_adj (u v : Addr N m) : AdjW u.1 v.1 ↔ (graph N m).Adj u v := by
  have he : u = v ↔ u.1 = v.1 := ⟨congrArg Subtype.val, Addr.ext⟩
  simp only [AdjW, graph, Sib, Par, ne_eq, he]

/-- **Suffix covariance**: for nonempty suffixes, adjacency below `a` and below `b` agree,
so the prefix substitution `a w ↦ b w` is an isomorphism on the moved slots. -/
theorem adjW_append_iff (a b w₁ w₂ : Word N) (h₁ : w₁ ≠ []) (h₂ : w₂ ≠ []) :
    AdjW (a ++ w₁) (a ++ w₂) ↔ AdjW (b ++ w₁) (b ++ w₂) := by
  simp [AdjW, List.dropLast_append_of_ne_nil h₁,
    List.dropLast_append_of_ne_nil h₂, Nat.add_assoc]

/-! ## Footprint-disjoint bookkeeping letters commute (Proposition prop:commute, instances) -/

theorem join_join_comm (x : Config N m) {s t : Word N} (h : s ≠ t) :
    (join s x).bind (join t) = (join t x).bind (join s) := by
  unfold join
  split_ifs <;> simp_all [Sl, Ne.symm h, Finset.insert_comm] <;> assumption

theorem leave_leave_comm (x : Config N m) {s t : Word N} (h : s ≠ t) :
    (leave s x).bind (leave t) = (leave t x).bind (leave s) := by
  unfold leave
  split_ifs <;> simp_all [Ne.symm h, Finset.erase_right_comm]

theorem join_leave_comm (x : Config N m) {s t : Word N} (h : s ≠ t) :
    (join s x).bind (leave t) = (leave t x).bind (join s) := by
  unfold join leave
  split_ifs <;> simp_all [Sl, Ne.symm h, Finset.erase_insert_of_ne]; assumption

theorem disable_enable_comm (x : Config N m) {s t : Word N} (h : s ≠ t) :
    (disable s x).bind (enable t) = (enable t x).bind (disable s) := by
  unfold disable enable
  split_ifs <;> simp_all [Sl, Ne.symm h, Finset.erase_insert_of_ne]; assumption

set_option linter.unusedVariables false in
/-- `spawn a` and `join s` commute when the footprints `{pre a, a} ∪ cell a` and `{pre s, s}`
are disjoint; the relevant disjointness is `s ≠ a`, `s ∉ cell a` and `a ∉ cell s`. -/
theorem spawn_join_comm (x : Config N m) {a s : Word N} (hsa : s ≠ a) (hs : s ∉ cellW a)
    (has : a ∉ cellW s) :
    (spawn a x).bind (join s) = (join s x).bind (spawn a) := by
  unfold spawn join
  split_ifs <;> simp_all [Sl] <;> assumption

/-- Two spawns at distinct, non-nested sites commute. -/
theorem spawn_spawn_comm (x : Config N m) {a b : Word N} (hab : a ≠ b) (ha : a ∉ cellW b)
    (hb : b ∉ cellW a) :
    (spawn a x).bind (spawn b) = (spawn b x).bind (spawn a) := by
  unfold spawn
  split_ifs <;> simp_all [Sl, Ne.symm hab, Finset.insert_comm] <;> assumption

end Calc

end HSFN
