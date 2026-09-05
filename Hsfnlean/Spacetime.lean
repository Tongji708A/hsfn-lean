/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Calculus

/-!
# Spacetime coordinates are carried, not reset
(Definition def:spacetime-coordinate; Proposition prop:coordinate-persistence, items (ii) and (iv))

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

A spacetime coordinate of the entity residing at an occupied slot `s` is the pair
`χ(s) = (a(s), h(s))`: the address of `s` together with the current block height of the *cell*
of `s`. In the word calculus of `Hsfnlean.Calculus` the address of a slot is the word itself and
the cell of a slot `s` is `s.dropLast` (this is how `Config.Sl` is built: `s` is a member slot of
the cell deployed at `s.dropLast`), so a height assignment is protocol metadata
`h : Word N → ℕ` attached to deployed cells — exactly the paper's reading, "a configuration whose
cells carry chains as protocol metadata riding on their memberships" — and
`coord h s = (s, h s.dropLast)`.

The reconfiguration dynamics moves addresses by prefix substitution (`graft`); the metadata
travels with the memberships. Formally, the height function of the post-graft configuration is
the *pullback* of the old one along the move, `transport a b h = fun w => h (subst false b a w)`,
which sends the new address of a cell back to its old address. What this module states:

* `transport_height_of_graft`, `transport_height_of_graft_root`,
  `transport_height_of_graft_outside` — item (ii), "time is carried, not reset", for the three
  positions a surviving occupied slot can occupy relative to the grafted root.
* `*_deployed_eq` for the six bookkeeping letters, together with `writesNoChainState_*` — "no
  generator writes chain state": those letters pin the deployed set exactly (`y.D` is `x.D`, or
  `x.D` with one site inserted or erased) and relocate no cell address, so the cell of a
  surviving occupant is still deployed at the *same* address afterwards and its height is read
  back at the same key. `graft_root_not_deployed` and `graft_target_deployed` are the contrast:
  `graft` is the one letter that does move a deployed cell address, which is why it alone needs a
  nontrivial transport.
  *Audit note.* `WritesNoChainState` does not by itself separate the six letters from `graft`:
  a slot moved by a graft is absent from `y.μ` under its old name, so the predicate's hypothesis
  is vacuous on the moved cone and `graft` satisfies the predicate as well. The separation is
  carried by `*_deployed_eq` and the two `graft_*` lemmas, not by `WritesNoChainState`.
* `coord_injective`, `coord_injOn` — the coordinate map is injective in its slot argument.
  This is trivially so, the address being the first component; the substance of "the address
  names the entity faithfully" is Proposition prop:addr-bij, which is not proved here.
* `coord_graft_equivariant`, `carriesHeights_graft` — item (iv), equivariance: under a graft the
  first component moves by the prefix substitution and the second component is unchanged.
* `worldline_graft` — "worldlines relocate; they never break": the traversed segment of the
  worldline after the graft is the image of the segment before it under the address relocation,
  same ticks, same length.

**Out of scope, honestly.** This module formalizes only the transport bookkeeping of items (ii)
and (iv) of Proposition prop:coordinate-persistence, and only for *single letters*, never for a
composite calculus word `w`. It does *not* formalize:
item (i) in its full generality (the relocation cocycle of Theorem thm:rep-tree(ii) and the
cell-wise relabelings of the `permute` letters — the calculus module has no `permute`);
item (iii) at all (the `O(1)` successor repairs that splice the canonical depth-first update
cycle, Remark rem:graft-splice); the identification of the rigid part with an element of `V_N`
(Theorem thm:vn-identification), so equivariance is stated per-graft rather than for a group
action; and the *consensus* semantics of a tick — nothing here says that a block is agreed, that
anchor uplinks reconcile heights upward, or that heights advance at all. Heights are inert data
here; the content stated is that the dynamics never rewrites them.
-/

namespace HSFN

namespace Calc

variable {N m : ℕ}

/-! ## The coordinate system (Definition def:spacetime-coordinate) -/

/-- A **height assignment**: protocol metadata attached to the deployed cells of a configuration
of `Config N m`, `h w` being the block height (the number of agreed blocks, i.e. of ticks) of the
chain of the cell deployed at the word `w`. It is not part of the configuration; it rides on the
memberships. The depth bound `m` plays no role in the metadata, so `Height` does not carry it;
every statement below gets `m` from the `Config N m` it speaks about. -/
abbrev Height (N : ℕ) := Word N → ℕ

/-- The cell of a slot: the slot `s` is a member slot of the cell deployed at `s.dropLast`
(`Config.Sl`). The statements below are written with `s.dropLast` directly; this abbreviation
records the modelling choice. -/
def cellOf (s : Word N) : Word N := s.dropLast

/-- The **spacetime coordinate** `χ(s) = (a(s), h(s))` of the entity residing at the slot `s`:
its address (the word itself) together with the current block height of its cell. -/
def coord (h : Height N) (s : Word N) : Word N × ℕ := (s, h s.dropLast)

/-- The **worldline** of the entity at slot `s`: the sequence `(a, 1), (a, 2), …` of coordinates
it traverses as the chain of its cell grows. -/
def worldline (s : Word N) : ℕ → Word N × ℕ := fun k => (s, k)

/-- The segment of the worldline traversed so far, at height assignment `h`: the finite set of
coordinates `(s, 1), …, (s, h(cell of s))`. This is the object in which "a worldline does not
break" has content — a break would lose ticks, i.e. shorten this segment. -/
def worldlineUpTo (h : Height N) (s : Word N) : Finset (Word N × ℕ) :=
  (Finset.Icc 1 (h s.dropLast)).image (worldline s)

@[simp] theorem coord_fst (h : Height N) (s : Word N) : (coord h s).1 = s := rfl

@[simp] theorem coord_snd (h : Height N) (s : Word N) : (coord h s).2 = h s.dropLast := rfl

/-- The height assignment carried across a `graft a b`: the pullback of `h` along the move, so
that the cell arriving at a new address reports the height it had at its old address. Read on
words, `graft a b` sends the deployed cell `a ++ t` to `b ++ t` (non-strictly: the cell `a` itself
moves to `b`), so the pullback substitutes `b ↦ a`, non-strictly as well. It is the correct
pullback on the addresses that actually occur in the configuration; off them it is meaningless,
which is why every statement below restricts to occupied slots of a well-formed `x`. -/
def transport (a b : Word N) (h : Height N) : Height N := fun w => h (subst false b a w)

/-- A letter `g` **carries heights** along the address relocation `t` with height transport `th`
when every occupied slot that survives `g` arrives at the address `t s` bearing the height its
cell had before: the coordinate of the moved slot is `(t s, h s.dropLast)`, the old height
verbatim. This is the formal content of "cells travel with their memberships and metadata
verbatim; no generator writes chain state" (Proposition prop:coordinate-persistence(ii)) and of
the displayed equivariance `χ(w(s)) = (g(a(s)), h(s))` of item (iv). -/
def CarriesHeights (g : Config N m → Option (Config N m)) (t : Word N → Word N)
    (th : Height N → Height N) : Prop :=
  ∀ x y : Config N m, x.WF → g x = some y → ∀ (h : Height N) (s : Word N),
    s ∈ x.μ → t s ∈ y.μ → coord (th h) (t s) = (t s, h s.dropLast)

/-- A letter **writes no chain state** when the cell hosting any occupied slot that survives it is
still deployed at the *same* address afterwards. Heights being keyed by cell address, this is
what makes the identity the correct height transport for that letter: the chain of a surviving
occupant is looked up, before and after, at one and the same address.
Honest reading of its strength: the predicate does *not* by itself separate the six bookkeeping
letters from `graft`. A slot moved by a graft is absent from `y.μ` under its old name, so the
hypothesis `s ∈ y.μ` is vacuous on the moved cone and `graft` satisfies the predicate too. What
separates them is that `graft` moves a deployed cell address at all
(`graft_root_not_deployed`, `graft_target_deployed`), while the six letters pin the deployed set
(`*_deployed_eq`). -/
def WritesNoChainState (g : Config N m → Option (Config N m)) : Prop :=
  ∀ x y : Config N m, x.WF → g x = some y → ∀ s ∈ x.μ, s ∈ y.μ →
    s.dropLast ∈ x.D ∧ s.dropLast ∈ y.D

/-! ### Word-calculus toolkit, re-derived locally

The corresponding auxiliary lemmas of `Hsfnlean.Calculus` are `private` and therefore invisible
here, so the handful of facts about `cellW`, `Config.Sl`, prefix closure and `subst` that the
proofs below need are re-derived. Nothing in this block is new mathematics. -/

private theorem aux_mem_cellW {v w : Word N} : v ∈ cellW w ↔ v ≠ [] ∧ v.dropLast = w := by
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨d, _, rfl⟩
    simp
  · rintro ⟨hv, rfl⟩
    exact Finset.mem_image.mpr
      ⟨v.getLast hv, Finset.mem_univ _, List.dropLast_append_getLast hv⟩

private theorem aux_mem_Sl {x : Config N m} {w : Word N} :
    w ∈ x.Sl ↔ w ≠ [] ∧ w.dropLast ∈ x.D := by
  simp only [Config.Sl, Finset.mem_biUnion, aux_mem_cellW]
  aesop

/-- An occupied slot of a well-formed configuration is nonempty and its cell is deployed. -/
private theorem aux_occupied_cell {x : Config N m} (hx : x.WF) {s : Word N} (hs : s ∈ x.μ) :
    s ≠ [] ∧ s.dropLast ∈ x.D :=
  aux_mem_Sl.mp (hx.2.2.2.1 hs)

/-- Prefix closure of `D`, iterated. -/
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

private theorem aux_subst_append (a b t : Word N) : subst false a b (a ++ t) = b ++ t := by
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

private theorem aux_subst_self (a b : Word N) : subst true a b a = a := by simp [subst]

private theorem aux_subst_id (st : Bool) {a b w : Word N} (hp : ¬ a <+: w) :
    subst st a b w = w := by simp [subst, hp]

/-- The guard and the effect of a successful `graft`, unpacked. -/
private theorem aux_graft_spec {x y : Config N m} {a b : Word N} (hg : graft a b x = some y) :
    (a ∈ x.D ∧ a ∈ x.μ ∧ b ∈ x.μ ∧ b ∉ x.D ∧ b ≠ [] ∧ b.dropLast ∈ x.D ∧ ¬ a <+: b ∧
        (∀ w ∈ x.D, a <+: w → b.length + (w.length - a.length) + 1 ≤ m)) ∧
      y = ⟨x.D.image (subst false a b), x.μ.image (subst true a b),
        x.ζ.image (subst true a b)⟩ := by
  unfold graft at hg
  split at hg
  · rename_i hgu
    cases hg
    exact ⟨hgu, rfl⟩
  · cases hg

/-- Under the graft guard, `b` is a prefix of no deployed cell of `x`: `b ∉ D` and `D` is
prefix-closed. This is what makes the pullback `subst false b a` the identity on every cell
address occurring in `x`. -/
private theorem aux_graft_no_prefix {x y : Config N m} {a b : Word N} (hx : x.WF)
    (hg : graft a b x = some y) {w : Word N} (hw : w ∈ x.D) : ¬ b <+: w :=
  fun hp => (aux_graft_spec hg).1.2.2.2.1 (aux_prefix_mem hx hw hp)

/-! ## (a) Heights are carried across a graft (Proposition prop:coordinate-persistence(ii))

Instance witnessing non-vacuity: `N = 2`, `m = 3`,
`x = ⟨{[], [0]}, {[0], [1], [0,0]}, ∅⟩`, `a = [0]`, `b = [1]`, `s = [0,0]`. Then `x.WF` holds,
`graft [0] [1] x` succeeds (all eight guards check), and `s` is an occupied slot strictly below
`a`; it relocates to `[1,0]` while the height `h [0]` of its cell is read back at `[1]`.

Audit note on `transport_height_of_graft`: the hypotheses `hx`, `hg`, `hs` place the statement in
the paper's setting (a graft applicable at `x`, an occupied slot `s` surviving it), but for a slot
strictly below `a` the displayed identity is in fact a word identity that holds unconditionally.
The two companion statements below, which cover the remaining positions of `s`, genuinely need
`x.WF` and the graft guard, and so does the uniform `carriesHeights_graft`. -/

set_option linter.unusedVariables false in
/-- **Time is carried, not reset.** For a graft `a → b` applicable at `x` and an occupied slot `s`
strictly below `a`, the cell of the relocated slot reports, under the transported height
assignment, exactly the height it had before the move. -/
theorem transport_height_of_graft {x y : Config N m} {a b s : Word N} (h : Height N)
    (hx : x.WF) (hg : graft a b x = some y) (hs : s ∈ x.μ) (hpre : a <+: s) (hne : a ≠ s) :
    (transport a b h) (subst true a b s).dropLast = h s.dropLast := by
  obtain ⟨t, rfl⟩ := hpre
  have ht : t ≠ [] := by rintro rfl; simp at hne
  rw [aux_subst_append_strict a b t ht]
  show h (subst false b a (b ++ t).dropLast) = h ((a ++ t).dropLast)
  rw [List.dropLast_append_of_ne_nil ht, List.dropLast_append_of_ne_nil ht,
    aux_subst_append b a t.dropLast]

/-- The slot `a` itself stays behind under `graft a b` (`μ` moves by the *strict* substitution),
and its cell `a.dropLast` does not move either, since `b` is a prefix of no deployed cell of a
well-formed `x` admitting `graft a b`. The entity at `a` therefore keeps its whole coordinate. -/
theorem transport_height_of_graft_root {x y : Config N m} {a b : Word N} (h : Height N)
    (hx : x.WF) (hg : graft a b x = some y) :
    (transport a b h) (subst true a b a).dropLast = h a.dropLast := by
  obtain ⟨ha, -, -, -, -, -, hab, -⟩ := (aux_graft_spec hg).1
  have han : a ≠ [] := by rintro rfl; exact hab (List.nil_prefix)
  have hap : a.dropLast ∈ x.D := hx.2.2.1 a ha han
  have hnb : ¬ b <+: a.dropLast := aux_graft_no_prefix hx hg hap
  rw [aux_subst_self]
  show h (subst false b a a.dropLast) = h a.dropLast
  rw [aux_subst_id false hnb]

/-- Slots outside the moved cone keep their height as well: their address is unchanged, and `b` is
a prefix of no deployed cell of a well-formed `x` admitting `graft a b` (prefix closure of `D`
together with `b ∉ D`), so the pullback is the identity on their cells. -/
theorem transport_height_of_graft_outside {x y : Config N m} {a b s : Word N} (h : Height N)
    (hx : x.WF) (hg : graft a b x = some y) (hs : s ∈ x.μ) (hpre : ¬ a <+: s) :
    (transport a b h) (subst true a b s).dropLast = h s.dropLast := by
  have hnb : ¬ b <+: s.dropLast := aux_graft_no_prefix hx hg (aux_occupied_cell hx hs).2
  rw [aux_subst_id true hpre]
  show h (subst false b a s.dropLast) = h s.dropLast
  rw [aux_subst_id false hnb]

/-! ## (b) No generator writes chain state

The six bookkeeping letters relocate no address at all: they change the deployed set only at the
site they act on, and never rewrite the address of an existing cell (`*_deployed_eq`). The cell of
a surviving occupant is therefore still deployed at the same address afterwards
(`writesNoChainState_*`), and the identity is the correct height transport for them. The contrast
with the one address-moving letter is `graft_root_not_deployed` and `graft_target_deployed`.

Instances witnessing non-vacuity: with `N = 2`, `m = 3` and `x = ⟨{[]}, ∅, ∅⟩` (the seed),
`join [0] x`, `spawn [0] x` and `disable [0] x` all succeed; `leave`, `retract` and `enable`
succeed at the corresponding results. For `writesNoChainState_*` a witness with a nonempty `μ` is
needed, e.g. `x = ⟨{[], [0]}, {[0], [0,0]}, ∅⟩` at `N = 2`, `m = 3`, where `join [1]`,
`leave [0,0]`, `spawn [1]`, `retract [0]` (after `leave [0,0]`), `disable [1]` all apply and
`[0] ∈ μ` survives each of them. -/

theorem join_deployed_eq {x y : Config N m} {s : Word N} (h : join s x = some y) : y.D = x.D := by
  unfold join at h
  split at h
  · cases h; rfl
  · cases h

theorem leave_deployed_eq {x y : Config N m} {s : Word N} (h : leave s x = some y) :
    y.D = x.D := by
  unfold leave at h
  split at h
  · cases h; rfl
  · cases h

theorem disable_deployed_eq {x y : Config N m} {s : Word N} (h : disable s x = some y) :
    y.D = x.D := by
  unfold disable at h
  split at h
  · cases h; rfl
  · cases h

theorem enable_deployed_eq {x y : Config N m} {s : Word N} (h : enable s x = some y) :
    y.D = x.D := by
  unfold enable at h
  split at h
  · cases h; rfl
  · cases h

/-- `spawn a` adds one cell at `a` and moves none: every old cell keeps its address. -/
theorem spawn_deployed_eq {x y : Config N m} {a : Word N} (h : spawn a x = some y) :
    y.D = insert a x.D := by
  unfold spawn at h
  split at h
  · cases h; rfl
  · cases h

/-- `retract a` deletes the cell at `a` and moves none: every surviving cell keeps its address. -/
theorem retract_deployed_eq {x y : Config N m} {a : Word N} (h : retract a x = some y) :
    y.D = x.D.erase a := by
  unfold retract at h
  split at h
  · cases h; rfl
  · cases h

/-- The contrast with the six letters above: `graft a b` does move a deployed cell address. The
cell at the grafted root is no longer deployed at `a` afterwards — no cell of `x` is carried to
`a` by the substitution, since `b` is a prefix of no deployed cell of a well-formed `x` admitting
`graft a b`. This is why `graft` is the one letter whose height metadata needs a nontrivial
transport. -/
theorem graft_root_not_deployed {x y : Config N m} {a b : Word N}
    (hx : x.WF) (hg : graft a b x = some y) : a ∉ y.D := by
  obtain ⟨⟨ha, -, -, hbd, -, -, -, -⟩, rfl⟩ := aux_graft_spec hg
  intro hmem
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hmem
  by_cases hp : a <+: v
  · obtain ⟨t, rfl⟩ := hp
    rw [aux_subst_append] at he
    exact hbd (aux_prefix_mem hx ha (he ▸ List.prefix_append b t))
  · rw [aux_subst_id false hp] at he
    exact hp (he ▸ List.prefix_refl v)

/-- … and the cell of the grafted root arrives at `b`: the height that was keyed at `a` is keyed at
`b` afterwards, which is exactly what `transport a b` undoes. -/
theorem graft_target_deployed {x y : Config N m} {a b : Word N}
    (hg : graft a b x = some y) : b ∈ y.D := by
  obtain ⟨hgu, rfl⟩ := aux_graft_spec hg
  exact Finset.mem_image.mpr ⟨a, hgu.1, by simp [subst]⟩

theorem writesNoChainState_join (s : Word N) :
    WritesNoChainState (fun x : Config N m => join s x) := by
  intro x y hx hg w hw _
  have hc : w.dropLast ∈ x.D := (aux_occupied_cell hx hw).2
  refine ⟨hc, ?_⟩
  rw [join_deployed_eq (show join s x = some y from hg)]
  exact hc

theorem writesNoChainState_leave (s : Word N) :
    WritesNoChainState (fun x : Config N m => leave s x) := by
  intro x y hx hg w hw _
  have hc : w.dropLast ∈ x.D := (aux_occupied_cell hx hw).2
  refine ⟨hc, ?_⟩
  rw [leave_deployed_eq (show leave s x = some y from hg)]
  exact hc

theorem writesNoChainState_disable (s : Word N) :
    WritesNoChainState (fun x : Config N m => disable s x) := by
  intro x y hx hg w hw _
  have hc : w.dropLast ∈ x.D := (aux_occupied_cell hx hw).2
  refine ⟨hc, ?_⟩
  rw [disable_deployed_eq (show disable s x = some y from hg)]
  exact hc

theorem writesNoChainState_enable (s : Word N) :
    WritesNoChainState (fun x : Config N m => enable s x) := by
  intro x y hx hg w hw _
  have hc : w.dropLast ∈ x.D := (aux_occupied_cell hx hw).2
  refine ⟨hc, ?_⟩
  rw [enable_deployed_eq (show enable s x = some y from hg)]
  exact hc

theorem writesNoChainState_spawn (a : Word N) :
    WritesNoChainState (fun x : Config N m => spawn a x) := by
  intro x y hx hg w hw _
  have hc : w.dropLast ∈ x.D := (aux_occupied_cell hx hw).2
  refine ⟨hc, ?_⟩
  rw [spawn_deployed_eq (show spawn a x = some y from hg)]
  exact Finset.mem_insert_of_mem hc

/-- The only nontrivial one: `retract a` erases the cell `a`, so one must know that `a` is the cell
of no occupied slot — which is the emptiness guard `Disjoint (cellW a) (D ∪ μ ∪ ζ)` of the letter. -/
theorem writesNoChainState_retract (a : Word N) :
    WritesNoChainState (fun x : Config N m => retract a x) := by
  intro x y hx hg w hw _
  have hg' : retract a x = some y := hg
  obtain ⟨hwn, hc⟩ := aux_occupied_cell hx hw
  refine ⟨hc, ?_⟩
  rw [retract_deployed_eq hg']
  refine Finset.mem_erase.mpr ⟨?_, hc⟩
  intro he
  unfold retract at hg'
  split at hg'
  · rename_i hgu
    exact Finset.disjoint_left.mp hgu.2.2 (aux_mem_cellW.mpr ⟨hwn, he⟩) (by simp [hw])
  · cases hg'

/-- **A definitional tautology, recorded as such.** `CarriesHeights g id id` unfolds to
`coord h s = (s, h s.dropLast)`, which is true by `rfl` for *every* `g` whatsoever; it says only
that the identity height transport is the correct one for a letter that relocates no address, and
by itself carries no information about `g`. The content for the six bookkeeping letters is
`writesNoChainState_*` above (which is what makes `id` the right relocation for them); the content
for the one address-moving letter is `carriesHeights_graft` below. -/
theorem carriesHeights_id (g : Config N m → Option (Config N m)) :
    CarriesHeights g id id := by
  intro _ _ _ _ _ _ _ _
  rfl

/-! ## (c) The coordinate names the entity faithfully (Definition def:spacetime-coordinate) -/

/-- At a fixed height assignment the coordinate map is injective in its slot argument: distinct
slots carry distinct spacetime coordinates. (Trivially so, the address being the first component;
the substance of "the address names the entity faithfully" is Proposition prop:addr-bij, which
lives in `Hsfnlean.Basic`, not here.) -/
theorem coord_injective (h : Height N) : Function.Injective (coord h) := by
  intro s t hst
  exact congrArg Prod.fst hst

/-- The same, read on the occupied slots of a configuration. -/
theorem coord_injOn (h : Height N) (x : Config N m) :
    Set.InjOn (coord h) (x.μ : Set (Word N)) := by
  intro s _ t _ hst
  exact coord_injective h hst

/-! ## (d) Equivariance (Proposition prop:coordinate-persistence(iv))

Instance witnessing non-vacuity: the same `N = 2`, `m = 3`,
`x = ⟨{[], [0]}, {[0], [1], [0,0]}, ∅⟩`, `a = [0]`, `b = [1]`, `s = [0,0]` as above; the slot
`[0,0]` relocates to `[1,0]` while the height `h [0]` of its cell is carried to `[1]` untouched. -/

set_option linter.unusedVariables false in
/-- **Equivariance under a graft.** The address moves by the prefix substitution and the second
component of the coordinate is unchanged: `χ(w(s)) = (g(a(s)), h(s))`. -/
theorem coord_graft_equivariant {x y : Config N m} {a b s : Word N} (h : Height N)
    (hx : x.WF) (hg : graft a b x = some y) (hs : s ∈ x.μ) (hpre : a <+: s) (hne : a ≠ s) :
    coord (transport a b h) (subst true a b s) = (subst true a b s, h s.dropLast) := by
  simp only [coord, transport_height_of_graft h hx hg hs hpre hne]

/-- The uniform statement, and the strongest in this module: a graft carries the heights of *every*
surviving occupied slot along the prefix substitution — in the moved cone, at the grafted root
itself, and outside the cone alike. Its proof needs `x.WF` and all eight graft guards. -/
theorem carriesHeights_graft (a b : Word N) :
    CarriesHeights (fun x : Config N m => graft a b x) (subst true a b) (transport a b) := by
  intro x y hx hg h s hs _
  have hg' : graft a b x = some y := hg
  have key : (transport a b h) (subst true a b s).dropLast = h s.dropLast := by
    by_cases hp : a <+: s
    · by_cases he : a = s
      · subst he
        exact transport_height_of_graft_root h hx hg'
      · exact transport_height_of_graft h hx hg' hs hp he
    · exact transport_height_of_graft_outside h hx hg' hs hp
  simp only [coord, key]

set_option linter.unusedVariables false in
/-- **Worldlines relocate; they never break.** The segment of the worldline traversed by the
entity at `s` after the graft is exactly the image, under the address relocation, of the segment
it had traversed before: same ticks `1, …, h`, same length, only a new address. No tick is lost
and none is re-numbered. -/
theorem worldline_graft {x y : Config N m} {a b s : Word N} (h : Height N)
    (hx : x.WF) (hg : graft a b x = some y) (hs : s ∈ x.μ) (hpre : a <+: s) (hne : a ≠ s) :
    worldlineUpTo (transport a b h) (subst true a b s)
      = (worldlineUpTo h s).image (fun c => (subst true a b c.1, c.2)) := by
  have key := transport_height_of_graft h hx hg hs hpre hne
  simp only [worldlineUpTo, key, Finset.image_image]
  exact Finset.image_congr fun k _ => rfl


end Calc

end HSFN
