/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Clique

/-!
# A tree decomposition of `F(N,m)` of width `N` (Lemma lem:tw-nec, upper bound)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409),
Lemma `lem:tw-nec` (`tw(F(N,1)) = N-1`, `tw(F(N,m)) = N` for `m ≥ 2`; hence
`tw(H) ≤ N` for every realized `H`). The proof in the deferred-proofs appendix
reads:

> The anchored cliques and the tier-`1` cell form a clique tree. Take one bag
> per cell, containing the cell's `N` members together with its anchor (the
> tier-`1` bag has `N` members and no anchor). Adjacent cells share exactly
> their common anchor node. The bags therefore satisfy the running-intersection
> property along the cell tree, giving a tree decomposition of width `N`
> (bag size `N+1`).

Mathlib carries no treewidth API to lean on, so this file formalizes the
*upper bound half* concretely: the bag family is defined explicitly and the
three tree-decomposition axioms — vertex covering, edge covering, and the
running-intersection (coherence) condition — are stated for it, together with
the width bound `|bag| ≤ N + 1`. The bags are exactly the anchored cliques of
`Hsfnlean.Clique` (`bag w = anchored w`, of order `N + 1` at a non-leaf `w`)
plus the root bag, the tier-`1` cell (`rootBag = tier1 N m`, of order `N`).

The index of the family is the cell tree: `none` names the tier-`1` cell and
`some w` names the cell spawned at `w`, with `treeParent` the parent map that
makes the index a tree (it strictly decreases the tier, `treeParent_tier_lt`).
`bag_inter_parent` / `rootBag_inter_bag` are the paper's "adjacent cells share
exactly their common anchor node", and `coherence_idx` is the running-intersection
property itself: the indices whose bag contains a fixed `v` are exactly the
tree-adjacent pair `some v`, `treeParent v`.

The width claims track the paper's two cases: `exists_card_bag_eq` shows that
for `m ≥ 2` some bag really does have order `N + 1`, so `card_bag_le` is not
vacuously loose and *this* decomposition has width exactly `N` (it does **not**
show `tw(F(N,m)) ≥ N`, which is a statement about every decomposition and needs
a treewidth API); `card_bagAt_le_of_m_one` shows every bag has order at most `N`
when `m = 1`, which is the upper half of the paper's `tw(F(N,1)) = N-1`.

The lower bounds `tw(F(N,m)) ≥ N` (from `K_{N+1} ⊆ F(N,m)`, Lemma
`lem:maxclique` / `HSFN.cliqueNum_eq`) and `tw(F(N,1)) ≥ N-1`, and the
minor-monotone transfer to a realized `H`, are **not** attempted here: all
three need a treewidth API.
-/

namespace HSFN

namespace TreeDecomp

variable {N m : ℕ}

open Finset

/-- Membership in the spawned cell, unfolded (a local copy of the private
helper of `Hsfnlean.Clique`). -/
private theorem aux_mem_chiF {u v : Addr N m} :
    v ∈ chiF u ↔ v.1.length = u.1.length + 1 ∧ v.1.dropLast = u.1 := by
  simp [chiF]

/-! ## The bag family -/

/-- The bag of the cell spawned at `w`: the `N` members of that cell together
with their anchor `w`. This is the anchored clique of `w`. -/
def bag (w : Addr N m) : Finset (Addr N m) := insert w (chiF w)

/-- The root bag: the tier-`1` cell, which has `N` members and no anchor. -/
def rootBag (N m : ℕ) : Finset (Addr N m) := tier1 N m

theorem bag_eq_anchored (w : Addr N m) : bag w = anchored w := rfl

theorem rootBag_eq_tier1 (N m : ℕ) : rootBag N m = tier1 N m := rfl

/-- The paper's opening sentence: the bags are cliques (the anchored cliques of
Lemma `lem:maxclique`), so the decomposition below is a *clique tree*. -/
theorem isClique_bag (w : Addr N m) :
    (graph N m).IsClique (bag w : Set (Addr N m)) := isClique_anchored w

/-- The root bag is a clique too: it is the tier-`1` cell. -/
theorem isClique_rootBag (N m : ℕ) :
    (graph N m).IsClique (rootBag N m : Set (Addr N m)) := isClique_tier1 N m

/-- The anchor of a node of tier `≥ 2`: its address with the last digit
dropped. -/
def anchorOf (v : Addr N m) (h : 2 ≤ v.tier) : Addr N m :=
  ⟨v.1.dropLast,
    by
      apply List.ne_nil_of_length_pos
      rw [List.length_dropLast]
      unfold Addr.tier at h
      omega,
    by
      rw [List.length_dropLast]
      have hle := Addr.tier_le v
      unfold Addr.tier at h hle
      omega⟩

theorem anchorOf_val (v : Addr N m) (h : 2 ≤ v.tier) :
    (anchorOf v h).1 = v.1.dropLast := rfl

theorem anchorOf_tier (v : Addr N m) (h : 2 ≤ v.tier) :
    v.tier = (anchorOf v h).tier + 1 := by
  show v.1.length = v.1.dropLast.length + 1
  rw [List.length_dropLast]
  unfold Addr.tier at h
  omega

/-- Membership in a bag, unfolded: `v` is in the bag of `w` exactly when it is
`w` itself or a member of the cell `w` spawns. -/
theorem mem_bag_iff (v w : Addr N m) :
    v ∈ bag w ↔ (v = w ∨ (v.1.length = w.1.length + 1 ∧ v.1.dropLast = w.1)) := by
  rw [← aux_mem_chiF]
  exact Finset.mem_insert

theorem mem_rootBag_iff (v : Addr N m) : v ∈ rootBag N m ↔ v.tier = 1 := by
  show v ∈ tier1 N m ↔ v.tier = 1
  simp [tier1]

/-- Every node lies in its own bag: `bag v` is the cell `v` spawns *together
with its anchor* `v`. This is the half of the running-intersection statement
that `coherence_idx` does not give, so that the indices whose bag contains `v`
are *exactly* `some v` and `treeParent v` and not merely contained in them. -/
theorem mem_bag_self (v : Addr N m) : v ∈ bag v := Finset.mem_insert_self v (chiF v)

/-! ## The index of the family is a tree (the cell tree) -/

/-- Index set of the bag family: `none` is the root bag (the tier-`1` cell),
`some w` is the cell spawned at `w`. -/
abbrev BagIdx (N m : ℕ) := Option (Addr N m)

/-- The bag attached to an index. -/
def bagAt : BagIdx N m → Finset (Addr N m)
  | none => rootBag N m
  | some w => bag w

/-- Parent map of the cell tree: the cell spawned at `w` hangs below the cell
that contains `w`, which is the cell of `w`'s anchor when `w` has tier `≥ 2`
and the tier-`1` cell otherwise. -/
def treeParent (w : Addr N m) : BagIdx N m :=
  if h : 2 ≤ w.tier then some (anchorOf w h) else none

/-- The parent map strictly decreases the tier, so the index really is a tree
(rooted at `none`, no cycles). -/
theorem treeParent_tier_lt (w w' : Addr N m) (h : treeParent w = some w') :
    w'.tier < w.tier := by
  unfold treeParent at h
  split_ifs at h with hw
  · injection h with h'
    subst h'
    have := anchorOf_tier w hw
    omega

/-- A tier-`1` node lies in the root bag (auxiliary copy, used before the
public statement below). -/
private theorem aux_mem_rootBag_of_tier_one (v : Addr N m) (h : v.tier = 1) :
    v ∈ rootBag N m := (mem_rootBag_iff v).mpr h

/-- A node of tier `≥ 2` lies in the bag of its anchor (auxiliary copy, used
before the public statement below). -/
private theorem aux_mem_bag_anchorOf (v : Addr N m) (h : 2 ≤ v.tier) :
    v ∈ bag (anchorOf v h) := by
  rw [mem_bag_iff]
  refine Or.inr ⟨?_, rfl⟩
  show v.1.length = v.1.dropLast.length + 1
  rw [List.length_dropLast]
  unfold Addr.tier at h
  omega

/-- Each cell's anchor lies in the parent cell's bag: this is the node shared
by two cells adjacent in the cell tree. -/
theorem mem_bagAt_treeParent (w : Addr N m) : w ∈ bagAt (treeParent w) := by
  unfold treeParent
  split_ifs with h
  · exact aux_mem_bag_anchorOf w h
  · have := Addr.one_le_tier w
    exact aux_mem_rootBag_of_tier_one w (by omega)

/-- Indexed form of `mem_bag_self`: `v` lies in the bag of its own cell. -/
theorem mem_bagAt_some_self (v : Addr N m) : v ∈ bagAt (some v) := mem_bag_self v

/-! ## (a) Vertex covering -/

/-- A tier-`1` node lies in the root bag. -/
theorem mem_rootBag_of_tier_one (v : Addr N m) (h : v.tier = 1) :
    v ∈ rootBag N m := (mem_rootBag_iff v).mpr h

/-- A node of tier `≥ 2` lies in the bag of its anchor. -/
theorem mem_bag_anchorOf (v : Addr N m) (h : 2 ≤ v.tier) :
    v ∈ bag (anchorOf v h) := aux_mem_bag_anchorOf v h

/-- **(a) Covering.** Every vertex lies in the root bag or in the bag of some
cell of which it is a member — namely the cell of its anchor. (The witness `w`
is pinned down by `v ∈ chiF w`, so this is not the trivial `v ∈ bag v`.) -/
theorem cover (v : Addr N m) :
    v ∈ rootBag N m ∨ ∃ w : Addr N m, v ∈ chiF w ∧ v ∈ bag w := by
  by_cases h : 2 ≤ v.tier
  · refine Or.inr ⟨anchorOf v h, ?_, mem_bag_anchorOf v h⟩
    refine aux_mem_chiF.mpr ⟨?_, rfl⟩
    show v.1.length = v.1.dropLast.length + 1
    rw [List.length_dropLast]
    unfold Addr.tier at h
    omega
  · have := Addr.one_le_tier v
    exact Or.inl (mem_rootBag_of_tier_one v (by omega))

/-! ## (b) Edge covering -/

/-- Sibling pairs of tier `≥ 2` sit in the bag of their common anchor. -/
theorem edge_cover_sib {u v : Addr N m} (hs : Sib u v) (h : 2 ≤ u.tier) :
    u ∈ bag (anchorOf u h) ∧ v ∈ bag (anchorOf u h) := by
  refine ⟨mem_bag_anchorOf u h, ?_⟩
  rw [mem_bag_iff]
  refine Or.inr ⟨?_, hs.2.symm⟩
  show v.1.length = u.1.dropLast.length + 1
  rw [List.length_dropLast, ← hs.1]
  unfold Addr.tier at h
  omega

/-- Sibling pairs of tier `1` sit in the root bag. -/
theorem edge_cover_sib_tier_one {u v : Addr N m} (hs : Sib u v) (h : u.tier = 1) :
    u ∈ rootBag N m ∧ v ∈ rootBag N m := by
  refine ⟨mem_rootBag_of_tier_one u h, mem_rootBag_of_tier_one v ?_⟩
  have hl := hs.1
  unfold Addr.tier at h ⊢
  omega

/-- Parent–child pairs sit in the bag of the parent. -/
theorem edge_cover_par {u v : Addr N m} (h : v ∈ chiF u) :
    u ∈ bag u ∧ v ∈ bag u := by
  refine ⟨?_, ?_⟩
  · exact Finset.mem_insert_self u (chiF u)
  · exact Finset.mem_insert_of_mem h

/-- **(b) Edge covering.** For every edge `{u,v}` of `graph N m` there is a bag
of the family containing both endpoints. -/
theorem edge_cover {u v : Addr N m} (h : (graph N m).Adj u v) :
    (u ∈ rootBag N m ∧ v ∈ rootBag N m) ∨ ∃ w : Addr N m, u ∈ bag w ∧ v ∈ bag w := by
  rcases h.2 with hS | hP
  · by_cases h2 : 2 ≤ u.tier
    · exact Or.inr ⟨anchorOf u h2, edge_cover_sib hS h2⟩
    · have := Addr.one_le_tier u
      exact Or.inl (edge_cover_sib_tier_one hS (by omega))
  · rcases hP with ⟨hl, hp⟩ | ⟨hl, hp⟩
    · exact Or.inr ⟨u, edge_cover_par (aux_mem_chiF.mpr ⟨hl, hp⟩)⟩
    · have hc := edge_cover_par (u := v) (v := u) (aux_mem_chiF.mpr ⟨hl, hp⟩)
      exact Or.inr ⟨v, hc.2, hc.1⟩

/-- **(b) Edge covering, indexed form.** -/
theorem edge_cover_idx {u v : Addr N m} (h : (graph N m).Adj u v) :
    ∃ i : BagIdx N m, u ∈ bagAt i ∧ v ∈ bagAt i := by
  rcases edge_cover h with ⟨hu, hv⟩ | ⟨w, hu, hv⟩
  · exact ⟨none, hu, hv⟩
  · exact ⟨some w, hu, hv⟩

/-! ## (c) Width -/

/-- Every bag has at most `N + 1` elements: the width of the decomposition is
at most `N`. -/
theorem card_bag_le (w : Addr N m) : (bag w).card ≤ N + 1 := by
  have h1 : (bag w).card ≤ (chiF w).card + 1 := Finset.card_insert_le w (chiF w)
  have h2 : (chiF w).card ≤ N := by
    rw [card_chi]
    split_ifs <;> omega
  omega

/-- A non-leaf bag attains the bound: it holds the anchor and all `N` members
of the cell it spawns. -/
theorem card_bag_of_lt (w : Addr N m) (h : w.tier < m) : (bag w).card = N + 1 :=
  card_anchored w h

/-- A leaf spawns no cell, so its bag is the singleton `{w}`. -/
theorem card_bag_of_leaf (w : Addr N m) (h : ¬ w.tier < m) : (bag w).card = 1 := by
  have hchi : chiF w = ∅ := by
    rw [← Finset.card_eq_zero, card_chi, if_neg h]
  show (insert w (chiF w)).card = 1
  rw [hchi]
  simp

/-- The root bag has exactly `N` elements: the tier-`1` cell has no anchor. -/
theorem card_rootBag (N m : ℕ) (hm : 1 ≤ m) : (rootBag N m).card = N :=
  card_tier1 N m hm

/-- **(c) Width.** Every bag of the family, root included, has at most `N + 1`
elements. -/
theorem card_bagAt_le (i : BagIdx N m) : (bagAt i).card ≤ N + 1 := by
  cases i with
  | none => exact card_le_of_isClique (rootBag N m) (isClique_rootBag N m)
  | some w => exact card_bag_le w

/-- The width bound `N` is attained by this decomposition when `m ≥ 2`, so
`card_bag_le` is not vacuously loose: some bag really has `N + 1` elements.
(Together with `HSFN.cliqueNum_eq` this is why the paper's `tw(F(N,m)) = N` for
`m ≥ 2` cannot be improved; the lower bound itself needs a treewidth API and is
not claimed here.) -/
theorem exists_card_bag_eq (hN : 1 ≤ N) (hm : 2 ≤ m) :
    ∃ w : Addr N m, (bag w).card = N + 1 := by
  let z : Addr N m := ⟨[⟨0, hN⟩], by simp, by
    simp only [List.length_cons, List.length_nil]
    omega⟩
  have hz1 : z.tier = 1 := by
    show ([(⟨0, hN⟩ : Fin N)] : List (Fin N)).length = 1
    simp
  exact ⟨z, card_bag_of_lt z (by omega)⟩

/-- At `m = 1` every node is a leaf, so every bag is a singleton and the only
bag of size `> 1` is the root bag, of size `N`: the decomposition has width
`N - 1` there, matching the paper's `tw(F(N,1)) = N-1` (upper half). Stated
subtraction-free as `card ≤ N`. -/
theorem card_bagAt_le_of_m_one (i : BagIdx N 1) : (bagAt i).card ≤ N := by
  cases i with
  | none => exact (card_rootBag N 1 le_rfl).le
  | some w =>
      have hleaf : ¬ w.tier < 1 := by
        have := Addr.one_le_tier w
        omega
      have hN := Addr.N_pos w
      show (bag w).card ≤ N
      rw [card_bag_of_leaf w hleaf]
      omega

/-! ## (d) Coherence (running intersection along the cell tree) -/

/-- **(d) Coherence.** If `v` lies in the bag of `w`, then `w` is `v` itself or
`w` is `v`'s anchor. Hence the bags containing a fixed `v` are exactly the bag
of `v`'s anchor and, when `v` is not a leaf, the bag of `v` — two cells adjacent
in the cell tree — plus the root bag when `v` has tier `1`. -/
theorem coherence {v w : Addr N m} (h : v ∈ bag w) : w = v ∨ v.1.dropLast = w.1 := by
  rcases (mem_bag_iff v w).mp h with rfl | ⟨-, hp⟩
  · exact Or.inl rfl
  · exact Or.inr hp

/-- Sharper form of (d): the only bag other than `v`'s own that contains `v` is
the bag of `v`'s anchor. -/
theorem eq_anchorOf_of_mem_bag {v w : Addr N m} (hv : 2 ≤ v.tier) (h : v ∈ bag w)
    (hne : w ≠ v) : w = anchorOf v hv := by
  rcases (mem_bag_iff v w).mp h with rfl | ⟨-, hp⟩
  · exact absurd rfl hne
  · exact Addr.ext hp.symm

/-- At tier `1` there is no anchor, so no bag `bag w` with `w ≠ v` contains
`v`: such a `v` is covered by the root bag (and by `bag v`) alone. -/
theorem eq_self_of_mem_bag_of_tier_one {v w : Addr N m} (h1 : v.tier = 1)
    (h : v ∈ bag w) : w = v := by
  rcases (mem_bag_iff v w).mp h with rfl | ⟨hl, -⟩
  · rfl
  · exfalso
    have := Addr.one_le_tier w
    unfold Addr.tier at h1 this
    omega

/-- **(d) Coherence, root bag.** The root bag holds exactly the tier-`1` nodes,
which is the half of (d) that concerns the index `none`. -/
theorem coherence_rootBag {v : Addr N m} (h : v ∈ rootBag N m) : v.tier = 1 :=
  (mem_rootBag_iff v).mp h

/-- **(d) Running intersection along the cell tree, indexed form.** The indices
whose bag contains `v` are exactly `some v` and `treeParent v`, which are
adjacent in the cell tree (`mem_bagAt_treeParent`, `treeParent_tier_lt`). Hence
the set of bags containing a fixed vertex is connected in the index tree — the
tree-decomposition axiom that `coherence` alone does not express, because
`coherence` says nothing about the root bag. -/
theorem coherence_idx (i : BagIdx N m) (v : Addr N m) (h : v ∈ bagAt i) :
    i = some v ∨ i = treeParent v := by
  cases i with
  | none =>
      refine Or.inr ?_
      have h1 : v.tier = 1 := coherence_rootBag h
      unfold treeParent
      rw [dif_neg (by omega : ¬ 2 ≤ v.tier)]
  | some w =>
      by_cases hw : w = v
      · exact Or.inl (by rw [hw])
      · refine Or.inr ?_
        have h' : v ∈ bag w := h
        have hv2 : 2 ≤ v.tier := by
          rcases (mem_bag_iff v w).mp h' with rfl | ⟨hl, -⟩
          · exact absurd rfl hw
          · have := Addr.one_le_tier w
            unfold Addr.tier at this ⊢
            omega
        unfold treeParent
        rw [dif_pos hv2, eq_anchorOf_of_mem_bag hv2 h' hw]

/-- The paper's "adjacent cells share exactly their common anchor node", for
two cells adjacent in the cell tree. -/
theorem bag_inter_parent (w : Addr N m) (h : 2 ≤ w.tier) :
    bag (anchorOf w h) ∩ bag w = {w} := by
  have hlen : (anchorOf w h).1.length + 1 = w.1.length := by
    have ht := anchorOf_tier w h
    unfold Addr.tier at ht
    omega
  ext x
  rw [Finset.mem_inter, mem_bag_iff, mem_bag_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hA, hB⟩
    rcases hB with hxw | ⟨hlx, -⟩
    · exact hxw
    · exfalso
      rcases hA with rfl | ⟨hlx', -⟩
      · omega
      · omega
  · rintro rfl
    exact ⟨Or.inr ⟨by omega, rfl⟩, Or.inl rfl⟩

/-- The same, for a tier-`1` cell and the root cell. -/
theorem rootBag_inter_bag (w : Addr N m) (h : w.tier = 1) :
    rootBag N m ∩ bag w = {w} := by
  ext x
  rw [Finset.mem_inter, mem_rootBag_iff, mem_bag_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hx1, hB⟩
    rcases hB with hxw | ⟨hlx, -⟩
    · exact hxw
    · exfalso
      unfold Addr.tier at hx1 h
      omega
  · rintro rfl
    exact ⟨h, Or.inl rfl⟩

/-! ## The decomposition -/

/-- **Lemma lem:tw-nec, upper bound.** The bags `bag w` (one per cell of the
cell tree, `rootBag` for the tier-`1` cell), indexed by the cell tree with
parent map `treeParent`, form a tree decomposition of `graph N m` of width at
most `N`: (a) every vertex is covered, by the bag of its anchor or by the root
bag; (b) every edge is covered by a single bag; (c) every bag has at most
`N + 1` elements and the root bag has exactly `N`; (d) the bags containing a
fixed vertex are coherent along the cell tree — a bag containing `v` is indexed
by `v` itself or by `v`'s anchor, the root bag holds only tier-`1` nodes, the
indices whose bag contains `v` are exactly the tree-adjacent pair
`some v`, `treeParent v` (both of which really do contain `v`), and `treeParent`
strictly decreases the tier, so the index is a genuine rooted tree. -/
theorem tw_le (N m : ℕ) (hm : 1 ≤ m) :
    -- (a) covering
    (∀ v : Addr N m, v ∈ rootBag N m ∨ ∃ w : Addr N m, v ∈ chiF w ∧ v ∈ bag w) ∧
    -- (b) edge covering
    (∀ u v : Addr N m, (graph N m).Adj u v →
        (u ∈ rootBag N m ∧ v ∈ rootBag N m) ∨
          ∃ w : Addr N m, u ∈ bag w ∧ v ∈ bag w) ∧
    -- (c) width at most `N`: every bag of the family, root included, has order
    -- at most `N + 1`, and the root bag has order exactly `N`
    ((∀ i : BagIdx N m, (bagAt i).card ≤ N + 1) ∧
      (∀ w : Addr N m, (bag w).card ≤ N + 1) ∧ (rootBag N m).card = N) ∧
    -- (d) coherence / running intersection along the cell tree: a bag
    -- containing `v` is indexed by `v` or by `v`'s anchor; the root bag holds
    -- only tier-`1` nodes; the indices holding `v` are `some v` and
    -- `treeParent v`, adjacent in the tree; and `treeParent` is acyclic
    ((∀ v w : Addr N m, v ∈ bag w → w = v ∨ v.1.dropLast = w.1) ∧
      (∀ v : Addr N m, v ∈ rootBag N m → v.tier = 1) ∧
      (∀ (i : BagIdx N m) (v : Addr N m), v ∈ bagAt i → i = some v ∨ i = treeParent v) ∧
      (∀ v : Addr N m, v ∈ bagAt (some v)) ∧
      (∀ v : Addr N m, v ∈ bagAt (treeParent v)) ∧
      (∀ w w' : Addr N m, treeParent w = some w' → w'.tier < w.tier)) := by
  refine ⟨fun v => cover v, fun u v h => edge_cover h,
    ⟨fun i => card_bagAt_le i, fun w => card_bag_le w, card_rootBag N m hm⟩,
    fun v w h => coherence h, fun v h => coherence_rootBag h,
    fun i v h => coherence_idx i v h, fun v => mem_bagAt_some_self v,
    fun v => mem_bagAt_treeParent v,
    fun w w' h => treeParent_tier_lt w w' h⟩

end TreeDecomp

end HSFN

