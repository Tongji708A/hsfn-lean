/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Mathlib
import Hsfnlean.Dense
import Hsfnlean.DenseUpdate

/-!
# The dense-variant node set really has `Dense.V N m` elements
(Theorem thm:node-count, Proposition prop:consensus-tree(1))

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

`Hsfnlean.Dense` proves the counting identities of Theorem thm:node-count about
the plain `ℕ`-recursion `Dense.V N m`, and `Hsfnlean.DenseUpdate` defines the
node type `DenseUpdate.DNode N m` of the dense variant (a consensus label `ℓ`,
valid for the grammar of Section subsec:duality and of length `≤ m-1`, together
with the index `i : Fin N` of the vertex `v_{ℓ,(i,0)}` inside the cell `Θ_ℓ`).
Nothing connected the two, so Theorem thm:node-count was a fact about a
recursion rather than about the node type.  This file closes that gap: the
counts below are theorems about `Fintype.card (DNode N m)`.  The step that
remains open is the one from the node type to the geometry of Definition
def:iteration; it is *not* taken here (see the scope boundaries at the end).

Proved here:

* `card_validVector` — **item (a)**, the per-length count against the *actual*
  validity predicate `DenseUpdate.Valid`: for `1 ≤ l` the length-`l` valid
  labels number `Dense.E N l = N (2N-2)^{l-1}`.  Stated as
  `Fintype.card {v : List.Vector (Fin N × Bool) l // Valid v.toList} = Dense.E N l`.
  The `N` comes from the first pair, whose `Bool` the grammar pins to `false`,
  and each later pair contributes `2(N-1)` because the veto forbids repeating
  the previous first component while its `Bool` is free
  (`length_childRaw_nil`, `length_childRaw_of_ne_nil`).
* `card_DNode` — **item (b)**, `Fintype.card (DNode N m) = Dense.V N m` for
  `m ≥ 1`; with `card_DNode_eq` the subtraction-free intermediate form
  `Fintype.card (DNode N m) = (allLabels N m).card * N`.
* `N_dvd_card_DNode` — **item (c)**, first corollary: `N` divides the node
  count of the network (from `Dense.N_dvd_V`).
* `card_CNode_mul`, `card_CNode`, `card_CNode_eq_V_div` — **item (c)**, second
  corollary and **Proposition prop:consensus-tree item (1)**: the consensus
  nodes of the depth-`m` dense variant (`CNode N m`, the valid labels of length
  `≤ m-1`, i.e. the cells `Θ_ℓ` of Definition def:consensus-node) number
  `Fintype.card (DNode N m) / N = Dense.V N m / N` for `N ≥ 1`, in the
  hypothesis-free and division-free form
  `Fintype.card (CNode N m) * N = Fintype.card (DNode N m)`.

Supporting material: `labels N l` (the valid labels of length exactly `l`, as a
`Finset`) with `mem_labels`, `card_labels_succ`, `card_labels`; `allLabels N m`
(the consensus labels) with `mem_allLabels`, `card_allLabels`.  The recursion
`labels N (l+1) = ⋃_{ℓ} childRaw N ℓ` reuses `DenseUpdate.childRaw`,
`mem_childRaw_iff`, `childRaw_nodup` and `aux_valid_prefix` rather than
re-deriving the grammar, and the two branching numbers are read off
`DenseUpdate.length_childList_root` / `length_childList_of_ne_nil`.

Still **not** covered (deliberate scope boundaries, inherited from
`Hsfnlean.DenseUpdate`):

* The geometry.  Facets `e_ℓ`, the vertices `v_{ℓ,(i,0)}` and the subdivision
  of Definition def:iteration are not modelled; `Valid` is taken as the
  *definition* of a label, exactly as Section subsec:duality states it, and the
  claim that it is the label set of the geometric construction is not proved.
  Equally, `CNode N m` is the label-level cell, not a proved quotient of a
  geometric vertex set: Definition def:consensus-node's map `π` is not built
  here (it is the first projection of `DNode`, but nothing identifies that with
  the geometric quotient).
* The closed form eq:closed-form and the asymptotics stay where they are, in
  `Hsfnlean.Dense` (`V_closed`, `V_bounds`), stated for the recursion `V`; this
  file transports them to `Fintype.card (DNode N m)` only through the equation
  `card_DNode`, and does not restate them.
* Of Proposition prop:consensus-tree, item (1) is proved here and items (2),(3)
  in `Hsfnlean.DenseUpdate`; item (4) (the level-`n` count) exists only in the
  recursion form `Dense.level_count` and is **not** proved here for the level
  sets of `CNode`, and item (5) (the depth of the tree is `m`) is not proved at
  all.
* The facet count `|E_{N,m}|` is identified with a count of *labels*
  (`card_validVector`), not with a count of facets of a simplicial complex.
* Nothing here is about the graphs, the protocol or the probabilistic content
  of the paper.
* This module is **not** imported by the root `Hsfnlean.lean`, so it is not
  built by `lake build` and its statements are not part of the `AxiomCheck`
  audit; it has been checked only with `lake env lean` on this file.  Adding
  the import line is left to whoever owns `Hsfnlean.lean`.
-/

namespace HSFN.DenseCard

open HSFN.DenseUpdate

variable {N m : ℕ}

/-! ### The valid labels of a fixed length -/

/-- The valid dense-variant labels of length exactly `l`, built by the child
recursion of `DenseUpdate.childRaw`. -/
def labels (N : ℕ) : ℕ → Finset (List (Fin N × Bool))
  | 0 => {[]}
  | l + 1 => (labels N l).biUnion fun ℓ => (childRaw N ℓ).toFinset

/-- `labels N l` is exactly the set of valid labels of length `l`. -/
theorem mem_labels (l : ℕ) (ℓ : List (Fin N × Bool)) :
    ℓ ∈ labels N l ↔ Valid ℓ ∧ ℓ.length = l := by
  induction l generalizing ℓ with
  | zero =>
      simp only [labels, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨trivial, rfl⟩
      · rintro ⟨-, h⟩
        exact List.eq_nil_of_length_eq_zero h
  | succ l ih =>
      simp only [labels, Finset.mem_biUnion]
      constructor
      · rintro ⟨p, hp, hc⟩
        have hpv := (ih p).mp hp
        obtain ⟨⟨q, rfl⟩, hv⟩ := (mem_childRaw_iff p hpv.1 ℓ).mp (List.mem_toFinset.mp hc)
        exact ⟨hv, by simp [hpv.2]⟩
      · rintro ⟨hv, hlen⟩
        have hne : ℓ ≠ [] := by
          intro h
          rw [h] at hlen
          simp at hlen
        have hpv : Valid ℓ.dropLast := aux_valid_prefix hv ℓ.dropLast_prefix
        refine ⟨ℓ.dropLast, (ih _).mpr ⟨hpv, ?_⟩, ?_⟩
        · rw [List.length_dropLast, hlen]
          simp
        · refine List.mem_toFinset.mpr ((mem_childRaw_iff _ hpv ℓ).mpr ⟨⟨ℓ.getLast hne, ?_⟩, hv⟩)
          exact (List.dropLast_append_getLast hne).symm

/-! ### The two branching numbers, for `childRaw` -/

/-- The root has `N` children (Proposition prop:consensus-tree(2), in the
cutoff-free form used for counting). -/
theorem length_childRaw_nil (N : ℕ) : (childRaw N ([] : List (Fin N × Bool))).length = N := by
  have h := length_childList_root N 2 (by omega)
  rwa [childList, if_neg (by simp)] at h

/-- Every non-root label has `2(N-1)` children (Proposition
prop:consensus-tree(3), in the cutoff-free form used for counting), stated
subtraction-free as `len + 2 = 2N`. -/
theorem length_childRaw_of_ne_nil (N : ℕ) (ℓ : List (Fin N × Bool)) (hne : ℓ ≠ []) :
    (childRaw N ℓ).length + 2 = 2 * N := by
  have h := length_childList_of_ne_nil N (ℓ.length + 2) ℓ hne (by omega)
  rwa [childList, if_neg (by omega)] at h

/-- Children of distinct labels are distinct: the parent is recoverable as
`dropLast`. -/
theorem childRaw_disjoint (N : ℕ) (ℓ₁ ℓ₂ : List (Fin N × Bool)) (h : ℓ₁ ≠ ℓ₂) :
    Disjoint (childRaw N ℓ₁).toFinset (childRaw N ℓ₂).toFinset := by
  refine Finset.disjoint_left.mpr ?_
  intro c hc₁ hc₂
  obtain ⟨p₁, rfl⟩ := aux_childRaw_append N ℓ₁ c (List.mem_toFinset.mp hc₁)
  obtain ⟨p₂, hp₂⟩ := aux_childRaw_append N ℓ₂ _ (List.mem_toFinset.mp hc₂)
  exact h (by simpa using congrArg List.dropLast hp₂)

/-! ### (a) The count of valid labels of a fixed length -/

/-- The number of valid labels of length `l+1`: `N` choices for the first pair
(its `Bool` is pinned to `false`) times `2(N-1)` for each later pair. -/
theorem card_labels_succ (N l : ℕ) : (labels N (l + 1)).card = N * (2 * N - 2) ^ l := by
  induction l with
  | zero =>
      simp only [labels, Finset.singleton_biUnion]
      rw [List.toFinset_card_of_nodup (childRaw_nodup N []), length_childRaw_nil]
      simp
  | succ l ih =>
      have hdisj : ((labels N (l + 1) : Finset (List (Fin N × Bool))) :
          Set (List (Fin N × Bool))).PairwiseDisjoint
          (fun ℓ => (childRaw N ℓ).toFinset) := by
        intro x _ y _ hxy
        exact childRaw_disjoint N x y hxy
      have hconst : ∀ ℓ ∈ labels N (l + 1),
          ((childRaw N ℓ).toFinset).card = 2 * N - 2 := by
        intro ℓ hℓ
        have hlen := ((mem_labels (l + 1) ℓ).mp hℓ).2
        have hne : ℓ ≠ [] := by
          intro hc
          rw [hc] at hlen
          simp at hlen
        rw [List.toFinset_card_of_nodup (childRaw_nodup N ℓ)]
        have := length_childRaw_of_ne_nil N ℓ hne
        omega
      show (Finset.biUnion (labels N (l + 1)) fun ℓ => (childRaw N ℓ).toFinset).card = _
      rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hconst, Finset.sum_const,
        smul_eq_mul, ih, pow_succ, mul_assoc]

/-- The number of valid labels of length `l ≥ 1` is `Dense.E N l = N (2N-2)^{l-1}`. -/
theorem card_labels (N l : ℕ) (hl : 1 ≤ l) : (labels N l).card = Dense.E N l := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hl
  rw [Nat.add_comm 1 k, card_labels_succ, Dense.E]
  simp

/-- **Theorem thm:node-count, item (a)**: for `1 ≤ l` the valid dense-variant
labels of length `l` number `Dense.E N l = N (2N-2)^{l-1}`.  This is stated
against the grammar `DenseUpdate.Valid` itself: a length-`l` word of pairs
`(r, b) : Fin N × Bool` is valid when the first `b` is `false` and consecutive
first components differ. -/
theorem card_validVector (N l : ℕ) (hl : 1 ≤ l) :
    Fintype.card { v : List.Vector (Fin N × Bool) l // Valid v.toList } = Dense.E N l := by
  have hbij : Function.Bijective
      (fun v : { v : List.Vector (Fin N × Bool) l // Valid v.toList } =>
        (⟨v.1.toList, (mem_labels l v.1.toList).mpr ⟨v.2, v.1.2⟩⟩ :
          { x // x ∈ labels N l })) := by
    constructor
    · intro a b h
      have h1 : a.1.toList = b.1.toList :=
        congrArg (fun p : { x // x ∈ labels N l } => (p : List (Fin N × Bool))) h
      exact Subtype.ext (Subtype.ext h1)
    · rintro ⟨x, hx⟩
      obtain ⟨hv, hlen⟩ := (mem_labels l x).mp hx
      exact ⟨⟨⟨x, hlen⟩, hv⟩, rfl⟩
  rw [Fintype.card_of_bijective hbij, Fintype.card_coe, card_labels N l hl]

/-! ### The consensus labels -/

/-- The consensus labels of the depth-`m` dense variant: the valid labels of
length `≤ m-1` (stated as `|ℓ| + 1 ≤ m`), that is the cells `Θ_ℓ` of
Definition def:consensus-node. -/
def allLabels (N m : ℕ) : Finset (List (Fin N × Bool)) :=
  (Finset.range m).biUnion (labels N)

theorem mem_allLabels (ℓ : List (Fin N × Bool)) :
    ℓ ∈ allLabels N m ↔ Valid ℓ ∧ ℓ.length + 1 ≤ m := by
  simp only [allLabels, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨l, hl, h⟩
    obtain ⟨hv, hlen⟩ := (mem_labels l ℓ).mp h
    exact ⟨hv, by omega⟩
  · rintro ⟨hv, hlen⟩
    exact ⟨ℓ.length, by omega, (mem_labels _ ℓ).mpr ⟨hv, rfl⟩⟩

theorem card_allLabels (N m : ℕ) :
    (allLabels N m).card = ∑ l ∈ Finset.range m, (labels N l).card := by
  refine Finset.card_biUnion ?_
  intro x _ y _ hxy
  refine Finset.disjoint_left.mpr ?_
  intro c hc₁ hc₂
  exact hxy ((((mem_labels x c).mp hc₁).2).symm.trans (((mem_labels y c).mp hc₂).2))

/-! ### (b) The node count of the dense variant -/

/-- Subtraction-free shape of the node count: `|V_{N,m}|` is `N` times the
number of consensus labels. -/
theorem card_DNode_eq (N m : ℕ) :
    Fintype.card (DNode N m) = (allLabels N m).card * N := by
  have hbij : Function.Bijective
      (fun x : DNode N m =>
        ((⟨x.1.1, (mem_allLabels x.1.1).mpr x.2⟩ : { y // y ∈ allLabels N m }), x.1.2)) := by
    constructor
    · intro a b h
      refine DNode.ext (Prod.ext ?_ ?_)
      · exact congrArg (fun p => (p.1 : List (Fin N × Bool))) h
      · exact congrArg (fun p => p.2) h
    · rintro ⟨⟨x, hx⟩, i⟩
      exact ⟨⟨(x, i), (mem_allLabels x).mp hx⟩, rfl⟩
  rw [Fintype.card_of_bijective hbij, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]

/-- **Theorem thm:node-count, item (b)**: the dense-variant node set of depth
`m ≥ 1` has exactly `Dense.V N m` elements, so the counting identities of
`Hsfnlean.Dense` are identities about the network. -/
theorem card_DNode (N m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (DNode N m) = Dense.V N m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [card_DNode_eq, card_allLabels, Finset.sum_range_succ']
  have hcards : ∀ i ∈ Finset.range m', (labels N (i + 1)).card = Dense.E N (i + 1) :=
    fun i _ => card_labels N (i + 1) (by omega)
  rw [Finset.sum_congr rfl hcards]
  have hV := Dense.V_eq_sum N (m' + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hV
  have h0 : (labels N 0).card = 1 := by simp [labels]
  rw [hV, h0]
  ring

/-! ### (c) The two corollaries the paper draws -/

/-- **Theorem thm:node-count, first corollary**: `N` divides the node count of
the depth-`m` dense variant. -/
theorem N_dvd_card_DNode (N m : ℕ) (hm : 1 ≤ m) : N ∣ Fintype.card (DNode N m) := by
  rw [card_DNode N m hm]
  exact Dense.N_dvd_V N m

/-- A consensus node of the depth-`m` dense variant: a valid label of length
`≤ m-1`, that is a cell `Θ_ℓ` of Definition def:consensus-node. -/
def CNode (N m : ℕ) : Type :=
  { ℓ : List (Fin N × Bool) // Valid ℓ ∧ ℓ.length + 1 ≤ m }

instance : Fintype (CNode N m) :=
  Fintype.subtype (allLabels N m) (fun x => mem_allLabels x)

theorem card_CNode_eq (N m : ℕ) : Fintype.card (CNode N m) = (allLabels N m).card := by
  have hbij : Function.Bijective (fun x : CNode N m =>
      (⟨x.1, (mem_allLabels x.1).mpr x.2⟩ : { y // y ∈ allLabels N m })) := by
    constructor
    · intro a b h
      exact Subtype.ext (congrArg (fun p : { y // y ∈ allLabels N m } =>
        (p : List (Fin N × Bool))) h)
    · rintro ⟨x, hx⟩
      exact ⟨⟨x, (mem_allLabels x).mp hx⟩, rfl⟩
  rw [Fintype.card_of_bijective hbij, Fintype.card_coe]

/-- **Proposition prop:consensus-tree(1)**, division-free: the consensus nodes
carry `N` network nodes each and together exhaust the node set. -/
theorem card_CNode_mul (N m : ℕ) :
    Fintype.card (CNode N m) * N = Fintype.card (DNode N m) := by
  rw [card_CNode_eq, card_DNode_eq]

/-- **Proposition prop:consensus-tree(1)**: the total number of consensus nodes
is `|V_{N,m}|/N`. -/
theorem card_CNode (N m : ℕ) (hN : 1 ≤ N) :
    Fintype.card (CNode N m) = Fintype.card (DNode N m) / N := by
  rw [← card_CNode_mul N m, Nat.mul_div_cancel _ hN]

/-- The same count against the closed-form recursion of `Hsfnlean.Dense`. -/
theorem card_CNode_eq_V_div (N m : ℕ) (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Fintype.card (CNode N m) = Dense.V N m / N := by
  rw [card_CNode N m hN, card_DNode N m hm]

end HSFN.DenseCard
