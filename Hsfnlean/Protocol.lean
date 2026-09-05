/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Mathlib
import Hsfnlean.DenseUpdate

/-!
# The dense-variant protocol graph: degrees, links, connectivity

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

This module formalizes Definition *Dense-variant protocol graph*, Theorem
`thm:deg-I` (protocol degrees and links, dense variant) and Proposition
`prop:conn-price`(ii) (the dense-variant protocol graph is `N`-connected).

The paper defines `G^prot_I(N,m)` on the dense-variant node set `V_{N,m}`
through the quotient map `π` onto the consensus cells and the consensus tree
`T_{N,m}` (Proposition `prop:consensus-tree`): distinct nodes `u, v` are
adjacent iff `π u = π v` (intra-cell) or `{π u, π v}` is a parent-child pair of
`T_{N,m}` (inter-cell). Only two facts about `T_{N,m}` are used: each cell holds
exactly `N` members, and the cells form a rooted tree. We therefore model the
graph abstractly, exactly as the paper does: the vertex set is `C × Fin N` with
`C` the cell type, `parent : C → Option C` the cell tree (the root being the
cell with `parent = none`), and adjacency `PAdj` the two-clause law above. Each
cell then induces a `K_N` and each tree edge a `K_{N,N}`, as the paper states.
The abstract cell type is not left abstract: the last section instantiates it at
the paper's consensus tree `T_{N,m}` and restates the degree and connectivity
results there, so that they are statements about `G^prot_I(N,m)` itself.

Contents.

* `PAdj`, `pgraph` — the protocol graph.
* `RootedTree` — the cell tree hypothesis: every cell reaches the root `r` by
  iterating `parent`. This is the paper's `T_{N,m}`.
* `degree_eq` — Theorem `thm:deg-I`(i) in the general form
  `deg (c,i) = (N-1) + [parent c ≠ none] * N + (#children c) * N`, with the
  paper's three classes as `degree_root` (`N^2 + N - 1`, root cell, `N`
  children), `degree_internal` (`2N^2 - 1`, non-root cell with `2(N-1)`
  children) and `degree_leaf` (`2N - 1`, non-root childless cell).
* `two_mul_card_edges` — Theorem `thm:deg-I`(ii), the handshake form of
  `|E_I| = (V/N) * C(N,2) + N^2 (V/N - 1)`: twice the edge count is
  `|C| * N(N-1) + 2N^2 * #(non-root cells)`.
* `induce_compl_reachable` — Proposition `prop:conn-price`(ii), lower bound:
  deleting fewer than `N` vertices leaves the graph connected. The supporting
  lemmas are `exists_survivor`, `adj_same_cell` and `adj_parent_child`.
* `card_cell`, `leaf_cell_separated` — the matching upper bound: a cell has `N`
  members and deleting the `N` members of a leaf cell's parent isolates it.
* `card_nonRoot`, `two_mul_card_edges'` — `#(non-root cells) = |C| - 1`, giving
  the edge count in the paper's own shape `V/N - 1`.

The abstraction is then discharged against the paper's own object, in the
section *The paper's instance* at the end of the file.

* `Cell N m` — the consensus cells of the depth-`m` dense variant, namely the
  valid subscript-pair labels of `Hsfnlean.DenseUpdate` of length at most `m-1`
  (Definition `def:consensus-node`); `parentCell` drops the last subscript pair,
  and `dnodeEquivCell : DNode N m ≃ Cell N m × Fin N` identifies the vertex type
  of `pgraph (Cell N m) (parentCell N m) N` with the paper's node set `V_{N,m}`.
* `rootedTree_dense` — the labels do form a rooted tree with root `Θ_(0,0)`, so
  the `RootedTree` hypothesis of every theorem above is discharged, not assumed.
* `image_children_eq`, `card_children_eq` — the children of a cell are exactly
  the entries of the paper's ordered child list `𝓒_m(ℓ)` of eq:app-children,
  whence `card_children_root` (`N`), `card_children_internal` (`2(N-1)`) and
  `card_children_leaf` (`0`) from `DenseUpdate.length_childList_root` and
  `DenseUpdate.length_childList_of_ne_nil`, that is Proposition
  `prop:consensus-tree`(2)–(3).
* `dense_degree_root`, `dense_degree_internal`, `dense_degree_leaf` — Theorem
  `thm:deg-I`(i) for `G^prot_I(N,m)` itself: `N^2 + N - 1`, `2N^2 - 1` and
  `2N - 1`, with **no** branching hypothesis left to the reader; the only
  hypotheses are the paper's own `N ≥ 3`, `m ≥ 2` and the position of the cell
  in `T_{N,m}` (empty label / non-empty and `|ℓ| + 1 < m` / non-empty and
  `|ℓ| + 1 = m`). Likewise `dense_two_mul_card_edges` (`thm:deg-I`(ii)),
  `dense_induce_compl_reachable` and `dense_leaf_cell_separated`
  (`prop:conn-price`(ii), both halves).
* `exists_internal_cell`, `exists_degree_internal` — the internal class is
  non-empty for `m ≥ 3`, so the `2N^2 - 1` degree is actually attained.

Not formalized here (named honestly, so that no reader over-reads the file).

* The tier bookkeeping of `thm:deg-I`(i) is only half done. The *if* direction
  is proved — `exists_internal_cell` / `exists_degree_internal` exhibit a
  non-root, non-last-tier cell whenever `m ≥ 3`, so `dense_degree_internal` is
  not vacuous — but the converse (that `m ≥ 3` is also *necessary* for the
  internal class to be populated) is not proved, the non-emptiness of the leaf
  class is not proved, and the `m = 1` boundary case `K_N` with all degrees
  `N-1` is not stated.
* `Fintype.card (Cell N m)`, the cell count `V/N` of Proposition
  `prop:consensus-tree`(1), is never evaluated to a closed form, so
  `dense_two_mul_card_edges` carries it symbolically. This mirrors the
  corresponding gap in `Hsfnlean.DenseUpdate`.
* Vertex connectivity is not stated as a numerical invariant `κ = N`. Proposition
  `prop:conn-price`(ii) is formalized as its two defining halves: the lower bound
  `induce_compl_reachable` (a full connectivity statement) and the upper bound
  `leaf_cell_separated` (a non-reachability statement) together with `card_cell`.
  Assembling these into `κ = N` in mathlib's vocabulary is not done.
* Proposition `prop:conn-price`(i), the HSFN cut-vertex law, is not in this file;
  it belongs to the `Addr`-based modules.
* The protocol provenance of the graph (the multi-layer PBFT message pairs of
  Section `subsec:multi-pbft` that justify clauses (i) and (ii)) is a modelling
  assumption, not a theorem.
-/

namespace HSFN.Protocol

open Finset

-- The section variables `[Fintype C]`, `[DecidableEq C]` are part of the frozen
-- statements below; a few of them do not use every instance.
set_option linter.unusedSectionVars false

variable (C : Type*) [Fintype C] [DecidableEq C] (parent : C → Option C) (N : ℕ)

/-! ## The protocol graph -/

/-- Adjacency of the dense-variant protocol graph: distinct members are adjacent
iff they sit in the same cell (intra-cell, clause (i)) or their cells form a
parent-child pair of the cell tree (inter-cell, clause (ii)). -/
def PAdj (u v : C × Fin N) : Prop :=
  u ≠ v ∧ (u.1 = v.1 ∨ parent u.1 = some v.1 ∨ parent v.1 = some u.1)

instance decidablePAdj : DecidableRel (PAdj C parent N) := fun u v =>
  decidable_of_iff
    (u ≠ v ∧ (u.1 = v.1 ∨ parent u.1 = some v.1 ∨ parent v.1 = some u.1)) Iff.rfl

/-- The dense-variant protocol graph `G^prot_I` on `C × Fin N`. -/
def pgraph : SimpleGraph (C × Fin N) where
  Adj := PAdj C parent N
  symm := by
    constructor
    rintro u v ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := by
    constructor
    rintro u ⟨hne, -⟩
    exact hne rfl

instance decidablePgraphAdj : DecidableRel (pgraph C parent N).Adj := fun u v =>
  decidable_of_iff (PAdj C parent N u v) Iff.rfl

/-- One step up the cell tree. -/
def up : Option C → Option C := fun o => o.bind parent

/-- The cell tree of the paper: `r` is a root and every cell reaches `r` by
iterating `parent`. This is `T_{N,m}` of Proposition `prop:consensus-tree`. -/
def RootedTree (r : C) : Prop :=
  parent r = none ∧ ∀ c : C, ∃ n : ℕ, (up C parent)^[n] (some c) = some r

/-- The children of a cell in the cell tree. -/
def children (c : C) : Finset C :=
  univ.filter fun d => parent d = some c

/-- The non-root cells, i.e. the cells carrying a parent-side `K_{N,N}`. -/
def nonRoot : Finset C :=
  univ.filter fun c => parent c ≠ none

/-! ## Auxiliary facts about the cell tree -/

/-- Adjacency of `pgraph`, unfolded. -/
private theorem aux_padj_iff (u v : C × Fin N) :
    (pgraph C parent N).Adj u v ↔
      u ≠ v ∧ (u.1 = v.1 ∨ parent u.1 = some v.1 ∨ parent v.1 = some u.1) :=
  Iff.rfl

/-- One step up from a cell. -/
private theorem aux_up_some (c : C) : up C parent (some c) = parent c := rfl

/-- The root absorbs every further step up the tree. -/
private theorem aux_up_none (n : ℕ) : (up C parent)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- In a rooted tree no cell is its own parent. -/
private theorem aux_parent_ne_self (r : C) (htree : RootedTree C parent r) (c : C) :
    parent c ≠ some c := by
  intro h
  have hiter : ∀ n : ℕ, (up C parent)^[n] (some c) = some c := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, aux_up_some]; exact h
  obtain ⟨n, hn⟩ := htree.2 c
  rw [hiter n] at hn
  have hcr : c = r := by simpa using hn
  subst hcr
  rw [htree.1] at h
  simp at h

/-- In a rooted tree no two cells are each other's parent. -/
private theorem aux_no_two_cycle (r : C) (htree : RootedTree C parent r) {c d : C}
    (h1 : parent c = some d) (h2 : parent d = some c) : False := by
  have hiter : ∀ n : ℕ,
      (up C parent)^[n] (some c) = some c ∨ (up C parent)^[n] (some c) = some d := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        rcases ih with h | h
        · rw [h, aux_up_some]; exact Or.inr h1
        · rw [h, aux_up_some]; exact Or.inl h2
  obtain ⟨n, hn⟩ := htree.2 c
  rcases hiter n with h | h <;> rw [h] at hn
  · have hcr : c = r := by simpa using hn
    subst hcr
    rw [htree.1] at h1
    simp at h1
  · have hdr : d = r := by simpa using hn
    subst hdr
    rw [htree.1] at h2
    simp at h2

/-! ## Cell-wise counting -/

/-- A cell has exactly `N` members. -/
private theorem aux_card_cell (c : C) :
    (univ.filter fun x : C × Fin N => x.1 = c).card = N := by
  have h : (univ.filter fun x : C × Fin N => x.1 = c)
      = ({c} : Finset C) ×ˢ (univ : Finset (Fin N)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Finset.mem_product, mem_singleton, and_true]
  rw [h, Finset.card_product]
  simp

/-- The members of the parent cell, when there is one. -/
private theorem aux_card_up (c : C) :
    (univ.filter fun x : C × Fin N => parent c = some x.1).card
      = if parent c = none then 0 else N := by
  have h : (univ.filter fun x : C × Fin N => parent c = some x.1)
      = (univ.filter fun d : C => parent c = some d) ×ˢ (univ : Finset (Fin N)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, Finset.mem_product, and_true]
  have hcard1 : (univ.filter fun d : C => parent c = some d).card
      = if parent c = none then 0 else 1 := by
    cases hp : parent c with
    | none => simp
    | some p =>
        have he : (univ.filter fun d : C => (some p : Option C) = some d) = {p} := by
          ext d
          simp only [mem_filter, mem_univ, true_and, mem_singleton, Option.some.injEq]
          exact eq_comm
        rw [he]
        simp
  rw [h, Finset.card_product, Finset.card_univ, Fintype.card_fin, hcard1]
  split_ifs <;> simp

/-- The members of the child cells. -/
private theorem aux_card_down (c : C) :
    (univ.filter fun x : C × Fin N => parent x.1 = some c).card
      = (children C parent c).card * N := by
  have h : (univ.filter fun x : C × Fin N => parent x.1 = some c)
      = (children C parent c) ×ˢ (univ : Finset (Fin N)) := by
    ext x
    simp [children, Finset.mem_product]
  rw [h, Finset.card_product, Finset.card_univ, Fintype.card_fin]

/-- Every non-root cell is a child of exactly one cell. -/
private theorem aux_sum_children :
    ∑ c : C, (children C parent c).card = (nonRoot C parent).card := by
  simp only [children, nonRoot, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  cases hp : parent d with
  | none => simp
  | some p => simp

/-! ## Degrees (Theorem thm:deg-I(i)) -/

/-- **Theorem `thm:deg-I`(i), general form.** A member of a cell `c` has `N-1`
intra-cell neighbours, `N` neighbours in the parent cell when `c` is not the
root, and `N` neighbours in each of its `#children c` child cells. -/
theorem degree_eq (r : C) (htree : RootedTree C parent r) (c : C) (i : Fin N) :
    (pgraph C parent N).degree (c, i) =
      (N - 1) + (if parent c = none then 0 else N) + (children C parent c).card * N := by
  have hself : parent c ≠ some c := aux_parent_ne_self C parent r htree c
  have hsplit : (pgraph C parent N).neighborFinset (c, i) =
      (((univ.filter fun x : C × Fin N => x.1 = c).erase (c, i)) ∪
        (univ.filter fun x : C × Fin N => parent c = some x.1)) ∪
        (univ.filter fun x : C × Fin N => parent x.1 = some c) := by
    ext x
    rw [SimpleGraph.mem_neighborFinset, aux_padj_iff]
    simp only [mem_union, mem_erase, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hne, h | h | h⟩
      · exact Or.inl (Or.inl ⟨fun hxe => hne hxe.symm, h.symm⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((⟨hxne, hx1⟩ | h) | h)
      · exact ⟨fun he => hxne he.symm, Or.inl hx1.symm⟩
      · refine ⟨?_, Or.inr (Or.inl h)⟩
        rintro rfl
        exact hself h
      · refine ⟨?_, Or.inr (Or.inr h)⟩
        rintro rfl
        exact hself h
  have hdisj1 : Disjoint ((univ.filter fun x : C × Fin N => x.1 = c).erase (c, i))
      (univ.filter fun x : C × Fin N => parent c = some x.1) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, j⟩ hx hx'
    simp only [mem_erase, mem_filter, mem_univ, true_and] at hx hx'
    apply hself
    rw [hx', hx.2]
  have hdisj2 : Disjoint
      (((univ.filter fun x : C × Fin N => x.1 = c).erase (c, i)) ∪
        (univ.filter fun x : C × Fin N => parent c = some x.1))
      (univ.filter fun x : C × Fin N => parent x.1 = some c) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, j⟩ hx hx'
    simp only [mem_union, mem_erase, mem_filter, mem_univ, true_and] at hx hx'
    rcases hx with ⟨-, hx1⟩ | hx2
    · subst hx1
      exact hself hx'
    · exact aux_no_two_cycle C parent r htree hx2 hx'
  have hmemcell : (c, i) ∈ (univ.filter fun x : C × Fin N => x.1 = c) := by simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hsplit,
    Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
    Finset.card_erase_of_mem hmemcell, aux_card_cell, aux_card_up, aux_card_down]

/-- **Theorem `thm:deg-I`(i), root-cell class.** A root-cell member whose cell
has `N` children has degree `N^2 + N - 1`. -/
theorem degree_root (hN : 3 ≤ N) (r : C) (htree : RootedTree C parent r) (c : C)
    (i : Fin N) (hroot : parent c = none) (hk : (children C parent c).card = N) :
    (pgraph C parent N).degree (c, i) = N ^ 2 + N - 1 := by
  rw [degree_eq C parent N r htree c i, if_pos hroot, hk]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have h : (n + 1) ^ 2 + (n + 1) = (n + 1 - 1 + 0 + (n + 1) * (n + 1)) + 1 := by
    have hn1 : n + 1 - 1 = n := by omega
    rw [hn1]
    ring
  omega

/-- **Theorem `thm:deg-I`(i), internal-cell class.** A member of a non-root cell
with `2(N-1)` children has degree `2N^2 - 1`. -/
theorem degree_internal (hN : 3 ≤ N) (r : C) (htree : RootedTree C parent r) (c : C)
    (i : Fin N) (hnr : parent c ≠ none) (hk : (children C parent c).card = 2 * (N - 1)) :
    (pgraph C parent N).degree (c, i) = 2 * N ^ 2 - 1 := by
  rw [degree_eq C parent N r htree c i, if_neg hnr, hk]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have h : 2 * (n + 1) ^ 2 = (n + 1 - 1 + (n + 1) + 2 * (n + 1 - 1) * (n + 1)) + 1 := by
    have hn1 : n + 1 - 1 = n := by omega
    rw [hn1]
    ring
  omega

/-- **Theorem `thm:deg-I`(i), leaf-cell class.** A member of a non-root childless
cell has degree `2N - 1`. -/
theorem degree_leaf (hN : 3 ≤ N) (r : C) (htree : RootedTree C parent r) (c : C)
    (i : Fin N) (hnr : parent c ≠ none) (hk : (children C parent c).card = 0) :
    (pgraph C parent N).degree (c, i) = 2 * N - 1 := by
  rw [degree_eq C parent N r htree c i, if_neg hnr, hk]
  omega

/-! ## Edge count (Theorem thm:deg-I(ii)) -/

/-- **Theorem `thm:deg-I`(ii).** Each of the `|C|` cells induces a `K_N`,
contributing `C(N,2)` edges, and each of the non-root cells contributes the `N^2`
edges of its parent-side `K_{N,N}`. In handshake form, free of the division by
`N` the paper writes: `2|E| = |C| * N(N-1) + 2N^2 * #(non-root cells)`. -/
theorem two_mul_card_edges (r : C) (htree : RootedTree C parent r) :
    2 * (pgraph C parent N).edgeFinset.card =
      Fintype.card C * (N * (N - 1)) + 2 * N ^ 2 * (nonRoot C parent).card := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges, Fintype.sum_prod_type]
  have hinner : ∀ c : C, ∑ i : Fin N, (pgraph C parent N).degree (c, i)
      = N * ((N - 1) + (if parent c = none then 0 else N)
          + (children C parent c).card * N) := by
    intro c
    rw [Finset.sum_congr rfl fun i _ => degree_eq C parent N r htree c i,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Finset.sum_congr rfl fun c _ => hinner c, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, smul_eq_mul]
  have h2 : ∑ c : C, (if parent c = none then 0 else N)
      = (nonRoot C parent).card * N := by
    rw [nonRoot, Finset.card_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : parent c = none <;> simp [h]
  have h3 : ∑ c : C, (children C parent c).card * N = (nonRoot C parent).card * N := by
    rw [← Finset.sum_mul, aux_sum_children]
  rw [h2, h3]
  generalize N - 1 = k
  ring

/-- In a rooted cell tree the root is the only cell without a parent, so the
non-root cells number `|C| - 1`. This is the paper's `V/N - 1`. -/
theorem card_nonRoot (r : C) (htree : RootedTree C parent r) :
    (nonRoot C parent).card = Fintype.card C - 1 := by
  have hset : nonRoot C parent = (univ : Finset C).erase r := by
    ext c
    simp only [nonRoot, mem_filter, mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · intro hc hcr
      subst hcr
      exact hc htree.1
    · intro hcr hnone
      obtain ⟨n, hn⟩ := htree.2 c
      cases n with
      | zero => exact hcr (by simpa using hn)
      | succ k =>
          rw [Function.iterate_succ_apply, aux_up_some, hnone, aux_up_none] at hn
          exact absurd hn (by simp)
  rw [hset, Finset.card_erase_of_mem (mem_univ r), Finset.card_univ]

/-- **Theorem `thm:deg-I`(ii), in the paper's shape.** With `V = |C| * N` the
node count, `|E_I| = (V/N) * C(N,2) + N^2 (V/N - 1)`; in handshake form
`2|E| = |C| * N(N-1) + 2N^2 * (|C| - 1)`. -/
theorem two_mul_card_edges' (r : C) (htree : RootedTree C parent r) :
    2 * (pgraph C parent N).edgeFinset.card =
      Fintype.card C * (N * (N - 1)) + 2 * N ^ 2 * (Fintype.card C - 1) := by
  rw [two_mul_card_edges C parent N r htree, card_nonRoot C parent r htree]

/-! ## Connectivity (Proposition prop:conn-price(ii)) -/

/-- Every cell has `N` members, hence retains a survivor after fewer than `N`
deletions. -/
theorem exists_survivor (S : Finset (C × Fin N)) (hS : S.card < N) (c : C) :
    ∃ i : Fin N, (c, i) ∉ S := by
  by_contra hcon
  have h : ∀ i : Fin N, (c, i) ∈ S := by
    intro i
    by_contra hi
    exact hcon ⟨i, hi⟩
  have hsub : (univ.image fun i : Fin N => (c, i)) ⊆ S := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact h i
  have hinj : Function.Injective fun i : Fin N => ((c, i) : C × Fin N) := by
    intro a b hab
    simpa using hab
  have hcard : (univ.image fun i : Fin N => (c, i)).card = N := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hle := Finset.card_le_card hsub
  omega

/-- Survivors of one cell are pairwise adjacent (the intra-cell clique `K_N`). -/
theorem adj_same_cell (c : C) (i j : Fin N) (hij : i ≠ j) :
    (pgraph C parent N).Adj (c, i) (c, j) := by
  refine ⟨?_, Or.inl rfl⟩
  simp only [ne_eq, Prod.mk.injEq, not_and]
  intro _
  exact hij

/-- Survivors of a parent-child cell pair are adjacent (the inter-cell complete
bipartite bundle `K_{N,N}`). -/
theorem adj_parent_child (r : C) (htree : RootedTree C parent r) (c d : C)
    (hd : parent d = some c) (i j : Fin N) :
    (pgraph C parent N).Adj (d, i) (c, j) := by
  have hne : d ≠ c := by
    rintro rfl
    exact aux_parent_ne_self C parent r htree d hd
  refine ⟨?_, Or.inr (Or.inl hd)⟩
  simp only [ne_eq, Prod.mk.injEq, not_and]
  intro h
  exact absurd h hne

/-- **Proposition `prop:conn-price`(ii), lower bound.** Deleting any set `S` of
fewer than `N` vertices leaves the dense-variant protocol graph connected: any
two surviving vertices are reachable inside the induced subgraph on `Sᶜ`. -/
theorem induce_compl_reachable (r : C) (htree : RootedTree C parent r)
    (S : Finset (C × Fin N)) (hS : S.card < N)
    (u v : ((↑S : Set (C × Fin N))ᶜ : Set (C × Fin N))) :
    ((pgraph C parent N).induce ((↑S : Set (C × Fin N))ᶜ)).Reachable u v := by
  choose s hs using fun c : C => exists_survivor C N S hS c
  have hmem : ∀ c : C, (c, s c) ∈ ((↑S : Set (C × Fin N))ᶜ) := by
    intro c
    simpa using hs c
  have hlocal : ∀ (c : C) (i : Fin N) (hx : (c, i) ∈ ((↑S : Set (C × Fin N))ᶜ)),
      ((pgraph C parent N).induce ((↑S : Set (C × Fin N))ᶜ)).Reachable
        ⟨(c, i), hx⟩ ⟨(c, s c), hmem c⟩ := by
    intro c i hx
    by_cases h : i = s c
    · subst h
      exact SimpleGraph.Reachable.refl _
    · exact (SimpleGraph.induce_adj.mpr (adj_same_cell C parent N c i (s c) h)).reachable
  have hup : ∀ (n : ℕ) (c : C), (up C parent)^[n] (some c) = some r →
      ((pgraph C parent N).induce ((↑S : Set (C × Fin N))ᶜ)).Reachable
        ⟨(c, s c), hmem c⟩ ⟨(r, s r), hmem r⟩ := by
    intro n
    induction n with
    | zero =>
        intro c hc
        have hcr : c = r := by simpa using hc
        subst hcr
        exact SimpleGraph.Reachable.refl _
    | succ k ih =>
        intro c hc
        rw [Function.iterate_succ_apply, aux_up_some] at hc
        cases hp : parent c with
        | none =>
            rw [hp, aux_up_none] at hc
            exact absurd hc (by simp)
        | some p =>
            rw [hp] at hc
            have hadj : (pgraph C parent N).Adj (c, s c) (p, s p) :=
              adj_parent_child C parent N r htree p c hp (s c) (s p)
            exact (SimpleGraph.induce_adj.mpr hadj).reachable.trans (ih p hc)
  have h1 : ((pgraph C parent N).induce ((↑S : Set (C × Fin N))ᶜ)).Reachable u
      ⟨((u : C × Fin N).1, s (u : C × Fin N).1), hmem _⟩ := hlocal _ _ u.2
  have h2 : ((pgraph C parent N).induce ((↑S : Set (C × Fin N))ᶜ)).Reachable v
      ⟨((v : C × Fin N).1, s (v : C × Fin N).1), hmem _⟩ := hlocal _ _ v.2
  obtain ⟨n1, hn1⟩ := htree.2 (u : C × Fin N).1
  obtain ⟨n2, hn2⟩ := htree.2 (v : C × Fin N).1
  exact (h1.trans (hup n1 _ hn1)).trans ((h2.trans (hup n2 _ hn2)).symm)

/-- A cell has exactly `N` members, so deleting a whole cell deletes `N`
vertices. -/
theorem card_cell (c : C) : (univ.filter fun x : C × Fin N => x.1 = c).card = N :=
  aux_card_cell C N c

-- The frozen statement carries `htree`; the separation argument uses only `hd`
-- and `hleaf`, so the tree hypothesis is not referenced in the proof.
set_option linter.unusedVariables false in
/-- **Proposition `prop:conn-price`(ii), upper bound.** The members of a leaf
cell `d` have no neighbours outside `d` other than the members of the parent
cell `c`. Deleting the `N` members of `c` therefore leaves `d` as a `K_N`
component: no member of `d` reaches any surviving vertex outside `d`. -/
theorem leaf_cell_separated (r : C) (htree : RootedTree C parent r) (c d : C)
    (hd : parent d = some c) (hleaf : children C parent d = ∅)
    (u v : ({x : C × Fin N | x.1 ≠ c} : Set (C × Fin N)))
    (hu : (u : C × Fin N).1 = d) (hv : (v : C × Fin N).1 ≠ d) :
    ¬ ((pgraph C parent N).induce {x : C × Fin N | x.1 ≠ c}).Reachable u v := by
  intro hreach
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have key : ∀ y : ({x : C × Fin N | x.1 ≠ c} : Set (C × Fin N)),
      Relation.ReflTransGen
        ((pgraph C parent N).induce {x : C × Fin N | x.1 ≠ c}).Adj u y →
      (y : C × Fin N).1 = d := by
    intro y hy
    induction hy with
    | refl => exact hu
    | tail hab hadj ih =>
        rename_i b y'
        rw [SimpleGraph.induce_adj, aux_padj_iff] at hadj
        obtain ⟨-, hcase⟩ := hadj
        rcases hcase with h | h | h
        · rw [← h]; exact ih
        · rw [ih, hd] at h
          have hyc : (y' : C × Fin N).1 = c := (Option.some.inj h).symm
          exact absurd hyc y'.2
        · rw [ih] at h
          have hmemc : (y' : C × Fin N).1 ∈ children C parent d := by
            simp only [children, mem_filter, mem_univ, true_and]
            exact h
          rw [hleaf] at hmemc
          exact absurd hmemc (Finset.notMem_empty _)
  exact hv (key v hreach)

/-! ## The paper's instance: the dense-variant consensus tree `T_{N,m}`

Everything above is stated for an abstract cell type with a parent map.  This
section discharges that abstraction against the paper's own object.  The cells
are the consensus labels of `Hsfnlean.DenseUpdate` (Definition
`def:consensus-node`), the parent map drops the last subscript pair, and the two
branching numbers of Proposition `prop:consensus-tree` are imported from
`DenseUpdate.length_childList_root` and
`DenseUpdate.length_childList_of_ne_nil`.  The corollaries at the end are
therefore statements about `G^prot_I(N,m)` itself, with no branching hypothesis
left to the reader. -/

section DenseInstance

open HSFN.DenseUpdate

/-- A **consensus cell** of the depth-`m` dense variant: a valid subscript-pair
word of length at most `m-1`, that is a vertex `Θ_ℓ` of the consensus tree
`T_{N,m}` (Definition `def:consensus-node`).  The cell carries the `N` network
nodes `v_{ℓ,(i,0)}`, so `Cell N m × Fin N` is the paper's node set `V_{N,m}`
(`dnodeEquivCell`). -/
def Cell (N m : ℕ) : Type :=
  { ℓ : List (Fin N × Bool) // Valid ℓ ∧ ℓ.length + 1 ≤ m }

instance instDecidableEqCell (N m : ℕ) : DecidableEq (Cell N m) :=
  inferInstanceAs (DecidableEq (Subtype _))

/-- A cell is determined by its length together with its label. -/
private def cellToSigma {N m : ℕ} (c : Cell N m) :
    Σ t : Fin m, List.Vector (Fin N × Bool) t.1 :=
  ⟨⟨c.1.length, Nat.lt_of_succ_le c.2.2⟩, ⟨c.1, rfl⟩⟩

private theorem cellToSigma_injective (N m : ℕ) :
    Function.Injective (cellToSigma (N := N) (m := m)) := by
  intro x y h
  exact Subtype.ext
    (congrArg (fun p : (Σ t : Fin m, List.Vector (Fin N × Bool) t.1) => p.2.1) h)

noncomputable instance instFintypeCell (N m : ℕ) : Fintype (Cell N m) :=
  Fintype.ofInjective _ (cellToSigma_injective N m)

/-- The parent map of the consensus tree `T_{N,m}`: drop the last subscript
pair.  The root `Θ_(0,0)`, the empty label, has no parent.  This is the
"`label₂` is a prefix of `label₁`" relation of Section `subsec:consensus-tree`
in its immediate-predecessor form. -/
def parentCell (N m : ℕ) (c : Cell N m) : Option (Cell N m) :=
  if h : c.1 = [] then none
  else
    some ⟨c.1.dropLast, aux_valid_prefix c.2.1 c.1.dropLast_prefix, by
      have h1 : c.1.dropLast.length = c.1.length - 1 := List.length_dropLast
      have h2 := c.2.2
      omega⟩

theorem parentCell_eq_none_iff (N m : ℕ) (c : Cell N m) :
    parentCell N m c = none ↔ c.1 = [] := by
  unfold parentCell
  split_ifs with h <;> simp [h]

theorem parentCell_eq_some_iff (N m : ℕ) (c d : Cell N m) :
    parentCell N m c = some d ↔ c.1 ≠ [] ∧ d.1 = c.1.dropLast := by
  unfold parentCell
  split_ifs with h
  · constructor
    · intro hcon
      exact absurd hcon (by simp)
    · rintro ⟨hne, -⟩
      exact absurd h hne
  · constructor
    · intro heq
      exact ⟨h, (congrArg Subtype.val (Option.some.inj heq)).symm⟩
    · rintro ⟨-, hd⟩
      exact congrArg some (Subtype.ext hd.symm)

/-- A child label is its parent's label extended by one subscript pair. -/
private theorem aux_parent_append (N m : ℕ) {c d : Cell N m}
    (h : parentCell N m d = some c) : ∃ p : Fin N × Bool, d.1 = c.1 ++ [p] := by
  rw [parentCell_eq_some_iff] at h
  obtain ⟨hne, hc⟩ := h
  exact ⟨d.1.getLast hne, by rw [hc]; exact (List.dropLast_append_getLast hne).symm⟩

/-- The root cell `Θ_(0,0)` of `T_{N,m}`: the empty label. -/
def rootCell (N m : ℕ) (hm : 1 ≤ m) : Cell N m :=
  ⟨[], trivial, by simp only [List.length_nil]; omega⟩

/-- **Proposition `prop:consensus-tree`, tree structure.** The consensus labels
with the drop-the-last-pair parent map form a rooted tree with root `Θ_(0,0)`:
every cell reaches the root in `|ℓ|` steps. This discharges the hypothesis
`RootedTree` of every theorem above. -/
theorem rootedTree_dense (N m : ℕ) (hm : 1 ≤ m) :
    RootedTree (Cell N m) (parentCell N m) (rootCell N m hm) := by
  refine ⟨(parentCell_eq_none_iff N m _).mpr rfl, ?_⟩
  have key : ∀ (k : ℕ) (c : Cell N m), c.1.length = k →
      (up (Cell N m) (parentCell N m))^[k] (some c) = some (rootCell N m hm) := by
    intro k
    induction k with
    | zero =>
        intro c hc
        have hnil : c.1 = [] := by
          cases hcc : c.1 with
          | nil => rfl
          | cons a t => rw [hcc] at hc; simp at hc
        simp only [Function.iterate_zero, id_eq]
        exact congrArg some (Subtype.ext (by rw [hnil]; rfl))
    | succ k ih =>
        intro c hc
        have hne : c.1 ≠ [] := by
          intro hcon
          rw [hcon] at hc
          simp at hc
        have hL : c.1.dropLast.length = c.1.length - 1 := List.length_dropLast
        have hval : Valid c.1.dropLast := aux_valid_prefix c.2.1 c.1.dropLast_prefix
        have hlen : c.1.dropLast.length + 1 ≤ m := by
          have h2 := c.2.2
          omega
        have hd : parentCell N m c = some ⟨c.1.dropLast, hval, hlen⟩ :=
          (parentCell_eq_some_iff N m c _).mpr ⟨hne, rfl⟩
        have hgoal : (⟨c.1.dropLast, hval, hlen⟩ : Cell N m).1.length = k := by
          show c.1.dropLast.length = k
          omega
        rw [Function.iterate_succ_apply, aux_up_some, hd]
        exact ih _ hgoal
  exact fun c => ⟨c.1.length, key _ c rfl⟩

/-- The paper's ordered child list `𝓒_m(ℓ)` is repetition-free. -/
private theorem childList_nodup (N m : ℕ) (ℓ : List (Fin N × Bool)) :
    (childList N m ℓ).Nodup := by
  rw [childList]
  split_ifs
  · exact List.nodup_nil
  · exact childRaw_nodup N ℓ

/-- The label of a consensus cell. -/
def label {N m : ℕ} (c : Cell N m) : List (Fin N × Bool) := c.1

private theorem label_injective (N m : ℕ) :
    Function.Injective (label (N := N) (m := m)) := fun _ _ h => Subtype.ext h

/-- Membership in `children`, on the instance. -/
theorem mem_children_iff (N m : ℕ) (c d : Cell N m) :
    d ∈ children (Cell N m) (parentCell N m) c ↔ parentCell N m d = some c := by
  simp [children]

/-- The children of a cell in `T_{N,m}` are exactly the entries of the paper's
ordered child list `𝓒_m(ℓ)` of eq:app-children. -/
theorem image_children_eq (N m : ℕ) (c : Cell N m) :
    (children (Cell N m) (parentCell N m) c).image label
      = (childList N m c.1).toFinset := by
  ext x
  simp only [Finset.mem_image, List.mem_toFinset, mem_children_iff]
  constructor
  · rintro ⟨d, hd, hdx⟩
    have hdx' : d.1 = x := hdx
    obtain ⟨p, hp⟩ := aux_parent_append N m hd
    have hlen : d.1.length = c.1.length + 1 := by rw [hp]; simp
    have hm2 : ¬ (c.1.length + 1 = m) := by
      have h2 := d.2.2
      omega
    rw [childList, if_neg hm2, ← hdx']
    exact (mem_childRaw_iff c.1 c.2.1 d.1).mpr ⟨⟨p, hp⟩, d.2.1⟩
  · intro hx
    have hm2 : ¬ (c.1.length + 1 = m) := by
      intro h
      rw [childList_of_last_tier N m c.1 h] at hx
      simp at hx
    rw [childList, if_neg hm2] at hx
    obtain ⟨⟨p, hp⟩, hv⟩ := (mem_childRaw_iff c.1 c.2.1 x).mp hx
    have hxl : x.length = c.1.length + 1 := by rw [hp]; simp
    have hlen : x.length + 1 ≤ m := by
      have h2 := c.2.2
      omega
    refine ⟨⟨x, hv, hlen⟩, ?_, rfl⟩
    rw [parentCell_eq_some_iff]
    constructor
    · show x ≠ []
      rw [hp]
      simp
    · show c.1 = x.dropLast
      rw [hp]
      simp

/-- The number of children of a cell in `T_{N,m}` is the length of the paper's
ordered child list. -/
theorem card_children_eq (N m : ℕ) (c : Cell N m) :
    (children (Cell N m) (parentCell N m) c).card = (childList N m c.1).length := by
  rw [← Finset.card_image_of_injective (children (Cell N m) (parentCell N m) c)
      (label_injective N m),
    image_children_eq, List.toFinset_card_of_nodup (childList_nodup N m c.1)]

/-- **Proposition `prop:consensus-tree`(2)** on the instance: the root cell has
`N` children. -/
theorem card_children_root (N m : ℕ) (hm : 2 ≤ m) (c : Cell N m) (hc : c.1 = []) :
    (children (Cell N m) (parentCell N m) c).card = N := by
  rw [card_children_eq, hc, length_childList_root N m hm]

/-- **Proposition `prop:consensus-tree`(3)** on the instance: a non-root,
non-leaf cell has `2(N-1)` children. -/
theorem card_children_internal (N m : ℕ) (c : Cell N m) (hne : c.1 ≠ [])
    (hlt : c.1.length + 1 < m) :
    (children (Cell N m) (parentCell N m) c).card = 2 * (N - 1) := by
  have h := length_childList_of_ne_nil N m c.1 hne hlt
  rw [card_children_eq]
  omega

/-- The cells of the last tier are the leaves of `T_{N,m}`. -/
theorem card_children_leaf (N m : ℕ) (c : Cell N m) (hc : c.1.length + 1 = m) :
    (children (Cell N m) (parentCell N m) c).card = 0 := by
  rw [card_children_eq, childList_of_last_tier N m c.1 hc, List.length_nil]

/-! ### The paper's statements about `G^prot_I(N,m)` -/

/-- **Theorem `thm:deg-I`(i), root-cell class, on the paper's own graph.** In
`G^prot_I(N,m)` a member of the root cell `Θ_(0,0)` has degree `N^2 + N - 1`.
No branching hypothesis is assumed: the root's `N` children come from
`prop:consensus-tree`(2) through `card_children_root`. -/
theorem dense_degree_root (N m : ℕ) (hN : 3 ≤ N) (hm : 2 ≤ m) (c : Cell N m)
    (hc : c.1 = []) (i : Fin N) :
    (pgraph (Cell N m) (parentCell N m) N).degree (c, i) = N ^ 2 + N - 1 :=
  degree_root (Cell N m) (parentCell N m) N hN (rootCell N m (by omega))
    (rootedTree_dense N m (by omega)) c i ((parentCell_eq_none_iff N m c).mpr hc)
    (card_children_root N m hm c hc)

/-- **Theorem `thm:deg-I`(i), internal-cell class, on the paper's own graph.** A
member of a non-root, non-leaf cell of `T_{N,m}` (a cell at tree level
`2, …, m-1`) has degree `2N^2 - 1` in `G^prot_I(N,m)`.  The `2(N-1)` children
come from `prop:consensus-tree`(3) through `card_children_internal`. -/
theorem dense_degree_internal (N m : ℕ) (hN : 3 ≤ N) (c : Cell N m) (hne : c.1 ≠ [])
    (hlt : c.1.length + 1 < m) (i : Fin N) :
    (pgraph (Cell N m) (parentCell N m) N).degree (c, i) = 2 * N ^ 2 - 1 :=
  degree_internal (Cell N m) (parentCell N m) N hN (rootCell N m (by omega))
    (rootedTree_dense N m (by omega)) c i
    (fun hcon => hne ((parentCell_eq_none_iff N m c).mp hcon))
    (card_children_internal N m c hne hlt)

/-- **Theorem `thm:deg-I`(i), leaf-cell class, on the paper's own graph.** A
member of a non-root last-tier cell of `T_{N,m}` has degree `2N - 1` in
`G^prot_I(N,m)`. -/
theorem dense_degree_leaf (N m : ℕ) (hN : 3 ≤ N) (c : Cell N m) (hne : c.1 ≠ [])
    (hleaf : c.1.length + 1 = m) (i : Fin N) :
    (pgraph (Cell N m) (parentCell N m) N).degree (c, i) = 2 * N - 1 :=
  degree_leaf (Cell N m) (parentCell N m) N hN (rootCell N m (by omega))
    (rootedTree_dense N m (by omega)) c i
    (fun hcon => hne ((parentCell_eq_none_iff N m c).mp hcon))
    (card_children_leaf N m c hleaf)

/-- **Theorem `thm:deg-I`(ii) on the paper's own graph**, handshake form:
`2|E_I| = (V/N) * N(N-1) + 2N^2 (V/N - 1)` with `V/N = Fintype.card (Cell N m)`
the number of consensus cells. -/
theorem dense_two_mul_card_edges (N m : ℕ) (hm : 1 ≤ m) :
    2 * (pgraph (Cell N m) (parentCell N m) N).edgeFinset.card =
      Fintype.card (Cell N m) * (N * (N - 1)) +
        2 * N ^ 2 * (Fintype.card (Cell N m) - 1) :=
  two_mul_card_edges' (Cell N m) (parentCell N m) N (rootCell N m hm)
    (rootedTree_dense N m hm)

/-- **Proposition `prop:conn-price`(ii), lower bound, on the paper's own
graph.** Deleting fewer than `N` nodes of `G^prot_I(N,m)` leaves it connected. -/
theorem dense_induce_compl_reachable (N m : ℕ) (hm : 1 ≤ m)
    (S : Finset (Cell N m × Fin N)) (hS : S.card < N)
    (u v : ((↑S : Set (Cell N m × Fin N))ᶜ : Set (Cell N m × Fin N))) :
    ((pgraph (Cell N m) (parentCell N m) N).induce
      ((↑S : Set (Cell N m × Fin N))ᶜ)).Reachable u v :=
  induce_compl_reachable (Cell N m) (parentCell N m) N (rootCell N m hm)
    (rootedTree_dense N m hm) S hS u v

/-- **Proposition `prop:conn-price`(ii), upper bound, on the paper's own
graph.** Deleting the `N` members of the parent cell of a last-tier cell `d`
cuts `d` off: no member of `d` reaches any surviving node outside `d`.  With
`card_cell` (a cell has `N` members) this is the matching half of the
connectivity price. -/
theorem dense_leaf_cell_separated (N m : ℕ) (hm : 1 ≤ m) (c d : Cell N m)
    (hd : parentCell N m d = some c) (hleaf : d.1.length + 1 = m)
    (u v : ({x : Cell N m × Fin N | x.1 ≠ c} : Set (Cell N m × Fin N)))
    (hu : (u : Cell N m × Fin N).1 = d) (hv : (v : Cell N m × Fin N).1 ≠ d) :
    ¬ ((pgraph (Cell N m) (parentCell N m) N).induce
        {x : Cell N m × Fin N | x.1 ≠ c}).Reachable u v :=
  leaf_cell_separated (Cell N m) (parentCell N m) N (rootCell N m hm)
    (rootedTree_dense N m hm) c d hd
    (Finset.card_eq_zero.mp (card_children_leaf N m d hleaf)) u v hu hv

/-- The vertex type of the instantiated graph is the paper's node set `V_{N,m}`:
a node is a consensus cell together with an index inside it (Definition
`def:consensus-node`), which is exactly `DenseUpdate.DNode`. -/
def dnodeEquivCell (N m : ℕ) : DNode N m ≃ Cell N m × Fin N where
  toFun x := (⟨x.1.1, x.2⟩, x.1.2)
  invFun p := ⟨(p.1.1, p.2), p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


/-- **The internal class of `thm:deg-I`(i) is populated when `m ≥ 3`.** A
one-pair label `Θ_((0,0))` is a valid cell that is neither the root nor a
last-tier cell, so `dense_degree_internal` is not vacuous. (The converse, that
`m ≥ 3` is also necessary, is not proved here.) -/
theorem exists_internal_cell (N m : ℕ) (hN : 0 < N) (hm : 3 ≤ m) :
    ∃ c : Cell N m, c.1 ≠ [] ∧ c.1.length + 1 < m :=
  ⟨⟨[(⟨0, hN⟩, false)], ⟨rfl, by simp⟩, by simp; omega⟩, by simp, by simp; omega⟩

/-- The internal degree `2N^2 - 1` of Theorem `thm:deg-I`(i) is actually
attained in `G^prot_I(N,m)` for `m ≥ 3`: the class is non-empty. -/
theorem exists_degree_internal (N m : ℕ) (hN : 3 ≤ N) (hm : 3 ≤ m) :
    ∃ (c : Cell N m) (i : Fin N),
      (pgraph (Cell N m) (parentCell N m) N).degree (c, i) = 2 * N ^ 2 - 1 := by
  obtain ⟨c, hne, hlt⟩ := exists_internal_cell N m (by omega) hm
  exact ⟨c, ⟨0, by omega⟩, dense_degree_internal N m hN c hne hlt _⟩


end DenseInstance

end HSFN.Protocol

