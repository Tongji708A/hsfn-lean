/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Clique

/-!
# Claw-freeness of the host graph (Definition def:realization)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

The remark following Definition~`def:realization` asserts that `F(N,m)` is
claw-free, "every neighborhood is covered by the birth clique and the spawn
cell; hence already the star `K_{1,3}`, and with it every graph carrying a
non-clique block, has no induced copy in any family member". The same fact is
invoked in the proof of Lemma~`lem:tree-embed` ("the claw-freeness noted after
Definition~`def:realization`") to justify that a fan-out `≥ 3` tree is embedded
by *selection* of links and never appears as an induced subgraph.

The two cliques of the cover are the ones classified in Lemma~`lem:maxclique`:
the **birth clique** of `u`, namely the birth cell of `u` — the cell `cell(p)`
spawned by `u`'s anchor `p`, or the seed cell when `u` sits at tier `1` —
together with that anchor, and the **anchored clique** `{u} ∪ cell(u)` of `u`,
whose non-`u` part is the spawn cell `chiF u`. (In the paper's notation
`cell(v)` always denotes the cell *spawned* at `v`, never the cell `v` was born
into.) By the two-clause adjacency law
(Theorem~`thm:adjacency-II`) a neighbour of `u` is a sibling, the anchor, or a
child, so these two cliques cover `N(u)`; three pairwise distinct neighbours
then meet in one of the two classes and are adjacent.

Only the graph-theoretic core is claimed here: the two-clique neighbourhood
cover and the absence of an induced `K_{1,3}`. The downstream consequences that
Definition~`def:realization` draws from claw-freeness (no induced copy of any
graph carrying a non-clique block, and the fan-out `≥ 3` case of
Lemma~`lem:tree-embed`) need the realization machinery and are not formalized
in this file.
-/

namespace HSFN

variable {N m : ℕ}

open Finset

/-- The **birth clique** of `u` (Lemma `lem:maxclique`): the birth cell of `u`,
i.e. the `N` addresses sharing its tier and its parent word — `u` itself
included — together with the anchor that spawned that cell. For a tier-`1`
address the anchor is absent and this is the seed cell `tier1 N m`. -/
def birthClique (u : Addr N m) : Finset (Addr N m) :=
  (univ.filter fun v => Sib u v) ∪ parF u

/-- Membership in the birth clique, unfolded: a birth-clique member of `u` is a
cell-mate of `u` (`u` itself included) or the anchor of `u`. -/
theorem mem_birthClique_iff (u v : Addr N m) :
    v ∈ birthClique u ↔
      Sib u v ∨ (u.1.length = v.1.length + 1 ∧ u.1.dropLast = v.1) := by
  simp only [birthClique, parF, mem_union, mem_filter, mem_univ, true_and]

theorem self_mem_birthClique (u : Addr N m) : u ∈ birthClique u :=
  (mem_birthClique_iff u u).mpr (Or.inl ⟨rfl, rfl⟩)

/-- The birth cell part of the birth clique: siblings of `u` are birth-clique
members. -/
theorem sibF_subset_birthClique (u : Addr N m) : sibF u ⊆ birthClique u := by
  intro v hv
  simp only [sibF, mem_filter, mem_univ, true_and] at hv
  exact (mem_birthClique_iff u v).mpr (Or.inl hv.1)

/-- The anchor part of the birth clique. -/
theorem parF_subset_birthClique (u : Addr N m) : parF u ⊆ birthClique u := by
  intro v hv
  simp only [parF, mem_filter, mem_univ, true_and] at hv
  exact (mem_birthClique_iff u v).mpr (Or.inr hv)

/-! ## (a) The two-clique neighbourhood cover -/

/-- The birth clique is a clique: two cell-mates are clause-(S) adjacent, and
the anchor is clause-(P) adjacent to every member of the cell it spawned. -/
theorem isClique_birthClique (u : Addr N m) :
    (graph N m).IsClique (birthClique u : Set (Addr N m)) := by
  intro a ha b hb hab
  rw [Finset.mem_coe, mem_birthClique_iff] at ha hb
  refine ⟨hab, ?_⟩
  rcases ha with hSa | hPa
  · rcases hb with hSb | hPb
    · exact Or.inl ⟨hSa.1.symm.trans hSb.1, hSa.2.symm.trans hSb.2⟩
    · refine Or.inr (Or.inr ⟨?_, hSa.2.symm.trans hPb.2⟩)
      have h1 := hSa.1
      have h2 := hPb.1
      omega
  · rcases hb with hSb | hPb
    · refine Or.inr (Or.inl ⟨?_, hSb.2.symm.trans hPa.2⟩)
      have h1 := hSb.1
      have h2 := hPa.1
      omega
    · exact absurd (Addr.ext (hPa.2.symm.trans hPb.2)) hab

/-- The birth cell alone is a clique (the sibling part of the birth clique). -/
theorem isClique_sibF (u : Addr N m) :
    (graph N m).IsClique (sibF u : Set (Addr N m)) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe, sibF, mem_filter, mem_univ, true_and] at ha hb
  exact ⟨hab, Or.inl ⟨ha.1.1.symm.trans hb.1.1, ha.1.2.symm.trans hb.1.2⟩⟩

/-- The spawn cell of `u` is a clique — the non-`u` part of the anchored clique
`anchored u` of Lemma `lem:maxclique`. -/
theorem isClique_chiF (u : Addr N m) :
    (graph N m).IsClique (chiF u : Set (Addr N m)) := by
  have hsub : (chiF u : Set (Addr N m)) ⊆ (anchored u : Set (Addr N m)) := by
    intro v hv
    simp only [Finset.mem_coe, anchored, mem_insert] at hv ⊢
    exact Or.inr hv
  exact (isClique_anchored u).subset hsub

/-- **Neighbourhood cover** (Definition `def:realization`, the claw-freeness
remark): every neighbour of `u` lies in the birth clique of `u` or in the cell
`u` spawns. Both sets are cliques (`isClique_birthClique`, `isClique_chiF`), so
the neighbourhood of every vertex is covered by two cliques. -/
theorem neighborSet_subset_birthClique_union_chiF (u : Addr N m) :
    ∀ v ∈ (graph N m).neighborSet u,
      v ∈ (birthClique u : Set (Addr N m)) ∪ (chiF u : Set (Addr N m)) := by
  intro v hv
  have hv' : v ∈ (graph N m).neighborFinset u := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hv
  rcases (mem_neighborFinset_iff u v).mp hv' with h | h | h
  · exact Or.inl (Finset.mem_coe.mpr (sibF_subset_birthClique u h))
  · exact Or.inl (Finset.mem_coe.mpr (parF_subset_birthClique u h))
  · exact Or.inr (Finset.mem_coe.mpr h)

/-- Finset form of the cover. -/
theorem neighborFinset_subset_birthClique_union_chiF (u : Addr N m) :
    (graph N m).neighborFinset u ⊆ birthClique u ∪ chiF u := by
  intro v hv
  rcases (mem_neighborFinset_iff u v).mp hv with h | h | h
  · exact mem_union_left _ (sibF_subset_birthClique u h)
  · exact mem_union_left _ (parF_subset_birthClique u h)
  · exact mem_union_right _ h

/-- At tier `1` there is no anchor, so the cover simplifies to the sibling set
and the spawn cell. -/
theorem neighborSet_subset_sibF_union_chiF (u : Addr N m) (h : u.tier = 1) :
    ∀ v ∈ (graph N m).neighborSet u,
      v ∈ (sibF u : Set (Addr N m)) ∪ (chiF u : Set (Addr N m)) := by
  intro v hv
  have hv' : v ∈ (graph N m).neighborFinset u := by
    rw [SimpleGraph.mem_neighborFinset]
    exact hv
  rcases (mem_neighborFinset_iff u v).mp hv' with hs | hp | hc
  · exact Or.inl (Finset.mem_coe.mpr hs)
  · exfalso
    simp only [parF, mem_filter, mem_univ, true_and] at hp
    have h1 := hp.1
    have h2 := Addr.one_le_tier v
    unfold Addr.tier at h h2
    omega
  · exact Or.inr (Finset.mem_coe.mpr hc)

/-! ## (b) Claw-freeness -/

private theorem aux_adj_of_mem_clique {s : Finset (Addr N m)}
    (hcl : (graph N m).IsClique (s : Set (Addr N m))) {a b : Addr N m}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) : (graph N m).Adj a b :=
  hcl (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab

/-- **Claw-freeness** (Definition `def:realization`; used in Lemma
`lem:tree-embed`): `F(N,m)` contains no induced star `K_{1,3}`. Stated without
naming the claw: three pairwise distinct common neighbours of a vertex `u` are
never pairwise non-adjacent. Two of `x, y, z` fall into the same one of the two
cliques covering `N(u)` and are therefore adjacent. -/
theorem clawFree (u x y z : Addr N m)
    (hx : (graph N m).Adj u x) (hy : (graph N m).Adj u y) (hz : (graph N m).Adj u z)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    (graph N m).Adj x y ∨ (graph N m).Adj y z ∨ (graph N m).Adj x z := by
  have hB := isClique_birthClique u
  have hC := isClique_chiF u
  have hxm := neighborSet_subset_birthClique_union_chiF u x hx
  have hym := neighborSet_subset_birthClique_union_chiF u y hy
  have hzm := neighborSet_subset_birthClique_union_chiF u z hz
  rcases hxm with hx' | hx' <;> rcases hym with hy' | hy' <;> rcases hzm with hz' | hz' <;>
    rw [Finset.mem_coe] at hx' hy' hz'
  · exact Or.inl (aux_adj_of_mem_clique hB hx' hy' hxy)
  · exact Or.inl (aux_adj_of_mem_clique hB hx' hy' hxy)
  · exact Or.inr (Or.inr (aux_adj_of_mem_clique hB hx' hz' hxz))
  · exact Or.inr (Or.inl (aux_adj_of_mem_clique hC hy' hz' hyz))
  · exact Or.inr (Or.inl (aux_adj_of_mem_clique hB hy' hz' hyz))
  · exact Or.inr (Or.inr (aux_adj_of_mem_clique hC hx' hz' hxz))
  · exact Or.inl (aux_adj_of_mem_clique hC hx' hy' hxy)
  · exact Or.inl (aux_adj_of_mem_clique hC hx' hy' hxy)

/-- Claw-freeness restated for independent sets: no independent set inside a
neighbourhood has three vertices, so no vertex is the centre of an induced
`K_{1,3}`. -/
theorem card_le_two_of_isIndepSet_of_subset_neighbors (u : Addr N m)
    (s : Finset (Addr N m)) (hs : ∀ v ∈ s, (graph N m).Adj u v)
    (hind : (graph N m).IsIndepSet (s : Set (Addr N m))) :
    s.card ≤ 2 := by
  by_contra hlt
  have hlt' : 2 < s.card := not_le.mp hlt
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hlt'
  rcases clawFree u a b c (hs a ha) (hs b hb) (hs c hc) hab hbc hac with h | h | h
  · exact hind (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab h
  · exact hind (Finset.mem_coe.mpr hb) (Finset.mem_coe.mpr hc) hbc h
  · exact hind (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hc) hac h

end HSFN
