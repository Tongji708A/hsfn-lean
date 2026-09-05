/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Clique

/-!
# Chordality of the host graph (block-graph consequence)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

The Related Work section places `F(N,m)` in Harary's class of *block graphs*
(every block a clique, the cell tree being the clique tree) and lists
"treewidth one below the clique number, chordality and distances realized
inside the block--cut tree" as consequences of block-graph theory
(`harary1963block`, `bodlaender1998partial`); the *classical counterpart*
paragraph of Lemma `lem:maxclique` repeats the claim ("Chordality and
treewidth one below the clique number carry over").

This file formalizes the chordality half of that claim directly from the
two-clause adjacency law, without going through the block decomposition:
**every cycle of length at least `4` in `graph N m` has a chord**, i.e. two
of its vertices are adjacent by an edge that is not an edge of the cycle
(`HSFN.chordal`).

The statement is not vacuous, and that is checked here rather than merely
asserted: `F(4,1)` is the seed cell `K₄` (Lemma `lem:maxclique`,
`HSFN.isClique_anchored`) and `HSFN.exists_cycle_length_four` exhibits a
`4`-cycle in it, so `HSFN.chordal` has a nonempty hypothesis class
(`HSFN.chordal_applies`).

Not formalized here: the block decomposition itself (that the blocks of
`F(N,m)` are exactly the seed cell and the anchored cliques), the block--cut
tree, the clique tree, and the treewidth statement `tw = ω - 1`. Only the
chordality half of the Related Work claim is proved, and it is proved
directly from the two-clause adjacency law rather than derived from
block-graph theory.

Proof route (for the proving stage). Take `x` a vertex of **maximum** tier on
the cycle and let `y, z` be its two cycle-neighbours; they are distinct
because the cycle has length `≥ 3`. Maximality rules out the "child" clause
of `Par`, so each of `y, z` is a sibling of `x` or the parent of `x`
(`chordal_sib_or_parent_of_adj_of_maxTier`); the case analysis on those two
options — mirroring the one inside `HSFN.isClique_subset`, whose helpers are
private there and are restated here — makes `y` and `z` adjacent
(`chordal_adj_of_sib_or_parent`): two siblings of `x` are siblings of each
other, a sibling of `x` is a child of the parent of `x`, and `x` has only one
parent, so the parent/parent case forces `y = z`. Since `y` and `z` sit at
distance `2` along a cycle of length `≥ 4`, the edge `s(y, z)` is not a cycle
edge, hence is a chord.
-/

namespace HSFN

variable {N m : ℕ}

/-- A neighbour of a vertex of **maximum** tier is a sibling of it or its
parent: the "child" clause of `Par` would raise the tier. (Restatement, for
the maximum-tier direction, of the dichotomy used inside
`HSFN.isClique_subset`.) -/
theorem chordal_sib_or_parent_of_adj_of_maxTier {S : Set (Addr N m)} {x w : Addr N m}
    (hmax : ∀ y ∈ S, y.tier ≤ x.tier) (hw : w ∈ S) (hadj : (graph N m).Adj x w) :
    Sib x w ∨ (x.1.length = w.1.length + 1 ∧ x.1.dropLast = w.1) := by
  rcases hadj.2 with hS | hP
  · exact Or.inl hS
  · rcases hP with ⟨hlen, -⟩ | hpar
    · have hle : w.tier ≤ x.tier := hmax w hw
      unfold Addr.tier at hle
      omega
    · exact Or.inr hpar

/-- Two distinct vertices, each of which is either a sibling of `x` or the
parent of `x`, are adjacent. (Sibling/sibling: siblinghood is transitive.
Sibling/parent: a sibling of `x` is a child of the parent of `x`.
Parent/parent: the parent is unique, so this case is empty.) -/
theorem chordal_adj_of_sib_or_parent {x y z : Addr N m} (hne : y ≠ z)
    (hy : Sib x y ∨ (x.1.length = y.1.length + 1 ∧ x.1.dropLast = y.1))
    (hz : Sib x z ∨ (x.1.length = z.1.length + 1 ∧ x.1.dropLast = z.1)) :
    (graph N m).Adj y z := by
  refine ⟨hne, ?_⟩
  rcases hy with ⟨hly, hdy⟩ | ⟨hly, hdy⟩
  · rcases hz with ⟨hlz, hdz⟩ | ⟨hlz, hdz⟩
    · exact Or.inl ⟨by omega, by rw [← hdy, hdz]⟩
    · exact Or.inr (Or.inr ⟨by omega, by rw [← hdy, hdz]⟩)
  · rcases hz with ⟨hlz, hdz⟩ | ⟨hlz, hdz⟩
    · exact Or.inr (Or.inl ⟨by omega, by rw [← hdz, hdy]⟩)
    · exact absurd (Addr.ext (hdy.symm.trans hdz)) hne

/-- In a cycle of length at least `4` the two neighbours of the base point are
not joined by an edge *of the cycle*: they sit at distance `2` along it. -/
private theorem aux_snd_penultimate_notMem_edges {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) (hc : c.IsCycle) (hlen : 4 ≤ c.length) :
    s(c.snd, c.penultimate) ∉ c.edges := by
  cases c with
  | nil => simp at hlen
  | @cons _ b _ h p =>
      obtain ⟨hp, -⟩ := (SimpleGraph.Walk.cons_isCycle_iff p h).mp hc
      have hplen : 3 ≤ p.length := by
        rw [SimpleGraph.Walk.length_cons] at hlen
        omega
      have hpnil : ¬ p.Nil := by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length]
        omega
      simp only [SimpleGraph.Walk.snd_cons,
        SimpleGraph.Walk.penultimate_cons_of_not_nil _ _ hpnil,
        SimpleGraph.Walk.edges_cons, List.mem_cons, not_or]
      constructor
      · rw [Sym2.eq_iff]
        rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · exact h.ne' h1
        · exact (SimpleGraph.Walk.adj_penultimate hpnil).ne h2
      · intro hin
        have h3 : p.penultimate = p.snd := hp.eq_snd_of_mem_edges hin
        have h4 : p.length - 1 = 1 :=
          hp.getVert_injOn (by simp) (by simp; omega) h3
        omega

/-- **Chordality of the host graph** (Related Work, block graphs; classical
counterpart of Lemma `lem:maxclique`): every cycle of `F(N,m)` of length at
least `4` has a chord, i.e. two vertices of the cycle joined by an edge of
the graph that is not one of the cycle's own edges. -/
theorem chordal {v : Addr N m} (c : (graph N m).Walk v v) (hc : c.IsCycle)
    (hlen : 4 ≤ c.length) :
    ∃ x y, x ∈ c.support ∧ y ∈ c.support ∧ (graph N m).Adj x y ∧
      ¬ c.edges.contains s(x, y) := by
  classical
  have hsne : (c.support : Multiset (Addr N m)) ≠ 0 := by
    simp only [ne_eq, Multiset.coe_eq_zero]
    exact List.ne_nil_of_mem c.start_mem_support
  obtain ⟨x, hxmem, hxmax⟩ :=
    Multiset.exists_max_image (fun a : Addr N m => a.tier) hsne
  have hxs : x ∈ c.support := Multiset.mem_coe.mp hxmem
  have hmax : ∀ w ∈ {a : Addr N m | a ∈ c.support}, w.tier ≤ x.tier :=
    fun w hw => hxmax w (Multiset.mem_coe.mpr hw)
  have hc' : (c.rotate x hxs).IsCycle := hc.rotate hxs
  have hlen' : 4 ≤ (c.rotate x hxs).length := by
    rw [SimpleGraph.Walk.length_rotate]
    exact hlen
  have hnil' : ¬ (c.rotate x hxs).Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hxy : (graph N m).Adj x (c.rotate x hxs).snd := SimpleGraph.Walk.adj_snd hnil'
  have hzx : (graph N m).Adj (c.rotate x hxs).penultimate x :=
    SimpleGraph.Walk.adj_penultimate hnil'
  have hyz : (c.rotate x hxs).snd ≠ (c.rotate x hxs).penultimate := hc'.snd_ne_penultimate
  have hysupp : (c.rotate x hxs).snd ∈ c.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hxs).mp
      (SimpleGraph.Walk.getVert_mem_support _ 1)
  have hzsupp : (c.rotate x hxs).penultimate ∈ c.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hxs).mp
      (SimpleGraph.Walk.getVert_mem_support _ _)
  refine ⟨(c.rotate x hxs).snd, (c.rotate x hxs).penultimate, hysupp, hzsupp, ?_, ?_⟩
  · exact chordal_adj_of_sib_or_parent hyz
      (chordal_sib_or_parent_of_adj_of_maxTier hmax hysupp hxy)
      (chordal_sib_or_parent_of_adj_of_maxTier hmax hzsupp hzx.symm)
  · have hnot : s((c.rotate x hxs).snd, (c.rotate x hxs).penultimate) ∉ (c.rotate x hxs).edges :=
      aux_snd_penultimate_notMem_edges _ hc' hlen'
    have hperm : (c.rotate x hxs).edges ~r c.edges := SimpleGraph.Walk.rotate_edges c x hxs
    simp only [List.contains_iff_mem]
    intro hmem
    exact hnot (hperm.perm.mem_iff.mpr hmem)


/-! ## The hypothesis class of `chordal` is nonempty

`F(4,1)` is the seed cell on the four one-digit addresses, a `K₄`; its four
vertices in cyclic order give a cycle of length `4`. This rules out the
cheapest way the theorem above could be true for the wrong reason.
-/

private def sqV0 : Addr 4 1 := ⟨[0], by decide⟩
private def sqV1 : Addr 4 1 := ⟨[1], by decide⟩
private def sqV2 : Addr 4 1 := ⟨[2], by decide⟩
private def sqV3 : Addr 4 1 := ⟨[3], by decide⟩

/-- The `4`-cycle `[0] - [1] - [2] - [3] - [0]` inside the seed cell of `F(4,1)`. -/
private def sqWalk : (graph 4 1).Walk sqV0 sqV0 :=
  .cons (by decide : (graph 4 1).Adj sqV0 sqV1)
    (.cons (by decide : (graph 4 1).Adj sqV1 sqV2)
      (.cons (by decide : (graph 4 1).Adj sqV2 sqV3)
        (.cons (by decide : (graph 4 1).Adj sqV3 sqV0) .nil)))

/-- `HSFN.chordal` is not vacuous: some HSFN graph carries a cycle of
length `4`. -/
theorem exists_cycle_length_four :
    ∃ (v : Addr 4 1) (c : (graph 4 1).Walk v v), c.IsCycle ∧ c.length = 4 := by
  refine ⟨sqV0, sqWalk, ?_, by simp [sqWalk]⟩
  simp [sqWalk, SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
  decide

/-- The conclusion of `HSFN.chordal` is actually reached on a concrete cycle:
the `4`-cycle of `F(4,1)` has a chord. -/
theorem chordal_applies :
    ∃ x y, x ∈ sqWalk.support ∧ y ∈ sqWalk.support ∧ (graph 4 1).Adj x y ∧
      ¬ sqWalk.edges.contains s(x, y) := by
  refine chordal sqWalk ?_ ?_
  · simp [sqWalk, SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
    decide
  · simp [sqWalk]

end HSFN
