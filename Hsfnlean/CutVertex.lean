/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Distance

/-!
# Every anchor is a cut vertex (Proposition prop:conn-price(i))

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
Deleting a tier-`t` node `a` with `t ≤ m-1` separates its
`(N^{m-t+1} - N)/(N-1)` descendants from the rest of the graph. Here the
descendant set is `desc a`, its size is stated in the subtraction-free form
`(N-1)·|desc a| + N = N^{m-t+1}`, every edge leaving `desc a` lands on `a`,
and in the graph with `a` removed no descendant reaches any other node.
The statements below are frozen; only the proofs are to be supplied.
-/

namespace HSFN

variable {N m : ℕ}

open Finset

/-- The descendants of `a`: the addresses having `a` as a proper prefix. -/
def desc (a : Addr N m) : Finset (Addr N m) :=
  univ.filter fun x => a.1 <+: x.1 ∧ a.1.length < x.1.length

private theorem aux_mem_desc {a x : Addr N m} :
    x ∈ desc a ↔ a.1 <+: x.1 ∧ a.1.length < x.1.length := by
  simp [desc]

/-- `a` is not its own descendant. -/
theorem notMem_desc_self (a : Addr N m) : a ∉ desc a := by
  intro h
  exact (lt_irrefl _) (aux_mem_desc.mp h).2

private theorem aux_prefix_dropLast {α : Type*} {u v : List α}
    (hpre : u <+: v) (hlt : u.length < v.length) : u <+: v.dropLast := by
  rw [List.dropLast_eq_take, List.prefix_take_iff]
  exact ⟨hpre, by omega⟩

private theorem aux_suffix_is_addr (a : Addr N m) {x : Addr N m} (hx : x ∈ desc a) :
    x.1.drop a.1.length ≠ [] ∧ (x.1.drop a.1.length).length ≤ m - a.tier := by
  have hx' := aux_mem_desc.mp hx
  constructor
  · intro hnil
    have : x.1.length ≤ a.1.length := List.drop_eq_nil_iff.mp hnil
    omega
  · have hlen : (x.1.drop a.1.length).length = x.1.length - a.1.length :=
      List.length_drop
    have hxle : x.1.length ≤ m := x.2.2
    have hat : a.tier = a.1.length := rfl
    omega

private theorem aux_append_is_addr (a : Addr N m) (w : Addr N (m - a.tier)) :
    a.1 ++ w.1 ≠ [] ∧ (a.1 ++ w.1).length ≤ m := by
  constructor
  · intro h
    exact a.2.1 (List.append_eq_nil_iff.mp h).1
  · have hw : w.1.length ≤ m - a.tier := w.2.2
    have ha : a.tier ≤ m := Addr.tier_le a
    have ht : a.tier = a.1.length := rfl
    simp only [List.length_append]
    omega

private theorem aux_append_mem_desc (a : Addr N m) (w : Addr N (m - a.tier)) :
    ⟨a.1 ++ w.1, aux_append_is_addr a w⟩ ∈ desc a := by
  refine aux_mem_desc.mpr ⟨List.prefix_append a.1 w.1, ?_⟩
  have hw : 0 < w.1.length := List.length_pos_of_ne_nil w.2.1
  simp only [List.length_append]
  omega

private theorem aux_card_desc (a : Addr N m) :
    (desc a).card = Fintype.card (Addr N (m - a.tier)) := by
  let e : { z // z ∈ desc a } ≃ Addr N (m - a.tier) :=
    { toFun := fun z => ⟨z.1.1.drop a.1.length, aux_suffix_is_addr a z.2⟩
      invFun := fun w => ⟨⟨a.1 ++ w.1, aux_append_is_addr a w⟩, aux_append_mem_desc a w⟩
      left_inv := fun z => by
        apply Subtype.ext
        apply Addr.ext
        have hx := (aux_mem_desc.mp z.2).1
        exact List.prefix_iff_eq_append.mp hx
      right_inv := fun w => by
        apply Addr.ext
        exact List.drop_append_length }
  exact Finset.card_eq_of_equiv_fintype e

/-- Descendant count, subtraction-free: `(N-1)·|desc a| + N = N^{m - tier a + 1}`
(this is `|desc a| = (N^{m-t+1} - N)/(N-1)`; for a leaf both sides equal `N`). -/
theorem card_desc (a : Addr N m) :
    (N - 1) * (desc a).card + N = N ^ (m - a.tier + 1) := by
  have hN : 0 < N := Addr.N_pos a
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [aux_card_desc a]
  simpa using Addr.card_closed n (m - a.tier)

/-- A non-leaf node has descendants. -/
theorem desc_nonempty (a : Addr N m) (h : a.tier < m) : (desc a).Nonempty := by
  let child : Addr N m :=
    ⟨a.1 ++ [⟨0, Addr.N_pos a⟩], by
      constructor
      · simp
      · have : a.1.length + 1 ≤ m := by
          simpa [Addr.tier] using Nat.succ_le_of_lt h
        simpa [List.length_append] using this⟩
  refine ⟨child, aux_mem_desc.mpr ⟨List.prefix_append _ _, ?_⟩⟩
  simp [child, List.length_append]

/-- **Boundary law**: an edge with exactly one endpoint among the descendants of
`a` has `a` as its other endpoint. -/
theorem adj_desc_boundary {a x y : Addr N m} (hx : x ∈ desc a) (hy : y ∉ desc a)
    (h : (graph N m).Adj x y) : y = a := by
  have hx' := aux_mem_desc.mp hx
  rcases h with ⟨_, hS | hP⟩
  · rcases hS with ⟨hlen, hdrop⟩
    have hpre_y : a.1 <+: y.1 :=
      ((hdrop ▸ aux_prefix_dropLast hx'.1 hx'.2).trans (List.dropLast_prefix y.1))
    have : y ∈ desc a := aux_mem_desc.mpr ⟨hpre_y, by omega⟩
    exact (hy this).elim
  · rcases hP with ⟨hlen, hpre⟩ | ⟨hlen, hpre⟩
    · have hxy : x.1 <+: y.1 := by
        rw [← hpre]
        exact List.dropLast_prefix y.1
      have : y ∈ desc a := aux_mem_desc.mpr ⟨hx'.1.trans hxy, by omega⟩
      exact (hy this).elim
    · have hyx : y.1 <+: x.1 := by
        rw [← hpre]
        exact List.dropLast_prefix x.1
      have hay : a.1 <+: y.1 := by
        rw [← hpre]
        exact aux_prefix_dropLast hx'.1 (by omega)
      by_cases hlt : a.1.length < y.1.length
      · exact (hy (aux_mem_desc.mpr ⟨hay, hlt⟩)).elim
      · have hlen_eq : a.1.length = y.1.length := by omega
        exact Addr.ext (List.IsPrefix.eq_of_length hay hlen_eq).symm

/-- Some node lies outside `desc a ∪ {a}` (for `N ≥ 2`): a tier-`1` node whose
digit differs from the first digit of `a`. -/
theorem exists_outside (a : Addr N m) (hN : 2 ≤ N) :
    ∃ y : Addr N m, y ∉ desc a ∧ y ≠ a := by
  have hm : 1 ≤ m := (Addr.one_le_tier a).trans (Addr.tier_le a)
  have hlt0 : (0 : ℕ) < N := Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hN
  have hlt1 : (1 : ℕ) < N := Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hN
  obtain ⟨d0, rest, hcons⟩ := List.exists_cons_of_ne_nil a.2.1
  let d : Fin N := if d0.val = 0 then Fin.mk 1 hlt1 else Fin.mk 0 hlt0
  have hdne : d ≠ d0 := by
    intro h
    by_cases h0 : d0.val = 0
    · have hd : d = Fin.mk 1 hlt1 := if_pos h0
      have hval : (1 : ℕ) = 0 := by
        calc
          (1 : ℕ) = (Fin.mk 1 hlt1).val := rfl
          _ = d.val := by rw [hd]
          _ = d0.val := by rw [h]
          _ = 0 := h0
      exact Nat.succ_ne_zero 0 hval
    · have hd : d = Fin.mk 0 hlt0 := if_neg h0
      have hval : (0 : ℕ) = d0.val := by
        calc
          (0 : ℕ) = (Fin.mk 0 hlt0).val := rfl
          _ = d.val := by rw [hd]
          _ = d0.val := by rw [h]
      exact h0 hval.symm
  let y : Addr N m := ⟨[d], by simp, by simpa using hm⟩
  refine ⟨y, ?_, ?_⟩
  · intro hy
    have hlen : a.1.length < 1 := by
      simpa [y] using (aux_mem_desc.mp hy).2
    have : 1 ≤ a.1.length := Addr.one_le_tier a
    omega
  · intro hya
    have ha : a.1 = [d] := (congrArg Subtype.val hya).symm
    rw [hcons, List.cons.injEq] at ha
    exact hdne ha.1.symm

/-- **Every anchor is a cut vertex** (Proposition prop:conn-price(i)): in the
graph induced on the nodes other than `a`, no descendant of `a` is reachable
from any node outside `desc a`. -/
theorem not_reachable_of_desc (a : Addr N m) {x y : Addr N m}
    (hx : x ∈ desc a) (hy : y ∉ desc a) (hya : y ≠ a) :
    ¬ ((graph N m).induce ({a}ᶜ : Set (Addr N m))).Reachable
        ⟨x, fun hxa => notMem_desc_self a (hxa ▸ hx)⟩ ⟨y, hya⟩ := by
  intro hR
  obtain ⟨p⟩ := hR
  let S : Set ({a}ᶜ : Set (Addr N m)) := {z | (z : Addr N m) ∈ desc a}
  obtain ⟨d, _, hd1, hd2⟩ :=
    p.exists_boundary_dart S (by exact hx) (by exact hy)
  have hadj : (graph N m).Adj d.fst d.snd := d.adj
  have hyeq : (d.snd : Addr N m) = a := adj_desc_boundary hd1 hd2 hadj
  have hmem : (d.snd : Addr N m) ∉ ({a} : Set (Addr N m)) := d.snd.property
  exact hmem (Set.mem_singleton_iff.mpr hyeq)

end HSFN
