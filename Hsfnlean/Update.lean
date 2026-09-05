/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Basic

/-!
# Canonical cyclic update order (Theorem thm:update-main)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
For a cell `cell(a)` the list `D(a)` consists of the `N` members
`a0, a1, …, a(N-1)` in increasing final digit, followed by
`D(a0), D(a1), …, D(a(N-1))` in that order (no child lists at the last tier).
`D(ε)` is a repetition-free list of all nodes, hence its wrap-around
successor is a single cyclic permutation of the node set.

`dfsW N k a` is `D(a)` with `k` tiers of room below `a` (so `D(ε) = dfsW N m []`).
The statements below are frozen; only the proofs are to be supplied.
-/

namespace HSFN

/-- The depth-first list `D(a)` of the words strictly below `a`, with `k`
tiers of room: members first (digit order), then the child lists in digit order. -/
def dfsW (N : ℕ) : ℕ → List (Fin N) → List (List (Fin N))
  | 0, _ => []
  | k + 1, a =>
      ((List.finRange N).map fun d => a ++ [d]) ++
        ((List.finRange N).flatMap fun d => dfsW N k (a ++ [d]))

/-- Words that are addresses of the depth-`m` HSFN, lifted to `Addr N m`. -/
def toAddr {N : ℕ} (m : ℕ) (w : List (Fin N)) : Option (Addr N m) :=
  if h : w ≠ [] ∧ w.length ≤ m then some ⟨w, h⟩ else none

/-- The global update list `D(ε)` of the depth-`m` HSFN, as addresses. -/
def dfsList (N m : ℕ) : List (Addr N m) :=
  (dfsW N m []).filterMap (toAddr m)

/-- Membership in `D(a)`: exactly the proper extensions of `a` by `1 … k` digits. -/
theorem mem_dfsW_iff (N k : ℕ) (a w : List (Fin N)) :
    w ∈ dfsW N k a ↔ a <+: w ∧ a.length < w.length ∧ w.length ≤ a.length + k := by
  induction k generalizing a w with
  | zero =>
      simp [dfsW]
  | succ k ih =>
      rw [dfsW, List.mem_append]
      constructor
      · intro hw
        rcases hw with hw | hw
        · rcases List.mem_map.mp hw with ⟨d, hd, rfl⟩
          refine ⟨List.prefix_append _ _, ?_, ?_⟩ <;>
            simp only [List.length_append, List.length_singleton] <;> omega
        · rcases List.mem_flatMap.1 hw with ⟨d, -, hw⟩
          have h' := (ih _ _).mp hw
          refine ⟨(List.prefix_append a [d]).trans h'.1, ?_, ?_⟩ <;>
            simp only [List.length_append, List.length_singleton] at h' <;> omega
      · rintro ⟨hpre, hlen, hle⟩
        let d : Fin N := w.get ⟨a.length, hlen⟩
        have hpre' : a ++ [d] <+: w := List.concat_get_prefix hpre hlen
        by_cases hEq : w.length = (a ++ [d]).length
        · have hEq' : w = a ++ [d] := by
            exact (List.IsPrefix.eq_of_length hpre' hEq.symm).symm
          left
          rw [hEq']
          exact List.mem_map.2 ⟨d, List.mem_finRange d, rfl⟩
        · right
          simp only [List.length_append, List.length_singleton] at hEq
          have hwlt : (a ++ [d]).length < w.length := by
            simp only [List.length_append, List.length_singleton]
            omega
          have hwle : w.length ≤ (a ++ [d]).length + k := by
            simp only [List.length_append, List.length_singleton]
            omega
          exact List.mem_flatMap.2 ⟨d, List.mem_finRange d,
            (ih _ _).mpr ⟨hpre', hwlt, hwle⟩⟩

/-- `D(a)` is repetition-free. -/
theorem dfsW_nodup (N k : ℕ) (a : List (Fin N)) : (dfsW N k a).Nodup := by
  induction k generalizing a with
  | zero =>
      simp [dfsW]
  | succ k ih =>
      rw [dfsW]
      rw [List.nodup_append']
      refine ⟨?_, ?_, ?_⟩
      · apply List.Nodup.map _ (List.nodup_finRange N)
        intro d₁ d₂ h
        simpa using List.append_right_injective a h
      ·
        rw [List.nodup_flatMap]
        refine ⟨?_, ?_⟩
        · intro d hd
          exact ih (a := a ++ [d])
        · apply (List.nodup_finRange N).pairwise_of_forall_ne
          intro d₁ hd₁ d₂ hd₂ hne
          apply List.disjoint_left.mpr
          intro x hx₁ hx₂
          have h₁ := (mem_dfsW_iff (N := N) (k := k) (a := a ++ [d₁]) (w := x)).1 hx₁
          have h₂ := (mem_dfsW_iff (N := N) (k := k) (a := a ++ [d₂]) (w := x)).1 hx₂
          have heq₁ : a ++ [d₁] = x.take (a.length + 1) := by
            simpa using List.prefix_iff_eq_take.mp h₁.1
          have heq₂ : a ++ [d₂] = x.take (a.length + 1) := by
            simpa using List.prefix_iff_eq_take.mp h₂.1
          exact hne (by
            simpa using List.append_right_injective a (heq₁.trans heq₂.symm))
      · rw [List.disjoint_left]
        intro x hxmap hxflat
        rcases List.mem_map.mp hxmap with ⟨d, -, rfl⟩
        rcases List.mem_flatMap.1 hxflat with ⟨d', _, hx⟩
        have h := (mem_dfsW_iff N k (a ++ [d']) (a ++ [d])).mp hx
        simp only [List.length_append, List.length_singleton] at h
        omega

/-- Every word of `D(ε)` is an address, so `dfsList` loses nothing. -/
theorem toAddr_dfsW_isSome (N m : ℕ) (w : List (Fin N)) (hw : w ∈ dfsW N m []) :
    (toAddr (N := N) m w).isSome := by
  have hw' := (mem_dfsW_iff (N := N) (k := m) (a := []) (w := w)).1 hw
  have hwlen : w ≠ [] := List.ne_nil_of_length_pos (by simpa using hw'.2.1)
  have hwle : w.length ≤ m := by simpa using hw'.2.2
  simp [toAddr, hwlen, hwle]

/-- `D(ε)` lists every address. -/
theorem mem_dfsList (N m : ℕ) (v : Addr N m) : v ∈ dfsList N m := by
  rw [dfsList]
  refine List.mem_filterMap.mpr ?_
  refine ⟨v.1, ?_, ?_⟩
  · exact (mem_dfsW_iff (N := N) (k := m) (a := []) (w := v.1)).2
      ⟨List.nil_prefix, List.length_pos_of_ne_nil v.2.1,
        by simpa using v.2.2⟩
  · simp [toAddr, v.2.1, v.2.2]

/-- `D(ε)` lists every address exactly once. -/
theorem dfsList_nodup (N m : ℕ) : (dfsList N m).Nodup := by
  refine List.Nodup.filterMap ?_ (dfsW_nodup N m [])
  intro w₁ w₂ v hw₁ hw₂
  rcases (by simpa [toAddr] using hw₁) with ⟨h₁, heq₁⟩
  rcases (by simpa [toAddr] using hw₂) with ⟨h₂, heq₂⟩
  have hEq : (⟨w₁, h₁⟩ : Addr N m) = ⟨w₂, h₂⟩ := by
    exact heq₁.trans heq₂.symm
  exact congrArg Subtype.val hEq

/-- The update list has exactly `|V|` entries. -/
theorem dfsList_length (N m : ℕ) : (dfsList N m).length = Fintype.card (Addr N m) := by
  rw [← List.toFinset_card_of_nodup (dfsList_nodup N m)]
  have hto : (dfsList N m).toFinset = Finset.univ := by
    apply Finset.eq_univ_iff_forall.2
    intro v
    simpa [List.mem_toFinset] using mem_dfsList (N := N) (m := m) v
  simp [hto]

/-- **Canonical cyclic update order** (Theorem thm:update-main): the wrap-around
successor of `D(ε)` is a single cycle (for `N ≥ 2`, `m ≥ 1`, so that there are
at least two nodes). -/
theorem dfsList_formPerm_isCycle (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) :
    (dfsList N m).formPerm.IsCycle := by
  have hlen : 2 ≤ (dfsList N m).length := by
    rw [dfsList_length]
    have hsub : N ≤ Fintype.card (Addr N m) := by
      simpa [Addr.card_tier (N := N) (m := m) 1 le_rfl hm] using
        (Fintype.card_subtype_le (fun a : Addr N m => a.tier = 1))
    exact hN.trans hsub
  exact List.isCycle_formPerm (dfsList_nodup N m) hlen

/-- The cycle visits every node: the support of the successor permutation is
the whole node set. -/
theorem dfsList_formPerm_support (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) :
    (dfsList N m).formPerm.support = Finset.univ := by
  have hne : ∀ x : Addr N m, (dfsList N m) ≠ [x] := by
    intro x hx
    have hlen : 2 ≤ (dfsList N m).length := by
      rw [dfsList_length]
      have hsub : N ≤ Fintype.card (Addr N m) := by
        simpa [Addr.card_tier (N := N) (m := m) 1 le_rfl hm] using
          (Fintype.card_subtype_le (fun a : Addr N m => a.tier = 1))
      exact hN.trans hsub
    have : (dfsList N m).length = 1 := by simp [hx]
    omega
  rw [List.support_formPerm_of_nodup (dfsList N m) (dfsList_nodup N m) hne]
  have hto : (dfsList N m).toFinset = Finset.univ := by
    apply Finset.eq_univ_iff_forall.2
    intro v
    simpa [List.mem_toFinset] using mem_dfsList (N := N) (m := m) v
  simp [hto]

end HSFN
