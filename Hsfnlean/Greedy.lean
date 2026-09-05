/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Distance

/-!
# Greedy locator routing as a function (Theorem thm:distance-II(ii))

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
At the current node `z ≠ v`: if `z` is a proper prefix of `v`, forward to the child
`pre_{|z|+1}(v)`; else if `z, v` are incomparable and `|z| = ℓ + 1` (`ℓ` the longest
common prefix), forward to the sibling `pre_{ℓ+1}(v)`; otherwise forward to the anchor.
Every hop is an edge, decreases the distance by exactly one, and the packet arrives
after exactly `d(u,v)` hops. The pilot proved the existence form (`exists_step`); here
the rule is a function on words. The statements below are frozen; only the proofs are
to be supplied.
-/

namespace HSFN

variable {N m : ℕ}

/-- The greedy next hop toward `v` from `z`, on words. -/
def greedyW (v z : List (Fin N)) : List (Fin N) :=
  if z <+: v then v.take (z.length + 1)
  else if z.length = lcp z v + 1 then v.take (lcp z v + 1)
  else z.dropLast

private theorem aux_lcp_take_left : ∀ (u v : List (Fin N)) (k : ℕ),
    lcp (u.take k) v = min (lcp u v) k
  | [], v, k => by simp [lcp]
  | a :: as, [], k => by cases k <;> simp [lcp]
  | a :: as, b :: bs, 0 => by simp [lcp]
  | a :: as, b :: bs, k + 1 => by
      simp only [List.take_succ_cons, lcp]
      by_cases h : a = b
      · rw [if_pos h, if_pos h]
        rw [aux_lcp_take_left as bs k]
        exact (Nat.succ_min_succ (lcp as bs) k).symm
      · rw [if_neg h, if_neg h]
        simp

private theorem aux_lcp_dropLast_left (u v : List (Fin N)) :
    lcp u.dropLast v = min (lcp u v) (u.length - 1) := by
  rw [List.dropLast_eq_take, aux_lcp_take_left]

private theorem aux_lcp_lt_min_of_not_prefixComp {u v : Addr N m}
    (h : ¬ PrefixComp u v) :
    lcp u.1 v.1 < min u.tier v.tier := by
  have h1 := lcp_le_left u.1 v.1
  have h2 := lcp_le_right u.1 v.1
  have h3 := (not_iff_not.mpr (prefixComp_iff_lcp u v)).mp h
  unfold Addr.tier at *
  omega

private theorem aux_length_take_of_le {α : Type _} {l : List α} {k : ℕ}
    (h : k ≤ l.length) :
    (l.take k).length = k := by
  rw [List.length_take]
  omega

private theorem aux_dropLast_eq_take_of_length_eq_succ {α : Type _} {l : List α} {k : ℕ}
    (h : l.length = k + 1) :
    l.dropLast = l.take k := by
  rw [List.dropLast_eq_take]
  have : l.length - 1 = k := by omega
  rw [this]

private theorem aux_dropLast_take_succ_of_le {α : Type _} {l : List α} {k : ℕ}
    (h : k + 1 ≤ l.length) :
    (l.take (k + 1)).dropLast = l.take k := by
  rw [List.dropLast_eq_take]
  have hlen : (l.take (k + 1)).length = k + 1 := aux_length_take_of_le h
  rw [hlen, List.take_take]
  have : min ((k + 1) - 1) (k + 1) = k := by omega
  rw [this]

private theorem aux_prefix_dropLast_of_prefix_of_lt {α : Type _} {u v : List α}
    (hpre : u <+: v) (hlt : u.length < v.length) :
    u <+: v.dropLast := by
  rw [List.prefix_iff_eq_take]
  rw [List.dropLast_eq_take, List.take_take]
  have : min u.length (v.length - 1) = u.length := by omega
  rw [this]
  exact (List.prefix_iff_eq_take.mp hpre)

private theorem aux_greedy_witness {u v : Addr N m} (h : u ≠ v) :
    ∃ z : Addr N m, z.1 = greedyW v.1 u.1 ∧ (graph N m).Adj u z ∧ dval z v + 1 = dval u v := by
  by_cases hpc : PrefixComp u v
  · rcases hpc with hpre | hpre
    · have hlt : u.tier < v.tier := by
        have hle := hpre.length_le
        have hne_len : u.1.length ≠ v.1.length := by
          intro hlen
          exact h (Addr.ext (List.IsPrefix.eq_of_length hpre hlen))
        unfold Addr.tier at *
        omega
      have hk : u.tier + 1 ≤ v.tier := by omega
      let z : Addr N m :=
        ⟨v.1.take (u.tier + 1), by
          have hlen : (v.1.take (u.tier + 1)).length = u.tier + 1 :=
            aux_length_take_of_le (by simpa [Addr.tier] using hk)
          constructor
          · exact List.ne_nil_of_length_pos (by rw [hlen]; omega)
          · have hv := Addr.tier_le v
            rw [hlen]
            omega⟩
      have hzlen : z.tier = u.tier + 1 := by
        dsimp [z, Addr.tier]
        exact aux_length_take_of_le (by simpa [Addr.tier] using hk)
      have hzpre : z.1 <+: v.1 := by
        dsimp [z]
        exact List.take_prefix _ _
      have hzdrop : z.1.dropLast = u.1 := by
        dsimp [z]
        rw [aux_dropLast_take_succ_of_le (by simpa [Addr.tier] using hk)]
        simpa [Addr.tier] using (List.prefix_iff_eq_take.mp hpre).symm
      have hne : u ≠ z := by
        intro huz
        have hlen_eq : u.tier = z.tier := by
          simpa using congrArg (fun a : Addr N m => a.tier) huz
        rw [hzlen] at hlen_eq
        omega
      have hadj : (graph N m).Adj u z := by
        change u ≠ z ∧ (Sib u z ∨ Par u z)
        refine ⟨hne, Or.inr (Or.inl ?_)⟩
        constructor
        · show z.1.length = u.1.length + 1
          simpa [Addr.tier] using hzlen
        · exact hzdrop
      have hword : z.1 = greedyW v.1 u.1 := by
        simp only [greedyW, if_pos hpre]
        rfl
      refine ⟨z, hword, hadj, ?_⟩
      have huv : PrefixComp u v := Or.inl hpre
      have hzv : PrefixComp z v := Or.inl hzpre
      unfold dval
      rw [if_pos hzv, if_pos huv]
      have hzlen' := hzlen
      unfold Addr.tier at *
      omega
    · have hlt : v.tier < u.tier := by
        have hle := hpre.length_le
        have hne_len : v.1.length ≠ u.1.length := by
          intro hlen
          exact h (Addr.ext (List.IsPrefix.eq_of_length hpre hlen).symm)
        unfold Addr.tier at *
        omega
      have htwo : 2 ≤ u.tier := by
        have hv := Addr.one_le_tier v
        omega
      let z : Addr N m :=
        ⟨u.1.dropLast, by
          have hlen : u.1.dropLast.length = u.tier - 1 := by
            simp [Addr.tier]
          constructor
          · exact List.ne_nil_of_length_pos (by rw [hlen]; omega)
          · have hu := Addr.tier_le u
            rw [hlen]
            omega⟩
      have hzlen : z.tier = u.tier - 1 := by
        dsimp [z, Addr.tier]
        rw [List.length_dropLast]
      have hzpre : v.1 <+: z.1 := by
        dsimp [z]
        exact aux_prefix_dropLast_of_prefix_of_lt hpre (by simpa [Addr.tier] using hlt)
      have hne : u ≠ z := by
        intro huz
        have hlen_eq : u.tier = z.tier := by
          simpa using congrArg (fun a : Addr N m => a.tier) huz
        rw [hzlen] at hlen_eq
        omega
      have hadj : (graph N m).Adj u z := by
        change u ≠ z ∧ (Sib u z ∨ Par u z)
        refine ⟨hne, Or.inr (Or.inr ?_)⟩
        constructor
        · show u.1.length = z.1.length + 1
          have hzlen' := hzlen
          unfold Addr.tier at *
          omega
        · rfl
      have hword : z.1 = greedyW v.1 u.1 := by
        have hnpre : ¬ u.1 <+: v.1 := by
          intro hp
          have := hp.length_le
          unfold Addr.tier at hlt
          omega
        have hlcp : lcp u.1 v.1 = v.1.length := by
          rw [lcp_comm]
          exact (lcp_eq_length_iff_prefix v.1 u.1).mpr hpre
        simp only [greedyW, if_neg hnpre, hlcp]
        split_ifs with he
        · have hz_eq : z.1 = v.1 := by
            apply (List.IsPrefix.eq_of_length hzpre ?_).symm
            dsimp [z]
            rw [List.length_dropLast]
            omega
          rw [hz_eq, List.take_of_length_le (by omega)]
        · rfl
      refine ⟨z, hword, hadj, ?_⟩
      have huv : PrefixComp u v := Or.inr hpre
      have hzv : PrefixComp z v := Or.inr hzpre
      unfold dval
      rw [if_pos hzv, if_pos huv]
      have hzlen' := hzlen
      unfold Addr.tier at *
      omega
  · have hlt_lcp := aux_lcp_lt_min_of_not_prefixComp hpc
    by_cases htier : u.tier = lcp u.1 v.1 + 1
    · have hk : lcp u.1 v.1 + 1 ≤ v.tier := by omega
      let z : Addr N m :=
        ⟨v.1.take (lcp u.1 v.1 + 1), by
          have hlen : (v.1.take (lcp u.1 v.1 + 1)).length =
              lcp u.1 v.1 + 1 :=
            aux_length_take_of_le (by simpa [Addr.tier] using hk)
          constructor
          · exact List.ne_nil_of_length_pos (by rw [hlen]; omega)
          · have hv := Addr.tier_le v
            rw [hlen]
            omega⟩
      have hzlen : z.tier = lcp u.1 v.1 + 1 := by
        dsimp [z, Addr.tier]
        exact aux_length_take_of_le (by simpa [Addr.tier] using hk)
      have hzpre : z.1 <+: v.1 := by
        dsimp [z]
        exact List.take_prefix _ _
      have hu_drop : u.1.dropLast = u.1.take (lcp u.1 v.1) := by
        exact aux_dropLast_eq_take_of_length_eq_succ (by simpa [Addr.tier] using htier)
      have hz_drop : z.1.dropLast = v.1.take (lcp u.1 v.1) := by
        dsimp [z]
        exact aux_dropLast_take_succ_of_le (by simpa [Addr.tier] using hk)
      have hdrop : u.1.dropLast = z.1.dropLast := by
        rw [hu_drop, hz_drop]
        exact take_lcp_eq u.1 v.1
      have hne : u ≠ z := by
        intro huz
        exact hpc (Or.inl (by simpa [huz] using hzpre))
      have hadj : (graph N m).Adj u z := by
        change u ≠ z ∧ (Sib u z ∨ Par u z)
        refine ⟨hne, Or.inl ?_⟩
        constructor
        · show u.1.length = z.1.length
          have hzlen' := hzlen
          unfold Addr.tier at *
          omega
        · exact hdrop
      have hword : z.1 = greedyW v.1 u.1 := by
        have hnpre : ¬ u.1 <+: v.1 := fun hp => hpc (Or.inl hp)
        simp only [greedyW, if_neg hnpre, show u.1.length = lcp u.1 v.1 + 1 from htier]
        rfl
      refine ⟨z, hword, hadj, ?_⟩
      have hzv : PrefixComp z v := Or.inl hzpre
      unfold dval
      rw [if_pos hzv, if_neg hpc]
      have hzlen' := hzlen
      unfold Addr.tier at *
      omega
    · have hge : lcp u.1 v.1 + 2 ≤ u.tier := by omega
      let z : Addr N m :=
        ⟨u.1.dropLast, by
          have hlen : u.1.dropLast.length = u.tier - 1 := by
            simp [Addr.tier]
          constructor
          · exact List.ne_nil_of_length_pos (by rw [hlen]; omega)
          · have hu := Addr.tier_le u
            rw [hlen]
            omega⟩
      have hzlen : z.tier = u.tier - 1 := by
        dsimp [z, Addr.tier]
        rw [List.length_dropLast]
      have hz_lcp : lcp z.1 v.1 = lcp u.1 v.1 := by
        dsimp [z]
        rw [aux_lcp_dropLast_left]
        exact min_eq_left (by
          unfold Addr.tier at hge
          omega)
      have hzlt_lcp : lcp z.1 v.1 < min z.tier v.tier := by
        rw [hz_lcp]
        have hzlen' := hzlen
        unfold Addr.tier at *
        omega
      have hzv_not : ¬ PrefixComp z v := by
        intro hzv
        have hzv_l := (prefixComp_iff_lcp z v).mp hzv
        omega
      have hne : u ≠ z := by
        intro huz
        have hlen_eq : u.tier = z.tier := by
          simpa using congrArg (fun a : Addr N m => a.tier) huz
        rw [hzlen] at hlen_eq
        omega
      have hadj : (graph N m).Adj u z := by
        change u ≠ z ∧ (Sib u z ∨ Par u z)
        refine ⟨hne, Or.inr (Or.inr ?_)⟩
        constructor
        · show u.1.length = z.1.length + 1
          have hzlen' := hzlen
          unfold Addr.tier at *
          omega
        · rfl
      have hword : z.1 = greedyW v.1 u.1 := by
        have hnpre : ¬ u.1 <+: v.1 := fun hp => hpc (Or.inl hp)
        have hntier : u.1.length ≠ lcp u.1 v.1 + 1 := htier
        simp only [greedyW, if_neg hnpre, if_neg hntier]
        rfl
      refine ⟨z, hword, hadj, ?_⟩
      unfold dval
      rw [if_neg hzv_not, if_neg hpc]
      rw [hz_lcp]
      have hzlen' := hzlen
      unfold Addr.tier at *
      omega

/-- The next hop is again an address. -/
theorem greedyW_valid (u v : Addr N m) (h : u ≠ v) :
    greedyW v.1 u.1 ≠ [] ∧ (greedyW v.1 u.1).length ≤ m := by
  obtain ⟨z, hz, _, _⟩ := aux_greedy_witness h
  rw [← hz]
  exact z.2

/-- The next hop, as an address. -/
def greedyStep (u v : Addr N m) (h : u ≠ v) : Addr N m :=
  ⟨greedyW v.1 u.1, greedyW_valid u v h⟩

/-- Every hop traverses an edge of the two-clause law. -/
theorem greedyStep_adj (u v : Addr N m) (h : u ≠ v) :
    (graph N m).Adj u (greedyStep u v h) := by
  obtain ⟨z, hz, hadj, _⟩ := aux_greedy_witness h
  have heq : z = greedyStep u v h := Addr.ext hz
  exact heq ▸ hadj

/-- Every hop decreases the distance to `v` by exactly one. -/
theorem dval_greedyStep (u v : Addr N m) (h : u ≠ v) :
    dval (greedyStep u v h) v + 1 = dval u v := by
  obtain ⟨z, hz, _, hd⟩ := aux_greedy_witness h
  have heq : z = greedyStep u v h := Addr.ext hz
  exact heq ▸ hd

/-- **Arrival after exactly `d(u,v)` hops** (Theorem thm:distance-II(ii)): iterating the
word-level rule `d(u,v)` times from `u` reaches `v`. -/
theorem greedyW_iterate (u v : Addr N m) :
    (greedyW v.1)^[dval u v] u.1 = v.1 := by
  generalize hn : dval u v = n
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
      by_cases huv : u = v
      · subst u
        simp only [dval_self] at hn
        subst n
        rfl
      · have hd := dval_greedyStep u v huv
        have hlt : dval (greedyStep u v huv) v < n := by omega
        have harr := ih _ hlt (greedyStep u v huv) rfl
        rw [← hn, ← hd, Function.iterate_succ_apply]
        exact harr

/-- No earlier arrival: before `d(u,v)` hops the packet is not at `v`. -/
theorem greedyW_iterate_ne (u v : Addr N m) {i : ℕ} (hi : i < dval u v) :
    (greedyW v.1)^[i] u.1 ≠ v.1 := by
  induction i generalizing u with
  | zero =>
      change u.1 ≠ v.1
      intro heq
      have huv := Addr.ext heq
      subst u
      rw [dval_self] at hi
      omega
  | succ i ih =>
      have huv : u ≠ v := by
        intro heq
        subst u
        rw [dval_self] at hi
        omega
      have hd := dval_greedyStep u v huv
      rw [Function.iterate_succ_apply]
      exact ih (greedyStep u v huv) (by omega)

end HSFN
