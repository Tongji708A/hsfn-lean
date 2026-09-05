/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Basic

/-!
# The exact HSFN metric (Theorem thm:distance-II)

The graph distance of the two-clause graph is

  `d(u,v) = |tier u - tier v|`                    if one address prefixes the other,
  `d(u,v) = tier u + tier v - 2·lcp(u,v) - 1`     otherwise.

Architecture (chosen for formalization economy):
* **Lower bound**: the candidate value `dval` is 1-Lipschitz along edges
  (`dval_lipschitz`); a trivial walk induction then gives `dval u v ≤ W.length`
  for every walk, hence `dval u v ≤ dist u v` on a geodesic.
* **Upper bound**: from every `u ≠ v` there is a neighbour strictly closer in
  `dval` (`exists_step`, the greedy hop of thm:distance-II(ii)); strong
  induction on `dval` yields reachability and `dist u v ≤ dval u v`.
Together: `dist = dval`, and the diameter `2m-1` follows arithmetically.
-/

namespace HSFN

variable {N m : ℕ}

/-! ## Longest common prefix -/

/-- Length of the longest common prefix of two words. -/
def lcp : List (Fin N) → List (Fin N) → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: as, b :: bs => if a = b then lcp as bs + 1 else 0

theorem lcp_comm : ∀ u v : List (Fin N), lcp u v = lcp v u
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
      simp only [lcp]
      by_cases h : a = b
      · rw [if_pos h, if_pos h.symm, lcp_comm as bs]
      · rw [if_neg h, if_neg (Ne.symm h)]

theorem lcp_le_left : ∀ u v : List (Fin N), lcp u v ≤ u.length
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.zero_le _
  | a :: as, b :: bs => by
      simp only [lcp, List.length_cons]
      split_ifs with h
      · exact Nat.succ_le_succ (lcp_le_left as bs)
      · exact Nat.zero_le _

theorem lcp_le_right (u v : List (Fin N)) : lcp u v ≤ v.length := by
  rw [lcp_comm]; exact lcp_le_left v u

theorem take_lcp_eq : ∀ u v : List (Fin N), u.take (lcp u v) = v.take (lcp u v)
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]
  | a :: as, b :: bs => by
      simp only [lcp]
      split_ifs with h
      · subst h
        simp only [List.take_succ_cons, List.cons.injEq, true_and]
        exact take_lcp_eq as bs
      · simp

theorem le_lcp_of_take_eq :
    ∀ (u v : List (Fin N)) (k : ℕ), k ≤ u.length → k ≤ v.length →
      u.take k = v.take k → k ≤ lcp u v
  | _, _, 0, _, _, _ => Nat.zero_le _
  | [], _, k + 1, h1, _, _ => by simp at h1
  | _ :: _, [], k + 1, _, h2, _ => by simp at h2
  | a :: as, b :: bs, k + 1, h1, h2, heq => by
      simp only [List.take_succ_cons, List.cons.injEq] at heq
      simp only [lcp, if_pos heq.1]
      exact Nat.succ_le_succ
        (le_lcp_of_take_eq as bs k (by simpa using h1) (by simpa using h2) heq.2)

theorem lcp_eq_length_iff_prefix (u v : List (Fin N)) :
    lcp u v = u.length ↔ u <+: v := by
  constructor
  · intro h
    have ht := take_lcp_eq u v
    rw [h, List.take_length] at ht
    exact ht ▸ List.take_prefix _ v
  · intro h
    refine le_antisymm (lcp_le_left u v) ?_
    refine le_lcp_of_take_eq u v u.length le_rfl h.length_le ?_
    rw [List.take_length]
    exact (List.prefix_iff_eq_take.mp h) ▸ rfl

/-- Just past the common prefix, the digits differ. -/
theorem getElem_lcp_ne :
    ∀ (u v : List (Fin N)) (h1 : lcp u v < u.length) (h2 : lcp u v < v.length),
      u[lcp u v]'h1 ≠ v[lcp u v]'h2
  | [], _, h1, _ => by simp [lcp] at h1
  | _ :: _, [], _, h2 => by simp [lcp] at h2
  | a :: as, b :: bs, h1, h2 => by
      by_cases h : a = b
      · have h1' : lcp as bs < as.length := by
          simp only [lcp, if_pos h, List.length_cons] at h1
          omega
        have h2' : lcp as bs < bs.length := by
          simp only [lcp, if_pos h, List.length_cons] at h2
          omega
        simp only [lcp, if_pos h, List.getElem_cons_succ]
        exact getElem_lcp_ne as bs h1' h2'
      · simp only [lcp, if_neg h, List.getElem_cons_zero]
        exact h

/-! ## The candidate distance -/

/-- Prefix-comparability: one address is a prefix of the other. -/
def PrefixComp (u v : Addr N m) : Prop := u.1 <+: v.1 ∨ v.1 <+: u.1

instance : ∀ u v : Addr N m, Decidable (PrefixComp u v) := fun _ _ => by
  unfold PrefixComp; infer_instance

theorem PrefixComp.comm {u v : Addr N m} (h : PrefixComp u v) : PrefixComp v u :=
  Or.symm h

/-- The candidate distance of Theorem thm:distance-II(i). -/
def dval (u v : Addr N m) : ℕ :=
  if PrefixComp u v then max u.tier v.tier - min u.tier v.tier
  else u.tier + v.tier - (2 * lcp u.1 v.1 + 1)

theorem dval_self (u : Addr N m) : dval u u = 0 := by
  simp [dval, PrefixComp, List.prefix_refl]

theorem dval_comm (u v : Addr N m) : dval u v = dval v u := by
  unfold dval
  by_cases h : PrefixComp u v
  · rw [if_pos h, if_pos h.comm, max_comm, min_comm]
  · rw [if_neg h, if_neg (fun h' => h h'.comm), lcp_comm]
    omega

/-- Prefix-comparability is equivalent to `lcp = min tier` (used throughout). -/
theorem prefixComp_iff_lcp (u v : Addr N m) :
    PrefixComp u v ↔ lcp u.1 v.1 = min u.tier v.tier := by
  unfold PrefixComp Addr.tier
  constructor
  · rintro (h | h)
    · have h1 : lcp u.1 v.1 = u.1.length := (lcp_eq_length_iff_prefix u.1 v.1).mpr h
      have h2 := h.length_le
      omega
    · have h1 : lcp v.1 u.1 = v.1.length := (lcp_eq_length_iff_prefix v.1 u.1).mpr h
      rw [lcp_comm] at h1
      have h2 := h.length_le
      omega
  · intro h
    rcases le_total u.1.length v.1.length with hle | hle
    · exact Or.inl ((lcp_eq_length_iff_prefix u.1 v.1).mp (by omega))
    · refine Or.inr ((lcp_eq_length_iff_prefix v.1 u.1).mp ?_)
      rw [lcp_comm]
      omega

theorem dval_pos_of_ne {u v : Addr N m} (h : u ≠ v) : 1 ≤ dval u v := by
  unfold dval
  by_cases hp : PrefixComp u v
  · rw [if_pos hp]
    -- comparable with equal tiers forces equality
    have : u.tier ≠ v.tier := by
      intro ht
      apply h
      rcases hp with hpre | hpre
      · exact Addr.ext (List.IsPrefix.eq_of_length hpre ht)
      · exact (Addr.ext (List.IsPrefix.eq_of_length hpre ht.symm)).symm
    omega
  · rw [if_neg hp]
    have hlt : lcp u.1 v.1 < min u.tier v.tier := by
      have h1 := lcp_le_left u.1 v.1
      have h2 := lcp_le_right u.1 v.1
      have h3 := (not_iff_not.mpr (prefixComp_iff_lcp u v)).mp hp
      unfold Addr.tier at *
      omega
    have h1 := Addr.one_le_tier u
    have h2 := Addr.one_le_tier v
    omega

/-! ## The two key local lemmas (leaf obligations) -/

private theorem lcp_take_left : ∀ (u v : List (Fin N)) (k : ℕ),
    lcp (u.take k) v = min (lcp u v) k
  | [], v, k => by simp [lcp]
  | a :: as, [], k => by cases k <;> simp [lcp]
  | a :: as, b :: bs, 0 => by simp [lcp]
  | a :: as, b :: bs, k + 1 => by
      simp only [List.take_succ_cons, lcp]
      by_cases h : a = b
      · rw [if_pos h, if_pos h]
        rw [lcp_take_left as bs k]
        exact (Nat.succ_min_succ (lcp as bs) k).symm
      · rw [if_neg h, if_neg h]
        simp

private theorem lcp_take_right (u v : List (Fin N)) (k : ℕ) :
    lcp u (v.take k) = min (lcp u v) k := by
  rw [lcp_comm, lcp_take_left, lcp_comm]

private theorem lcp_dropLast_left (u v : List (Fin N)) :
    lcp u.dropLast v = min (lcp u v) (u.length - 1) := by
  rw [List.dropLast_eq_take, lcp_take_left]

private theorem lcp_dropLast_right (u v : List (Fin N)) :
    lcp u v.dropLast = min (lcp u v) (v.length - 1) := by
  rw [lcp_comm, lcp_dropLast_left, lcp_comm]

private theorem lcp_of_child_dropLast {u z v : List (Fin N)}
    (hlen : z.length = u.length + 1) (hdrop : z.dropLast = u) :
    lcp u v = min (lcp z v) u.length := by
  calc
    lcp u v = lcp z.dropLast v := by rw [hdrop]
    _ = min (lcp z v) (z.length - 1) := lcp_dropLast_left z v
    _ = min (lcp z v) u.length := by
      have : z.length - 1 = u.length := by omega
      rw [this]

private theorem lcp_sib_drop_min {u z v : List (Fin N)}
    (hdrop : u.dropLast = z.dropLast) :
    min (lcp u v) (u.length - 1) = min (lcp z v) (z.length - 1) := by
  rw [Eq.symm (lcp_dropLast_left u v), Eq.symm (lcp_dropLast_left z v), hdrop]

private theorem lcp_lt_min_of_not_prefixComp {u v : Addr N m}
    (h : ¬ PrefixComp u v) :
    lcp u.1 v.1 < min u.tier v.tier := by
  have h1 := lcp_le_left u.1 v.1
  have h2 := lcp_le_right u.1 v.1
  have h3 := (not_iff_not.mpr (prefixComp_iff_lcp u v)).mp h
  unfold Addr.tier at *
  omega

private theorem length_take_of_le {α : Type _} {l : List α} {k : ℕ}
    (h : k ≤ l.length) :
    (l.take k).length = k := by
  rw [List.length_take]
  omega

private theorem dropLast_eq_take_of_length_eq_succ {α : Type _} {l : List α} {k : ℕ}
    (h : l.length = k + 1) :
    l.dropLast = l.take k := by
  rw [List.dropLast_eq_take]
  have : l.length - 1 = k := by omega
  rw [this]

private theorem dropLast_take_succ_of_le {α : Type _} {l : List α} {k : ℕ}
    (h : k + 1 ≤ l.length) :
    (l.take (k + 1)).dropLast = l.take k := by
  rw [List.dropLast_eq_take]
  have hlen : (l.take (k + 1)).length = k + 1 := length_take_of_le h
  rw [hlen, List.take_take]
  have : min ((k + 1) - 1) (k + 1) = k := by omega
  rw [this]

private theorem prefix_dropLast_of_prefix_of_lt {α : Type _} {u v : List α}
    (hpre : u <+: v) (hlt : u.length < v.length) :
    u <+: v.dropLast := by
  rw [List.prefix_iff_eq_take]
  rw [List.dropLast_eq_take, List.take_take]
  have : min u.length (v.length - 1) = u.length := by omega
  rw [this]
  exact (List.prefix_iff_eq_take.mp hpre)

/-- **Lipschitz along edges** (lower-bound engine): one hop changes the
candidate distance to a fixed target by at most one. Paper: Steps 1–3 of the
proof of thm:distance-II(i), localized. -/
theorem dval_lipschitz {u z v : Addr N m} (h : (graph N m).Adj u z) :
    dval u v ≤ dval z v + 1 := by
  rcases h with ⟨_, hS | hP⟩
  · rcases hS with ⟨hlen, hdrop⟩
    have hrel := lcp_sib_drop_min (v := v.1) hdrop
    unfold dval
    by_cases huv : PrefixComp u v <;> by_cases hzv : PrefixComp z v
    · have huv_l := (prefixComp_iff_lcp u v).mp huv
      have hzv_l := (prefixComp_iff_lcp z v).mp hzv
      rw [if_pos huv, if_pos hzv]
      unfold Addr.tier at *
      omega
    · have huv_l := (prefixComp_iff_lcp u v).mp huv
      have hzv_l := lcp_lt_min_of_not_prefixComp hzv
      rw [if_pos huv, if_neg hzv]
      unfold Addr.tier at *
      omega
    · have huv_l := lcp_lt_min_of_not_prefixComp huv
      have hzv_l := (prefixComp_iff_lcp z v).mp hzv
      rw [if_neg huv, if_pos hzv]
      unfold Addr.tier at *
      omega
    · have huv_l := lcp_lt_min_of_not_prefixComp huv
      have hzv_l := lcp_lt_min_of_not_prefixComp hzv
      rw [if_neg huv, if_neg hzv]
      unfold Addr.tier at *
      omega
  · rcases hP with hdown | hup
    · rcases hdown with ⟨hlen, hdrop⟩
      have hrel := lcp_of_child_dropLast (v := v.1) hlen hdrop
      unfold dval
      by_cases huv : PrefixComp u v <;> by_cases hzv : PrefixComp z v
      · have huv_l := (prefixComp_iff_lcp u v).mp huv
        have hzv_l := (prefixComp_iff_lcp z v).mp hzv
        rw [if_pos huv, if_pos hzv]
        unfold Addr.tier at *
        omega
      · have huv_l := (prefixComp_iff_lcp u v).mp huv
        have hzv_l := lcp_lt_min_of_not_prefixComp hzv
        rw [if_pos huv, if_neg hzv]
        unfold Addr.tier at *
        omega
      · have huv_l := lcp_lt_min_of_not_prefixComp huv
        have hzv_l := (prefixComp_iff_lcp z v).mp hzv
        rw [if_neg huv, if_pos hzv]
        unfold Addr.tier at *
        omega
      · have huv_l := lcp_lt_min_of_not_prefixComp huv
        have hzv_l := lcp_lt_min_of_not_prefixComp hzv
        rw [if_neg huv, if_neg hzv]
        unfold Addr.tier at *
        omega
    · rcases hup with ⟨hlen, hdrop⟩
      have hrel := lcp_of_child_dropLast (u := z.1) (z := u.1) (v := v.1) hlen hdrop
      unfold dval
      by_cases huv : PrefixComp u v <;> by_cases hzv : PrefixComp z v
      · have huv_l := (prefixComp_iff_lcp u v).mp huv
        have hzv_l := (prefixComp_iff_lcp z v).mp hzv
        rw [if_pos huv, if_pos hzv]
        unfold Addr.tier at *
        omega
      · have huv_l := (prefixComp_iff_lcp u v).mp huv
        have hzv_l := lcp_lt_min_of_not_prefixComp hzv
        rw [if_pos huv, if_neg hzv]
        unfold Addr.tier at *
        omega
      · have huv_l := lcp_lt_min_of_not_prefixComp huv
        have hzv_l := (prefixComp_iff_lcp z v).mp hzv
        rw [if_neg huv, if_pos hzv]
        unfold Addr.tier at *
        omega
      · have huv_l := lcp_lt_min_of_not_prefixComp huv
        have hzv_l := lcp_lt_min_of_not_prefixComp hzv
        rw [if_neg huv, if_neg hzv]
        unfold Addr.tier at *
        omega

/-- **Greedy step** (upper-bound engine, thm:distance-II(ii)): from `u ≠ v`
some neighbour is strictly closer in `dval`; concretely the child
`pre_{|u|+1}(v)` when `u` prefixes `v`, the sibling `pre_{λ+1}(v)` when
incomparable at tier `λ+1`, and the anchor otherwise. -/
theorem exists_step {u v : Addr N m} (h : u ≠ v) :
    ∃ z : Addr N m, (graph N m).Adj u z ∧ dval z v + 1 = dval u v := by
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
            length_take_of_le (by simpa [Addr.tier] using hk)
          constructor
          · exact List.ne_nil_of_length_pos (by rw [hlen]; omega)
          · have hv := Addr.tier_le v
            rw [hlen]
            omega⟩
      have hzlen : z.tier = u.tier + 1 := by
        dsimp [z, Addr.tier]
        exact length_take_of_le (by simpa [Addr.tier] using hk)
      have hzpre : z.1 <+: v.1 := by
        dsimp [z]
        exact List.take_prefix _ _
      have hzdrop : z.1.dropLast = u.1 := by
        dsimp [z]
        rw [dropLast_take_succ_of_le (by simpa [Addr.tier] using hk)]
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
      refine ⟨z, hadj, ?_⟩
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
        exact prefix_dropLast_of_prefix_of_lt hpre (by simpa [Addr.tier] using hlt)
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
      refine ⟨z, hadj, ?_⟩
      have huv : PrefixComp u v := Or.inr hpre
      have hzv : PrefixComp z v := Or.inr hzpre
      unfold dval
      rw [if_pos hzv, if_pos huv]
      have hzlen' := hzlen
      unfold Addr.tier at *
      omega
  · have hlt_lcp := lcp_lt_min_of_not_prefixComp hpc
    by_cases htier : u.tier = lcp u.1 v.1 + 1
    · have hk : lcp u.1 v.1 + 1 ≤ v.tier := by omega
      let z : Addr N m :=
        ⟨v.1.take (lcp u.1 v.1 + 1), by
          have hlen : (v.1.take (lcp u.1 v.1 + 1)).length =
              lcp u.1 v.1 + 1 :=
            length_take_of_le (by simpa [Addr.tier] using hk)
          constructor
          · exact List.ne_nil_of_length_pos (by rw [hlen]; omega)
          · have hv := Addr.tier_le v
            rw [hlen]
            omega⟩
      have hzlen : z.tier = lcp u.1 v.1 + 1 := by
        dsimp [z, Addr.tier]
        exact length_take_of_le (by simpa [Addr.tier] using hk)
      have hzpre : z.1 <+: v.1 := by
        dsimp [z]
        exact List.take_prefix _ _
      have hu_drop : u.1.dropLast = u.1.take (lcp u.1 v.1) := by
        exact dropLast_eq_take_of_length_eq_succ (by simpa [Addr.tier] using htier)
      have hz_drop : z.1.dropLast = v.1.take (lcp u.1 v.1) := by
        dsimp [z]
        exact dropLast_take_succ_of_le (by simpa [Addr.tier] using hk)
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
      refine ⟨z, hadj, ?_⟩
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
        rw [lcp_dropLast_left]
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
      refine ⟨z, hadj, ?_⟩
      unfold dval
      rw [if_neg hzv_not, if_neg hpc]
      rw [hz_lcp]
      have hzlen' := hzlen
      unfold Addr.tier at *
      omega

/-! ## Assembly: dist = dval -/

theorem dval_le_walk_length {u v : Addr N m} (W : (graph N m).Walk u v) :
    dval u v ≤ W.length := by
  induction W with
  | nil => simp [dval_self]
  | @cons a b c hadj W ih =>
      have h1 : dval a c ≤ dval b c + 1 := dval_lipschitz hadj
      simp only [SimpleGraph.Walk.length_cons]
      omega

theorem reachable_and_dist_le (v : Addr N m) :
    ∀ n (u : Addr N m), dval u v ≤ n →
      (graph N m).Reachable u v ∧ (graph N m).dist u v ≤ dval u v := by
  intro n
  induction n with
  | zero =>
      intro u hu
      have h0 : dval u v = 0 := Nat.le_zero.mp hu
      have huv : u = v := by
        by_contra hne
        have := dval_pos_of_ne hne
        omega
      subst huv
      exact ⟨SimpleGraph.Reachable.refl u, by simp [h0]⟩
  | succ k ih =>
      intro u hu
      by_cases huv : u = v
      · subst huv
        exact ⟨SimpleGraph.Reachable.refl u, by simp [dval_self]⟩
      · obtain ⟨z, hadj, hz⟩ := exists_step huv
        have hzk : dval z v ≤ k := by omega
        obtain ⟨hreach, hdist⟩ := ih z hzk
        refine ⟨(SimpleGraph.Adj.reachable hadj).trans hreach, ?_⟩
        obtain ⟨W, hW⟩ := hreach.exists_walk_length_eq_dist
        have h1 : (graph N m).dist u v ≤ (SimpleGraph.Walk.cons hadj W).length :=
          SimpleGraph.dist_le _
        simp only [SimpleGraph.Walk.length_cons] at h1
        omega

/-- **The exact HSFN metric** (Theorem thm:distance-II(i)). -/
theorem dist_eq_dval (u v : Addr N m) :
    (graph N m).dist u v = dval u v := by
  obtain ⟨hreach, hle⟩ := reachable_and_dist_le v (dval u v) u le_rfl
  refine le_antisymm hle ?_
  obtain ⟨W, hW⟩ := hreach.exists_walk_length_eq_dist
  have := dval_le_walk_length W
  omega

/-- The HSFN graph is connected (every pair of addresses is reachable). -/
theorem graph_connected (u v : Addr N m) : (graph N m).Reachable u v :=
  (reachable_and_dist_le v (dval u v) u le_rfl).1

/-! ## Diameter (Theorem thm:distance-II(iii)) -/

theorem dval_le_diam (u v : Addr N m) : dval u v ≤ 2 * m - 1 := by
  have h1 := Addr.one_le_tier u
  have h2 := Addr.one_le_tier v
  have h3 := Addr.tier_le u
  have h4 := Addr.tier_le v
  unfold dval
  split_ifs
  · omega
  · omega

theorem dist_le_diam (u v : Addr N m) : (graph N m).dist u v ≤ 2 * m - 1 := by
  rw [dist_eq_dval]; exact dval_le_diam u v

/-- The diameter is attained (for `N ≥ 2`): the all-`0` and all-`1` words at
tier `m` are at distance exactly `2m - 1`. -/
theorem exists_dist_eq_diam (hN : 2 ≤ N) (hm : 1 ≤ m) :
    ∃ u v : Addr N m, (graph N m).dist u v = 2 * m - 1 := by
  have hrep : ∀ x : Fin N, List.replicate m x ≠ [] := by
    intro x hx
    have h2 := congrArg List.length hx
    simp at h2
    omega
  refine ⟨⟨List.replicate m ⟨0, by omega⟩, hrep _, by simp⟩,
          ⟨List.replicate m ⟨1, by omega⟩, hrep _, by simp⟩, ?_⟩
  · rw [dist_eq_dval]
    have hne0 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
      simp [Fin.ext_iff]
    have hlcp : lcp (List.replicate m (⟨0, by omega⟩ : Fin N))
        (List.replicate m ⟨1, by omega⟩) = 0 := by
      cases m with
      | zero => omega
      | succ k =>
          simp only [List.replicate_succ, lcp]
          rw [if_neg hne0]
    have hpc : ¬ PrefixComp
        (⟨List.replicate m ⟨0, by omega⟩, hrep _, by simp⟩ : Addr N m)
        (⟨List.replicate m ⟨1, by omega⟩, hrep _, by simp⟩ : Addr N m) := by
      rw [prefixComp_iff_lcp]
      simp only [Addr.tier, List.length_replicate]
      rw [hlcp]
      omega
    unfold dval
    rw [if_neg hpc]
    simp only [Addr.tier, List.length_replicate]
    rw [hlcp]
    omega

end HSFN
