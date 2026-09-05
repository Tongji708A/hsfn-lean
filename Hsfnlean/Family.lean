/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Distance

/-!
# Family monotonicity (Lemma lem:family-mono)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
For `N ≤ N'` and `m ≤ m'` the inclusion of address sets realizes `F(N,m)` as an
induced subnetwork of `F(N',m')`: adjacency is preserved and reflected, tiers,
marks (digit-`0` duplicates) and the exact distance are preserved, and the
inclusions compose. The statements below are frozen; only the proofs are to be
supplied.
-/

namespace HSFN

variable {N N' N'' m m' m'' : ℕ}

/-- The inclusion `Addr N m → Addr N' m'`, digit by digit via `Fin.castLE`. -/
def castAddr (hN : N ≤ N') (hm : m ≤ m') (a : Addr N m) : Addr N' m' :=
  ⟨a.1.map (Fin.castLE hN),
    by simpa using a.2.1,
    by simpa using a.2.2.trans hm⟩

/-- The inclusion is injective. -/
theorem castAddr_injective (hN : N ≤ N') (hm : m ≤ m') :
    Function.Injective (castAddr hN hm) := by
  intro a b h
  apply Addr.ext
  exact (List.map_injective_iff.mpr (Fin.castLE_injective hN))
    (congrArg Subtype.val h)

/-- Tiers are preserved. -/
theorem tier_castAddr (hN : N ≤ N') (hm : m ≤ m') (a : Addr N m) :
    (castAddr hN hm a).tier = a.tier := by
  simp [castAddr, Addr.tier]

/-- Inclusions compose. -/
theorem castAddr_castAddr (hN : N ≤ N') (hm : m ≤ m') (hN' : N' ≤ N'') (hm' : m' ≤ m'')
    (a : Addr N m) :
    castAddr hN' hm' (castAddr hN hm a) = castAddr (hN.trans hN') (hm.trans hm') a := by
  apply Addr.ext
  simp [castAddr, List.map_map, Fin.castLE_comp_castLE]

private theorem aux_map_castLE_dropLast (hN : N ≤ N') (u : List (Fin N)) :
    (u.map (Fin.castLE hN)).dropLast = u.dropLast.map (Fin.castLE hN) :=
  List.map_dropLast.symm

private theorem aux_sib_castAddr (hN : N ≤ N') (hm : m ≤ m') (u v : Addr N m) :
    Sib (castAddr hN hm u) (castAddr hN hm v) ↔ Sib u v := by
  have hinj : Function.Injective (List.map (Fin.castLE hN)) :=
    List.map_injective_iff.mpr (Fin.castLE_injective hN)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [castAddr] using h.1
    · have := h.2
      simp only [castAddr] at this
      rw [aux_map_castLE_dropLast, aux_map_castLE_dropLast] at this
      exact hinj this
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [castAddr] using h.1
    · simp only [castAddr]
      rw [aux_map_castLE_dropLast, aux_map_castLE_dropLast, h.2]

private theorem aux_par_castAddr (hN : N ≤ N') (hm : m ≤ m') (u v : Addr N m) :
    Par (castAddr hN hm u) (castAddr hN hm v) ↔ Par u v := by
  have hinj : Function.Injective (List.map (Fin.castLE hN)) :=
    List.map_injective_iff.mpr (Fin.castLE_injective hN)
  constructor
  · rintro (⟨hlen, hpre⟩ | ⟨hlen, hpre⟩)
    · refine Or.inl ⟨?_, ?_⟩
      · simpa [castAddr] using hlen
      · simp only [castAddr] at hpre
        rw [aux_map_castLE_dropLast] at hpre
        exact hinj hpre
    · refine Or.inr ⟨?_, ?_⟩
      · simpa [castAddr] using hlen
      · simp only [castAddr] at hpre
        rw [aux_map_castLE_dropLast] at hpre
        exact hinj hpre
  · rintro (⟨hlen, hpre⟩ | ⟨hlen, hpre⟩)
    · refine Or.inl ⟨?_, ?_⟩
      · simpa [castAddr] using hlen
      · simp only [castAddr]
        rw [aux_map_castLE_dropLast, hpre]
    · refine Or.inr ⟨?_, ?_⟩
      · simpa [castAddr] using hlen
      · simp only [castAddr]
        rw [aux_map_castLE_dropLast, hpre]

/-- Adjacency is preserved and reflected: `F(N,m)` is an induced subgraph of
`F(N',m')`. -/
theorem adj_castAddr_iff (hN : N ≤ N') (hm : m ≤ m') (u v : Addr N m) :
    (graph N' m').Adj (castAddr hN hm u) (castAddr hN hm v) ↔ (graph N m).Adj u v := by
  change (_ ≠ _ ∧ (_ ∨ _)) ↔ (_ ≠ _ ∧ (_ ∨ _))
  rw [aux_sib_castAddr, aux_par_castAddr,
      (castAddr_injective hN hm).ne_iff]

/-- The longest common prefix is unchanged by the digit inclusion. -/
theorem lcp_map_castLE (hN : N ≤ N') (u v : List (Fin N)) :
    lcp (u.map (Fin.castLE hN)) (v.map (Fin.castLE hN)) = lcp u v := by
  induction u generalizing v with
  | nil => simp [lcp]
  | cons a as ih =>
      cases v with
      | nil => simp [lcp]
      | cons b bs =>
          simp only [List.map_cons, lcp, Fin.castLE_inj]
          split_ifs
          · rw [ih]
          · rfl

/-- The candidate distance is preserved. -/
theorem dval_castAddr (hN : N ≤ N') (hm : m ≤ m') (u v : Addr N m) :
    dval (castAddr hN hm u) (castAddr hN hm v) = dval u v := by
  have ht_u := tier_castAddr hN hm u
  have ht_v := tier_castAddr hN hm v
  have hlcp : lcp (castAddr hN hm u).1 (castAddr hN hm v).1 = lcp u.1 v.1 := by
    simp [castAddr, lcp_map_castLE]
  unfold dval
  simp_rw [prefixComp_iff_lcp, ht_u, ht_v, hlcp]

/-- **Family monotonicity is isometric** (Lemma lem:family-mono): graph
distances are preserved by the inclusion. -/
theorem dist_castAddr (hN : N ≤ N') (hm : m ≤ m') (u v : Addr N m) :
    (graph N' m').dist (castAddr hN hm u) (castAddr hN hm v) = (graph N m).dist u v := by
  rw [dist_eq_dval, dist_eq_dval, dval_castAddr]

/-- A marked (duplicate) address: tier at least `2` and final digit `0`. -/
def IsMark (a : Addr N m) : Prop :=
  2 ≤ a.tier ∧ ∀ d : Fin N, a.1.getLast? = some d → d.val = 0

/-- Marks are preserved and reflected by the inclusion. -/
theorem isMark_castAddr_iff (hN : N ≤ N') (hm : m ≤ m') (a : Addr N m) :
    IsMark (castAddr hN hm a) ↔ IsMark a := by
  unfold IsMark
  rw [tier_castAddr]
  simp only [castAddr, List.getLast?_map]
  constructor
  · rintro ⟨h2, hlast⟩
    refine ⟨h2, ?_⟩
    intro d hd
    have := hlast (Fin.castLE hN d) (by simp [hd])
    simpa [Fin.val_castLE] using this
  · rintro ⟨h2, hlast⟩
    refine ⟨h2, ?_⟩
    intro d' hd'
    rw [Option.map_eq_some_iff] at hd'
    obtain ⟨d₀, hd₀, hcast⟩ := hd'
    have := hlast d₀ hd₀
    rw [← hcast, Fin.val_castLE]
    exact this

end HSFN
