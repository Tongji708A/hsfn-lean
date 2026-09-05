/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Family

/-!
# Cell-wise relabelings are automorphisms (Lemma lem:dup-digit(ii))

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
A family `τ` of digit permutations indexed by words (the permutation `τ w` acts on the
digit that follows the prefix `w`) induces the map
`φ(a_1 ⋯ a_t) = b_1 ⋯ b_t`, `b_s = τ (a_1 ⋯ a_{s-1}) (a_s)`.
It is a bijection of the address set and an automorphism of the graph. It preserves
the marking (digit-`0` duplicates at tier `≥ 2`) whenever every non-root permutation
fixes `0`; if some non-root permutation moves `0` at a word that has room below it,
some mark is moved. The statements below are frozen; only the proofs are to be
supplied.
-/

namespace HSFN

variable {N m : ℕ}

/-- Apply the prefix-indexed digit permutations along a word, accumulating the prefix. -/
def relabelAux (τ : List (Fin N) → Equiv.Perm (Fin N)) :
    List (Fin N) → List (Fin N) → List (Fin N)
  | _, [] => []
  | pre, d :: rest => τ pre d :: relabelAux τ (pre ++ [d]) rest

/-- The induced relabeling of words, `φ(a)` with `b_s = τ(pre_{s-1} a)(a_s)`. -/
def relabel (τ : List (Fin N) → Equiv.Perm (Fin N)) (a : List (Fin N)) : List (Fin N) :=
  relabelAux τ [] a

theorem length_relabelAux (τ : List (Fin N) → Equiv.Perm (Fin N)) (pre l : List (Fin N)) :
    (relabelAux τ pre l).length = l.length := by
  induction l generalizing pre with
  | nil => simp [relabelAux]
  | cons d rest ih => simp [relabelAux, ih]

/-- The relabeling of an address is an address. -/
def relabelAddr (τ : List (Fin N) → Equiv.Perm (Fin N)) (a : Addr N m) : Addr N m :=
  ⟨relabel τ a.1, by
    unfold relabel
    constructor
    · intro h
      have := congrArg List.length h
      rw [length_relabelAux] at this
      exact a.2.1 (List.length_eq_zero_iff.mp this)
    · rw [length_relabelAux]; exact a.2.2⟩

private theorem aux_relabelAux_take (τ : List (Fin N) → Equiv.Perm (Fin N))
    (pre l : List (Fin N)) (s : ℕ) :
    (relabelAux τ pre l).take s = relabelAux τ pre (l.take s) := by
  induction l generalizing pre s with
  | nil => simp [relabelAux]
  | cons d rest ih =>
    cases s with
    | zero => simp [relabelAux]
    | succ s => simp [relabelAux, List.take_succ_cons, ih]

/-- Prefixes are respected: relabeling commutes with `take`. -/
theorem relabel_take (τ : List (Fin N) → Equiv.Perm (Fin N)) (a : List (Fin N)) (s : ℕ) :
    (relabel τ a).take s = relabel τ (a.take s) :=
  aux_relabelAux_take τ [] a s

private theorem aux_relabelAux_injective (τ : List (Fin N) → Equiv.Perm (Fin N))
    (pre : List (Fin N)) : Function.Injective (relabelAux τ pre) := by
  intro l₁ l₂
  induction l₁ generalizing pre l₂ with
  | nil =>
    intro h
    cases l₂ with
    | nil => rfl
    | cons _ _ => simp [relabelAux] at h
  | cons d rest ih =>
    intro h
    cases l₂ with
    | nil => simp [relabelAux] at h
    | cons d' rest' =>
      simp only [relabelAux, List.cons.injEq] at h
      obtain ⟨hhead, htail⟩ := h
      have hd : d = d' := (τ pre).injective hhead
      subst hd
      rw [ih (pre ++ [d]) htail]

/-- The relabeling is injective on words. -/
theorem relabel_injective (τ : List (Fin N) → Equiv.Perm (Fin N)) :
    Function.Injective (relabel τ) :=
  aux_relabelAux_injective τ []

/-- The induced map on addresses is a bijection. -/
theorem relabelAddr_bijective (τ : List (Fin N) → Equiv.Perm (Fin N)) :
    Function.Bijective (relabelAddr (m := m) τ) := by
  have hinj : Function.Injective (relabelAddr (m := m) τ) := by
    intro a b h
    apply Addr.ext
    exact relabel_injective τ (congrArg Subtype.val h)
  exact hinj.bijective_of_finite

theorem tier_relabelAddr (τ : List (Fin N) → Equiv.Perm (Fin N)) (a : Addr N m) :
    (relabelAddr τ a).tier = a.tier := by
  simp [relabelAddr, Addr.tier, relabel, length_relabelAux]

private theorem aux_length_relabel (τ : List (Fin N) → Equiv.Perm (Fin N)) (l : List (Fin N)) :
    (relabel τ l).length = l.length :=
  length_relabelAux τ [] l

private theorem aux_relabel_dropLast (τ : List (Fin N) → Equiv.Perm (Fin N)) (l : List (Fin N)) :
    (relabel τ l).dropLast = relabel τ l.dropLast := by
  rw [List.dropLast_eq_take, List.dropLast_eq_take, relabel_take, aux_length_relabel]

private theorem aux_sib_relabelAddr (τ : List (Fin N) → Equiv.Perm (Fin N)) (u v : Addr N m) :
    Sib (relabelAddr τ u) (relabelAddr τ v) ↔ Sib u v := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [relabelAddr, relabel, length_relabelAux] using h.1
    · have := h.2
      simp only [relabelAddr] at this
      rw [aux_relabel_dropLast, aux_relabel_dropLast] at this
      exact relabel_injective τ this
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [relabelAddr, relabel, length_relabelAux] using h.1
    · simp only [relabelAddr]
      rw [aux_relabel_dropLast, aux_relabel_dropLast, h.2]

private theorem aux_par_relabelAddr (τ : List (Fin N) → Equiv.Perm (Fin N)) (u v : Addr N m) :
    Par (relabelAddr τ u) (relabelAddr τ v) ↔ Par u v := by
  constructor
  · rintro (⟨hlen, hpre⟩ | ⟨hlen, hpre⟩)
    · refine Or.inl ⟨?_, ?_⟩
      · simpa [relabelAddr, relabel, length_relabelAux] using hlen
      · simp only [relabelAddr] at hpre
        rw [aux_relabel_dropLast] at hpre
        exact relabel_injective τ hpre
    · refine Or.inr ⟨?_, ?_⟩
      · simpa [relabelAddr, relabel, length_relabelAux] using hlen
      · simp only [relabelAddr] at hpre
        rw [aux_relabel_dropLast] at hpre
        exact relabel_injective τ hpre
  · rintro (⟨hlen, hpre⟩ | ⟨hlen, hpre⟩)
    · refine Or.inl ⟨?_, ?_⟩
      · simpa [relabelAddr, relabel, length_relabelAux] using hlen
      · simp only [relabelAddr]
        rw [aux_relabel_dropLast, hpre]
    · refine Or.inr ⟨?_, ?_⟩
      · simpa [relabelAddr, relabel, length_relabelAux] using hlen
      · simp only [relabelAddr]
        rw [aux_relabel_dropLast, hpre]

/-- **Automorphism** (Lemma lem:dup-digit(ii)): the relabeling preserves and reflects
adjacency. -/
theorem adj_relabelAddr_iff (τ : List (Fin N) → Equiv.Perm (Fin N)) (u v : Addr N m) :
    (graph N m).Adj (relabelAddr τ u) (relabelAddr τ v) ↔ (graph N m).Adj u v := by
  have hinj : Function.Injective (relabelAddr (m := m) τ) :=
    (relabelAddr_bijective (m := m) τ).1
  change (_ ≠ _ ∧ (_ ∨ _)) ↔ (_ ≠ _ ∧ (_ ∨ _))
  rw [aux_sib_relabelAddr, aux_par_relabelAddr, hinj.ne_iff]

private theorem aux_getLast?_relabelAux (τ : List (Fin N) → Equiv.Perm (Fin N))
    (pre l : List (Fin N)) (hl : l ≠ []) :
    (relabelAux τ pre l).getLast? =
      some (τ (pre ++ l.dropLast) (l.getLast hl)) := by
  induction l generalizing pre with
  | nil => exact (hl rfl).elim
  | cons d rest ih =>
    cases rest with
    | nil =>
      simp [relabelAux]
    | cons d' rest' =>
      have hrest : d' :: rest' ≠ [] := List.cons_ne_nil _ _
      have htail : relabelAux τ (pre ++ [d]) (d' :: rest') ≠ [] := by
        intro h
        have := congrArg List.length h
        simp [length_relabelAux] at this
      change (τ pre d :: relabelAux τ (pre ++ [d]) (d' :: rest')).getLast? = _
      rw [List.getLast?_cons_of_ne_nil htail, ih (pre ++ [d]) hrest]
      have hlast : (d :: d' :: rest').getLast hl = (d' :: rest').getLast hrest :=
        List.getLast_cons hrest
      have hdrop : (d :: d' :: rest').dropLast = d :: (d' :: rest').dropLast := rfl
      apply congrArg some
      apply congrArg₂ (fun p x => τ p x)
      · rw [hdrop]
        exact (List.append_cons pre d (d' :: rest').dropLast).symm
      · exact hlast.symm

/-- The marking is preserved when every non-root permutation fixes the digit `0`. -/
theorem isMark_relabelAddr_iff (τ : List (Fin N) → Equiv.Perm (Fin N)) (hN : 0 < N)
    (hτ : ∀ w : List (Fin N), w ≠ [] → τ w ⟨0, hN⟩ = ⟨0, hN⟩) (a : Addr N m) :
    IsMark (relabelAddr τ a) ↔ IsMark a := by
  unfold IsMark
  rw [tier_relabelAddr]
  have hne : a.1 ≠ [] := a.2.1
  have hlast :
      (relabel τ a.1).getLast? = some (τ a.1.dropLast (a.1.getLast hne)) := by
    simpa [relabel, List.nil_append] using aux_getLast?_relabelAux τ [] a.1 hne
  constructor
  · rintro ⟨h2, hmark⟩
    refine ⟨h2, ?_⟩
    intro d hd
    have hdrop : a.1.dropLast ≠ [] := by
      have : 1 < a.1.length := Nat.succ_le_iff.mp (by simpa [Addr.tier] using h2)
      intro hempty
      have : a.1.dropLast.length = 0 := by simp [hempty]
      rw [List.length_dropLast] at this
      omega
    have hd0 : d = a.1.getLast hne := by
      have : some d = some (a.1.getLast hne) := by
        rw [← List.getLast?_eq_some_getLast hne]
        exact hd.symm
      exact Option.some.inj this
    subst hd0
    have hτd := hmark (τ a.1.dropLast (a.1.getLast hne)) (by
      simpa [relabelAddr] using hlast)
    have hfix : τ a.1.dropLast ⟨0, hN⟩ = ⟨0, hN⟩ := hτ _ hdrop
    have : τ a.1.dropLast (a.1.getLast hne) = τ a.1.dropLast ⟨0, hN⟩ := by
      apply Fin.ext
      simpa [hfix] using hτd
    have hinj := (τ a.1.dropLast).injective this
    simpa [Fin.ext_iff] using hinj
  · rintro ⟨h2, hmark⟩
    refine ⟨h2, ?_⟩
    intro d hd
    have hdrop : a.1.dropLast ≠ [] := by
      have : 1 < a.1.length := Nat.succ_le_iff.mp (by simpa [Addr.tier] using h2)
      intro hempty
      have : a.1.dropLast.length = 0 := by simp [hempty]
      rw [List.length_dropLast] at this
      omega
    have hdτ : d = τ a.1.dropLast (a.1.getLast hne) := by
      have : some d = some (τ a.1.dropLast (a.1.getLast hne)) := by
        rw [← hlast]
        simpa [relabelAddr] using hd.symm
      exact Option.some.inj this
    subst hdτ
    have hlast0 : (a.1.getLast hne).val = 0 :=
      hmark (a.1.getLast hne) (List.getLast?_eq_some_getLast hne)
    have hfin : a.1.getLast hne = ⟨0, hN⟩ := Fin.ext hlast0
    rw [hfin, hτ _ hdrop]

/-- Conversely, a non-root permutation that moves `0` at a word with room below it
moves a mark: the marked address `w0` is sent to an unmarked one. -/
theorem exists_mark_moved (τ : List (Fin N) → Equiv.Perm (Fin N)) (hN : 0 < N)
    {w : List (Fin N)} (hw : w ≠ []) (hwm : w.length < m) (hτ : τ w ⟨0, hN⟩ ≠ ⟨0, hN⟩) :
    ∃ a : Addr N m, IsMark a ∧ ¬ IsMark (relabelAddr τ a) := by
  let d0 : Fin N := ⟨0, hN⟩
  have hne : w ++ [d0] ≠ [] := by simp
  have hlen : (w ++ [d0]).length ≤ m := by
    simp [List.length_append]
    omega
  let a : Addr N m := ⟨w ++ [d0], And.intro hne hlen⟩
  refine ⟨a, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have : 1 ≤ w.length := List.length_pos_of_ne_nil hw
      simp [Addr.tier, a, List.length_append]
      omega
    · intro d hd
      have : (w ++ [d0]).getLast? = some d0 := List.getLast?_concat
      simp only [a] at hd
      have hd0 : some d = some d0 := hd.symm.trans this
      have : d = d0 := Option.some.inj hd0
      simp [this, d0]
  · intro hmark
    have hlast :
        (relabel τ a.1).getLast? = some (τ w d0) := by
      have hl := aux_getLast?_relabelAux τ [] a.1 a.2.1
      have hdrop : a.1.dropLast = w := by
        change (w ++ [d0]).dropLast = w
        exact List.dropLast_concat
      have hget : a.1.getLast a.2.1 = d0 := by
        change (w ++ [d0]).getLast _ = d0
        rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil d0 [])]
        rfl
      unfold relabel
      simpa [hdrop, hget] using hl
    have h2 : 2 ≤ (relabelAddr τ a).tier := by
      have : 1 ≤ w.length := List.length_pos_of_ne_nil hw
      rw [tier_relabelAddr]
      simp [Addr.tier, a, List.length_append]
      omega
    have hzero := hmark.2 (τ w d0) (by
      simpa [relabelAddr] using hlast)
    have : τ w d0 = d0 := Fin.ext hzero
    exact hτ this

end HSFN
