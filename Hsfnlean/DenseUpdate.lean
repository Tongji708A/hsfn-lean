/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Mathlib

/-!
# Dense-variant cyclic update order (Theorem thm:appendix-update-correct)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409),
Appendix `app:update` ("Detailed Update Ordering Formulas"), together with
Proposition `prop:consensus-tree` items 2 and 3.

The dense variant labels its facets by *subscript-pair* words
`ℓ = ((r₁,j₁), …, (r_d,j_d))` with `rᵢ : Fin N` and `jᵢ : Bool`, subject to the
grammar of Section `subsec:duality`: the first pair has `j₁ = 0`, and consecutive
first components differ (`rᵢ₊₁ ≠ rᵢ`).  This is `Valid` below; `Label_{N,d}` is
`{ℓ // Valid ℓ ∧ ℓ.length = d}` and the consensus labels `𝓛^≤_{N,m}` are the
valid words of length at most `m-1`, the empty word being the root `Θ_(0,0)`.
Each consensus label `ℓ` carries the `N` network nodes `v_{ℓ,(i,0)}`
(Definition `def:consensus-node`), so the node set `V_{N,m}` is modelled as the
pairs `(ℓ, i)` with `ℓ` a consensus label and `i : Fin N` (`DNode` below).

Formalized here:

* `valid_append_iff`, `veto_iff_eq_last`, `existsUnique_veto` — eq:app-k0 and
  item (1) of Theorem thm:appendix-update-correct: the vetoed first component
  below a non-root label is unique and equals `last ℓ`.
* `childList` — the ordered child list eq:app-children, with
  `length_childList_root` (`N` children at the root) and
  `length_childList_of_ne_nil` (`2(N-1)` children elsewhere), which are
  Proposition prop:consensus-tree items 2 and 3.
* `dfsD` / `dfsList` — the depth-first list eq:app-dfs, shown repetition-free
  (`dfsList_nodup`) and complete (`mem_dfsList`), which is item (2);
  `dfsD_eq_childList` is the bridge that unfolds `dfsD` through the paper's
  ordered child list `𝓒_m` of eq:app-children.
* `dfsList_formPerm_isCycle` and `dfsList_formPerm_support` — the wrap-around
  successor map eq:app-successor is a single cycle on `V_{N,m}`, item (3);
  stated exactly as `Hsfnlean.Update` states the HSFN analogue
  (Theorem thm:update-main).

`dfsD N k ℓ` is `𝓓_m(ℓ)` with `k` tiers of room at and below `ℓ`, so
`𝓓_m(∅) = dfsD N m []`.  Subtraction-free forms are used where the paper
divides or subtracts.  The statements below are frozen; only the proofs are to
be supplied.

Not formalized here (deliberate scope boundaries):

* The geometry behind the grammar.  Facets `e_ℓ`, vertices `v_ℓ,(i,0)` and the
  subdivision of Definition `def:iteration` are not modelled; `Valid` is taken
  as the *definition* of a label, exactly as Section `subsec:duality` states it,
  and the claim that it is the label set of the geometric construction is not
  proved.  Likewise the tier locator of Section `subsec:duality` and the routing
  of Section `subsec:routing` are absent.
* The counting statements.  `|Label_{N,m}| = N(2N-2)^{m-1}`, item (1) of
  Proposition prop:consensus-tree (`|V_{N,m}|/N` consensus nodes), item (4)
  (`N(2N-2)^{n-2}` nodes at level `n`) and item (5) (depth `m`) are *not* proved
  in this file; only items (2) and (3), the two branching numbers, are.  In
  particular `Fintype.card (DNode N m)` is never evaluated to a closed form, and
  `DNode N m` is not identified with the `V N m` of `Hsfnlean.Dense`.
* The successor map is formalized as `List.formPerm` of the depth-first list.
  That is eq:app-successor up to the standard reading of `formPerm` (`x_t ↦
  x_{t+1}`, last back to first); no separate index-based definition of `B` is
  given and the two are not proved equal.
* The ordering claim of eq:app-children is only partly captured.  `childRaw`
  realizes "increasing first component, `b = 0` before `b = 1`", and
  `mem_childRaw_iff` proves the entries are exactly the valid immediate children;
  the paper's phrasing via the cycle `1, σ(1), …, σ^{N-1}(1)` is read as the
  increasing order and is not separately formalized.  Nothing downstream depends
  on the order: nodup, completeness and the cycle hold for any ordering of the
  children.
* No probabilistic or protocol content (Section `subsec:multi-pbft`, the
  partial-fill proxies of Section `subsec:partial-fill`) appears here.
-/

namespace HSFN.DenseUpdate

variable {N m : ℕ}

/-! ### The dense-variant label grammar (Section subsec:duality) -/

/-- A subscript-pair word is a **valid** dense-variant label when the first pair
carries `j = 0` and consecutive first components differ.  The empty word (the
root consensus label `Θ_(0,0)`) is valid. -/
def Valid {N : ℕ} : List (Fin N × Bool) → Prop
  | [] => True
  | p :: l => p.2 = false ∧ (p :: l).IsChain (fun a b => a.1 ≠ b.1)

instance decidableValid {N : ℕ} : ∀ l : List (Fin N × Bool), Decidable (Valid l) :=
  fun l => by cases l <;> (unfold Valid; infer_instance)

/-- The grammar is prefix-closed: a prefix of a valid label is valid. -/
theorem aux_valid_prefix {N : ℕ} {l l' : List (Fin N × Bool)} (h : Valid l) (hp : l' <+: l) :
    Valid l' := by
  match l' with
  | [] => trivial
  | q :: t =>
    obtain ⟨s, hs⟩ := hp
    match l, h with
    | p :: u, ⟨h1, h2⟩ =>
      have hq : q = p := by
        have h3 := hs
        simp at h3
        exact h3.1
      subst hq
      refine ⟨h1, ?_⟩
      have h4 : (q :: t) ++ s = q :: u := hs
      rw [← h4] at h2
      exact h2.left_of_append

/-! ### The ordered child list (eq:app-children) -/

/-- The ordered child list of `ℓ` before the depth cutoff: the `N` labels
`((i,0))` when `ℓ` is the root, and otherwise the `2(N-1)` labels
`ℓ,(r,0)`, `ℓ,(r,1)` for the `r` different from `last ℓ`, in increasing `r` and
with `0` before `1`. -/
def childRaw (N : ℕ) (ℓ : List (Fin N × Bool)) : List (List (Fin N × Bool)) :=
  match ℓ.getLast? with
  | none => (List.finRange N).map fun i => [(i, false)]
  | some p =>
      ((List.finRange N).filter fun r => decide (r ≠ p.1)).flatMap fun r =>
        [ℓ ++ [(r, false)], ℓ ++ [(r, true)]]

/-- `𝓒_m(ℓ)` of eq:app-children: the child list is empty at the last tier
(`|ℓ| = m-1`, stated as `|ℓ| + 1 = m`) and is `childRaw` otherwise. -/
def childList (N m : ℕ) (ℓ : List (Fin N × Bool)) : List (List (Fin N × Bool)) :=
  if ℓ.length + 1 = m then [] else childRaw N ℓ

/-! ### The node set `V_{N,m}` (Definition def:consensus-node) -/

/-- A network node of the depth-`m` dense variant: a consensus label `ℓ`, valid
and of length at most `m-1` (stated as `|ℓ| + 1 ≤ m`), together with the index
`i` of the vertex `v_{ℓ,(i,0)}` inside the consensus node `Θ_ℓ`. -/
def DNode (N m : ℕ) : Type :=
  { x : List (Fin N × Bool) × Fin N // Valid x.1 ∧ x.1.length + 1 ≤ m }

instance : DecidableEq (DNode N m) := inferInstanceAs (DecidableEq (Subtype _))

@[ext] theorem DNode.ext {u v : DNode N m} (h : u.1 = v.1) : u = v := Subtype.ext h

/-- A node is determined by its consensus label, a word of length `< m`, and by
its index inside the cell. -/
def toSigma (x : DNode N m) :
    (Σ t : Fin m, List.Vector (Fin N × Bool) t.1) × Fin N :=
  (⟨⟨x.1.1.length, Nat.lt_of_succ_le x.2.2⟩, ⟨x.1.1, rfl⟩⟩, x.1.2)

theorem toSigma_injective (N m : ℕ) : Function.Injective (toSigma (N := N) (m := m)) := by
  intro x y h
  apply DNode.ext
  have h1 : x.1.1 = y.1.1 := congrArg (fun p => p.1.2.1) h
  have h2 : x.1.2 = y.1.2 := congrArg (fun p => p.2) h
  exact Prod.ext h1 h2

noncomputable instance : Fintype (DNode N m) :=
  Fintype.ofInjective _ (toSigma_injective N m)

/-! ### The depth-first list (eq:app-dfs) -/

/-- `𝓓_m(ℓ)` of eq:app-dfs with `k` tiers of room at and below `ℓ`: first the
`N` members `𝓝(ℓ) = (v_{ℓ,(1,0)}, …, v_{ℓ,(N,0)})` of the cell `Θ_ℓ` in index
order, then the depth-first lists of the ordered children, concatenated in the
order of `childRaw`. -/
def dfsD (N : ℕ) : ℕ → List (Fin N × Bool) → List (List (Fin N × Bool) × Fin N)
  | 0, _ => []
  | k + 1, ℓ =>
      ((List.finRange N).map fun i => (ℓ, i)) ++
        (childRaw N ℓ).flatMap fun c => dfsD N k c

/-- Raw pairs that are nodes of the depth-`m` dense variant, lifted to `DNode`. -/
def toDNode (m : ℕ) (x : List (Fin N × Bool) × Fin N) : Option (DNode N m) :=
  if h : Valid x.1 ∧ x.1.length + 1 ≤ m then some ⟨x, h⟩ else none

/-- The global update list `𝓓_m(∅)` of the depth-`m` dense variant, as nodes. -/
def dfsList (N m : ℕ) : List (DNode N m) :=
  (dfsD N m []).filterMap (toDNode m)

/-- **eq:app-dfs** in the paper's own shape: when the fuel `k+1` is exactly the
room left at and below `ℓ` (`|ℓ| + (k+1) = m`), one unfolding of `dfsD` is
`𝓝(ℓ)` followed by the depth-first lists of the paper's ordered child list
`𝓒_m(ℓ) = childList N m ℓ`.  This is what ties `dfsD`, which cuts off by fuel and
recurses through `childRaw`, to eq:app-children: at the last tier
(`k = 0`) the child list is empty by `childList_of_last_tier`, and above it
`childList N m ℓ = childRaw N ℓ`. -/
theorem dfsD_eq_childList (N m k : ℕ) (ℓ : List (Fin N × Bool))
    (h : ℓ.length + (k + 1) = m) :
    dfsD N (k + 1) ℓ =
      ((List.finRange N).map fun i => (ℓ, i)) ++
        (childList N m ℓ).flatMap fun c => dfsD N k c := by
  rw [dfsD]
  congr 1
  by_cases hc : ℓ.length + 1 = m
  · have hk : k = 0 := by omega
    subst hk
    rw [childList, if_pos hc]
    simp [dfsD]
  · rw [childList, if_neg hc]

/-! ### (1) Uniqueness of the vetoed first component (eq:app-k0) -/

/-- The label grammar in the form used by eq:app-k0: below a non-root valid
label `ℓ`, appending `(r,b)` stays valid exactly when `r ≠ last ℓ`, for either
value of `b`. -/
theorem valid_append_iff (ℓ : List (Fin N × Bool)) (hℓ : Valid ℓ) (hne : ℓ ≠ [])
    (r : Fin N) (b : Bool) :
    Valid (ℓ ++ [(r, b)]) ↔ r ≠ (ℓ.getLast hne).1 := by
  match ℓ, hne, hℓ with
  | p :: t, _, ⟨h1, h2⟩ =>
    have hL : ((p :: t) ++ [(r, b)]) = p :: (t ++ [(r, b)]) := by simp
    constructor
    · rintro ⟨-, hc⟩
      simp only [List.append_eq] at hc
      rw [← hL] at hc
      rw [List.isChain_append] at hc
      have h4 : ((p :: t).getLast?) = some ((p :: t).getLast (by simp)) :=
        List.getLast?_eq_some_getLast _
      have h5 := hc.2.2 _ (by rw [h4]; rfl) (r, b) rfl
      exact fun hcon => h5 (by rw [hcon])
    · intro hr
      refine ⟨h1, ?_⟩
      simp only [List.append_eq]
      rw [← hL]
      refine List.IsChain.append h2 (List.IsChain.singleton _) ?_
      intro x hx y hy
      have h4 : ((p :: t).getLast?) = some ((p :: t).getLast (by simp)) :=
        List.getLast?_eq_some_getLast _
      rw [h4] at hx
      simp at hx hy
      subst hx
      subst hy
      exact fun hcon => hr hcon.symm

/-- **eq:app-k0**: for a non-empty valid label `ℓ`, the vetoed value `k₀`, namely
the one for which `ℓ,(k₀,0)` is not a label, is exactly `last ℓ`. -/
theorem veto_iff_eq_last (ℓ : List (Fin N × Bool)) (hℓ : Valid ℓ) (hne : ℓ ≠ [])
    (k₀ : Fin N) :
    k₀ = (ℓ.getLast hne).1 ↔ ¬ Valid (ℓ ++ [(k₀, false)]) := by
  rw [valid_append_iff ℓ hℓ hne k₀ false, not_not]

/-- **Theorem thm:appendix-update-correct (1)**: below a non-empty valid label
exactly one first component is vetoed. -/
theorem existsUnique_veto (ℓ : List (Fin N × Bool)) (hℓ : Valid ℓ) (hne : ℓ ≠ []) :
    ∃! k₀ : Fin N, ¬ Valid (ℓ ++ [(k₀, false)]) := by
  refine ⟨(ℓ.getLast hne).1, ?_, ?_⟩
  · exact (veto_iff_eq_last ℓ hℓ hne _).mp rfl
  · intro y hy
    exact (veto_iff_eq_last ℓ hℓ hne y).mpr hy

/-! ### (2) The ordered child lists (eq:app-children, prop:consensus-tree 2–3) -/

/-- The entries of `childRaw` are precisely the valid immediate child labels
of `ℓ`. -/
theorem mem_childRaw_iff (ℓ : List (Fin N × Bool)) (hℓ : Valid ℓ)
    (c : List (Fin N × Bool)) :
    c ∈ childRaw N ℓ ↔ (∃ p : Fin N × Bool, c = ℓ ++ [p]) ∧ Valid c := by
  rcases eq_or_ne ℓ [] with rfl | hne
  · simp only [childRaw, List.getLast?_nil, List.nil_append]
    constructor
    · intro h
      obtain ⟨i, -, hi⟩ := List.mem_map.mp h
      subst hi
      exact ⟨⟨(i, false), rfl⟩, ⟨rfl, List.IsChain.singleton _⟩⟩
    · rintro ⟨⟨q, rfl⟩, hv⟩
      have hq : q.2 = false := hv.1
      refine List.mem_map.mpr ⟨q.1, List.mem_finRange _, ?_⟩
      simp [Prod.ext_iff, hq]
  · rw [childRaw]
    rw [List.getLast?_eq_some_getLast hne]
    constructor
    · intro h
      obtain ⟨r, hr, hc⟩ := List.mem_flatMap.mp h
      have hrne : r ≠ (ℓ.getLast hne).1 := by
        have h6 := List.of_mem_filter hr
        simpa using h6
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨⟨(r, false), rfl⟩, (valid_append_iff ℓ hℓ hne r false).mpr hrne⟩
      · exact ⟨⟨(r, true), rfl⟩, (valid_append_iff ℓ hℓ hne r true).mpr hrne⟩
    · rintro ⟨⟨q, rfl⟩, hv⟩
      have hrne : q.1 ≠ (ℓ.getLast hne).1 := (valid_append_iff ℓ hℓ hne q.1 q.2).mp (by
        simpa using hv)
      refine List.mem_flatMap.mpr ⟨q.1, ?_, ?_⟩
      · exact List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using hrne⟩
      · cases hb : q.2 with
        | false => simp [← hb]
        | true => simp [← hb]

/-- Distinct children have distinct labels. -/
theorem childRaw_nodup (N : ℕ) (ℓ : List (Fin N × Bool)) : (childRaw N ℓ).Nodup := by
  rcases eq_or_ne ℓ [] with rfl | hne
  · simp only [childRaw, List.getLast?_nil]
    apply List.Nodup.map _ (List.nodup_finRange N)
    intro i j h
    simpa using h
  · rw [childRaw, List.getLast?_eq_some_getLast hne]
    rw [List.nodup_flatMap]
    constructor
    · intro r _
      simp
    · apply ((List.nodup_finRange N).filter _).pairwise_of_forall_ne
      intro r₁ _ r₂ _ hr
      apply List.disjoint_left.mpr
      intro x hx₁ hx₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx₁ hx₂
      apply hr
      rcases hx₁ with rfl | rfl <;> rcases hx₂ with h | h <;>
        · have h2 := List.append_right_injective ℓ h
          simp_all

/-- Last-tier labels are leaves of the consensus tree (eq:app-children, case
`|ℓ| = m-1`). -/
theorem childList_of_last_tier (N m : ℕ) (ℓ : List (Fin N × Bool))
    (h : ℓ.length + 1 = m) : childList N m ℓ = [] := by
  rw [childList, if_pos h]

/-- **Proposition prop:consensus-tree (2)**: the root has `N` children. -/
theorem length_childList_root (N m : ℕ) (hm : 2 ≤ m) :
    (childList N m ([] : List (Fin N × Bool))).length = N := by
  have h : ¬ (([] : List (Fin N × Bool)).length + 1 = m) := by simp; omega
  rw [childList, if_neg h, childRaw]
  simp

/-- **Proposition prop:consensus-tree (3)**: every non-root, non-leaf consensus
node has `2(N-1)` children, stated subtraction-free as `len + 2 = 2N`. -/
theorem length_childList_of_ne_nil (N m : ℕ) (ℓ : List (Fin N × Bool)) (hne : ℓ ≠ [])
    (hlt : ℓ.length + 1 < m) :
    (childList N m ℓ).length + 2 = 2 * N := by
  have h : ¬ (ℓ.length + 1 = m) := by omega
  have hfil : ((List.finRange N).filter (fun r => decide (r ≠ (ℓ.getLast hne).1))).length
      + 1 = N := by
    have hnd : ((List.finRange N).filter (fun r => decide (r ≠ (ℓ.getLast hne).1))).Nodup :=
      (List.nodup_finRange N).filter _
    rw [← List.toFinset_card_of_nodup hnd, List.toFinset_filter, List.toFinset_finRange]
    have hcard : ({x ∈ (Finset.univ : Finset (Fin N)) |
        decide (x ≠ (ℓ.getLast hne).1) = true}).card + 1 = N := by
      simp only [decide_eq_true_eq]
      rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
      have h7 := (ℓ.getLast hne).1.pos
      omega
    exact hcard
  rw [childList, if_neg h, childRaw, List.getLast?_eq_some_getLast hne]
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_nil, List.map_const', List.sum_replicate,
    smul_eq_mul]
  omega

/-! ### (2) The depth-first list is repetition-free and complete -/

/-- Every entry of the ordered child list is `ℓ` extended by one pair. -/
theorem aux_childRaw_append (N : ℕ) (ℓ c : List (Fin N × Bool)) (hc : c ∈ childRaw N ℓ) :
    ∃ p : Fin N × Bool, c = ℓ ++ [p] := by
  rcases eq_or_ne ℓ [] with rfl | hne
  · simp only [childRaw, List.getLast?_nil] at hc
    obtain ⟨i, -, hi⟩ := List.mem_map.mp hc
    exact ⟨(i, false), by simp [← hi]⟩
  · rw [childRaw, List.getLast?_eq_some_getLast hne] at hc
    obtain ⟨r, -, hr⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨(r, false), rfl⟩
    · exact ⟨(r, true), rfl⟩

/-- The part of `mem_dfsD_iff` that needs no validity hypothesis on `ℓ`: every
entry of `𝓓(ℓ)` sits below `ℓ` and within the remaining room. -/
theorem aux_mem_dfsD_prefix (N k : ℕ) (ℓ : List (Fin N × Bool))
    (x : List (Fin N × Bool) × Fin N) (hx : x ∈ dfsD N k ℓ) :
    ℓ <+: x.1 ∧ x.1.length < ℓ.length + k := by
  induction k generalizing ℓ with
  | zero => simp [dfsD] at hx
  | succ k ih =>
      rw [dfsD, List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨i, -, hi⟩ := List.mem_map.mp hx
        subst hi
        exact ⟨List.prefix_refl _, by dsimp only; omega⟩
      · obtain ⟨c, hc, hx⟩ := List.mem_flatMap.mp hx
        obtain ⟨p, rfl⟩ := aux_childRaw_append N ℓ c hc
        have h := ih (ℓ ++ [p]) hx
        refine ⟨(List.prefix_append ℓ [p]).trans h.1, ?_⟩
        have h8 := h.2
        simp only [List.length_append, List.length_cons, List.length_nil] at h8
        omega

/-- Membership in `𝓓(ℓ)` with `k` tiers of room: exactly the nodes whose
consensus label is a valid extension of `ℓ` by fewer than `k` further pairs. -/
theorem mem_dfsD_iff (N k : ℕ) (ℓ : List (Fin N × Bool)) (hℓ : Valid ℓ)
    (x : List (Fin N × Bool) × Fin N) :
    x ∈ dfsD N k ℓ ↔ ℓ <+: x.1 ∧ Valid x.1 ∧ x.1.length < ℓ.length + k := by
  induction k generalizing ℓ with
  | zero =>
      simp only [dfsD, List.not_mem_nil, false_iff, not_and]
      intro hpre _
      have h9 := hpre.length_le
      omega
  | succ k ih =>
      rw [dfsD, List.mem_append]
      constructor
      · rintro (hx | hx)
        · obtain ⟨i, -, hi⟩ := List.mem_map.mp hx
          subst hi
          exact ⟨List.prefix_refl _, hℓ, by dsimp only; omega⟩
        · obtain ⟨c, hc, hx⟩ := List.mem_flatMap.mp hx
          have hcv : Valid c := ((mem_childRaw_iff ℓ hℓ c).mp hc).2
          obtain ⟨p, rfl⟩ := aux_childRaw_append N ℓ c hc
          have h := (ih (ℓ ++ [p]) hcv).mp hx
          refine ⟨(List.prefix_append ℓ [p]).trans h.1, h.2.1, ?_⟩
          have h8 := h.2.2
          simp only [List.length_append, List.length_cons, List.length_nil] at h8
          omega
      · rintro ⟨hpre, hv, hlen⟩
        rcases Nat.eq_or_lt_of_le hpre.length_le with heq | hlt
        · left
          have hxe : ℓ = x.1 := hpre.eq_of_length heq
          refine List.mem_map.mpr ⟨x.2, List.mem_finRange _, ?_⟩
          rw [hxe]
        · right
          have hpre' : ℓ ++ [x.1.get ⟨ℓ.length, hlt⟩] <+: x.1 :=
            List.concat_get_prefix hpre hlt
          set p := x.1.get ⟨ℓ.length, hlt⟩ with hp
          have hcv : Valid (ℓ ++ [p]) := aux_valid_prefix hv hpre'
          have hcmem : (ℓ ++ [p]) ∈ childRaw N ℓ :=
            (mem_childRaw_iff ℓ hℓ _).mpr ⟨⟨p, rfl⟩, hcv⟩
          refine List.mem_flatMap.mpr ⟨ℓ ++ [p], hcmem, ?_⟩
          refine (ih (ℓ ++ [p]) hcv).mpr ⟨hpre', hv, ?_⟩
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega

/-- `𝓓(ℓ)` is repetition-free. -/
theorem dfsD_nodup (N k : ℕ) (ℓ : List (Fin N × Bool)) : (dfsD N k ℓ).Nodup := by
  induction k generalizing ℓ with
  | zero => simp [dfsD]
  | succ k ih =>
      rw [dfsD, List.nodup_append']
      refine ⟨?_, ?_, ?_⟩
      · apply List.Nodup.map _ (List.nodup_finRange N)
        intro i j h
        simpa using h
      · rw [List.nodup_flatMap]
        refine ⟨fun c _ => ih c, ?_⟩
        apply (childRaw_nodup N ℓ).pairwise_of_forall_ne
        intro c₁ hc₁ c₂ hc₂ hne
        apply List.disjoint_left.mpr
        intro x hx₁ hx₂
        obtain ⟨p₁, rfl⟩ := aux_childRaw_append N ℓ c₁ hc₁
        obtain ⟨p₂, rfl⟩ := aux_childRaw_append N ℓ c₂ hc₂
        have h₁ := aux_mem_dfsD_prefix N k _ x hx₁
        have h₂ := aux_mem_dfsD_prefix N k _ x hx₂
        apply hne
        have e₁ : ℓ ++ [p₁] = x.1.take (ℓ.length + 1) := by
          have h10 := List.prefix_iff_eq_take.mp h₁.1
          simpa using h10
        have e₂ : ℓ ++ [p₂] = x.1.take (ℓ.length + 1) := by
          have h11 := List.prefix_iff_eq_take.mp h₂.1
          simpa using h11
        rw [e₁, e₂]
      · rw [List.disjoint_left]
        intro x hxmap hxflat
        obtain ⟨i, -, hi⟩ := List.mem_map.mp hxmap
        obtain ⟨c, hc, hx⟩ := List.mem_flatMap.mp hxflat
        obtain ⟨p, rfl⟩ := aux_childRaw_append N ℓ c hc
        have h := aux_mem_dfsD_prefix N k _ x hx
        have hl := h.1.length_le
        rw [← hi] at hl
        simp only [List.length_append, List.length_cons, List.length_nil] at hl
        omega

/-- Every entry of `𝓓_m(∅)` is a node of `V_{N,m}`, so `dfsList` loses nothing. -/
theorem toDNode_dfsD_isSome (N m : ℕ) (x : List (Fin N × Bool) × Fin N)
    (hx : x ∈ dfsD N m []) : (toDNode (N := N) m x).isSome := by
  have hx' := (mem_dfsD_iff (N := N) (k := m) (ℓ := []) trivial x).mp hx
  have hlen : x.1.length + 1 ≤ m := by
    have h12 := hx'.2.2
    simp only [List.length_nil, Nat.zero_add] at h12
    omega
  simp [toDNode, hx'.2.1, hlen]

/-- **Theorem thm:appendix-update-correct (2)**, completeness: `𝓓_m(∅)` lists
every node of `V_{N,m}`. -/
theorem mem_dfsList (N m : ℕ) (v : DNode N m) : v ∈ dfsList N m := by
  rw [dfsList]
  refine List.mem_filterMap.mpr ⟨v.1, ?_, ?_⟩
  · refine (mem_dfsD_iff (N := N) (k := m) (ℓ := []) trivial v.1).mpr ?_
    refine ⟨List.nil_prefix, v.2.1, ?_⟩
    have h13 := v.2.2
    simp only [List.length_nil, Nat.zero_add]
    omega
  · simp [toDNode, v.2.1, v.2.2]

/-- **Theorem thm:appendix-update-correct (2)**, no repetition: `𝓓_m(∅)` lists
every node of `V_{N,m}` at most once. -/
theorem dfsList_nodup (N m : ℕ) : (dfsList N m).Nodup := by
  refine List.Nodup.filterMap ?_ (dfsD_nodup N m [])
  intro x₁ x₂ v hx₁ hx₂
  rcases (by simpa [toDNode] using hx₁) with ⟨h₁, heq₁⟩
  rcases (by simpa [toDNode] using hx₂) with ⟨h₂, heq₂⟩
  have hEq : (⟨x₁, h₁⟩ : DNode N m) = ⟨x₂, h₂⟩ := heq₁.trans heq₂.symm
  exact congrArg Subtype.val hEq

/-- The update list has exactly `|V_{N,m}|` entries. -/
theorem dfsList_length (N m : ℕ) : (dfsList N m).length = Fintype.card (DNode N m) := by
  rw [← List.toFinset_card_of_nodup (dfsList_nodup N m)]
  have hto : (dfsList N m).toFinset = Finset.univ := by
    apply Finset.eq_univ_iff_forall.2
    intro v
    simpa [List.mem_toFinset] using mem_dfsList (N := N) (m := m) v
  simp [hto]

/-- The root cell alone contributes `N` nodes. -/
theorem le_card_DNode (N m : ℕ) (hm : 1 ≤ m) : N ≤ Fintype.card (DNode N m) := by
  have hf : Function.Injective
      (show Fin N → DNode N m from
        fun i => ⟨(([] : List (Fin N × Bool)), i), ⟨trivial, by simpa using hm⟩⟩) := by
    intro i j h
    have h2 := congrArg (fun v : DNode N m => v.1.2) h
    simpa using h2
  have h3 := Fintype.card_le_of_injective _ hf
  simpa using h3

/-! ### (3) The successor map is one cycle (eq:app-successor) -/

/-- **Theorem thm:appendix-update-correct (3)**: the wrap-around successor map
`B` of eq:app-successor, that is the `formPerm` of the depth-first list
`𝓓_m(∅)`, is a single cycle on `V_{N,m}` (`N ≥ 2`, `m ≥ 1`, so that there are
at least two nodes). -/
theorem dfsList_formPerm_isCycle (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) :
    (dfsList N m).formPerm.IsCycle := by
  have hlen : 2 ≤ (dfsList N m).length := by
    rw [dfsList_length]
    exact hN.trans (le_card_DNode N m hm)
  exact List.isCycle_formPerm (dfsList_nodup N m) hlen

/-- **Theorem thm:appendix-update-correct (3)**, no dead end and no smaller
cycle: the support of `B` is the whole node set `V_{N,m}`. -/
theorem dfsList_formPerm_support (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) :
    (dfsList N m).formPerm.support = Finset.univ := by
  have hlen : 2 ≤ (dfsList N m).length := by
    rw [dfsList_length]
    exact hN.trans (le_card_DNode N m hm)
  have hne : ∀ x : DNode N m, (dfsList N m) ≠ [x] := by
    intro x hx
    have h14 : (dfsList N m).length = 1 := by simp [hx]
    omega
  rw [List.support_formPerm_of_nodup (dfsList N m) (dfsList_nodup N m) hne]
  have hto : (dfsList N m).toFinset = Finset.univ := by
    apply Finset.eq_univ_iff_forall.2
    intro v
    simpa [List.mem_toFinset] using mem_dfsList (N := N) (m := m) v
  simp [hto]



end HSFN.DenseUpdate

