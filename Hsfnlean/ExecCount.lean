/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Basic
import Hsfnlean.Distance

/-!
# Executed message count of one hierarchical PBFT round (Proposition prop:exec-count)

Paper: "The Hyper-Simplex Fractal Network as Space, Protocol and Dynamical System" (R260409).

We work at depth `m + 1` with cell size `N = n + 1`, so that no truncated subtraction
appears. Nodes are the addresses `Addr N (m+1)`. Cells are `Option (Addr N m)`: `none` is
the seed cell and `some a` is the cell spawned by the anchor `a`, whose members are the
words `a ++ [d]`. One fault-free round sends five kinds of point-to-point messages:

* `pp` — the primary (digit `0`) of a cell sends a pre-prepare to every other member;
* `pr` — every backup (digit `≠ 0`) sends a prepare to every other member;
* `cm` — every member sends a commit to every other member;
* `rp` — in every non-seed cell `some a`, each of the `s` report senders
  (digits `0, …, s-1`) sends the report to every member of the parent cell;
* `dc` — for every non-seed cell `some a`, each of the `s` dissemination senders of the
  parent cell sends the decision to every member of `some a`.

`Msg n m s` is the disjoint union of these five index sets. The results are
(i) `endpoints_injective`: a message is determined by its kind, sender and receiver, so the
count is a count of distinct point-to-point messages; (ii) `card_msg`: the exact count
`2(N-1)V + 2s(V-N)` in subtraction-free form; (iii) `hop_eq_dist`: the hop count charged to
each message is the exact graph distance of its endpoints in `G_II`, and `sum_hop` gives the
link total `2(N-1)V + 2s(2N-1)(V/N - 1)`, again subtraction-free.
The statements are frozen; only the proofs are to be supplied.
-/

namespace HSFN
namespace ExecCount

open Finset

variable {n m s : ℕ}

/-- The cells of the depth-`(m+1)` HSFN: `none` is the seed, `some a` is anchored at `a`. -/
abbrev Cell (n m : ℕ) := Option (Addr (n + 1) m)

/-- The member with digit `d` of a cell, as a node of depth `m + 1`. -/
def member (c : Cell n m) (d : Fin (n + 1)) : Addr (n + 1) (m + 1) :=
  match c with
  | none => ⟨[d], by simp⟩
  | some a => ⟨a.1 ++ [d], by
      refine ⟨by simp, ?_⟩
      have := a.2.2
      simp [List.length_append]
      omega⟩

/-- The last digit of an anchor, i.e. the digit of the anchor inside its own cell. -/
def lastDigit (a : Addr (n + 1) m) : Fin (n + 1) := a.1.getLast a.2.1

/-- The parent cell of the cell anchored at `a`: the anchor of `a`'s own cell. -/
def parentCell (a : Addr (n + 1) m) : Cell n m :=
  if h : a.1.dropLast = [] then none
  else some ⟨a.1.dropLast, h, by
    have := a.2.2
    simp [List.length_dropLast]
    omega⟩

/-- The five message kinds. -/
inductive Kind | pp | pr | cm | rp | dc
  deriving DecidableEq

/-- One fault-free round, indexed by its five disjoint message kinds. -/
abbrev Msg (n m s : ℕ) :=
  (Cell n m × { j : Fin (n + 1) // j ≠ 0 }) ⊕
  (Cell n m × { ij : Fin (n + 1) × Fin (n + 1) // ij.1 ≠ 0 ∧ ij.2 ≠ ij.1 }) ⊕
  (Cell n m × { ij : Fin (n + 1) × Fin (n + 1) // ij.2 ≠ ij.1 }) ⊕
  (Addr (n + 1) m × Fin s × Fin (n + 1)) ⊕
  (Addr (n + 1) m × Fin s × Fin (n + 1))

/-- Kind, sender and receiver of a message. The `k`-th of the `s ≤ N` senders of a cell is
its member with digit `k`. -/
def endpoints (hs : s ≤ n + 1) :
    Msg n m s → Kind × Addr (n + 1) (m + 1) × Addr (n + 1) (m + 1)
  | .inl (c, j) => (.pp, member c 0, member c j.1)
  | .inr (.inl (c, ij)) => (.pr, member c ij.1.1, member c ij.1.2)
  | .inr (.inr (.inl (c, ij))) => (.cm, member c ij.1.1, member c ij.1.2)
  | .inr (.inr (.inr (.inl (a, k, j)))) =>
      (.rp, member (some a) (Fin.castLE hs k), member (parentCell a) j)
  | .inr (.inr (.inr (.inr (a, k, i)))) =>
      (.dc, member (parentCell a) (Fin.castLE hs k), member (some a) i)

/-- The anchor word of a cell (empty for the seed cell). -/
def cellWord : Cell n m → List (Fin (n + 1))
  | none => []
  | some a => a.1

theorem member_val (c : Cell n m) (d : Fin (n + 1)) :
    (member c d).1 = cellWord c ++ [d] := by
  cases c <;> rfl

theorem member_parentCell_val (a : Addr (n + 1) m) (d : Fin (n + 1)) :
    (member (parentCell a) d).1 = a.1.dropLast ++ [d] := by
  unfold parentCell
  split_ifs with h
  · rw [h]; rfl
  · rfl

theorem val_eq_dropLast_append_lastDigit (a : Addr (n + 1) m) :
    a.1 = a.1.dropLast ++ [lastDigit a] :=
  (List.dropLast_append_getLast a.2.1).symm

theorem member_inj {c c' : Cell n m} {d d' : Fin (n + 1)}
    (h : member c d = member c' d') : c = c' ∧ d = d' := by
  have h1 : cellWord c ++ [d] = cellWord c' ++ [d'] := by
    rw [← member_val, ← member_val, h]
  obtain ⟨h2, h3⟩ := List.append_inj' h1 rfl
  refine ⟨?_, by simpa using h3⟩
  cases c with
  | none =>
    cases c' with
    | none => rfl
    | some a' => exact (a'.2.1 h2.symm).elim
  | some a =>
    cases c' with
    | none => exact (a.2.1 h2).elim
    | some a' => exact congrArg some (Subtype.ext h2)

/-- (i) Every counted message is a distinct point-to-point message. -/
theorem endpoints_injective (hs : s ≤ n + 1) :
    Function.Injective (endpoints (m := m) hs) := by
  rintro (⟨c, j⟩ | ⟨c, ij⟩ | ⟨c, ij⟩ | ⟨a, k, j⟩ | ⟨a, k, i⟩)
    (⟨c', j'⟩ | ⟨c', ij'⟩ | ⟨c', ij'⟩ | ⟨a', k', j'⟩ | ⟨a', k', i'⟩) h <;>
    simp only [endpoints, Prod.mk.injEq, reduceCtorEq, false_and, true_and] at h
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨rfl, hj⟩ := member_inj h2
    obtain rfl : j = j' := Subtype.ext hj
    rfl
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨rfl, hi⟩ := member_inj h1
    obtain ⟨-, hj⟩ := member_inj h2
    obtain rfl : ij = ij' := Subtype.ext (Prod.ext hi hj)
    rfl
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨rfl, hi⟩ := member_inj h1
    obtain ⟨-, hj⟩ := member_inj h2
    obtain rfl : ij = ij' := Subtype.ext (Prod.ext hi hj)
    rfl
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨ha, hk⟩ := member_inj h1
    obtain rfl : a = a' := Option.some.inj ha
    obtain rfl : k = k' := Fin.castLE_injective hs hk
    obtain ⟨-, hj⟩ := member_inj h2
    subst hj
    rfl
  · obtain ⟨h1, h2⟩ := h
    obtain ⟨ha, hi⟩ := member_inj h2
    obtain rfl : a = a' := Option.some.inj ha
    subst hi
    obtain ⟨-, hk⟩ := member_inj h1
    obtain rfl : k = k' := Fin.castLE_injective hs hk
    rfl

/-- The node count is `N` times the cell count: `|V_{m+1}| = N (|Addr_m| + 1)`. -/
theorem card_node_eq (n m : ℕ) :
    Fintype.card (Addr (n + 1) (m + 1)) = (n + 1) * (Fintype.card (Addr (n + 1) m) + 1) := by
  rw [Addr.card_eq_sum, Addr.card_eq_sum, Finset.sum_range_succ', mul_add, Finset.mul_sum,
    mul_one, zero_add, pow_one]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

theorem card_ne (i : Fin (n + 1)) : Fintype.card {j : Fin (n + 1) // j ≠ i} = n := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  omega

/-- Reindexing of the prepare pairs. -/
def prEquiv : {ij : Fin (n + 1) × Fin (n + 1) // ij.1 ≠ 0 ∧ ij.2 ≠ ij.1} ≃
    Σ i : {i : Fin (n + 1) // i ≠ 0}, {j : Fin (n + 1) // j ≠ i.1} where
  toFun x := ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
  invFun y := ⟨(y.1.1, y.2.1), y.1.2, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindexing of the commit pairs. -/
def cmEquiv : {ij : Fin (n + 1) × Fin (n + 1) // ij.2 ≠ ij.1} ≃
    Σ i : Fin (n + 1), {j : Fin (n + 1) // j ≠ i} where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun y := ⟨(y.1, y.2.1), y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_pr :
    Fintype.card {ij : Fin (n + 1) × Fin (n + 1) // ij.1 ≠ 0 ∧ ij.2 ≠ ij.1} = n * n := by
  rw [Fintype.card_congr prEquiv, Fintype.card_sigma]
  simp only [card_ne, Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem card_cm :
    Fintype.card {ij : Fin (n + 1) × Fin (n + 1) // ij.2 ≠ ij.1} = (n + 1) * n := by
  rw [Fintype.card_congr cmEquiv, Fintype.card_sigma]
  simp only [card_ne, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]

/-- (ii) The exact count, subtraction-free form of `C_exec = 2(N-1)V + 2s(V-N)`:
with `V = |Addr N (m+1)|`, `|Msg| + 2sN = 2nV + 2sV`. -/
theorem card_msg (n m s : ℕ) :
    Fintype.card (Msg n m s) + 2 * s * (n + 1) =
      2 * n * Fintype.card (Addr (n + 1) (m + 1)) +
        2 * s * Fintype.card (Addr (n + 1) (m + 1)) := by
  simp only [Msg, Fintype.card_sum, Fintype.card_prod, Fintype.card_option, Fintype.card_fin,
    card_ne, card_pr, card_cm]
  rw [card_node_eq]
  ring

/-- The number of physical links a message crosses under anchor routing: a message inside a
cell uses its sibling link; a message between a cell and its parent crosses the anchor, one
link when the far end is the anchor itself and two otherwise. -/
def hop (hs : s ≤ n + 1) : Msg n m s → ℕ
  | .inl _ => 1
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr (.inl (a, _, j)))) => if j = lastDigit a then 1 else 2
  | .inr (.inr (.inr (.inr (a, k, _)))) => if Fin.castLE hs k = lastDigit a then 1 else 2

theorem lcp_append_same {N : ℕ} (l x y : List (Fin N)) :
    lcp (l ++ x) (l ++ y) = l.length + lcp x y := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.cons_append, lcp, ↓reduceIte, ih, List.length_cons]
    omega

/-- Two distinct members of one cell are at distance one. -/
theorem dval_sib {N k : ℕ} {u v : Addr N k} {c : List (Fin N)} {i j : Fin N} (hij : i ≠ j)
    (hu : u.1 = c ++ [i]) (hv : v.1 = c ++ [j]) : dval u v = 1 := by
  have hl : lcp u.1 v.1 = c.length := by
    rw [hu, hv, lcp_append_same]
    simp [lcp, hij]
  have hnp : ¬ PrefixComp u v := by
    rw [prefixComp_iff_lcp, hl]
    simp only [Addr.tier, hu, hv, List.length_append, List.length_singleton]
    omega
  unfold dval
  rw [if_neg hnp, hl]
  simp only [Addr.tier, hu, hv, List.length_append, List.length_singleton]
  omega

/-- A child and its anchor are at distance one. -/
theorem dval_child {N k : ℕ} {u v : Addr N k} {d : Fin N}
    (hu : u.1 = v.1 ++ [d]) : dval u v = 1 := by
  have hp : PrefixComp u v := Or.inr (by rw [hu]; exact List.prefix_append _ _)
  unfold dval
  rw [if_pos hp]
  simp only [Addr.tier, hu, List.length_append, List.length_singleton]
  omega

/-- A child of an anchor and a sibling of that anchor are at distance two. -/
theorem dval_nephew {N k : ℕ} {u v : Addr N k} {p : List (Fin N)} {d e j : Fin N}
    (hdj : d ≠ j) (hu : u.1 = p ++ [d, e]) (hv : v.1 = p ++ [j]) : dval u v = 2 := by
  have hl : lcp u.1 v.1 = p.length := by
    rw [hu, hv, lcp_append_same]
    simp [lcp, hdj]
  have hnp : ¬ PrefixComp u v := by
    rw [prefixComp_iff_lcp, hl]
    simp only [Addr.tier, hu, hv, List.length_append, List.length_cons,
      List.length_nil]
    omega
  unfold dval
  rw [if_neg hnp, hl]
  simp only [Addr.tier, hu, hv, List.length_append, List.length_cons,
    List.length_nil]
  omega

/-- Report/decision distance: child `a ++ [e]` of anchor `a` versus member `j` of the
parent cell of `a`. -/
theorem dval_child_parentCell (a : Addr (n + 1) m) (e j : Fin (n + 1)) :
    dval (member (some a) e) (member (parentCell a) j) =
      if j = lastDigit a then 1 else 2 := by
  split_ifs with hj
  · apply dval_child (d := e)
    rw [member_val, member_parentCell_val, hj, ← val_eq_dropLast_append_lastDigit]
    rfl
  · apply dval_nephew (p := a.1.dropLast) (d := lastDigit a) (e := e) (j := j) (Ne.symm hj)
    · rw [member_val]
      show a.1 ++ [e] = _
      conv_lhs => rw [val_eq_dropLast_append_lastDigit a]
      simp
    · exact member_parentCell_val a j

/-- (iii) Anchor routing is shortest-path routing: the hop charge of every message equals the
graph distance of its endpoints in `G_II(N, m+1)`. -/
theorem hop_eq_dist (hs : s ≤ n + 1) (x : Msg n m s) :
    hop hs x = (graph (n + 1) (m + 1)).dist (endpoints hs x).2.1 (endpoints hs x).2.2 := by
  rw [dist_eq_dval]
  rcases x with ⟨c, j⟩ | ⟨c, ij⟩ | ⟨c, ij⟩ | ⟨a, k, j⟩ | ⟨a, k, i⟩
  · simp only [hop, endpoints]
    exact (dval_sib (Ne.symm j.2) (member_val _ _) (member_val _ _)).symm
  · simp only [hop, endpoints]
    exact (dval_sib (Ne.symm ij.2.2) (member_val _ _) (member_val _ _)).symm
  · simp only [hop, endpoints]
    exact (dval_sib (Ne.symm ij.2) (member_val _ _) (member_val _ _)).symm
  · simp only [hop, endpoints]
    rw [dval_child_parentCell]
  · simp only [hop, endpoints]
    rw [dval_comm, dval_child_parentCell]

/-- Anchors ending in a fixed digit are one `N`-th of all anchors. -/
theorem card_lastDigit (n m : ℕ) (d : Fin (n + 1)) :
    (n + 1) * (univ.filter fun a : Addr (n + 1) m => lastDigit a = d).card =
      Fintype.card (Addr (n + 1) m) := by
  cases m with
  | zero =>
    have h0 : Fintype.card (Addr (n + 1) 0) = 0 := by
      rw [Addr.card_eq_sum]; simp
    have h1 : (univ.filter fun a : Addr (n + 1) 0 => lastDigit a = d).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← h0, ← Finset.card_univ]
      exact Finset.card_filter_le _ _
    rw [h1, h0, mul_zero]
  | succ k =>
    have hmem : ∀ c : Cell n k, lastDigit (member c d) = d := by
      intro c
      cases c <;> simp [lastDigit, member]
    let f : Cell n k → {a : Addr (n + 1) (k + 1) // lastDigit a = d} :=
      fun c => ⟨member c d, hmem c⟩
    have hf : Function.Bijective f := by
      constructor
      · intro c c' h
        exact (member_inj (congrArg Subtype.val h)).1
      · rintro ⟨a, ha⟩
        by_cases h : a.1.dropLast = []
        · refine ⟨none, Subtype.ext (Addr.ext ?_)⟩
          show [d] = a.1
          rw [val_eq_dropLast_append_lastDigit a, h, ha]
          rfl
        · refine ⟨some ⟨a.1.dropLast, h, ?_⟩, Subtype.ext (Addr.ext ?_)⟩
          · have := a.2.2
            simp only [List.length_dropLast]
            omega
          · show a.1.dropLast ++ [d] = a.1
            conv_rhs => rw [val_eq_dropLast_append_lastDigit a, ha]
    have hc : (univ.filter fun a : Addr (n + 1) (k + 1) => lastDigit a = d).card =
        Fintype.card (Addr (n + 1) k) + 1 := by
      rw [← Fintype.card_subtype, ← Fintype.card_congr (Equiv.ofBijective f hf),
        Fintype.card_option]
    rw [hc, card_node_eq]

theorem sum_ite_digit (d : Fin (n + 1)) :
    ∑ j : Fin (n + 1), (if j = d then 1 else 2) = 2 * n + 1 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ d), if_pos rfl,
    Finset.sum_congr rfl (g := fun _ => 2) (fun j hj => if_neg (Finset.ne_of_mem_erase hj)),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ d), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  omega

theorem dc_inner (e : Fin (n + 1)) :
    ∑ a : Addr (n + 1) m, (n + 1) * (if e = lastDigit a then 1 else 2) =
      (2 * n + 1) * Fintype.card (Addr (n + 1) m) := by
  rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul,
    smul_eq_mul]
  have h1 := card_lastDigit n m e
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Addr (n + 1) m)))
    (fun a => e = lastDigit a)
  have h3 : (univ.filter fun a : Addr (n + 1) m => e = lastDigit a) =
      univ.filter fun a => lastDigit a = e := by
    ext a; simp [eq_comm]
  rw [h3] at h2 ⊢
  rw [Finset.card_univ] at h2
  set F := (univ.filter fun a : Addr (n + 1) m => lastDigit a = e).card
  set G := (univ.filter fun a : Addr (n + 1) m => ¬ e = lastDigit a).card
  have h4 : (n + 1) * (F + G) = (n + 1) * Fintype.card (Addr (n + 1) m) := by rw [h2]
  nlinarith

theorem dc_inner' (e : Fin (n + 1)) :
    ∑ a : Addr (n + 1) m, ∑ _i : Fin (n + 1), (if e = lastDigit a then 1 else 2) =
      (2 * n + 1) * Fintype.card (Addr (n + 1) m) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact dc_inner e

/-- (iii') The link total, subtraction-free form of
`2(N-1)V + 2s(2N-1)(V/N - 1)`: with `V/N - 1 = |Addr N m|`,
`∑ hop = 2nV + 2s(2n+1)|Addr N m|`. -/
theorem sum_hop (hs : s ≤ n + 1) :
    ∑ x : Msg n m s, hop hs x =
      2 * n * Fintype.card (Addr (n + 1) (m + 1)) +
        2 * s * (2 * n + 1) * Fintype.card (Addr (n + 1) m) := by
  have e1 : ∑ x : Cell n m × {j : Fin (n + 1) // j ≠ 0},
      hop hs (Sum.inl x : Msg n m s) = (Fintype.card (Addr (n + 1) m) + 1) * n := by
    simp only [hop, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_prod, Fintype.card_option, card_ne]
  have e2 : ∑ x : Cell n m × {ij : Fin (n + 1) × Fin (n + 1) // ij.1 ≠ 0 ∧ ij.2 ≠ ij.1},
      hop hs (Sum.inr (Sum.inl x) : Msg n m s) =
        (Fintype.card (Addr (n + 1) m) + 1) * (n * n) := by
    simp only [hop, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_prod, Fintype.card_option, card_pr]
  have e3 : ∑ x : Cell n m × {ij : Fin (n + 1) × Fin (n + 1) // ij.2 ≠ ij.1},
      hop hs (Sum.inr (Sum.inr (Sum.inl x)) : Msg n m s) =
        (Fintype.card (Addr (n + 1) m) + 1) * ((n + 1) * n) := by
    simp only [hop, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_prod, Fintype.card_option, card_cm]
  have e4 : ∑ x : Addr (n + 1) m × Fin s × Fin (n + 1),
      hop hs (Sum.inr (Sum.inr (Sum.inr (Sum.inl x))) : Msg n m s) =
        s * (2 * n + 1) * Fintype.card (Addr (n + 1) m) := by
    simp only [Fintype.sum_prod_type, hop, sum_ite_digit, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    ring
  have e5 : ∑ x : Addr (n + 1) m × Fin s × Fin (n + 1),
      hop hs (Sum.inr (Sum.inr (Sum.inr (Sum.inr x))) : Msg n m s) =
        s * (2 * n + 1) * Fintype.card (Addr (n + 1) m) := by
    simp only [Fintype.sum_prod_type, hop]
    rw [Finset.sum_comm]
    simp only [dc_inner', Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type,
    e1, e2, e3, e4, e5, card_node_eq]
  ring

end ExecCount
end HSFN
