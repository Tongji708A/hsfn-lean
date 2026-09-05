/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Mathlib

/-!
# Dense-variant counts and the message proxy (Theorem thm:node-count,
Proposition prop:consensus-tree(4), Proposition thm:complexity)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
The dense variant replaces every facet by `2(N-1)` facets and adds `N` vertices per
facet, so `|E_{N,m}| = N (2N-2)^{m-1}` and `|V_{N,m}| = N + N ∑_{k<m-1} |E_{N,k+1}|`,
which sums to `N + N^2((2N-2)^{m-1} - 1)/(2N-3)`. These are natural-number identities,
stated subtraction-free. The full-population message proxy `(N+1)V` follows from
`V/N` cells at `N^2` messages each plus one leader message per node.
The statements below are frozen; only the proofs are to be supplied.
-/

namespace HSFN.Dense

/-- Facet count of the dense variant at depth `m ≥ 1`: `N (2N-2)^{m-1}`. -/
def E (N m : ℕ) : ℕ := N * (2 * N - 2) ^ (m - 1)

/-- Vertex count of the dense variant, by the recurrence `V_1 = N`,
`V_{m+1} = V_m + N · E_m`. -/
def V (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => N
  | m + 2 => V N (m + 1) + N * E N (m + 1)

/-- The facet recurrence `E_{m+1} = (2N-2) E_m` (Theorem thm:node-count). -/
theorem E_succ (N m : ℕ) (hm : 1 ≤ m) : E N (m + 1) = (2 * N - 2) * E N m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp only [E, Nat.add_sub_cancel_left, Nat.add_sub_cancel]
  rw [Nat.add_comm 1 k]
  rw [pow_succ]
  ring

/-- The vertex count as a geometric sum: `V_m = N + N ∑_{k<m-1} E_{k+1}`. -/
theorem V_eq_sum (N m : ℕ) (hm : 1 ≤ m) :
    V N m = N + N * ∑ k ∈ Finset.range (m - 1), E N (k + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => simp [V]
  | succ k ih =>
      have ih' : V N (k + 1) = N + N * ∑ i ∈ Finset.range k, E N (i + 1) := by
        simpa [Nat.add_comm] using ih
      rw [show 1 + (k + 1) - 1 = k + 1 by omega]
      rw [Nat.add_comm 1 (k + 1)]
      change V N (k + 2) = N + N * ∑ i ∈ Finset.range (k + 1), E N (i + 1)
      rw [V, ih', Finset.sum_range_succ]
      ring

/-- **Closed form** (Theorem thm:node-count, eq:closed-form), subtraction-free:
`(2N-3)(V_m - N) = N^2 ((2N-2)^{m-1} - 1)`, stated as
`(2N-3) V_m + N^2 = (2N-3) N + N^2 (2N-2)^{m-1}` for `N ≥ 2`, `m ≥ 1`. -/
theorem V_closed (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) :
    (2 * N - 3) * V N m + N ^ 2 = (2 * N - 3) * N + N ^ 2 * (2 * N - 2) ^ (m - 1) := by
  have hr : (2 * N - 3) + 1 = 2 * N - 2 := by omega
  have hgeom := geom_sum_mul_add (2 * N - 3) (m - 1)
  rw [hr] at hgeom
  rw [V_eq_sum N m hm]
  simp only [E, Nat.add_sub_cancel, ← Finset.mul_sum]
  have hscaled := congrArg (fun x => N ^ 2 * x) hgeom
  nlinarith only [hscaled]

/-- `N` divides the vertex count, so the cell total `V/N` is an integer. -/
theorem N_dvd_V (N m : ℕ) : N ∣ V N m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [V]
  | one => simp [V]
  | more k _ ih =>
      exact dvd_add ih (dvd_mul_right N (E N (k + 1)))

/-- Asymptotic order: `V_m ≤ N + N^2 (2N-2)^{m-1}` and `N^2 (2N-2)^{m-2} ≤ V_m` for `m ≥ 2`. -/
theorem V_bounds (N m : ℕ) (hN : 2 ≤ N) (hm : 2 ≤ m) :
    N ^ 2 * (2 * N - 2) ^ (m - 2) ≤ V N m ∧ V N m ≤ N + N ^ 2 * (2 * N - 2) ^ (m - 1) := by
  have hm1 : 1 ≤ m := by omega
  have hsum := V_eq_sum N m hm1
  have hlast : E N (m - 2 + 1) ≤ ∑ k ∈ Finset.range (m - 1), E N (k + 1) :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (E N (k + 1)))
      (Finset.mem_range.mpr (by omega))
  have hlow := Nat.mul_le_mul_left N hlast
  have hgeom : ∀ n : ℕ, (∑ k ∈ Finset.range n, (2 * N - 2) ^ k) ≤
      (2 * N - 2) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, pow_succ]
        have hr : 2 ≤ 2 * N - 2 := by omega
        calc
          _ ≤ (2 * N - 2) ^ n + (2 * N - 2) ^ n := Nat.add_le_add_right ih _
          _ = (2 * N - 2) ^ n * 2 := by omega
          _ ≤ _ := Nat.mul_le_mul_left _ hr
  simp only [E, Nat.add_sub_cancel, ← Finset.mul_sum] at hsum hlow
  constructor
  · nlinarith
  · nlinarith only [hsum, Nat.mul_le_mul_left (N ^ 2) (hgeom (m - 1))]

/-- **Consensus-tree level count** (Proposition prop:consensus-tree(4)): level `n ≥ 2`
holds `N (2N-2)^{n-2} = |E_{N,n-1}|` consensus nodes. -/
theorem level_count (N n : ℕ) (hn : 2 ≤ n) : N * (2 * N - 2) ^ (n - 2) = E N (n - 1) := by
  have := hn
  simp [E, Nat.sub_sub]

/-- **Message proxy** (Proposition thm:complexity): `V/N` cells at `N^2` messages each
plus one leader message per node give `(N+1) V`. -/
theorem message_proxy (N V : ℕ) (hN : 0 < N) (hV : N ∣ V) : (V / N) * N ^ 2 + V = (N + 1) * V := by
  obtain ⟨c, rfl⟩ := hV
  rw [Nat.mul_div_cancel_left c hN]
  ring

end HSFN.Dense
