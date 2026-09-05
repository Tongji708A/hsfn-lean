/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Links

/-!
# Average degree of the HSFN (Theorem thm:deg-II(iii), equation eq:avgdeg-II)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).

With `V = |V_II| = N(N^m - 1)/(N - 1)` (Theorem thm:unified-count, closed form
`Addr.card_closed`) and `L = L_II` the link count (Theorem thm:deg-II(ii),
`card_edges_closed`), the paper's equation eq:avgdeg-II reads

  `d̄_II = 2 L / V = (N + 1) - 2 (N - 1) / (N^m - 1)`,

"which is increasing in `m` with limit `N + 1`".

Three statements are given.

* `two_mul_card_edges_mul_pow` is the natural-number, subtraction-free form of
  eq:avgdeg-II, obtained by clearing both denominators of
  `2 L / V = (N + 1) - 2 (N - 1)/(N^m - 1)` and moving every negative term to
  the other side; the alphabet size is written `N = n + 1` so that no natural
  subtraction occurs.
* `avgDeg_eq` is eq:avgdeg-II itself over `ℝ`, valid for `N ≥ 2` and `m ≥ 1`
  (both hypotheses are needed: `V ≠ 0` and `N^m ≠ 1`).
* `avgDeg_strictMono` (with its nondecreasing corollary `avgDeg_mono`) and
  `tendsto_avgDeg` are the two closing clauses of Theorem thm:deg-II(iii): the
  average degree is *increasing* in the depth `m`, with limit `N + 1`.

Scope, honestly stated. Formalized here is *only* part (iii) of Theorem
thm:deg-II. Parts (i) (the tier-wise degree profile) and (ii) (the closed form
for `L_II`) are not proved in this file; they live in `Hsfnlean.Degree`
(`degree_eq`) and `Hsfnlean.Links` (`card_edges_closed`) and are imported as
black boxes. The paper states thm:deg-II under `N >= 3`; the hypotheses below
are the weaker `N >= 2` (with `m >= 1`), so every statement here covers the
paper's range and more. Nothing about `m = 0` or `N <= 1` is claimed: at
`m = 0` the address set is empty and `avgDeg N 0` is the junk value `0`, which
is why `avgDeg_eq`, `avgDeg_strictMono` and `avgDeg_mono` all carry `1 <= m`
(the limit statement needs no such hypothesis, `atTop` discarding `m = 0`).
No asymptotic *rate* is claimed, only the limit.
-/

namespace HSFN

open Finset

/-- **Average degree, subtraction-free natural-number form**
(Theorem thm:deg-II(iii), equation eq:avgdeg-II with `N = n + 1`).

Writing `V = Fintype.card (Addr N m)` and `L = (graph N m).edgeFinset.card`,
equation eq:avgdeg-II says `2 L / V = (N + 1) - 2 (N - 1)/(N^m - 1)`, i.e.
`2 L (N^m - 1) + 2 (N - 1) V = (N + 1)(N^m - 1) V`. Clearing the two natural
subtractions `N^m - 1` and `N - 1` by transposition gives the identity below,
in which every term is a product of naturals. -/
theorem two_mul_card_edges_mul_pow (n m : ℕ) (hm : 1 ≤ m) :
    2 * (graph (n + 1) m).edgeFinset.card * (n + 1) ^ m
        + 2 * n * Fintype.card (Addr (n + 1) m)
        + (n + 2) * Fintype.card (Addr (n + 1) m)
      = 2 * (graph (n + 1) m).edgeFinset.card
        + (n + 2) * (n + 1) ^ m * Fintype.card (Addr (n + 1) m) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · -- Write `N ^ m = Q + N` (legitimate since `m ≥ 1`), so that both closed
    -- forms become subtraction-free polynomials in `n` and `Q`.
    obtain ⟨Q, hQ⟩ : ∃ Q, (n + 1) ^ m = Q + (n + 1) :=
      ⟨(n + 1) ^ m - (n + 1), by
        have := Nat.le_self_pow (n := m) (by omega) (n + 1); omega⟩
    have hsub : (n + 1) ^ m - (n + 1) = Q := by omega
    have hA : n * (2 * (graph (n + 1) m).edgeFinset.card)
        = (n + 1) * n ^ 2 + (n + 1) * (n + 2) * Q := by
      rw [card_edges_closed n m hm, hsub]
    have hB : n * Fintype.card (Addr (n + 1) m) = (n + 1) * Q + (n + 1) * n := by
      have h := Addr.card_closed n m
      rw [pow_succ, hQ] at h
      have hring : (Q + (n + 1)) * (n + 1) = ((n + 1) * Q + (n + 1) * n) + (n + 1) := by
        ring
      rw [hring] at h
      exact Nat.add_right_cancel h
    -- Cancel the factor `n` over `ℤ`, where the two closed forms combine linearly.
    have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have hAZ : (n : ℤ) * (2 * ((graph (n + 1) m).edgeFinset.card : ℤ))
        = ((n : ℤ) + 1) * (n : ℤ) ^ 2 + ((n : ℤ) + 1) * ((n : ℤ) + 2) * (Q : ℤ) := by
      exact_mod_cast hA
    have hBZ : (n : ℤ) * (Fintype.card (Addr (n + 1) m) : ℤ)
        = ((n : ℤ) + 1) * (Q : ℤ) + ((n : ℤ) + 1) * (n : ℤ) := by
      exact_mod_cast hB
    have hQZ : ((n : ℤ) + 1) ^ m = (Q : ℤ) + ((n : ℤ) + 1) := by exact_mod_cast hQ
    have goalZ :
        2 * ((graph (n + 1) m).edgeFinset.card : ℤ) * ((n : ℤ) + 1) ^ m
            + 2 * (n : ℤ) * (Fintype.card (Addr (n + 1) m) : ℤ)
            + ((n : ℤ) + 2) * (Fintype.card (Addr (n + 1) m) : ℤ)
          = 2 * ((graph (n + 1) m).edgeFinset.card : ℤ)
            + ((n : ℤ) + 2) * ((n : ℤ) + 1) ^ m
              * (Fintype.card (Addr (n + 1) m) : ℤ) := by
      apply mul_left_cancel₀ hnZ
      rw [hQZ]
      linear_combination ((Q : ℤ) + (n : ℤ)) * hAZ
        + ((3 * (n : ℤ) + 2) - ((n : ℤ) + 2) * ((Q : ℤ) + (n : ℤ) + 1)) * hBZ
    exact_mod_cast goalZ

/-- The average degree `d̄_II(N,m) = 2 L_II / V_II` of the HSFN, as a real
number (Theorem thm:deg-II(iii)). -/
noncomputable def avgDeg (N m : ℕ) : ℝ :=
  (2 * ((graph N m).edgeFinset.card : ℝ)) / (Fintype.card (Addr N m) : ℝ)

/-- **Equation eq:avgdeg-II**: for `N ≥ 2` and `m ≥ 1` the average degree of
`G_II(N,m)` is `(N + 1) - 2 (N - 1)/(N^m - 1)`.

Both hypotheses are used: `m ≥ 1` makes the vertex set nonempty, and `N ≥ 2`
together with `m ≥ 1` makes `N^m - 1 ≠ 0`. (Concrete instance: `N = 3`, `m = 2`,
where `V = 12`, `L = 21` and both sides equal `7/2`.) -/
theorem avgDeg_eq (N m : ℕ) (hN : 2 ≤ N) (hm : 1 ≤ m) :
    avgDeg N m = ((N : ℝ) + 1) - 2 * ((N : ℝ) - 1) / ((N : ℝ) ^ m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hVpos : 0 < Fintype.card (Addr (n + 1) m) := by
    have : Nonempty (Addr (n + 1) m) := ⟨⟨[0], by simp, by simpa using hm⟩⟩
    exact Fintype.card_pos
  have hV : (Fintype.card (Addr (n + 1) m) : ℝ) ≠ 0 := by
    exact_mod_cast hVpos.ne'
  have hN1 : (1 : ℝ) < ((n : ℝ) + 1) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hPow : (1 : ℝ) < ((n : ℝ) + 1) ^ m := one_lt_pow₀ hN1 (by omega)
  have hP : ((n : ℝ) + 1) ^ m - 1 ≠ 0 := sub_ne_zero_of_ne (ne_of_gt hPow)
  have keyR :
      2 * ((graph (n + 1) m).edgeFinset.card : ℝ) * ((n : ℝ) + 1) ^ m
          + 2 * (n : ℝ) * (Fintype.card (Addr (n + 1) m) : ℝ)
          + ((n : ℝ) + 2) * (Fintype.card (Addr (n + 1) m) : ℝ)
        = 2 * ((graph (n + 1) m).edgeFinset.card : ℝ)
          + ((n : ℝ) + 2) * ((n : ℝ) + 1) ^ m
            * (Fintype.card (Addr (n + 1) m) : ℝ) := by
    exact_mod_cast two_mul_card_edges_mul_pow n m hm
  unfold avgDeg
  push_cast
  rw [div_eq_iff hV]
  field_simp
  ring_nf
  ring_nf at keyR
  linarith [keyR]

/-- **Strict monotonicity in the depth** (Theorem thm:deg-II(iii): the average
degree "is increasing in `m`"). The paper's word is *increasing*, so the faithful
statement is the strict one: for `N ≥ 2` and `1 ≤ m₁ < m₂`,
`d̄_II(N,m₁) < d̄_II(N,m₂)`. Indeed the subtracted term `2(N-1)/(N^m - 1)` of
eq:avgdeg-II is strictly positive and strictly shrinking in `m`. -/
theorem avgDeg_strictMono (N : ℕ) (hN : 2 ≤ N) {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁)
    (h : m₁ < m₂) : avgDeg N m₁ < avgDeg N m₂ := by
  have hm₂ : 1 ≤ m₂ := le_trans hm₁ h.le
  rw [avgDeg_eq N m₁ hN hm₁, avgDeg_eq N m₂ hN hm₂]
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have h1 : (0 : ℝ) < (N : ℝ) ^ m₁ - 1 := by
    have := one_lt_pow₀ hN1 (by omega : m₁ ≠ 0)
    linarith
  have h2 : (N : ℝ) ^ m₁ - 1 < (N : ℝ) ^ m₂ - 1 := by
    have := pow_lt_pow_right₀ hN1 h
    linarith
  have hnum : (0 : ℝ) < 2 * ((N : ℝ) - 1) := by linarith
  have := div_lt_div_of_pos_left hnum h1 h2
  linarith

/-- Nondecreasing form of `avgDeg_strictMono`, for `1 ≤ m₁ ≤ m₂`. -/
theorem avgDeg_mono (N : ℕ) (hN : 2 ≤ N) {m₁ m₂ : ℕ} (hm₁ : 1 ≤ m₁)
    (h : m₁ ≤ m₂) : avgDeg N m₁ ≤ avgDeg N m₂ := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_refl _
  · exact (avgDeg_strictMono N hN hm₁ hlt).le

/-- **The limit** (Theorem thm:deg-II(iii), "with limit `N + 1`"): for `N ≥ 2`
the average degree tends to `N + 1` as the depth `m` grows. -/
theorem tendsto_avgDeg (N : ℕ) (hN : 2 ≤ N) :
    Filter.Tendsto (fun m => avgDeg N m) Filter.atTop (nhds ((N : ℝ) + 1)) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  -- `N ^ m - 1 → ∞`, hence the subtracted term of eq:avgdeg-II tends to `0`.
  have hpow : Filter.Tendsto (fun m : ℕ => (N : ℝ) ^ m - 1) Filter.atTop Filter.atTop := by
    simpa [sub_eq_add_neg] using
      Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ)
        (tendsto_pow_atTop_atTop_of_one_lt hN1)
  have hzero : Filter.Tendsto
      (fun m : ℕ => 2 * ((N : ℝ) - 1) / ((N : ℝ) ^ m - 1)) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hpow
  have hmain : Filter.Tendsto
      (fun m : ℕ => ((N : ℝ) + 1) - 2 * ((N : ℝ) - 1) / ((N : ℝ) ^ m - 1))
      Filter.atTop (nhds ((N : ℝ) + 1)) := by
    simpa using (tendsto_const_nhds (x := ((N : ℝ) + 1))
      (f := Filter.atTop (α := ℕ))).sub hzero
  refine hmain.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with m hm
  exact (avgDeg_eq N m hN hm).symm

end HSFN
