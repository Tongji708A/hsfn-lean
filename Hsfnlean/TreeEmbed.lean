/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Basic

/-!
# Tree embedding (Lemma lem:tree-embed)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409).
A rooted tree of fan-out at most `N` and depth `d` is identified with the prefix-closed
set of its root paths, digit words over `Fin N` of length at most `d`. Prefixing every
path with the tier-`1` digit `0` embeds the tree into `F(N, d+1)` with dilation one:
the map is injective and every parent–child pair lands on an anchor uplink. No
contraction is used, and the sibling links of the host are simply left unselected.
-/

namespace HSFN

variable {N : ℕ}

/-- The embedding of root paths: prefix the tier-`1` digit `0`. -/
def treeEmbed (hN : 0 < N) (p : List (Fin N)) : List (Fin N) := ⟨0, hN⟩ :: p

theorem treeEmbed_injective (hN : 0 < N) : Function.Injective (treeEmbed hN) := by
  intro p q h
  simpa [treeEmbed] using h

theorem treeEmbed_length (hN : 0 < N) (p : List (Fin N)) :
    (treeEmbed hN p).length = p.length + 1 := by
  simp [treeEmbed]

/-- A path of length at most `d` lands on an address of `F(N, d+1)`. -/
def treeEmbedAddr (hN : 0 < N) {d : ℕ} (p : List (Fin N)) (hp : p.length ≤ d) : Addr N (d + 1) :=
  ⟨treeEmbed hN p, by simp [treeEmbed], by simp [treeEmbed]; omega⟩

theorem tier_treeEmbedAddr (hN : 0 < N) {d : ℕ} (p : List (Fin N)) (hp : p.length ≤ d) :
    (treeEmbedAddr hN p hp).tier = p.length + 1 := by
  simp [treeEmbedAddr, Addr.tier, treeEmbed]

theorem treeEmbedAddr_injective (hN : 0 < N) {d : ℕ} {p q : List (Fin N)}
    (hp : p.length ≤ d) (hq : q.length ≤ d) (h : treeEmbedAddr hN p hp = treeEmbedAddr hN q hq) :
    p = q := by
  apply treeEmbed_injective hN
  simpa [treeEmbedAddr] using congrArg Subtype.val h

/-- **Dilation one** (Lemma lem:tree-embed): a tree edge, from a path to a child path,
is carried to an anchor uplink of `F(N, d+1)`. -/
theorem treeEmbedAddr_adj (hN : 0 < N) {d : ℕ} (p : List (Fin N)) (j : Fin N)
    (hp : p.length + 1 ≤ d) :
    (graph N (d + 1)).Adj (treeEmbedAddr hN p (by omega)) (treeEmbedAddr hN (p ++ [j]) (by simpa using hp)) := by
  refine ⟨?_, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
  · intro h
    have := congrArg (fun a : Addr N (d + 1) => a.1.length) h
    simp [treeEmbedAddr, treeEmbed] at this
  · simp [treeEmbedAddr, treeEmbed]
  · show (⟨0, hN⟩ :: (p ++ [j])).dropLast = ⟨0, hN⟩ :: p
    rw [List.dropLast_cons_of_ne_nil (List.append_ne_nil_of_right_ne_nil _ (by simp)),
      List.dropLast_concat]

/-- The root lands at tier `1` and a path of length `k` at tier `k + 1`: depth `d`
reaches tier `d + 1`. -/
theorem tier_treeEmbedAddr_le (hN : 0 < N) {d : ℕ} (p : List (Fin N)) (hp : p.length ≤ d) :
    (treeEmbedAddr hN p hp).tier ≤ d + 1 := by
  rw [tier_treeEmbedAddr]; omega

end HSFN
