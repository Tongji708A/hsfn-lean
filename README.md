# hsfn-lean

Lean 4 formalization of the combinatorial core of the paper
**The Hyper-Simplex Fractal Network as Space, Protocol and Dynamical System** (HSFN;
earlier title *A Mathematical Theory of the Hyper-Simplex Fractal Network*).

The hyper-simplex fractal network is a self-similar peer-to-peer topology in which every
node spawns a half-scale clique of `N` offspring anchored to itself. Its nodes are the
nonempty digit words of length at most `m` over an `N`-letter alphabet, and adjacency is
decided by two prefix comparisons (siblings, parent–child). This repository
machine-checks the statements of the paper that rest on that address grammar, together
with the real-algebra core of its reliability threshold.

## What is proved

All statements are proved for every `N` and `m` (no enumeration). With the two-clause
adjacency law taken as the definition of the graph `HSFN.graph N m` on `HSFN.Addr N m`:

| Module | Paper | Content |
|---|---|---|
| `Hsfnlean/Basic.lean` | Def. address, Thm. counting, Prop. address bijection | addresses, tiers, the graph; `card_tier : |tier t| = N^t`; closed form `(N-1)|V| + N = N^{m+1}` |
| `Hsfnlean/Degree.lean` | Thm. degrees (i) | `degree_eq`: degree `2N-1` at tier 1, `2N` in the interior, `N` at the leaves, `N-1` when `m = 1` |
| `Hsfnlean/Distance.lean` | Thm. exact metric (i)–(iii) | `dist_eq_dval`: the exact distance formula; `graph_connected`; diameter `2m-1`; greedy one-step descent (existence form) |
| `Hsfnlean/Greedy.lean` | Thm. exact metric (ii) | the greedy rule as a function on words: every hop is an edge, lowers the distance by one, arrival after exactly `d(u,v)` hops and not before |
| `Hsfnlean/Links.lean` | Thm. degrees (ii) | link count in subtraction-free closed form |
| `Hsfnlean/Update.lean` | Thm. canonical cyclic update order | the digit-ordered depth-first list is repetition-free and complete; its wrap-around successor is a single cycle on the node set |
| `Hsfnlean/Family.lean` | Lemma family monotonicity | the inclusion `F(N,m) ↪ F(N',m')` is an induced, isometric, mark-preserving embedding and inclusions compose |
| `Hsfnlean/Relabel.lean` | Lemma duplicate-digit convention (ii) | cell-wise digit permutations induce graph automorphisms; marks are preserved iff every non-root permutation fixes `0` |
| `Hsfnlean/Clique.lean`, `MaxClique.lean` | Lemma blocks and maximal cliques | every clique lies in one anchored clique or in the seed cell; clique number `N+1`; the maximal cliques are exactly the non-leaf anchored cliques and the seed cell |
| `Hsfnlean/CutVertex.lean` | Prop. connectivity price (i) | descendant count `(N-1)|D(a)| + N = N^{m-t+1}`; every edge leaving `D(a)` lands on `a`; deleting `a` disconnects its descendants |
| `Hsfnlean/TreeEmbed.lean` | Lemma tree embedding | root paths of a fan-out-`N`, depth-`d` tree embed into `F(N,d+1)` with dilation one |
| `Hsfnlean/Threshold.lean` | Thm. depth-uniform reliability threshold (items 2–3), Cor. dense root correction | `f_b(x) = 1-(1-q)S_b(x)`; union bound `1-S_b(x) ≤ C(b,k)x^k`; for `2^k C(b,k) q^{k-1} < 1` (equivalently `q < q_0`) the interval `[q,2q]` is invariant and every iterate from `q` stays below `2q`; for `q > 1 - C(b,⌊b/2⌋+1)^{-1}`, `f_b(x) > x` on `[0,1)`; root correction `q + C(N,⌈N/2⌉)(2q)^{⌈N/2⌉}` |
| `Hsfnlean/ThresholdMono.lean` | Thm. depth-uniform reliability threshold (item 1) | `S_b` is nonincreasing on `[0,1]` (derivative identity), `f_b` nondecreasing, iterates from `q` nondecreasing and bounded |
| `Hsfnlean/Dense.lean` | Thm. dense counts, Prop. consensus tree (4), Prop. message proxy | facet and vertex counts of the dense variant in closed form, divisibility by `N`, level counts, `(N+1)V` proxy |
| `Hsfnlean/ExecCount.lean` | Prop. executed message count | one fault-free round as a finite type of point-to-point messages (pre-prepare, prepare, commit, `s` report and `s` dissemination senders); messages are determined by kind, sender and receiver; exact count `|Msg| + 2sN = 2(N-1)V + 2sV`; the hop charged to each message equals its graph distance in `G_II`, and the link total is `2(N-1)V + 2s(2N-1)(V/N-1)` |
| `Hsfnlean/PhysRecursion.lean` | Prop. failure recursion on the physical graph | the physical level map `g_N`; the binomial-tail shift `P[Bin(N-j,x) ≤ r-j] ≤ P[Bin(N,x) ≤ r]`; `f_N ≤ g_N` on `[0,1]`; `g_N` maps `[0,1]` into itself and is nondecreasing; `f_N^[k](q) ≤ g_N^[k](q)` at every depth |

`AxiomCheck.lean` prints the axioms of every main theorem; each uses only
`propext`, `Classical.choice` and `Quot.sound`. The recorded output is in `AXIOMS_*.txt` (latest `AXIOMS_260924.txt`: 831 statements).
The table lists the original core modules and the two added on 2026-09-24; the remaining
modules are described in `FORMALIZATION_REPORT_v5.md`.

## Build

```
# toolchain is pinned by lean-toolchain (leanprover/lean4:v4.31.0), mathlib v4.31.0
lake exe cache get      # download the prebuilt mathlib cache
lake build              # expected: Build completed successfully, no sorry
lake env lean AxiomCheck.lean
```

## Conventions

* `Addr N m := {l : List (Fin N) // l ≠ [] ∧ l.length ≤ m}`; the tier of an address is its length.
* Clause (S): equal length and equal `dropLast`. Clause (P): one word is the other plus one digit.
* Subtraction-free forms are used wherever the paper divides by `N-1` or `2N-3`.
* The reliability results are stated for the level map as a real function; no probability
  measure is constructed. `half b = (b+1)/2` is `⌈b/2⌉`.

## License

Apache 2.0, see `LICENSE`.
