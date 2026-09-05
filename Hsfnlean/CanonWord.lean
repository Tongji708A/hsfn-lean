/-
Copyright (c) 2026 Hao Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Xu
-/
import Hsfnlean.Calculus

/-!
# Canonical words and fixed-origin reachability (Proposition prop:canon-word)

Paper: "A Mathematical Theory of the Hyper-Simplex Fractal Network" (R260409),
Proposition `prop:canon-word` item 1 (canonical word, reachability, closure), with the
generator-preservation half resting on the `wf_*` lemmas of `Hsfnlean.Calculus`
(Definition `def:calc-state`, Table `tab:typing`).

The paper's item 1 reads: every configuration `x = (D, μ, ζ)` of `F(N,m)` is reachable from the
seed by the canonical word

  `w_can(x) : spawn (D \ {ε}) ; join μ ; disable ζ`,

each block in length-lexicographic order; and conversely every state reachable from the seed is a
configuration, so that the state space is exactly the configuration space and `w_can` is a normal
form for states.

## What this file states

* `runSpawns`, `runJoins`, `runDisables`, `canonical` — executing the three blocks of the canonical
  word from the seed, as a fold of the `Option`-valued generators of `Hsfnlean.Calculus`.
* `Letter`, `runGen`, `runWord`, `canonWord`, `Reachable` — arbitrary generator words and the
  reachability relation they induce; `canonical` is `runWord (canonWord …)` (`canonical_eq_runWord`).
* `SpawnOrder`, `Enumerates` — the ordering hypothesis. Rather than constructing the
  length-lexicographic sort, we abstract the property the paper's proof actually uses: the spawn
  block is a duplicate-free enumeration of `D \ {[]}` in which every proper nonempty prefix of an
  entry occurs strictly earlier. `exists_spawnOrder` proves that every well-formed configuration
  admits such a list, by sorting `D \ {[]}` with `List.mergeSort` on length: a proper prefix is
  strictly shorter, hence sorted earlier.
* `exists_canonWord_run` — the paper's item-1 sentence verbatim: every configuration is reachable
  from the seed *by a canonical word*, the three block enumerations existing.
* `canonical_eq` — item 1, forward half: under those hypotheses `canonical … = some x` for every
  well-formed `x`. Its three block lemmas `runSpawns_partial`, `runJoins_all`, `runDisables_all`
  spell out the paper's argument: when `spawn a` fires its parent cell is already deployed so `a` is
  a slot, `ζ` is still empty so `a` is enabled; the joins then find existing vacant enabled slots;
  the disables find vacant childless enabled slots by the invariant `ζ ∩ (μ ∪ D) = ∅`.
  `spawn_step_of_mem_target` is the single-step form of the spawn invariant.
* `wf_runGen`, `wf_runWord`, `reachable_wf`, `reachable_seed_wf` — item 1, converse half: folding
  any list of generators from a well-formed state yields a well-formed state, so every state
  reachable from the seed is a configuration.
* `reachable_seed_iff` — the two halves combined: the state space is exactly the configuration
  space. `canonWord_normal_form` records that the canonical word determines the state.

## What this file does NOT formalize

* Item 2 of `prop:canon-word` (fixed-origin decidability). Executing a word is already decidable
  here because the generators are computable `Option`-valued functions on `Finset`s, but the
  complexity claim ("linear in the word lengths times the footprint sizes") is a cost model that is
  not modelled at all.
* The length-lexicographic order itself. Of the paper's three ordered blocks it survives only in the
  spawn block, and there only through its consequence `SpawnOrder.prefix_before` (a proper prefix is
  strictly shorter, hence earlier). The tie-breaking lexicographic component is never defined:
  `exists_spawnOrder` builds a merely length-sorted witness, which is enough for the proof but is a
  coarsening of the paper's order. For the join and the disable blocks the order is dropped outright:
  `Enumerates` constrains nothing but membership and non-repetition, so `runJoins_all` and
  `runDisables_all` assert more than the paper does, not less.
* The `permute` generator of the paper's eight. `Hsfnlean.Calculus` defines seven letters (spawn,
  retract, join, leave, disable, enable, graft) and `Letter` has exactly those seven constructors, so
  `Reachable` is reachability in the permutation-free calculus. Since the canonical word uses only
  spawn/join/disable, adding `permute` would not change `reachable_seed_iff` provided it too
  preserved well-formedness, but that is not proved here.
* Uniqueness of the canonical word as a *word* (Knuth–Bendix style confluence). The paper claims no
  confluence theorem and neither do we; `canonWord_normal_form` only says the word determines the
  state it produces.
-/

namespace HSFN

namespace Calc

variable {N m : ℕ}

/-! ### Private re-derivations of the slot calculus of `Hsfnlean.Calculus`

The corresponding lemmas there are `private`, hence invisible across modules; the proofs are the
same. -/

private theorem aux_mem_cellW {v w : Word N} :
    v ∈ cellW w ↔ v ≠ [] ∧ v.dropLast = w := by
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨d, _, rfl⟩
    simp
  · rintro ⟨hv, rfl⟩
    exact Finset.mem_image.mpr
      ⟨v.getLast hv, Finset.mem_univ _, List.dropLast_append_getLast hv⟩

private theorem aux_mem_Sl {x : Config N m} {w : Word N} :
    w ∈ x.Sl ↔ w ≠ [] ∧ w.dropLast ∈ x.D := by
  simp only [Config.Sl, Finset.mem_biUnion, aux_mem_cellW]
  aesop

private theorem aux_dropLast_ne {w : Word N} (hw : w ≠ []) : w.dropLast ≠ w := by
  intro he
  have := congrArg List.length he
  have := List.length_pos_of_ne_nil hw
  simp only [List.length_dropLast] at *
  omega

private theorem aux_prefix_mem {x : Config N m} (hx : x.WF) {v w : Word N}
    (hw : w ∈ x.D) (hv : v <+: w) : v ∈ x.D := by
  obtain ⟨t, rfl⟩ := hv
  revert hw
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t d ih =>
    intro hw
    apply ih
    have hp := hx.2.2.1 (v ++ (t ++ [d])) hw (by simp)
    simpa [← List.append_assoc] using hp

private theorem aux_prefix_length_lt {a b : Word N} (hba : b <+: a) (hne : b ≠ a) :
    b.length < a.length := by
  obtain ⟨t, rfl⟩ := hba
  have ht : t ≠ [] := by rintro rfl; simp at hne
  have h1 : 0 < t.length := List.length_pos_of_ne_nil ht
  simp only [List.length_append]
  omega

/-! ## Executing blocks of the canonical word -/

/-- Fold `spawn` over a list of addresses, left to right. -/
def runSpawns : List (Word N) → Config N m → Option (Config N m)
  | [], x => some x
  | a :: l, x => (spawn a x).bind (runSpawns l)

/-- Fold `join` over a list of slots, left to right. -/
def runJoins : List (Word N) → Config N m → Option (Config N m)
  | [], x => some x
  | s :: l, x => (join s x).bind (runJoins l)

/-- Fold `disable` over a list of slots, left to right. -/
def runDisables : List (Word N) → Config N m → Option (Config N m)
  | [], x => some x
  | s :: l, x => (disable s x).bind (runDisables l)

/-- The canonical word `w_can` executed from the seed: spawn the addresses of `lD`, then join the
slots of `lμ`, then disable the slots of `lζ`. The three lists carry the enumeration and the
ordering; the hypotheses relating them to a target configuration are `SpawnOrder` and
`Enumerates`. -/
def canonical (N m : ℕ) (lD lμ lζ : List (Word N)) : Option (Config N m) :=
  ((runSpawns lD (seed N m)).bind (runJoins lμ)).bind (runDisables lζ)

/-! ## Generator words and reachability -/

/-- One letter of the calculus (Table `tab:typing`), excluding `permute`, which
`Hsfnlean.Calculus` does not define. -/
inductive Letter (N : ℕ) where
  | spawn (a : Word N)
  | retract (a : Word N)
  | join (s : Word N)
  | leave (s : Word N)
  | disable (s : Word N)
  | enable (s : Word N)
  | graft (a b : Word N)
  deriving DecidableEq

/-- The partial map denoted by a letter. -/
def runGen : Letter N → Config N m → Option (Config N m)
  | .spawn a, x => spawn a x
  | .retract a, x => retract a x
  | .join s, x => join s x
  | .leave s, x => leave s x
  | .disable s, x => disable s x
  | .enable s, x => enable s x
  | .graft a b, x => graft a b x

/-- A word is executed left to right. -/
def runWord : List (Letter N) → Config N m → Option (Config N m)
  | [], x => some x
  | g :: w, x => (runGen g x).bind (runWord w)

/-- The canonical word as an actual word of generators. -/
def canonWord (lD lμ lζ : List (Word N)) : List (Letter N) :=
  lD.map Letter.spawn ++ lμ.map Letter.join ++ lζ.map Letter.disable

/-- `y` is reachable from `x` by some word of generators. -/
def Reachable (x y : Config N m) : Prop := ∃ w : List (Letter N), runWord w x = some y

theorem runWord_append (w₁ w₂ : List (Letter N)) (x : Config N m) :
    runWord (w₁ ++ w₂) x = (runWord w₁ x).bind (runWord w₂) := by
  induction w₁ generalizing x with
  | nil => simp [runWord]
  | cons g w ih =>
    simp only [List.cons_append, runWord]
    cases hg : runGen g x with
    | none => simp
    | some y => simp [ih]

private theorem aux_runWord_spawns (l : List (Word N)) (x : Config N m) :
    runWord (l.map Letter.spawn) x = runSpawns l x := by
  induction l generalizing x with
  | nil => simp [runWord, runSpawns]
  | cons a l ih =>
    simp only [List.map_cons, runWord, runGen, runSpawns]
    cases h : spawn a x with
    | none => simp
    | some y => simp [ih]

private theorem aux_runWord_joins (l : List (Word N)) (x : Config N m) :
    runWord (l.map Letter.join) x = runJoins l x := by
  induction l generalizing x with
  | nil => simp [runWord, runJoins]
  | cons s l ih =>
    simp only [List.map_cons, runWord, runGen, runJoins]
    cases h : join s x with
    | none => simp
    | some y => simp [ih]

private theorem aux_runWord_disables (l : List (Word N)) (x : Config N m) :
    runWord (l.map Letter.disable) x = runDisables l x := by
  induction l generalizing x with
  | nil => simp [runWord, runDisables]
  | cons s l ih =>
    simp only [List.map_cons, runWord, runGen, runDisables]
    cases h : disable s x with
    | none => simp
    | some y => simp [ih]

/-- `canonical` is exactly the execution of `canonWord` from the seed. -/
theorem canonical_eq_runWord (N m : ℕ) (lD lμ lζ : List (Word N)) :
    canonical N m lD lμ lζ = runWord (canonWord lD lμ lζ) (seed N m) := by
  have e1 : (runWord (lD.map Letter.spawn) : Config N m → Option (Config N m)) = runSpawns lD :=
    funext (aux_runWord_spawns lD)
  have e2 : (runWord (lμ.map Letter.join) : Config N m → Option (Config N m)) = runJoins lμ :=
    funext (aux_runWord_joins lμ)
  have e3 : (runWord (lζ.map Letter.disable) : Config N m → Option (Config N m)) = runDisables lζ :=
    funext (aux_runWord_disables lζ)
  rw [canonical, canonWord, runWord_append, runWord_append, e1, e2, e3]

/-! ## The ordering hypothesis -/

/-- `l` is a duplicate-free enumeration of the finite set `s`. Used for the join block and for the
disable block. For those two blocks the paper's length-lexicographic order carries no information:
the guards of `join` (resp. `disable`) read only `Sl`, `μ` and `ζ` (resp. `Sl`, `μ`, `D` and `ζ`),
none of which any earlier letter of the same block can invalidate, so *every* enumeration of the
block executes (`runJoins_all`, `runDisables_all` are stated for an arbitrary `Enumerates` list, and
are therefore strictly stronger than the paper's ordered claim). `join_join_comm` of
`Hsfnlean.Calculus` is the two-letter instance of that independence; the corresponding
`disable`/`disable` instance is not among the commutation lemmas proved there. -/
def Enumerates (s : Finset (Word N)) (l : List (Word N)) : Prop :=
  l.Nodup ∧ ∀ a : Word N, a ∈ l ↔ a ∈ s

/-- The spawn block of the canonical word: `l` enumerates `x.D \ {[]}` without repetition, in an
order in which every proper nonempty prefix of an entry occurs strictly earlier. This is the only
consequence of the paper's length-lexicographic order that the proof of `prop:canon-word` uses:
"when `spawn a` fires, `pre(a) ∈ D` has already been spawned, because it precedes `a`
length-lexicographically". -/
structure SpawnOrder (x : Config N m) (l : List (Word N)) : Prop where
  /-- `l` lists exactly the nonempty deployed cells. -/
  mem_iff : ∀ a : Word N, a ∈ l ↔ (a ∈ x.D ∧ a ≠ [])
  /-- No address is spawned twice. -/
  nodup : l.Nodup
  /-- Every proper nonempty prefix of an entry occurs before it. -/
  prefix_before : ∀ (l₁ l₂ : List (Word N)) (a b : Word N), l = l₁ ++ a :: l₂ →
    b <+: a → b ≠ a → b ≠ [] → b ∈ l₁

/-- Comparison by length, the `Bool`-valued relation `mergeSort` wants. -/
private def aux_lenLe (u v : Word N) : Bool := decide (u.length ≤ v.length)

private theorem aux_lenLe_trans (a b c : Word N)
    (h₁ : aux_lenLe a b) (h₂ : aux_lenLe b c) : aux_lenLe a c := by
  simp only [aux_lenLe, decide_eq_true_eq] at *
  omega

private theorem aux_lenLe_total (a b : Word N) : aux_lenLe a b || aux_lenLe b a := by
  simp only [aux_lenLe, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- Every configuration admits a spawn order; sorting `D \ {[]}` by length (a coarsening of the
paper's length-lexicographic order) is a witness, since a proper prefix is strictly shorter. This is
the one place where the existence of an order with `prefix_before` is constructed rather than
assumed, which is what keeps `canonical_eq` and `SpawnOrder` from being vacuous. -/
theorem exists_spawnOrder (x : Config N m) (hx : x.WF) : ∃ l : List (Word N), SpawnOrder x l := by
  classical
  set L : List (Word N) := ((x.D.erase []).toList).mergeSort aux_lenLe with hL
  have hmem : ∀ a : Word N, a ∈ L ↔ (a ∈ x.D ∧ a ≠ []) := by
    intro a
    have h : a ∈ L ↔ (a ≠ [] ∧ a ∈ x.D) := by
      rw [hL]
      simp [Finset.mem_toList, Finset.mem_erase]
    rw [h]
    tauto
  have hnodup : L.Nodup := by
    rw [hL]
    exact List.nodup_mergeSort.mpr (Finset.nodup_toList _)
  have hpair : L.Pairwise (fun u v : Word N => u.length ≤ v.length) := by
    have h := List.pairwise_mergeSort aux_lenLe_trans aux_lenLe_total ((x.D.erase []).toList)
    rw [hL]
    refine h.imp ?_
    intro u v huv
    simpa [aux_lenLe] using huv
  refine ⟨L, hmem, hnodup, ?_⟩
  intro l₁ l₂ a b hdec hba hne hbn
  have haL : a ∈ L := by rw [hdec]; simp
  have haD : a ∈ x.D := (hmem a).mp haL |>.1
  have hbD : b ∈ x.D := aux_prefix_mem hx haD hba
  have hbL : b ∈ L := (hmem b).mpr ⟨hbD, hbn⟩
  rw [hdec] at hbL hpair
  rcases List.mem_append.mp hbL with h | h
  · exact h
  · rcases List.mem_cons.mp h with rfl | h
    · exact absurd rfl hne
    · exfalso
      rcases List.pairwise_append.mp hpair with ⟨-, hcons, -⟩
      have hle := (List.pairwise_cons.mp hcons).1 b h
      have := aux_prefix_length_lt hba hne
      omega

/-- Any finite set is enumerated by some duplicate-free list. -/
theorem exists_enumerates (s : Finset (Word N)) : ∃ l : List (Word N), Enumerates s l :=
  ⟨s.toList, Finset.nodup_toList s, fun _ => Finset.mem_toList⟩

/-! ## Item 1, forward half: the canonical word reaches `x` -/

/-- The single-step form of the spawn invariant: while the partially built state `y` is a
prefix-closed subset of the target's deployment with empty decommission set, spawning the next
address `a` of the target is applicable, and the result is still a subset of the target. This is the
fallback statement isolated in the task description; `runSpawns_partial` is its iteration. -/
theorem spawn_step_of_mem_target {x y : Config N m} (hx : x.WF) (a : Word N)
    (ha : a ∈ x.D) (han : a ≠ []) (hsub : y.D ⊆ x.D)
    (hclosed : ∀ w ∈ y.D, w ≠ [] → w.dropLast ∈ y.D)
    (hpar : a.dropLast ∈ y.D) (hnew : a ∉ y.D) (hζ : y.ζ = ∅) :
    spawn a y = some ⟨insert a y.D, y.μ, y.ζ⟩ ∧ insert a y.D ⊆ x.D ∧
      (∀ w ∈ insert a y.D, w ≠ [] → w.dropLast ∈ insert a y.D) := by
  refine ⟨?_, ?_, ?_⟩
  · have hg : a ∈ y.Sl ∧ a ∉ y.D ∧ a ∉ y.ζ ∧ a.length + 1 ≤ m :=
      ⟨aux_mem_Sl.mpr ⟨han, hpar⟩, hnew, by simp [hζ], hx.2.1 a ha⟩
    unfold spawn
    rw [if_pos hg]
  · intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact ha
    · exact hsub hw
  · intro w hw hwn
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_insert_of_mem hpar
    · exact Finset.mem_insert_of_mem (hclosed w hw hwn)

/-- The spawn block executed from a state that already deploys the root together with the addresses
of `l₀`. This is the induction that `runSpawns_partial` specializes at `l₀ = []`. -/
private theorem aux_runSpawns_prefix (x : Config N m) (hx : x.WF) :
    ∀ (l₁ l₀ l₂ : List (Word N)), SpawnOrder x (l₀ ++ l₁ ++ l₂) →
      runSpawns l₁ (⟨insert [] l₀.toFinset, ∅, ∅⟩ : Config N m)
        = some ⟨insert [] (l₀ ++ l₁).toFinset, ∅, ∅⟩ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₀ l₂ _
    simp [runSpawns]
  | cons a l ih =>
    intro l₀ l₂ h
    have hdec : l₀ ++ (a :: l) ++ l₂ = l₀ ++ a :: (l ++ l₂) := by simp
    have hax : a ∈ x.D ∧ a ≠ [] := (h.mem_iff a).mp (by simp)
    have hnodup := h.nodup
    rw [hdec] at hnodup
    have hnotin : a ∉ l₀ := by
      intro hmem
      rw [List.nodup_append] at hnodup
      exact hnodup.2.2 a hmem a (by simp) rfl
    have hpar : a.dropLast ∈ insert ([] : Word N) l₀.toFinset := by
      by_cases hd : a.dropLast = []
      · rw [hd]; exact Finset.mem_insert_self _ _
      · have hb := h.prefix_before l₀ (l ++ l₂) a a.dropLast hdec (List.dropLast_prefix a)
          (aux_dropLast_ne hax.2) hd
        exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hb)
    have hspawn : spawn a (⟨insert [] l₀.toFinset, ∅, ∅⟩ : Config N m)
        = some ⟨insert a (insert [] l₀.toFinset), ∅, ∅⟩ := by
      have hg : a ∈ (⟨insert ([] : Word N) l₀.toFinset, ∅, ∅⟩ : Config N m).Sl ∧
          a ∉ (⟨insert ([] : Word N) l₀.toFinset, ∅, ∅⟩ : Config N m).D ∧
          a ∉ (⟨insert ([] : Word N) l₀.toFinset, ∅, ∅⟩ : Config N m).ζ ∧ a.length + 1 ≤ m := by
        refine ⟨aux_mem_Sl.mpr ⟨hax.2, hpar⟩, ?_, by simp, hx.2.1 a hax.1⟩
        simp only [Finset.mem_insert, List.mem_toFinset, not_or]
        exact ⟨hax.2, hnotin⟩
      unfold spawn
      rw [if_pos hg]
    have hL : l₀ ++ (a :: l) ++ l₂ = (l₀ ++ [a]) ++ l ++ l₂ := by simp
    have hIH := ih (l₀ ++ [a]) l₂ (by rw [← hL]; exact h)
    have hlist : (l₀ ++ [a]) ++ l = l₀ ++ a :: l := by simp
    have hset : insert ([] : Word N) (l₀ ++ [a]).toFinset
        = insert a (insert ([] : Word N) l₀.toFinset) := by
      ext w
      simp only [Finset.mem_insert, List.toFinset_append, Finset.mem_union, List.mem_toFinset,
        List.mem_singleton]
      tauto
    rw [hlist, hset] at hIH
    simp only [runSpawns, hspawn, Option.bind_some]
    exact hIH

/-- After the first `l₁` letters of the spawn block, the state deploys exactly the root together
with the addresses already spawned, with no occupancy and no decommission. -/
theorem runSpawns_partial (x : Config N m) (hx : x.WF) (l₁ l₂ : List (Word N))
    (h : SpawnOrder x (l₁ ++ l₂)) :
    runSpawns l₁ (seed N m) = some ⟨insert [] l₁.toFinset, ∅, ∅⟩ := by
  have h0 : SpawnOrder x ([] ++ l₁ ++ l₂) := by simpa using h
  have := aux_runSpawns_prefix x hx l₁ [] l₂ h0
  simpa [seed] using this

/-- The whole spawn block deploys exactly `x.D`. -/
theorem runSpawns_all (x : Config N m) (hx : x.WF) (lD : List (Word N)) (h : SpawnOrder x lD) :
    runSpawns lD (seed N m) = some ⟨x.D, ∅, ∅⟩ := by
  have h0 : SpawnOrder x (lD ++ []) := by simpa using h
  have hrun := runSpawns_partial x hx lD [] h0
  have hset : insert ([] : Word N) lD.toFinset = x.D := by
    ext w
    simp only [Finset.mem_insert, List.mem_toFinset]
    constructor
    · rintro (rfl | hw)
      · exact hx.1
      · exact ((h.mem_iff w).mp hw).1
    · intro hw
      by_cases he : w = []
      · exact Or.inl he
      · exact Or.inr ((h.mem_iff w).mpr ⟨hw, he⟩)
  rw [hrun, hset]

private theorem aux_runJoins : ∀ (l : List (Word N)) (D M Z : Finset (Word N)),
    (∀ s ∈ l, s ∈ D.biUnion cellW) → (∀ s ∈ l, s ∉ M) → (∀ s ∈ l, s ∉ Z) → l.Nodup →
      runJoins l (⟨D, M, Z⟩ : Config N m) = some ⟨D, M ∪ l.toFinset, Z⟩ := by
  intro l
  induction l with
  | nil => intro D M Z _ _ _ _; simp [runJoins]
  | cons s l ih =>
    intro D M Z hs hm hz hn
    have hjoin : join s (⟨D, M, Z⟩ : Config N m) = some ⟨D, insert s M, Z⟩ := by
      have hg : s ∈ (⟨D, M, Z⟩ : Config N m).Sl ∧ s ∉ (⟨D, M, Z⟩ : Config N m).μ ∧
          s ∉ (⟨D, M, Z⟩ : Config N m).ζ :=
        ⟨hs s (by simp), hm s (by simp), hz s (by simp)⟩
      unfold join
      rw [if_pos hg]
    have hnc := List.nodup_cons.mp hn
    have hM : ∀ t ∈ l, t ∉ insert s M := by
      intro t ht hmem
      rcases Finset.mem_insert.mp hmem with rfl | hmm
      · exact hnc.1 ht
      · exact hm t (by simp [ht]) hmm
    have hIH := ih D (insert s M) Z (fun t ht => hs t (by simp [ht])) hM
      (fun t ht => hz t (by simp [ht])) hnc.2
    simp only [runJoins, hjoin, Option.bind_some, hIH]
    have : insert s M ∪ l.toFinset = M ∪ (s :: l).toFinset := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons, List.mem_toFinset]
      tauto
    rw [this]

/-- The join block finds existing vacant enabled slots, since `x.μ ⊆ Sl(x)` and `ζ` is still
empty. -/
theorem runJoins_all (x : Config N m) (hx : x.WF) (lμ : List (Word N)) (h : Enumerates x.μ lμ) :
    runJoins lμ (⟨x.D, ∅, ∅⟩ : Config N m) = some ⟨x.D, x.μ, ∅⟩ := by
  have hsl : ∀ s ∈ lμ, s ∈ x.D.biUnion cellW := by
    intro s hs
    exact hx.2.2.2.1 ((h.2 s).mp hs)
  have hIH := aux_runJoins (m := m) lμ x.D ∅ ∅ hsl (by simp) (by simp) h.1
  rw [hIH]
  have hset : (∅ : Finset (Word N)) ∪ lμ.toFinset = x.μ := by
    ext w
    simp only [Finset.empty_union, List.mem_toFinset]
    exact h.2 w
  rw [hset]

private theorem aux_runDisables : ∀ (l : List (Word N)) (D M Z : Finset (Word N)),
    (∀ s ∈ l, s ∈ D.biUnion cellW) → (∀ s ∈ l, s ∉ M) → (∀ s ∈ l, s ∉ D) → (∀ s ∈ l, s ∉ Z) →
      l.Nodup → runDisables l (⟨D, M, Z⟩ : Config N m) = some ⟨D, M, Z ∪ l.toFinset⟩ := by
  intro l
  induction l with
  | nil => intro D M Z _ _ _ _ _; simp [runDisables]
  | cons s l ih =>
    intro D M Z hs hm hd hz hn
    have hdis : disable s (⟨D, M, Z⟩ : Config N m) = some ⟨D, M, insert s Z⟩ := by
      have hg : s ∈ (⟨D, M, Z⟩ : Config N m).Sl ∧ s ∉ (⟨D, M, Z⟩ : Config N m).μ ∧
          s ∉ (⟨D, M, Z⟩ : Config N m).D ∧ s ∉ (⟨D, M, Z⟩ : Config N m).ζ :=
        ⟨hs s (by simp), hm s (by simp), hd s (by simp), hz s (by simp)⟩
      unfold disable
      rw [if_pos hg]
    have hnc := List.nodup_cons.mp hn
    have hZ : ∀ t ∈ l, t ∉ insert s Z := by
      intro t ht hmem
      rcases Finset.mem_insert.mp hmem with rfl | hmm
      · exact hnc.1 ht
      · exact hz t (by simp [ht]) hmm
    have hIH := ih D M (insert s Z) (fun t ht => hs t (by simp [ht]))
      (fun t ht => hm t (by simp [ht])) (fun t ht => hd t (by simp [ht])) hZ hnc.2
    simp only [runDisables, hdis, Option.bind_some, hIH]
    have : insert s Z ∪ l.toFinset = Z ∪ (s :: l).toFinset := by
      ext w
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons, List.mem_toFinset]
      tauto
    rw [this]

/-- The disable block finds existing vacant childless enabled slots, by the target's invariant
`Disjoint ζ (μ ∪ D)`. -/
theorem runDisables_all (x : Config N m) (hx : x.WF) (lζ : List (Word N)) (h : Enumerates x.ζ lζ) :
    runDisables lζ (⟨x.D, x.μ, ∅⟩ : Config N m) = some x := by
  have hz : ∀ s ∈ lζ, s ∈ x.ζ := fun s hs => (h.2 s).mp hs
  have hsl : ∀ s ∈ lζ, s ∈ x.D.biUnion cellW := fun s hs => hx.2.2.2.2.1 (hz s hs)
  have hdisj := hx.2.2.2.2.2
  have hm : ∀ s ∈ lζ, s ∉ x.μ := by
    intro s hs hmem
    exact Finset.disjoint_left.mp hdisj (hz s hs) (Finset.mem_union_left _ hmem)
  have hd : ∀ s ∈ lζ, s ∉ x.D := by
    intro s hs hmem
    exact Finset.disjoint_left.mp hdisj (hz s hs) (Finset.mem_union_right _ hmem)
  have hIH := aux_runDisables (m := m) lζ x.D x.μ ∅ hsl hm hd (by simp) h.1
  rw [hIH]
  have hset : (∅ : Finset (Word N)) ∪ lζ.toFinset = x.ζ := by
    ext w
    simp only [Finset.empty_union, List.mem_toFinset]
    exact h.2 w
  rw [hset]

/-- **Proposition prop:canon-word (1), forward half.** The canonical word carries the seed to `x`. -/
theorem canonical_eq (x : Config N m) (hx : x.WF) (lD lμ lζ : List (Word N))
    (hD : SpawnOrder x lD) (hμ : Enumerates x.μ lμ) (hζ : Enumerates x.ζ lζ) :
    canonical N m lD lμ lζ = some x := by
  unfold canonical
  rw [runSpawns_all x hx lD hD]
  simp only [Option.bind_some]
  rw [runJoins_all x hx lμ hμ]
  simp only [Option.bind_some]
  exact runDisables_all x hx lζ hζ

/-- The same, read as a word of generators. -/
theorem runWord_canonWord (x : Config N m) (hx : x.WF) (lD lμ lζ : List (Word N))
    (hD : SpawnOrder x lD) (hμ : Enumerates x.μ lμ) (hζ : Enumerates x.ζ lζ) :
    runWord (canonWord lD lμ lζ) (seed N m) = some x := by
  rw [← canonical_eq_runWord]
  exact canonical_eq x hx lD lμ lζ hD hμ hζ

/-- **Proposition prop:canon-word (1), as the paper states it.** Every configuration is reachable
from the seed *by a canonical word*: some triple of block enumerations satisfies the ordering
hypotheses and carries the seed to `x`. This is the sentence "every configuration is reachable from
the seed configuration by the canonical word"; `reachable_seed_of_wf` below forgets which word. -/
theorem exists_canonWord_run (x : Config N m) (hx : x.WF) :
    ∃ lD lμ lζ : List (Word N), SpawnOrder x lD ∧ Enumerates x.μ lμ ∧ Enumerates x.ζ lζ ∧
      runWord (canonWord lD lμ lζ) (seed N m) = some x := by
  obtain ⟨lD, hD⟩ := exists_spawnOrder x hx
  obtain ⟨lμ, hμ⟩ := exists_enumerates x.μ
  obtain ⟨lζ, hζ⟩ := exists_enumerates x.ζ
  exact ⟨lD, lμ, lζ, hD, hμ, hζ, runWord_canonWord x hx lD lμ lζ hD hμ hζ⟩

/-- Every configuration is reachable from the seed (the canonical word forgotten). -/
theorem reachable_seed_of_wf (x : Config N m) (hx : x.WF) : Reachable (seed N m) x := by
  obtain ⟨lD, lμ, lζ, -, -, -, hrun⟩ := exists_canonWord_run x hx
  exact ⟨canonWord lD lμ lζ, hrun⟩

/-! ## Item 1, converse half: reachable states are configurations -/

/-- Every generator preserves well-formedness (assembled from the `wf_*` lemmas of
`Hsfnlean.Calculus`). -/
theorem wf_runGen {x y : Config N m} {g : Letter N} (hx : x.WF) (h : runGen g x = some y) : y.WF := by
  cases g with
  | spawn a => exact wf_spawn hx h
  | retract a => exact wf_retract hx h
  | join s => exact wf_join hx h
  | leave s => exact wf_leave hx h
  | disable s => exact wf_disable hx h
  | enable s => exact wf_enable hx h
  | graft a b => exact wf_graft hx h

/-- **Proposition prop:canon-word (1), closure.** Folding any word of generators from a well-formed
state yields a well-formed state. -/
theorem wf_runWord {x y : Config N m} {w : List (Letter N)} (hx : x.WF) (h : runWord w x = some y) :
    y.WF := by
  induction w generalizing x with
  | nil =>
    simp only [runWord, Option.some.injEq] at h
    exact h ▸ hx
  | cons g w ih =>
    rw [runWord] at h
    cases hg : runGen g x with
    | none => rw [hg] at h; simp at h
    | some z =>
      rw [hg] at h
      simp only [Option.bind_some] at h
      exact ih (wf_runGen hx hg) h

/-- Reachability from a configuration lands in configurations. -/
theorem reachable_wf {x y : Config N m} (hx : x.WF) (h : Reachable x y) : y.WF := by
  obtain ⟨w, hw⟩ := h
  exact wf_runWord hx hw

/-- Every state reachable from the seed is a configuration. -/
theorem reachable_seed_wf (hm : 1 ≤ m) {y : Config N m} (h : Reachable (seed N m) y) : y.WF :=
  reachable_wf (seed_wf hm) h

/-! ## The state space is exactly the configuration space -/

/-- **Proposition prop:canon-word (1).** The states reachable from the seed are exactly the
well-formed configurations. -/
theorem reachable_seed_iff (hm : 1 ≤ m) (y : Config N m) : Reachable (seed N m) y ↔ y.WF :=
  ⟨reachable_seed_wf hm, reachable_seed_of_wf y⟩

/-- `w_can` is a normal form for states: the canonical word determines the configuration it
produces, so two configurations with a common canonical word coincide. -/
theorem canonWord_normal_form {x y : Config N m} (hx : x.WF) (hy : y.WF)
    (lD lμ lζ lD' lμ' lζ' : List (Word N))
    (hxD : SpawnOrder x lD) (hxμ : Enumerates x.μ lμ) (hxζ : Enumerates x.ζ lζ)
    (hyD : SpawnOrder y lD') (hyμ : Enumerates y.μ lμ') (hyζ : Enumerates y.ζ lζ')
    (he : canonWord lD lμ lζ = canonWord lD' lμ' lζ') : x = y := by
  have h1 := runWord_canonWord x hx lD lμ lζ hxD hxμ hxζ
  have h2 := runWord_canonWord y hy lD' lμ' lζ' hyD hyμ hyζ
  rw [he, h2] at h1
  exact (Option.some.inj h1).symm

/-- The letterwise inverse of a generator (Theorem `thm:rep-tree`(i)). -/
private def aux_invGen : Letter N → Letter N
  | .spawn a => .retract a
  | .retract a => .spawn a
  | .join s => .leave s
  | .leave s => .join s
  | .disable s => .enable s
  | .enable s => .disable s
  | .graft a b => .graft b a

/-- The inverse word: invert each letter and reverse the order. -/
private def aux_invWord (w : List (Letter N)) : List (Letter N) := (w.map aux_invGen).reverse

private theorem aux_runGen_inv {x y : Config N m} {g : Letter N} (hx : x.WF)
    (h : runGen g x = some y) : runGen (aux_invGen g) y = some x := by
  cases g with
  | spawn a => exact retract_spawn hx h
  | retract a => exact spawn_retract hx h
  | join s => exact leave_join h
  | leave s => exact join_leave hx h
  | disable s => exact enable_disable h
  | enable s => exact disable_enable hx h
  | graft a b => exact graft_graft hx h

private theorem aux_runWord_inv : ∀ (w : List (Letter N)) {x y : Config N m}, x.WF →
    runWord w x = some y → runWord (aux_invWord w) y = some x := by
  intro w
  induction w with
  | nil =>
    intro x y hx h
    simp only [runWord, Option.some.injEq] at h
    subst h
    simp [aux_invWord, runWord]
  | cons g w ih =>
    intro x y hx h
    rw [runWord] at h
    cases hg : runGen g x with
    | none => rw [hg] at h; simp at h
    | some z =>
      rw [hg] at h
      simp only [Option.bind_some] at h
      have hz : z.WF := wf_runGen hx hg
      have hrec := ih hz h
      have hsplit : aux_invWord (g :: w) = aux_invWord w ++ [aux_invGen g] := by
        simp [aux_invWord]
      rw [hsplit, runWord_append, hrec]
      simp only [Option.bind_some, runWord, aux_runGen_inv hx hg]

/-- Any configuration can be carried to any other, the (`Reach`) ingredient quoted from
`prop:canon-word` in the proof of the lifting theorem: run the inverse of the source's canonical
word back to the seed, then the target's canonical word forward. Stated here as bare reachability
between configurations. -/
theorem reachable_of_wf {x y : Config N m} (hx : x.WF) (hy : y.WF) :
    Reachable x y := by
  have hm : 1 ≤ m := by
    have h := hx.2.1 [] hx.1
    simpa using h
  obtain ⟨lD, lμ, lζ, -, -, -, hrun⟩ := exists_canonWord_run x hx
  obtain ⟨w₂, hw₂⟩ := reachable_seed_of_wf y hy
  refine ⟨aux_invWord (canonWord lD lμ lζ) ++ w₂, ?_⟩
  rw [runWord_append, aux_runWord_inv _ (seed_wf hm) hrun]
  simpa using hw₂

end Calc

end HSFN
