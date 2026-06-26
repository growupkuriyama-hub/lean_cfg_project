# Lean formalization companion for the fixed-observation MCFG paper

This note documents the current Lean companion for the paper

> **Fixed-Monoid Tuple Substitution for Positive-Data Learning of Multiple Context-Free Grammars**

The purpose of the Lean development at this stage is deliberately limited: it formalizes the **fixed finite-monoid observation layer** used in the paper, including tuple types, abstract tuple distributions, the semantic fixed-observation substitutability condition, refinement of observations, and the monotonicity theorem under refinement. It does **not** yet formalize the full MCFG reconstruction theorem.

The current checked file is:

```text
LeanCfgProject/MCFG/FI_v2_1_FixedObservation.lean
```

The file was checked by GitHub Actions Lean CI at commit

```text
b0d10d1
```

as reported by `Lean CI #369` in the repository `growupkuriyama-hub/lean_cfg_project`.

---

## 1. Repository layout

The current MCFG formalization layer is organized as follows.

```text
LeanCfgProject.lean
LeanCfgProject/MCFG/Basic.lean
LeanCfgProject/MCFG/FI_v2_1_FixedObservation.lean
.github/workflows/lean.yml
```

The intended import chain is:

```lean
-- LeanCfgProject.lean
import LeanCfgProject.MCFG.Basic
```

```lean
-- LeanCfgProject/MCFG/Basic.lean
import LeanCfgProject.MCFG.FI_v2_1_FixedObservation
```

The CI workflow builds the MCFG fixed-observation module and then the project root through Lake. A typical local check is:

```bash
lake build LeanCfgProject.MCFG.FI_v2_1_FixedObservation
lake build LeanCfgProject.MCFG.Basic
lake build LeanCfgProject
```

The GitHub CI run used Lean 4 through Lake/mathlib. In the observed CI log, the Lean toolchain was `leanprover/lean4:v4.31.0-rc1`.

---

## 2. Scope of the current formalization

The current file formalizes the preliminary observation-theoretic part of the paper. In paper terminology, it corresponds mainly to the fixed observation morphism, componentwise tuple typing, tuple distributions, fixed-`h` tuple substitutability, and monotonicity under refinement of the observation morphism.

The current formalization is intentionally abstract in two places.

First, contexts are not yet represented as concrete named sentence contexts with permutations. Instead, the file assumes an arity-indexed context type family

```lean
Ctx : Nat → Type
```

and an abstract filling operation

```lean
fill : ∀ d : Nat, Ctx d → Tuple α d → Word α
```

This makes it possible to state and prove the fixed-observation substitutability layer independently of the eventual concrete representation of named holes.

Second, refinement of observations is represented by an explicit Lean structure rather than by mathlib's bundled monoid homomorphism notation. This was chosen to keep the first CI experiment robust.

```lean
structure Refines (obs : α → M) (obs' : α → M') where
  map : M' → M
  map_one : map 1 = 1
  map_mul : ∀ x y : M', map (x * y) = map x * map y
  comm : ∀ a : α, map (obs' a) = obs a
```

Mathematically, this is the same data as a monoid homomorphism from the finer observation monoid to the coarser one, commuting with the two letter observations.

---

## 3. Formalized definitions

### 3.1 Words and tuples

Words over an alphabet are represented by lists.

```lean
abbrev Word (α : Type u) := List α
```

A tuple of arity `d` is a `Fin d`-indexed family of words.

```lean
abbrev Tuple (α : Type u) (d : Nat) := Fin d → Word α
```

This matches the paper's convention that an MCFG nonterminal of fan-out `d` derives a `d`-tuple of strings.

### 3.2 Letter observations and word observations

A letter observation is a function

```lean
obs : α → M
```

where `M` is a monoid. It is extended multiplicatively to words by:

```lean
def evalObs (obs : α → M) : Word α → M
  | [] => 1
  | a :: w => obs a * evalObs obs w
```

The file proves the basic append law:

```lean
theorem evalObs_append (obs : α → M) (u v : Word α) :
    evalObs obs (u ++ v) = evalObs obs u * evalObs obs v
```

This is the Lean counterpart of extending a finite observation morphism
`h : Σ* → M` from letters to words.

### 3.3 Componentwise tuple type

The componentwise observation type of a tuple is formalized as:

```lean
def tupleType {d : Nat} (obs : α → M) (x : Tuple α d) : Fin d → M :=
  fun i => evalObs obs (x i)
```

This corresponds to the paper's notation

```text
h^{(d)}(w_1, ..., w_d) = (h(w_1), ..., h(w_d)).
```

### 3.4 Tuple distributions and shared contexts

Given an abstract filling operation, the distribution of a tuple is the set of contexts that accept it.

```lean
def Distribution {d : Nat} (L : Set (Word α)) (x : Tuple α d) : Set (Ctx d) :=
  { c | fill d c x ∈ L }
```

Two tuples share an accepting context if there exists a context that accepts both.

```lean
def SharesContext {d : Nat} (L : Set (Word α)) (x y : Tuple α d) : Prop :=
  ∃ c : Ctx d, fill d c x ∈ L ∧ fill d c y ∈ L
```

This is the abstract Lean version of the paper's shared sentence-context condition.

### 3.5 Fixed-observation tuple substitutability

The semantic fixed-observation substitutability condition is formalized as:

```lean
def FixedTupleSubstitutable (f : Nat) (obs : α → M) (L : Set (Word α)) : Prop :=
  ∀ {d : Nat}, d ≤ f → 0 < d →
    ∀ x y : Tuple α d,
      tupleType obs x = tupleType obs y →
      SharesContext fill L x y →
      Distribution fill L x = Distribution fill L y
```

This directly mirrors the paper's condition:

> equality of componentwise fixed observation type plus one shared accepting sentence context implies equality of all accepting sentence contexts.

The Lean statement is parameterized by an arbitrary context family and filling operation; concrete named sentence contexts will be introduced in a later layer.

---

## 4. Formalized theorems

### 4.1 Multiplicativity of observation evaluation

The file proves that the extended observation of a concatenation is the product of the observations.

```lean
theorem evalObs_append (obs : α → M) (u v : Word α) :
    evalObs obs (u ++ v) = evalObs obs u * evalObs obs v
```

This is a basic algebraic lemma used to justify reading `evalObs` as a monoid morphism from the free monoid of words.

### 4.2 Compatibility of word observations with refinement

Given a refinement map from a finer observation to a coarser one, evaluation commutes with refinement.

```lean
theorem evalObs_refines (r : Refines obs obs') (w : Word α) :
    r.map (evalObs obs' w) = evalObs obs w
```

This says that evaluating a word in the finer observation and then projecting to the coarser monoid is the same as evaluating the word directly in the coarser observation.

### 4.3 Compatibility of tuple types with refinement

The pointwise form is:

```lean
theorem tupleType_refines_apply {d : Nat} (r : Refines obs obs')
    (x : Tuple α d) (i : Fin d) :
    r.map (tupleType obs' x i) = tupleType obs x i
```

The componentwise functional form is:

```lean
theorem tupleType_refines {d : Nat} (r : Refines obs obs') (x : Tuple α d) :
    (fun i : Fin d => r.map (tupleType obs' x i)) = tupleType obs x
```

These lemmas provide the Lean bridge from finer tuple equality to coarser tuple equality.

### 4.4 Monotonicity under refinement

The main theorem currently formalized is:

```lean
theorem fixedTupleSubstitutable_of_refines
    {f : Nat} {L : Set (Word α)}
    (r : Refines obs obs')
    (hL : FixedTupleSubstitutable fill f obs L) :
    FixedTupleSubstitutable fill f obs' L
```

This is the Lean version of the paper's monotonicity proposition:

> If the observation morphism `h'` refines `h`, then every `(f,h)`-tuple-substitutable language is also `(f,h')`-tuple-substitutable.

Mathematically, the reason is simple. If two tuples have the same finer type, then after applying the refinement map componentwise they have the same coarser type. Therefore the coarser substitutability hypothesis applies.

This theorem is one of the safest early targets for machine checking because it is central to the observation-parameter story but does not require formalizing MCFG derivation trees.

### 4.5 Characteristic sample skeleton

The file also contains a small abstract skeleton for the positive-data learning argument.

A hypothesis interpretation is represented as:

```lean
abbrev HypLanguage (α : Type u) (Hyp : Type v) := Hyp → Set (Word α)
```

A characteristic sample is represented as:

```lean
def CharacteristicSample
    [DecidableEq α]
    (lang : HypLanguage α Hyp)
    (learner : Finset (Word α) → Hyp)
    (S : Finset (Word α))
    (L : Set (Word α)) : Prop :=
  (S : Set (Word α)) ⊆ L ∧
  ∀ K : Finset (Word α),
    (S : Set (Word α)) ⊆ (K : Set (Word α)) →
    (K : Set (Word α)) ⊆ L →
    lang (learner K) = L
```

The file proves the immediate correctness lemma:

```lean
theorem characteristicSample_correct
    [DecidableEq α]
    (lang : HypLanguage α Hyp)
    (learner : Finset (Word α) → Hyp)
    {S K : Finset (Word α)} {L : Set (Word α)}
    (hS : CharacteristicSample lang learner S L)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKL : (K : Set (Word α)) ⊆ L) :
    lang (learner K) = L
```

This does not yet formalize texts, computability, or Gold identification. It records the finite-sample implication used by the paper's characteristic-sample argument.

---

## 5. Sandbox fan-out-one context layer

The file includes a small sandbox for ordinary one-hole string contexts.

```lean
abbrev TwoSidedContext (α : Type u) := Word α × Word α
```

The filling operation is:

```lean
def fillOne (c : TwoSidedContext α) (x : Tuple α 1) : Word α :=
  c.1 ++ x finOne ++ c.2
```

This is not the final MCFG context representation. It is included only as a check that the abstract context interface can specialize to the ordinary fan-out-one, two-sided context case.

---

## 6. Correspondence with the paper

The following table summarizes the current correspondence between paper notions and Lean declarations.

| Paper notion | Lean declaration | Status |
|---|---|---|
| alphabet `Σ` | type variable `α` | formalized abstractly |
| word over `Σ` | `Word α := List α` | formalized |
| tuple of arity `d` | `Tuple α d := Fin d → Word α` | formalized |
| letter observation | `obs : α → M` | formalized |
| extension to words | `evalObs obs` | formalized |
| componentwise tuple type | `tupleType obs x` | formalized |
| arity-indexed sentence contexts | `Ctx : Nat → Type` | abstracted |
| context filling | `fill : ∀ d, Ctx d → Tuple α d → Word α` | abstracted |
| tuple distribution `D_L(x)` | `Distribution fill L x` | formalized abstractly |
| shared accepting context | `SharesContext fill L x y` | formalized abstractly |
| `(f,h)`-tuple substitutability | `FixedTupleSubstitutable fill f obs L` | formalized abstractly |
| refinement `h ≼ h'` | `Refines obs obs'` | formalized |
| monotonicity under refinement | `fixedTupleSubstitutable_of_refines` | proved |
| characteristic sample condition | `CharacteristicSample` | formalized abstractly |
| finite-sample correctness from characteristic sample | `characteristicSample_correct` | proved |

---

## 7. What is not formalized yet

The current Lean development should not be described as a formalization of the full paper. The following parts are not yet formalized.

1. **Concrete named sentence contexts.**
   The paper's contexts have named holes, possible component permutation, and intervening terminal material. The current Lean file keeps contexts abstract through `Ctx` and `fill`.

2. **MCFG syntax and derivation semantics.**
   The current file does not yet define working binary linear nondeleting MCFGs, rules, derivation trees, tuple languages of nonterminals, or start-separated presentations.

3. **Output-type refinement of grammars.**
   The paper's construction that refines nonterminals by componentwise output type is not yet formalized.

4. **Canonical learner grammar.**
   The current file does not yet construct the canonical grammar from a finite positive sample.

5. **Exact reconstruction theorem.**
   The main reconstruction theorem of the paper is not yet formalized.

6. **Existence of presentation-relative characteristic samples.**
   The file contains an abstract characteristic-sample predicate and its immediate consequence, but not the proof that the paper's characteristic sample exists.

7. **Gold-style identification from texts.**
   Infinite texts, computability of the learner, and eventual stabilization are not yet encoded.

8. **No-advice non-identifiability.**
   The superfinite chain argument for the union over all observations is not yet formalized.

9. **Polynomial-time and polynomial-data statements.**
   Complexity bounds, sample-size bounds, and fixed-parameter polynomiality are not yet formalized.

10. **Compression lower bound and bounded spine width.**
    The singleton compression example, bounded-spine definitions, and polynomial-data recovery theorem are not yet formalized.

11. **Yoshinaka comparison and examples.**
    The ordered-context comparison, parallel-agreement examples, cross-serial examples, and finite-kernel comparison are not yet formalized.

12. **Finiteness and explicitness of the monoid.**
    The current monotonicity theorem does not require `M` to be finite, so the Lean file assumes only `[Monoid M]`. The paper's finite and explicit monoid assumptions are mathematically important for learning and computation, but they are not needed for the currently formalized refinement theorem.

---

## 8. Suggested wording for the paper

A safe way to refer to the current Lean development in the paper is the following.

```latex
A Lean companion formalizes the fixed-observation layer used in the paper:
words as lists, arity-indexed tuples, componentwise observation types,
abstract tuple distributions, fixed-observation tuple substitutability,
refinement of observations, and the monotonicity theorem under refinement.
The formalization is intentionally preliminary: the full MCFG reconstruction
argument, the canonical learner, the no-advice boundary, and the bounded-spine
polynomial-data theorem are not yet machine-checked.
```

A slightly shorter version suitable for a footnote is:

```latex
A preliminary Lean companion checks the fixed-observation layer, including the
monotonicity of $(f,h)$-tuple substitutability under refinement of the finite
observation morphism.  The full MCFG reconstruction theorem is not yet
machine-checked.
```

This wording is intentionally conservative. It avoids suggesting that the full paper is already formalized.

---

## 9. Suggested next formalization milestones

A natural next sequence is:

1. Define concrete named sentence contexts.
2. Prove that ordinary two-sided contexts are the arity-one special case.
3. Define MCFG templates and simultaneous substitution.
4. Define working binary linear nondeleting MCFG presentations.
5. Define derivation trees and tuple languages of nonterminals.
6. Formalize output-type refinement of a grammar.
7. Formalize sample occurrences and extracted rules.
8. Prove sample consistency: every positive sample word is generated by the canonical hypothesis.
9. Prove the hybrid filling lemma used in exact reconstruction.
10. Prove the exact reconstruction theorem under the semantic fixed-observation substitutability promise.

For FI submission purposes, the most valuable next milestone is not the no-advice theorem or complexity theory, but the core MCFG bookkeeping: named holes, tuple filling, template substitution, and the hybrid filling lemma. Those are exactly the places where machine checking reduces the risk of hidden indexing or permutation errors.

---

## 10. Current formalization status summary

Current status:

```text
Checked by CI: yes, at commit b0d10d1 as reported by Lean CI #369
Current main file: LeanCfgProject/MCFG/FI_v2_1_FixedObservation.lean
Main checked theorem: fixedTupleSubstitutable_of_refines
Scope: fixed-observation layer only
Full MCFG reconstruction theorem checked: no
```

In one sentence:

> The current Lean development machine-checks the fixed-observation substrate of the paper, especially refinement monotonicity, and provides a stable starting point for later formalization of named sentence contexts and the MCFG reconstruction argument.
