# Lean formalization companion for the fixed-observation MCFG paper

This note documents the current Lean companion for the paper

> **Fixed-Monoid Tuple Substitution for Positive-Data Learning of Multiple Context-Free Grammars**

The Lean development is a companion formalization of the paper's core
bookkeeping layers around fixed finite observations, named sentence contexts,
tuple distributions, positive samples, unit-rule closure, and a
distribution-level reconstruction/stabilization skeleton.

It should be read with the following scope in mind.

- The current development **does formalize** the fixed-observation substrate,
  named sentence contexts, a working MCFG syntax layer, a first derivation
  semantics layer, sample-safe context transport, learner unit closure,
  distribution-level reconstruction certificates, and a Gold-style stabilization
  wrapper.
- The current development **does not yet formalize** the full
  presentation-relative characteristic-sample construction, the full canonical
  MCFG learner grammar, the hybrid filling lemma in its final paper form, the
  no-advice non-identifiability theorem, or the bounded-spine polynomial-data
  theorem.

The latest checked CI status is:

```text
Lean CI #377
commit: 591118a
repository: growupkuriyama-hub/lean_cfg_project
status: succeeded
```

The top formalization layer at that point is:

```text
LeanCfgProject/MCFG/FI_v2_1_GoldStabilization.lean
```

The aggregate MCFG import file is:

```text
LeanCfgProject/MCFG/Basic.lean
```

---

## 1. Repository layout

The current MCFG formalization is organized as a sequence of small layers.

```text
LeanCfgProject.lean
LeanCfgProject/MCFG/Basic.lean

LeanCfgProject/MCFG/FI_v2_1_FixedObservation.lean
LeanCfgProject/MCFG/FI_v2_1_NamedSentenceContext.lean
LeanCfgProject/MCFG/FI_v2_1_MCFG_Syntax.lean
LeanCfgProject/MCFG/FI_v2_1_MCFG_Derivation.lean
LeanCfgProject/MCFG/FI_v2_1_MCFG_ContextualSemantics.lean
LeanCfgProject/MCFG/FI_v2_1_LearnerUnitClosure.lean
LeanCfgProject/MCFG/FI_v2_1_LearnerDistribution.lean
LeanCfgProject/MCFG/FI_v2_1_ReconstructionCertificate.lean
LeanCfgProject/MCFG/FI_v2_1_GoldStabilization.lean

.github/workflows/lean.yml
```

The intended root import chain is:

```lean
-- LeanCfgProject.lean
import LeanCfgProject.MCFG.Basic
```

```lean
-- LeanCfgProject/MCFG/Basic.lean
import LeanCfgProject.MCFG.FI_v2_1_FixedObservation
import LeanCfgProject.MCFG.FI_v2_1_NamedSentenceContext
import LeanCfgProject.MCFG.FI_v2_1_MCFG_Syntax
import LeanCfgProject.MCFG.FI_v2_1_MCFG_Derivation
import LeanCfgProject.MCFG.FI_v2_1_MCFG_ContextualSemantics
import LeanCfgProject.MCFG.FI_v2_1_LearnerUnitClosure
import LeanCfgProject.MCFG.FI_v2_1_LearnerDistribution
import LeanCfgProject.MCFG.FI_v2_1_ReconstructionCertificate
import LeanCfgProject.MCFG.FI_v2_1_GoldStabilization
```

A typical local check is:

```bash
lake build LeanCfgProject.MCFG.FI_v2_1_GoldStabilization
lake build LeanCfgProject.MCFG.Basic
lake build LeanCfgProject
```

The GitHub Actions workflow checks the Lean files through Lake. The latest
successful run reported the Lean CI success at commit `591118a`.

---

## 2. Layer-by-layer status

The formalization is deliberately organized so that each layer can be understood
without committing to the whole reconstruction theorem at once.

| Layer | File | Main role | Status |
|---|---|---|---|
| 1 | `FI_v2_1_FixedObservation.lean` | Words, tuples, observation evaluation, fixed-`h` substitutability, refinement monotonicity | checked |
| 2 | `FI_v2_1_NamedSentenceContext.lean` | Concrete named sentence contexts and named filling | checked |
| 3 | `FI_v2_1_MCFG_Syntax.lean` | Working binary MCFG syntax: templates, rules, fan-out, nondeleting side conditions | checked |
| 4 | `FI_v2_1_MCFG_Derivation.lean` | First derivation semantics: tuple and string languages | checked |
| 5 | `FI_v2_1_MCFG_ContextualSemantics.lean` | Exposed tuples, grammar named distributions, sample-safe merge soundness | checked |
| 6 | `FI_v2_1_LearnerUnitClosure.lean` | Learner unit edges, unit reachability, soundness of unit-rule closure | checked |
| 7 | `FI_v2_1_LearnerDistribution.lean` | Transported contexts and learner approximate distributions | checked |
| 8 | `FI_v2_1_ReconstructionCertificate.lean` | Distribution-level reconstruction certificates and characteristic-sample skeleton | checked |
| 9 | `FI_v2_1_GoldStabilization.lean` | Texts, prefix samples, eventual containment, Gold-style stabilization | checked |

This is not yet a full formal proof of the paper's main theorem, but it now
covers a substantial part of the formal infrastructure around the main theorem.

---

## 3. What is currently formalized

### 3.1 Words and tuples

Words over an alphabet are represented by lists.

```lean
abbrev Word (α : Type u) := List α
```

A tuple of arity `d` is a `Fin d`-indexed family of words.

```lean
abbrev Tuple (α : Type u) (d : Nat) := Fin d → Word α
```

This matches the paper's convention that an MCFG nonterminal of fan-out `d`
derives a `d`-tuple of strings.

---

### 3.2 Fixed observations and tuple types

A letter observation is represented as a function

```lean
obs : α → M
```

where `M` is a monoid. It is extended multiplicatively to words:

```lean
def evalObs (obs : α → M) : Word α → M
```

The file proves the append law:

```lean
theorem evalObs_append (obs : α → M) (u v : Word α) :
    evalObs obs (u ++ v) = evalObs obs u * evalObs obs v
```

The componentwise type of a tuple is:

```lean
def tupleType {d : Nat} (obs : α → M) (x : Tuple α d) : Fin d → M
```

This corresponds to the paper's notation

```text
h^{(d)}(w_1, ..., w_d) = (h(w_1), ..., h(w_d)).
```

---

### 3.3 Refinement of observations

The formalization uses an explicit refinement structure.

```lean
structure Refines (obs : α → M) (obs' : α → M') where
  map : M' → M
  map_one : map 1 = 1
  map_mul : ∀ x y : M', map (x * y) = map x * map y
  comm : ∀ a : α, map (obs' a) = obs a
```

Mathematically, this is the same data as a monoid homomorphism from the finer
observation monoid to the coarser one, commuting with the two letter
observations.

The key checked compatibility lemmas are:

```lean
theorem evalObs_refines (r : Refines obs obs') (w : Word α) :
    r.map (evalObs obs' w) = evalObs obs w
```

```lean
theorem tupleType_refines_apply {d : Nat} (r : Refines obs obs')
    (x : Tuple α d) (i : Fin d) :
    r.map (tupleType obs' x i) = tupleType obs x i
```

---

### 3.4 Fixed-observation tuple substitutability

The semantic fixed-observation substitutability condition is formalized first
for an abstract context interface and then specialized to named sentence
contexts.

At the abstract level, a context family and filling operation are parameters.

```lean
Ctx : Nat → Type
fill : ∀ d : Nat, Ctx d → Tuple α d → Word α
```

The distribution of a tuple is the set of contexts accepting it.

```lean
def Distribution {d : Nat} (L : Set (Word α)) (x : Tuple α d) : Set (Ctx d)
```

Two tuples share an accepting context if some context accepts both.

```lean
def SharesContext {d : Nat} (L : Set (Word α)) (x y : Tuple α d) : Prop
```

The fixed-observation substitutability predicate is:

```lean
def FixedTupleSubstitutable
    (f : Nat) (obs : α → M) (L : Set (Word α)) : Prop
```

It formalizes the paper's implication:

> same componentwise observation type + one shared accepting context  
> implies equality of all accepting contexts.

The monotonicity theorem under refinement is checked:

```lean
theorem fixedTupleSubstitutable_of_refines
    {f : Nat} {L : Set (Word α)}
    (r : Refines obs obs')
    (hL : FixedTupleSubstitutable fill f obs L) :
    FixedTupleSubstitutable fill f obs' L
```

This corresponds to the paper's refinement monotonicity proposition.

---

### 3.5 Named sentence contexts

The second layer introduces concrete named sentence contexts.

The formalization distinguishes raw contexts from well-formed named contexts.
This makes the representation extensible and avoids making later MCFG
bookkeeping depend on a brittle concrete encoding too early.

Main declarations include:

```lean
RawNamedSentenceContext
RawNamedSentenceContext.WellFormed
NamedSentenceContext
rawNamedFill
namedFill
NamedDistribution
NamedSharesContext
FixedNamedTupleSubstitutable
fixedNamedTupleSubstitutable_of_refines
```

This is the Lean counterpart of the paper's arity-`d` sentence contexts with
named holes. The layer is meant to support contexts where tuple components may
be exposed in non-left-to-right order.

---

### 3.6 MCFG syntax

The syntax layer introduces a working binary linear MCFG presentation skeleton.

Main declarations include:

```lean
TemplateAtom
TemplateWord
evalTemplateAtom
evalTemplateWord
TemplateTuple
evalTemplateTuple
TemplateTuple.Nondeleting
StartRule
TerminalRule
BinaryRule
BinaryRule.apply
WorkingMCFG
WorkingMCFG.FanoutAtMost
WorkingMCFG.BasicWorkingConditions
```

This corresponds to the paper's definition of working binary linear nondeleting
MCFG rules. The goal of this layer is to make the template and rule
bookkeeping explicit before proving reconstruction statements.

---

### 3.7 Derivation semantics

The derivation layer introduces a first semantics for tuple derivability and
string languages.

Main declarations include:

```lean
castTuple
singletonTuple
StartRule.WellTyped
WorkingMCFG.StartRulesWellTyped
WorkingMCFG.SemanticWorkingConditions
DerivesTuple
TupleLanguage
StringLanguage
```

This is not yet a full derivation-tree development with occurrence tracking,
but it gives a checked inductive semantics for generated tuple languages and
the start string language.

---

### 3.8 Contextual semantics and sample-safe merge

The contextual-semantics layer connects derivations with named sentence
contexts and positive samples.

Main declarations include:

```lean
ExposedWithContext
GrammarNamedDistribution
GrammarNamedSharesContext
grammarNamedSharesContext_of_two_exposures
grammarNamedDistribution_eq_of_fixed_substitutable
grammarNamedDistribution_eq_of_two_exposures

PositiveSample
SampleNamedDistribution
SampleNamedSharesContext
ObservedInSampleWithContext
observedInSample_to_exposedWithContext

SampleSafeMerge
sampleSafeMerge_sound_for_grammar
sampleObservedExposures_sound_for_grammar
```

The most important checked idea here is:

> If two tuples are observed in a positive sample with the same fixed observation
> type and a shared sample context, then the fixed-substitutability promise makes
> the corresponding grammar-level named distributions equal.

This is the formalized core of the safety of the learner's unit-rule merging
step.

---

### 3.9 Learner unit-rule closure

The unit-closure layer formalizes the soundness of repeatedly applying
sample-safe unit edges.

Main declarations include:

```lean
PositiveForLanguage
sampleSafeMerge_sound_for_language

LearnerUnitEdge
LearnerUnitEdge.sound_for_language

LearnerUnitReach
LearnerUnitReach.sound_for_language
LearnerUnitReach.mem_namedDistribution_of_reachable
LearnerUnitReach.mem_namedDistribution_iff_of_reachable

LearnerUnitHypothesis
LearnerUnitHypothesis.reach_sound_for_language
```

The checked content is:

> Finite-sample safe unit edges preserve target named-context distributions, and
> this preservation remains true after taking the reflexive-transitive closure
> of those unit edges.

This is the distributional soundness half of the learner's unit-rule closure.

---

### 3.10 Learner transported distributions

The learner-distribution layer defines contexts licensed by observation and
unit transport.

Main declarations include:

```lean
LearnerLicensedContext
LearnerApproxDistribution
DistributionComplete

sampleSafeMerge_symm
LearnerUnitEdge.reverse
LearnerUnitReach.symm

learnerApproxDistribution_sound_for_language
learnerApproxDistribution_exact_of_complete

LearnerObservedNode
LearnerObservedNode.transported_context_sound_for_language
```

The key checked statement is:

> A context observed in the sample can be transported along safe unit reachability
> to another tuple without leaving the target distribution.

This is a formalized version of the context-transport step used in the
reconstruction proof.

---

### 3.11 Reconstruction certificates

The reconstruction-certificate layer abstracts the point where the paper's
presentation-relative characteristic sample enters.

Main declarations include:

```lean
DistributionReconstructionCertificate
LearnerDistributionExact
TargetContextsLicensed
TargetContextsTransportWitnessed
DistributionCharacteristicSample
DistributionCharacteristicSample.exact_after_extending
exact_for_grammar_after_characteristic_sample
```

This layer proves a distribution-level version of the characteristic-sample
argument:

> If a finite sample is rich enough to license all target contexts relevant to
> the tuples under consideration, then the learner's transported distribution
> equals the target distribution.

The important limitation is that this layer assumes the relevant reconstruction
certificate. It does not yet construct that certificate from an arbitrary
working MCFG presentation.

---

### 3.12 Gold-style stabilization

The latest layer formalizes the abstract Gold-style stabilization argument for
finite characteristic samples.

Main declarations include:

```lean
Text
TextFor
PrefixSample
prefixSample_positive
prefixSample_extends_mono
text_eventually_contains_finite_sample

DistributionIdentifiesInLimit
distributionCharacteristicSample_identifiesInLimit
eventually_licensed_iff_target_context

TextForGrammar
DistributionIdentifiesInLimitForGrammar
distributionCharacteristicSample_identifiesGrammarInLimit
eventually_licensed_iff_grammar_context
```

This layer proves the standard finite-characteristic-sample implication:

> If a finite characteristic sample exists, then along every text for the target
> language, some finite prefix eventually contains it, and all later prefix
> samples satisfy the corresponding reconstruction condition.

This is a distribution-level Gold identification wrapper. It is not yet the full
grammar-level exact reconstruction theorem, but it formalizes the final
stabilization step once the characteristic sample has been obtained.

---

## 4. Correspondence with the paper

The following table summarizes the current correspondence between paper notions
and Lean declarations.

| Paper notion | Lean declaration | Status |
|---|---|---|
| alphabet `Σ` | type variable `α` | formalized abstractly |
| word over `Σ` | `Word α := List α` | formalized |
| tuple of arity `d` | `Tuple α d := Fin d → Word α` | formalized |
| fixed observation on letters | `obs : α → M` | formalized |
| extension to words | `evalObs obs` | formalized |
| componentwise tuple type | `tupleType obs x` | formalized |
| refinement of observations | `Refines obs obs'` | formalized |
| monotonicity under refinement | `fixedTupleSubstitutable_of_refines` | proved |
| named sentence contexts | `NamedSentenceContext` | formalized |
| named context filling | `namedFill` | formalized |
| named tuple distribution | `NamedDistribution` | formalized |
| fixed named tuple substitutability | `FixedNamedTupleSubstitutable` | formalized |
| MCFG templates | `TemplateAtom`, `TemplateWord`, `TemplateTuple` | formalized |
| nondeleting templates | `TemplateTuple.Nondeleting` | formalized |
| start, terminal, binary rules | `StartRule`, `TerminalRule`, `BinaryRule` | formalized |
| working MCFG presentation skeleton | `WorkingMCFG` | formalized |
| tuple derivability | `DerivesTuple` | formalized |
| tuple and string languages | `TupleLanguage`, `StringLanguage` | formalized |
| exposed tuple with context | `ExposedWithContext` | formalized |
| sample-safe merge | `SampleSafeMerge` | formalized |
| unit-rule closure | `LearnerUnitReach` | formalized |
| learner transported distribution | `LearnerApproxDistribution` | formalized |
| reconstruction certificate | `DistributionReconstructionCertificate` | formalized abstractly |
| characteristic sample skeleton | `DistributionCharacteristicSample` | formalized abstractly |
| text and prefix sample | `Text`, `PrefixSample` | formalized |
| eventual containment of finite sample | `text_eventually_contains_finite_sample` | proved |
| distribution-level identification in the limit | `DistributionIdentifiesInLimit` | formalized |
| full canonical learner grammar | not yet formalized | pending |
| full exact reconstruction theorem | not yet formalized | pending |
| no-advice non-identifiability | not yet formalized | pending |
| bounded-spine polynomial-data theorem | not yet formalized | pending |

---

## 5. What is not formalized yet

The current Lean development should not be described as a complete
machine-checked proof of the paper. The following parts remain outside the
formalization.

1. **Construction of the presentation-relative characteristic sample.**  
   The current certificate layer assumes a distribution-level reconstruction
   certificate. It does not yet prove that the paper's finite characteristic
   sample can be extracted from every witnessing working MCFG presentation.

2. **The full canonical learner grammar.**  
   Unit-rule closure and transported distributions are formalized, but the full
   canonical hypothesis grammar, including all extracted binary rules and start
   rules, is not yet formalized.

3. **The hybrid filling lemma in final grammar form.**  
   The context-transport and distribution-level soundness statements are checked,
   but the full MCFG hybrid filling argument for arbitrary binary derivation
   contexts is not yet formalized.

4. **Output-type refinement of grammars.**  
   The monoid typing layer is formalized, but the grammar-level construction
   refining nonterminals by componentwise output type is still pending.

5. **Productivity, reachability, and reducedness closure.**  
   The current MCFG syntax and derivation semantics include basic working
   conditions, but not the full reducedness and closure infrastructure used in
   the paper.

6. **No-advice non-identifiability.**  
   The superfinite-chain argument for the union over all finite observations is
   not yet formalized.

7. **Polynomial-time and polynomial-data statements.**  
   Complexity bounds, enumeration bounds, characteristic-sample size bounds, and
   fixed-parameter polynomiality are not yet formalized.

8. **Compression lower bound and bounded spine width.**  
   The unary singleton compression example, bounded-spine-width definitions, and
   polynomial-data recovery theorem are not yet formalized.

9. **Yoshinaka comparison and examples.**  
   The ordered-context comparison, parallel-agreement examples, cross-serial
   examples, finite-kernel comparison, conservativity proposition, and slope
   counterexample are not yet formalized.

10. **Finiteness and explicitness of the monoid.**  
    Many currently checked lemmas require only `[Monoid M]`, not `[Fintype M]`.
    This is mathematically appropriate for those algebraic lemmas. The paper's
    finite and explicit monoid hypotheses are essential for learning and
    algorithmic construction, but not for the already checked refinement and
    distribution-preservation statements.

---

## 6. Suggested wording for the paper

A safe paragraph for the paper is:

```latex
A preliminary Lean companion formalizes the main bookkeeping substrate of the
paper: fixed observation morphisms, tuple types, named sentence contexts,
working MCFG syntax and a first derivation semantics, sample-safe distributional
merging, unit-rule closure, transported learner distributions, and a
distribution-level Gold stabilization wrapper.  The formalization is not yet a
machine-checked proof of the full reconstruction theorem: the construction of
the presentation-relative characteristic sample, the complete canonical learner
grammar, the no-advice boundary, and the bounded-spine polynomial-data theorem
remain outside the current Lean development.
```

A shorter footnote version is:

```latex
A preliminary Lean companion checks the fixed-observation and distributional
bookkeeping layers, including named sentence contexts, MCFG syntax and
derivation skeletons, safe unit-rule closure, transported learner
distributions, reconstruction certificates, and a Gold-style stabilization
wrapper.  The full presentation-relative reconstruction theorem is not yet
machine-checked.
```

An even shorter version for the introduction is:

```latex
A Lean companion is available for the core bookkeeping layers of the
construction; it currently reaches a distribution-level reconstruction and
Gold-style stabilization skeleton, but not the full canonical-grammar
reconstruction theorem.
```

These statements are intentionally conservative. They emphasize what is checked
without suggesting that the entire paper is already formalized.

---

## 7. Suggested next formalization milestones

The most valuable next milestones are:

1. **Output-type refinement of working MCFGs.**  
   Define the refinement of a nonterminal by componentwise observation type and
   prove that typed derivations preserve the intended tuple type.

2. **Occurrence witnesses in derivation trees.**  
   Strengthen `ExposedWithContext` into a derivation-tree occurrence notion
   connecting nonterminal occurrences to named sentence contexts.

3. **Extracted sample rules.**  
   Formalize how terminal, binary, start, and unit rules are extracted from a
   finite positive sample.

4. **Canonical learner grammar.**  
   Define the full learner grammar rather than only transported distributions.

5. **Sample consistency.**  
   Prove that every positive sample word is generated by the learner grammar.

6. **Hybrid filling lemma.**  
   Prove that replacing a tuple by a distribution-equivalent tuple inside a
   binary derivation context preserves target membership.

7. **Exact reconstruction theorem.**  
   Combine output-type refinement, characteristic sample coverage, unit
   transport, and hybrid filling to prove the grammar-level exact reconstruction
   theorem.

8. **No-advice boundary.**  
   Formalize the superfinite chain
   \(\{a^n b^n \mid 1 \le n \le k\} \uparrow
     \{a^n b^n \mid n \ge 1\}\).

For FI submission purposes, the most valuable next step is still not the
complexity theory, but the core MCFG bookkeeping: output-type refinement,
occurrence witnesses, extracted rules, and the hybrid filling lemma.

---

## 8. Current status summary

```text
Checked by CI: yes
Latest CI: Lean CI #377
Latest commit reported by user: 591118a
Top checked module: LeanCfgProject.MCFG.FI_v2_1_GoldStabilization
Aggregate import: LeanCfgProject.MCFG.Basic
Scope: fixed-observation, named-context, MCFG syntax/semantics, sample-safe
       distribution transport, reconstruction certificates, and Gold-style
       stabilization skeleton
Full MCFG reconstruction theorem checked: no
No-advice theorem checked: no
Bounded-spine theorem checked: no
```

In one sentence:

> The current Lean development machine-checks the main fixed-observation and
> distributional bookkeeping layers of the paper up through a
> distribution-level reconstruction certificate and Gold-style stabilization
> skeleton, while leaving the full presentation-relative canonical-grammar
> reconstruction theorem for future formalization.
