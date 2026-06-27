import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedLearnerGrammarSkeletonGold

/-!
# FI v2.1 Lean experiment: sample-generated rule skeletons

This file is the next vertical step after the sample-generated learner-grammar
skeleton.  The previous layer produced the finite nonterminal universe and
same-context/same-type unit candidates.  Here we begin to expose the *rule side*
of the future concrete learner grammar.

The construction is still deliberately conservative: this is a rule skeleton,
not yet the final `WorkingMCFG`.  It provides concrete start-rule candidates,
unit-edge candidates, terminal candidates for singleton exposed middles, and a
binary concatenation candidate for one-hole subword nodes.
-/

namespace FIv21

universe u v w

section SampleGeneratedRuleSkeleton

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- The canonical arity map on learner nonterminals. -/
def canonicalLearnerArity : CanonicalLearnerNonterminal α M → Nat :=
  CanonicalLearnerNonterminal.arity

@[simp] theorem canonicalLearnerArity_root :
    canonicalLearnerArity (α := α) (M := M)
      CanonicalLearnerNonterminal.root = 1 := by
  rfl

@[simp] theorem canonicalLearnerArity_tuple
    {d : Nat} (x : Tuple α d) :
    canonicalLearnerArity (α := α) (M := M)
      (CanonicalLearnerNonterminal.tuple d x) = d := by
  rfl

@[simp] theorem canonicalLearnerArity_context
    {d : Nat} (c : NamedSentenceContext α d) :
    canonicalLearnerArity (α := α) (M := M)
      (CanonicalLearnerNonterminal.context d c) = d := by
  rfl

@[simp] theorem canonicalLearnerArity_typed
    {d : Nat} (τ : Fin d → M) :
    canonicalLearnerArity (α := α) (M := M)
      (CanonicalLearnerNonterminal.typed d τ) = d := by
  rfl

/-- A listed decomposition node, viewed as a start-rule candidate from the
learner root to the tuple exposed by that decomposition. -/
structure SampleGeneratedStartCandidate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) where
  node : SampleGeneratedDecompositionNode S

namespace SampleGeneratedStartCandidate

/-- Child nonterminal of the generated start-rule candidate. -/
def child
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedStartCandidate S) : CanonicalLearnerNonterminal α M :=
  C.node.tupleNonterminal

/-- The syntactic start rule associated with a generated start candidate. -/
def toStartRule
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedStartCandidate S) :
    StartRule (CanonicalLearnerNonterminal α M) :=
  { child := C.child }

/-- The child of a generated start candidate is listed by the learner skeleton. -/
theorem child_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedStartCandidate S) :
    C.child ∈ S.nonterminals := by
  exact C.node.tuple_mem_nonterminals

/-- A generated start candidate points to a one-component tuple node. -/
theorem child_arity_one
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedStartCandidate S) :
    canonicalLearnerArity (α := α) (M := M) C.child = 1 := by
  rfl

/-- The sample word represented by the start candidate is in the underlying
support sample. -/
theorem filled_mem_support_sample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedStartCandidate S) :
    namedFill 1 C.node.decomposition.context C.node.decomposition.tuple ∈
      S.support.sample := by
  exact C.node.filled_mem_support_sample

end SampleGeneratedStartCandidate

/-- Terminal-rule candidate for a listed decomposition whose exposed middle is a
single terminal. -/
structure SampleGeneratedTerminalCandidate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) where
  node : SampleGeneratedDecompositionNode S
  terminal : α
  middle_eq : node.decomposition.middle = [terminal]

namespace SampleGeneratedTerminalCandidate

/-- Left-hand side of a terminal candidate. -/
def lhs
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedTerminalCandidate S) : CanonicalLearnerNonterminal α M :=
  C.node.tupleNonterminal

/-- The syntactic terminal rule associated with a singleton-middle candidate. -/
def toTerminalRule
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedTerminalCandidate S) :
    TerminalRule (CanonicalLearnerNonterminal α M) α :=
  { lhs := C.lhs
    terminal := C.terminal }

/-- The terminal candidate's left-hand side is listed by the learner skeleton. -/
theorem lhs_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedTerminalCandidate S) :
    C.lhs ∈ S.nonterminals := by
  exact C.node.tuple_mem_nonterminals

/-- Terminal candidates are well-typed for the canonical learner arity map. -/
theorem wellTyped
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedTerminalCandidate S) :
    C.toTerminalRule.WellTyped (canonicalLearnerArity (α := α) (M := M)) := by
  rfl

/-- The terminal rule outputs the exposed singleton middle. -/
theorem outputTuple_eq_exposed_middle
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedTerminalCandidate S) :
    C.toTerminalRule.outputTuple = C.node.decomposition.tuple := by
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  simp [TerminalRule.outputTuple, SubwordSampleDecomposition.tuple,
    singletonTuple, toTerminalRule, C.middle_eq]

end SampleGeneratedTerminalCandidate

/-- The one-component concatenation template used by binary concatenation
candidates.  It maps two one-component children to their concatenation. -/
def singletonConcatTemplate : TemplateTuple α 1 1 1 :=
  fun _ =>
    [TemplateAtom.leftVar (α := α) (dB := 1) (dC := 1) 0,
     TemplateAtom.rightVar (α := α) (dB := 1) (dC := 1) 0]

@[simp] theorem evalTemplateTuple_singletonConcatTemplate
    (x y : Tuple α 1) :
    evalTemplateTuple (singletonConcatTemplate (α := α)) x y =
      singletonTuple (x 0 ++ y 0) := by
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst i
  simp [singletonConcatTemplate, evalTemplateTuple, evalTemplateWord,
    evalTemplateAtom, singletonTuple]

/-- Binary-rule candidate asserting that one listed exposed middle is the
concatenation of two other listed exposed middles. -/
structure SampleGeneratedConcatCandidate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) where
  left : SampleGeneratedDecompositionNode S
  right : SampleGeneratedDecompositionNode S
  result : SampleGeneratedDecompositionNode S
  middle_eq : result.decomposition.middle =
    left.decomposition.middle ++ right.decomposition.middle

namespace SampleGeneratedConcatCandidate

/-- Syntactic binary rule associated with a concatenation candidate. -/
def toBinaryRule
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedConcatCandidate S) :
    BinaryRule (CanonicalLearnerNonterminal α M) α
      (canonicalLearnerArity (α := α) (M := M)) :=
  { lhs := C.result.tupleNonterminal
    left := C.left.tupleNonterminal
    right := C.right.tupleNonterminal
    body := singletonConcatTemplate (α := α) }

/-- The left endpoint of a concatenation candidate is listed. -/
theorem left_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedConcatCandidate S) :
    C.left.tupleNonterminal ∈ S.nonterminals := by
  exact C.left.tuple_mem_nonterminals

/-- The right endpoint of a concatenation candidate is listed. -/
theorem right_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedConcatCandidate S) :
    C.right.tupleNonterminal ∈ S.nonterminals := by
  exact C.right.tuple_mem_nonterminals

/-- The result endpoint of a concatenation candidate is listed. -/
theorem result_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedConcatCandidate S) :
    C.result.tupleNonterminal ∈ S.nonterminals := by
  exact C.result.tuple_mem_nonterminals

/-- The syntactic binary rule of a concatenation candidate is nondeleting. -/
theorem nondeleting
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedConcatCandidate S) :
    C.toBinaryRule.Nondeleting := by
  constructor
  · intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    refine ⟨0, ?_⟩
    simp [toBinaryRule, singletonConcatTemplate, BinaryRule.Nondeleting,
      TemplateTuple.Nondeleting]
  · intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    refine ⟨0, ?_⟩
    simp [toBinaryRule, singletonConcatTemplate, BinaryRule.Nondeleting,
      TemplateTuple.Nondeleting]

end SampleGeneratedConcatCandidate

/-- A unit-edge rule candidate, now viewed as part of the rule skeleton. -/
structure SampleGeneratedUnitRuleCandidate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) where
  unit : SampleGeneratedUnitCandidate S

namespace SampleGeneratedUnitRuleCandidate

/-- Source nonterminal of the unit-rule candidate. -/
def src
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitRuleCandidate S) : CanonicalLearnerNonterminal α M :=
  U.unit.srcNonterminal

/-- Target nonterminal of the unit-rule candidate. -/
def tgt
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitRuleCandidate S) : CanonicalLearnerNonterminal α M :=
  U.unit.tgtNonterminal

/-- Source nonterminal is listed by the skeleton. -/
theorem src_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitRuleCandidate S) :
    U.src ∈ S.nonterminals := by
  exact U.unit.src_mem_nonterminals

/-- Target nonterminal is listed by the skeleton. -/
theorem tgt_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitRuleCandidate S) :
    U.tgt ∈ S.nonterminals := by
  exact U.unit.tgt_mem_nonterminals

/-- Unit-rule candidates preserve the previously constructed unit reachability. -/
theorem unitReach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitRuleCandidate S) :
    S.data.toSubwordContextDecompositionData.toSampleExtractedRuleLists.UnitReach
      U.unit.pair.src.tuple U.unit.pair.tgt.tuple := by
  exact U.unit.unitReach

/-- Unit-rule candidates are same-context/same-type candidates. -/
theorem property
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (U : SampleGeneratedUnitRuleCandidate S) :
    SubwordUnitEdgePredicate (α := α) obs U.unit.pair := by
  exact U.unit.property

end SampleGeneratedUnitRuleCandidate

/-- A rule skeleton generated from the sample-generated learner skeleton.

It exposes concrete finite candidate lists for start rules and unit edges.  The
terminal and concatenation candidates are defined above as certified objects;
full finite enumeration of those candidates is left to the following layers. -/
structure SampleGeneratedRuleSkeleton
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  skeleton : SampleGeneratedLearnerGrammarSkeleton G obs K

namespace SampleGeneratedRuleSkeleton

/-- The underlying learner-grammar skeleton. -/
def toSampleGeneratedLearnerGrammarSkeleton
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    SampleGeneratedLearnerGrammarSkeleton G obs K :=
  R.skeleton

/-- The finite nonterminal list inherited from the underlying skeleton. -/
noncomputable def nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    List (CanonicalLearnerNonterminal α M) :=
  R.skeleton.nonterminals

/-- The finite support inherited from the underlying skeleton. -/
noncomputable def support
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) : FiniteLearnerSupport α :=
  R.skeleton.support

/-- The listed decomposition nodes used to generate start-rule candidates. -/
noncomputable def decompositionNodes
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    List (SampleGeneratedDecompositionNode R.skeleton) :=
  R.skeleton.data.subwordDecompositions.attach.map (fun S =>
    { decomposition := S.1, mem := S.2 })

/-- Start-rule candidates, one for each listed decomposition node. -/
noncomputable def startCandidates
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    List (SampleGeneratedStartCandidate R.skeleton) :=
  R.decompositionNodes.map (fun X => { node := X })

/-- Unit-rule candidates, one for each same-context/same-type filtered pair. -/
noncomputable def unitCandidates
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    List (SampleGeneratedUnitRuleCandidate R.skeleton) :=
  (typedSameContextSubwordPairs (α := α) obs
      R.skeleton.data.subwordDecompositions).attach.map (fun P =>
    { unit := { pair := P.1, pair_mem := P.2 } })

/-- The root is listed in the rule skeleton's nonterminal list. -/
theorem root_mem_nonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    SampleGeneratedLearnerGrammarSkeleton.root (α := α) (M := M) ∈
      R.nonterminals := by
  exact R.skeleton.root_mem_nonterminals

/-- The inherited support sample is exactly the input sample. -/
theorem support_sample_eq
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) :
    R.support.sample = K := by
  exact R.skeleton.support_sample_eq

/-- A listed decomposition node contributes a listed start-rule candidate. -/
theorem startCandidate_mem_of_node_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    {X : SampleGeneratedDecompositionNode R.skeleton}
    (hX : X ∈ R.decompositionNodes) :
    ({ node := X } : SampleGeneratedStartCandidate R.skeleton) ∈
      R.startCandidates := by
  unfold startCandidates
  exact List.mem_map.mpr ⟨X, hX, rfl⟩

/-- Every concrete start candidate has a listed child. -/
theorem startCandidate_child_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    {C : SampleGeneratedStartCandidate R.skeleton}
    (_hC : C ∈ R.startCandidates) :
    C.child ∈ R.nonterminals := by
  exact C.child_mem_nonterminals

/-- Every concrete unit candidate has listed endpoints and reachability. -/
theorem unitCandidate_nodes_and_reach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    {U : SampleGeneratedUnitRuleCandidate R.skeleton}
    (_hU : U ∈ R.unitCandidates) :
    U.src ∈ R.nonterminals ∧
    U.tgt ∈ R.nonterminals ∧
    R.skeleton.data.toSubwordContextDecompositionData.toSampleExtractedRuleLists.UnitReach
      U.unit.pair.src.tuple U.unit.pair.tgt.tuple := by
  exact ⟨U.src_mem_nonterminals, U.tgt_mem_nonterminals, U.unitReach⟩

end SampleGeneratedRuleSkeleton

/-- Concrete rule skeleton obtained from the concrete enumerated learner
skeleton. -/
noncomputable def enumeratedSampleGeneratedRuleSkeleton
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedRuleSkeleton G obs K :=
  { skeleton := enumeratedSampleGeneratedLearnerGrammarSkeleton G obs K f hfanout hG }

/-- Every sampled word in the concrete enumerated rule skeleton gives a start
candidate whose child is listed and whose decomposition is licensed by the
sample distribution. -/
theorem enumeratedRuleSkeleton_sample_word_start_candidate
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    {w : Word α} (hw : w ∈ K) :
    ∃ C : SampleGeneratedStartCandidate
        (enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG).skeleton,
      C.node.decomposition.sampleWord = w ∧
      C.child ∈
        (enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG).nonterminals ∧
      C.node.decomposition.context ∈
        SampleNamedDistribution K C.node.decomposition.tuple := by
  rcases enumeratedSkeleton_sample_word_node G obs K f hfanout hG hw with
    ⟨X, hWord, hTuple, _hContext, _hTyped, hDist⟩
  exact ⟨{ node := X }, hWord, hTuple, hDist⟩

end SampleGeneratedRuleSkeleton

end FIv21
