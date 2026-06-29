import LeanCfgProject.MCFG.FI_v2_1_RawSampleDecompositionEnumerationGold

/-!
# FI v2.1 Lean experiment: subword two-sided context decompositions

This file is a vertical step after the elementary raw-sample decomposition
enumeration layer.

The previous file generated the trivial one-hole decomposition of each sampled
word.  Here we introduce a more concrete two-sided decomposition witness

`sampleWord = left ++ middle ++ right`,

which exposes `middle` as a singleton tuple and uses the ordinary two-sided
named context determined by `left` and `right`.  This is still not a complete
automatic enumeration of all subwords of every sampled word, but it is the
right implementation-facing representation for the next such enumeration.
-/

namespace FIv21

universe u v w

noncomputable section SubwordContextDecomposition

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- The named one-hole context with terminal material on the left and right. -/
def twoSidedNamedContext (left right : Word α) : NamedSentenceContext α 1 :=
  { val := rawTwoSidedAsNamed left right
    property := by
      refine ⟨rfl, ?_, ?_⟩
      · simp [rawTwoSidedAsNamed, finOne]
      · intro i
        fin_cases i
        simp [rawTwoSidedAsNamed, finOne] }

@[simp] theorem namedFill_twoSidedNamedContext_singletonTuple
    (left middle right : Word α) :
    namedFill 1 (twoSidedNamedContext (α := α) left right)
      (singletonTuple middle) = left ++ middle ++ right := by
  change rawNamedFill (rawTwoSidedAsNamed left right) (singletonTuple middle) =
    left ++ middle ++ right
  rw [rawNamedFill_twoSided]
  simp [singletonTuple, finOne]

/-- A concrete two-sided subword decomposition of a sampled word.

The intended reading is that `middle` is the exposed tuple component and
`left`/`right` form the surrounding one-hole sentence context. -/
structure SubwordSampleDecomposition (K : Finset (Word α)) where
  left : Word α
  middle : Word α
  right : Word α
  sampleWord : Word α
  sampleWord_mem : sampleWord ∈ K
  sampleWord_eq : left ++ middle ++ right = sampleWord

namespace SubwordSampleDecomposition

/-- The singleton tuple exposed by a two-sided subword decomposition. -/
def tuple {K : Finset (Word α)}
    (S : SubwordSampleDecomposition (α := α) K) : Tuple α 1 :=
  singletonTuple S.middle

/-- The two-sided named context exposed by a subword decomposition. -/
def context {K : Finset (Word α)}
    (S : SubwordSampleDecomposition (α := α) K) : NamedSentenceContext α 1 :=
  twoSidedNamedContext S.left S.right

/-- Forget a subword decomposition to the raw named-context decomposition layer. -/
def toRawSampleDecomposition {K : Finset (Word α)}
    (S : SubwordSampleDecomposition (α := α) K) :
    RawSampleDecomposition (α := α) K :=
  { d := 1
    tuple := S.tuple
    context := S.context
    sampleWord := S.sampleWord
    sampleWord_mem := S.sampleWord_mem
    filled_eq := by
      simpa [tuple, context] using S.sampleWord_eq }

/-- Filling the exposed tuple in the exposed context returns the sampled word. -/
theorem filled_eq_sampleWord {K : Finset (Word α)}
    (S : SubwordSampleDecomposition (α := α) K) :
    namedFill 1 S.context S.tuple = S.sampleWord := by
  exact S.toRawSampleDecomposition.filled_eq

/-- The filled word of a subword decomposition belongs to the sample. -/
theorem filled_mem_sample {K : Finset (Word α)}
    (S : SubwordSampleDecomposition (α := α) K) :
    namedFill 1 S.context S.tuple ∈ K := by
  exact S.toRawSampleDecomposition.filled_mem_sample

/-- The exposed context is licensed by the sample distribution of the exposed
singleton tuple. -/
theorem context_mem_sampleDistribution {K : Finset (Word α)}
    (S : SubwordSampleDecomposition (α := α) K) :
    S.context ∈ SampleNamedDistribution K S.tuple := by
  exact S.toRawSampleDecomposition.context_mem_sampleDistribution

end SubwordSampleDecomposition

/-- Convert a finite list of subword decompositions to raw decompositions. -/
def rawDecompositionsOfSubwords
    {K : Finset (Word α)}
    (Ss : List (SubwordSampleDecomposition (α := α) K)) :
    List (RawSampleDecomposition (α := α) K) :=
  Ss.map SubwordSampleDecomposition.toRawSampleDecomposition

/-- A listed subword decomposition contributes its raw decomposition to the
converted list. -/
theorem rawDecomposition_mem_of_subword_mem
    {K : Finset (Word α)}
    {Ss : List (SubwordSampleDecomposition (α := α) K)}
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ Ss) :
    S.toRawSampleDecomposition ∈ rawDecompositionsOfSubwords Ss := by
  exact List.mem_map.mpr ⟨S, hS, rfl⟩

/-- Data consisting of finite subword decompositions plus raw unit-edge
witnesses.  Forgetting this data gives ordinary raw-sample decomposition data. -/
structure SubwordContextDecompositionData
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  f : Nat
  subwordDecompositions : List (SubwordSampleDecomposition (α := α) K)
  unitEdgeWitnesses : List (RawSampleUnitEdgeWitness (α := α) K obs f)
  semanticWorking : G.SemanticWorkingConditions

namespace SubwordContextDecompositionData

/-- The raw decompositions induced by the listed subword decompositions. -/
def rawDecompositions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :
    List (RawSampleDecomposition (α := α) K) :=
  rawDecompositionsOfSubwords D.subwordDecompositions

/-- Forget subword decomposition data to the previous raw decomposition layer. -/
noncomputable def toRawSampleDecompositionData
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :
    RawSampleDecompositionData G obs K :=
  { f := D.f
    decompositions := D.rawDecompositions
    unitEdgeWitnesses := D.unitEdgeWitnesses
    semanticWorking := D.semanticWorking }

@[simp] theorem toRawSampleDecompositionData_decompositions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :
    D.toRawSampleDecompositionData.decompositions = D.rawDecompositions := by
  rfl

@[simp] theorem toRawSampleDecompositionData_unitEdgeWitnesses
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :
    D.toRawSampleDecompositionData.unitEdgeWitnesses = D.unitEdgeWitnesses := by
  rfl

/-- A listed subword decomposition is listed after forgetting to raw
sample-decomposition data. -/
theorem rawDecomposition_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    S.toRawSampleDecomposition ∈ D.toRawSampleDecompositionData.decompositions := by
  exact rawDecomposition_mem_of_subword_mem hS

/-- The finite support induced by subword data. -/
noncomputable def support
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) : FiniteLearnerSupport α :=
  D.toRawSampleDecompositionData.support

/-- The induced support records the original sample exactly. -/
theorem support_sample_eq
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :
    D.support.sample = K := by
  exact D.toRawSampleDecompositionData.support_sample_eq

/-- A listed subword decomposition contributes a supported singleton tuple. -/
theorem supportsTuple_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    D.support.SupportsTuple S.tuple := by
  exact D.toRawSampleDecompositionData.supportsTuple_of_decomposition_mem
    (D.rawDecomposition_mem hS)

/-- A listed subword decomposition contributes a supported two-sided context. -/
theorem supportsContext_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    D.support.SupportsContext S.context := by
  exact D.toRawSampleDecompositionData.supportsContext_of_decomposition_mem
    (D.rawDecomposition_mem hS)

/-- A listed subword decomposition is licensed by the sample distribution. -/
theorem subword_context_mem_sampleDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K)
    {S : SubwordSampleDecomposition (α := α) K}
    (_hS : S ∈ D.subwordDecompositions) :
    S.context ∈ SampleNamedDistribution K S.tuple := by
  exact S.context_mem_sampleDistribution

/-- The filled word of a listed subword decomposition belongs to the induced
support sample. -/
theorem subword_filled_mem_support_sample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K)
    {S : SubwordSampleDecomposition (α := α) K}
    (_hS : S ∈ D.subwordDecompositions) :
    namedFill 1 S.context S.tuple ∈ D.support.sample := by
  simpa [support] using
    (RawSampleDecomposition.filled_mem_support_sample
      D.toRawSampleDecompositionData.support_sample_eq S.toRawSampleDecomposition)

/-- Forget to the observed-atom layer through raw decomposition data. -/
noncomputable def toObservedSampleAtoms
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :
    ObservedSampleAtoms G obs K :=
  D.toRawSampleDecompositionData.toObservedSampleAtoms

/-- Forget to the sample-extracted rule-list layer. -/
noncomputable def toSampleExtractedRuleLists
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :
    SampleExtractedRuleLists G obs K :=
  D.toRawSampleDecompositionData.toSampleExtractedRuleLists

/-- Forget to concrete extracted sample data. -/
noncomputable def toConcreteExtractedSampleData
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :
    ConcreteExtractedSampleData G obs K :=
  D.toRawSampleDecompositionData.toConcreteExtractedSampleData

/-- Forget to a finite learner hypothesis. -/
noncomputable def toFiniteLearnerHypothesis
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :
    FiniteLearnerHypothesis α M :=
  D.toRawSampleDecompositionData.toFiniteLearnerHypothesis

/-- The actual refined rule lists are still the finite-monoid lists generated
from the grammar-side plan. -/
theorem concreteRules_eq_actual
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :
    D.toObservedSampleAtoms.concreteRules =
      actualFintypeConcreteRuleEnumeration G obs D.semanticWorking := by
  exact D.toRawSampleDecompositionData.concreteRules_eq_actual

/-- The actual refined rule lists contain all ordinary output-type refinements. -/
theorem concrete_containsAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K) :
    D.toObservedSampleAtoms.concreteRules.toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact D.toRawSampleDecompositionData.concrete_containsAllOrdinaryRuleRefinements

/-- Unit reachability induced by the underlying raw decomposition data. -/
noncomputable def UnitReach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K)
    {d : Nat} (x y : Tuple α d) : Prop :=
  D.toRawSampleDecompositionData.UnitReach x y

/-- Approximate named distribution induced by subword decomposition data. -/
noncomputable def ApproxDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordContextDecompositionData G obs K)
    {d : Nat} (x : Tuple α d) : Set (NamedSentenceContext α d) :=
  D.toRawSampleDecompositionData.ApproxDistribution x

end SubwordContextDecompositionData

/-- The whole-word subword decomposition, with empty left and right context. -/
def wholeWordSubwordDecomposition
    (K : Finset (Word α))
    (w : { w // w ∈ K }) : SubwordSampleDecomposition (α := α) K :=
  { left := []
    middle := w.1
    right := []
    sampleWord := w.1
    sampleWord_mem := w.2
    sampleWord_eq := by
      simp }

/-- The finite list of whole-word subword decompositions generated by the sample. -/
noncomputable def wholeWordSubwordDecompositions
    (K : Finset (Word α)) : List (SubwordSampleDecomposition (α := α) K) :=
  K.attach.toList.map (wholeWordSubwordDecomposition (α := α) K)

/-- Every sample word contributes its whole-word subword decomposition. -/
theorem wholeWordSubwordDecomposition_mem
    {K : Finset (Word α)}
    (w : { w // w ∈ K }) :
    wholeWordSubwordDecomposition (α := α) K w ∈
      wholeWordSubwordDecompositions (α := α) K := by
  unfold wholeWordSubwordDecompositions
  exact List.mem_map.mpr ⟨w, by simp, rfl⟩

/-- Whole-word subword decomposition data with no unit-edge witnesses. -/
noncomputable def wholeWordSubwordContextDecompositionData
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hG : G.SemanticWorkingConditions) :
    SubwordContextDecompositionData G obs K :=
  { f := f
    subwordDecompositions := wholeWordSubwordDecompositions (α := α) K
    unitEdgeWitnesses := []
    semanticWorking := hG }

@[simp] theorem wholeWordSubwordContextDecompositionData_decompositions
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hG : G.SemanticWorkingConditions) :
    (wholeWordSubwordContextDecompositionData G obs K f hG).subwordDecompositions =
      wholeWordSubwordDecompositions (α := α) K := by
  rfl

/-- Every sampled word has a listed whole-word subword decomposition. -/
theorem exists_wholeWordSubwordDecomposition_of_mem
    {K : Finset (Word α)} {w : Word α}
    (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ wholeWordSubwordDecompositions (α := α) K ∧
      S.sampleWord = w ∧
      S.left = [] ∧ S.middle = w ∧ S.right = [] := by
  let sw : { w // w ∈ K } := ⟨w, hw⟩
  refine ⟨wholeWordSubwordDecomposition (α := α) K sw, ?_, rfl, rfl, rfl, rfl⟩
  exact wholeWordSubwordDecomposition_mem (α := α) sw

/-- Whole-word subword data supports the exposed singleton tuple and context for
every sampled word. -/
theorem wholeWordSubwordContextDecompositionData_supported_sample_word
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hG : G.SemanticWorkingConditions)
    {w : Word α} (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ (wholeWordSubwordContextDecompositionData G obs K f hG).subwordDecompositions ∧
      S.sampleWord = w ∧
      (wholeWordSubwordContextDecompositionData G obs K f hG).support.SupportsTuple S.tuple ∧
      (wholeWordSubwordContextDecompositionData G obs K f hG).support.SupportsContext S.context ∧
      S.context ∈ SampleNamedDistribution K S.tuple := by
  rcases exists_wholeWordSubwordDecomposition_of_mem (α := α) hw with
    ⟨S, hS, hWord, _hLeft, _hMid, _hRight⟩
  refine ⟨S, hS, hWord, ?_, ?_, ?_⟩
  · exact (wholeWordSubwordContextDecompositionData G obs K f hG).supportsTuple_of_subword_mem hS
  · exact (wholeWordSubwordContextDecompositionData G obs K f hG).supportsContext_of_subword_mem hS
  · exact S.context_mem_sampleDistribution

/-- A learner using whole-word subword decompositions for every finite sample. -/
noncomputable def wholeWordSubwordContextDecompositionLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hG : G.SemanticWorkingConditions) :=
  fun K => wholeWordSubwordContextDecompositionData G obs K f hG

end SubwordContextDecomposition

end FIv21
