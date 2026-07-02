import LeanCfgProject.MCFG.FI_v2_1_SubwordContextEnumerationGold

/-!
# FI v2.1 Lean experiment: finite enumeration of subword unit edges

This file is the next vertical step after `SubwordContextEnumeration`.

The previous layer built an actual finite list of two-sided subword-context
candidates for each finite sample.  Here we use that list to generate unit-edge
witnesses: whenever two listed subword decompositions expose tuples in the same
named context and have the same fixed observation type, they determine a raw
sample-safe unit-edge witness.

The construction is still deliberately conservative.  The equality and type
checks are performed by a classical finite filter over the finite list of
subword-decomposition pairs.  This gives an actual finite list of raw unit-edge
witnesses, rather than an arbitrary externally supplied list.
-/

namespace FIv21

universe u v w

section SubwordUnitEdgeEnumeration

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A pair of listed subword decompositions.  Such a pair becomes a unit-edge
candidate when the two decompositions use the same context and expose tuples of
the same fixed observation type. -/
structure SubwordDecompositionPair (K : Finset (Word α)) where
  src : SubwordSampleDecomposition (α := α) K
  tgt : SubwordSampleDecomposition (α := α) K

namespace SubwordDecompositionPair

/-- Source tuple of a subword pair. -/
def srcTuple {K : Finset (Word α)} (P : SubwordDecompositionPair (α := α) K) :
    Tuple α 1 :=
  P.src.tuple

/-- Target tuple of a subword pair. -/
def tgtTuple {K : Finset (Word α)} (P : SubwordDecompositionPair (α := α) K) :
    Tuple α 1 :=
  P.tgt.tuple

/-- The context used for the induced unit edge. -/
def context {K : Finset (Word α)} (P : SubwordDecompositionPair (α := α) K) :
    NamedSentenceContext α 1 :=
  P.src.context

end SubwordDecompositionPair

/-- All ordered pairs drawn from a finite list of subword decompositions. -/
def subwordDecompositionPairs
    {K : Finset (Word α)}
    (Ss : List (SubwordSampleDecomposition (α := α) K)) :
    List (SubwordDecompositionPair (α := α) K) :=
  Ss.flatMap (fun S => Ss.map (fun T => { src := S, tgt := T }))

/-- If source and target are listed, their ordered pair is listed. -/
theorem subwordDecompositionPair_mem
    {K : Finset (Word α)}
    {Ss : List (SubwordSampleDecomposition (α := α) K)}
    {S T : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ Ss) (hT : T ∈ Ss) :
    ({ src := S, tgt := T } : SubwordDecompositionPair (α := α) K) ∈
      subwordDecompositionPairs (α := α) Ss := by
  unfold subwordDecompositionPairs
  exact List.mem_flatMap.mpr ⟨S, hS, List.mem_map.mpr ⟨T, hT, rfl⟩⟩

/-- Predicate selecting the ordered subword pairs that can generate a unit edge:
the same context is observed on both sides and the exposed singleton tuples have
the same fixed observation type. -/
def SubwordUnitEdgePredicate
    {K : Finset (Word α)} (obs : α → M)
    (P : SubwordDecompositionPair (α := α) K) : Prop :=
  P.src.context = P.tgt.context ∧
    tupleType obs P.src.tuple = tupleType obs P.tgt.tuple

/-- The finite list of unit-edge candidate pairs obtained by filtering all
ordered subword-decomposition pairs. -/
noncomputable def typedSameContextSubwordPairs
    {K : Finset (Word α)}
    (obs : α → M)
    (Ss : List (SubwordSampleDecomposition (α := α) K)) :
    List (SubwordDecompositionPair (α := α) K) := by
  classical
  exact (subwordDecompositionPairs (α := α) Ss).filter
    (fun P => SubwordUnitEdgePredicate (α := α) obs P)

/-- Membership in the filtered pair list exposes the same-context and same-type
witnesses. -/
theorem typedSameContextSubwordPairs_property
    {K : Finset (Word α)}
    {obs : α → M}
    {Ss : List (SubwordSampleDecomposition (α := α) K)}
    {P : SubwordDecompositionPair (α := α) K}
    (hP : P ∈ typedSameContextSubwordPairs (α := α) obs Ss) :
    SubwordUnitEdgePredicate (α := α) obs P := by
  classical
  unfold typedSameContextSubwordPairs at hP
  exact of_decide_eq_true (List.mem_filter.mp hP).2

/-- A filtered pair is still a pair drawn from the original subword list. -/
theorem typedSameContextSubwordPairs_mem_pairs
    {K : Finset (Word α)}
    {obs : α → M}
    {Ss : List (SubwordSampleDecomposition (α := α) K)}
    {P : SubwordDecompositionPair (α := α) K}
    (hP : P ∈ typedSameContextSubwordPairs (α := α) obs Ss) :
    P ∈ subwordDecompositionPairs (α := α) Ss := by
  classical
  unfold typedSameContextSubwordPairs at hP
  exact (List.mem_filter.mp hP).1

/-- Convert a same-context, same-type subword pair into a raw unit-edge witness. -/
noncomputable def rawUnitEdgeWitnessOfSubwordPair
    {K : Finset (Word α)}
    (obs : α → M) (f : Nat) (hfanout : 1 ≤ f)
    (P : SubwordDecompositionPair (α := α) K)
    (hP : SubwordUnitEdgePredicate (α := α) obs P) :
    RawSampleUnitEdgeWitness (α := α) K obs f :=
  { d := 1
    src := P.src.tuple
    tgt := P.tgt.tuple
    context := P.src.context
    hd := hfanout
    hpos := by decide
    src_mem := by
      exact P.src.filled_mem_sample
    tgt_mem := by
      rcases hP with ⟨hctx, _htype⟩
      rw [hctx]
      exact P.tgt.filled_mem_sample
    type_eq := hP.2 }

/-- The raw witness produced from a filtered pair is sample safe. -/
theorem rawUnitEdgeWitnessOfSubwordPair_sampleSafeMerge
    {K : Finset (Word α)}
    {obs : α → M} {f : Nat} {hfanout : 1 ≤ f}
    {P : SubwordDecompositionPair (α := α) K}
    (hP : SubwordUnitEdgePredicate (α := α) obs P) :
    SampleSafeMerge K obs
      (rawUnitEdgeWitnessOfSubwordPair (α := α) obs f hfanout P hP).src
      (rawUnitEdgeWitnessOfSubwordPair (α := α) obs f hfanout P hP).tgt := by
  exact (rawUnitEdgeWitnessOfSubwordPair (α := α) obs f hfanout P hP).sampleSafeMerge

/-- Raw unit-edge witnesses generated from the filtered subword-pair list. -/
noncomputable def rawUnitEdgeWitnessesOfSubwordPairs
    {K : Finset (Word α)}
    (obs : α → M) (f : Nat) (hfanout : 1 ≤ f)
    (Ss : List (SubwordSampleDecomposition (α := α) K)) :
    List (RawSampleUnitEdgeWitness (α := α) K obs f) :=
  (typedSameContextSubwordPairs (α := α) obs Ss).attach.map (fun P =>
    rawUnitEdgeWitnessOfSubwordPair (α := α) obs f hfanout P.1
      (typedSameContextSubwordPairs_property (α := α) P.2))

/-- A filtered same-context/same-type pair contributes its raw unit-edge witness
to the generated witness list. -/
theorem rawUnitEdgeWitness_mem_of_typedPair_mem
    {K : Finset (Word α)}
    {obs : α → M} {f : Nat} {hfanout : 1 ≤ f}
    {Ss : List (SubwordSampleDecomposition (α := α) K)}
    {P : SubwordDecompositionPair (α := α) K}
    (hP : P ∈ typedSameContextSubwordPairs (α := α) obs Ss) :
    rawUnitEdgeWitnessOfSubwordPair (α := α) obs f hfanout P
        (typedSameContextSubwordPairs_property (α := α) hP) ∈
      rawUnitEdgeWitnessesOfSubwordPairs (α := α) obs f hfanout Ss := by
  unfold rawUnitEdgeWitnessesOfSubwordPairs
  exact List.mem_map.mpr ⟨⟨P, hP⟩, by simp, rfl⟩

/-- Subword-context data whose unit-edge witnesses are generated by finite
filtering of its own listed subword decompositions. -/
structure SubwordUnitEdgeEnumerationData
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  f : Nat
  hfanout : 1 ≤ f
  subwordDecompositions : List (SubwordSampleDecomposition (α := α) K)
  semanticWorking : G.SemanticWorkingConditions

namespace SubwordUnitEdgeEnumerationData

/-- The raw unit-edge witnesses generated from the listed subword decompositions. -/
noncomputable def unitEdgeWitnesses
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) :
    List (RawSampleUnitEdgeWitness (α := α) K obs D.f) :=
  rawUnitEdgeWitnessesOfSubwordPairs (α := α) obs D.f D.hfanout D.subwordDecompositions

/-- Forget to the previous subword-context decomposition-data layer. -/
noncomputable def toSubwordContextDecompositionData
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) :
    SubwordContextDecompositionData G obs K :=
  { f := D.f
    subwordDecompositions := D.subwordDecompositions
    unitEdgeWitnesses := D.unitEdgeWitnesses
    semanticWorking := D.semanticWorking }

@[simp] theorem toSubwordContextDecompositionData_decompositions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) :
    D.toSubwordContextDecompositionData.subwordDecompositions =
      D.subwordDecompositions := by
  rfl

@[simp] theorem toSubwordContextDecompositionData_unitEdgeWitnesses
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) :
    D.toSubwordContextDecompositionData.unitEdgeWitnesses =
      D.unitEdgeWitnesses := by
  rfl

/-- The induced finite support. -/
noncomputable def support
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) : FiniteLearnerSupport α :=
  D.toSubwordContextDecompositionData.support

/-- The induced support records the original sample exactly. -/
theorem support_sample_eq
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) :
    D.support.sample = K := by
  exact D.toSubwordContextDecompositionData.support_sample_eq

/-- Listed subword decompositions still support their exposed tuples. -/
theorem supportsTuple_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    D.support.SupportsTuple S.tuple := by
  exact D.toSubwordContextDecompositionData.supportsTuple_of_subword_mem hS

/-- Listed subword decompositions still support their exposed contexts. -/
theorem supportsContext_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    D.support.SupportsContext S.context := by
  exact D.toSubwordContextDecompositionData.supportsContext_of_subword_mem hS

/-- Listed subword decompositions are still licensed by the sample distribution. -/
theorem subword_context_mem_sampleDistribution
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    S.context ∈ SampleNamedDistribution K S.tuple := by
  exact D.toSubwordContextDecompositionData.subword_context_mem_sampleDistribution hS

/-- A filtered same-context/same-type pair gives a raw unit-edge witness in
the locally generated witness list. -/
theorem unitEdgeWitness_mem_of_typedPair_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K)
    {P : SubwordDecompositionPair (α := α) K}
    (hP : P ∈ typedSameContextSubwordPairs (α := α) obs D.subwordDecompositions) :
    rawUnitEdgeWitnessOfSubwordPair (α := α) obs D.f D.hfanout P
        (typedSameContextSubwordPairs_property (α := α) hP) ∈
      D.unitEdgeWitnesses := by
  unfold unitEdgeWitnesses
  exact _root_.FIv21.rawUnitEdgeWitness_mem_of_typedPair_mem
    (α := α) (f := D.f) (hfanout := D.hfanout)
    (Ss := D.subwordDecompositions) hP

/-- A filtered same-context/same-type pair gives a raw unit-edge witness in the
induced subword-context data. -/
theorem rawUnitEdgeWitness_mem_of_typedPair_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K)
    {P : SubwordDecompositionPair (α := α) K}
    (hP : P ∈ typedSameContextSubwordPairs (α := α) obs D.subwordDecompositions) :
    rawUnitEdgeWitnessOfSubwordPair (α := α) obs D.f D.hfanout P
        (typedSameContextSubwordPairs_property (α := α) hP) ∈
      D.toSubwordContextDecompositionData.unitEdgeWitnesses := by
  change
    rawUnitEdgeWitnessOfSubwordPair (α := α) obs D.f D.hfanout P
        (typedSameContextSubwordPairs_property (α := α) hP) ∈
      D.unitEdgeWitnesses
  exact D.unitEdgeWitness_mem_of_typedPair_mem hP

/-- A filtered same-context/same-type pair gives unit reachability in the induced
sample-extracted rule-list object. -/
theorem typedPair_unitReach
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K)
    {P : SubwordDecompositionPair (α := α) K}
    (hP : P ∈ typedSameContextSubwordPairs (α := α) obs D.subwordDecompositions) :
    D.toSubwordContextDecompositionData.toSampleExtractedRuleLists.UnitReach
      P.src.tuple P.tgt.tuple := by
  change
    D.toSubwordContextDecompositionData.toRawSampleDecompositionData
      |>.toSampleExtractedRuleLists
      |>.UnitReach P.src.tuple P.tgt.tuple
  exact
    RawSampleDecompositionData.unitEdge_reaches_in_sampleExtractedRuleLists
      D.toSubwordContextDecompositionData.toRawSampleDecompositionData
      (D.rawUnitEdgeWitness_mem_of_typedPair_mem hP)

/-- Forget to the finite-hypothesis layer. -/
noncomputable def toFiniteLearnerHypothesis
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) :
    FiniteHypothesisLearner α M :=
  fun _K => D.toSubwordContextDecompositionData.toFiniteLearnerHypothesis

end SubwordUnitEdgeEnumerationData

/-- Concrete unit-edge enumeration data using the already constructed finite
subword-context enumeration list. -/
noncomputable def enumeratedSubwordUnitEdgeEnumerationData
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SubwordUnitEdgeEnumerationData G obs K :=
  { f := f
    hfanout := hfanout
    subwordDecompositions := enumeratedSubwordDecompositions (α := α) K
    semanticWorking := hG }

@[simp] theorem enumeratedSubwordUnitEdgeEnumerationData_decompositions
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).subwordDecompositions =
      enumeratedSubwordDecompositions (α := α) K := by
  rfl

/-- The concrete unit-edge enumeration data has the same sample support. -/
theorem enumeratedSubwordUnitEdgeEnumerationData_support_sample_eq
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).support.sample = K := by
  exact (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).support_sample_eq

/-- The concrete unit-edge enumeration still represents every sampled word by a
supported enumerated subword decomposition. -/
theorem enumeratedSubwordUnitEdgeEnumerationData_supported_sample_word
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    {w : Word α} (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).subwordDecompositions ∧
      S.sampleWord = w ∧
      (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).support.SupportsTuple S.tuple ∧
      (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).support.SupportsContext S.context ∧
      S.context ∈ SampleNamedDistribution K S.tuple := by
  rcases exists_enumeratedSubwordDecomposition_of_mem (α := α) hw with
    ⟨S, hS, hWord, _hLeft, _hMid, _hRight⟩
  refine ⟨S, hS, hWord, ?_, ?_, ?_⟩
  · exact (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).supportsTuple_of_subword_mem hS
  · exact (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).supportsContext_of_subword_mem hS
  · exact S.context_mem_sampleDistribution

/-- Learner using concrete subword decomposition enumeration plus finite
same-context/same-type unit-edge filtering. -/
noncomputable def enumeratedSubwordUnitEdgeEnumerationLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :=
  fun K => enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG

end SubwordUnitEdgeEnumeration

end FIv21
