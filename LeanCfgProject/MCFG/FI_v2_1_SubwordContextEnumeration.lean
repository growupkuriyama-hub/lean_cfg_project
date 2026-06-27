import LeanCfgProject.MCFG.FI_v2_1_SubwordContextDecompositionGold

/-!
# FI v2.1 Lean experiment: finite enumeration of subword contexts

This file is a vertical step after `SubwordContextDecomposition`.

The previous layer accepted a finite list of two-sided decompositions
`sampleWord = left ++ middle ++ right`.  Here we build an actual finite
enumeration of such cut candidates for each sampled word.  The enumeration is
still intentionally simple: it enumerates prefix/suffix cuts of a word, then
prefix/suffix cuts of the remaining suffix, yielding all listed triples of the
form `left ++ middle ++ right`.

For safety and continuity with the previous whole-word layer, the final list is
prefixed by the already checked whole-word decompositions.  Thus every sampled
word is still represented even if later refinements replace the cut enumerator.
-/

namespace FIv21

universe u v w

section SubwordContextEnumeration

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A prefix/suffix cut of a fixed word. -/
structure PrefixSuffixCut (w : Word α) where
  prefix : Word α
  suffix : Word α
  eq_append : prefix ++ suffix = w

namespace PrefixSuffixCut

/-- The word reconstructed from a prefix/suffix cut. -/
theorem append_eq {w : Word α} (C : PrefixSuffixCut (α := α) w) :
    C.prefix ++ C.suffix = w :=
  C.eq_append

end PrefixSuffixCut

/-- All prefix/suffix cuts of a word, represented with equality witnesses.

The definition is recursive and concrete.  For `a :: xs`, it contains the cut
`([], a :: xs)` and then extends every cut of `xs` by prefixing `a` to its left
part. -/
def prefixSuffixCuts : (w : Word α) → List (PrefixSuffixCut (α := α) w)
  | [] =>
      [{ prefix := []
         suffix := []
         eq_append := by simp }]
  | a :: xs =>
      { prefix := []
        suffix := a :: xs
        eq_append := by simp } ::
      (prefixSuffixCuts xs).map (fun C =>
        { prefix := a :: C.prefix
          suffix := C.suffix
          eq_append := by
            simpa [C.eq_append] })

/-- Every listed prefix/suffix cut reconstructs the original word. -/
theorem prefixSuffixCuts_sound
    {w : Word α} {C : PrefixSuffixCut (α := α) w}
    (_hC : C ∈ prefixSuffixCuts (α := α) w) :
    C.prefix ++ C.suffix = w := by
  exact C.eq_append

/-- A two-sided subword cut of a fixed word. -/
structure SubwordCut (w : Word α) where
  left : Word α
  middle : Word α
  right : Word α
  eq_append : left ++ middle ++ right = w

namespace SubwordCut

/-- The two-sided cut reconstructs the original word. -/
theorem append_eq {w : Word α} (C : SubwordCut (α := α) w) :
    C.left ++ C.middle ++ C.right = w :=
  C.eq_append

/-- The named two-sided context associated with a cut. -/
def context {w : Word α} (C : SubwordCut (α := α) w) :
    NamedSentenceContext α 1 :=
  twoSidedNamedContext C.left C.right

/-- The singleton tuple associated with a cut. -/
def tuple {w : Word α} (C : SubwordCut (α := α) w) : Tuple α 1 :=
  singletonTuple C.middle

/-- Filling the context associated with a cut by its tuple reconstructs the
original word. -/
theorem namedFill_context_tuple {w : Word α} (C : SubwordCut (α := α) w) :
    namedFill 1 C.context C.tuple = w := by
  simpa [context, tuple] using C.eq_append

end SubwordCut

/-- Enumerate two-sided subword cuts by first cutting the word into
`left ++ rest`, then cutting `rest` into `middle ++ right`. -/
def subwordCuts (w : Word α) : List (SubwordCut (α := α) w) :=
  (prefixSuffixCuts (α := α) w).bind (fun LR =>
    (prefixSuffixCuts (α := α) LR.suffix).map (fun MR =>
      { left := LR.prefix
        middle := MR.prefix
        right := MR.suffix
        eq_append := by
          calc
            LR.prefix ++ MR.prefix ++ MR.suffix
                = LR.prefix ++ (MR.prefix ++ MR.suffix) := by
                    simp [List.append_assoc]
            _ = LR.prefix ++ LR.suffix := by
                    simpa [MR.eq_append]
            _ = w := LR.eq_append }))

/-- Every listed subword cut reconstructs the original word. -/
theorem subwordCuts_sound
    {w : Word α} {C : SubwordCut (α := α) w}
    (_hC : C ∈ subwordCuts (α := α) w) :
    C.left ++ C.middle ++ C.right = w := by
  exact C.eq_append

/-- Turn a cut of an attached sample word into a subword-sample decomposition. -/
def subwordSampleDecompositionOfCut
    (K : Finset (Word α)) (w : { w // w ∈ K })
    (C : SubwordCut (α := α) w.1) :
    SubwordSampleDecomposition (α := α) K :=
  { left := C.left
    middle := C.middle
    right := C.right
    sampleWord := w.1
    sampleWord_mem := w.2
    sampleWord_eq := C.eq_append }

/-- Enumerated subword decompositions for one attached sample word. -/
def subwordDecompositionsForWord
    (K : Finset (Word α)) (w : { w // w ∈ K }) :
    List (SubwordSampleDecomposition (α := α) K) :=
  (subwordCuts (α := α) w.1).map (subwordSampleDecompositionOfCut (α := α) K w)

/-- A listed cut contributes the corresponding subword decomposition for that
attached sample word. -/
theorem subwordSampleDecomposition_mem_of_cut_mem
    {K : Finset (Word α)} {w : { w // w ∈ K }}
    {C : SubwordCut (α := α) w.1}
    (hC : C ∈ subwordCuts (α := α) w.1) :
    subwordSampleDecompositionOfCut (α := α) K w C ∈
      subwordDecompositionsForWord (α := α) K w := by
  unfold subwordDecompositionsForWord
  exact List.mem_map.mpr ⟨C, hC, rfl⟩

/-- Enumerated subword decompositions for a finite sample.

We include the whole-word decompositions first, then all enumerated two-sided
cuts.  This preserves the previously checked guarantee that every sample word
has at least one listed decomposition. -/
def enumeratedSubwordDecompositions
    (K : Finset (Word α)) :
    List (SubwordSampleDecomposition (α := α) K) :=
  wholeWordSubwordDecompositions (α := α) K ++
    K.attach.toList.bind (fun w => subwordDecompositionsForWord (α := α) K w)

/-- A whole-word decomposition is included in the enumerated subword list. -/
theorem wholeWordSubwordDecomposition_mem_enumerated
    {K : Finset (Word α)}
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ wholeWordSubwordDecompositions (α := α) K) :
    S ∈ enumeratedSubwordDecompositions (α := α) K := by
  unfold enumeratedSubwordDecompositions
  exact List.mem_append_left _ hS

/-- A generated cut decomposition is included in the enumerated subword list. -/
theorem subwordSampleDecomposition_mem_enumerated_of_cut_mem
    {K : Finset (Word α)} {w : { w // w ∈ K }}
    {C : SubwordCut (α := α) w.1}
    (hC : C ∈ subwordCuts (α := α) w.1) :
    subwordSampleDecompositionOfCut (α := α) K w C ∈
      enumeratedSubwordDecompositions (α := α) K := by
  unfold enumeratedSubwordDecompositions
  apply List.mem_append_right
  exact List.mem_bind.mpr
    ⟨w, by simp, subwordSampleDecomposition_mem_of_cut_mem (α := α) hC⟩

/-- Every sample word has a listed whole-word representative inside the full
subword enumeration. -/
theorem exists_enumeratedSubwordDecomposition_of_mem
    {K : Finset (Word α)} {w : Word α}
    (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ enumeratedSubwordDecompositions (α := α) K ∧
      S.sampleWord = w ∧
      S.left = [] ∧ S.middle = w ∧ S.right = [] := by
  rcases exists_wholeWordSubwordDecomposition_of_mem (α := α) hw with
    ⟨S, hS, hWord, hLeft, hMid, hRight⟩
  exact ⟨S, wholeWordSubwordDecomposition_mem_enumerated (α := α) hS,
    hWord, hLeft, hMid, hRight⟩

/-- Subword-context decomposition data using the concrete enumerated subword
list and no raw unit-edge witnesses. -/
noncomputable def enumeratedSubwordContextDecompositionData
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hG : G.SemanticWorkingConditions) :
    SubwordContextDecompositionData G obs K :=
  { f := f
    subwordDecompositions := enumeratedSubwordDecompositions (α := α) K
    unitEdgeWitnesses := []
    semanticWorking := hG }

@[simp] theorem enumeratedSubwordContextDecompositionData_decompositions
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hG : G.SemanticWorkingConditions) :
    (enumeratedSubwordContextDecompositionData G obs K f hG).subwordDecompositions =
      enumeratedSubwordDecompositions (α := α) K := by
  rfl

@[simp] theorem enumeratedSubwordContextDecompositionData_unitEdgeWitnesses
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hG : G.SemanticWorkingConditions) :
    (enumeratedSubwordContextDecompositionData G obs K f hG).unitEdgeWitnesses =
      ([] : List (RawSampleUnitEdgeWitness (α := α) K obs f)) := by
  rfl

/-- The enumerated subword data records the sample exactly in its support. -/
theorem enumeratedSubwordContextDecompositionData_support_sample_eq
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hG : G.SemanticWorkingConditions) :
    (enumeratedSubwordContextDecompositionData G obs K f hG).support.sample = K := by
  exact (enumeratedSubwordContextDecompositionData G obs K f hG).support_sample_eq

/-- Every sampled word has a supported enumerated subword decomposition. -/
theorem enumeratedSubwordContextDecompositionData_supported_sample_word
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hG : G.SemanticWorkingConditions)
    {w : Word α} (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ (enumeratedSubwordContextDecompositionData G obs K f hG).subwordDecompositions ∧
      S.sampleWord = w ∧
      (enumeratedSubwordContextDecompositionData G obs K f hG).support.SupportsTuple S.tuple ∧
      (enumeratedSubwordContextDecompositionData G obs K f hG).support.SupportsContext S.context ∧
      S.context ∈ SampleNamedDistribution K S.tuple := by
  rcases exists_enumeratedSubwordDecomposition_of_mem (α := α) hw with
    ⟨S, hS, hWord, _hLeft, _hMid, _hRight⟩
  refine ⟨S, hS, hWord, ?_, ?_, ?_⟩
  · exact (enumeratedSubwordContextDecompositionData G obs K f hG).supportsTuple_of_subword_mem hS
  · exact (enumeratedSubwordContextDecompositionData G obs K f hG).supportsContext_of_subword_mem hS
  · exact S.context_mem_sampleDistribution

/-- A learner using the concrete enumerated subword decompositions for every
finite sample. -/
noncomputable def enumeratedSubwordContextDecompositionLearner
    (G : WorkingMCFG N α) (obs : α → M)
    (f : Nat) (hG : G.SemanticWorkingConditions) :=
  fun K => enumeratedSubwordContextDecompositionData G obs K f hG

end SubwordContextEnumeration

end FIv21
