import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedWordParseWitnessConstructionGold

/-!
# FI v2.1 Lean experiment: sample-level prefix-enumeration families

The previous layer turned a prefix-node enumeration for a single word into a
word-parse witness, and a family of such enumerations for all sample words into
sample inclusion in the generated terminal+concat `WorkingMCFG` shell.

This file names that family as a first-class object.  It is intentionally still
certificate-driven: it does not synthesize the prefix-node enumerations.  The
point is to expose the exact sample-level obligation needed by the generated
working grammar: for every sample word, provide a listed prefix-node enumeration.
Once such a family is supplied, the existing construction layer gives
`K ⊆ L(G_K)` for the generated grammar shell.
-/

namespace FIv21

universe u v w

section SampleGeneratedPrefixEnumerationFamily

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A sample-level family of prefix-node enumerations.  This is the precise
finite/combinatorial obligation needed to prove that the generated
terminal+concat grammar shell covers the finite sample. -/
structure SampleGeneratedPrefixEnumerationFamily
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) where
  enumeration : ∀ w : Word α, w ∈ K → SampleGeneratedPrefixNodeEnumeration (M := M) R w

namespace SampleGeneratedPrefixEnumerationFamily

/-- The prefix-node enumeration attached to a sample word. -/
def enumerationOfMem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedPrefixEnumerationFamily (M := M) R)
    {w : Word α} (hw : w ∈ K) :
    SampleGeneratedPrefixNodeEnumeration (M := M) R w :=
  F.enumeration w hw

/-- The word-parse construction attached to a sample word. -/
def wordConstructionOfMem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedPrefixEnumerationFamily (M := M) R)
    {w : Word α} (hw : w ∈ K) :
    SampleGeneratedWordParseWitnessConstruction (M := M) R w :=
  { sample_mem := hw
    prefixEnumeration := F.enumerationOfMem (M := M) hw }

/-- Convert a prefix-enumeration family into the previous sample parse-witness
construction package. -/
def toSampleParseWitnessConstruction
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedPrefixEnumerationFamily (M := M) R) :
    SampleGeneratedSampleParseWitnessConstruction (M := M) R :=
  { prefixEnumeration := fun w hw => F.enumeration w hw }

/-- Convert a prefix-enumeration family directly into sample parse witnesses. -/
def toSampleParseWitnesses
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedPrefixEnumerationFamily (M := M) R) :
    SampleGeneratedSampleParseWitnesses (M := M) R :=
  F.toSampleParseWitnessConstruction.toSampleParseWitnesses

/-- The endpoint listed node associated with a sample word. -/
def endpointOfMem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedPrefixEnumerationFamily (M := M) R)
    {w : Word α} (hw : w ∈ K) :
    ListedSampleGeneratedDecompositionNode R :=
  (F.enumerationOfMem (M := M) hw).endpoint

/-- The endpoint associated with a sample word exposes exactly that word. -/
theorem endpoint_middle_eq_of_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedPrefixEnumerationFamily (M := M) R)
    {w : Word α} (hw : w ∈ K) :
    (F.endpointOfMem (M := M) hw).middle = w := by
  exact (F.enumerationOfMem (M := M) hw).endpoint_middle_eq

/-- The endpoint context associated with a sample word is licensed by the sample
named distribution. -/
theorem endpoint_context_mem_sampleDistribution_of_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedPrefixEnumerationFamily (M := M) R)
    {w : Word α} (hw : w ∈ K) :
    (F.endpointOfMem (M := M) hw).context ∈
      SampleNamedDistribution K (F.endpointOfMem (M := M) hw).tuple := by
  exact (F.endpointOfMem (M := M) hw).context_mem_sampleDistribution

/-- A prefix-enumeration family proves that every sample word lies in the
generated terminal+concat grammar shell. -/
theorem sample_subset_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedPrefixEnumerationFamily (M := M) R) :
    ∀ w : Word α,
      w ∈ K →
        w ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  intro w hw
  exact (F.wordConstructionOfMem (M := M) hw).word_mem_stringLanguage (M := M)

/-- A single sample word from the family is generated by the generated grammar
shell. -/
theorem word_mem_stringLanguage_of_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedPrefixEnumerationFamily (M := M) R)
    {w : Word α} (hw : w ∈ K) :
    w ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact F.sample_subset_stringLanguage (M := M) w hw

end SampleGeneratedPrefixEnumerationFamily

end SampleGeneratedPrefixEnumerationFamily

end FIv21
