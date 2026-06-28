import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedPrefixEnumerationFamilyGold

/-!
# FI v2.1 Lean experiment: nonempty sample consistency

The prefix-enumeration family layer proves sample inclusion once every sample
word is equipped with a prefix-node enumeration.  In the terminal+concat branch,
that obligation is naturally nonempty-word shaped: a word can be parsed from
singleton terminal leaves and binary concatenation steps only when the word is
nonempty.

This file isolates the corresponding sample-level side condition.  A
`SampleGeneratedNonemptyPrefixEnumerationFamily` supplies a prefix-node
enumeration for each sample word, but only after using the explicit hypothesis
that the sample contains no empty word.  It then converts to the previous
unconditional family and obtains `K ⊆ L(G_K)` for the generated working grammar
shell.
-/

namespace FIv21

universe u v w

section SampleGeneratedNonemptySampleConsistency

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- A finite word sample is nonempty when no sampled word is the empty word.
This is the natural side condition for the terminal+concat sample-generated
working grammar shell, whose current parse certificates are built from singleton
terminal leaves. -/
def NonemptyWordSample (K : Finset (Word α)) : Prop :=
  ∀ w : Word α, w ∈ K → w ≠ []

namespace NonemptyWordSample

/-- Extract nonemptiness for a member of a nonempty finite sample. -/
theorem of_mem {K : Finset (Word α)}
    (hK : NonemptyWordSample K) {w : Word α} (hw : w ∈ K) :
    w ≠ [] :=
  hK w hw

/-- The empty finite sample is nonempty in the vacuous sense. -/
theorem empty : NonemptyWordSample (∅ : Finset (Word α)) := by
  intro w hw
  simp at hw

/-- Restricting to a subset preserves the nonempty-word property. -/
theorem mono {K K' : Finset (Word α)}
    (hK : NonemptyWordSample K) (hsub : ∀ w : Word α, w ∈ K' → w ∈ K) :
    NonemptyWordSample K' := by
  intro w hw
  exact hK w (hsub w hw)

end NonemptyWordSample

/-- A prefix-enumeration family for samples known to have no empty words.  The
field `enumeration_of_nonempty` records the real parse obligation: for each
sample word, after proving it is nonempty, provide a listed prefix-node
enumeration for that word. -/
structure SampleGeneratedNonemptyPrefixEnumerationFamily
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) where
  nonemptySample : NonemptyWordSample K
  enumeration_of_nonempty :
    ∀ w : Word α, (hw : w ∈ K) → w ≠ [] →
      SampleGeneratedPrefixNodeEnumeration (M := M) R w

namespace SampleGeneratedNonemptyPrefixEnumerationFamily

/-- The enumeration attached to a sample word, using the stored nonempty-sample
hypothesis. -/
def enumerationOfMem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M) R)
    {w : Word α} (hw : w ∈ K) :
    SampleGeneratedPrefixNodeEnumeration (M := M) R w :=
  F.enumeration_of_nonempty w hw (F.nonemptySample w hw)

/-- Forget the nonempty-word side condition after using it to provide an
ordinary prefix-enumeration family. -/
def toPrefixEnumerationFamily
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M) R) :
    SampleGeneratedPrefixEnumerationFamily (M := M) R :=
  { enumeration := fun w hw => F.enumerationOfMem (M := M) hw }

/-- Convert to the previous sample-parse witness construction package. -/
def toSampleParseWitnessConstruction
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M) R) :
    SampleGeneratedSampleParseWitnessConstruction (M := M) R :=
  F.toPrefixEnumerationFamily.toSampleParseWitnessConstruction

/-- Convert to sample parse witnesses. -/
def toSampleParseWitnesses
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M) R) :
    SampleGeneratedSampleParseWitnesses (M := M) R :=
  F.toPrefixEnumerationFamily.toSampleParseWitnesses

/-- The endpoint associated with a sample word exposes exactly that word. -/
theorem endpoint_middle_eq_of_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M) R)
    {w : Word α} (hw : w ∈ K) :
    (F.toPrefixEnumerationFamily.endpointOfMem (M := M) hw).middle = w := by
  exact F.toPrefixEnumerationFamily.endpoint_middle_eq_of_mem (M := M) hw

/-- The endpoint context associated with a sample word is licensed by the sample
named distribution. -/
theorem endpoint_context_mem_sampleDistribution_of_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M) R)
    {w : Word α} (hw : w ∈ K) :
    (F.toPrefixEnumerationFamily.endpointOfMem (M := M) hw).context ∈
      SampleNamedDistribution K
        (F.toPrefixEnumerationFamily.endpointOfMem (M := M) hw).tuple := by
  exact F.toPrefixEnumerationFamily.endpoint_context_mem_sampleDistribution_of_mem
    (M := M) hw

/-- A nonempty prefix-enumeration family proves sample inclusion in the generated
terminal+concat grammar shell. -/
theorem sample_subset_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M) R) :
    ∀ w : Word α,
      w ∈ K →
        w ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact F.toPrefixEnumerationFamily.sample_subset_stringLanguage (M := M)

/-- A single sample word is generated by the generated grammar shell. -/
theorem word_mem_stringLanguage_of_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (F : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M) R)
    {w : Word α} (hw : w ∈ K) :
    w ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact F.sample_subset_stringLanguage (M := M) w hw

end SampleGeneratedNonemptyPrefixEnumerationFamily

/-- Sample consistency package for the generated grammar shell under the
nonempty-word side condition.  This is deliberately phrased as a language-level
statement, matching `PositiveForLanguage`: every sample word is generated by the
sample-generated working grammar. -/
structure SampleGeneratedNonemptySampleConsistency
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K) where
  family : SampleGeneratedNonemptyPrefixEnumerationFamily (M := M) R

namespace SampleGeneratedNonemptySampleConsistency

/-- The underlying nonempty-word condition. -/
def nonemptySample
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (C : SampleGeneratedNonemptySampleConsistency (M := M) R) :
    NonemptyWordSample K :=
  C.family.nonemptySample

/-- Forget to the unconditional prefix-enumeration family. -/
def toPrefixEnumerationFamily
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (C : SampleGeneratedNonemptySampleConsistency (M := M) R) :
    SampleGeneratedPrefixEnumerationFamily (M := M) R :=
  C.family.toPrefixEnumerationFamily

/-- Sample inclusion in the generated grammar shell. -/
theorem sample_subset_stringLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (C : SampleGeneratedNonemptySampleConsistency (M := M) R) :
    ∀ w : Word α,
      w ∈ K →
        w ∈ (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact C.family.sample_subset_stringLanguage (M := M)

/-- The same statement as a `PositiveForLanguage` certificate. -/
theorem positiveForGeneratedLanguage
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {R : SampleGeneratedRuleSkeleton G obs K}
    (C : SampleGeneratedNonemptySampleConsistency (M := M) R) :
    PositiveForLanguage K
      (terminalConcatEnumeratedRuleListPackage (M := M) R).toWorkingMCFG.StringLanguage := by
  exact C.sample_subset_stringLanguage (M := M)

end SampleGeneratedNonemptySampleConsistency

end SampleGeneratedNonemptySampleConsistency

end FIv21
