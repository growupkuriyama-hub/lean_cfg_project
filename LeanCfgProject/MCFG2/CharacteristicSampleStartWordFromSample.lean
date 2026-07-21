/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleExposingCoreFinal

/-!
# CharacteristicSampleStartWordFromSample.lean

Sixty-fourth clean Lean experiment for the fixed-observation MCFG project.

`CharacteristicSampleStartWordEvidence.lean` separated the distinguished
start-word positivity obligation:

```lean
TrimmedPresentationStartWordEvidence
```

This file gives a small, reusable way to obtain that evidence from any positive
finite sample containing the distinguished start word.

This is intentionally modest but useful.  In many construction routes we
already have a positive sample package, a witness-sample package, or a
characteristic-sample object.  Each of those immediately supplies the
start-word evidence needed by the separated exposing-core final route.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section StartWordFromPositiveSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- A positive finite sample containing the distinguished start word. -/
structure TrimmedPresentationStartWordSampleEvidence
    (D : TrimmedPresentationPreCoreData T f)
    (S : Finset (Word α)) where
  sample_positive :
    (S : Set (Word α)) ⊆ G.StringLanguage
  startWord_mem :
    D.startWord ∈ S

namespace TrimmedPresentationStartWordSampleEvidence

/-- The distinguished start word is positive. -/
theorem startWord_positive
    {S : Finset (Word α)}
    (E : TrimmedPresentationStartWordSampleEvidence D S) :
    D.startWord ∈ G.StringLanguage :=
  E.sample_positive E.startWord_mem

/-- Convert positive-sample start-word evidence to the compact start-word
evidence interface. -/
def toStartWordEvidence
    {S : Finset (Word α)}
    (E : TrimmedPresentationStartWordSampleEvidence D S) :
    TrimmedPresentationStartWordEvidence D where
  mem_target := E.startWord_positive

/-- Monotonicity of start-word sample evidence. -/
def mono
    {S K : Finset (Word α)}
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    TrimmedPresentationStartWordSampleEvidence D K where
  sample_positive := hKpos
  startWord_mem := hSK E.startWord_mem

@[simp] theorem mono_toStartWordEvidence
    {S K : Finset (Word α)}
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKpos : (K : Set (Word α)) ⊆ G.StringLanguage) :
    (E.mono hSK hKpos).toStartWordEvidence =
      E.toStartWordEvidence := by
  rfl

end TrimmedPresentationStartWordSampleEvidence

end StartWordFromPositiveSample


section StartWordEvidenceFromExistingPackages

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

namespace TrimmedPresentationSampleData

/-- A trimmed sample-data package supplies start-word sample evidence. -/
def toStartWordSampleEvidence
    (H : TrimmedPresentationSampleData D S) :
    TrimmedPresentationStartWordSampleEvidence D S where
  sample_positive := H.sample_positive
  startWord_mem := H.startWord_mem

/-- A trimmed sample-data package supplies compact start-word evidence. -/
def toStartWordEvidence
    (H : TrimmedPresentationSampleData D S) :
    TrimmedPresentationStartWordEvidence D :=
  H.toStartWordSampleEvidence.toStartWordEvidence

end TrimmedPresentationSampleData

namespace TrimmedPresentationWitnessSample

/-- A witness-sample package supplies start-word sample evidence. -/
def toStartWordSampleEvidence
    (H : TrimmedPresentationWitnessSample D S) :
    TrimmedPresentationStartWordSampleEvidence D S where
  sample_positive := H.sample_positive
  startWord_mem :=
    H.contains_witnesses
      (TrimmedPresentationWitnessWordSet.startWord_mem (D := D))

/-- A witness-sample package supplies compact start-word evidence. -/
def toStartWordEvidence
    (H : TrimmedPresentationWitnessSample D S) :
    TrimmedPresentationStartWordEvidence D :=
  H.toStartWordSampleEvidence.toStartWordEvidence

end TrimmedPresentationWitnessSample

namespace TrimmedPresentationCharacteristicSample

/-- A characteristic-sample object supplies start-word sample evidence. -/
def toStartWordSampleEvidence
    (C : TrimmedPresentationCharacteristicSample D) :
    TrimmedPresentationStartWordSampleEvidence D C.sample where
  sample_positive := C.sample_positive
  startWord_mem := C.startWord_mem

/-- A characteristic-sample object supplies compact start-word evidence. -/
def toStartWordEvidence
    (C : TrimmedPresentationCharacteristicSample D) :
    TrimmedPresentationStartWordEvidence D :=
  C.toStartWordSampleEvidence.toStartWordEvidence

end TrimmedPresentationCharacteristicSample

namespace TrimmedPresentationFiniteSampleBuilder

/-- A finite builder plus positivity supplies start-word sample evidence. -/
def toStartWordSampleEvidence
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage) :
    TrimmedPresentationStartWordSampleEvidence D B.sample where
  sample_positive := hpos
  startWord_mem := B.startWord_mem

/-- A finite builder plus positivity supplies compact start-word evidence. -/
def toStartWordEvidence
    (B : TrimmedPresentationFiniteSampleBuilder D)
    (hpos : (B.sample : Set (Word α)) ⊆ G.StringLanguage) :
    TrimmedPresentationStartWordEvidence D :=
  (B.toStartWordSampleEvidence hpos).toStartWordEvidence

end TrimmedPresentationFiniteSampleBuilder

end StartWordEvidenceFromExistingPackages


section ExposingCoreFromStartWordSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

namespace TrimmedPresentationExposingTransportCoreData

/-- Build separated exposing-core final data using start-word evidence extracted
from any positive finite sample containing the distinguished start word. -/
def toFinalDataOfStartWordSample
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingCoreFinalData D where
  coreData := P
  startEvidence := E.toStartWordEvidence
  splicingConstructor := U
  fanout := hfan
  promise := hL

/-- Eventual prefix-exact reconstruction from exposing-core data and
start-word evidence extracted from a positive finite sample. -/
theorem prefix_exact_eventually_of_startWord_sample
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toFinalDataOfStartWordSample E U hfan hL).prefix_exact_eventually

/-- Reachable Gold identification from exposing-core data and start-word
evidence extracted from a positive finite sample. -/
theorem identifies_from_positive_text_of_startWord_sample
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (P.toFinalDataOfStartWordSample E U hfan hL).identifies_from_positive_text

end TrimmedPresentationExposingTransportCoreData

end ExposingCoreFromStartWordSample


section MainTheoremsFromStartWordSample

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}
variable {S : Finset (Word α)}

/-- Stable top-level reachable identification theorem using start-word evidence
extracted from a positive finite sample. -/
theorem trimmed_exposing_core_startWord_sample_reachable_identification
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.identifies_from_positive_text_of_startWord_sample E U hfan hL

/-- Stable top-level prefix-exact theorem using start-word evidence extracted
from a positive finite sample. -/
theorem trimmed_exposing_core_startWord_sample_reachable_prefix_exact
    (P : TrimmedPresentationExposingTransportCoreData D)
    (E : TrimmedPresentationStartWordSampleEvidence D S)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually_of_startWord_sample E U hfan hL

end MainTheoremsFromStartWordSample

end MCFG
