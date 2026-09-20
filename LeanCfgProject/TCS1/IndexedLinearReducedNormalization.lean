import LeanCfgProject.TCS1.IndexedLinearNormalizationTheorem
import LeanCfgProject.TCS1.UntypedUsefulTrimSize

/-!
# TCS #1: reduced arbitrary-linear normalization package

The specialized normalization theorem constructs a language-equivalent
linear-spine terminal/binary presentation.  The manuscript's Proposition
`linear-normal` additionally performs a final useless-symbol trim and calls
the result reduced.

This module composes the concrete arbitrary-linear normalization with the
generic productive/reachable trim.  The resulting separated-start
presentation

* has exactly the original source language;
* is reduced: every non-start symbol is productive and reachable;
* retains the one-wrapper-child linear-spine shape; and
* has size bounded by an explicit fixed polynomial in the original indexed
  source scale.

The start symbol is represented by the already established separate
`startRule` / `epsilonStart` interface; the non-start state subtype is the
formal counterpart of the manuscript's final trimming step.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedLinearReducedNormalization

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]

/-- Final reduced non-start state type for an arbitrary indexed linear CFG. -/
abbrev IndexedLinearReducedState
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :=
  UntypedUsefulState
    (LinearConstructedTerminalRule
      (G.linearPreparedGrammar hlinear))
    (LinearConstructedBinaryRule
      (G.linearPreparedGrammar hlinear))
    (linearConstructedStartRule
      (G.linearPreparedGrammar hlinear) S)

/-- Terminal rules of the final reduced linear-spine presentation. -/
abbrev indexedLinearReducedTerminalRule
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :=
  untypedUsefulTerminalRule
    (LinearConstructedTerminalRule
      (G.linearPreparedGrammar hlinear))
    (LinearConstructedBinaryRule
      (G.linearPreparedGrammar hlinear))
    (linearConstructedStartRule
      (G.linearPreparedGrammar hlinear) S)

/-- Binary rules of the final reduced linear-spine presentation. -/
abbrev indexedLinearReducedBinaryRule
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :=
  untypedUsefulBinaryRule
    (LinearConstructedTerminalRule
      (G.linearPreparedGrammar hlinear))
    (LinearConstructedBinaryRule
      (G.linearPreparedGrammar hlinear))
    (linearConstructedStartRule
      (G.linearPreparedGrammar hlinear) S)

/-- Start-child relation of the final reduced presentation. -/
abbrev indexedLinearReducedStartRule
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :=
  untypedUsefulStartRule
    (LinearConstructedTerminalRule
      (G.linearPreparedGrammar hlinear))
    (LinearConstructedBinaryRule
      (G.linearPreparedGrammar hlinear))
    (linearConstructedStartRule
      (G.linearPreparedGrammar hlinear) S)

/-- Wrapper predicate inherited by the final reduced state subtype. -/
abbrev indexedLinearReducedWrapper
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :=
  untypedUsefulWrapper
    (LinearConstructedTerminalRule
      (G.linearPreparedGrammar hlinear))
    (LinearConstructedBinaryRule
      (G.linearPreparedGrammar hlinear))
    (linearConstructedStartRule
      (G.linearPreparedGrammar hlinear) S)
    (LinearConstructedWrapper
      (G.linearPreparedGrammar hlinear))

/-- The final reduced presentation generates exactly the source CFG language. -/
theorem indexedLinear_reduced_language_eq_source
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :
    UntypedStartLanguage
        (indexedLinearReducedTerminalRule G hlinear S)
        (indexedLinearReducedBinaryRule G hlinear S)
        (indexedLinearReducedStartRule G hlinear S)
        (G.linearKeepEmpty hlinear S)
      =
    LeastClosedLanguage G.toMixedRules S := by
  calc
    UntypedStartLanguage
        (indexedLinearReducedTerminalRule G hlinear S)
        (indexedLinearReducedBinaryRule G hlinear S)
        (indexedLinearReducedStartRule G hlinear S)
        (G.linearKeepEmpty hlinear S)
      =
    UntypedStartLanguage
        (LinearConstructedTerminalRule
          (G.linearPreparedGrammar hlinear))
        (LinearConstructedBinaryRule
          (G.linearPreparedGrammar hlinear))
        (linearConstructedStartRule
          (G.linearPreparedGrammar hlinear) S)
        (G.linearKeepEmpty hlinear S) :=
      untypedUsefulStartLanguage_eq
        (LinearConstructedTerminalRule
          (G.linearPreparedGrammar hlinear))
        (LinearConstructedBinaryRule
          (G.linearPreparedGrammar hlinear))
        (linearConstructedStartRule
          (G.linearPreparedGrammar hlinear) S)
        (G.linearKeepEmpty hlinear S)
    _ =
      LeastClosedLanguage G.toMixedRules S :=
      indexedLinear_normalization_language_eq
        G hlinear S

/-- The final presentation is reduced in the standard productive/reachable sense. -/
theorem indexedLinear_reduced_isReduced
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :
    UntypedReducedPresentation
      (indexedLinearReducedTerminalRule G hlinear S)
      (indexedLinearReducedBinaryRule G hlinear S)
      (indexedLinearReducedStartRule G hlinear S) := by
  exact
    untypedUseful_reduced
      (LinearConstructedTerminalRule
        (G.linearPreparedGrammar hlinear))
      (LinearConstructedBinaryRule
        (G.linearPreparedGrammar hlinear))
      (linearConstructedStartRule
        (G.linearPreparedGrammar hlinear) S)

/-- Final trimming preserves the required one-wrapper-child linear-spine form. -/
theorem indexedLinear_reduced_shape
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :
    UntypedLinearSpineShape
      (indexedLinearReducedTerminalRule G hlinear S)
      (indexedLinearReducedBinaryRule G hlinear S)
      (indexedLinearReducedWrapper G hlinear S) := by
  exact
    untypedUseful_linearSpineShape
      (LinearConstructedTerminalRule
        (G.linearPreparedGrammar hlinear))
      (LinearConstructedBinaryRule
        (G.linearPreparedGrammar hlinear))
      (linearConstructedStartRule
        (G.linearPreparedGrammar hlinear) S)
      (LinearConstructedWrapper
        (G.linearPreparedGrammar hlinear))
      (linearConstructed_untypedLinearSpineShape
        (G.linearPreparedGrammar hlinear))

/--
Fixed polynomial envelope for the fully reduced normalization.

The inner envelope bounds the prepared grammar produced by epsilon/unit
preprocessing; the outer cubic is the representation-independent cost of
counting actual terminal/binary rules after final useful-state trimming.
-/
def indexedLinearReducedNormalizationEnvelope
    (sourceScale : Nat) : Nat :=
  untypedUsefulGrammarSizeEnvelope
    (linearPreparedEncodingEnvelope sourceScale)

/-- The original alphabet size is bounded by the linear normalization source scale. -/
theorem indexedLinear_alphabet_card_le_sourceScale
    (G : IndexedMixedCFG N α P) :
    Fintype.card α ≤
      G.linearNormalizationSourceScale := by
  unfold IndexedMixedCFG.linearNormalizationSourceScale
  omega

/-- The source scale is no larger than its prepared-grammar polynomial envelope. -/
theorem sourceScale_le_linearPreparedEncodingEnvelope
    (g : Nat) :
    g ≤ linearPreparedEncodingEnvelope g := by
  unfold linearPreparedEncodingEnvelope
  omega

/--
The fully reduced grammar has source-polynomial state-plus-rule size.
-/
theorem indexedLinear_reduced_size_le
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :
    untypedUsefulGrammarSize
        (LinearConstructedTerminalRule
          (G.linearPreparedGrammar hlinear))
        (LinearConstructedBinaryRule
          (G.linearPreparedGrammar hlinear))
        (linearConstructedStartRule
          (G.linearPreparedGrammar hlinear) S)
      ≤
    indexedLinearReducedNormalizationEnvelope
      G.linearNormalizationSourceScale := by
  let g :=
    linearPreparedEncodingEnvelope
      G.linearNormalizationSourceScale
  have hstatePrepared :
      Fintype.card
          (LinearConstructedState
            (G.linearPreparedGrammar hlinear))
        ≤
      (G.linearPreparedGrammar hlinear).encodingScale :=
    linearConstructedState_card_le_scale
      (G.linearPreparedGrammar hlinear)
  have hprepared :
      (G.linearPreparedGrammar hlinear).encodingScale
        ≤ g := by
    simpa [g] using
      indexedLinear_preparedEncodingScale_le
        G hlinear
  have hstate :
      Fintype.card
          (LinearConstructedState
            (G.linearPreparedGrammar hlinear))
        ≤ g :=
    le_trans hstatePrepared hprepared
  have halphaSource :
      Fintype.card α ≤
        G.linearNormalizationSourceScale :=
    indexedLinear_alphabet_card_le_sourceScale G
  have hsource :
      G.linearNormalizationSourceScale ≤ g := by
    simpa [g] using
      sourceScale_le_linearPreparedEncodingEnvelope
        G.linearNormalizationSourceScale
  have halpha :
      Fintype.card α ≤ g :=
    le_trans halphaSource hsource
  have h :=
    untypedUsefulGrammarSize_le_envelope
      (LinearConstructedTerminalRule
        (G.linearPreparedGrammar hlinear))
      (LinearConstructedBinaryRule
        (G.linearPreparedGrammar hlinear))
      (linearConstructedStartRule
        (G.linearPreparedGrammar hlinear) S)
      g hstate halpha
  simpa [indexedLinearReducedNormalizationEnvelope, g]
    using h

/--
Paper-facing reduced normalization package, now including the manuscript's
final trimming conclusion explicitly.
-/
theorem indexedLinear_reduced_normalization_source_package
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :
    UntypedStartLanguage
        (indexedLinearReducedTerminalRule G hlinear S)
        (indexedLinearReducedBinaryRule G hlinear S)
        (indexedLinearReducedStartRule G hlinear S)
        (G.linearKeepEmpty hlinear S)
      =
    LeastClosedLanguage G.toMixedRules S
    ∧
    UntypedReducedPresentation
      (indexedLinearReducedTerminalRule G hlinear S)
      (indexedLinearReducedBinaryRule G hlinear S)
      (indexedLinearReducedStartRule G hlinear S)
    ∧
    UntypedLinearSpineShape
      (indexedLinearReducedTerminalRule G hlinear S)
      (indexedLinearReducedBinaryRule G hlinear S)
      (indexedLinearReducedWrapper G hlinear S)
    ∧
    untypedUsefulGrammarSize
        (LinearConstructedTerminalRule
          (G.linearPreparedGrammar hlinear))
        (LinearConstructedBinaryRule
          (G.linearPreparedGrammar hlinear))
        (linearConstructedStartRule
          (G.linearPreparedGrammar hlinear) S)
      ≤
    indexedLinearReducedNormalizationEnvelope
      G.linearNormalizationSourceScale := by
  exact
    ⟨indexedLinear_reduced_language_eq_source
        G hlinear S,
      indexedLinear_reduced_isReduced
        G hlinear S,
      indexedLinear_reduced_shape
        G hlinear S,
      indexedLinear_reduced_size_le
        G hlinear S⟩

end IndexedLinearReducedNormalization

end TCS1
end LeanCfgProject
