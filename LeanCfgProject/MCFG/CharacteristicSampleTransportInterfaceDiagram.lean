/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.CharacteristicSampleExposingAsCommonContext

/-!
# CharacteristicSampleTransportInterfaceDiagram.lean

Sixty-ninth clean Lean experiment for the fixed-observation MCFG project.

The preceding files introduced several semantic transport interfaces:

* `TrimmedPresentationSameContextTransport`;
* `TrimmedPresentationExposingContextTransport`;
* `TrimmedPresentationAnchorCommonContextTransport`;
* `TrimmedPresentationAnchorDistributionTransport`.

This file records the conversion diagram between them, without adding new
mathematical assumptions.

The useful implication chain is:

```text
SameContextTransport
⇒ ExposingContextTransport
⇒ ExposingAsCommonContext
⇒ AnchorCommonContextTransport
⇒ AnchorDistributionTransport
⇒ ExposingContextTransport.
```

The last arrow uses the already verified distributional-equivalence route.
The resulting cycle is intentional: it lets later semantic work enter from
whichever interface is easiest to prove.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section InterfaceDiagram

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationTransportDiagram

/-- Same-context transport implies exposing-context transport. -/
def sameContext_to_exposing
    (C : TrimmedPresentationSameContextTransport D) :
    TrimmedPresentationExposingContextTransport D :=
  TrimmedPresentationExposingContextTransport.ofSameContextTransport C

/-- Exposing-context transport plus arity positivity gives the
exposing-as-common-context package. -/
def exposing_to_exposingAsCommon
    (E : TrimmedPresentationExposingContextTransport D)
    (hpos : ∀ A : N, 0 < G.arity A) :
    TrimmedPresentationExposingAsCommonContext D where
  arity_pos := hpos
  exposingTransport := E

/-- Exposing-as-common-context data gives common-context transport. -/
def exposingAsCommon_to_common
    (E : TrimmedPresentationExposingAsCommonContext D) :
    TrimmedPresentationAnchorCommonContextTransport D :=
  E.toAnchorCommonContextTransport

/-- Common-context transport gives anchor distributional transport, after
fanout and fixed-observation substitutability are supplied. -/
def common_to_anchorDistribution
    (C : TrimmedPresentationAnchorCommonContextTransport D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationAnchorDistributionTransport D :=
  C.toAnchorDistributionTransport hfan hL

/-- Anchor distributional transport gives exposing-context transport. -/
def anchorDistribution_to_exposing
    (H : TrimmedPresentationAnchorDistributionTransport D) :
    TrimmedPresentationExposingContextTransport D :=
  H.toExposingContextTransport

/-- Same-context transport enters the common-context route after adding arity
positivity. -/
def sameContext_to_exposingAsCommon
    (C : TrimmedPresentationSameContextTransport D)
    (hpos : ∀ A : N, 0 < G.arity A) :
    TrimmedPresentationExposingAsCommonContext D :=
  exposing_to_exposingAsCommon (sameContext_to_exposing C) hpos

/-- Same-context transport gives common-context transport after adding arity
positivity. -/
def sameContext_to_common
    (C : TrimmedPresentationSameContextTransport D)
    (hpos : ∀ A : N, 0 < G.arity A) :
    TrimmedPresentationAnchorCommonContextTransport D :=
  (sameContext_to_exposingAsCommon C hpos).toAnchorCommonContextTransport

/-- Same-context transport gives anchor distributional transport through the
common-context route. -/
def sameContext_to_anchorDistribution
    (C : TrimmedPresentationSameContextTransport D)
    (hpos : ∀ A : N, 0 < G.arity A)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationAnchorDistributionTransport D :=
  (sameContext_to_common C hpos).toAnchorDistributionTransport hfan hL

/-- Exposing-context transport gives anchor distributional transport through
`D.expose A` as the common context. -/
def exposing_to_anchorDistribution
    (E : TrimmedPresentationExposingContextTransport D)
    (hpos : ∀ A : N, 0 < G.arity A)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationAnchorDistributionTransport D :=
  (exposing_to_exposingAsCommon E hpos).toAnchorDistributionTransport hfan hL

/-- The round trip from exposing-context transport through the common-context
and distributional routes returns an exposing-context transport object. -/
def exposing_roundTrip
    (E : TrimmedPresentationExposingContextTransport D)
    (hpos : ∀ A : N, 0 < G.arity A)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingContextTransport D :=
  (exposing_to_anchorDistribution E hpos hfan hL).toExposingContextTransport

/-- The round trip from same-context transport through the common-context and
distributional routes returns an exposing-context transport object. -/
def sameContext_roundTrip_to_exposing
    (C : TrimmedPresentationSameContextTransport D)
    (hpos : ∀ A : N, 0 < G.arity A)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingContextTransport D :=
  (sameContext_to_anchorDistribution C hpos hfan hL).toExposingContextTransport

end TrimmedPresentationTransportDiagram

end InterfaceDiagram


section CoreDataDiagram

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

namespace TrimmedPresentationSameContextCoreData

/-- Same-context core data enters the exposing-as-common route after adding
arity positivity. -/
def toExposingCommonCoreData
    (P : TrimmedPresentationSameContextCoreData D)
    (hpos : ∀ A : N, 0 < G.arity A) :
    TrimmedPresentationExposingCommonCoreData D where
  coreData := P.toExposingTransportCoreData
  arity_pos := hpos

/-- Same-context core data enters the common-context route after adding arity
positivity. -/
def toAnchorCommonContextCoreData
    (P : TrimmedPresentationSameContextCoreData D)
    (hpos : ∀ A : N, 0 < G.arity A) :
    TrimmedPresentationAnchorCommonContextCoreData D :=
  (P.toExposingCommonCoreData hpos).toAnchorCommonContextCoreData

/-- Same-context core data enters the anchor-distribution route through the
common-context bridge. -/
def toAnchorDistributionCoreDataViaCommon
    (P : TrimmedPresentationSameContextCoreData D)
    (hpos : ∀ A : N, 0 < G.arity A)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationAnchorDistributionCoreData D :=
  (P.toExposingCommonCoreData hpos).toAnchorDistributionCoreData hfan hL

/-- Reachable identification through the exposing-as-common route. -/
theorem identifies_from_positive_text_via_common
    (P : TrimmedPresentationSameContextCoreData D)
    (hpos : ∀ A : N, 0 < G.arity A)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (P.toExposingCommonCoreData hpos).identifies_from_positive_text E U hfan hL

/-- Prefix-exact reconstruction through the exposing-as-common route. -/
theorem prefix_exact_eventually_via_common
    (P : TrimmedPresentationSameContextCoreData D)
    (hpos : ∀ A : N, 0 < G.arity A)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toExposingCommonCoreData hpos).prefix_exact_eventually E U hfan hL

end TrimmedPresentationSameContextCoreData

namespace TrimmedPresentationAnchorDistributionCoreData

/-- Anchor-distribution core data can be viewed as exposing-common core data
once arity positivity is supplied. -/
def toExposingCommonCoreData
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (hpos : ∀ A : N, 0 < G.arity A) :
    TrimmedPresentationExposingCommonCoreData D where
  coreData := P.toExposingTransportCoreData
  arity_pos := hpos

/-- Reachable identification from anchor-distribution core data through the
exposing-common view. -/
theorem identifies_from_positive_text_via_exposing_common
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (hpos : ∀ A : N, 0 < G.arity A)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (P.toExposingCommonCoreData hpos).identifies_from_positive_text E U hfan hL

/-- Prefix-exact reconstruction from anchor-distribution core data through the
exposing-common view. -/
theorem prefix_exact_eventually_via_exposing_common
    (P : TrimmedPresentationAnchorDistributionCoreData D)
    (hpos : ∀ A : N, 0 < G.arity A)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toExposingCommonCoreData hpos).prefix_exact_eventually E U hfan hL

end TrimmedPresentationAnchorDistributionCoreData

namespace TrimmedPresentationAnchorCommonContextCoreData

/-- Common-context core data can be viewed as exposing-common core data after
fanout and fixed-observation substitutability are supplied. -/
def toExposingCommonCoreData
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    TrimmedPresentationExposingCommonCoreData D where
  coreData := P.toExposingTransportCoreData hfan hL
  arity_pos := P.commonContext.arity_pos

/-- Reachable identification from common-context core data through the
exposing-common view. -/
theorem identifies_from_positive_text_via_exposing_common
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  (P.toExposingCommonCoreData hfan hL).identifies_from_positive_text
    E U hfan hL

/-- Prefix-exact reconstruction from common-context core data through the
exposing-common view. -/
theorem prefix_exact_eventually_via_exposing_common
    (P : TrimmedPresentationAnchorCommonContextCoreData D)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  (P.toExposingCommonCoreData hfan hL).prefix_exact_eventually
    E U hfan hL

end TrimmedPresentationAnchorCommonContextCoreData

end CoreDataDiagram


section MainDiagramTheorems

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}
variable {T : TrimmedOutputTypePresentation G obs}
variable {D : TrimmedPresentationPreCoreData T f}

/-- Stable top-level reachable identification theorem for the same-context
core route through the common-context diagram. -/
theorem trimmed_transport_diagram_same_context_reachable_identification
    (P : TrimmedPresentationSameContextCoreData D)
    (hpos : ∀ A : N, 0 < G.arity A)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      EventuallyCorrectOnText
        (reachableHypLanguage obs f)
        (reachableSampleLearner (α := α))
        Ttxt :=
  P.identifies_from_positive_text_via_common hpos E U hfan hL

/-- Stable top-level prefix-exact theorem for the same-context core route
through the common-context diagram. -/
theorem trimmed_transport_diagram_same_context_prefix_exact
    (P : TrimmedPresentationSameContextCoreData D)
    (hpos : ∀ A : N, 0 < G.arity A)
    (E : TrimmedPresentationStartWordEvidence D)
    (U : NamedContextSplicingConstructor α)
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage) :
    ∀ Ttxt : TextFor G.StringLanguage,
      ∃ n0 : Nat, ∀ n : Nat, n0 ≤ n →
        ReachableSampleStringLanguage (Ttxt.prefixSample n) obs f =
          G.StringLanguage :=
  P.prefix_exact_eventually_via_common hpos E U hfan hL

end MainDiagramTheorems

end MCFG
