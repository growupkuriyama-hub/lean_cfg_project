/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.FillingIdentity

/-!
# WitnessedComposition.lean

Seventh clean Lean experiment for the fixed-observation MCFG project.

This file formalizes the composition step used in learner soundness.

Informally, assume a parent context `E` accepts the composed tuple
`ρ(x,y)`.  If `u` is distributionally equivalent to `x` and `v` is
distributionally equivalent to `y`, then the same parent context also accepts
`ρ(u,v)`.  If the target language satisfies the fixed-observation
substitutability promise, this shared parent context then implies

`ρ(u,v) ≡ ρ(x,y)`.

The concrete construction of the child contexts is still abstracted by the
`LeftFillingIdentity` and `RightFillingIdentity` witnesses introduced in
`FillingIdentity.lean`.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section AbstractWitnessedComposition

variable {α : Type u} {M : Type v} [Monoid M]
variable {Ctx : Nat → Type w}

variable (fill : ∀ d : Nat, Ctx d → Tuple α d → Word α)

/-- One-step left replacement inside a witnessed binary composition.

If the parent context accepts `body x y`, and `u ≡ x`, then the parent context
also accepts `body u y`. -/
theorem witnessedComposition_accepts_left_replacement
    {L : Set (Word α)} {obs : α → M}
    {e dB dC : Nat}
    {parent : Ctx e}
    {body : TemplateTuple α e dB dC}
    {x u : Tuple α dB}
    {y : Tuple α dC}
    (Hleft : LeftFillingIdentity fill parent body y)
    (hux : FixedDistributionalEquivalent fill obs L u x)
    (hparent : fill e parent (evalTemplateTuple body x y) ∈ L) :
    fill e parent (evalTemplateTuple body u y) ∈ L :=
  parent_mem_of_left_equiv
    (fill := fill) Hleft hux hparent

/-- One-step right replacement inside a witnessed binary composition.

If the parent context accepts `body u y`, and `v ≡ y`, then the parent context
also accepts `body u v`. -/
theorem witnessedComposition_accepts_right_replacement
    {L : Set (Word α)} {obs : α → M}
    {e dB dC : Nat}
    {parent : Ctx e}
    {body : TemplateTuple α e dB dC}
    {u : Tuple α dB}
    {y v : Tuple α dC}
    (Hright : RightFillingIdentity fill parent body u)
    (hvy : FixedDistributionalEquivalent fill obs L v y)
    (hparent : fill e parent (evalTemplateTuple body u y) ∈ L) :
    fill e parent (evalTemplateTuple body u v) ∈ L :=
  parent_mem_of_right_equiv
    (fill := fill) Hright hvy hparent

/-- Witnessed composition preserves acceptance.

This is the acceptance part of the paper's witnessed-composition lemma:
starting from acceptance of `body x y`, replace the left child by an equivalent
tuple `u`, then replace the right child by an equivalent tuple `v`. -/
theorem witnessedComposition_accepts
    {L : Set (Word α)} {obs : α → M}
    {e dB dC : Nat}
    {parent : Ctx e}
    {body : TemplateTuple α e dB dC}
    {x u : Tuple α dB}
    {y v : Tuple α dC}
    (Hleft : LeftFillingIdentity fill parent body y)
    (Hright : RightFillingIdentity fill parent body u)
    (hux : FixedDistributionalEquivalent fill obs L u x)
    (hvy : FixedDistributionalEquivalent fill obs L v y)
    (hparent : fill e parent (evalTemplateTuple body x y) ∈ L) :
    fill e parent (evalTemplateTuple body u v) ∈ L := by
  have hleft :
      fill e parent (evalTemplateTuple body u y) ∈ L :=
    witnessedComposition_accepts_left_replacement
      (fill := fill) Hleft hux hparent
  exact witnessedComposition_accepts_right_replacement
    (fill := fill) Hright hvy hleft

/-- Witnessed composition preserves fixed-observation distributional
equivalence.

Under the `(f,h)` target promise, if the parent context accepts `body x y`,
then after replacing both children by distributionally equivalent tuples, the
new parent tuple is distributionally equivalent to the old parent tuple. -/
theorem witnessedComposition_preserves_equivalence
    {f e dB dC : Nat}
    {L : Set (Word α)} {obs : α → M}
    (hL : FixedTupleSubstitutable fill f obs L)
    (he : e ≤ f)
    (hpos : 0 < e)
    {parent : Ctx e}
    {body : TemplateTuple α e dB dC}
    {x u : Tuple α dB}
    {y v : Tuple α dC}
    (Hleft : LeftFillingIdentity fill parent body y)
    (Hright : RightFillingIdentity fill parent body u)
    (hux : FixedDistributionalEquivalent fill obs L u x)
    (hvy : FixedDistributionalEquivalent fill obs L v y)
    (hparent : fill e parent (evalTemplateTuple body x y) ∈ L) :
    FixedDistributionalEquivalent fill obs L
      (evalTemplateTuple body u v)
      (evalTemplateTuple body x y) := by
  have hnew :
      fill e parent (evalTemplateTuple body u v) ∈ L :=
    witnessedComposition_accepts
      (fill := fill) Hleft Hright hux hvy hparent
  have htype :
      tupleType obs (evalTemplateTuple body u v) =
        tupleType obs (evalTemplateTuple body x y) :=
    tupleType_evalTemplateTuple_congr obs body hux.1 hvy.1
  exact fixedDistributionalEquivalent_of_common_context
    (fill := fill) hL he hpos htype hnew hparent

end AbstractWitnessedComposition


section NamedWitnessedComposition

variable {α : Type u} {M : Type v} [Monoid M]

/-- Named-context specialization of witnessed-composition acceptance. -/
theorem named_witnessedComposition_accepts
    {L : Set (Word α)} {obs : α → M}
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x u : Tuple α dB}
    {y v : Tuple α dC}
    (Hleft : LeftFillingIdentity namedFill parent body y)
    (Hright : RightFillingIdentity namedFill parent body u)
    (hux : FixedNamedDistributionalEquivalent obs L u x)
    (hvy : FixedNamedDistributionalEquivalent obs L v y)
    (hparent : namedFill e parent (evalTemplateTuple body x y) ∈ L) :
    namedFill e parent (evalTemplateTuple body u v) ∈ L :=
  witnessedComposition_accepts
    (fill := namedFill) Hleft Hright hux hvy hparent

/-- Named-context specialization of witnessed composition preserving
distributional equivalence. -/
theorem named_witnessedComposition_preserves_equivalence
    {f e dB dC : Nat}
    {L : Set (Word α)} {obs : α → M}
    (hL : FixedNamedTupleSubstitutable f obs L)
    (he : e ≤ f)
    (hpos : 0 < e)
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x u : Tuple α dB}
    {y v : Tuple α dC}
    (Hleft : LeftFillingIdentity namedFill parent body y)
    (Hright : RightFillingIdentity namedFill parent body u)
    (hux : FixedNamedDistributionalEquivalent obs L u x)
    (hvy : FixedNamedDistributionalEquivalent obs L v y)
    (hparent : namedFill e parent (evalTemplateTuple body x y) ∈ L) :
    FixedNamedDistributionalEquivalent obs L
      (evalTemplateTuple body u v)
      (evalTemplateTuple body x y) :=
  witnessedComposition_preserves_equivalence
    (fill := namedFill) hL he hpos Hleft Hright hux hvy hparent

end NamedWitnessedComposition


section GrammarWitnessedComposition

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]

/-- Grammar-language specialization of witnessed-composition equivalence.

This is the form closest to the learner-soundness proof: the target language is
`G.StringLanguage`, and the fixed-observation promise is assumed for that
language. -/
theorem grammar_witnessedComposition_preserves_equivalence
    (G : WorkingMCFG N α)
    {f e dB dC : Nat}
    {obs : α → M}
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (he : e ≤ f)
    (hpos : 0 < e)
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x u : Tuple α dB}
    {y v : Tuple α dC}
    (Hleft : LeftFillingIdentity namedFill parent body y)
    (Hright : RightFillingIdentity namedFill parent body u)
    (hux : GrammarNamedDistributionalEquivalent G obs u x)
    (hvy : GrammarNamedDistributionalEquivalent G obs v y)
    (hparent : namedFill e parent (evalTemplateTuple body x y) ∈ G.StringLanguage) :
    GrammarNamedDistributionalEquivalent G obs
      (evalTemplateTuple body u v)
      (evalTemplateTuple body x y) :=
  named_witnessedComposition_preserves_equivalence
    hL he hpos Hleft Hright hux hvy hparent

end GrammarWitnessedComposition

end MCFG
