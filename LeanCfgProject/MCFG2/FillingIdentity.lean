/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.DistributionalEquivalence

/-!
# FillingIdentity.lean

Sixth clean Lean experiment for the fixed-observation MCFG project.

This file prepares the "filling identity" layer used in the learner-soundness
proof.

In the paper, if a parent context `E` surrounds a tuple
`ρ(x,y)`, then by holding `y` fixed and turning the occurrences of the
`x`-variables into holes, one obtains a child context `E_B` satisfying

`E_B[x] = E[ρ(x,y)]`.

Likewise, holding `x` fixed gives a child context `E_C` for the right child.

Constructing the concrete named child context is bookkeeping-heavy, especially
with empty components.  This file therefore introduces a Lean-stable abstract
witness for such identities:

* `LeftFillingIdentity`
* `RightFillingIdentity`

The later named-context construction can produce these witnesses.  The
transport lemmas in this file already give the semantic effect needed for the
next stage: distributional equivalence of a child tuple transports acceptance
of the parent filling.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section TemplateTypeCongruence

variable {α : Type u} {M : Type v} [Monoid M]

/-- If both child tuples have the same componentwise output types, then the
template-composed parent tuples have the same componentwise output types. -/
theorem tupleType_evalTemplateTuple_congr
    {e dB dC : Nat}
    (obs : α → M)
    (body : TemplateTuple α e dB dC)
    {x u : Tuple α dB}
    {y v : Tuple α dC}
    (hx : tupleType obs u = tupleType obs x)
    (hy : tupleType obs v = tupleType obs y) :
    tupleType obs (evalTemplateTuple body u v) =
      tupleType obs (evalTemplateTuple body x y) := by
  rw [evalTemplateTuple_obs obs body u v,
    evalTemplateTuple_obs obs body x y, hx, hy]

/-- Left-child version of output-type congruence. -/
theorem tupleType_evalTemplateTuple_left_congr
    {e dB dC : Nat}
    (obs : α → M)
    (body : TemplateTuple α e dB dC)
    {x u : Tuple α dB}
    (y : Tuple α dC)
    (hx : tupleType obs u = tupleType obs x) :
    tupleType obs (evalTemplateTuple body u y) =
      tupleType obs (evalTemplateTuple body x y) := by
  exact tupleType_evalTemplateTuple_congr obs body hx rfl

/-- Right-child version of output-type congruence. -/
theorem tupleType_evalTemplateTuple_right_congr
    {e dB dC : Nat}
    (obs : α → M)
    (body : TemplateTuple α e dB dC)
    (x : Tuple α dB)
    {y v : Tuple α dC}
    (hy : tupleType obs v = tupleType obs y) :
    tupleType obs (evalTemplateTuple body x v) =
      tupleType obs (evalTemplateTuple body x y) := by
  exact tupleType_evalTemplateTuple_congr obs body rfl hy

end TemplateTypeCongruence


section AbstractFillingIdentity

variable {α : Type u} {Ctx : Nat → Type w}

variable (fill : ∀ d : Nat, Ctx d → Tuple α d → Word α)

/-- A left-child filling identity witness.

Given a parent context of arity `e`, a binary template body
`body : TemplateTuple α e dB dC`, and a fixed right sibling tuple `y`, this
witness stores a context of arity `dB` whose filling agrees with the parent
filling after composing with the template. -/
structure LeftFillingIdentity
    {e dB dC : Nat}
    (parent : Ctx e)
    (body : TemplateTuple α e dB dC)
    (y : Tuple α dC) where
  ctx : Ctx dB
  identity :
    ∀ x : Tuple α dB,
      fill dB ctx x = fill e parent (evalTemplateTuple body x y)

/-- A right-child filling identity witness. -/
structure RightFillingIdentity
    {e dB dC : Nat}
    (parent : Ctx e)
    (body : TemplateTuple α e dB dC)
    (x : Tuple α dB) where
  ctx : Ctx dC
  identity :
    ∀ y : Tuple α dC,
      fill dC ctx y = fill e parent (evalTemplateTuple body x y)

namespace LeftFillingIdentity

variable {fill}
variable {e dB dC : Nat}
variable {parent : Ctx e}
variable {body : TemplateTuple α e dB dC}
variable {y : Tuple α dC}

/-- The defining equation of a left filling identity, as a rewrite lemma. -/
theorem fill_eq
    (H : LeftFillingIdentity fill parent body y)
    (x : Tuple α dB) :
    fill dB H.ctx x = fill e parent (evalTemplateTuple body x y) :=
  H.identity x

end LeftFillingIdentity

namespace RightFillingIdentity

variable {fill}
variable {e dB dC : Nat}
variable {parent : Ctx e}
variable {body : TemplateTuple α e dB dC}
variable {x : Tuple α dB}

/-- The defining equation of a right filling identity, as a rewrite lemma. -/
theorem fill_eq
    (H : RightFillingIdentity fill parent body x)
    (y : Tuple α dC) :
    fill dC H.ctx y = fill e parent (evalTemplateTuple body x y) :=
  H.identity y

end RightFillingIdentity

end AbstractFillingIdentity


section AcceptanceTransport

variable {α : Type u} {M : Type v} [Monoid M]
variable {Ctx : Nat → Type w}

variable (fill : ∀ d : Nat, Ctx d → Tuple α d → Word α)

/-- Left-side filling transport.

If `u` and `x` are distributionally equivalent child tuples, and the parent
filling with `x` and fixed right sibling `y` is accepted, then the parent
filling with `u` and the same sibling is accepted. -/
theorem parent_mem_of_left_equiv
    {L : Set (Word α)} {obs : α → M}
    {e dB dC : Nat}
    {parent : Ctx e}
    {body : TemplateTuple α e dB dC}
    {y : Tuple α dC}
    (H : LeftFillingIdentity fill parent body y)
    {u x : Tuple α dB}
    (hux : FixedDistributionalEquivalent fill obs L u x)
    (hparent : fill e parent (evalTemplateTuple body x y) ∈ L) :
    fill e parent (evalTemplateTuple body u y) ∈ L := by
  have hxCtx : fill dB H.ctx x ∈ L := by
    rw [H.fill_eq x]
    exact hparent
  have huCtx : fill dB H.ctx u ∈ L := by
    exact (FixedDistributionalEquivalent.fill_mem_iff
      (fill := fill) hux H.ctx).2 hxCtx
  rwa [H.fill_eq u] at huCtx

/-- Right-side filling transport.

If `v` and `y` are distributionally equivalent child tuples, and the parent
filling with fixed left sibling `x` and `y` is accepted, then the parent filling
with `x` and `v` is accepted. -/
theorem parent_mem_of_right_equiv
    {L : Set (Word α)} {obs : α → M}
    {e dB dC : Nat}
    {parent : Ctx e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    (H : RightFillingIdentity fill parent body x)
    {v y : Tuple α dC}
    (hvy : FixedDistributionalEquivalent fill obs L v y)
    (hparent : fill e parent (evalTemplateTuple body x y) ∈ L) :
    fill e parent (evalTemplateTuple body x v) ∈ L := by
  have hyCtx : fill dC H.ctx y ∈ L := by
    rw [H.fill_eq y]
    exact hparent
  have hvCtx : fill dC H.ctx v ∈ L := by
    exact (FixedDistributionalEquivalent.fill_mem_iff
      (fill := fill) hvy H.ctx).2 hyCtx
  rwa [H.fill_eq v] at hvCtx

/-- Same as `parent_mem_of_left_equiv`, specialized to named sentence contexts. -/
theorem named_parent_mem_of_left_equiv
    {α : Type u} {M : Type v} [Monoid M]
    {L : Set (Word α)} {obs : α → M}
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {y : Tuple α dC}
    (H : LeftFillingIdentity namedFill parent body y)
    {u x : Tuple α dB}
    (hux : FixedNamedDistributionalEquivalent obs L u x)
    (hparent : namedFill e parent (evalTemplateTuple body x y) ∈ L) :
    namedFill e parent (evalTemplateTuple body u y) ∈ L := by
  exact parent_mem_of_left_equiv
    (fill := namedFill) H hux hparent

/-- Same as `parent_mem_of_right_equiv`, specialized to named sentence contexts. -/
theorem named_parent_mem_of_right_equiv
    {α : Type u} {M : Type v} [Monoid M]
    {L : Set (Word α)} {obs : α → M}
    {e dB dC : Nat}
    {parent : NamedSentenceContext α e}
    {body : TemplateTuple α e dB dC}
    {x : Tuple α dB}
    (H : RightFillingIdentity namedFill parent body x)
    {v y : Tuple α dC}
    (hvy : FixedNamedDistributionalEquivalent obs L v y)
    (hparent : namedFill e parent (evalTemplateTuple body x y) ∈ L) :
    namedFill e parent (evalTemplateTuple body x v) ∈ L := by
  exact parent_mem_of_right_equiv
    (fill := namedFill) H hvy hparent

end AcceptanceTransport

end MCFG
