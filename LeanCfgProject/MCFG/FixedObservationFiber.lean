/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.OutputTypeLift

/-!
# FixedObservationFiber.lean

Fifth clean Lean experiment for the fixed-observation MCFG project.

This file introduces the Lean counterpart of the paper's fixed observation
fiber `C^{mcf}_{f,h}`.

The definition is intentionally presentation-relative:

* there exists a working MCFG presentation;
* the presentation satisfies the exact working conditions developed so far;
* all nonterminal arities are bounded by `f`;
* the generated string language is the target language;
* the target language satisfies fixed named tuple substitutability for `obs`.

This matches the paper's semantic viewpoint: the substitutability condition is
a property of the generated language, not an effectively checkable syntactic
condition on the grammar.

The file also records the monotonicity of the fiber under refinement of the
fixed finite observation.
-/

namespace MCFG

universe u v w z

section Fiber

variable {α : Type u} {M : Type v} [Monoid M]

/-- A grammar presentation witnesses membership in the fixed observation fiber. -/
def WitnessesFixedObservationFiber
    (f : Nat) (obs : α → M) (L : Set (Word α))
    {N : Type w} (G : WorkingMCFG N α) : Prop :=
  G.FanoutAtMost f ∧
  G.ExactWorkingConditions ∧
  G.StringLanguage = L ∧
  FixedNamedTupleSubstitutable f obs L

/-- The fixed observation MCFG fiber.

This is the formal counterpart of the paper's class `C^{mcf}_{f,h}`, except that
the finite nature of the observation monoid is not needed for the semantic
lemmas in this file.  Later algorithmic files may add `[Fintype M]` when actual
enumeration is required. -/
def FixedObservationFiber
    (f : Nat) (obs : α → M) (L : Set (Word α)) : Prop :=
  ∃ (N : Type w), ∃ G : WorkingMCFG N α,
    WitnessesFixedObservationFiber f obs L G

/-- Extract the fan-out bound from a witnessing presentation. -/
theorem WitnessesFixedObservationFiber.fanout
    {f : Nat} {obs : α → M} {L : Set (Word α)}
    {N : Type w} {G : WorkingMCFG N α}
    (h : WitnessesFixedObservationFiber f obs L G) :
    G.FanoutAtMost f :=
  h.1

/-- Extract exact working conditions from a witnessing presentation. -/
theorem WitnessesFixedObservationFiber.exactWorking
    {f : Nat} {obs : α → M} {L : Set (Word α)}
    {N : Type w} {G : WorkingMCFG N α}
    (h : WitnessesFixedObservationFiber f obs L G) :
    G.ExactWorkingConditions :=
  h.2.1

/-- Extract the language equation from a witnessing presentation. -/
theorem WitnessesFixedObservationFiber.language_eq
    {f : Nat} {obs : α → M} {L : Set (Word α)}
    {N : Type w} {G : WorkingMCFG N α}
    (h : WitnessesFixedObservationFiber f obs L G) :
    G.StringLanguage = L :=
  h.2.2.1

/-- Extract semantic fixed-observation substitutability from a witness. -/
theorem WitnessesFixedObservationFiber.substitutable
    {f : Nat} {obs : α → M} {L : Set (Word α)}
    {N : Type w} {G : WorkingMCFG N α}
    (h : WitnessesFixedObservationFiber f obs L G) :
    FixedNamedTupleSubstitutable f obs L :=
  h.2.2.2

/-- A witnessing presentation also satisfies the basic working conditions from
the first experiment. -/
theorem WitnessesFixedObservationFiber.basicWorking
    {f : Nat} {obs : α → M} {L : Set (Word α)}
    {N : Type w} {G : WorkingMCFG N α}
    (h : WitnessesFixedObservationFiber f obs L G) :
    G.BasicWorkingConditions :=
  h.exactWorking.basic

/-- Repackage explicit witness data as fiber membership. -/
theorem FixedObservationFiber.of_witness
    {f : Nat} {obs : α → M} {L : Set (Word α)}
    {N : Type w} {G : WorkingMCFG N α}
    (h : WitnessesFixedObservationFiber f obs L G) :
    FixedObservationFiber (w := w) f obs L := by
  exact ⟨N, G, h⟩

/-- Unpack fiber membership into an explicit witnessing presentation. -/
theorem FixedObservationFiber.exists_witness
    {f : Nat} {obs : α → M} {L : Set (Word α)}
    (h : FixedObservationFiber (w := w) f obs L) :
    ∃ (N : Type w), ∃ G : WorkingMCFG N α,
      WitnessesFixedObservationFiber f obs L G :=
  h

end Fiber


section FiberMonotonicity

variable {α : Type u}
variable {M : Type v} {M' : Type w}
variable [Monoid M] [Monoid M']

/-- A fixed-observation witness is preserved when the observation is refined. -/
theorem WitnessesFixedObservationFiber.of_refines
    {f : Nat} {obs : α → M} {obs' : α → M'} {L : Set (Word α)}
    {N : Type z} {G : WorkingMCFG N α}
    (r : Refines obs obs')
    (h : WitnessesFixedObservationFiber f obs L G) :
    WitnessesFixedObservationFiber f obs' L G := by
  refine ⟨h.fanout, h.exactWorking, h.language_eq, ?_⟩
  exact fixedNamedTupleSubstitutable_of_refines r h.substitutable

/-- Monotonicity of the fixed observation fiber under refinement.

If `obs'` refines `obs`, then every language in the `obs`-fiber is also in the
`obs'`-fiber. -/
theorem FixedObservationFiber.of_refines
    {f : Nat} {obs : α → M} {obs' : α → M'} {L : Set (Word α)}
    (r : Refines obs obs')
    (h : FixedObservationFiber (w := z) f obs L) :
    FixedObservationFiber (w := z) f obs' L := by
  rcases h with ⟨N, G, hG⟩
  exact ⟨N, G, WitnessesFixedObservationFiber.of_refines r hG⟩

end FiberMonotonicity


section FiberLanguageTransport

variable {α : Type u} {M : Type v} [Monoid M]

/-- Transport a fixed-observation witness across equality of target languages.

This is a small convenience lemma for later files, where the target language may
be rewritten from `G.StringLanguage` to a named set `L`. -/
theorem WitnessesFixedObservationFiber.language_mono
    {f : Nat} {obs : α → M} {L L' : Set (Word α)}
    {N : Type w} {G : WorkingMCFG N α}
    (h : WitnessesFixedObservationFiber f obs L G)
    (hLL' : L = L') :
    WitnessesFixedObservationFiber f obs L' G := by
  subst hLL'
  exact h

/-- If a grammar witnesses the fiber for its own string language, it witnesses
the fiber for any definitionally equal target language. -/
theorem FixedObservationFiber.of_language_eq
    {f : Nat} {obs : α → M} {L : Set (Word α)}
    {N : Type w} {G : WorkingMCFG N α}
    (hfan : G.FanoutAtMost f)
    (hexact : G.ExactWorkingConditions)
    (hsub : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    (hL : G.StringLanguage = L) :
    FixedObservationFiber (w := w) f obs L := by
  refine ⟨N, G, ?_⟩
  refine ⟨hfan, hexact, hL, ?_⟩
  rw [← hL]
  exact hsub

end FiberLanguageTransport

end MCFG
