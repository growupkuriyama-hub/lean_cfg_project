import LeanCfgProject.TCS1.ClarkCongruentialEndpoints
import LeanCfgProject.TCS1.ClarkCongruentialIndexedFacade
import LeanCfgProject.TCS1.DyckOneBracketGrammar

/-!
# TCS #1 v78: Proposition 9.9 comparison facade

This file packages the Section 9 comparison in a representation-level form.

* A congruential presentation records a finite nonterminal type, a finite
  initial set, exact generated-language equality, and Clark's one-syntactic-
  class condition for every nonterminal.
* Every fixed-h substitutable language presented by the repository's finite
  indexed CFG model receives such a presentation.  The proof splits exactly
  into the three semantic cases needed by the normalization pipeline:
  empty, epsilon-only, and a target containing a nonempty word.
* The one-bracket Dyck language has a finite congruential presentation but is
  not fixed-h substitutable for any supplied finite-monoid typing.

Thus the formal statement mirrors Proposition 9.9 at the level of the finite
CFG representation used throughout the Lean development.
-/

namespace LeanCfgProject
namespace TCS1

universe u s v w x

/-- A finite Clark-congruential CFG presentation of a language. -/
structure ClarkCongruentialPresentation
    {α : Type u}
    (L : Set (Word α)) where
  State : Type s
  finiteState : Finite State
  grammar : BinaryNullableGrammar State α
  initial : Set State
  initial_finite : initial.Finite
  language_eq :
    InitialSetLanguage grammar initial = L
  congruential :
    ClarkCongruentialInitialSet grammar initial

section EndpointPresentations

variable {α : Type u}

/-- Finite congruential presentation of the empty language. -/
def clarkEmptyPresentation :
    ClarkCongruentialPresentation
      (∅ : Set (Word α)) where
  State := ClarkEndpointState
  finiteState := inferInstance
  grammar := clarkEmptyGrammar
  initial := clarkEndpointInitial
  initial_finite := clarkEndpointInitial_finite
  language_eq := clarkEmptyGrammar_language_eq
  congruential := clarkEmptyGrammar_congruential

/-- Finite congruential presentation of the epsilon-only language. -/
def clarkEpsilonPresentation :
    ClarkCongruentialPresentation
      ({[]} : Set (Word α)) where
  State := ClarkEndpointState
  finiteState := inferInstance
  grammar := clarkEpsilonGrammar
  initial := clarkEndpointInitial
  initial_finite := clarkEndpointInitial_finite
  language_eq := clarkEpsilonGrammar_language_eq
  congruential := clarkEpsilonGrammar_congruential

end EndpointPresentations

section IndexedComparison

variable {N : Type v}
variable {α : Type u}
variable {P : Type w}
variable {M : Type x}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]
variable [Monoid M] [Fintype M]

noncomputable section

/--
The packaged nonterminal type produced in the nontrivial case of the indexed
normalization theorem.
-/
abbrev IndexedClarkPackagedState
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ z : Word α,
        z ∈ LeastClosedLanguage G.toMixedRules A ∧
        z ≠ []) :=
  ClarkPackagedState
    H
    (indexedClarkTerminalRule G A hprod)
    (indexedClarkBinaryRule G A hprod)
    (indexedClarkStartRule G A hprod)

/--
Nontrivial case: compose the indexed normalization theorem with the finite
initial-set packaging theorem and record the result as one presentation.
-/
def indexedFixedHClarkPresentation_of_nonempty
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ z : Word α,
        z ∈ LeastClosedLanguage G.toMixedRules A ∧
        z ≠ [])
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A)) :
    ClarkCongruentialPresentation
      (LeastClosedLanguage G.toMixedRules A) := by
  have hpack :=
    indexed_fixedH_has_Clark_congruential_packaging
      H G A hprod hsub
  rcases hpack with
    ⟨hfinite, hlang, hcong⟩
  exact
    { State :=
        IndexedClarkPackagedState H G A hprod
      finiteState := by infer_instance
      grammar :=
        indexedClarkPackagedGrammar H G A hprod
      initial :=
        indexedClarkInitial H G A hprod
      initial_finite := hfinite
      language_eq := hlang
      congruential := hcong }

/--
Full finite-CFG form of the inclusion direction of Proposition 9.9.

No nontriviality assumption remains: if the source language has a nonempty
word we use the normalized typed refinement; otherwise it is either empty or
epsilon-only and the explicit endpoint presentations apply.
-/
theorem indexedFixedH_has_ClarkCongruentialPresentation
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A)) :
    ClarkCongruentialPresentation
      (LeastClosedLanguage G.toMixedRules A) := by
  classical
  let L : Set (Word α) :=
    LeastClosedLanguage G.toMixedRules A
  by_cases hprod :
      ∃ z : Word α, z ∈ L ∧ z ≠ []
  · exact
      indexedFixedHClarkPresentation_of_nonempty
        H G A hprod hsub
  · by_cases heps : ([] : Word α) ∈ L
    · have hL :
          L = ({[]} : Set (Word α)) := by
        apply Set.ext
        intro z
        constructor
        · intro hz
          have hz0 : z = [] := by
            by_contra hzne
            exact hprod ⟨z, hz, hzne⟩
          simpa [hz0]
        · intro hz
          have hz0 : z = [] := by
            simpa using hz
          simpa [hz0] using heps
      change
        ClarkCongruentialPresentation L
      rw [hL]
      exact clarkEpsilonPresentation
    · have hL :
          L = (∅ : Set (Word α)) := by
        apply Set.ext
        intro z
        constructor
        · intro hz
          exfalso
          by_cases hz0 : z = []
          · exact heps (hz0 ▸ hz)
          · exact hprod ⟨z, hz, hz0⟩
        · intro hz
          exact False.elim (by simpa using hz)
      change
        ClarkCongruentialPresentation L
      rw [hL]
      exact clarkEmptyPresentation

end

end IndexedComparison

section DyckProperness

/--
Properness witness from Proposition 9.9, stated independently of the chosen
finite monoid: D1 has a finite congruential presentation, while the supplied
arbitrary finite-monoid typing cannot make it fixed-h substitutable.
-/
theorem proposition99_dyck_properness
    {M : Type x} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom
      DyckOne.Symbol M) :
    (DyckOne.initial.Finite
      ∧
      InitialSetLanguage
          DyckOne.binaryGrammar
          DyckOne.initial
        =
      DyckOne.Language
      ∧
      ClarkCongruentialInitialSet
        DyckOne.binaryGrammar
        DyckOne.initial)
      ∧
    ¬ FixedHSubstitutable
      H DyckOne.Language :=
  DyckOne.congruential_but_not_fixedH H

end DyckProperness

end TCS1
end LeanCfgProject
