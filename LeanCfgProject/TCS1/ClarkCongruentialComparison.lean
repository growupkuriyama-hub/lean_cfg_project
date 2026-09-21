import LeanCfgProject.TCS1.ClarkCongruentialEndpoints
import LeanCfgProject.TCS1.ClarkCongruentialIndexedFacade
import LeanCfgProject.TCS1.DyckOneBracketGrammar

/-!
# TCS #1 v78: Proposition 9.9 comparison facade

This file packages the Section 9 comparison in a representation-level form.

A language has a Clark-congruential presentation here when there exist a
finite nonterminal type, a finite initial set, an exact binary-CFG
presentation, and Clark's one-syntactic-class condition for every
nonterminal.

The indexed theorem covers all target cases.  A target containing a nonempty
word is handled by the concrete SSBNF normalization, yield-typed refinement,
and start-removal construction.  If there is no nonempty word, the language
is either empty or epsilon-only and the explicit endpoint grammars apply.

The one-bracket Dyck theorem packages the properness witness: D1 has a finite
congruential grammar, while no supplied finite-monoid typing makes D1
fixed-h substitutable.
-/

namespace LeanCfgProject
namespace TCS1

universe u s v w x

/-- Existence of a finite Clark-congruential CFG presentation. -/
def ClarkCongruentialRepresentable
    {α : Type u}
    (L : Set (Word α)) : Prop :=
  ∃ State : Type s,
    ∃ _finiteState : Finite State,
    ∃ grammar : BinaryNullableGrammar State α,
    ∃ initial : Set State,
      initial.Finite
        ∧
      InitialSetLanguage grammar initial = L
        ∧
      ClarkCongruentialInitialSet grammar initial

section EndpointRepresentability

variable {α : Type u}

/-- The empty language has a finite congruential presentation. -/
theorem clarkEmpty_representable :
    ClarkCongruentialRepresentable.{u, s}
      (∅ : Set (Word α)) := by
  refine
    ⟨ClarkEndpointState,
      inferInstance,
      clarkEmptyGrammar,
      clarkEndpointInitial,
      clarkEndpointInitial_finite,
      clarkEmptyGrammar_language_eq,
      clarkEmptyGrammar_congruential⟩

/-- The epsilon-only language has a finite congruential presentation. -/
theorem clarkEpsilon_representable :
    ClarkCongruentialRepresentable.{u, s}
      ({[]} : Set (Word α)) := by
  refine
    ⟨ClarkEndpointState,
      inferInstance,
      clarkEpsilonGrammar,
      clarkEndpointInitial,
      clarkEndpointInitial_finite,
      clarkEpsilonGrammar_language_eq,
      clarkEpsilonGrammar_congruential⟩

end EndpointRepresentability

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
Nontrivial case of the inclusion: the normalized typed grammar yields an
explicit finite congruential presentation of the source language.
-/
theorem indexedFixedH_representable_of_nonempty
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
    ClarkCongruentialRepresentable.{
      u, max (max x v) u}
      (LeastClosedLanguage G.toMixedRules A) := by
  have hpack :=
    indexed_fixedH_has_Clark_congruential_packaging
      H G A hprod hsub
  rcases hpack with
    ⟨hfinite, hlang, hcong⟩
  refine
    ⟨IndexedClarkPackagedState H G A hprod,
      ?_,
      indexedClarkPackagedGrammar H G A hprod,
      indexedClarkInitial H G A hprod,
      hfinite,
      hlang,
      hcong⟩
  infer_instance

/--
Full finite-CFG form of the inclusion direction of Proposition 9.9.

No nontriviality assumption remains.  If the source language has a nonempty
word, use the normalized typed refinement.  Otherwise the source is either
empty or epsilon-only.
-/
theorem indexedFixedH_has_ClarkCongruentialPresentation
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A)) :
    ClarkCongruentialRepresentable.{
      u, max (max x v) u}
      (LeastClosedLanguage G.toMixedRules A) := by
  classical
  let L : Set (Word α) :=
    LeastClosedLanguage G.toMixedRules A
  by_cases hprod :
      ∃ z : Word α, z ∈ L ∧ z ≠ []
  · exact
      indexedFixedH_representable_of_nonempty
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
        ClarkCongruentialRepresentable.{
          u, max (max x v) u} L
      rw [hL]
      exact clarkEpsilon_representable
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
        ClarkCongruentialRepresentable.{
          u, max (max x v) u} L
      rw [hL]
      exact clarkEmpty_representable

end

end IndexedComparison

section DyckProperness

/--
Properness witness from Proposition 9.9, stated independently of the chosen
finite monoid: D1 has a finite congruential grammar, yet the supplied
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
