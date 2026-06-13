import LeanCfgProject.JALC.MonotoneListIteratorKernel

namespace LeanCfgProject
namespace JALC
namespace FiniteUniverseListEnumerationKernel

/-
Finite universe list enumeration boundary.

This module records a finite list interface for a universe.  From a complete
universe list one can build list certificates for filtered predicates, provided
the predicate is decidable.
-/

universe u v w

open InverseKernel RoundTripKernel
open ListCertificateKernel
open MonotoneListIteratorKernel


/-- Convert a decidability value into the Boolean expected by List.filter. -/
def boolOfDecision {p : Prop} : Decidable p → Bool
  | isTrue _ => true
  | isFalse _ => false


/-- A finite list enumerating all elements of a type. -/
structure UniverseList (α : Type u) : Type u where
  support : List α
  complete : ∀ x : α, x ∈ support


/-- Filter a complete universe list by a decidable predicate. -/
def filteredListCertificate
    {α : Type u}
    (U : UniverseList α)
    (P : α → Prop)
    (dec : DecidablePred P) :
    ListPredicateCertificate P :=
  { support := U.support.filter (fun x => boolOfDecision (dec x)),
    sound := by
      intro x hx
      have hb : boolOfDecision (dec x) = true :=
        (List.mem_filter.mp hx).2
      cases h : dec x with
      | isTrue hp =>
          exact hp
      | isFalse hn =>
          simp [boolOfDecision, h] at hb
    complete := by
      intro x hp
      apply List.mem_filter.mpr
      constructor
      · exact U.complete x
      · cases h : dec x with
        | isTrue hp' =>
            simp [boolOfDecision, h]
        | isFalse hn =>
            exact False.elim (hn hp) }


/-- A complete universe list gives a decidability package for any filtered predicate. -/
theorem filteredListCertificate_decidable
    {α : Type u}
    [DecidableEq α]
    (U : UniverseList α)
    (P : α → Prop)
    (dec : DecidablePred P) :
    Nonempty (DecidablePred P) :=
  ⟨decidablePred_of_listCertificate
    (filteredListCertificate U P dec)⟩


/-- Universe list for typed states, used by later finite enumerators. -/
abbrev TypedStateUniverseList (V : Type u) (M : Type v) :=
  UniverseList (TypedState V M)


/-- Universe list for binary triples of typed states. -/
abbrev BinaryTripleUniverseList (V : Type u) (M : Type v) :=
  UniverseList (ListCertificateKernel.BinaryTriple V M)


/--
A typed-state universe list and a binary-triple universe list are the finite
enumeration payload needed by later rule-predicate list certificates.
-/
structure FullRuleUniverseLists
    (V : Type u)
    (M : Type v) : Type (max u v) where
  states :
    TypedStateUniverseList V M
  triples :
    BinaryTripleUniverseList V M


/-- The state universe list is available from the bundled rule-universe lists. -/
theorem fullRuleUniverseLists_states_complete
    {V : Type u} {M : Type v}
    (U : FullRuleUniverseLists V M) :
    ∀ s : TypedState V M, s ∈ U.states.support :=
  U.states.complete

end FiniteUniverseListEnumerationKernel
end JALC
end LeanCfgProject
