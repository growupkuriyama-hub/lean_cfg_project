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
  { support := U.support.filter (fun x => dec x),
    sound := by
      intro x hx
      exact (List.mem_filter.1 hx).2
    complete := by
      intro x hp
      exact List.mem_filter.2 ⟨U.complete x, hp⟩ }


/-- A complete universe list gives decidability of equality-filtered membership predicates. -/
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
