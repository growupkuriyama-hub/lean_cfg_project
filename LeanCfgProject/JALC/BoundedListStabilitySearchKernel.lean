import LeanCfgProject.JALC.ListStabilityKernel

namespace LeanCfgProject
namespace JALC
namespace BoundedListStabilitySearchKernel

/-
Generic bounded search for finite list-stability witnesses.

This intentionally stays generic.  It does not depend on the concrete full-rule
data layer.  The concrete connection is already handled by
ConcreteListStabilityKernel: once a list-stability proof is supplied, it yields
CertifiedExtraction and then FullKept decidability.
-/

universe u

open FiniteClosureKernel
open FiniteUniverseListEnumerationKernel
open ListStabilityKernel


/-- Finite list agreement is decidable when both predicates are decidable. -/
def decidableAgreeOnListForSearch
    {α : Type u}
    (xs : List α)
    (P Q : α → Prop)
    (Pdec : DecidablePred P)
    (Qdec : DecidablePred Q) :
    Decidable (AgreeOnList xs P Q) :=
  match xs with
  | [] =>
      isTrue (by
        intro x hx
        cases hx)
  | a :: rest =>
      letI : Decidable (P a) := Pdec a
      letI : Decidable (Q a) := Qdec a
      match (inferInstance : Decidable (P a ↔ Q a)) with
      | isFalse hneq =>
          isFalse (by
            intro h
            exact hneq (h a (List.mem_cons.mpr (Or.inl rfl))))
      | isTrue ha =>
          match decidableAgreeOnListForSearch rest P Q Pdec Qdec with
          | isTrue hrest =>
              isTrue (by
                intro x hx
                have hx' : x = a ∨ x ∈ rest := List.mem_cons.mp hx
                cases hx' with
                | inl heq =>
                    subst x
                    exact ha
                | inr hmem =>
                    exact hrest x hmem)
          | isFalse hbad =>
              isFalse (by
                intro h
                exact hbad (by
                  intro x hx
                  exact h x (List.mem_cons.mpr (Or.inr hx))))


/-- List-stability at a fixed height is decidable from predicate deciders. -/
def decidableListStabilityAtForSearch
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (n : Nat)
    (nextDec : DecidablePred (F (Iter F n)))
    (iterDec : DecidablePred (Iter F n)) :
    Decidable
      (AgreeOnList U.support
        (F (Iter F n))
        (Iter F n)) :=
  decidableAgreeOnListForSearch U.support
    (F (Iter F n))
    (Iter F n)
    nextDec
    iterDec


/-- A witness that `F` has stabilized at height `n` on a finite universe list. -/
structure ListStabilityWitness
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop) : Type (u + 1) where
  height :
    Nat
  stable_on_list :
    AgreeOnList U.support
      (F (Iter F height))
      (Iter F height)


/-- Convert a finite list-stability witness into a closure certificate. -/
def closureCertificate_of_listStabilityWitness
    {α : Type u}
    {U : UniverseList α}
    {F : (α → Prop) → α → Prop}
    (W : ListStabilityWitness U F) :
    ClosureCertificate F :=
  closureCertificate_of_listStability U F
    W.height W.stable_on_list


/--
Search for a list-stability witness up to a given fuel.
This is bounded search.  It does not assert that a witness must be found.
-/
def findListStabilityWitness
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (dec :
      ∀ n : Nat,
        Decidable
          (AgreeOnList U.support
            (F (Iter F n))
            (Iter F n))) :
    Nat → Option (ListStabilityWitness U F)
  | 0 =>
      match dec 0 with
      | isTrue h =>
          some { height := 0, stable_on_list := h }
      | isFalse _ =>
          none
  | Nat.succ fuel =>
      match findListStabilityWitness U F dec fuel with
      | some W =>
          some W
      | none =>
          match dec (Nat.succ fuel) with
          | isTrue h =>
              some { height := Nat.succ fuel, stable_on_list := h }
          | isFalse _ =>
              none


/--
A successful bounded search result exposes a closure certificate.
-/
def closureCertificate_of_successfulBoundedSearch
    {α : Type u}
    {U : UniverseList α}
    {F : (α → Prop) → α → Prop}
    (W : ListStabilityWitness U F) :
    ClosureCertificate F :=
  closureCertificate_of_listStabilityWitness W


/--
If a bounded search returns a witness, then that witness gives `StableAt` at
its recorded height.
-/
theorem stableAt_of_listStabilityWitness
    {α : Type u}
    {U : UniverseList α}
    {F : (α → Prop) → α → Prop}
    (W : ListStabilityWitness U F) :
    StableAt F W.height :=
  stableAt_of_listStability U F W.height W.stable_on_list


/--
If a bounded search returns a witness, the corresponding certificate is
available.
-/
theorem boundedSearchWitness_certified
    {α : Type u}
    {U : UniverseList α}
    {F : (α → Prop) → α → Prop}
    (W : ListStabilityWitness U F) :
    StableAt F
      (closureCertificate_of_successfulBoundedSearch W).height :=
  (closureCertificate_of_successfulBoundedSearch W).stable

end BoundedListStabilitySearchKernel
end JALC
end LeanCfgProject
