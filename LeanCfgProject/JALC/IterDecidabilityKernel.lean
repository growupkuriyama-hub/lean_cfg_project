import LeanCfgProject.JALC.IteratorFromDecidableIteratesKernel

namespace LeanCfgProject
namespace JALC
namespace IterDecidabilityKernel

/-
Decidability of finite iterates.

This module proves the generic recursion principle needed before implementing
the productive/reachable iterator: if a step sends decidable predicates to
decidable predicates, then every finite iterate is decidable.
-/

universe u v w

open InverseKernel RoundTripKernel
open FiniteClosureKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel
open FullAlgorithmicAgreementKernel
open ListCertificateKernel
open ListIterateCertificateKernel
open FiniteUniverseListEnumerationKernel
open MonotoneListIteratorKernel
open IteratorFromDecidableIteratesKernel


/--
A predicate transformer preserves decidability if it maps every decidable
predicate to a decidable predicate.
-/
abbrev PreservesDecidablePred
    {α : Type u}
    (F : (α → Prop) → α → Prop) : Type u :=
  ∀ P : α → Prop, DecidablePred P → DecidablePred (F P)


/--
If a step preserves decidability, then every finite iterate of the step is
decidable.
-/
@[reducible]
def decidablePred_iter
    {α : Type u}
    (F : (α → Prop) → α → Prop)
    (pres : PreservesDecidablePred F) :
    ∀ n : Nat, DecidablePred (Iter F n)
  | 0 =>
      fun x => isFalse (by intro h; exact h)
  | Nat.succ n =>
      pres (Iter F n) (decidablePred_iter F pres n)


/-- The previous result as a nonempty package. -/
theorem decidablePred_iter_nonempty
    {α : Type u}
    (F : (α → Prop) → α → Prop)
    (pres : PreservesDecidablePred F)
    (n : Nat) :
    Nonempty (DecidablePred (Iter F n)) :=
  ⟨decidablePred_iter F pres n⟩


/--
Build a list-iterator output from a complete finite universe list and a
decidability-preserving step.
-/
def listIteratorOutput_of_preservesDecidable
    {α : Type u}
    (U : UniverseList α)
    (F : (α → Prop) → α → Prop)
    (pres : PreservesDecidablePred F)
    (n : Nat) :
    ListIteratorOutput F n :=
  listIteratorOutput_of_decidableIterate U F n
    (decidablePred_iter F pres n)


/--
Generic finite iterator package: a complete universe and a
decidability-preserving step supply an iterator output for every finite height.
-/
structure GenericDecidableIteratorData
    {α : Type u}
    (F : (α → Prop) → α → Prop) : Type u where
  univ_list :
    UniverseList α
  preserves_decidable :
    PreservesDecidablePred F


/-- Extract the iterator output at height n from generic decidable iterator data. -/
def GenericDecidableIteratorData.output
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (D : GenericDecidableIteratorData F)
    (n : Nat) :
    ListIteratorOutput F n :=
  listIteratorOutput_of_preservesDecidable
    D.univ_list F D.preserves_decidable n


/-- The output of generic decidable iterator data gives a list certificate. -/
theorem GenericDecidableIteratorData.output_certificate
    {α : Type u}
    {F : (α → Prop) → α → Prop}
    (D : GenericDecidableIteratorData F)
    (n : Nat) :
    Nonempty (ListIterateCertificate F n) :=
  ⟨(D.output n).certificate⟩

end IterDecidabilityKernel
end JALC
end LeanCfgProject
