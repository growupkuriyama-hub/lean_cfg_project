import LeanCfgProject.Step25_Test
import Mathlib.CategoryTheory.Category.Basic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

universe u

namespace TwoSidedTypedCFG

open Classical
open CategoryTheory

noncomputable section

/-
  Full architecture test file.

  This file intentionally uses ASCII syntax only.
  It extends the definitions checked in Step25_Test.lean.

  The proof-heavy global categorical/extraction facts are registered as
  axioms here. The purpose of this file is to check that the full
  architecture has coherent Lean types. It is not the final proof file.
-/

namespace ContextCategory

structure ContextPath
    {M : Type u} [Monoid M]
    (X Y : TypedState M) where
  l : M
  r : M
  left_eq : Y.lt = X.lt * l
  right_eq : Y.rt = r * X.rt

def ContextPath.id
    {M : Type u} [Monoid M]
    (X : TypedState M) :
    ContextPath X X :=
  {
    l := 1
    r := 1
    left_eq := by simp
    right_eq := by simp
  }

def ContextPath.comp
    {M : Type u} [Monoid M]
    {X Y Z : TypedState M}
    (f : ContextPath X Y)
    (g : ContextPath Y Z) :
    ContextPath X Z :=
  {
    l := f.l * g.l
    r := g.r * f.r
    left_eq := by
      calc
        Z.lt = Y.lt * g.l := g.left_eq
        _ = (X.lt * f.l) * g.l := by rw [f.left_eq]
        _ = X.lt * (f.l * g.l) := by simp [mul_assoc]
    right_eq := by
      calc
        Z.rt = g.r * Y.rt := g.right_eq
        _ = g.r * (f.r * X.rt) := by rw [f.right_eq]
        _ = (g.r * f.r) * X.rt := by simp [mul_assoc]
  }

axiom typedStateCategory
    {M : Type u} [Monoid M] :
    Category (TypedState M)

attribute [instance] typedStateCategory

end ContextCategory

namespace RuleFamilies

variable {Sigma : Type u}
variable {M : Type u} [Monoid M] [Fintype M]
variable (H : FixedFiniteMonoidHom Sigma M)
variable {W : Type u}
variable (profile : W -> TypedState M)

inductive CarrierIsProductive
    (R : List (CarrierTypedRule H profile)) :
    W -> Prop where
  | terminal
      (tr : CarrierTerminalRule H profile)
      (hmem : List.Mem (CarrierTypedRule.terminal tr) R) :
      CarrierIsProductive R tr.X
  | binary
      (br : CarrierBinaryRule profile)
      (hmem : List.Mem (CarrierTypedRule.binary br) R)
      (hY : CarrierIsProductive R br.Y)
      (hZ : CarrierIsProductive R br.Z) :
      CarrierIsProductive R br.X

inductive CarrierIsReachable
    (R : List (CarrierTypedRule H profile))
    (S : Finset W) :
    W -> Prop where
  | start
      (x : W)
      (hmem : Membership.mem S x) :
      CarrierIsReachable R S x
  | binary_left
      (br : CarrierBinaryRule profile)
      (hmem : List.Mem (CarrierTypedRule.binary br) R)
      (hX : CarrierIsReachable R S br.X) :
      CarrierIsReachable R S br.Y
  | binary_right
      (br : CarrierBinaryRule profile)
      (hmem : List.Mem (CarrierTypedRule.binary br) R)
      (hX : CarrierIsReachable R S br.X) :
      CarrierIsReachable R S br.Z

inductive YieldFamily
    (R : List (CarrierTypedRule H profile)) :
    W -> Word Sigma -> Prop where
  | terminal
      (tr : CarrierTerminalRule H profile)
      (hmem : List.Mem (CarrierTypedRule.terminal tr) R) :
      YieldFamily R tr.X [tr.a]
  | binary
      (br : CarrierBinaryRule profile)
      (hmem : List.Mem (CarrierTypedRule.binary br) R)
      {u v : Word Sigma}
      (hY : YieldFamily R br.Y u)
      (hZ : YieldFamily R br.Z v) :
      YieldFamily R br.X (u ++ v)

inductive ContextFamily
    (R : List (CarrierTypedRule H profile))
    (S : Finset W) :
    W -> Word Sigma -> Word Sigma -> Prop where
  | start
      (x : W)
      (hmem : Membership.mem S x) :
      ContextFamily R S x [] []
  | binary_left
      (br : CarrierBinaryRule profile)
      (hmem : List.Mem (CarrierTypedRule.binary br) R)
      {u v z : Word Sigma}
      (hctx : ContextFamily R S br.X u v)
      (hz : YieldFamily H profile R br.Z z) :
      ContextFamily R S br.Y u (z ++ v)
  | binary_right
      (br : CarrierBinaryRule profile)
      (hmem : List.Mem (CarrierTypedRule.binary br) R)
      {u v y : Word Sigma}
      (hctx : ContextFamily R S br.X u v)
      (hy : YieldFamily H profile R br.Y y) :
      ContextFamily R S br.Z (u ++ y) v

end RuleFamilies

open RuleFamilies

structure FiniteContextStructure
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M) where
  W : Type u
  fintypeW : Fintype W
  profile : W -> TypedState M
  R : List (CarrierTypedRule H profile)
  S : Finset W
  axiomS :
    forall x : W,
      Membership.mem S x ->
        And ((profile x).lt = 1) ((profile x).rt = 1)
  axiomP :
    forall x : W,
      CarrierIsProductive H profile R x
  axiomRch :
    forall x : W,
      CarrierIsReachable H profile R S x

structure WitnessedFiniteContextStructure
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M) where
  W : Type u
  fintypeW : Fintype W
  profile : W -> TypedState M
  R : List (CarrierTypedRule H profile)
  S : Finset W
  axiomS :
    forall x : W,
      Membership.mem S x ->
        And ((profile x).lt = 1) ((profile x).rt = 1)
  axiomP :
    forall x : W,
      CarrierIsProductive H profile R x
  axiomRch :
    forall x : W,
      CarrierIsReachable H profile R S x
  omega : W -> Word Sigma
  chi : W -> Prod (Word Sigma) (Word Sigma)
  axiomOmega :
    forall x : W,
      And
        (YieldFamily H profile R x (omega x))
        (H.h (omega x) = (profile x).yt)
  axiomC :
    forall x : W,
      And
        (ContextFamily H profile R S x (chi x).1 (chi x).2)
        (And
          (H.h (chi x).1 = (profile x).lt)
          (H.h (chi x).2 = (profile x).rt))

namespace WitnessedFiniteContextStructure

def toFinite
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A : WitnessedFiniteContextStructure H) :
    FiniteContextStructure H :=
  {
    W := A.W
    fintypeW := A.fintypeW
    profile := A.profile
    R := A.R
    S := A.S
    axiomS := A.axiomS
    axiomP := A.axiomP
    axiomRch := A.axiomRch
  }

end WitnessedFiniteContextStructure

structure StructureMorphism
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A B : WitnessedFiniteContextStructure H) where
  map : A.W -> B.W
  profile_map :
    forall x : A.W,
      B.profile (map x) = A.profile x
  start_map :
    forall x : A.W,
      Membership.mem A.S x ->
        Membership.mem B.S (map x)
  terminal_map :
    forall tr : CarrierTerminalRule H A.profile,
      List.Mem (CarrierTypedRule.terminal tr) A.R ->
        Exists
          (fun trB : CarrierTerminalRule H B.profile =>
            And
              (trB.X = map tr.X)
              (And
                (trB.a = tr.a)
                (List.Mem (CarrierTypedRule.terminal trB) B.R)))
  binary_map :
    forall br : CarrierBinaryRule A.profile,
      List.Mem (CarrierTypedRule.binary br) A.R ->
        Exists
          (fun brB : CarrierBinaryRule B.profile =>
            And
              (brB.X = map br.X)
              (And
                (brB.Y = map br.Y)
                (And
                  (brB.Z = map br.Z)
                  (List.Mem (CarrierTypedRule.binary brB) B.R))))
  omega_map :
    forall x : A.W,
      B.omega (map x) = A.omega x
  chi_map :
    forall x : A.W,
      B.chi (map x) = A.chi x

axiom witnessedFiniteContextStructureCategory
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M) :
    Category (WitnessedFiniteContextStructure H)

attribute [instance] witnessedFiniteContextStructureCategory

namespace SSBNFGrammar

structure GrammarMorphism
    {Sigma : Type u}
    (G1 G2 : SSBNFGrammar Sigma) where
  map : G1.V -> G2.V
  start_map :
    forall x : G1.V,
      Membership.mem G1.startRules x ->
        Membership.mem G2.startRules (map x)
  terminal_map :
    forall r : Prod G1.V Sigma,
      List.Mem r G1.terminalRules ->
        List.Mem (map r.1, r.2) G2.terminalRules
  binary_map :
    forall r : Prod G1.V (Prod G1.V G1.V),
      List.Mem r G1.binaryRules ->
        List.Mem (map r.1, map r.2.1, map r.2.2) G2.binaryRules

end SSBNFGrammar

axiom ssbnfGrammarCategory
    {Sigma : Type u} :
    Category (SSBNFGrammar Sigma)

attribute [instance] ssbnfGrammarCategory

namespace Realization

variable {Sigma : Type u}
variable {M : Type u} [Monoid M] [Fintype M]
variable (H : FixedFiniteMonoidHom Sigma M)

noncomputable def stateSeparatedGrammar
    (A : WitnessedFiniteContextStructure H) :
    SSBNFGrammar Sigma :=
  {
    V := A.W
    fintypeV := A.fintypeW
    startRules := A.S
    terminalRules :=
      A.R.filterMap
        (fun rule =>
          match rule with
          | CarrierTypedRule.terminal tr => some (tr.X, tr.a)
          | CarrierTypedRule.binary _ => none)
    binaryRules :=
      A.R.filterMap
        (fun rule =>
          match rule with
          | CarrierTypedRule.terminal _ => none
          | CarrierTypedRule.binary br => some (br.X, br.Y, br.Z))
  }

axiom realizationMap
    {A B : WitnessedFiniteContextStructure H}
    (f : StructureMorphism A B) :
    SSBNFGrammar.GrammarMorphism
      (stateSeparatedGrammar H A)
      (stateSeparatedGrammar H B)

axiom realizationFunctor :
    Functor
      (WitnessedFiniteContextStructure H)
      (SSBNFGrammar Sigma)

end Realization

namespace Extraction

open FullTypedRefinement

variable {Sigma : Type u}
variable {M : Type u} [Monoid M] [Fintype M]

noncomputable def extractedS
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    Finset (TrimmedState G H) :=
  Finset.empty

axiom extracted_axiomS
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    forall x : TrimmedState G H,
      Membership.mem (extractedS G H) x ->
        And
          ((extractedProfile G H x).lt = 1)
          ((extractedProfile G H x).rt = 1)

axiom extracted_axiomP
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    forall x : TrimmedState G H,
      CarrierIsProductive H (extractedProfile G H) (extractedR G H) x

axiom extracted_axiomRch
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    forall x : TrimmedState G H,
      CarrierIsReachable H (extractedProfile G H) (extractedR G H) (extractedS G H) x

noncomputable def extractedFiniteContextStructure
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    FiniteContextStructure H :=
  {
    W := TrimmedState G H
    fintypeW := by infer_instance
    profile := extractedProfile G H
    R := extractedR G H
    S := extractedS G H
    axiomS := extracted_axiomS G H
    axiomP := extracted_axiomP G H
    axiomRch := extracted_axiomRch G H
  }

axiom extracted_axiomOmega
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    forall x : TrimmedState G H,
      And
        (YieldFamily H (extractedProfile G H) (extractedR G H) x [])
        (H.h [] = (extractedProfile G H x).yt)

axiom extracted_axiomC
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    forall x : TrimmedState G H,
      And
        (ContextFamily H (extractedProfile G H) (extractedR G H) (extractedS G H) x [] [])
        (And
          (H.h [] = (extractedProfile G H x).lt)
          (H.h [] = (extractedProfile G H x).rt))

noncomputable def extractedWitnessedStructure
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    WitnessedFiniteContextStructure H :=
  {
    W := TrimmedState G H
    fintypeW := by infer_instance
    profile := extractedProfile G H
    R := extractedR G H
    S := extractedS G H
    axiomS := extracted_axiomS G H
    axiomP := extracted_axiomP G H
    axiomRch := extracted_axiomRch G H
    omega := fun _ => []
    chi := fun _ => ([], [])
    axiomOmega := extracted_axiomOmega G H
    axiomC := extracted_axiomC G H
  }

axiom extractionMap
    (G1 G2 : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2) :
    StructureMorphism
      (extractedWitnessedStructure G1 H)
      (extractedWitnessedStructure G2 H)

axiom extractionFunctor
    (H : FixedFiniteMonoidHom Sigma M) :
    Functor
      (SSBNFGrammar Sigma)
      (WitnessedFiniteContextStructure H)

end Extraction

def IsShortlexNormalized
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A : WitnessedFiniteContextStructure H) : Prop :=
  True

structure StructureIso
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A B : WitnessedFiniteContextStructure H) where
  hom : StructureMorphism A B
  inv : StructureMorphism B A
  left_inv : forall x : A.W, inv.map (hom.map x) = x
  right_inv : forall y : B.W, hom.map (inv.map y) = y

axiom extraction_realization_retraction
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A : WitnessedFiniteContextStructure H)
    (hshort : IsShortlexNormalized A) :
    Nonempty
      (StructureIso
        A
        ((Extraction.extractionFunctor H).obj
          ((Realization.realizationFunctor H).obj A)))

end

end TwoSidedTypedCFG
