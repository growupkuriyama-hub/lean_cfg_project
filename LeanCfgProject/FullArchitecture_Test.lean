import LeanCfgProject.Step25_Test
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.style.openClassical false
set_option linter.style.whitespace false
set_option linter.style.multiGoal false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

universe u

namespace TwoSidedTypedCFG

open Classical
open CategoryTheory

noncomputable section

namespace ContextCategory

@[ext]
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

instance typedStateCategory
    {M : Type u} [Monoid M] :
    Category (TypedState M) where
  Hom X Y := ContextPath X Y
  id X := ContextPath.id X
  comp f g := ContextPath.comp f g
  id_comp := by
    intro X Y f
    ext <;> simp [ContextPath.id, ContextPath.comp]
  comp_id := by
    intro X Y f
    ext <;> simp [ContextPath.id, ContextPath.comp]
  assoc := by
    intro W X Y Z f g h
    ext <;> simp [ContextPath.comp, mul_assoc]

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

theorem carrier_productive_has_yield
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    {W : Type u}
    {profile : W -> TypedState M}
    {R : List (CarrierTypedRule H profile)}
    {x : W}
    (hp : CarrierIsProductive H profile R x) :
    Exists
      (fun w : Word Sigma =>
        YieldFamily H profile R x w) := by
  induction hp with
  | terminal tr hmem =>
      exact Exists.intro [tr.a] (YieldFamily.terminal tr hmem)
  | binary br hmem hY hZ ihY ihZ =>
      cases ihY with
      | intro u hu =>
        cases ihZ with
        | intro v hv =>
          exact Exists.intro (u ++ v) (YieldFamily.binary br hmem hu hv)

theorem carrier_reachable_has_context
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    {W : Type u}
    {profile : W -> TypedState M}
    {R : List (CarrierTypedRule H profile)}
    {S : Finset W}
    (axP : forall x : W, CarrierIsProductive H profile R x)
    {x : W}
    (hr : CarrierIsReachable H profile R S x) :
    Exists
      (fun c : Prod (Word Sigma) (Word Sigma) =>
        ContextFamily H profile R S x c.1 c.2) := by
  induction hr with
  | start x hmem =>
      exact Exists.intro ([], []) (ContextFamily.start x hmem)
  | binary_left br hmem hX ihX =>
      cases ihX with
      | intro ctx hctx =>
        have hpZ : CarrierIsProductive H profile R br.Z :=
          axP br.Z
        cases carrier_productive_has_yield hpZ with
        | intro z hz =>
          exact
            Exists.intro
              (ctx.1, z ++ ctx.2)
              (ContextFamily.binary_left br hmem hctx hz)
  | binary_right br hmem hX ihX =>
      cases ihX with
      | intro ctx hctx =>
        have hpY : CarrierIsProductive H profile R br.Y :=
          axP br.Y
        cases carrier_productive_has_yield hpY with
        | intro y hy =>
          exact
            Exists.intro
              (ctx.1 ++ y, ctx.2)
              (ContextFamily.binary_right br hmem hctx hy)

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

theorem finiteContext_has_yield
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A : FiniteContextStructure H)
    (x : A.W) :
    Exists
      (fun w : Word Sigma =>
        YieldFamily H A.profile A.R x w) :=
  carrier_productive_has_yield (A.axiomP x)

theorem finiteContext_has_context
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A : FiniteContextStructure H)
    (x : A.W) :
    Exists
      (fun c : Prod (Word Sigma) (Word Sigma) =>
        ContextFamily H A.profile A.R A.S x c.1 c.2) :=
  carrier_reachable_has_context A.axiomP (A.axiomRch x)

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

/-- Morphisms preserve the finite typed rule structure. The witness choices `omega` and
`chi` are proof data of objects, not functorial data of morphisms. -/
@[ext]
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

namespace StructureMorphism

def id
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A : WitnessedFiniteContextStructure H) :
    StructureMorphism A A :=
  {
    map := fun x => x
    profile_map := by
      intro x
      rfl
    start_map := by
      intro x hx
      exact hx
    terminal_map := by
      intro tr hmem
      apply Exists.intro tr
      apply And.intro
      exact rfl
      apply And.intro
      exact rfl
      exact hmem
    binary_map := by
      intro br hmem
      apply Exists.intro br
      apply And.intro
      exact rfl
      apply And.intro
      exact rfl
      apply And.intro
      exact rfl
      exact hmem
  }

def comp
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    {A B C : WitnessedFiniteContextStructure H}
    (f : StructureMorphism A B)
    (g : StructureMorphism B C) :
    StructureMorphism A C :=
  {
    map := fun x => g.map (f.map x)
    profile_map := by
      intro x
      exact (g.profile_map (f.map x)).trans (f.profile_map x)
    start_map := by
      intro x hx
      exact g.start_map (f.map x) (f.start_map x hx)
    terminal_map := by
      intro trA hmemA
      cases f.terminal_map trA hmemA with
      | intro trB hB =>
        cases hB with
        | intro hBX hBrest =>
          cases hBrest with
          | intro hBa hBmem =>
            cases g.terminal_map trB hBmem with
            | intro trC hC =>
              cases hC with
              | intro hCX hCrest =>
                cases hCrest with
                | intro hCa hCmem =>
                  apply Exists.intro trC
                  apply And.intro
                  calc
                    trC.X = g.map trB.X := hCX
                    _ = g.map (f.map trA.X) := by rw [hBX]
                  apply And.intro
                  calc
                    trC.a = trB.a := hCa
                    _ = trA.a := hBa
                  exact hCmem
    binary_map := by
      intro brA hmemA
      cases f.binary_map brA hmemA with
      | intro brB hB =>
        cases hB with
        | intro hBX hBrest1 =>
          cases hBrest1 with
          | intro hBY hBrest2 =>
            cases hBrest2 with
            | intro hBZ hBmem =>
              cases g.binary_map brB hBmem with
              | intro brC hC =>
                cases hC with
                | intro hCX hCrest1 =>
                  cases hCrest1 with
                  | intro hCY hCrest2 =>
                    cases hCrest2 with
                    | intro hCZ hCmem =>
                      apply Exists.intro brC
                      apply And.intro
                      calc
                        brC.X = g.map brB.X := hCX
                        _ = g.map (f.map brA.X) := by rw [hBX]
                      apply And.intro
                      calc
                        brC.Y = g.map brB.Y := hCY
                        _ = g.map (f.map brA.Y) := by rw [hBY]
                      apply And.intro
                      calc
                        brC.Z = g.map brB.Z := hCZ
                        _ = g.map (f.map brA.Z) := by rw [hBZ]
                      exact hCmem
  }

end StructureMorphism

instance witnessedFiniteContextStructureCategory
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M) :
    Category (WitnessedFiniteContextStructure H) where
  Hom A B := StructureMorphism A B
  id A := StructureMorphism.id A
  comp f g := StructureMorphism.comp f g
  id_comp := by
    intro A B f
    ext x
    rfl
  comp_id := by
    intro A B f
    ext x
    rfl
  assoc := by
    intro A B C D f g h
    ext x
    rfl

namespace SSBNFGrammar

@[ext]
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

def GrammarMorphism.id
    {Sigma : Type u}
    (G : SSBNFGrammar Sigma) :
    GrammarMorphism G G :=
  {
    map := fun x => x
    start_map := by
      intro x hx
      exact hx
    terminal_map := by
      intro r hr
      simpa using hr
    binary_map := by
      intro r hr
      simpa using hr
  }

def GrammarMorphism.comp
    {Sigma : Type u}
    {G1 G2 G3 : SSBNFGrammar Sigma}
    (f : GrammarMorphism G1 G2)
    (g : GrammarMorphism G2 G3) :
    GrammarMorphism G1 G3 :=
  {
    map := fun x => g.map (f.map x)
    start_map := by
      intro x hx
      exact g.start_map (f.map x) (f.start_map x hx)
    terminal_map := by
      intro r hr
      exact g.terminal_map (f.map r.1, r.2) (f.terminal_map r hr)
    binary_map := by
      intro r hr
      exact g.binary_map (f.map r.1, f.map r.2.1, f.map r.2.2) (f.binary_map r hr)
  }

end SSBNFGrammar

instance ssbnfGrammarCategory
    {Sigma : Type u} :
    Category (SSBNFGrammar Sigma) where
  Hom G1 G2 := SSBNFGrammar.GrammarMorphism G1 G2
  id G := SSBNFGrammar.GrammarMorphism.id G
  comp f g := SSBNFGrammar.GrammarMorphism.comp f g
  id_comp := by
    intro G1 G2 f
    ext x
    rfl
  comp_id := by
    intro G1 G2 f
    ext x
    rfl
  assoc := by
    intro G1 G2 G3 G4 f g h
    ext x
    rfl

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

noncomputable def realizationMap
    {A B : WitnessedFiniteContextStructure H}
    (f : StructureMorphism A B) :
    SSBNFGrammar.GrammarMorphism
      (stateSeparatedGrammar H A)
      (stateSeparatedGrammar H B) :=
  {
    map := f.map
    start_map := by
      intro x hx
      exact f.start_map x hx
    terminal_map := by
      intro r hr
      dsimp [stateSeparatedGrammar] at hr
      dsimp [stateSeparatedGrammar]
      cases List.mem_filterMap.mp hr with
      | intro rule h1 =>
        cases h1 with
        | intro hRule hSome =>
          cases rule with
          | terminal tr =>
            simp only at hSome
            cases hSome
            cases f.terminal_map tr hRule with
            | intro trB hB =>
              cases hB with
              | intro hBX hBrest =>
                cases hBrest with
                | intro hBa hBmem =>
                  apply List.mem_filterMap.mpr
                  apply Exists.intro (CarrierTypedRule.terminal trB)
                  apply And.intro
                  exact hBmem
                  dsimp
                  rw [hBX, hBa]
          | binary br =>
            simp at hSome
    binary_map := by
      intro r hr
      dsimp [stateSeparatedGrammar] at hr
      dsimp [stateSeparatedGrammar]
      cases List.mem_filterMap.mp hr with
      | intro rule h1 =>
        cases h1 with
        | intro hRule hSome =>
          cases rule with
          | terminal tr =>
            simp at hSome
          | binary br =>
            simp only at hSome
            cases hSome
            cases f.binary_map br hRule with
            | intro brB hB =>
              cases hB with
              | intro hBX hBrest1 =>
                cases hBrest1 with
                | intro hBY hBrest2 =>
                  cases hBrest2 with
                  | intro hBZ hBmem =>
                    apply List.mem_filterMap.mpr
                    apply Exists.intro (CarrierTypedRule.binary brB)
                    apply And.intro
                    exact hBmem
                    dsimp
                    rw [hBX, hBY, hBZ]
  }

noncomputable def realizationFunctor :
    CategoryTheory.Functor
      (WitnessedFiniteContextStructure H)
      (SSBNFGrammar Sigma) :=
  {
    obj := fun A => stateSeparatedGrammar H A
    map := fun {A B} f => realizationMap H f
    map_id := by
      intro A
      apply SSBNFGrammar.GrammarMorphism.ext
      funext x
      rfl
    map_comp := by
      intro A B C f g
      apply SSBNFGrammar.GrammarMorphism.ext
      funext x
      rfl
  }

end Realization

namespace Extraction

open FullTypedRefinement

variable {Sigma : Type u}
variable {M : Type u} [Monoid M] [Fintype M]

@[reducible]
noncomputable def trimmedStateFintype
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    Fintype (TrimmedState G H) := by
  classical
  unfold TrimmedState
  infer_instance

noncomputable def extractedS
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    Finset (TrimmedState G H) := by
  classical
  letI : Fintype (TrimmedState G H) := trimmedStateFintype G H
  exact
    (Finset.univ : Finset (TrimmedState G H)).filter
      (fun x =>
        And
          ((extractedProfile G H x).lt = 1)
          ((extractedProfile G H x).rt = 1))

theorem extracted_axiomS
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    forall x : TrimmedState G H,
      Membership.mem (extractedS G H) x ->
        And
          ((extractedProfile G H x).lt = 1)
          ((extractedProfile G H x).rt = 1) := by
  intro x hx
  classical
  unfold extractedS at hx
  simpa using (Finset.mem_filter.mp hx).2

theorem reachable_implies_productive
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    {X : FullTypedState G M}
    (hreach : IsReachable G H X) :
    IsProductive G H X := by
  induction hreach with
  | start A p hstart hprod =>
      exact hprod
  | binary_left hmem hX hYprod hZprod ihX =>
      exact hYprod
  | binary_right hmem hX hYprod hZprod ihX =>
      exact hZprod

theorem extracted_axiomP
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    forall x : TrimmedState G H,
      CarrierIsProductive H (extractedProfile G H) (extractedR G H) x := by
  intro x
  classical
  cases x with
  | mk X hsurv =>
      exact
        IsProductive.rec
          (motive := fun X hprod =>
            forall hreach : IsReachable G H X,
              CarrierIsProductive H (extractedProfile G H) (extractedR G H)
                ({ val := X, property := And.intro hprod hreach } : TrimmedState G H))
          (terminal := by
            intro X0 a hmem hreach
            have hprod0 : IsProductive G H X0 :=
              IsProductive.terminal hmem
            have hsurv0 : And (IsProductive G H X0) (IsReachable G H X0) :=
              And.intro hprod0 hreach
            cases terminal_mem_extractedR G H X0 a hmem hsurv0 with
            | intro tr htr =>
              cases htr with
              | intro hX hrest =>
                cases hrest with
                | intro ha hmemR =>
                  have ht :
                      CarrierIsProductive H (extractedProfile G H) (extractedR G H) tr.X :=
                    CarrierIsProductive.terminal tr hmemR
                  rw [hX] at ht
                  exact ht)
          (binary := by
            intro X0 Y0 Z0 hmem hY hZ ihY ihZ hreach
            have hXprod : IsProductive G H X0 :=
              IsProductive.binary hmem hY hZ
            have hYreach : IsReachable G H Y0 :=
              IsReachable.binary_left hmem hreach hY hZ
            have hZreach : IsReachable G H Z0 :=
              IsReachable.binary_right hmem hreach hY hZ
            have hXsurv : And (IsProductive G H X0) (IsReachable G H X0) :=
              And.intro hXprod hreach
            have hYsurv : And (IsProductive G H Y0) (IsReachable G H Y0) :=
              And.intro hY hYreach
            have hZsurv : And (IsProductive G H Z0) (IsReachable G H Z0) :=
              And.intro hZ hZreach
            have hYcarrier :
                CarrierIsProductive H (extractedProfile G H) (extractedR G H)
                  ({ val := Y0, property := hYsurv } : TrimmedState G H) :=
              ihY hYreach
            have hZcarrier :
                CarrierIsProductive H (extractedProfile G H) (extractedR G H)
                  ({ val := Z0, property := hZsurv } : TrimmedState G H) :=
              ihZ hZreach
            cases binary_mem_extractedR G H X0 Y0 Z0 hmem hXsurv hYsurv hZsurv with
            | intro br hbr =>
              cases hbr with
              | intro hbrX hrest1 =>
                cases hrest1 with
                | intro hbrY hrest2 =>
                  cases hrest2 with
                  | intro hbrZ hmemR =>
                    have hYfinal :
                        CarrierIsProductive H (extractedProfile G H) (extractedR G H) br.Y := by
                      rw [hbrY]
                      exact hYcarrier
                    have hZfinal :
                        CarrierIsProductive H (extractedProfile G H) (extractedR G H) br.Z := by
                      rw [hbrZ]
                      exact hZcarrier
                    have hb :
                        CarrierIsProductive H (extractedProfile G H) (extractedR G H) br.X :=
                      CarrierIsProductive.binary br hmemR hYfinal hZfinal
                    rw [hbrX] at hb
                    exact hb)
          hsurv.1
          hsurv.2

theorem extracted_axiomRch
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    forall x : TrimmedState G H,
      CarrierIsReachable H (extractedProfile G H) (extractedR G H) (extractedS G H) x := by
  intro x
  classical
  cases x with
  | mk X hsurv =>
      exact
        IsReachable.rec
          (motive := fun X hreach =>
            forall hprod : IsProductive G H X,
              CarrierIsReachable H (extractedProfile G H) (extractedR G H) (extractedS G H)
                ({ val := X, property := And.intro hprod hreach } : TrimmedState G H))
          (start := by
            intro A p hstart hprod0 hprodArg
            let xs : TrimmedState G H :=
              { val := mkFullTypedState A p 1 1
                property := And.intro hprodArg (IsReachable.start A p hstart hprod0) }
            have hmemS : Membership.mem (extractedS G H) xs := by
              letI : Fintype (TrimmedState G H) := trimmedStateFintype G H
              unfold extractedS
              apply Finset.mem_filter.mpr
              apply And.intro
              exact Finset.mem_univ xs
              dsimp [xs, extractedProfile]
              exact And.intro rfl rfl
            exact CarrierIsReachable.start xs hmemS)
          (binary_left := by
            intro X0 Y0 Z0 hmem hXreach hYprod hZprod ihX hprodY
            have hYreach : IsReachable G H Y0 :=
              IsReachable.binary_left hmem hXreach hYprod hZprod
            have hZreach : IsReachable G H Z0 :=
              IsReachable.binary_right hmem hXreach hYprod hZprod
            have hXprod : IsProductive G H X0 :=
              reachable_implies_productive G H hXreach

            have hXsurv : And (IsProductive G H X0) (IsReachable G H X0) :=
              And.intro hXprod hXreach
            have hYsurv : And (IsProductive G H Y0) (IsReachable G H Y0) :=
              And.intro hYprod hYreach
            have hZsurv : And (IsProductive G H Z0) (IsReachable G H Z0) :=
              And.intro hZprod hZreach

            have hXcarrier :
                CarrierIsReachable H (extractedProfile G H) (extractedR G H) (extractedS G H)
                  ({ val := X0, property := hXsurv } : TrimmedState G H) :=
              ihX hXprod

            cases binary_mem_extractedR G H X0 Y0 Z0 hmem hXsurv hYsurv hZsurv with
            | intro br hbr =>
              cases hbr with
              | intro hbrX hrest1 =>
                cases hrest1 with
                | intro hbrY hrest2 =>
                  cases hrest2 with
                  | intro hbrZ hmemR =>
                    have hXfinal :
                        CarrierIsReachable H (extractedProfile G H) (extractedR G H) (extractedS G H) br.X := by
                      rw [hbrX]
                      exact hXcarrier
                    have hYcarrier :
                        CarrierIsReachable H (extractedProfile G H) (extractedR G H) (extractedS G H) br.Y :=
                      CarrierIsReachable.binary_left br hmemR hXfinal
                    rw [hbrY] at hYcarrier
                    have hsame :
                        ({ val := Y0, property := hYsurv } : TrimmedState G H) =
                        ({ val := Y0, property := And.intro hprodY hYreach } : TrimmedState G H) :=
                      Subtype.ext rfl
                    rw [hsame] at hYcarrier
                    exact hYcarrier)
          (binary_right := by
            intro X0 Y0 Z0 hmem hXreach hYprod hZprod ihX hprodZ
            have hYreach : IsReachable G H Y0 :=
              IsReachable.binary_left hmem hXreach hYprod hZprod
            have hZreach : IsReachable G H Z0 :=
              IsReachable.binary_right hmem hXreach hYprod hZprod
            have hXprod : IsProductive G H X0 :=
              reachable_implies_productive G H hXreach

            have hXsurv : And (IsProductive G H X0) (IsReachable G H X0) :=
              And.intro hXprod hXreach
            have hYsurv : And (IsProductive G H Y0) (IsReachable G H Y0) :=
              And.intro hYprod hYreach
            have hZsurv : And (IsProductive G H Z0) (IsReachable G H Z0) :=
              And.intro hZprod hZreach

            have hXcarrier :
                CarrierIsReachable H (extractedProfile G H) (extractedR G H) (extractedS G H)
                  ({ val := X0, property := hXsurv } : TrimmedState G H) :=
              ihX hXprod

            cases binary_mem_extractedR G H X0 Y0 Z0 hmem hXsurv hYsurv hZsurv with
            | intro br hbr =>
              cases hbr with
              | intro hbrX hrest1 =>
                cases hrest1 with
                | intro hbrY hrest2 =>
                  cases hrest2 with
                  | intro hbrZ hmemR =>
                    have hXfinal :
                        CarrierIsReachable H (extractedProfile G H) (extractedR G H) (extractedS G H) br.X := by
                      rw [hbrX]
                      exact hXcarrier
                    have hZcarrier :
                        CarrierIsReachable H (extractedProfile G H) (extractedR G H) (extractedS G H) br.Z :=
                      CarrierIsReachable.binary_right br hmemR hXfinal
                    rw [hbrZ] at hZcarrier
                    have hsame :
                        ({ val := Z0, property := hZsurv } : TrimmedState G H) =
                        ({ val := Z0, property := And.intro hprodZ hZreach } : TrimmedState G H) :=
                      Subtype.ext rfl
                    rw [hsame] at hZcarrier
                    exact hZcarrier)
          hsurv.2
          hsurv.1

noncomputable def extractedFiniteContextStructure
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    FiniteContextStructure H :=
  {
    W := TrimmedState G H
    fintypeW := trimmedStateFintype G H
    profile := extractedProfile G H
    R := extractedR G H
    S := extractedS G H
    axiomS := extracted_axiomS G H
    axiomP := extracted_axiomP G H
    axiomRch := extracted_axiomRch G H
  }

noncomputable def extractedOmega
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (x : TrimmedState G H) :
    Word Sigma :=
  Classical.choose (carrier_productive_has_yield (extracted_axiomP G H x))

theorem extractedOmega_yield
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (x : TrimmedState G H) :
    YieldFamily H (extractedProfile G H) (extractedR G H) x
      (extractedOmega G H x) :=
  Classical.choose_spec (carrier_productive_has_yield (extracted_axiomP G H x))

noncomputable def extractedChi
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (x : TrimmedState G H) :
    Prod (Word Sigma) (Word Sigma) :=
  Classical.choose
    (carrier_reachable_has_context
      (extracted_axiomP G H)
      (extracted_axiomRch G H x))

theorem extractedChi_context
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (x : TrimmedState G H) :
    ContextFamily H (extractedProfile G H) (extractedR G H) (extractedS G H) x
      (extractedChi G H x).1
      (extractedChi G H x).2 :=
  Classical.choose_spec
    (carrier_reachable_has_context
      (extracted_axiomP G H)
      (extracted_axiomRch G H x))

structure FixedFiniteMonoidHomLaws
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M) where
  map_empty : H.h [] = 1
  map_append :
    forall u v : Word Sigma,
      H.h (u ++ v) = H.h u * H.h v

axiom fixedHom_laws
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M) :
    FixedFiniteMonoidHomLaws H

theorem fixedHom_empty
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M) :
    H.h [] = 1 :=
  (fixedHom_laws H).map_empty

theorem fixedHom_append
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (u v : Word Sigma) :
    H.h (u ++ v) = H.h u * H.h v :=
  (fixedHom_laws H).map_append u v

theorem yieldFamily_type_sound
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    {W : Type u}
    {profile : W -> TypedState M}
    {R : List (CarrierTypedRule H profile)}
    {x : W}
    {w : Word Sigma}
    (hy : YieldFamily H profile R x w) :
    H.h w = (profile x).yt := by
  induction hy with
  | terminal tr hmem =>
      exact tr.type_eq
  | binary br hmem hY hZ ihY ihZ =>
      calc
        H.h (_ ++ _) = H.h _ * H.h _ := fixedHom_append H _ _
        _ = (profile br.Y).yt * (profile br.Z).yt := by rw [ihY, ihZ]
        _ = (profile br.X).yt := by rw [← br.yield_eq]

theorem contextFamily_type_sound_of_axiomS
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    {W : Type u}
    {profile : W -> TypedState M}
    {R : List (CarrierTypedRule H profile)}
    {S : Finset W}
    (axS :
      forall x : W,
        Membership.mem S x ->
          And ((profile x).lt = 1) ((profile x).rt = 1))
    {x : W}
    {l r : Word Sigma}
    (hc : ContextFamily H profile R S x l r) :
    And
      (H.h l = (profile x).lt)
      (H.h r = (profile x).rt) := by
  induction hc with
  | start x hmem =>
      have hs := axS x hmem
      apply And.intro
      · calc
          H.h [] = 1 := fixedHom_empty H
          _ = (profile x).lt := hs.1.symm
      · calc
          H.h [] = 1 := fixedHom_empty H
          _ = (profile x).rt := hs.2.symm
  | binary_left br hmem hctx hz ihctx =>
      have hztype : H.h _ = (profile br.Z).yt :=
        yieldFamily_type_sound hz
      apply And.intro
      · exact ihctx.1.trans br.left_child_left_eq.symm
      · calc
          H.h (_ ++ _) = H.h _ * H.h _ := fixedHom_append H _ _
          _ = (profile br.Z).yt * (profile br.X).rt := by rw [hztype, ihctx.2]
          _ = (profile br.Y).rt := br.left_child_right_eq.symm
  | binary_right br hmem hctx hy ihctx =>
      have hytype : H.h _ = (profile br.Y).yt :=
        yieldFamily_type_sound hy
      apply And.intro
      · calc
          H.h (_ ++ _) = H.h _ * H.h _ := fixedHom_append H _ _
          _ = (profile br.X).lt * (profile br.Y).yt := by rw [ihctx.1, hytype]
          _ = (profile br.Z).lt := br.right_child_left_eq.symm
      · exact ihctx.2.trans br.right_child_right_eq.symm

theorem extractedOmega_type
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    forall x : TrimmedState G H,
      H.h (extractedOmega G H x) = (extractedProfile G H x).yt := by
  intro x
  exact yieldFamily_type_sound (extractedOmega_yield G H x)

theorem extractedChi_type
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    forall x : TrimmedState G H,
      And
        (H.h (extractedChi G H x).1 = (extractedProfile G H x).lt)
        (H.h (extractedChi G H x).2 = (extractedProfile G H x).rt) := by
  intro x
  exact
    contextFamily_type_sound_of_axiomS
      (extracted_axiomS G H)
      (extractedChi_context G H x)

theorem extracted_axiomOmega_from_witness
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    forall x : TrimmedState G H,
      And
        (YieldFamily H (extractedProfile G H) (extractedR G H) x
          (extractedOmega G H x))
        (H.h (extractedOmega G H x) = (extractedProfile G H x).yt) := by
  intro x
  exact And.intro (extractedOmega_yield G H x) (extractedOmega_type G H x)

theorem extracted_axiomC_from_witness
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    forall x : TrimmedState G H,
      And
        (ContextFamily H (extractedProfile G H) (extractedR G H) (extractedS G H) x
          (extractedChi G H x).1
          (extractedChi G H x).2)
        (And
          (H.h (extractedChi G H x).1 = (extractedProfile G H x).lt)
          (H.h (extractedChi G H x).2 = (extractedProfile G H x).rt)) := by
  intro x
  exact And.intro (extractedChi_context G H x) ((extractedChi_type G H) x)

noncomputable def extractedWitnessedStructure
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    WitnessedFiniteContextStructure H :=
  {
    W := TrimmedState G H
    fintypeW := trimmedStateFintype G H
    profile := extractedProfile G H
    R := extractedR G H
    S := extractedS G H
    axiomS := extracted_axiomS G H
    axiomP := extracted_axiomP G H
    axiomRch := extracted_axiomRch G H
    omega := extractedOmega G H
    chi := extractedChi G H
    axiomOmega := extracted_axiomOmega_from_witness G H
    axiomC := extracted_axiomC_from_witness G H
  }

def mapFullTypedState
    {G1 G2 : SSBNFGrammar Sigma}
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    (X : FullTypedState G1 M) :
    FullTypedState G2 M :=
  match X with
  | (A, p, m, n) => mkFullTypedState (f.map A) p m n

theorem mapFullTypedState_id
    (G : SSBNFGrammar Sigma)
    (X : FullTypedState G M) :
    mapFullTypedState (SSBNFGrammar.GrammarMorphism.id G) X = X := by
  cases X with
  | mk A rest1 =>
      cases rest1 with
      | mk p rest2 =>
          cases rest2 with
          | mk m n =>
              rfl

theorem mapFullTypedState_comp
    {G1 G2 G3 : SSBNFGrammar Sigma}
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    (g : SSBNFGrammar.GrammarMorphism G2 G3)
    (X : FullTypedState G1 M) :
    mapFullTypedState (SSBNFGrammar.GrammarMorphism.comp f g) X =
      mapFullTypedState g (mapFullTypedState f X) := by
  cases X with
  | mk A rest1 =>
      cases rest1 with
      | mk p rest2 =>
          cases rest2 with
          | mk m n =>
              rfl

theorem finiteList_mem
    {alpha : Type u}
    [Fintype alpha]
    (x : alpha) :
    List.Mem x (finiteList alpha) := by
  classical
  unfold finiteList
  exact Finset.mem_toList.mpr (Finset.mem_univ x)

theorem map_fullTerminalRules_mem
    (G1 G2 : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    {X : FullTypedState G1 M}
    {a : Sigma}
    (hmem : List.Mem (X, a) (fullTerminalRules G1 H)) :
    List.Mem (mapFullTypedState f X, a) (fullTerminalRules G2 H) := by
  classical
  unfold fullTerminalRules at hmem
  unfold fullTerminalRules
  rcases List.mem_flatMap.mp hmem with ⟨rule, hrule, hbranch1⟩
  rcases rule with ⟨A, a0⟩
  rcases List.mem_flatMap.mp hbranch1 with ⟨m, hm, hbranch2⟩
  rcases List.mem_map.mp hbranch2 with ⟨n, hn, heq⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hX, ha⟩ := heq
  subst X
  subst a
  apply List.mem_flatMap.mpr
  refine ⟨(f.map A, a0), f.terminal_map (A, a0) hrule, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨m, finiteList_mem m, ?_⟩
  apply List.mem_map.mpr
  refine ⟨n, finiteList_mem n, ?_⟩
  simp [mapFullTypedState, mkFullTypedState]

theorem map_fullBinaryRules_mem
    (G1 G2 : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    {X Y Z : FullTypedState G1 M}
    (hmem : List.Mem (X, Y, Z) (fullBinaryRules G1)) :
    List.Mem
      (mapFullTypedState f X,
       mapFullTypedState f Y,
       mapFullTypedState f Z)
      (fullBinaryRules G2) := by
  classical
  unfold fullBinaryRules at hmem
  unfold fullBinaryRules
  rcases List.mem_flatMap.mp hmem with ⟨rule, hrule, hbranch1⟩
  rcases rule with ⟨A, rest⟩
  rcases rest with ⟨B, C⟩
  rcases List.mem_flatMap.mp hbranch1 with ⟨m, hm, hbranch2⟩
  rcases List.mem_flatMap.mp hbranch2 with ⟨n, hn, hbranch3⟩
  rcases List.mem_flatMap.mp hbranch3 with ⟨q, hq, hbranch4⟩
  rcases List.mem_map.mp hbranch4 with ⟨r, hr, heq⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hX, hY, hZ⟩ := heq
  subst X
  subst Y
  subst Z
  apply List.mem_flatMap.mpr
  refine ⟨(f.map A, f.map B, f.map C), f.binary_map (A, B, C) hrule, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨m, finiteList_mem m, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨n, finiteList_mem n, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨q, finiteList_mem q, ?_⟩
  apply List.mem_map.mpr
  refine ⟨r, finiteList_mem r, ?_⟩
  simp [mapFullTypedState, mkFullTypedState]

theorem mapFullTypedState_productive
    (G1 G2 : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    {X : FullTypedState G1 M}
    (hprod : IsProductive G1 H X) :
    IsProductive G2 H (mapFullTypedState f X) := by
  induction hprod with
  | terminal hmem =>
      exact
        IsProductive.terminal
          (map_fullTerminalRules_mem G1 G2 H f hmem)
  | binary hmem hY hZ ihY ihZ =>
      exact
        IsProductive.binary
          (map_fullBinaryRules_mem G1 G2 H f hmem)
          ihY
          ihZ

theorem mapFullTypedState_reachable
    (G1 G2 : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    {X : FullTypedState G1 M}
    (hreach : IsReachable G1 H X) :
    IsReachable G2 H (mapFullTypedState f X) := by
  induction hreach with
  | start A p hstart hprod =>
      have hstart2 : Membership.mem G2.startRules (f.map A) :=
        f.start_map A hstart
      have hprod2 :
          IsProductive G2 H (mapFullTypedState f (mkFullTypedState A p 1 1)) :=
        mapFullTypedState_productive G1 G2 H f hprod
      simpa [mapFullTypedState, mkFullTypedState] using
        IsReachable.start (f.map A) p hstart2 hprod2
  | binary_left hmem hX hYprod hZprod ihX =>
      exact
        IsReachable.binary_left
          (map_fullBinaryRules_mem G1 G2 H f hmem)
          ihX
          (mapFullTypedState_productive G1 G2 H f hYprod)
          (mapFullTypedState_productive G1 G2 H f hZprod)
  | binary_right hmem hX hYprod hZprod ihX =>
      exact
        IsReachable.binary_right
          (map_fullBinaryRules_mem G1 G2 H f hmem)
          ihX
          (mapFullTypedState_productive G1 G2 H f hYprod)
          (mapFullTypedState_productive G1 G2 H f hZprod)

theorem mapFullTypedState_trimmed_property
    (G1 G2 : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    (x : TrimmedState G1 H) :
    And
      (IsProductive G2 H (mapFullTypedState f x.val))
      (IsReachable G2 H (mapFullTypedState f x.val)) :=
  And.intro
    (mapFullTypedState_productive G1 G2 H f x.property.1)
    (mapFullTypedState_reachable G1 G2 H f x.property.2)

noncomputable def mapTrimmedState
    {G1 G2 : SSBNFGrammar Sigma}
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    (x : TrimmedState G1 H) :
    TrimmedState G2 H :=
  {
    val := mapFullTypedState f x.val
    property := mapFullTypedState_trimmed_property G1 G2 H f x
  }

theorem mapTrimmedState_profile
    {G1 G2 : SSBNFGrammar Sigma}
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    (x : TrimmedState G1 H) :
    extractedProfile G2 H (mapTrimmedState H f x) =
      extractedProfile G1 H x := by
  cases x with
  | mk X hx =>
      cases X with
      | mk A rest1 =>
          cases rest1 with
          | mk p rest2 =>
              cases rest2 with
              | mk m n =>
                  simp [mapTrimmedState, mapFullTypedState,
                    extractedProfile, mkFullTypedState]

theorem mapTrimmedState_start_mem
    {G1 G2 : SSBNFGrammar Sigma}
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    (x : TrimmedState G1 H)
    (hx : Membership.mem (extractedS G1 H) x) :
    Membership.mem (extractedS G2 H) (mapTrimmedState H f x) := by
  classical
  letI : Fintype (TrimmedState G2 H) := trimmedStateFintype G2 H
  unfold extractedS
  apply Finset.mem_filter.mpr
  apply And.intro
  · exact Finset.mem_univ (mapTrimmedState H f x)
  · have hb := extracted_axiomS G1 H x hx
    have hp := mapTrimmedState_profile H f x
    rw [hp]
    exact hb

theorem mapTrimmedState_id
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (x : TrimmedState G H) :
    mapTrimmedState H (SSBNFGrammar.GrammarMorphism.id G) x = x := by
  cases x with
  | mk X hx =>
      apply Subtype.ext
      exact mapFullTypedState_id G X

theorem mapTrimmedState_comp
    {G1 G2 G3 : SSBNFGrammar Sigma}
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    (g : SSBNFGrammar.GrammarMorphism G2 G3)
    (x : TrimmedState G1 H) :
    mapTrimmedState H (SSBNFGrammar.GrammarMorphism.comp f g) x =
      mapTrimmedState H g (mapTrimmedState H f x) := by
  cases x with
  | mk X hx =>
      apply Subtype.ext
      exact mapFullTypedState_comp f g X

theorem extractedR_terminal_to_full
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (tr : CarrierTerminalRule H (extractedProfile G H))
    (hmem : List.Mem (CarrierTypedRule.terminal tr) (extractedR G H)) :
    List.Mem (tr.X.val, tr.a) (fullTerminalRules G H) := by
  classical
  unfold extractedR at hmem
  rcases List.mem_append.mp hmem with hleft | hright
  · rcases List.mem_filterMap.mp hleft with ⟨rule, hfull, hsome⟩
    rcases rule with ⟨X, a⟩
    dsimp only at hsome
    by_cases hsurv : And (IsProductive G H X) (IsReachable G H X)
    · rw [dif_pos hsurv] at hsome
      by_cases htype :
          H.h [a] =
            (extractedProfile G H
              ({ val := X, property := hsurv } : TrimmedState G H)).yt
      · rw [dif_pos htype] at hsome
        cases hsome
        simpa
      · rw [dif_neg htype] at hsome
        cases hsome
    · rw [dif_neg hsurv] at hsome
      cases hsome
  · rcases List.mem_filterMap.mp hright with ⟨rule, hfull, hsome⟩
    rcases rule with ⟨X, rest⟩
    rcases rest with ⟨Y, Z⟩
    dsimp only at hsome
    by_cases hXsurv : And (IsProductive G H X) (IsReachable G H X)
    · rw [dif_pos hXsurv] at hsome
      by_cases hYsurv : And (IsProductive G H Y) (IsReachable G H Y)
      · rw [dif_pos hYsurv] at hsome
        by_cases hZsurv : And (IsProductive G H Z) (IsReachable G H Z)
        · rw [dif_pos hZsurv] at hsome
          let Xt : TrimmedState G H := { val := X, property := hXsurv }
          let Yt : TrimmedState G H := { val := Y, property := hYsurv }
          let Zt : TrimmedState G H := { val := Z, property := hZsurv }
          by_cases hyield :
              (extractedProfile G H Xt).yt =
                (extractedProfile G H Yt).yt *
                (extractedProfile G H Zt).yt
          · rw [dif_pos hyield] at hsome
            by_cases hleft_left :
                (extractedProfile G H Yt).lt =
                  (extractedProfile G H Xt).lt
            · rw [dif_pos hleft_left] at hsome
              by_cases hleft_right :
                  (extractedProfile G H Yt).rt =
                    (extractedProfile G H Zt).yt *
                    (extractedProfile G H Xt).rt
              · rw [dif_pos hleft_right] at hsome
                by_cases hright_left :
                    (extractedProfile G H Zt).lt =
                      (extractedProfile G H Xt).lt *
                      (extractedProfile G H Yt).yt
                · rw [dif_pos hright_left] at hsome
                  by_cases hright_right :
                      (extractedProfile G H Zt).rt =
                        (extractedProfile G H Xt).rt
                  · rw [dif_pos hright_right] at hsome
                    cases hsome
                  · rw [dif_neg hright_right] at hsome
                    cases hsome
                · rw [dif_neg hright_left] at hsome
                  cases hsome
              · rw [dif_neg hleft_right] at hsome
                cases hsome
            · rw [dif_neg hleft_left] at hsome
              cases hsome
          · rw [dif_neg hyield] at hsome
            cases hsome
        · rw [dif_neg hZsurv] at hsome
          cases hsome
      · rw [dif_neg hYsurv] at hsome
        cases hsome
    · rw [dif_neg hXsurv] at hsome
      cases hsome

theorem extractedR_binary_to_full
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (br : CarrierBinaryRule (extractedProfile G H))
    (hmem : List.Mem (CarrierTypedRule.binary br) (extractedR G H)) :
    List.Mem (br.X.val, br.Y.val, br.Z.val) (fullBinaryRules G) := by
  classical
  unfold extractedR at hmem
  rcases List.mem_append.mp hmem with hleft | hright
  · rcases List.mem_filterMap.mp hleft with ⟨rule, hfull, hsome⟩
    rcases rule with ⟨X, a⟩
    dsimp only at hsome
    by_cases hsurv : And (IsProductive G H X) (IsReachable G H X)
    · rw [dif_pos hsurv] at hsome
      by_cases htype :
          H.h [a] =
            (extractedProfile G H
              ({ val := X, property := hsurv } : TrimmedState G H)).yt
      · rw [dif_pos htype] at hsome
        cases hsome
      · rw [dif_neg htype] at hsome
        cases hsome
    · rw [dif_neg hsurv] at hsome
      cases hsome
  · rcases List.mem_filterMap.mp hright with ⟨rule, hfull, hsome⟩
    rcases rule with ⟨X, rest⟩
    rcases rest with ⟨Y, Z⟩
    dsimp only at hsome
    by_cases hXsurv : And (IsProductive G H X) (IsReachable G H X)
    · rw [dif_pos hXsurv] at hsome
      by_cases hYsurv : And (IsProductive G H Y) (IsReachable G H Y)
      · rw [dif_pos hYsurv] at hsome
        by_cases hZsurv : And (IsProductive G H Z) (IsReachable G H Z)
        · rw [dif_pos hZsurv] at hsome
          let Xt : TrimmedState G H := { val := X, property := hXsurv }
          let Yt : TrimmedState G H := { val := Y, property := hYsurv }
          let Zt : TrimmedState G H := { val := Z, property := hZsurv }
          by_cases hyield :
              (extractedProfile G H Xt).yt =
                (extractedProfile G H Yt).yt *
                (extractedProfile G H Zt).yt
          · rw [dif_pos hyield] at hsome
            by_cases hleft_left :
                (extractedProfile G H Yt).lt =
                  (extractedProfile G H Xt).lt
            · rw [dif_pos hleft_left] at hsome
              by_cases hleft_right :
                  (extractedProfile G H Yt).rt =
                    (extractedProfile G H Zt).yt *
                    (extractedProfile G H Xt).rt
              · rw [dif_pos hleft_right] at hsome
                by_cases hright_left :
                    (extractedProfile G H Zt).lt =
                      (extractedProfile G H Xt).lt *
                      (extractedProfile G H Yt).yt
                · rw [dif_pos hright_left] at hsome
                  by_cases hright_right :
                      (extractedProfile G H Zt).rt =
                        (extractedProfile G H Xt).rt
                  · rw [dif_pos hright_right] at hsome
                    cases hsome
                    simpa
                  · rw [dif_neg hright_right] at hsome
                    cases hsome
                · rw [dif_neg hright_left] at hsome
                  cases hsome
              · rw [dif_neg hleft_right] at hsome
                cases hsome
            · rw [dif_neg hleft_left] at hsome
              cases hsome
          · rw [dif_neg hyield] at hsome
            cases hsome
        · rw [dif_neg hZsurv] at hsome
          cases hsome
      · rw [dif_neg hYsurv] at hsome
        cases hsome
    · rw [dif_neg hXsurv] at hsome
      cases hsome

theorem extraction_terminal_map_core
    (G1 G2 : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    (tr : CarrierTerminalRule H (extractedProfile G1 H))
    (hmem : List.Mem (CarrierTypedRule.terminal tr) (extractedR G1 H)) :
    Exists
      (fun trB : CarrierTerminalRule H (extractedProfile G2 H) =>
        And
          (trB.X = mapTrimmedState H f tr.X)
          (And
            (trB.a = tr.a)
            (List.Mem (CarrierTypedRule.terminal trB) (extractedR G2 H)))) := by
  classical
  have hfull1 :
      List.Mem (tr.X.val, tr.a) (fullTerminalRules G1 H) :=
    extractedR_terminal_to_full G1 H tr hmem
  have hfull2 :
      List.Mem (mapFullTypedState f tr.X.val, tr.a) (fullTerminalRules G2 H) :=
    map_fullTerminalRules_mem G1 G2 H f hfull1
  have hsurv :
      And
        (IsProductive G2 H (mapFullTypedState f tr.X.val))
        (IsReachable G2 H (mapFullTypedState f tr.X.val)) :=
    (mapTrimmedState H f tr.X).property
  cases terminal_mem_extractedR G2 H (mapFullTypedState f tr.X.val) tr.a hfull2 hsurv with
  | intro trB htrB =>
      cases htrB with
      | intro hX hrest =>
          cases hrest with
          | intro ha hmemB =>
              exact Exists.intro trB (And.intro hX (And.intro ha hmemB))

theorem extraction_binary_map_core
    (G1 G2 : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    (br : CarrierBinaryRule (extractedProfile G1 H))
    (hmem : List.Mem (CarrierTypedRule.binary br) (extractedR G1 H)) :
    Exists
      (fun brB : CarrierBinaryRule (extractedProfile G2 H) =>
        And
          (brB.X = mapTrimmedState H f br.X)
          (And
            (brB.Y = mapTrimmedState H f br.Y)
            (And
              (brB.Z = mapTrimmedState H f br.Z)
              (List.Mem (CarrierTypedRule.binary brB) (extractedR G2 H))))) := by
  classical
  have hfull1 :
      List.Mem (br.X.val, br.Y.val, br.Z.val) (fullBinaryRules G1) :=
    extractedR_binary_to_full G1 H br hmem
  have hfull2 :
      List.Mem
        (mapFullTypedState f br.X.val,
         mapFullTypedState f br.Y.val,
         mapFullTypedState f br.Z.val)
        (fullBinaryRules G2) :=
    map_fullBinaryRules_mem G1 G2 H f hfull1
  have hXsurv :
      And
        (IsProductive G2 H (mapFullTypedState f br.X.val))
        (IsReachable G2 H (mapFullTypedState f br.X.val)) :=
    (mapTrimmedState H f br.X).property
  have hYsurv :
      And
        (IsProductive G2 H (mapFullTypedState f br.Y.val))
        (IsReachable G2 H (mapFullTypedState f br.Y.val)) :=
    (mapTrimmedState H f br.Y).property
  have hZsurv :
      And
        (IsProductive G2 H (mapFullTypedState f br.Z.val))
        (IsReachable G2 H (mapFullTypedState f br.Z.val)) :=
    (mapTrimmedState H f br.Z).property
  cases
      binary_mem_extractedR G2 H
        (mapFullTypedState f br.X.val)
        (mapFullTypedState f br.Y.val)
        (mapFullTypedState f br.Z.val)
        hfull2 hXsurv hYsurv hZsurv with
  | intro brB hbrB =>
      cases hbrB with
      | intro hX hrest1 =>
          cases hrest1 with
          | intro hY hrest2 =>
              cases hrest2 with
              | intro hZ hmemB =>
                  exact
                    Exists.intro brB
                      (And.intro hX
                        (And.intro hY
                          (And.intro hZ hmemB)))

noncomputable def extractionMap
    (G1 G2 : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2) :
    StructureMorphism
      (extractedWitnessedStructure G1 H)
      (extractedWitnessedStructure G2 H) :=
  {
    map := mapTrimmedState H f
    profile_map := by
      intro x
      exact mapTrimmedState_profile H f x
    start_map := by
      intro x hx
      exact mapTrimmedState_start_mem H f x hx
    terminal_map := by
      intro tr hmem
      exact extraction_terminal_map_core G1 G2 H f tr hmem
    binary_map := by
      intro br hmem
      exact extraction_binary_map_core G1 G2 H f br hmem
  }

theorem extractionMap_id
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    extractionMap G G H (SSBNFGrammar.GrammarMorphism.id G) =
      StructureMorphism.id (extractedWitnessedStructure G H) := by
  apply StructureMorphism.ext
  funext x
  exact mapTrimmedState_id G H x

theorem extractionMap_comp
    (G1 G2 G3 : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (f : SSBNFGrammar.GrammarMorphism G1 G2)
    (g : SSBNFGrammar.GrammarMorphism G2 G3) :
    extractionMap G1 G3 H (SSBNFGrammar.GrammarMorphism.comp f g) =
      StructureMorphism.comp
        (extractionMap G1 G2 H f)
        (extractionMap G2 G3 H g) := by
  apply StructureMorphism.ext
  funext x
  exact mapTrimmedState_comp H f g x

noncomputable def extractionFunctor
    (H : FixedFiniteMonoidHom Sigma M) :
    CategoryTheory.Functor
      (SSBNFGrammar Sigma)
      (WitnessedFiniteContextStructure H) :=
  {
    obj := fun G => extractedWitnessedStructure G H
    map := fun {G1 G2} f => extractionMap G1 G2 H f
    map_id := by
      intro G
      exact extractionMap_id G H
    map_comp := by
      intro G1 G2 G3 f g
      exact extractionMap_comp G1 G2 G3 H f g
  }

end Extraction

structure IsShortlexNormalized
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A : WitnessedFiniteContextStructure H) where
  hom :
    StructureMorphism
      A
      ((Extraction.extractionFunctor H).obj
        ((Realization.realizationFunctor H).obj A))
  inv :
    StructureMorphism
      ((Extraction.extractionFunctor H).obj
        ((Realization.realizationFunctor H).obj A))
      A
  left_inv :
    forall x : A.W,
      inv.map (hom.map x) = x
  right_inv :
    forall y :
      ((Extraction.extractionFunctor H).obj
        ((Realization.realizationFunctor H).obj A)).W,
      hom.map (inv.map y) = y

structure StructureIso
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A B : WitnessedFiniteContextStructure H) where
  hom : StructureMorphism A B
  inv : StructureMorphism B A
  left_inv : forall x : A.W, inv.map (hom.map x) = x
  right_inv : forall y : B.W, hom.map (inv.map y) = y

noncomputable def extraction_realization_hom
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A : WitnessedFiniteContextStructure H)
    (hshort : IsShortlexNormalized A) :
    StructureMorphism
      A
      ((Extraction.extractionFunctor H).obj
        ((Realization.realizationFunctor H).obj A)) :=
  hshort.hom

noncomputable def extraction_realization_inv
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A : WitnessedFiniteContextStructure H)
    (hshort : IsShortlexNormalized A) :
    StructureMorphism
      ((Extraction.extractionFunctor H).obj
        ((Realization.realizationFunctor H).obj A))
      A :=
  hshort.inv

theorem extraction_realization_left_inv
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A : WitnessedFiniteContextStructure H)
    (hshort : IsShortlexNormalized A) :
    forall x : A.W,
      (extraction_realization_inv A hshort).map
        ((extraction_realization_hom A hshort).map x) = x :=
  hshort.left_inv

theorem extraction_realization_right_inv
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A : WitnessedFiniteContextStructure H)
    (hshort : IsShortlexNormalized A) :
    forall y :
      ((Extraction.extractionFunctor H).obj
        ((Realization.realizationFunctor H).obj A)).W,
      (extraction_realization_hom A hshort).map
        ((extraction_realization_inv A hshort).map y) = y :=
  hshort.right_inv

theorem extraction_realization_retraction
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {H : FixedFiniteMonoidHom Sigma M}
    (A : WitnessedFiniteContextStructure H)
    (hshort : IsShortlexNormalized A) :
    Nonempty
      (StructureIso
        A
        ((Extraction.extractionFunctor H).obj
          ((Realization.realizationFunctor H).obj A))) :=
  Nonempty.intro
    {
      hom := extraction_realization_hom A hshort
      inv := extraction_realization_inv A hshort
      left_inv := extraction_realization_left_inv A hshort
      right_inv := extraction_realization_right_inv A hshort
    }

end

end TwoSidedTypedCFG
