import Mathlib

set_option linter.style.openClassical false

universe u

namespace TwoSidedTypedCFG

open Classical

noncomputable section

abbrev Word (Sigma : Type u) := List Sigma

structure FixedFiniteMonoidHom (Sigma : Type u) (M : Type u)
    [Monoid M] [Fintype M] where
  h : Word Sigma → M
  map_empty : h [] = 1
  map_append :
    forall u v : Word Sigma,
      h (u ++ v) = h u * h v

structure TypedState (M : Type u) [Monoid M] where
  yt : M
  lt : M
  rt : M

structure SSBNFGrammar (Sigma : Type u) where
  V : Type u
  [fintypeV : Fintype V]
  startRules : Finset V
  terminalRules : List (V × Sigma)
  binaryRules : List (V × V × V)

attribute [instance] SSBNFGrammar.fintypeV

noncomputable def finiteList (α : Type u) [Fintype α] : List α := by
  classical
  exact (Finset.univ : Finset α).toList

abbrev FullTypedState
    {Sigma : Type u}
    (G : SSBNFGrammar Sigma)
    (M : Type u) : Type u :=
  G.V × M × M × M

abbrev FullTerminalRule
    {Sigma : Type u}
    (G : SSBNFGrammar Sigma)
    (M : Type u) : Type u :=
  FullTypedState G M × Sigma

abbrev FullBinaryRule
    {Sigma : Type u}
    (G : SSBNFGrammar Sigma)
    (M : Type u) : Type u :=
  FullTypedState G M × FullTypedState G M × FullTypedState G M

def mkFullTypedState
    {Sigma : Type u}
    {G : SSBNFGrammar Sigma}
    {M : Type u}
    (A : G.V)
    (p m n : M) :
    FullTypedState G M :=
  (A, p, m, n)

def fullTerminalRules
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    List (FullTerminalRule G M) :=
  G.terminalRules.bind
    (fun rule =>
      let A : G.V := rule.1
      let a : Sigma := rule.2
      (finiteList M).bind
        (fun m =>
          (finiteList M).map
            (fun n =>
              (mkFullTypedState A (H.h [a]) m n, a))))

def fullBinaryRules
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (G : SSBNFGrammar Sigma) :
    List (FullBinaryRule G M) :=
  G.binaryRules.bind
    (fun rule =>
      let A : G.V := rule.1
      let B : G.V := rule.2.1
      let C : G.V := rule.2.2
      (finiteList M).bind
        (fun m =>
          (finiteList M).bind
            (fun n =>
              (finiteList M).bind
                (fun q =>
                  (finiteList M).map
                    (fun r =>
                      let p : M := q * r
                      let parent : FullTypedState G M :=
                        mkFullTypedState A p m n
                      let leftChild : FullTypedState G M :=
                        mkFullTypedState B q m (r * n)
                      let rightChild : FullTypedState G M :=
                        mkFullTypedState C r (m * q) n
                      (parent, leftChild, rightChild))))))

namespace FullTypedRefinement

inductive IsProductive
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    FullTypedState G M → Prop where
  | terminal
      {X : FullTypedState G M}
      {a : Sigma}
      (hmem : (X, a) ∈ fullTerminalRules G H) :
      IsProductive G H X
  | binary
      {X Y Z : FullTypedState G M}
      (hmem : (X, Y, Z) ∈ fullBinaryRules G)
      (hY : IsProductive G H Y)
      (hZ : IsProductive G H Z) :
      IsProductive G H X

inductive IsReachable
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    FullTypedState G M → Prop where
  | start
      (A : G.V)
      (p : M)
      (hstart : A ∈ G.startRules)
      (hprod : IsProductive G H (mkFullTypedState A p 1 1)) :
      IsReachable G H (mkFullTypedState A p 1 1)
  | binary_left
      {X Y Z : FullTypedState G M}
      (hmem : (X, Y, Z) ∈ fullBinaryRules G)
      (hX : IsReachable G H X)
      (hYprod : IsProductive G H Y)
      (hZprod : IsProductive G H Z) :
      IsReachable G H Y
  | binary_right
      {X Y Z : FullTypedState G M}
      (hmem : (X, Y, Z) ∈ fullBinaryRules G)
      (hX : IsReachable G H X)
      (hYprod : IsProductive G H Y)
      (hZprod : IsProductive G H Z) :
      IsReachable G H Z

def TrimmedState
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) : Type u :=
  { X : FullTypedState G M // IsProductive G H X ∧ IsReachable G H X }

end FullTypedRefinement

open FullTypedRefinement

structure CarrierTerminalRule
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M) where
  X : W
  a : Sigma
  type_eq : H.h [a] = (profile X).yt

structure CarrierBinaryRule
    {M : Type u} [Monoid M] [Fintype M]
    {W : Type u}
    (profile : W → TypedState M) where
  X : W
  Y : W
  Z : W
  yield_eq :
    (profile X).yt = (profile Y).yt * (profile Z).yt
  left_child_left_eq :
    (profile Y).lt = (profile X).lt
  left_child_right_eq :
    (profile Y).rt = (profile Z).yt * (profile X).rt
  right_child_left_eq :
    (profile Z).lt = (profile X).lt * (profile Y).yt
  right_child_right_eq :
    (profile Z).rt = (profile X).rt

inductive CarrierTypedRule
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M) where
  | terminal : CarrierTerminalRule H profile → CarrierTypedRule H profile
  | binary : CarrierBinaryRule profile → CarrierTypedRule H profile

def extractedProfile
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    TrimmedState G H → TypedState M :=
  fun X =>
    match X.val with
    | (_, p, m, n) =>
        {
          yt := p
          lt := m
          rt := n
        }

namespace Extraction

open FullTypedRefinement

variable {Sigma : Type u}
variable {M : Type u} [Monoid M] [Fintype M]

noncomputable def extractedR
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M) :
    List (CarrierTypedRule H (extractedProfile G H)) := by
  classical

  let terminalPart : List (CarrierTypedRule H (extractedProfile G H)) :=
    (fullTerminalRules G H).filterMap
      (fun rule =>
        let X : FullTypedState G M := rule.1
        let a : Sigma := rule.2

        if hsurv :
            IsProductive G H X ∧ IsReachable G H X then

          let Xt : TrimmedState G H :=
            { val := X, property := hsurv }

          if htype :
              H.h [a] = (extractedProfile G H Xt).yt then

            some
              (CarrierTypedRule.terminal
                ({
                  X := Xt
                  a := a
                  type_eq := htype
                } : CarrierTerminalRule H (extractedProfile G H)))
          else
            none
        else
          none)

  let binaryPart : List (CarrierTypedRule H (extractedProfile G H)) :=
    (fullBinaryRules G).filterMap
      (fun rule =>
        let X : FullTypedState G M := rule.1
        let Y : FullTypedState G M := rule.2.1
        let Z : FullTypedState G M := rule.2.2

        if hXsurv :
            IsProductive G H X ∧ IsReachable G H X then
          if hYsurv :
              IsProductive G H Y ∧ IsReachable G H Y then
            if hZsurv :
                IsProductive G H Z ∧ IsReachable G H Z then

              let Xt : TrimmedState G H :=
                { val := X, property := hXsurv }

              let Yt : TrimmedState G H :=
                { val := Y, property := hYsurv }

              let Zt : TrimmedState G H :=
                { val := Z, property := hZsurv }

              if hyield :
                  (extractedProfile G H Xt).yt =
                    (extractedProfile G H Yt).yt *
                    (extractedProfile G H Zt).yt then

                if hleft_left :
                    (extractedProfile G H Yt).lt =
                      (extractedProfile G H Xt).lt then

                  if hleft_right :
                      (extractedProfile G H Yt).rt =
                        (extractedProfile G H Zt).yt *
                        (extractedProfile G H Xt).rt then

                    if hright_left :
                        (extractedProfile G H Zt).lt =
                          (extractedProfile G H Xt).lt *
                          (extractedProfile G H Yt).yt then

                      if hright_right :
                          (extractedProfile G H Zt).rt =
                            (extractedProfile G H Xt).rt then

                        some
                          (CarrierTypedRule.binary
                            ({
                              X := Xt
                              Y := Yt
                              Z := Zt

                              yield_eq := hyield

                              left_child_left_eq := hleft_left
                              left_child_right_eq := hleft_right

                              right_child_left_eq := hright_left
                              right_child_right_eq := hright_right
                            } : CarrierBinaryRule (extractedProfile G H)))
                      else
                        none
                    else
                      none
                  else
                    none
                else
                  none
              else
                none
            else
              none
          else
            none
        else
          none)

  exact terminalPart ++ binaryPart

/-!
Axiom T soundness lemmas for full refined rules.
If `List.mem_flatMap` is unavailable in your Mathlib, replace it with
`List.mem_bind`.
-/

lemma fullTerminalRules_type_eq
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (X : FullTypedState G M)
    (a : Sigma)
    (hmem : (X, a) ∈ fullTerminalRules G H)
    (hsurv : IsProductive G H X ∧ IsReachable G H X) :
    H.h [a] =
      (extractedProfile G H
        ({ val := X, property := hsurv } : TrimmedState G H)).yt := by
  classical
  unfold fullTerminalRules at hmem
  rcases List.mem_flatMap.mp hmem with ⟨rule, _hrule, hbranch₁⟩
  rcases rule with ⟨A, a₀⟩
  rcases List.mem_flatMap.mp hbranch₁ with ⟨m, _hm, hbranch₂⟩
  rcases List.mem_map.mp hbranch₂ with ⟨n, _hn, heq⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  simp [extractedProfile, mkFullTypedState]

lemma fullBinaryRules_yield_eq
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (X Y Z : FullTypedState G M)
    (hmem : (X, Y, Z) ∈ fullBinaryRules G)
    (hXsurv : IsProductive G H X ∧ IsReachable G H X)
    (hYsurv : IsProductive G H Y ∧ IsReachable G H Y)
    (hZsurv : IsProductive G H Z ∧ IsReachable G H Z) :
    (extractedProfile G H
      ({ val := X, property := hXsurv } : TrimmedState G H)).yt =
      (extractedProfile G H
        ({ val := Y, property := hYsurv } : TrimmedState G H)).yt *
      (extractedProfile G H
        ({ val := Z, property := hZsurv } : TrimmedState G H)).yt := by
  classical
  unfold fullBinaryRules at hmem
  rcases List.mem_flatMap.mp hmem with ⟨rule, _hrule, hbranch₁⟩
  rcases rule with ⟨A, rest⟩
  rcases rest with ⟨B, C⟩
  rcases List.mem_flatMap.mp hbranch₁ with ⟨m, _hm, hbranch₂⟩
  rcases List.mem_flatMap.mp hbranch₂ with ⟨n, _hn, hbranch₃⟩
  rcases List.mem_flatMap.mp hbranch₃ with ⟨q, _hq, hbranch₄⟩
  rcases List.mem_map.mp hbranch₄ with ⟨r, _hr, heq⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  simp [extractedProfile, mkFullTypedState]

lemma fullBinaryRules_left_child_left_eq
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (X Y Z : FullTypedState G M)
    (hmem : (X, Y, Z) ∈ fullBinaryRules G)
    (hXsurv : IsProductive G H X ∧ IsReachable G H X)
    (hYsurv : IsProductive G H Y ∧ IsReachable G H Y)
    (hZsurv : IsProductive G H Z ∧ IsReachable G H Z) :
    (extractedProfile G H
      ({ val := Y, property := hYsurv } : TrimmedState G H)).lt =
    (extractedProfile G H
      ({ val := X, property := hXsurv } : TrimmedState G H)).lt := by
  classical
  unfold fullBinaryRules at hmem
  rcases List.mem_flatMap.mp hmem with ⟨rule, _hrule, hbranch₁⟩
  rcases rule with ⟨A, rest⟩
  rcases rest with ⟨B, C⟩
  rcases List.mem_flatMap.mp hbranch₁ with ⟨m, _hm, hbranch₂⟩
  rcases List.mem_flatMap.mp hbranch₂ with ⟨n, _hn, hbranch₃⟩
  rcases List.mem_flatMap.mp hbranch₃ with ⟨q, _hq, hbranch₄⟩
  rcases List.mem_map.mp hbranch₄ with ⟨r, _hr, heq⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  simp [extractedProfile, mkFullTypedState]

lemma fullBinaryRules_left_child_right_eq
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (X Y Z : FullTypedState G M)
    (hmem : (X, Y, Z) ∈ fullBinaryRules G)
    (hXsurv : IsProductive G H X ∧ IsReachable G H X)
    (hYsurv : IsProductive G H Y ∧ IsReachable G H Y)
    (hZsurv : IsProductive G H Z ∧ IsReachable G H Z) :
    (extractedProfile G H
      ({ val := Y, property := hYsurv } : TrimmedState G H)).rt =
      (extractedProfile G H
        ({ val := Z, property := hZsurv } : TrimmedState G H)).yt *
      (extractedProfile G H
        ({ val := X, property := hXsurv } : TrimmedState G H)).rt := by
  classical
  unfold fullBinaryRules at hmem
  rcases List.mem_flatMap.mp hmem with ⟨rule, _hrule, hbranch₁⟩
  rcases rule with ⟨A, rest⟩
  rcases rest with ⟨B, C⟩
  rcases List.mem_flatMap.mp hbranch₁ with ⟨m, _hm, hbranch₂⟩
  rcases List.mem_flatMap.mp hbranch₂ with ⟨n, _hn, hbranch₃⟩
  rcases List.mem_flatMap.mp hbranch₃ with ⟨q, _hq, hbranch₄⟩
  rcases List.mem_map.mp hbranch₄ with ⟨r, _hr, heq⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  simp [extractedProfile, mkFullTypedState]

lemma fullBinaryRules_right_child_left_eq
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (X Y Z : FullTypedState G M)
    (hmem : (X, Y, Z) ∈ fullBinaryRules G)
    (hXsurv : IsProductive G H X ∧ IsReachable G H X)
    (hYsurv : IsProductive G H Y ∧ IsReachable G H Y)
    (hZsurv : IsProductive G H Z ∧ IsReachable G H Z) :
    (extractedProfile G H
      ({ val := Z, property := hZsurv } : TrimmedState G H)).lt =
      (extractedProfile G H
        ({ val := X, property := hXsurv } : TrimmedState G H)).lt *
      (extractedProfile G H
        ({ val := Y, property := hYsurv } : TrimmedState G H)).yt := by
  classical
  unfold fullBinaryRules at hmem
  rcases List.mem_flatMap.mp hmem with ⟨rule, _hrule, hbranch₁⟩
  rcases rule with ⟨A, rest⟩
  rcases rest with ⟨B, C⟩
  rcases List.mem_flatMap.mp hbranch₁ with ⟨m, _hm, hbranch₂⟩
  rcases List.mem_flatMap.mp hbranch₂ with ⟨n, _hn, hbranch₃⟩
  rcases List.mem_flatMap.mp hbranch₃ with ⟨q, _hq, hbranch₄⟩
  rcases List.mem_map.mp hbranch₄ with ⟨r, _hr, heq⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  simp [extractedProfile, mkFullTypedState]

lemma fullBinaryRules_right_child_right_eq
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (X Y Z : FullTypedState G M)
    (hmem : (X, Y, Z) ∈ fullBinaryRules G)
    (hXsurv : IsProductive G H X ∧ IsReachable G H X)
    (hYsurv : IsProductive G H Y ∧ IsReachable G H Y)
    (hZsurv : IsProductive G H Z ∧ IsReachable G H Z) :
    (extractedProfile G H
      ({ val := Z, property := hZsurv } : TrimmedState G H)).rt =
    (extractedProfile G H
      ({ val := X, property := hXsurv } : TrimmedState G H)).rt := by
  classical
  unfold fullBinaryRules at hmem
  rcases List.mem_flatMap.mp hmem with ⟨rule, _hrule, hbranch₁⟩
  rcases rule with ⟨A, rest⟩
  rcases rest with ⟨B, C⟩
  rcases List.mem_flatMap.mp hbranch₁ with ⟨m, _hm, hbranch₂⟩
  rcases List.mem_flatMap.mp hbranch₂ with ⟨n, _hn, hbranch₃⟩
  rcases List.mem_flatMap.mp hbranch₃ with ⟨q, _hq, hbranch₄⟩
  rcases List.mem_map.mp hbranch₄ with ⟨r, _hr, heq⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  simp [extractedProfile, mkFullTypedState]

lemma terminal_mem_extractedR
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (X : FullTypedState G M)
    (a : Sigma)
    (hmem : (X, a) ∈ fullTerminalRules G H)
    (hsurv : IsProductive G H X ∧ IsReachable G H X) :
    ∃ tr : CarrierTerminalRule H (extractedProfile G H),
      tr.X = ({ val := X, property := hsurv } : TrimmedState G H)
      ∧ tr.a = a
      ∧ CarrierTypedRule.terminal tr ∈ extractedR G H := by
  classical
  let Xt : TrimmedState G H := { val := X, property := hsurv }
  have htype : H.h [a] = (extractedProfile G H Xt).yt :=
    fullTerminalRules_type_eq G H X a hmem hsurv
  let tr : CarrierTerminalRule H (extractedProfile G H) :=
    { X := Xt, a := a, type_eq := htype }
  refine ⟨tr, rfl, rfl, ?_⟩
  unfold extractedR
  apply List.mem_append_left
  apply List.mem_filterMap.mpr
  refine ⟨(X, a), hmem, ?_⟩
  dsimp only
  rw [dif_pos hsurv, dif_pos htype]

lemma binary_mem_extractedR
    (G : SSBNFGrammar Sigma)
    (H : FixedFiniteMonoidHom Sigma M)
    (X Y Z : FullTypedState G M)
    (hmem : (X, Y, Z) ∈ fullBinaryRules G)
    (hXsurv : IsProductive G H X ∧ IsReachable G H X)
    (hYsurv : IsProductive G H Y ∧ IsReachable G H Y)
    (hZsurv : IsProductive G H Z ∧ IsReachable G H Z) :
    ∃ br : CarrierBinaryRule (extractedProfile G H),
      br.X = ({ val := X, property := hXsurv } : TrimmedState G H)
      ∧ br.Y = ({ val := Y, property := hYsurv } : TrimmedState G H)
      ∧ br.Z = ({ val := Z, property := hZsurv } : TrimmedState G H)
      ∧ CarrierTypedRule.binary br ∈ extractedR G H := by
  classical
  let Xt : TrimmedState G H := { val := X, property := hXsurv }
  let Yt : TrimmedState G H := { val := Y, property := hYsurv }
  let Zt : TrimmedState G H := { val := Z, property := hZsurv }
  have hyield :
      (extractedProfile G H Xt).yt =
        (extractedProfile G H Yt).yt * (extractedProfile G H Zt).yt :=
    fullBinaryRules_yield_eq G H X Y Z hmem hXsurv hYsurv hZsurv
  have hleft_left :
      (extractedProfile G H Yt).lt = (extractedProfile G H Xt).lt :=
    fullBinaryRules_left_child_left_eq G H X Y Z hmem hXsurv hYsurv hZsurv
  have hleft_right :
      (extractedProfile G H Yt).rt =
        (extractedProfile G H Zt).yt * (extractedProfile G H Xt).rt :=
    fullBinaryRules_left_child_right_eq G H X Y Z hmem hXsurv hYsurv hZsurv
  have hright_left :
      (extractedProfile G H Zt).lt =
        (extractedProfile G H Xt).lt * (extractedProfile G H Yt).yt :=
    fullBinaryRules_right_child_left_eq G H X Y Z hmem hXsurv hYsurv hZsurv
  have hright_right :
      (extractedProfile G H Zt).rt = (extractedProfile G H Xt).rt :=
    fullBinaryRules_right_child_right_eq G H X Y Z hmem hXsurv hYsurv hZsurv
  let br : CarrierBinaryRule (extractedProfile G H) :=
    { X := Xt, Y := Yt, Z := Zt
      yield_eq := hyield
      left_child_left_eq := hleft_left
      left_child_right_eq := hleft_right
      right_child_left_eq := hright_left
      right_child_right_eq := hright_right }
  refine ⟨br, rfl, rfl, rfl, ?_⟩
  unfold extractedR
  apply List.mem_append_right
  apply List.mem_filterMap.mpr
  refine ⟨(X, Y, Z), hmem, ?_⟩
  dsimp only
  rw [dif_pos hXsurv, dif_pos hYsurv, dif_pos hZsurv,
      dif_pos hyield, dif_pos hleft_left, dif_pos hleft_right,
      dif_pos hright_left, dif_pos hright_right]

end Extraction

end

end TwoSidedTypedCFG
