import LeanCfgProject.StateSemantics

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG

universe u

def HTypedContextTypes
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u : Word Sigma) :
    Set (M × M) :=
  { mn | ∃ l r : Word Sigma,
      mn = (H.h l, H.h r) ∧
      l ++ u ++ r ∈ L }

def SameHTypedObservation
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) : Prop :=
  H.h u = H.h v ∧
  HTypedContextTypes H L u = HTypedContextTypes H L v

def SameHTypedSyntacticObservation
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) : Prop :=
  ∀ x y : Word Sigma,
    SameHTypedObservation H L (x ++ u ++ y) (x ++ v ++ y)

def SameSyntacticContext
    {Sigma : Type u}
    (L : Language Sigma)
    (u v : Word Sigma) : Prop :=
  ∀ x y : Word Sigma,
    (x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L)

def SameHTypedPointedObservation
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) : Prop :=
  H.h u = H.h v ∧
  (u ∈ L ↔ v ∈ L) ∧
  HTypedContextTypes H L u = HTypedContextTypes H L v

def SameHTypedPointedSyntacticObservation
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) : Prop :=
  ∀ x y : Word Sigma,
    SameHTypedPointedObservation H L (x ++ u ++ y) (x ++ v ++ y)

theorem sameHTypedObservation_refl
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u : Word Sigma) :
    SameHTypedObservation H L u u := by
  constructor
  · rfl
  · rfl

theorem sameHTypedObservation_symm
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) :
    SameHTypedObservation H L u v →
    SameHTypedObservation H L v u := by
  intro h
  constructor
  · exact h.1.symm
  · exact h.2.symm

theorem sameHTypedObservation_trans
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v w : Word Sigma) :
    SameHTypedObservation H L u v →
    SameHTypedObservation H L v w →
    SameHTypedObservation H L u w := by
  intro huv hvw
  constructor
  · exact huv.1.trans hvw.1
  · exact huv.2.trans hvw.2

theorem sameHTypedSyntacticObservation_refl
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u : Word Sigma) :
    SameHTypedSyntacticObservation H L u u := by
  intro x y
  exact sameHTypedObservation_refl H L (x ++ u ++ y)

theorem sameHTypedSyntacticObservation_symm
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) :
    SameHTypedSyntacticObservation H L u v →
    SameHTypedSyntacticObservation H L v u := by
  intro h x y
  exact sameHTypedObservation_symm H L (x ++ u ++ y) (x ++ v ++ y) (h x y)

theorem sameHTypedSyntacticObservation_trans
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v w : Word Sigma) :
    SameHTypedSyntacticObservation H L u v →
    SameHTypedSyntacticObservation H L v w →
    SameHTypedSyntacticObservation H L u w := by
  intro huv hvw x y
  exact sameHTypedObservation_trans H L (x ++ u ++ y) (x ++ v ++ y) (x ++ w ++ y)
    (huv x y) (hvw x y)

theorem sameHTypedSyntacticObservation_implies_observation
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) :
    SameHTypedSyntacticObservation H L u v →
    SameHTypedObservation H L u v := by
  intro h
  simpa using h [] []

theorem sameHTypedSyntacticObservation_left
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v s : Word Sigma) :
    SameHTypedSyntacticObservation H L u v →
    SameHTypedSyntacticObservation H L (s ++ u) (s ++ v) := by
  intro h x y
  simpa [List.append_assoc] using h (x ++ s) y

theorem sameHTypedSyntacticObservation_right
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v t : Word Sigma) :
    SameHTypedSyntacticObservation H L u v →
    SameHTypedSyntacticObservation H L (u ++ t) (v ++ t) := by
  intro h x y
  simpa [List.append_assoc] using h x (t ++ y)

theorem sameHTypedSyntacticObservation_concat
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u₁ v₁ u₂ v₂ : Word Sigma) :
    SameHTypedSyntacticObservation H L u₁ v₁ →
    SameHTypedSyntacticObservation H L u₂ v₂ →
    SameHTypedSyntacticObservation H L (u₁ ++ u₂) (v₁ ++ v₂) := by
  intro h1 h2
  have hleft : SameHTypedSyntacticObservation H L (u₁ ++ u₂) (v₁ ++ u₂) :=
    sameHTypedSyntacticObservation_right H L u₁ v₁ u₂ h1
  have hright : SameHTypedSyntacticObservation H L (v₁ ++ u₂) (v₁ ++ v₂) :=
    sameHTypedSyntacticObservation_left H L u₂ v₂ v₁ h2
  exact sameHTypedSyntacticObservation_trans H L (u₁ ++ u₂) (v₁ ++ u₂) (v₁ ++ v₂) hleft hright

theorem sameHTypedPointedObservation_refl
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u : Word Sigma) :
    SameHTypedPointedObservation H L u u := by
  constructor
  · rfl
  · constructor
    · exact Iff.rfl
    · rfl

theorem sameHTypedPointedObservation_symm
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) :
    SameHTypedPointedObservation H L u v →
    SameHTypedPointedObservation H L v u := by
  intro h
  constructor
  · exact h.1.symm
  · constructor
    · exact h.2.1.symm
    · exact h.2.2.symm

theorem sameHTypedPointedObservation_trans
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v w : Word Sigma) :
    SameHTypedPointedObservation H L u v →
    SameHTypedPointedObservation H L v w →
    SameHTypedPointedObservation H L u w := by
  intro huv hvw
  constructor
  · exact huv.1.trans hvw.1
  · constructor
    · exact Iff.trans huv.2.1 hvw.2.1
    · exact huv.2.2.trans hvw.2.2

theorem sameHTypedPointedSyntacticObservation_refl
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u : Word Sigma) :
    SameHTypedPointedSyntacticObservation H L u u := by
  intro x y
  exact sameHTypedPointedObservation_refl H L (x ++ u ++ y)

theorem pointedSynObs_implies_syntacticContext
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) :
    SameHTypedPointedSyntacticObservation H L u v →
    SameSyntacticContext L u v := by
  intro h x y
  exact (h x y).2.1

theorem pointedSynObs_implies_h_eq
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) :
    SameHTypedPointedSyntacticObservation H L u v →
    H.h u = H.h v := by
  intro h
  have h0 := (h [] []).1
  simpa using h0

-- Target theorem, intentionally left as a comment rather than an unfinished theorem:
-- If SameSyntacticContext L u v and H.h u = H.h v, then
-- SameHTypedPointedSyntacticObservation H L u v.
-- The proof should use set extensionality for HTypedContextTypes and H.map_append.
-- It is not included here so that this file remains placeholder-free and assumption-free.

end LeanCfgProject.JALC