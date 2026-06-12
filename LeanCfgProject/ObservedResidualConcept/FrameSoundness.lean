import LeanCfgProject.ObservedResidualConcept.CarrierConceptSemantics
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open TwoSidedTypedCFG.RuleFamilies

universe u v

/--
Yield soundness for carrier typed rules: every generated word has the
`h`-yield value recorded in the state's profile.

This is the first place where the `yield_eq` field of `CarrierBinaryRule`
is used as an actual semantic invariant rather than as stored data.
-/
theorem carrier_yield_frame_sound
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    {X : W}
    {w : Word Sigma}
    (hy : YieldFamily H profile R X w) :
    H.h w = (profile X).yt := by
  induction hy with
  | terminal tr hmem =>
      simpa using tr.type_eq
  | binary br hmem hY hZ ihY ihZ =>
      calc
        H.h (_ ++ _) = H.h _ * H.h _ := H.map_append _ _
        _ = (profile br.Y).yt * (profile br.Z).yt := by
          rw [ihY, ihZ]
        _ = (profile br.X).yt := by
          exact br.yield_eq.symm

/--
Context soundness for carrier typed rules.

The start-frame hypothesis is necessary: the present `ContextFamily.start`
constructor only says that the external words are both empty; it does not
store that the chosen start state has profile frame `(1,1)`.
-/
theorem carrier_context_frame_sound
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    H.h ell = (profile X).lt ∧ H.h r = (profile X).rt := by
  induction hctx with
  | start x hmem =>
      have hs := hStartFrame x hmem
      constructor
      · calc
          H.h [] = 1 := H.map_empty
          _ = (profile x).lt := hs.1.symm
      · calc
          H.h [] = 1 := H.map_empty
          _ = (profile x).rt := hs.2.symm
  | binary_left br hmem hctx hz ih =>
      have hzSound := carrier_yield_frame_sound H profile R hz
      constructor
      · calc
          H.h _ = (profile br.X).lt := ih.1
          _ = (profile br.Y).lt := br.left_child_left_eq.symm
      · calc
          H.h (_ ++ _) = H.h _ * H.h _ := H.map_append _ _
          _ = (profile br.Z).yt * (profile br.X).rt := by
            rw [hzSound, ih.2]
          _ = (profile br.Y).rt := br.left_child_right_eq.symm
  | binary_right br hmem hctx hyLeft ih =>
      have hySound := carrier_yield_frame_sound H profile R hyLeft
      constructor
      · calc
          H.h (_ ++ _) = H.h _ * H.h _ := H.map_append _ _
          _ = (profile br.X).lt * (profile br.Y).yt := by
            rw [ih.1, hySound]
          _ = (profile br.Z).lt := br.right_child_left_eq.symm
      · calc
          H.h _ = (profile br.X).rt := ih.2
          _ = (profile br.Z).rt := br.right_child_right_eq.symm

/--
For the standard observation `q = h`, the two-sided frame of a witnessed
context determines the residual bound of the carrier state semantics.
-/
theorem carrier_state_semantics_subset_frame_residual_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    CarrierStateSemantics H.h H profile R X ⊆
      TwoSidedResidual
        (ImageOfLanguage H.h (CarrierStartLanguage H profile R S0))
        (profile X).lt
        (profile X).rt := by
  have hFrame := carrier_context_frame_sound H profile R S0 hStartFrame hctx
  have hResidual :=
    carrier_state_semantics_subset_residual
      H.h H.map_append H profile R S0 ell r hctx
  simpa [hFrame.1, hFrame.2] using hResidual

/--
Intent form of the previous theorem: the typed frame `(lt,rt)` is a common
context of the state semantics in the residual concept incidence.
-/
theorem carrier_frame_mem_commonContexts_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    ((profile X).lt, (profile X).rt) ∈
      CommonContexts
        (ImageOfLanguage H.h (CarrierStartLanguage H profile R S0))
        (CarrierStateSemantics H.h H profile R X) := by
  intro gamma hgamma
  exact carrier_state_semantics_subset_frame_residual_h
    H profile R S0 hStartFrame hctx hgamma

/--
Closure-level form: after concept closure, the carrier concept semantics is
contained in the closure of the residual determined by the typed frame.
-/
theorem carrier_concept_semantics_subset_frame_residual_closure_h
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    CarrierConceptSemantics
        (ImageOfLanguage H.h (CarrierStartLanguage H profile R S0))
        H.h H profile R X ⊆
      ConceptClosure
        (ImageOfLanguage H.h (CarrierStartLanguage H profile R S0))
        (TwoSidedResidual
          (ImageOfLanguage H.h (CarrierStartLanguage H profile R S0))
          (profile X).lt
          (profile X).rt) := by
  unfold CarrierConceptSemantics
  exact conceptClosure_mono _
    (carrier_state_semantics_subset_frame_residual_h
      H profile R S0 hStartFrame hctx)

/--
Frame residual soundness for any observation factoring through `h`.
-/
theorem carrier_state_semantics_subset_frame_residual_factor
    {Sigma : Type u}
    {M : Type u} [Monoid M] [Fintype M]
    {Q : Type v} [Monoid Q]
    (theta : M →* Q)
    (H : FixedFiniteMonoidHom Sigma M)
    {W : Type u}
    (profile : W → TypedState M)
    (R : List (CarrierTypedRule H profile))
    (S0 : Finset W)
    (hStartFrame :
      ∀ X : W, X ∈ S0 → (profile X).lt = 1 ∧ (profile X).rt = 1)
    {X : W}
    {ell r : Word Sigma}
    (hctx : ContextFamily H profile R S0 X ell r) :
    CarrierStateSemantics (fun w : Word Sigma => theta (H.h w)) H profile R X ⊆
      TwoSidedResidual
        (ImageOfLanguage (fun w : Word Sigma => theta (H.h w))
          (CarrierStartLanguage H profile R S0))
        (theta ((profile X).lt))
        (theta ((profile X).rt)) := by
  let q : Word Sigma → Q := fun w => theta (H.h w)
  have q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v := by
    intro u v
    dsimp [q]
    rw [H.map_append]
    simp
  have hFrame := carrier_context_frame_sound H profile R S0 hStartFrame hctx
  have hResidual :=
    carrier_state_semantics_subset_residual
      q q_mul H profile R S0 ell r hctx
  have hleft : q ell = theta ((profile X).lt) := by
    dsimp [q]
    rw [hFrame.1]
  have hright : q r = theta ((profile X).rt) := by
    dsimp [q]
    rw [hFrame.2]
  simpa [q, hleft, hright] using hResidual

end LeanCfgProject
