import LeanCfgProject.LanguageQuotient

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG

universe u

def ObservationSignature
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u : Word Sigma) :
    M × Set (M × M) :=
  (H.h u, HTypedContextTypes H L u)

theorem observationSignature_eq_of_sameHTypedObservation
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) :
    SameHTypedObservation H L u v →
    ObservationSignature H L u = ObservationSignature H L v := by
  intro h
  cases h with
  | intro h_yield h_ctx =>
      unfold ObservationSignature
      simp [h_yield, h_ctx]

theorem sameHTypedObservation_of_observationSignature_eq
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) :
    ObservationSignature H L u = ObservationSignature H L v →
    SameHTypedObservation H L u v := by
  intro hsig
  constructor
  · exact congrArg Prod.fst hsig
  · exact congrArg Prod.snd hsig

theorem sameHTypedObservation_iff_observationSignature_eq
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) :
    SameHTypedObservation H L u v ↔
      ObservationSignature H L u = ObservationSignature H L v := by
  constructor
  · exact observationSignature_eq_of_sameHTypedObservation H L u v
  · exact sameHTypedObservation_of_observationSignature_eq H L u v

theorem sameHTypedObservation_kernel
    {Sigma M : Type u}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Sigma M)
    (L : Language Sigma)
    (u v : Word Sigma) :
    SameHTypedObservation H L u v ↔
      ObservationSignature H L u = ObservationSignature H L v :=
  sameHTypedObservation_iff_observationSignature_eq H L u v

end LeanCfgProject
