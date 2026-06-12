import LeanCfgProject.ObservedResidualConcept.ObservationFinite
import LeanCfgProject.ObservedResidualConcept.ObservationCounterexample_v2
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG
open CExSym
open Parity

theorem observationSignature_a_eq_c :
    ObservationSignature parityHom counterexampleLanguage [a] =
      ObservationSignature parityHom counterexampleLanguage [c] := by
  exact
    (sameHTypedObservation_kernel
      parityHom counterexampleLanguage [a] [c]).mp
      same_observation_a_c

theorem observationSignature_b_eq_b :
    ObservationSignature parityHom counterexampleLanguage [b] =
      ObservationSignature parityHom counterexampleLanguage [b] := by
  rfl

theorem observationSignature_ab_ne_cb :
    ObservationSignature parityHom counterexampleLanguage [a, b] ≠
      ObservationSignature parityHom counterexampleLanguage [c, b] := by
  intro hsig
  have hobs :
      SameHTypedObservation
        parityHom counterexampleLanguage [a, b] [c, b] :=
    (sameHTypedObservation_kernel
      parityHom counterexampleLanguage [a, b] [c, b]).mpr hsig
  exact not_same_observation_ab_cb hobs

theorem observationSignature_not_concat_compatible :
    ∃ u v s t : Word CExSym,
      ObservationSignature parityHom counterexampleLanguage u =
        ObservationSignature parityHom counterexampleLanguage v ∧
      ObservationSignature parityHom counterexampleLanguage s =
        ObservationSignature parityHom counterexampleLanguage t ∧
      ObservationSignature parityHom counterexampleLanguage (u ++ s) ≠
        ObservationSignature parityHom counterexampleLanguage (v ++ t) := by
  refine ⟨[a], [c], [b], [b], ?_, ?_, ?_⟩
  · exact observationSignature_a_eq_c
  · exact observationSignature_b_eq_b
  · simpa using observationSignature_ab_ne_cb

end LeanCfgProject
