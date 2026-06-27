import LeanCfgProject.MCFG.FI_v2_1_PresentationRecoveryGold

/-!
# FI v2.1 Lean experiment: main-theorem interface

This seventy-seventh layer packages the current presentation-relative recovery
infrastructure as a conservative main-theorem interface.

It is still **not** the full proof of the paper's reconstruction theorem: the
actual construction of the canonical learner grammar and of the
presentation-relative characteristic sample remains abstract.  What is checked
here is the final certificate shape: a sample-indexed canonical learner package
together with a presentation-relative characteristic-sample certificate implies
Gold-style distributional identification.
-/

namespace FIv21

universe u v w

noncomputable section

section MainTheoremInterface

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Conservative main-theorem package for the fixed-monoid MCFG learner.

A package consists of a sample-indexed canonical learner grammar package and a
presentation-relative characteristic-sample certificate for it.  The latter is
still assumed rather than constructed. -/
structure FixedMonoidMCFGLearningMainPackage
    (G : WorkingMCFG N α) (obs : α → M) where
  learner : CanonicalLearnerGrammarLearner G obs
  characteristic : CanonicalPresentationRecoveryCharacteristicSample learner

namespace FixedMonoidMCFGLearningMainPackage

/-- The finite-hypothesis learner underlying the canonical learner package. -/
def toFiniteHypothesisLearner
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FixedMonoidMCFGLearningMainPackage G obs) :
    FiniteHypothesisLearner α :=
  C.learner.toFiniteHypothesisLearner

/-- The finite characteristic sample displayed by the underlying certificate. -/
def characteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FixedMonoidMCFGLearningMainPackage G obs) :
    Finset (Word α) :=
  C.characteristic.base.base.base.base.base.base.startWitness.base.sample

/-- Forget to the presentation-relative characteristic-sample certificate. -/
def toPresentationRecoveryCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FixedMonoidMCFGLearningMainPackage G obs) :
    CanonicalPresentationRecoveryCharacteristicSample C.learner :=
  C.characteristic

/-- Forget to the bounded-data recovery characteristic-sample certificate. -/
def toBoundedDataRecoveryCharacteristicSample
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FixedMonoidMCFGLearningMainPackage G obs) :
    CanonicalBoundedDataRecoveryCharacteristicSample C.learner :=
  C.characteristic.toBoundedDataRecoveryCharacteristicSample

/-- The package yields Gold-style identification in the distributional sense. -/
theorem identifiesInLimit
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FixedMonoidMCFGLearningMainPackage G obs) :
    FiniteHypothesisIdentifiesGrammarInLimit C.learner.toFiniteHypothesisLearner G := by
  exact C.characteristic.identifiesInLimit

/-- The package yields eventual correctness of named-context distributions. -/
theorem eventuallyCorrectContexts
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FixedMonoidMCFGLearningMainPackage G obs) :
    FiniteHypothesisEventuallyCorrectContexts
      C.learner.toFiniteHypothesisLearner G.StringLanguage := by
  exact C.characteristic.eventuallyCorrectContexts

/-- The characteristic sample is positive for the target grammar language. -/
theorem characteristicSample_positive
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FixedMonoidMCFGLearningMainPackage G obs) :
    PositiveForLanguage C.characteristicSample G.StringLanguage := by
  exact C.characteristic.base.base.base.base.base.base.startWitness.base.positive

end FixedMonoidMCFGLearningMainPackage

end MainTheoremInterface

end

end FIv21
