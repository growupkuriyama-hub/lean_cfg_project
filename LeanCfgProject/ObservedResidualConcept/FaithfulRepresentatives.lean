import LeanCfgProject.ObservedResidualConcept.FiniteSetQueryReconstruction
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u v

/-
FaithfulRepresentatives.lean

Representative-access reconstruction layer.

This abstracts the situation where each observed value has a chosen word-like
representative whose membership answer matches membership in the observed
subset.
-/

/--
A system of representatives for an observed subset S. The type W may be a word
type, but no word-specific structure is needed for this abstract layer.
-/
structure FaithfulRepresentatives
    (W : Type u) (Q : Type v)
    (L : Set W) (q : W → Q) (S : Set Q) where
  rep : Q → W
  rep_observes : ∀ s : Q, q (rep s) = s
  rep_membership : ∀ s : Q, rep s ∈ L ↔ s ∈ S

/--
The observed subset is recovered from the membership answers of faithful
representatives.
-/
theorem observedSubset_eq_representative_membership
    {W : Type u} {Q : Type v}
    {L : Set W} {q : W → Q} {S : Set Q}
    (R : FaithfulRepresentatives W Q L q S) :
    S = {s : Q | R.rep s ∈ L} := by
  ext s
  constructor
  · intro hs
    exact (R.rep_membership s).2 hs
  · intro hs
    exact (R.rep_membership s).1 hs

/--
Two observed subsets with the same faithful representative membership answers
are equal.
-/
theorem observedSubset_eq_of_same_representative_answers
    {W : Type u} {Q : Type v}
    {L : Set W} {q : W → Q} {S T : Set Q}
    (R : FaithfulRepresentatives W Q L q S)
    (hT : ∀ s : Q, R.rep s ∈ L ↔ s ∈ T) :
    S = T := by
  apply finiteSet_eq_of_same_membership
  intro s
  exact (R.rep_membership s).symm.trans (hT s)

end LeanCfgProject
