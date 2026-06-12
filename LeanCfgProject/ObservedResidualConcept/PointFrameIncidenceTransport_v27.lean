import LeanCfgProject.ObservedResidualConcept.CanonicalPointFrameStablePackage_v27
import LeanCfgProject.ObservedResidualConcept.ObservedMembershipEquivalence_v27
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

universe u

/-
PointFrameIncidenceTransport_v27.lean

Transport of the canonical point-frame incidence core along observed
membership equivalence.
-/

variable {Q : Type u} [Mul Q]

theorem observedMembershipEquivalent_transport_point_frame_incidence
    {S T : Set Q}
    (h : ObservedMembershipEquivalent (Q := Q) S T)
    (gamma a b : Q) :
    (CanonicalPoint S gamma ⊆
        (canonicalObservedFrameStructure (Q := Q) S).residual a b)
      ↔
    (CanonicalPoint T gamma ⊆
        (canonicalObservedFrameStructure (Q := Q) T).residual a b) := by
  exact canonical_point_frame_incidence_respects_membership_equality
    (Q := Q) h gamma a b

theorem observedMembershipEquivalent_transport_point_collapse
    {S T : Set Q}
    (h : ObservedMembershipEquivalent (Q := Q) S T)
    (x y : Q) :
    (CanonicalPoint S x = CanonicalPoint S y)
      ↔
    (CanonicalPoint T x = CanonicalPoint T y) := by
  exact canonical_point_collapse_respects_membership_equality
    (Q := Q) h x y

theorem observedMembershipEquivalent_transport_observed_relation
    {S T : Set Q}
    (h : ObservedMembershipEquivalent (Q := Q) S T)
    (x y : Q) :
    (canonicalObservedFrameStructure (Q := Q) S).rel x y
      ↔
    (canonicalObservedFrameStructure (Q := Q) T).rel x y := by
  exact membership_identifies_observed_relation (Q := Q) h x y

theorem observedMembershipEquivalent_transport_residual_map
    {S T : Set Q}
    (h : ObservedMembershipEquivalent (Q := Q) S T)
    (a b : Q) :
    (canonicalObservedFrameStructure (Q := Q) S).residual a b =
      (canonicalObservedFrameStructure (Q := Q) T).residual a b := by
  exact membership_identifies_observed_residual_map (Q := Q) h a b

theorem observedMembershipEquivalent_transport_singleBlock_map
    {S T : Set Q}
    (h : ObservedMembershipEquivalent (Q := Q) S T)
    (a b : Q) :
    (canonicalObservedFrameStructure (Q := Q) S).singleBlock a b
      ↔
    (canonicalObservedFrameStructure (Q := Q) T).singleBlock a b := by
  exact membership_identifies_observed_singleBlock_map (Q := Q) h a b

end LeanCfgProject
