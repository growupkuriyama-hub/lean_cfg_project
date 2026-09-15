import LeanCfgProject.FixedHCFGv44.ClarkCongruentialPresentationV49
import LeanCfgProject.FixedHCFGv44.ClarkDyckStrictnessV49

namespace LeanCfgProject
namespace FixedHCFGv44

/-!
Helper languages for turning the Dyck strictness core into an actual finite
congruential SSBNF presentation.

The eventual SSBNF realization of the recursive equation

  D = {epsilon} ∪ a D b D

needs intermediate nonterminals for a balanced block followed by `b`, for `b`
followed by a balanced block, and for two balanced blocks separated by `b`.
This file isolates the congruence argument for those helper languages.  The
remaining task is the grammar-language equality, whose nontrivial direction is
the first-return decomposition of an operational Dyck word.
-/

/-- Appending and prepending fixed terminal contexts preserves syntactic
congruence when the varying middle factors are balanced Dyck words. -/
theorem dyck1_fixed_context_sameDistribution_v49
    {x y l r : Word DyckLetter}
    (hx : x ∈ Dyck1) (hy : y ∈ Dyck1) :
    SameDistribution Dyck1 (l ++ x ++ r) (l ++ y ++ r) := by
  intro p q
  constructor
  · intro h
    have h' : (p ++ l) ++ x ++ (r ++ q) ∈ Dyck1 := by
      simpa only [List.append_assoc] using h
    have hrep := dyck1_balanced_replacement hx hy h'
    simpa only [List.append_assoc] using hrep
  · intro h
    have h' : (p ++ l) ++ y ++ (r ++ q) ∈ Dyck1 := by
      simpa only [List.append_assoc] using h
    have hrep := dyck1_balanced_replacement hy hx h'
    simpa only [List.append_assoc] using hrep

/-- Transitivity of two-sided syntactic-distribution equality. -/
theorem sameDistribution_trans_v49
    {Sigma : Type} {L : Language Sigma}
    {x y z : Word Sigma}
    (hxy : SameDistribution L x y)
    (hyz : SameDistribution L y z) :
    SameDistribution L x z := by
  intro p q
  exact (hxy p q).trans (hyz p q)

/-- Nonempty balanced block followed by one closing symbol. -/
def DyckBalancedCloseV49 : Language DyckLetter :=
  fun w => ∃ x : Word DyckLetter, x ∈ Dyck1 ∧ w = x ++ [DyckLetter.b]

/-- One closing symbol followed by a nonempty-or-empty balanced block. -/
def DyckCloseBalancedV49 : Language DyckLetter :=
  fun w => ∃ x : Word DyckLetter, x ∈ Dyck1 ∧ w = [DyckLetter.b] ++ x

/-- Two balanced blocks separated by one closing symbol. -/
def DyckBalancedCloseBalancedV49 : Language DyckLetter :=
  fun w => ∃ x y : Word DyckLetter,
    x ∈ Dyck1 ∧ y ∈ Dyck1 ∧
      w = x ++ [DyckLetter.b] ++ y

/-- The `D b` helper language is contained in one syntactic class of `D`. -/
theorem dyckBalancedClose_syntacticallyHomogeneous_v49 :
    SyntacticallyHomogeneousV49 Dyck1 DyckBalancedCloseV49 := by
  intro u hu v hv
  rcases hu with ⟨x, hx, rfl⟩
  rcases hv with ⟨y, hy, rfl⟩
  simpa using
    (dyck1_fixed_context_sameDistribution_v49
      (l := ([] : Word DyckLetter))
      (r := [DyckLetter.b]) hx hy)

/-- The `b D` helper language is contained in one syntactic class of `D`. -/
theorem dyckCloseBalanced_syntacticallyHomogeneous_v49 :
    SyntacticallyHomogeneousV49 Dyck1 DyckCloseBalancedV49 := by
  intro u hu v hv
  rcases hu with ⟨x, hx, rfl⟩
  rcases hv with ⟨y, hy, rfl⟩
  simpa using
    (dyck1_fixed_context_sameDistribution_v49
      (l := [DyckLetter.b])
      (r := ([] : Word DyckLetter)) hx hy)

/-- The `D b D` helper language is contained in one syntactic class of `D`. -/
theorem dyckBalancedCloseBalanced_syntacticallyHomogeneous_v49 :
    SyntacticallyHomogeneousV49 Dyck1 DyckBalancedCloseBalancedV49 := by
  intro u hu v hv
  rcases hu with ⟨x₁, y₁, hx₁, hy₁, rfl⟩
  rcases hv with ⟨x₂, y₂, hx₂, hy₂, rfl⟩
  have hLeft :
      SameDistribution Dyck1
        (x₁ ++ [DyckLetter.b] ++ y₁)
        (x₂ ++ [DyckLetter.b] ++ y₁) := by
    simpa only [List.nil_append, List.append_assoc] using
      (dyck1_fixed_context_sameDistribution_v49
        (l := ([] : Word DyckLetter))
        (r := [DyckLetter.b] ++ y₁) hx₁ hx₂)
  have hRight :
      SameDistribution Dyck1
        (x₂ ++ [DyckLetter.b] ++ y₁)
        (x₂ ++ [DyckLetter.b] ++ y₂) := by
    simpa only [List.append_assoc, List.append_nil] using
      (dyck1_fixed_context_sameDistribution_v49
        (l := x₂ ++ [DyckLetter.b])
        (r := ([] : Word DyckLetter)) hy₁ hy₂)
  exact sameDistribution_trans_v49 hLeft hRight

end FixedHCFGv44
end LeanCfgProject
