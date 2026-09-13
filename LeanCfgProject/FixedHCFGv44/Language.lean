import LeanCfgProject.FixedHCFGv44.Observer

namespace LeanCfgProject
namespace FixedHCFGv44

universe u

/-- A language over `Sigma`. -/
abbrev Language (Sigma : Type u) := Set (Word Sigma)

/-- A word is an admissible internal fragment in v44 exactly when it is nonempty. -/
def Internal {Sigma : Type u} (x : Word Sigma) : Prop :=
  x ≠ []

/-- A two-sided context belongs to the distribution of `x` in `L`. -/
def InDistribution {Sigma : Type u} (L : Language Sigma)
    (x u v : Word Sigma) : Prop :=
  u ++ x ++ v ∈ L

/-- Two strings have the same two-sided distribution in `L`. -/
def SameDistribution {Sigma : Type u} (L : Language Sigma)
    (x y : Word Sigma) : Prop :=
  ∀ u v : Word Sigma,
    InDistribution L x u v ↔ InDistribution L y u v

/-- Two strings have at least one common context in `L`. -/
def ShareContext {Sigma : Type u} (L : Language Sigma)
    (x y : Word Sigma) : Prop :=
  ∃ u v : Word Sigma,
    InDistribution L x u v ∧ InDistribution L y u v

/--
v44 Definition 2.1 / fixed-h substitutability.

Only nonempty internal fragments are compared.  The empty word is handled
separately at the learner start symbol, exactly as in the revised manuscript.
-/
def HSubstitutable {Sigma : Type u} (Obs : Observer Sigma)
    (L : Language Sigma) : Prop :=
  ∀ x y : Word Sigma,
    Internal x →
    Internal y →
    obsValue Obs x = obsValue Obs y →
    ShareContext L x y →
    SameDistribution L x y

/-- Symmetry of distribution equality. -/
theorem sameDistribution_symm {Sigma : Type u} {L : Language Sigma}
    {x y : Word Sigma} (h : SameDistribution L x y) :
    SameDistribution L y x := by
  intro u v
  exact (h u v).symm

/-- A shared context is symmetric. -/
theorem shareContext_symm {Sigma : Type u} {L : Language Sigma}
    {x y : Word Sigma} (h : ShareContext L x y) :
    ShareContext L y x := by
  rcases h with ⟨u, v, hx, hy⟩
  exact ⟨u, v, hy, hx⟩

end FixedHCFGv44
end LeanCfgProject
