import LeanCfgProject.SCLCompression.CanonicalRelation
import LeanCfgProject.SCLCompression.CompatibleTolerance

namespace LeanCfgProject
namespace SCLCompression

universe u v w

/-- Choose one relational-fibre value for each free generator. -/
noncomputable def selectedGenerator
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (eta : Word Sigma →* T) (rho : RelMorphism T M) (a : Sigma) : M :=
  Classical.choose (rho.nonempty (eta [a]))

/-- The selected generator value really lies in the required relational fibre. -/
theorem selectedGenerator_mem
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (eta : Word Sigma →* T) (rho : RelMorphism T M) (a : Sigma) :
    selectedGenerator eta rho a ∈ rho.fiber (eta [a]) := by
  exact Classical.choose_spec (rho.nonempty (eta [a]))

/-- The functional compression witness extracted from an arbitrary relation. -/
noncomputable def selectedHom
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (eta : Word Sigma →* T) (rho : RelMorphism T M) : Word Sigma →* M :=
  selectorHom (selectedGenerator eta rho)

/-- Every selected word value remains inside the original relational fibre. -/
theorem selectedHom_mem_fiber
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (eta : Word Sigma →* T) (rho : RelMorphism T M) (word : Word Sigma) :
    selectedHom eta rho word ∈ rho.fiber (eta word) := by
  exact selector_mem_fiber eta rho (selectedGenerator eta rho)
    (selectedGenerator_mem eta rho) word

/--
The canonical fibres of the selected homomorphism are pointwise contained in
the original relational fibres.  This is the key inclusion in the reverse
direction of Theorem `alg:thm:relational-characterization`.
-/
theorem selectedCanonical_fiber_subset
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (eta : Word Sigma →* T) (heta : Function.Surjective eta)
    (rho : RelMorphism T M) (t : T) :
    (canonicalRel eta heta (selectedHom eta rho)).fiber t ⊆ rho.fiber t := by
  exact canonicalFiber_selector_subset eta rho (selectedGenerator eta rho)
    (selectedGenerator_mem eta rho) t

/--
Any finite-profile separation witnessed by an arbitrary relational morphism is
preserved by the canonical relation of the selected functional witness.
-/
theorem selectedCanonical_preserves_separation
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (eta : Word Sigma →* T) (heta : Function.Surjective eta)
    (rho : RelMorphism T M)
    (UnsafeProfile : (d : Nat) → Tuple T d → Tuple T d → Prop)
    (f : Nat)
    (hsep : rho.SeparatesProfilesThrough UnsafeProfile f) :
    (canonicalRel eta heta (selectedHom eta rho)).SeparatesProfilesThrough
      UnsafeProfile f := by
  exact RelMorphism.separatesProfiles_mono UnsafeProfile
    (fun t => selectedCanonical_fiber_subset eta heta rho t) hsep

end SCLCompression
end LeanCfgProject
