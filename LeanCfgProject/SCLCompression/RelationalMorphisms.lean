import LeanCfgProject.SCLCompression.SafetyInterface

namespace LeanCfgProject
namespace SCLCompression

universe u v

/--
A finite-semigroup style relational morphism, represented by its nonempty
fibres.  For the first verification phase we record exactly the multiplicative
properties used in the #3 manuscript.
-/
structure RelMorphism (T : Type u) (M : Type v) [Monoid T] [Monoid M] where
  fiber : T → Set M
  nonempty : ∀ t, (fiber t).Nonempty
  one_mem : (1 : M) ∈ fiber 1
  mul_mem : ∀ {s t : T} {m n : M},
    m ∈ fiber s → n ∈ fiber t → m * n ∈ fiber (s * t)

namespace RelMorphism

variable {T : Type u} {M : Type v} [Monoid T] [Monoid M]

/-- Two source elements are separated when their relational fibres are disjoint. -/
def FiberSeparated (ρ : RelMorphism T M) (s t : T) : Prop :=
  ∀ m : M, m ∈ ρ.fiber s → m ∈ ρ.fiber t → False

/-- Pointwise containment of relational fibres. -/
def FiberwiseSubrelation (ρ' ρ : RelMorphism T M) : Prop :=
  ∀ t, ρ'.fiber t ⊆ ρ.fiber t

/-- Shrinking both fibres preserves disjointness. -/
theorem fiberSeparated_mono {ρ' ρ : RelMorphism T M}
    (hsub : FiberwiseSubrelation ρ' ρ) {s t : T}
    (hsep : FiberSeparated ρ s t) : FiberSeparated ρ' s t := by
  intro m hms hmt
  exact hsep m (hsub s hms) (hsub t hmt)

/--
Abstract finite-profile unsafe clauses for a pointed syntactic monoid.  The
concrete profile relation will be connected to the manuscript's
`mathcal U_d(T,P)` in a later layer.
-/
def SeparatesProfilesThrough
    (UnsafeProfile : (d : Nat) → Tuple T d → Tuple T d → Prop)
    (ρ : RelMorphism T M) (f : Nat) : Prop :=
  ∀ d, 1 ≤ d → d ≤ f → ∀ s t : Tuple T d,
    UnsafeProfile d s t → ∃ i, FiberSeparated ρ (s i) (t i)

/--
The monotonicity step used in the relational-morphism characterization:
if every canonical fibre is contained in an arbitrary relational fibre, then
any separating coordinate for the latter also separates for the former.
-/
theorem separatesProfiles_mono
    (UnsafeProfile : (d : Nat) → Tuple T d → Tuple T d → Prop)
    {ρ' ρ : RelMorphism T M} {f : Nat}
    (hsub : FiberwiseSubrelation ρ' ρ)
    (hsep : SeparatesProfilesThrough UnsafeProfile ρ f) :
    SeparatesProfilesThrough UnsafeProfile ρ' f := by
  intro d hdpos hdf s t hunsafe
  obtain ⟨i, hi⟩ := hsep d hdpos hdf s t hunsafe
  exact ⟨i, fiberSeparated_mono hsub hi⟩

/-- The codomain values actually used by a relational morphism form a submonoid. -/
def usedSubmonoid (ρ : RelMorphism T M) : Submonoid M where
  carrier := {m | ∃ t : T, m ∈ ρ.fiber t}
  one_mem' := ⟨1, ρ.one_mem⟩
  mul_mem' := by
    rintro a b ⟨s, ha⟩ ⟨t, hb⟩
    exact ⟨s * t, ρ.mul_mem ha hb⟩

@[simp] theorem mem_usedSubmonoid_iff (ρ : RelMorphism T M) (m : M) :
    m ∈ ρ.usedSubmonoid ↔ ∃ t : T, m ∈ ρ.fiber t := by
  rfl

/-- Every relational fibre lies inside the used-codomain submonoid. -/
theorem fiber_subset_usedSubmonoid (ρ : RelMorphism T M) (t : T) :
    ρ.fiber t ⊆ (ρ.usedSubmonoid : Set M) := by
  intro m hm
  exact ⟨t, hm⟩

end RelMorphism

end SCLCompression
end LeanCfgProject
