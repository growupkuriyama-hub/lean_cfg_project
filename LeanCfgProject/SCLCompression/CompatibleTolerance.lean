import LeanCfgProject.SCLCompression.RelationalMorphisms

namespace LeanCfgProject
namespace SCLCompression

universe u v

/--
A compatible tolerance on a monoid: reflexive, symmetric, and stable under
coordinatewise multiplication.  This is the exact relational notion used in
Section 8 of the #3 manuscript.
-/
def IsCompatibleTolerance {T : Type u} [Monoid T] (tau : T → T → Prop) : Prop :=
  (∀ x, tau x x) ∧
  (∀ x y, tau x y → tau y x) ∧
  (∀ x y u v, tau x y → tau u v → tau (x * u) (y * v))

/-- The overlap relation induced by a relational morphism. -/
def FiberOverlap {T : Type u} {M : Type v} [Monoid T] [Monoid M]
    (rho : RelMorphism T M) (x y : T) : Prop :=
  ∃ m : M, m ∈ rho.fiber x ∧ m ∈ rho.fiber y

/-- Relational-fibre separation is exactly failure of overlap. -/
theorem fiberSeparated_iff_not_overlap
    {T : Type u} {M : Type v} [Monoid T] [Monoid M]
    (rho : RelMorphism T M) (x y : T) :
    rho.FiberSeparated x y ↔ ¬ FiberOverlap rho x y := by
  constructor
  · intro hsep hoverlap
    rcases hoverlap with ⟨m, hx, hy⟩
    exact hsep m hx hy
  · intro hnot m hx hy
    exact hnot ⟨m, hx, hy⟩

/-- Lemma `alg:lem:relational-overlap`, first half. -/
theorem overlap_isCompatibleTolerance
    {T : Type u} {M : Type v} [Monoid T] [Monoid M]
    (rho : RelMorphism T M) :
    IsCompatibleTolerance (FiberOverlap rho) := by
  constructor
  · intro x
    obtain ⟨m, hm⟩ := rho.nonempty x
    exact ⟨m, hm, hm⟩
  constructor
  · intro x y hxy
    rcases hxy with ⟨m, hx, hy⟩
    exact ⟨m, hy, hx⟩
  · intro x y u v hxy huv
    rcases hxy with ⟨m, hx, hy⟩
    rcases huv with ⟨n, hu, hv⟩
    exact ⟨m * n, rho.mul_mem hx hu, rho.mul_mem hy hv⟩

/-- Safety of a compatible tolerance against a family of finite unsafe profiles. -/
def ToleranceSafeThrough
    {T : Type u}
    (UnsafeProfile : (d : Nat) → Tuple T d → Tuple T d → Prop)
    (tau : T → T → Prop) (f : Nat) : Prop :=
  ∀ d, 1 ≤ d → d ≤ f → ∀ s t : Tuple T d,
    UnsafeProfile d s t → ∃ i, ¬ tau (s i) (t i)

/--
Lemma `alg:lem:relational-overlap`, second half: relational separation and
safety of the overlap tolerance are the same coordinatewise condition.
-/
theorem separatesProfiles_iff_overlapSafe
    {T : Type u} {M : Type v} [Monoid T] [Monoid M]
    (UnsafeProfile : (d : Nat) → Tuple T d → Tuple T d → Prop)
    (rho : RelMorphism T M) (f : Nat) :
    rho.SeparatesProfilesThrough UnsafeProfile f ↔
      ToleranceSafeThrough UnsafeProfile (FiberOverlap rho) f := by
  constructor
  · intro hsep d hdpos hdf s t hunsafe
    obtain ⟨i, hi⟩ := hsep d hdpos hdf s t hunsafe
    exact ⟨i, (fiberSeparated_iff_not_overlap rho (s i) (t i)).mp hi⟩
  · intro hsafe d hdpos hdf s t hunsafe
    obtain ⟨i, hi⟩ := hsafe d hdpos hdf s t hunsafe
    exact ⟨i, (fiberSeparated_iff_not_overlap rho (s i) (t i)).mpr hi⟩

end SCLCompression
end LeanCfgProject
