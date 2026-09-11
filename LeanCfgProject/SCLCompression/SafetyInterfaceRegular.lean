import LeanCfgProject.SCLCompression.FiniteProfiles
import LeanCfgProject.SCLCompression.CanonicalRelation

namespace LeanCfgProject
namespace SCLCompression

universe u v w

/-- Failure of relational fibre separation is exactly nonempty fibre overlap. -/
theorem not_fiberSeparated_iff_inter_nonempty
    {T : Type v} {M : Type w} [Monoid T] [Monoid M]
    (rho : RelMorphism T M) (s t : T) :
    ¬ RelMorphism.FiberSeparated rho s t ↔
      (rho.fiber s ∩ rho.fiber t).Nonempty := by
  classical
  constructor
  · intro hnsep
    by_contra hno
    apply hnsep
    intro m hms hmt
    apply hno
    exact ⟨m, hms, hmt⟩
  · rintro ⟨m, hms, hmt⟩ hsep
    exact hsep m hms hmt

/--
Regular-language part of the Safety Interface Theorem, conditions (iii) and
(v): semantic unsafe-pair separation by `h` is equivalent to finite syntactic
unsafe-profile separation by the canonical relation `rho_h`.
-/
theorem semanticSeparation_iff_canonicalRelSeparation
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (L : Language Sigma) (eta : Word Sigma →* T)
    (heta : Function.Surjective eta) (P : Set T)
    (hL : ∀ word : Word Sigma, word ∈ L ↔ eta word ∈ P)
    (h : Word Sigma →* M) (f : Nat) :
    SemanticSeparationThrough L h f ↔
      RelMorphism.SeparatesProfilesThrough (SyntacticUnsafe P)
        (canonicalRel eta heta h) f := by
  classical
  constructor
  · intro hsem d hdpos hdf s t hunsafe
    by_contra hnotSeparated
    have hnsep : ∀ i : Fin d,
        ¬ RelMorphism.FiberSeparated (canonicalRel eta heta h) (s i) (t i) := by
      intro i hi
      exact hnotSeparated ⟨i, hi⟩
    have hoverlap : ∀ i : Fin d,
        ((canonicalRel eta heta h).fiber (s i) ∩
          (canonicalRel eta heta h).fiber (t i)).Nonempty := by
      intro i
      exact (not_fiberSeparated_iff_inter_nonempty
        (canonicalRel eta heta h) (s i) (t i)).mp (hnsep i)
    let m : Fin d → M := fun i => Classical.choose (hoverlap i)
    have hmS : ∀ i : Fin d, m i ∈ (canonicalRel eta heta h).fiber (s i) := by
      intro i
      exact (Classical.choose_spec (hoverlap i)).1
    have hmT : ∀ i : Fin d, m i ∈ (canonicalRel eta heta h).fiber (t i) := by
      intro i
      exact (Classical.choose_spec (hoverlap i)).2
    have hxWitness : ∀ i : Fin d,
        ∃ word : Word Sigma, eta word = s i ∧ h word = m i := by
      intro i
      exact (mem_canonicalRel_fiber_iff eta heta h (s i) (m i)).mp (hmS i)
    have hyWitness : ∀ i : Fin d,
        ∃ word : Word Sigma, eta word = t i ∧ h word = m i := by
      intro i
      exact (mem_canonicalRel_fiber_iff eta heta h (t i) (m i)).mp (hmT i)
    let x : Tuple (Word Sigma) d := fun i => Classical.choose (hxWitness i)
    let y : Tuple (Word Sigma) d := fun i => Classical.choose (hyWitness i)
    have hxeta : tupleImage eta x = s := by
      funext i
      exact (Classical.choose_spec (hxWitness i)).1
    have hyeta : tupleImage eta y = t := by
      funext i
      exact (Classical.choose_spec (hyWitness i)).1
    have hxh : ∀ i : Fin d, h (x i) = m i := by
      intro i
      exact (Classical.choose_spec (hxWitness i)).2
    have hyh : ∀ i : Fin d, h (y i) = m i := by
      intro i
      exact (Classical.choose_spec (hyWitness i)).2
    have hsyntactic :
        SyntacticUnsafe P d (tupleImage eta x) (tupleImage eta y) := by
      rw [hxeta, hyeta]
      exact hunsafe
    have hsemantic : SemanticUnsafe L d x y :=
      (semanticUnsafe_iff_syntacticUnsafe L eta P hL heta d x y).mpr hsyntactic
    obtain ⟨i, hne⟩ := hsem d hdpos hdf x y hsemantic
    apply hne
    rw [hxh i, hyh i]
  · intro hrel d hdpos hdf x y hunsafe
    have hsyntactic :
        SyntacticUnsafe P d (tupleImage eta x) (tupleImage eta y) :=
      (semanticUnsafe_iff_syntacticUnsafe L eta P hL heta d x y).mp hunsafe
    obtain ⟨i, hsep⟩ := hrel d hdpos hdf
      (tupleImage eta x) (tupleImage eta y) hsyntactic
    refine ⟨i, ?_⟩
    intro heq
    have hmx :
        h (x i) ∈ (canonicalRel eta heta h).fiber ((tupleImage eta x) i) := by
      exact mem_canonicalRel_fiber eta heta h (x i)
    have hmy :
        h (y i) ∈ (canonicalRel eta heta h).fiber ((tupleImage eta y) i) := by
      exact mem_canonicalRel_fiber eta heta h (y i)
    apply hsep (h (x i)) hmx
    rw [heq]
    exact hmy

/-- Conditions (ii)--(v) of the regular-language Safety Interface coincide. -/
theorem wordContextSafe_iff_canonicalRelSeparation
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (L : Language Sigma) (eta : Word Sigma →* T)
    (heta : Function.Surjective eta) (P : Set T)
    (hL : ∀ word : Word Sigma, word ∈ L ↔ eta word ∈ P)
    (h : Word Sigma →* M) (f : Nat) :
    WordContextSafeThrough L h f ↔
      RelMorphism.SeparatesProfilesThrough (SyntacticUnsafe P)
        (canonicalRel eta heta h) f := by
  rw [wordContextSafe_iff_semanticSeparation]
  exact semanticSeparation_iff_canonicalRelSeparation L eta heta P hL h f

end SCLCompression
end LeanCfgProject
