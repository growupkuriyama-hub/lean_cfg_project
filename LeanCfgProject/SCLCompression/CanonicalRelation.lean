import LeanCfgProject.SCLCompression.Selector

namespace LeanCfgProject
namespace SCLCompression

universe u v w

/--
The canonical relation `rho_h(t) = { h(w) | eta(w) = t }` from the manuscript,
packaged as a relational morphism.  Surjectivity of `eta` supplies nonempty
fibres.
-/
def canonicalRel
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (eta : Word Sigma →* T) (heta : Function.Surjective eta)
    (h : Word Sigma →* M) : RelMorphism T M where
  fiber := CanonicalFiber eta h
  nonempty := by
    intro t
    obtain ⟨word, hword⟩ := heta t
    exact ⟨h word, word, hword, rfl⟩
  one_mem := by
    refine ⟨(1 : Word Sigma), ?_, ?_⟩
    · exact eta.map_one
    · exact h.map_one
  mul_mem := by
    intro s t m n hm hn
    rcases hm with ⟨uword, hueta, huh⟩
    rcases hn with ⟨vword, hveta, hvh⟩
    refine ⟨uword * vword, ?_, ?_⟩
    · simpa [hueta, hveta] using eta.map_mul uword vword
    · simpa [huh, hvh] using h.map_mul uword vword

@[simp] theorem mem_canonicalRel_fiber_iff
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (eta : Word Sigma →* T) (heta : Function.Surjective eta)
    (h : Word Sigma →* M) (t : T) (m : M) :
    m ∈ (canonicalRel eta heta h).fiber t ↔
      ∃ word : Word Sigma, eta word = t ∧ h word = m := by
  rfl

/-- The graph-membership form of the canonical relation. -/
theorem mem_canonicalRel_fiber
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (eta : Word Sigma →* T) (heta : Function.Surjective eta)
    (h : Word Sigma →* M) (word : Word Sigma) :
    h word ∈ (canonicalRel eta heta h).fiber (eta word) := by
  exact ⟨word, rfl, rfl⟩

end SCLCompression
end LeanCfgProject
