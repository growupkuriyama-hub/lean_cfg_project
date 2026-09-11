import LeanCfgProject.SCLCompression.TupleContexts
import LeanCfgProject.SCLCompression.RelationalMorphisms

namespace LeanCfgProject
namespace SCLCompression

universe u v w

/-- The homomorphism from the free monoid of words selected by generator values. -/
def selectorHom {Sigma : Type u} {M : Type v} [Monoid M]
    (g : Sigma → M) : Word Sigma →* M where
  toFun word := (word.map g).prod
  map_one' := by simp [Word]
  map_mul' x y := by simp [Word]

@[simp] theorem selectorHom_letter {Sigma : Type u} {M : Type v} [Monoid M]
    (g : Sigma → M) (a : Sigma) : selectorHom g [a] = g a := by
  simp [selectorHom]

/--
Free-monoid selector lemma from the manuscript: choosing one value in the
relational fibre of each generator extends to a homomorphism whose value on
every word remains in the corresponding fibre.
-/
theorem selector_mem_fiber
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (eta : Word Sigma →* T) (rho : RelMorphism T M)
    (g : Sigma → M)
    (hg : ∀ a : Sigma, g a ∈ rho.fiber (eta [a])) :
    ∀ word : Word Sigma, selectorHom g word ∈ rho.fiber (eta word) := by
  intro word
  induction word with
  | nil =>
      simpa [selectorHom] using rho.one_mem
  | cons a tail ih =>
      have hmul := rho.mul_mem (hg a) ih
      simpa [selectorHom] using hmul

/-- Canonical fibre induced jointly by a syntactic map `eta` and observer `h`. -/
def CanonicalFiber
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (eta : Word Sigma →* T) (h : Word Sigma →* M) (t : T) : Set M :=
  {m | ∃ word : Word Sigma, eta word = t ∧ h word = m}

/--
The key fibre inclusion in the selector lemma:
`rho_{h_rho}(t) ⊆ rho(t)`.
-/
theorem canonicalFiber_selector_subset
    {Sigma : Type u} {T : Type v} {M : Type w}
    [Monoid T] [Monoid M]
    (eta : Word Sigma →* T) (rho : RelMorphism T M)
    (g : Sigma → M)
    (hg : ∀ a : Sigma, g a ∈ rho.fiber (eta [a]))
    (t : T) :
    CanonicalFiber eta (selectorHom g) t ⊆ rho.fiber t := by
  intro m hm
  rcases hm with ⟨word, heta, rfl⟩
  simpa [heta] using selector_mem_fiber eta rho g hg word

end SCLCompression
end LeanCfgProject
