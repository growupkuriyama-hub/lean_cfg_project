import LeanCfgProject.ObservedResidualConcept.StateSemantics
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

open TwoSidedTypedCFG

universe u v w

def TwoSidedResidual
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (alpha beta : Q) : Set Q :=
  { gamma | alpha * gamma * beta ∈ S }

def CommonContexts
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (U : Set Q) : Set (Q × Q) :=
  { ab | ∀ gamma : Q, gamma ∈ U → ab.1 * gamma * ab.2 ∈ S }

def ElementsOfContexts
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (K : Set (Q × Q)) : Set Q :=
  { gamma | ∀ ab : Q × Q, ab ∈ K → ab.1 * gamma * ab.2 ∈ S }

def ConceptClosure
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (U : Set Q) : Set Q :=
  ElementsOfContexts S (CommonContexts S U)

theorem residual_galois_connection
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (U : Set Q)
    (K : Set (Q × Q)) :
    K ⊆ CommonContexts S U ↔ U ⊆ ElementsOfContexts S K := by
  constructor
  · intro hK gamma hgamma ab hab
    exact hK hab gamma hgamma
  · intro hU ab hab gamma hgamma
    exact hU hgamma ab hab

theorem subset_conceptClosure
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (U : Set Q) :
    U ⊆ ConceptClosure S U := by
  intro gamma hgamma ab hab
  exact hab gamma hgamma

theorem state_semantics_subset_residual
    {Sigma : Type u} {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (L Y : Set (Word Sigma))
    (ell r : Word Sigma)
    (hctx : ∀ w : Word Sigma, w ∈ Y → ell ++ w ++ r ∈ L) :
    ImageOfLanguage q Y ⊆
      TwoSidedResidual (ImageOfLanguage q L) (q ell) (q r) := by
  intro gamma hgamma
  rcases hgamma with ⟨w, hwY, hgamma_eq⟩
  refine ⟨ell ++ w ++ r, hctx w hwY, ?_⟩
  rw [hgamma_eq]
  rw [← q_mul ell w]
  rw [← q_mul (ell ++ w) r]

theorem commonContexts_antitone
    {Q : Type u} [Mul Q]
    (S : Set Q)
    {U V : Set Q}
    (hUV : U ⊆ V) :
    CommonContexts S V ⊆ CommonContexts S U := by
  intro ab hab gamma hgamma
  exact hab gamma (hUV hgamma)

theorem elementsOfContexts_antitone
    {Q : Type u} [Mul Q]
    (S : Set Q)
    {K L : Set (Q × Q)}
    (hKL : K ⊆ L) :
    ElementsOfContexts S L ⊆ ElementsOfContexts S K := by
  intro gamma hgamma ab hab
  exact hgamma ab (hKL hab)

theorem conceptClosure_mono
    {Q : Type u} [Mul Q]
    (S : Set Q)
    {U V : Set Q}
    (hUV : U ⊆ V) :
    ConceptClosure S U ⊆ ConceptClosure S V := by
  intro gamma hgamma ab hab
  apply hgamma
  intro delta hdelta
  exact hab delta (hUV hdelta)

theorem binary_sound_after_closure
    {Sigma : Type u} {Q : Type v} {State : Type w}
    [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (Yield : State → Set (Word Sigma))
    (X Y Z : State)
    (hbin : ∀ u v : Word Sigma,
      u ∈ Yield Y →
      v ∈ Yield Z →
      u ++ v ∈ Yield X) :
    ConceptClosure S
      (SetMul (StateSemantics q Yield Y)
              (StateSemantics q Yield Z))
      ⊆
    ConceptClosure S (StateSemantics q Yield X) := by
  exact conceptClosure_mono S (binary_sound q q_mul Yield X Y Z hbin)

theorem commonContexts_conceptClosure
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (U : Set Q) :
    CommonContexts S U ⊆ CommonContexts S (ConceptClosure S U) := by
  intro ab hab gamma hgamma
  exact hgamma ab hab

theorem conceptClosure_idempotent
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (U : Set Q) :
    ConceptClosure S (ConceptClosure S U) = ConceptClosure S U := by
  apply Set.Subset.antisymm
  · intro gamma hgamma ab hab
    exact hgamma ab (commonContexts_conceptClosure S U hab)
  · exact subset_conceptClosure S (ConceptClosure S U)

def IsConceptExtent
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (U : Set Q) : Prop :=
  ConceptClosure S U = U

theorem conceptClosure_isConceptExtent
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (U : Set Q) :
    IsConceptExtent S (ConceptClosure S U) := by
  unfold IsConceptExtent
  exact conceptClosure_idempotent S U

def ConceptProduct
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (A B : Set Q) : Set Q :=
  ConceptClosure S (SetMul A B)

theorem conceptProduct_isConceptExtent
    {Q : Type u} [Mul Q]
    (S : Set Q)
    (A B : Set Q) :
    IsConceptExtent S (ConceptProduct S A B) := by
  unfold ConceptProduct
  exact conceptClosure_isConceptExtent S (SetMul A B)

theorem binary_sound_as_conceptProduct
    {Sigma : Type u} {Q : Type v} {State : Type w}
    [Monoid Q]
    (S : Set Q)
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (Yield : State → Set (Word Sigma))
    (X Y Z : State)
    (hbin : ∀ u v : Word Sigma,
      u ∈ Yield Y →
      v ∈ Yield Z →
      u ++ v ∈ Yield X) :
    ConceptProduct S
      (StateSemantics q Yield Y)
      (StateSemantics q Yield Z)
      ⊆
    ConceptClosure S (StateSemantics q Yield X) := by
  exact binary_sound_after_closure S q q_mul Yield X Y Z hbin

end LeanCfgProject
