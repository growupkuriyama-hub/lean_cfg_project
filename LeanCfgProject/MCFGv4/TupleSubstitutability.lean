import LeanCfgProject.MCFGv4.OrientedContexts
import LeanCfgProject.MCFGv4.SemanticKernel

/-!
# MCFGv4.TupleSubstitutability

Paper-facing semantic core for Definition `def:tuple-substitutable` and the
first consequences in the frozen 2026-09-07 manuscript.

This module uses the concrete orientation sectors from `OrientedContexts` and
keeps the fixed observation at the letter level; `evalObs` is the induced word
homomorphism.
-/

namespace MCFGv4

universe u v w

section SectorSemantics

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Two tuples share one accepting context in the same orientation sector. -/
def SharesSectorContext {d : Nat} {σ : Equiv.Perm (Fin d)}
    (L : Set (Word α)) (x y : Tuple α d) : Prop :=
  ∃ E : SectorContext α d σ, sectorFill E x ∈ L ∧ sectorFill E y ∈ L

/-- Definition `def:tuple-substitutable` from the frozen manuscript. -/
def TupleSubstitutable (f : Nat) (obs : α → M) (L : Set (Word α)) : Prop :=
  ∀ {d : Nat}, 0 < d → d ≤ f →
    ∀ (σ : Equiv.Perm (Fin d)) (x y : Tuple α d),
      tupleType obs x = tupleType obs y →
      SharesSectorContext (σ := σ) L x y →
      SectorDistribution (σ := σ) L x = SectorDistribution (σ := σ) L y

/-- The identity-sector-only formulation appearing in
Corollary `cor:identity-sector-equivalence`. -/
def IdentitySectorSubstitutable (f : Nat) (obs : α → M)
    (L : Set (Word α)) : Prop :=
  ∀ {d : Nat}, 0 < d → d ≤ f →
    ∀ x y : Tuple α d,
      tupleType obs x = tupleType obs y →
      SharesSectorContext (σ := idOrientation d) L x y →
      SectorDistribution (σ := idOrientation d) L x =
        SectorDistribution (σ := idOrientation d) L y

/-- Observation-distribution equivalence `≡^d_{L,h,σ}` from the manuscript. -/
def ObsDistributionEquivalent {d : Nat} (obs : α → M)
    (L : Set (Word α)) (σ : Equiv.Perm (Fin d))
    (x y : Tuple α d) : Prop :=
  tupleType obs x = tupleType obs y ∧
    SectorDistribution (σ := σ) L x = SectorDistribution (σ := σ) L y

/-- Membership transport underlying sector canonicalization. -/
theorem canonicalize_mem_distribution_iff {d : Nat}
    (σ : Equiv.Perm (Fin d)) (L : Set (Word α))
    (x : Tuple α d) (E : SectorContext α d σ) :
    canonicalizeContext σ E ∈
        SectorDistribution (σ := idOrientation d) L (permuteTuple σ x) ↔
      E ∈ SectorDistribution (σ := σ) L x := by
  change sectorFill (canonicalizeContext σ E) (permuteTuple σ x) ∈ L ↔
    sectorFill E x ∈ L
  rw [canonicalize_fill]

/-- Applying one permutation to both tuples preserves componentwise observation
value equality. -/
theorem tupleType_permute_eq {d : Nat}
    (obs : α → M) (σ : Equiv.Perm (Fin d)) (x y : Tuple α d)
    (hxy : tupleType obs x = tupleType obs y) :
    tupleType obs (permuteTuple σ x) = tupleType obs (permuteTuple σ y) := by
  funext i
  exact congrFun hxy (σ i)

/-- One implication of Corollary `cor:identity-sector-equivalence`. -/
theorem identitySectorSubstitutable_of_tupleSubstitutable
    {f : Nat} {obs : α → M} {L : Set (Word α)}
    (hL : TupleSubstitutable f obs L) :
    IdentitySectorSubstitutable f obs L := by
  intro d hpos hdf x y htype hshare
  exact hL hpos hdf (idOrientation d) x y htype hshare

/-- Converse implication of Corollary `cor:identity-sector-equivalence`.
Every orientation sector is transported to the identity sector by the same
canonical bijection used in Lemma `lem:sector-canonicalization`. -/
theorem tupleSubstitutable_of_identitySectorSubstitutable
    {f : Nat} {obs : α → M} {L : Set (Word α)}
    (hId : IdentitySectorSubstitutable f obs L) :
    TupleSubstitutable f obs L := by
  intro d hpos hdf σ x y htype hshare
  have htype' :
      tupleType obs (permuteTuple σ x) = tupleType obs (permuteTuple σ y) :=
    tupleType_permute_eq obs σ x y htype
  obtain ⟨E, hx, hy⟩ := hshare
  have hshare' : SharesSectorContext (σ := idOrientation d) L
      (permuteTuple σ x) (permuteTuple σ y) := by
    refine ⟨canonicalizeContext σ E, ?_, ?_⟩
    · rw [canonicalize_fill]
      exact hx
    · rw [canonicalize_fill]
      exact hy
  have hdist' := hId hpos hdf (permuteTuple σ x) (permuteTuple σ y) htype' hshare'
  ext D
  have hxI := canonicalize_mem_distribution_iff σ L x D
  have hyI := canonicalize_mem_distribution_iff σ L y D
  rw [← hxI, ← hyI]
  exact Set.ext_iff.mp hdist' (canonicalizeContext σ D)

/-- Corollary `cor:identity-sector-equivalence` in biconditional form. -/
theorem identitySector_equiv_tupleSubstitutable
    {f : Nat} {obs : α → M} {L : Set (Word α)} :
    TupleSubstitutable f obs L ↔ IdentitySectorSubstitutable f obs L := by
  constructor
  · exact identitySectorSubstitutable_of_tupleSubstitutable
  · exact tupleSubstitutable_of_identitySectorSubstitutable

/-- Lemma `lem:shared-context`: a concrete common accepting context plus equal
observation type yields full observation-distribution equivalence. -/
theorem sharedContext_substitutability
    {f d : Nat} {obs : α → M} {L : Set (Word α)}
    (hL : TupleSubstitutable f obs L)
    (hpos : 0 < d) (hdf : d ≤ f)
    (σ : Equiv.Perm (Fin d)) (x y : Tuple α d)
    (htype : tupleType obs x = tupleType obs y)
    (E : SectorContext α d σ)
    (hx : sectorFill E x ∈ L) (hy : sectorFill E y ∈ L) :
    ObsDistributionEquivalent obs L σ x y := by
  refine ⟨htype, ?_⟩
  exact hL hpos hdf σ x y htype ⟨E, hx, hy⟩

end SectorSemantics

section ObservationRefinement

variable {α : Type u}
variable {M : Type v} {M' : Type w}
variable [Monoid M] [Monoid M']
variable {obs : α → M} {obs' : α → M'}

/-- Semantic content of Proposition `prop:h-refinement-monotonicity`:
substitutability is monotone under refinement of the finite observation. -/
theorem tupleSubstitutable_of_refines
    {f : Nat} {L : Set (Word α)}
    (r : Refines obs obs')
    (hL : TupleSubstitutable f obs L) :
    TupleSubstitutable f obs' L := by
  intro d hpos hdf σ x y htype hshare
  have hcoarse : tupleType obs x = tupleType obs y := by
    funext i
    calc
      tupleType obs x i = r.map (tupleType obs' x i) :=
        (tupleType_refines_apply r x i).symm
      _ = r.map (tupleType obs' y i) := by
        exact congrArg r.map (congrFun htype i)
      _ = tupleType obs y i := tupleType_refines_apply r y i
  exact hL hpos hdf σ x y hcoarse hshare

end ObservationRefinement

end MCFGv4
