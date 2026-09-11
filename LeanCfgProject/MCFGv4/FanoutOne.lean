import LeanCfgProject.MCFGv4.TupleSubstitutability
import Mathlib.Tactic

/-!
# MCFGv4.FanoutOne

Paper-facing verification of Proposition `prop:fanout-one-specialization` in
the frozen 2026-09-07 manuscript.

At arity one there is a unique orientation and a sector context is exactly an
ordinary two-sided word context `(u,v)`.  This module makes that identification
explicit and proves that `(1,h)` tuple-substitutability is exactly the fixed-h
CFL distribution condition.
-/

namespace MCFGv4

universe u v

section

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- The one-component tuple associated with a word. -/
def singletonTuple (x : Word α) : Tuple α 1 :=
  fun _ => x

/-- The ordinary two-sided distribution `D_L(x)`. -/
def OrdinaryDistribution (L : Set (Word α)) (x : Word α) :
    Set (Word α × Word α) :=
  { p | p.1 ++ x ++ p.2 ∈ L }

/-- A two-sided context `(u,v)` viewed as the unique arity-one oriented sector
context. -/
def unarySectorContext (u v : Word α) :
    SectorContext α 1 (idOrientation 1) where
  spacers := fun i =>
    if i.val = 0 then u else v

/-- Every arity-one identity-sector context is uniquely determined by its two
spacers. -/
theorem unarySectorContext_reconstruct
    (E : SectorContext α 1 (idOrientation 1)) :
    unarySectorContext (E.spacers 0) (E.spacers 1) = E := by
  cases E with
  | mk spacers =>
      unfold unarySectorContext
      congr
      funext i
      fin_cases i <;> simp

/-- Filling the arity-one sector context is ordinary two-sided concatenation. -/
theorem sectorFill_unarySectorContext (u v x : Word α) :
    sectorFill (unarySectorContext u v) (singletonTuple x) = u ++ x ++ v := by
  simp [sectorFill, unarySectorContext, singletonTuple, idOrientation]

/-- Membership in the arity-one sector distribution is exactly ordinary
context membership. -/
theorem unarySector_mem_iff
    (L : Set (Word α)) (x u v : Word α) :
    unarySectorContext u v ∈
        SectorDistribution (σ := idOrientation 1) L (singletonTuple x) ↔
      (u, v) ∈ OrdinaryDistribution L x := by
  change sectorFill (unarySectorContext u v) (singletonTuple x) ∈ L ↔
    u ++ x ++ v ∈ L
  rw [sectorFill_unarySectorContext]

/-- Equality of the unique arity-one sector distributions is exactly equality
of ordinary two-sided distributions. -/
theorem unarySectorDistribution_eq_iff
    (L : Set (Word α)) (x y : Word α) :
    SectorDistribution (σ := idOrientation 1) L (singletonTuple x) =
        SectorDistribution (σ := idOrientation 1) L (singletonTuple y) ↔
      OrdinaryDistribution L x = OrdinaryDistribution L y := by
  constructor
  · intro h
    ext p
    rcases p with ⟨u, v⟩
    rw [← unarySector_mem_iff L x u v, ← unarySector_mem_iff L y u v, h]
  · intro h
    ext E
    have hE := unarySectorContext_reconstruct E
    rw [← hE]
    rw [unarySector_mem_iff L x, unarySector_mem_iff L y, h]

/-- Sharing an accepting arity-one sector context is exactly nonempty
intersection of ordinary two-sided distributions. -/
theorem unarySharesSectorContext_iff
    (L : Set (Word α)) (x y : Word α) :
    SharesSectorContext (σ := idOrientation 1) L
        (singletonTuple x) (singletonTuple y) ↔
      (OrdinaryDistribution L x ∩ OrdinaryDistribution L y).Nonempty := by
  constructor
  · rintro ⟨E, hx, hy⟩
    refine ⟨(E.spacers 0, E.spacers 1), ?_⟩
    constructor
    · rw [← unarySector_mem_iff L x]
      rw [unarySectorContext_reconstruct E]
      exact hx
    · rw [← unarySector_mem_iff L y]
      rw [unarySectorContext_reconstruct E]
      exact hy
  · rintro ⟨⟨u, v⟩, hx, hy⟩
    refine ⟨unarySectorContext u v, ?_, ?_⟩
    · rw [sectorFill_unarySectorContext]
      exact hx
    · rw [sectorFill_unarySectorContext]
      exact hy

/-- The ordinary fixed-observation substitutability condition displayed in
Proposition `prop:fanout-one-specialization`. -/
def OrdinarySubstitutable (obs : α → M) (L : Set (Word α)) : Prop :=
  ∀ x y : Word α,
    evalObs obs x = evalObs obs y →
    (OrdinaryDistribution L x ∩ OrdinaryDistribution L y).Nonempty →
    OrdinaryDistribution L x = OrdinaryDistribution L y

/-- Every unary tuple is the singleton tuple of its unique component. -/
theorem unaryTuple_eq_singleton (x : Tuple α 1) :
    x = singletonTuple (x 0) := by
  funext i
  fin_cases i
  rfl

/-- Proposition `prop:fanout-one-specialization` from the frozen manuscript. -/
theorem fanoutOne_specialization
    (obs : α → M) (L : Set (Word α)) :
    TupleSubstitutable 1 obs L ↔ OrdinarySubstitutable obs L := by
  rw [identitySector_equiv_tupleSubstitutable]
  constructor
  · intro hId x y htype hoverlap
    have htupleType :
        tupleType obs (singletonTuple x) = tupleType obs (singletonTuple y) := by
      funext i
      fin_cases i
      exact htype
    have hshare :
        SharesSectorContext (σ := idOrientation 1) L
          (singletonTuple x) (singletonTuple y) :=
      (unarySharesSectorContext_iff L x y).2 hoverlap
    have hdist := hId (d := 1) (by omega) (by omega)
      (singletonTuple x) (singletonTuple y) htupleType hshare
    exact (unarySectorDistribution_eq_iff L x y).1 hdist
  · intro hOrd d hpos hd1 x y htype hshare
    have hd : d = 1 := by omega
    subst d
    have hwordType : evalObs obs (x 0) = evalObs obs (y 0) := by
      exact congrFun htype 0
    have hx : x = singletonTuple (x 0) := unaryTuple_eq_singleton x
    have hy : y = singletonTuple (y 0) := unaryTuple_eq_singleton y
    rw [hx, hy] at hshare
    have hoverlap :
        (OrdinaryDistribution L (x 0) ∩ OrdinaryDistribution L (y 0)).Nonempty :=
      (unarySharesSectorContext_iff L (x 0) (y 0)).1 hshare
    have hord := hOrd (x 0) (y 0) hwordType hoverlap
    have hsector := (unarySectorDistribution_eq_iff L (x 0) (y 0)).2 hord
    rw [hx, hy]
    exact hsector

end

end MCFGv4
