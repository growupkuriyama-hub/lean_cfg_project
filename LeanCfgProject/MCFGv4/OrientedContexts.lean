import LeanCfgProject.MCFGv4.Basic
import Mathlib.Data.Set.Basic
import Mathlib.GroupTheory.Perm.Basic

/-!
# MCFGv4.OrientedContexts

Concrete model of the orientation sectors `E_{d,σ}` from the frozen v4
manuscript.

For a fixed permutation `σ`, a sentence context

`u₀ □_{σ(1)} u₁ ... □_{σ(d)} u_d`

is represented by its `d+1` terminal spacers.  Keeping the orientation as a
parameter of the type makes the sector separation explicit and makes the
canonical hole-renaming map `C_σ` a literal equivalence obtained by preserving
those spacers.
-/

namespace MCFGv4

universe u

/-- The identity orientation at arity `d`. -/
abbrev idOrientation (d : Nat) : Equiv.Perm (Fin d) := Equiv.refl (Fin d)

/-- A sentence context in one fixed orientation sector.

`spacers 0, ..., spacers d` are the terminal words around the `d` named holes. -/
structure SectorContext (α : Type u) (d : Nat) (σ : Equiv.Perm (Fin d)) where
  spacers : Fin (d + 1) → Word α

/-- Permute tuple components into left-to-right order for sector `σ`.
This is the manuscript map `P_σ`. -/
def permuteTuple {α : Type u} {d : Nat} (σ : Equiv.Perm (Fin d))
    (x : Tuple α d) : Tuple α d :=
  fun i => x (σ i)

/-- Fill a fixed-sector sentence context with a tuple. -/
def sectorFill {α : Type u} {d : Nat} {σ : Equiv.Perm (Fin d)}
    (E : SectorContext α d σ) (x : Tuple α d) : Word α :=
  ((List.ofFn fun i : Fin d =>
      E.spacers i.castSucc ++ x (σ i)).join) ++
    E.spacers (Fin.last d)

/-- Rename holes according to their left-to-right order.  This is the
manuscript map `C_σ : E_{d,σ} → E_{d,id}`. -/
def canonicalizeContext {α : Type u} {d : Nat} (σ : Equiv.Perm (Fin d)) :
    SectorContext α d σ → SectorContext α d (idOrientation d) :=
  fun E => ⟨E.spacers⟩

/-- Inverse hole renaming from the identity sector back to sector `σ`. -/
def uncanonicalizeContext {α : Type u} {d : Nat} (σ : Equiv.Perm (Fin d)) :
    SectorContext α d (idOrientation d) → SectorContext α d σ :=
  fun E => ⟨E.spacers⟩

/-- `C_σ` is a bijection between orientation sectors. -/
def canonicalizeEquiv {α : Type u} {d : Nat} (σ : Equiv.Perm (Fin d)) :
    SectorContext α d σ ≃ SectorContext α d (idOrientation d) where
  toFun := canonicalizeContext σ
  invFun := uncanonicalizeContext σ
  left_inv := by
    intro E
    cases E
    rfl
  right_inv := by
    intro E
    cases E
    rfl

/-- Filling after canonicalization and tuple permutation gives exactly the same
word.  This is the central filling identity in
`lem:sector-canonicalization`. -/
theorem canonicalize_fill {α : Type u} {d : Nat}
    (σ : Equiv.Perm (Fin d)) (E : SectorContext α d σ) (x : Tuple α d) :
    sectorFill (canonicalizeContext σ E) (permuteTuple σ x) = sectorFill E x := by
  simp [sectorFill, canonicalizeContext, permuteTuple, idOrientation]

/-- Orientation-sector distribution from the manuscript. -/
def SectorDistribution {α : Type u} {d : Nat} {σ : Equiv.Perm (Fin d)}
    (L : Set (Word α)) (x : Tuple α d) : Set (SectorContext α d σ) :=
  { E | sectorFill E x ∈ L }

/-- Canonicalization transports the whole accepting distribution to the
identity sector.  Together with `canonicalizeEquiv` and `canonicalize_fill`,
this is the complete mathematical content of manuscript
Lemma `lem:sector-canonicalization`. -/
theorem canonicalize_distribution {α : Type u} {d : Nat}
    (σ : Equiv.Perm (Fin d)) (L : Set (Word α)) (x : Tuple α d) :
    canonicalizeContext σ '' SectorDistribution (σ := σ) L x =
      SectorDistribution (σ := idOrientation d) L (permuteTuple σ x) := by
  ext E
  constructor
  · rintro ⟨D, hD, rfl⟩
    change sectorFill D x ∈ L at hD
    change sectorFill (canonicalizeContext σ D) (permuteTuple σ x) ∈ L
    rw [canonicalize_fill]
    exact hD
  · intro hE
    let D : SectorContext α d σ := uncanonicalizeContext σ E
    refine ⟨D, ?_, ?_⟩
    · change sectorFill D x ∈ L
      have hfill := canonicalize_fill σ D x
      rw [← hfill]
      simpa [D, canonicalizeContext, uncanonicalizeContext] using hE
    · cases E
      rfl

end MCFGv4
