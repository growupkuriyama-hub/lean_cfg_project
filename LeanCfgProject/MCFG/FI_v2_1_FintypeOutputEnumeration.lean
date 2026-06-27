import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import LeanCfgProject.MCFG.FI_v2_1_FiniteEnumerationSummary

/-!
# FI v2.1 Lean experiment: output-type enumeration from `Fintype`

This twenty-first layer turns the previous certificate-style output-type
enumeration into an actual noncomputable construction from `[Fintype M]`.

The paper assumes a fixed finite monoid.  The preceding layer isolated the
certificate needed by the refined-grammar construction: for each arity `d`, a
finite list containing every output-type vector `Fin d → M`.  This file builds
that certificate from Lean's `Fintype` machinery.

The construction is intentionally noncomputable.  For the learning theorem, the
important point is finite support and exhaustive coverage, not a particular
executable ordering of the output-type vectors.
-/

namespace FIv21

universe u v w

section FintypeOutputEnumeration

variable {M : Type v}

/-- The finite list of all output-type vectors of arity `d`, obtained from
Lean's `Fintype` enumeration. -/
noncomputable def fintypeOutputTypeList [Fintype M] (d : Nat) :
    List (Fin d → M) :=
  ((Fintype.elems : Finset (Fin d → M))).toList

/-- Every output-type vector occurs in the `Fintype`-generated list. -/
theorem mem_fintypeOutputTypeList [Fintype M]
    {d : Nat} (ty : Fin d → M) :
    ty ∈ fintypeOutputTypeList (M := M) d := by
  classical
  simp [fintypeOutputTypeList]

/-- The number of output-type vectors listed at arity `d`. -/
noncomputable def fintypeOutputTypeCount [Fintype M] (d : Nat) : Nat :=
  (fintypeOutputTypeList (M := M) d).length

end FintypeOutputEnumeration

section OutputTypeEnumerationOfFintype

variable {M : Type v} [Monoid M] [Fintype M]

namespace OutputTypeEnumeration

/-- A complete output-type enumeration produced from `[Fintype M]`.

This is the formal bridge from the paper's finite-monoid assumption to the
finite output-type certificates used by the refined grammar layers. -/
noncomputable def ofFintype (M : Type v) [Monoid M] [Fintype M] :
    OutputTypeEnumeration M :=
  { types := fun d => fintypeOutputTypeList (M := M) d
    complete := by
      intro d ty
      exact mem_fintypeOutputTypeList (M := M) ty }

/-- The `Fintype`-generated enumeration lists every output-type vector. -/
theorem ofFintype_complete {d : Nat} (ty : Fin d → M) :
    ty ∈ (OutputTypeEnumeration.ofFintype M).types d := by
  exact mem_fintypeOutputTypeList (M := M) ty

/-- The `Fintype`-generated enumeration supports every refined nonterminal. -/
theorem ofFintype_supports_refinedNonterminal
    {N : Type w} {α : Type u}
    {G : WorkingMCFG N α}
    (A : RefinedNonterminal G M) :
    (OutputTypeEnumeration.ofFintype M).SupportsRefinedNonterminal A := by
  exact OutputTypeEnumeration.supports_refinedNonterminal
    (OutputTypeEnumeration.ofFintype M) A

/-- The `Fintype`-generated enumeration supports every refined binary rule. -/
theorem ofFintype_supports_refinedBinaryRule
    {N : Type w} {α : Type u}
    {G : WorkingMCFG N α} {obs : α → M}
    (ρ : RefinedBinaryRule G obs) :
    (OutputTypeEnumeration.ofFintype M).SupportsRefinedBinaryRule ρ := by
  exact OutputTypeEnumeration.supports_refinedBinaryRule
    (OutputTypeEnumeration.ofFintype M) ρ

/-- The `Fintype`-generated enumeration supports every refined start rule. -/
theorem ofFintype_supports_refinedStartRule
    {N : Type w} {α : Type u}
    {G : WorkingMCFG N α} {obs : α → M}
    (ρ : RefinedStartRule G obs) :
    (OutputTypeEnumeration.ofFintype M).SupportsRefinedStartRule ρ := by
  exact OutputTypeEnumeration.supports_refinedStartRule
    (OutputTypeEnumeration.ofFintype M) ρ

end OutputTypeEnumeration

namespace GrammarOutputTypeEnumeration

/-- A grammar-level output-type enumeration produced from `[Fintype M]`. -/
noncomputable def ofFintype
    {N : Type w} {α : Type u}
    (G : WorkingMCFG N α) (obs : α → M) :
    GrammarOutputTypeEnumeration G obs :=
  { outputTypes := OutputTypeEnumeration.ofFintype M }

/-- Every actual refined nonterminal is supported by the grammar-level
`Fintype` enumeration. -/
theorem ofFintype_supports_actualRefinedNonterminal
    {N : Type w} {α : Type u}
    (G : WorkingMCFG N α) (obs : α → M)
    (A : N) (x : Tuple α (G.arity A)) :
    (GrammarOutputTypeEnumeration.ofFintype G obs).outputTypes.SupportsRefinedNonterminal
      (actualRefinedNonterminal G obs A x) := by
  exact (GrammarOutputTypeEnumeration.ofFintype G obs).supports_actualRefinedNonterminal A x

end GrammarOutputTypeEnumeration

end OutputTypeEnumerationOfFintype

end FIv21
