import LeanCfgProject.FixedHCFG.V60TrimmedRefinement
import LeanCfgProject.FixedHCFG.V60Reconstruction

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Concrete extraction of the v60 reconstruction basis from the trimmed yield-only
refinement.  The choices in this file are proof-facing witnesses; the next
canonical layer will refine them to the manuscript's shortlex `omega` and
minimum-total-length `chi` choices.
-/

/-- Choose one terminal yield of each retained yield-typed state. -/
noncomputable def v60ChosenOmega
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) : Word Sigma :=
  Classical.choose X.property.1

/-- The chosen yield is genuinely derivable. -/
theorem v60ChosenOmega_spec
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) :
    V60YieldTypedDerives Obs terminal binary X.1 (v60ChosenOmega X) := by
  exact Classical.choose_spec X.property.1

/-- Every chosen non-start yield is nonempty. -/
theorem v60ChosenOmega_nonempty
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) :
    v60ChosenOmega X ≠ [] := by
  exact v60_yield_typed_derivation_nonempty Obs terminal binary
    (v60ChosenOmega_spec X)

/--
Choose a successful terminal context, normalized so a direct start state uses
`([],[])`.
-/
theorem v60_exists_preferred_context
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) :
    ∃ u v : Word Sigma,
      V60TypedOccurs Obs terminal binary start X.1 u v ∧
        (V60KeptStart X → u = [] ∧ v = []) := by
  classical
  by_cases hStart : V60KeptStart X
  · exact ⟨[], [],
      v60_kept_start_occurs_empty Obs terminal binary start X hStart,
      fun _ => ⟨rfl, rfl⟩⟩
  · rcases X.property.2 with ⟨u, v, hOcc⟩
    exact ⟨u, v, hOcc, fun hs => (hStart hs).elim⟩

noncomputable def v60ChosenLeftCtx
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) : Word Sigma :=
  Classical.choose (v60_exists_preferred_context X)

noncomputable def v60ChosenRightCtx
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) : Word Sigma :=
  Classical.choose (Classical.choose_spec (v60_exists_preferred_context X))

/-- Specification of the chosen successful context. -/
theorem v60ChosenContext_spec
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) :
    V60TypedOccurs Obs terminal binary start X.1
      (v60ChosenLeftCtx X) (v60ChosenRightCtx X) ∧
    (V60KeptStart X → v60ChosenLeftCtx X = [] ∧ v60ChosenRightCtx X = []) := by
  exact Classical.choose_spec
    (Classical.choose_spec (v60_exists_preferred_context X))

/-- Anchor witness `u_X omega(X) v_X`. -/
noncomputable def v60AnchorWord
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) : Word Sigma :=
  v60ChosenLeftCtx X ++ v60ChosenOmega X ++ v60ChosenRightCtx X

/-- Terminal-rule witness `u_X a v_X`. -/
noncomputable def v60TerminalWitnessWord
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) (a : Sigma) : Word Sigma :=
  v60ChosenLeftCtx X ++ [a] ++ v60ChosenRightCtx X

/-- Binary-rule witness `u_X omega(Y) omega(Z) v_X`. -/
noncomputable def v60BinaryWitnessWord
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X Y Z : V60KeptState Obs terminal binary start) : Word Sigma :=
  v60ChosenLeftCtx X ++ v60ChosenOmega Y ++ v60ChosenOmega Z ++
    v60ChosenRightCtx X

/-- The finite-evidence shape from the v60 manuscript. -/
noncomputable def V60WitnessSet
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (epsilonStart : Prop) : Language Sigma :=
  fun z =>
    (∃ X : V60KeptState Obs terminal binary start, z = v60AnchorWord X) ∨
    (∃ (X : V60KeptState Obs terminal binary start) (a : Sigma),
      V60KeptTerminal X a ∧ z = v60TerminalWitnessWord X a) ∨
    (∃ X Y Z : V60KeptState Obs terminal binary start,
      V60KeptBinary X Y Z ∧ z = v60BinaryWitnessWord X Y Z) ∨
    (z = [] ∧ epsilonStart)

/-- Build the reconstruction interface directly from the actual trimmed v60 states. -/
noncomputable def v60ExtractedReconstructionBasis
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) :
    V60ReconstructionBasis Obs (V60KeptState Obs terminal binary start) where
  terminal := V60KeptTerminal
  binary := V60KeptBinary
  startState := V60KeptStart
  hasEpsilon := epsilonStart
  omega := v60ChosenOmega
  leftCtx := v60ChosenLeftCtx
  rightCtx := v60ChosenRightCtx
  yieldType := fun X => X.1.yieldType
  witnessSet := V60WitnessSet epsilonStart
  omega_nonempty := by
    intro X
    exact v60ChosenOmega_nonempty X
  omega_type := by
    intro X
    exact v60_yield_typed_invariant Obs terminal binary (v60ChosenOmega_spec X)
  terminal_type := by
    intro X a h
    exact h.2
  binary_yield_type := by
    intro X Y Z h
    exact h.2
  anchor_mem := by
    intro X
    exact Or.inl ⟨X, rfl⟩
  terminal_observation_mem := by
    intro X a h
    exact Or.inr (Or.inl ⟨X, a, h, rfl⟩)
  binary_observation_mem := by
    intro X Y Z h
    exact Or.inr (Or.inr (Or.inl ⟨X, Y, Z, h, rfl⟩))
  start_context := by
    intro X hStart
    exact (v60ChosenContext_spec X).2 hStart
  epsilon_mem := by
    intro h
    exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))

/-- The extracted basis derivations are exactly the trimmed v60 derivations. -/
theorem v60_extracted_basis_derives_iff_kept
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop)
    (X : V60KeptState Obs terminal binary start) (w : Word Sigma) :
    V60BasisDerives
        (v60ExtractedReconstructionBasis Obs terminal binary start epsilonStart)
        X w ↔
      V60KeptDerives Obs terminal binary start X w := by
  constructor
  · intro d
    induction d with
    | terminal hrule =>
        exact V60KeptDerives.terminal hrule
    | binary hrule left right ihLeft ihRight =>
        exact V60KeptDerives.binary hrule ihLeft ihRight
  · intro d
    induction d with
    | terminal hrule =>
        exact V60BasisDerives.terminal hrule
    | binary hrule left right ihLeft ihRight =>
        exact V60BasisDerives.binary hrule ihLeft ihRight

/-- The extracted reconstruction basis denotes exactly the trimmed typed language. -/
theorem v60_extracted_basis_language_iff_trimmed
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) (w : Word Sigma) :
    V60BasisLanguage
        (v60ExtractedReconstructionBasis Obs terminal binary start epsilonStart) w ↔
      V60TrimmedTypedStartLanguage Obs terminal binary start epsilonStart w := by
  constructor
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨X, hStart, hDeriv⟩
      exact Or.inr ⟨X, hStart,
        (v60_extracted_basis_derives_iff_kept
          Obs terminal binary start epsilonStart X w).mp hDeriv⟩
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨X, hStart, hDeriv⟩
      exact Or.inr ⟨X, hStart,
        (v60_extracted_basis_derives_iff_kept
          Obs terminal binary start epsilonStart X w).mpr hDeriv⟩

/-- Thus the extracted basis has exactly the original SSBNF language. -/
theorem v60_extracted_basis_language_iff_untyped
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) (w : Word Sigma) :
    V60BasisLanguage
        (v60ExtractedReconstructionBasis Obs terminal binary start epsilonStart) w ↔
      V60UntypedStartLanguage terminal binary start epsilonStart w := by
  exact (v60_extracted_basis_language_iff_trimmed
    Obs terminal binary start epsilonStart w).trans
      (v60_trimmed_typed_language_iff_untyped
        Obs terminal binary start epsilonStart w)

end FixedHCFG
end LeanCfgProject
