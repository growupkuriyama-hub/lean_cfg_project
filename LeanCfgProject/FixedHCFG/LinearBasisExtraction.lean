import LeanCfgProject.FixedHCFG.LinearLanguage
import LeanCfgProject.FixedHCFG.LinearCanonical
import LeanCfgProject.FixedHCFG.LinearTypedRefinement
import LeanCfgProject.FixedHCFG.LinearReconstruction

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Extraction of the Section-7 reconstruction basis from the actual typed linear
grammar `H = trim(fullTypedLinearGrammar Obs G)`.

This discharges the abstract witness/rule interface used by `LinearReconstruction`
with the concrete canonical `omega` and `chi` of the manuscript.
-/

/-- The actual reduced typed linear grammar `H` of Section 7.2. -/
abbrev ActualLinearGrammar
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :=
  trimStrictLinearGrammar (fullTypedLinearGrammar Obs G)

/-- Its retained typed nonterminals `W`. -/
abbrev ActualLinearState
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :=
  StrictLinearKeptState (fullTypedLinearGrammar Obs G)

/-- A start state has the empty canonical context pair. -/
theorem trimLinearChi_eq_nil_of_start
    {W : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (G : StrictLinearGrammar W Sigma)
    (X : StrictLinearKeptState G)
    (hstart : (trimStrictLinearGrammar G).startState X) :
    trimLinearLeftCtx G X = [] ∧ trimLinearRightCtx G X = [] := by
  have hocc0 : LinearOccurs (trimStrictLinearGrammar G) X [] [] :=
    ⟨[X], LinearOccursSpine.start hstart⟩
  have hnot := trimLinearChi_minimal G X hocc0
  have hLeft : trimLinearLeftCtx G X = [] := by
    by_contra hne
    have hpos : 0 < (trimLinearLeftCtx G X).length := by
      cases hleft : trimLinearLeftCtx G X with
      | nil => exact (hne hleft).elim
      | cons a xs => simp
    have hword : WordShortlex ([] : Word Sigma) (trimLinearLeftCtx G X) :=
      List.Shortlex.of_length_lt hpos
    have hsmall : ContextShortlex
        (([] : Word Sigma), ([] : Word Sigma))
        (trimLinearLeftCtx G X, trimLinearRightCtx G X) :=
      Prod.Lex.left _ _ hword
    exact hnot hsmall
  have hRight : trimLinearRightCtx G X = [] := by
    by_contra hne
    have hpos : 0 < (trimLinearRightCtx G X).length := by
      cases hright : trimLinearRightCtx G X with
      | nil => exact (hne hright).elim
      | cons a xs => simp
    have hword : WordShortlex ([] : Word Sigma) (trimLinearRightCtx G X) :=
      List.Shortlex.of_length_lt hpos
    have hsmall : ContextShortlex
        (([] : Word Sigma), ([] : Word Sigma))
        (trimLinearLeftCtx G X, trimLinearRightCtx G X) := by
      rw [hLeft]
      exact Prod.Lex.right [] hword
    exact hnot hsmall
  exact ⟨hLeft, hRight⟩

/--
The exact manuscript-shaped observation language `CS_lin(H)` before choosing a
finite indexing of realised rules.  It consists of anchors, one local witness
shape for each realised terminal/left/right rule, and epsilon when present.
-/
noncomputable def ActualLinearCS
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) : Language Sigma :=
  let F := fullTypedLinearGrammar Obs G
  let H := trimStrictLinearGrammar F
  fun z =>
    (∃ X : StrictLinearKeptState F,
      z = trimLinearLeftCtx F X ++ trimLinearOmega F X ++ trimLinearRightCtx F X) ∨
    (∃ X : StrictLinearKeptState F, ∃ a : Sigma,
      H.terminalRule X a ∧
      z = trimLinearLeftCtx F X ++ [a] ++ trimLinearRightCtx F X) ∨
    (∃ X Y : StrictLinearKeptState F, ∃ a : Sigma,
      H.leftRule X a Y ∧
      z = trimLinearLeftCtx F X ++ [a] ++ trimLinearOmega F Y ++
        trimLinearRightCtx F X) ∨
    (∃ X Y : StrictLinearKeptState F, ∃ a : Sigma,
      H.rightRule X Y a ∧
      z = trimLinearLeftCtx F X ++ trimLinearOmega F Y ++ [a] ++
        trimLinearRightCtx F X) ∨
    (H.hasEpsilon ∧ z = [])

/-- Canonical yields in the actual reduced typed linear grammar have the state's yield type. -/
theorem actualLinearOmega_type
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (X : ActualLinearState Obs G) :
    Obs.value (trimLinearOmega (fullTypedLinearGrammar Obs G) X) =
      X.1.yieldType := by
  have htrim := trimLinearOmega_spec (fullTypedLinearGrammar Obs G) X
  have hfull := linear_derives_forget_trim htrim
  exact linearTyped_yield_type_of_derives Obs G hfull

/-- The exact `LinearReconstructionBasis` extracted from the manuscript grammar `H`. -/
noncomputable def actualLinearReconstructionBasis
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :
    LinearReconstructionBasis Obs (ActualLinearState Obs G) := by
  let F := fullTypedLinearGrammar Obs G
  let H := trimStrictLinearGrammar F
  exact {
    terminal := H.terminalRule
    leftRule := H.leftRule
    rightRule := H.rightRule
    startState := H.startState
    hasEpsilon := H.hasEpsilon
    omega := trimLinearOmega F
    leftCtx := trimLinearLeftCtx F
    rightCtx := trimLinearRightCtx F
    yieldType := fun X => X.1.yieldType
    CS := ActualLinearCS Obs G
    omega_type := actualLinearOmega_type Obs G
    terminal_type := by
      intro X a hrule
      have hfull : F.terminalRule X.1 a := by
        simpa [H, trimStrictLinearGrammar] using hrule
      exact hfull.2
    left_rule_type := by
      intro X Y a hrule
      have hfull : F.leftRule X.1 a Y.1 := by
        simpa [H, trimStrictLinearGrammar] using hrule
      exact hfull.2.1.symm
    right_rule_type := by
      intro X Y a hrule
      have hfull : F.rightRule X.1 Y.1 a := by
        simpa [H, trimStrictLinearGrammar] using hrule
      exact hfull.2.1.symm
    anchor_mem := by
      intro X
      exact Or.inl ⟨X, rfl⟩
    terminal_observation_mem := by
      intro X a hrule
      exact Or.inr (Or.inl ⟨X, a, hrule, rfl⟩)
    left_observation_mem := by
      intro X Y a hrule
      exact Or.inr (Or.inr (Or.inl ⟨X, Y, a, hrule, rfl⟩))
    right_observation_mem := by
      intro X Y a hrule
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨X, Y, a, hrule, rfl⟩)))
    start_context := by
      intro X hstart
      exact trimLinearChi_eq_nil_of_start F X hstart
    epsilon_mem := by
      intro heps
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨heps, rfl⟩)))
  }

/-- Every exact Section-7 observation word is a positive word of `H`. -/
theorem actualLinearCS_subset_language
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :
    ActualLinearCS Obs G ⊆
      StrictLinearLanguage (ActualLinearGrammar Obs G) := by
  let F := fullTypedLinearGrammar Obs G
  let H := trimStrictLinearGrammar F
  intro z hz
  rcases hz with hAnchor | hTerm | hLeft | hRight | hEps
  · rcases hAnchor with ⟨X, rfl⟩
    exact linear_occurs_plug_derivation
      (trimLinearChi_spec F X) (trimLinearOmega_spec F X)
  · rcases hTerm with ⟨X, a, hrule, rfl⟩
    have hder : LinearDerives H X [a] :=
      ⟨[X], LinearDerivesSpine.terminal hrule⟩
    exact linear_occurs_plug_derivation (trimLinearChi_spec F X) hder
  · rcases hLeft with ⟨X, Y, a, hrule, rfl⟩
    rcases trimLinearOmega_spec F Y with ⟨sp, hY⟩
    have hder : LinearDerives H X ([a] ++ trimLinearOmega F Y) := by
      exact ⟨X :: sp, LinearDerivesSpine.left hrule hY⟩
    have hplug : StrictLinearLanguage H
        (trimLinearLeftCtx F X ++ ([a] ++ trimLinearOmega F Y) ++
          trimLinearRightCtx F X) :=
      linear_occurs_plug_derivation (trimLinearChi_spec F X) hder
    simpa [H, ActualLinearGrammar, List.append_assoc] using hplug
  · rcases hRight with ⟨X, Y, a, hrule, rfl⟩
    rcases trimLinearOmega_spec F Y with ⟨sp, hY⟩
    have hder : LinearDerives H X (trimLinearOmega F Y ++ [a]) :=
      ⟨X :: sp, LinearDerivesSpine.right hrule hY⟩
    have hplug : StrictLinearLanguage H
        (trimLinearLeftCtx F X ++ (trimLinearOmega F Y ++ [a]) ++
          trimLinearRightCtx F X) :=
      linear_occurs_plug_derivation (trimLinearChi_spec F X) hder
    simpa [H, ActualLinearGrammar, List.append_assoc] using hplug
  · rcases hEps with ⟨heps, rfl⟩
    exact Or.inl ⟨rfl, heps⟩

/-- Basis derivability extracted from `H` implies ordinary strict-linear derivability in `H`. -/
theorem actualBasisDerives_to_linear
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    {X : ActualLinearState Obs G} {z : Word Sigma}
    (d : LinearBasisDerives (actualLinearReconstructionBasis Obs G) X z) :
    LinearDerives (ActualLinearGrammar Obs G) X z := by
  induction d with
  | @terminal X a hrule =>
      refine ⟨[X], LinearDerivesSpine.terminal ?_⟩
      simpa [actualLinearReconstructionBasis, ActualLinearGrammar] using hrule
  | @left X Y a z hrule child ih =>
      rcases ih with ⟨sp, hchild⟩
      refine ⟨X :: sp, LinearDerivesSpine.left ?_ hchild⟩
      simpa [actualLinearReconstructionBasis, ActualLinearGrammar] using hrule
  | @right X Y a z hrule child ih =>
      rcases ih with ⟨sp, hchild⟩
      refine ⟨X :: sp, LinearDerivesSpine.right ?_ hchild⟩
      simpa [actualLinearReconstructionBasis, ActualLinearGrammar] using hrule

/-- Every ordinary spine derivation in `H` is represented by the extracted basis. -/
theorem linearSpine_to_actualBasisDerives
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    {X : ActualLinearState Obs G}
    {sp : List (ActualLinearState Obs G)} {z : Word Sigma}
    (d : LinearDerivesSpine (ActualLinearGrammar Obs G) X sp z) :
    LinearBasisDerives (actualLinearReconstructionBasis Obs G) X z := by
  induction d with
  | @terminal X a hrule =>
      exact LinearBasisDerives.terminal (by
        simpa [actualLinearReconstructionBasis, ActualLinearGrammar] using hrule)
  | @left X Y a sp z hrule child ih =>
      exact LinearBasisDerives.left (by
        simpa [actualLinearReconstructionBasis, ActualLinearGrammar] using hrule) ih
  | @right X Y a sp z hrule child ih =>
      exact LinearBasisDerives.right (by
        simpa [actualLinearReconstructionBasis, ActualLinearGrammar] using hrule) ih

/-- Ordinary derivability in `H` and derivability in the extracted basis coincide. -/
theorem actualBasisDerives_iff
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    {X : ActualLinearState Obs G} {z : Word Sigma} :
    LinearBasisDerives (actualLinearReconstructionBasis Obs G) X z ↔
      LinearDerives (ActualLinearGrammar Obs G) X z := by
  constructor
  · exact actualBasisDerives_to_linear Obs G
  · intro h
    rcases h with ⟨sp, hd⟩
    exact linearSpine_to_actualBasisDerives Obs G hd

/-- The language of the extracted reconstruction basis is exactly `L(H)`. -/
theorem actualBasisLanguage_eq
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :
    LinearBasisLanguage (actualLinearReconstructionBasis Obs G) =
      StrictLinearLanguage (ActualLinearGrammar Obs G) := by
  ext z
  constructor
  · intro hz
    rcases hz with hEps | hWord
    · exact Or.inl ⟨hEps.1, by
        simpa [actualLinearReconstructionBasis, ActualLinearGrammar] using hEps.2⟩
    · rcases hWord with ⟨X, hstart, hder⟩
      exact Or.inr ⟨X,
        by simpa [actualLinearReconstructionBasis, ActualLinearGrammar] using hstart,
        actualBasisDerives_to_linear Obs G hder⟩
  · intro hz
    rcases hz with hEps | hWord
    · exact Or.inl ⟨hEps.1, by
        simpa [actualLinearReconstructionBasis, ActualLinearGrammar] using hEps.2⟩
    · rcases hWord with ⟨X, hstart, hder⟩
      exact Or.inr ⟨X,
        by simpa [actualLinearReconstructionBasis, ActualLinearGrammar] using hstart,
        (actualBasisDerives_iff Obs G).mpr hder⟩

/-- Lemma 7.8 instantiated with the actual reduced typed linear grammar `H`. -/
theorem lemma_7_8_actual_typed_linear
    {N : Type v} {Sigma : Type u} {P : Type w}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (K : Language Sigma)
    (hCSK : ActualLinearCS Obs G ⊆ K)
    (hKL : K ⊆ StrictLinearLanguage (ActualLinearGrammar Obs G))
    (hSub : HSubstitutable Obs
      (StrictLinearLanguage (ActualLinearGrammar Obs G)))
    (z : Word Sigma) :
    StartDerives Obs K z ↔
      StrictLinearLanguage (ActualLinearGrammar Obs G) z := by
  let B := actualLinearReconstructionBasis Obs G
  have hLang : LinearBasisLanguage B =
      StrictLinearLanguage (ActualLinearGrammar Obs G) :=
    actualBasisLanguage_eq Obs G
  have hCSKB : B.CS ⊆ K := by
    simpa [B, actualLinearReconstructionBasis] using hCSK
  have hKLB : K ⊆ LinearBasisLanguage B := by
    intro x hx
    rw [hLang]
    exact hKL hx
  have hSubB : HSubstitutable Obs (LinearBasisLanguage B) := by
    rw [hLang]
    exact hSub
  have hExact := lemma_7_8_exact_reconstruction B K hCSKB hKLB hSubB z
  rw [hLang] at hExact
  exact hExact

end FixedHCFG
end LeanCfgProject
