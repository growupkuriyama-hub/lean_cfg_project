import LeanCfgProject.FixedHCFG.EnrichedExtraction
import LeanCfgProject.FixedHCFG.Identification

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-- A trimmed derivation certifies that its root state is retained. -/
theorem keptDerives_root_kept
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : KeptDerives Obs terminal binary start X w) :
    TypedKept Obs terminal binary start X := by
  cases d with
  | terminal hrule htype hkeep => exact hkeep
  | binary hrule hproduct hkeep left right => exact hkeep

/-- Every trimmed derivation is represented by the concrete reconstruction basis. -/
theorem keptDerives_to_enrichedBasis_exists
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : KeptDerives Obs terminal binary start X w) :
    ∃ hkeep : TypedKept Obs terminal binary start X,
      BasisDerives
        (enrichedReconstructionBasis Obs terminal binary start epsilonStart)
        (⟨X, hkeep⟩ : KeptState Obs terminal binary start) w := by
  induction d with
  | @terminal A a p m n hrule htype hkeep =>
      refine ⟨hkeep, ?_⟩
      exact BasisDerives.terminal ⟨hrule, htype⟩
  | @binary A B C p m n q r x y hrule hproduct hkeep left right ihLeft ihRight =>
      rcases ihLeft with ⟨hLeftKeep, hLeftBasis⟩
      rcases ihRight with ⟨hRightKeep, hRightBasis⟩
      let Xs : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := p, leftType := m, rightType := n }, hkeep⟩
      let Ys : KeptState Obs terminal binary start :=
        ⟨{ label := B,
           yieldType := q,
           leftType := m,
           rightType := Obs.mul r n }, hLeftKeep⟩
      let Zs : KeptState Obs terminal binary start :=
        ⟨{ label := C,
           yieldType := r,
           leftType := Obs.mul m q,
           rightType := n }, hRightKeep⟩
      have hRule : keptBinary Xs Ys Zs := by
        exact ⟨hrule, hproduct, rfl, rfl, rfl, rfl⟩
      refine ⟨hkeep, ?_⟩
      exact BasisDerives.binary hRule hLeftBasis hRightBasis

/-- Every extracted-basis derivation is a trimmed typed derivation. -/
theorem enrichedBasisDerives_to_kept
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    {X : KeptState Obs terminal binary start} {w : Word Sigma}
    (d : BasisDerives
      (enrichedReconstructionBasis Obs terminal binary start epsilonStart) X w) :
    KeptDerives Obs terminal binary start X.1 w := by
  induction d with
  | @terminal X a hrule =>
      exact KeptDerives.terminal hrule.1 hrule.2 X.property
  | @binary X Y Z x y hrule left right ihLeft ihRight =>
      rcases X with ⟨⟨A, p, m, n⟩, hXKeep⟩
      rcases Y with ⟨⟨B, q, mY, nY⟩, hYKeep⟩
      rcases Z with ⟨⟨C, r, mZ, nZ⟩, hZKeep⟩
      change
        binary A B C ∧
          Obs.mul q r = p ∧
          mY = m ∧
          nY = Obs.mul r n ∧
          mZ = Obs.mul m q ∧
          nZ = n at hrule
      rcases hrule with ⟨hBinary, hProduct, hmY, hnY, hmZ, hnZ⟩
      subst mY
      subst nY
      subst mZ
      subst nZ
      exact KeptDerives.binary hBinary hProduct hXKeep ihLeft ihRight

/-- The extracted reconstruction basis has exactly the trimmed typed language. -/
theorem enrichedBasisLanguage_iff_trimmed
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    BasisLanguage
        (enrichedReconstructionBasis Obs terminal binary start epsilonStart) w ↔
      TrimmedTypedStartLanguage Obs terminal binary start epsilonStart w := by
  constructor
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨X, hStart, hDeriv⟩
      have hKept := enrichedBasisDerives_to_kept
        Obs terminal binary start epsilonStart hDeriv
      rcases X with ⟨⟨A, p, m, n⟩, hXKeep⟩
      change start A ∧ m = Obs.one ∧ n = Obs.one at hStart
      rcases hStart with ⟨hA, hm, hn⟩
      subst m
      subst n
      exact Or.inr ⟨A, p, hA, hKept⟩
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨A, p, hA, hDeriv⟩
      rcases keptDerives_to_enrichedBasis_exists
          Obs terminal binary start epsilonStart hDeriv with
        ⟨hKeep, hBasis⟩
      let X : KeptState Obs terminal binary start :=
        ⟨{ label := A,
           yieldType := p,
           leftType := Obs.one,
           rightType := Obs.one }, hKeep⟩
      exact Or.inr ⟨X, ⟨hA, rfl, rfl⟩, hBasis⟩

/-- The extracted basis has exactly the original SSBNF presentation language. -/
theorem enrichedBasisLanguage_iff_untyped
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    BasisLanguage
        (enrichedReconstructionBasis Obs terminal binary start epsilonStart) w ↔
      UntypedStartLanguage terminal binary start epsilonStart w := by
  exact (enrichedBasisLanguage_iff_trimmed
    Obs terminal binary start epsilonStart w).trans
      (lemma_4_5_iii_trimmed_language
        Obs terminal binary start epsilonStart w)

/-- Plugging a terminal derivation into an occurrence yields a full typed start derivation. -/
theorem typedOccurs_plug_start
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    {X : TypedNT N Obs} {u v w : Word Sigma}
    (hOcc : TypedOccurs Obs terminal binary start X u v)
    (hDeriv : TypedDerives Obs terminal binary X w) :
    ∃ (A : N) (p : Obs.M),
      start A ∧
        TypedDerives Obs terminal binary
          { label := A,
            yieldType := p,
            leftType := Obs.one,
            rightType := Obs.one }
          (u ++ w ++ v) := by
  induction hOcc generalizing w with
  | @start A p hStart =>
      exact ⟨A, p, hStart, by simpa using hDeriv⟩
  | @left A B C p m n q r u v y parent hrule hproduct rightDeriv ih =>
      have hParentDeriv : TypedDerives Obs terminal binary
          { label := A, yieldType := p, leftType := m, rightType := n }
          (w ++ y) :=
        TypedDerives.binary hrule hproduct hDeriv rightDeriv
      rcases ih hParentDeriv with ⟨S, s, hS, hRoot⟩
      refine ⟨S, s, hS, ?_⟩
      simpa [List.append_assoc] using hRoot
  | @right A B C p m n q r u v x parent hrule hproduct leftDeriv ih =>
      have hParentDeriv : TypedDerives Obs terminal binary
          { label := A, yieldType := p, leftType := m, rightType := n }
          (x ++ w) :=
        TypedDerives.binary hrule hproduct leftDeriv hDeriv
      rcases ih hParentDeriv with ⟨S, s, hS, hRoot⟩
      refine ⟨S, s, hS, ?_⟩
      simpa [List.append_assoc] using hRoot

/-- Plugging a typed occurrence and trimming gives a word of the trimmed language. -/
theorem typedOccurs_plug_trimmed
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    {X : TypedNT N Obs} {u v w : Word Sigma}
    (hOcc : TypedOccurs Obs terminal binary start X u v)
    (hDeriv : TypedDerives Obs terminal binary X w) :
    TrimmedTypedStartLanguage Obs terminal binary start epsilonStart
      (u ++ w ++ v) := by
  rcases typedOccurs_plug_start Obs terminal binary start hOcc hDeriv with
    ⟨A, p, hA, hRoot⟩
  have hRootOcc : TypedOccurs Obs terminal binary start
      { label := A,
        yieldType := p,
        leftType := Obs.one,
        rightType := Obs.one } [] [] :=
    TypedOccurs.start (p := p) hA
  have hKept := successful_derivation_survives
    Obs terminal binary start hRootOcc hRoot
  exact Or.inr ⟨A, p, hA, hKept⟩

/-- Lemma 4.7 for the enriched interface: every observation is positive. -/
theorem enrichedCS_subset_trimmed
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    EnrichedCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart ⊆
      TrimmedTypedStartLanguage Obs terminal binary start epsilonStart := by
  intro z hz
  rcases hz with hAnchor | hTerminal | hBinary | hEps
  · rcases hAnchor with ⟨X, rfl⟩
    exact typedOccurs_plug_trimmed Obs terminal binary start epsilonStart
      (chosenContext_spec X).1 (chosenOmega_spec X)
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    rcases X with ⟨⟨A, p, m, n⟩, hKeep⟩
    change terminal A a ∧ Obs.value [a] = p at hRule
    have hDeriv : TypedDerives Obs terminal binary
        { label := A, yieldType := p, leftType := m, rightType := n } [a] :=
      TypedDerives.terminal hRule.1 hRule.2
    exact typedOccurs_plug_trimmed Obs terminal binary start epsilonStart
      (chosenContext_spec
        (⟨{ label := A, yieldType := p, leftType := m, rightType := n }, hKeep⟩ :
          KeptState Obs terminal binary start)).1 hDeriv
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    rcases X with ⟨⟨A, p, m, n⟩, hXKeep⟩
    rcases Y with ⟨⟨B, q, mY, nY⟩, hYKeep⟩
    rcases Z with ⟨⟨C, r, mZ, nZ⟩, hZKeep⟩
    change
      binary A B C ∧
        Obs.mul q r = p ∧
        mY = m ∧
        nY = Obs.mul r n ∧
        mZ = Obs.mul m q ∧
        nZ = n at hRule
    rcases hRule with ⟨hBC, hProduct, hmY, hnY, hmZ, hnZ⟩
    subst mY
    subst nY
    subst mZ
    subst nZ
    let Xs : KeptState Obs terminal binary start :=
      ⟨{ label := A, yieldType := p, leftType := m, rightType := n }, hXKeep⟩
    let Ys : KeptState Obs terminal binary start :=
      ⟨{ label := B,
         yieldType := q,
         leftType := m,
         rightType := Obs.mul r n }, hYKeep⟩
    let Zs : KeptState Obs terminal binary start :=
      ⟨{ label := C,
         yieldType := r,
         leftType := Obs.mul m q,
         rightType := n }, hZKeep⟩
    have hDeriv : TypedDerives Obs terminal binary Xs.1
        (chosenOmega Ys ++ chosenOmega Zs) :=
      TypedDerives.binary hBC hProduct
        (chosenOmega_spec Ys) (chosenOmega_spec Zs)
    have hPlug := typedOccurs_plug_trimmed
      (X := Xs.1)
      (u := chosenLeftCtx Xs)
      (v := chosenRightCtx Xs)
      (w := chosenOmega Ys ++ chosenOmega Zs)
      Obs terminal binary start epsilonStart
      (chosenContext_spec Xs).1 hDeriv
    change TrimmedTypedStartLanguage Obs terminal binary start epsilonStart
      (chosenLeftCtx Xs ++ chosenOmega Ys ++ chosenOmega Zs ++ chosenRightCtx Xs)
    simpa only [List.append_assoc] using hPlug
  · rcases hEps with ⟨rfl, hEpsilon⟩
    exact Or.inl ⟨rfl, hEpsilon⟩

/-- Lemma 4.7 in the original-language formulation. -/
theorem enrichedCS_subset_untyped
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    EnrichedCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart ⊆
      UntypedStartLanguage terminal binary start epsilonStart := by
  intro w hw
  exact (lemma_4_5_iii_trimmed_language
    Obs terminal binary start epsilonStart w).mp
      (enrichedCS_subset_trimmed
        Obs terminal binary start epsilonStart hw)

/-- The enriched observation set is contained in its extracted basis language. -/
theorem enrichedCS_subset_basisLanguage
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    (enrichedReconstructionBasis Obs terminal binary start epsilonStart).CS ⊆
      BasisLanguage
        (enrichedReconstructionBasis Obs terminal binary start epsilonStart) := by
  intro w hw
  apply (enrichedBasisLanguage_iff_trimmed
    Obs terminal binary start epsilonStart w).mpr
  exact enrichedCS_subset_trimmed
    Obs terminal binary start epsilonStart hw

/--
End-to-end Corollary 5.8 for a concrete SSBNF presentation.
-/
theorem corollary_5_8_from_ssbnf
    {N : Type v} {Sigma : Type u}
    [Finite N] [Finite Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart))
    (text : Nat → Word Sigma)
    (hText : TextFor
      (UntypedStartLanguage terminal binary start epsilonStart) text) :
    ∃ N0 : Nat, ∀ n : Nat, N0 ≤ n →
      ∀ w : Word Sigma,
        StartDerives Obs (PrefixSample text n) w ↔
          UntypedStartLanguage terminal binary start epsilonStart w := by
  let B := enrichedReconstructionBasis Obs terminal binary start epsilonStart
  have hLangEq : BasisLanguage B =
      UntypedStartLanguage terminal binary start epsilonStart := by
    apply Set.ext
    intro w
    exact enrichedBasisLanguage_iff_untyped
      Obs terminal binary start epsilonStart w
  have hFinite : B.CS.Finite := by
    simpa [B, enrichedReconstructionBasis] using
      (enrichedCS_finite
        (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart)
  have hCS : B.CS ⊆ BasisLanguage B := by
    simpa [B] using
      (enrichedCS_subset_basisLanguage
        Obs terminal binary start epsilonStart)
  have hSubB : HSubstitutable Obs (BasisLanguage B) := by
    rw [hLangEq]
    exact hSub
  have hTextB : TextFor (BasisLanguage B) text := by
    rw [hLangEq]
    exact hText
  obtain ⟨N0, hN0⟩ :=
    corollary_5_8_semantic_identification B hFinite hCS hSubB text hTextB
  refine ⟨N0, ?_⟩
  intro n hn w
  have h := hN0 n hn w
  rw [hLangEq] at h
  exact h

end FixedHCFG
end LeanCfgProject
