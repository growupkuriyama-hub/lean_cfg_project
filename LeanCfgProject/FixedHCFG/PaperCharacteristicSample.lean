import LeanCfgProject.FixedHCFG.ShortlexWitness
import LeanCfgProject.FixedHCFG.EndToEnd

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-- Canonical terminal-rule observation from Section 4.3. -/
noncomputable def paperTerminalObservationWord
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) (a : Sigma) : Word Sigma :=
  shortlexLeftCtx X ++ [a] ++ shortlexRightCtx X

/-- Canonical binary-rule observation `u_X omega(Y) omega(Z) v_X`. -/
noncomputable def paperBinaryObservationWord
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X Y Z : KeptState Obs terminal binary start) : Word Sigma :=
  shortlexLeftCtx X ++ shortlexOmega Y ++ shortlexOmega Z ++ shortlexRightCtx X

/-- Canonical anchor `u_X omega(X) v_X`.  It is not inserted separately into `PaperCS`. -/
noncomputable def paperAnchorWord
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma :=
  shortlexLeftCtx X ++ shortlexOmega X ++ shortlexRightCtx X

/--
The characteristic sample exactly as in Section 4.3 of the TCS manuscript:
one canonical observation per realizable non-start rule, plus epsilon when the
start epsilon rule is present.  Unlike `EnrichedCS`, anchors are not added as
an extra family.
-/
noncomputable def PaperCS
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) : Language Sigma :=
  fun z =>
    (∃ (X : KeptState Obs terminal binary start) (a : Sigma),
      keptTerminal X a ∧ z = paperTerminalObservationWord X a) ∨
    (∃ X Y Z : KeptState Obs terminal binary start,
      keptBinary X Y Z ∧ z = paperBinaryObservationWord X Y Z) ∨
    (z = [] ∧ epsilonStart)

/--
Lemma 4.8: every reachable productive typed state has its canonical anchor in
the manuscript characteristic sample, although anchors are not a separate
family in the definition of `PaperCS`.
-/
theorem lemma_4_8_paper_anchor_mem
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop)
    (X : KeptState Obs terminal binary start) :
    paperAnchorWord X ∈
      PaperCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart := by
  rcases shortlexOmega_root_decomposition X with hTerm | hBin
  · rcases hTerm with ⟨a, hRule, hOmega⟩
    left
    refine ⟨X, a, hRule, ?_⟩
    simp only [paperAnchorWord, paperTerminalObservationWord]
    rw [hOmega]
  · rcases hBin with ⟨Y, Z, hRule, hOmega⟩
    right
    left
    refine ⟨X, Y, Z, hRule, ?_⟩
    simp only [paperAnchorWord, paperBinaryObservationWord]
    rw [hOmega]
    simp only [List.append_assoc]

/-- The exact paper characteristic sample is finite. -/
theorem paperCS_finite
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Finite N] [Finite Sigma]
    (epsilonStart : Prop) :
    (PaperCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart).Finite := by
  let W := KeptState Obs terminal binary start
  let T : Set (Word Sigma) := Set.range
    (fun p : W × Sigma => paperTerminalObservationWord p.1 p.2)
  let R : Set (Word Sigma) := Set.range
    (fun p : W × W × W => paperBinaryObservationWord p.1 p.2.1 p.2.2)
  have hT : T.Finite := Set.finite_range _
  have hR : R.Finite := Set.finite_range _
  have hAll : (T ∪ R ∪ ({[]} : Set (Word Sigma))).Finite :=
    ((hT.union hR).union (Set.finite_singleton []))
  refine hAll.subset ?_
  intro z hz
  rcases hz with hTerminal | hBinary | hEps
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    exact Or.inl (Or.inl ⟨(X, a), rfl⟩)
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    exact Or.inl (Or.inr ⟨(X, Y, Z), rfl⟩)
  · rcases hEps with ⟨rfl, hStart⟩
    exact Or.inr (Set.mem_singleton [])

/--
Theorem 4.12 interface, now using the manuscript's exact shortlex witnesses and
its exact characteristic sample rather than the enriched auxiliary sample.
-/
noncomputable def paperReconstructionBasis
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    ReconstructionBasis Obs (KeptState Obs terminal binary start) where
  terminal := keptTerminal
  binary := keptBinary
  startState := keptStart
  hasEpsilon := epsilonStart
  omega := shortlexOmega
  leftCtx := shortlexLeftCtx
  rightCtx := shortlexRightCtx
  yieldType := fun X => X.1.yieldType
  leftType := fun X => X.1.leftType
  rightType := fun X => X.1.rightType
  CS := PaperCS epsilonStart
  omega_type := by
    intro X
    exact lemma_4_5_i_yield_type Obs terminal binary (shortlexOmega_spec X)
  left_context_type := by
    intro X
    exact (lemma_4_5_ii_context_type Obs terminal binary start
      (shortlexChi_spec X)).1
  right_context_type := by
    intro X
    exact (lemma_4_5_ii_context_type Obs terminal binary start
      (shortlexChi_spec X)).2
  terminal_type := by
    intro X a h
    exact h.2
  binary_yield_type := by
    intro X Y Z h
    exact h.2.1
  anchor_mem := by
    intro X
    exact lemma_4_8_paper_anchor_mem epsilonStart X
  terminal_observation_mem := by
    intro X a h
    exact Or.inl ⟨X, a, h, rfl⟩
  binary_observation_mem := by
    intro X Y Z h
    exact Or.inr (Or.inl ⟨X, Y, Z, h, rfl⟩)
  start_context := by
    intro X h
    exact shortlexChi_start_empty X h
  epsilon_mem := by
    intro h
    exact Or.inr (Or.inr ⟨rfl, h⟩)

/-- Lemma 4.7: every exact paper observation is a positive target example. -/
theorem lemma_4_7_paperCS_subset_trimmed
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    PaperCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart ⊆
      TrimmedTypedStartLanguage Obs terminal binary start epsilonStart := by
  intro z hz
  rcases hz with hTerminal | hBinary | hEps
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    have hDeriv : TypedDerives Obs terminal binary X.1 [a] := by
      rcases X with ⟨⟨A, p, m, n⟩, hKeep⟩
      change terminal A a ∧ Obs.value [a] = p at hRule
      exact TypedDerives.terminal hRule.1 hRule.2
    exact typedOccurs_plug_trimmed Obs terminal binary start epsilonStart
      (shortlexChi_spec X) hDeriv
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    have hDeriv : TypedDerives Obs terminal binary X.1
        (shortlexOmega Y ++ shortlexOmega Z) :=
      keptBinary_derives hRule (shortlexOmega_spec Y) (shortlexOmega_spec Z)
    have hPlug := typedOccurs_plug_trimmed
      (X := X.1)
      (u := shortlexLeftCtx X)
      (v := shortlexRightCtx X)
      (w := shortlexOmega Y ++ shortlexOmega Z)
      Obs terminal binary start epsilonStart
      (shortlexChi_spec X) hDeriv
    change TrimmedTypedStartLanguage Obs terminal binary start epsilonStart
      (shortlexLeftCtx X ++ shortlexOmega Y ++ shortlexOmega Z ++ shortlexRightCtx X)
    simpa only [List.append_assoc] using hPlug
  · rcases hEps with ⟨rfl, hStart⟩
    exact Or.inl ⟨rfl, hStart⟩

/-- Lemma 4.7 in the original untyped target-language formulation. -/
theorem lemma_4_7_paperCS_subset_untyped
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    PaperCS (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart ⊆
      UntypedStartLanguage terminal binary start epsilonStart := by
  intro w hw
  exact (lemma_4_5_iii_trimmed_language
    Obs terminal binary start epsilonStart w).mp
      (lemma_4_7_paperCS_subset_trimmed
        Obs terminal binary start epsilonStart hw)

/-- A trimmed derivation is represented by the paper reconstruction basis. -/
theorem keptDerives_to_paperBasis_exists
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    {X : TypedNT N Obs} {w : Word Sigma}
    (d : KeptDerives Obs terminal binary start X w) :
    ∃ hkeep : TypedKept Obs terminal binary start X,
      BasisDerives
        (paperReconstructionBasis Obs terminal binary start epsilonStart)
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
        ⟨{ label := B, yieldType := q, leftType := m,
           rightType := Obs.mul r n }, hLeftKeep⟩
      let Zs : KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := r, leftType := Obs.mul m q,
           rightType := n }, hRightKeep⟩
      have hRule : keptBinary Xs Ys Zs := by
        exact ⟨hrule, hproduct, rfl, rfl, rfl, rfl⟩
      refine ⟨hkeep, ?_⟩
      exact BasisDerives.binary hRule hLeftBasis hRightBasis

/-- A paper-basis derivation is a trimmed typed derivation after removing subtype wrappers. -/
theorem paperBasisDerives_to_kept
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    {X : KeptState Obs terminal binary start} {w : Word Sigma}
    (d : BasisDerives
      (paperReconstructionBasis Obs terminal binary start epsilonStart) X w) :
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

/-- The paper basis generates exactly the trimmed typed language. -/
theorem paperBasisLanguage_iff_trimmed
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    BasisLanguage
        (paperReconstructionBasis Obs terminal binary start epsilonStart) w ↔
      TrimmedTypedStartLanguage Obs terminal binary start epsilonStart w := by
  constructor
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨X, hStart, hDeriv⟩
      have hKept := paperBasisDerives_to_kept
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
      rcases keptDerives_to_paperBasis_exists
          Obs terminal binary start epsilonStart hDeriv with
        ⟨hKeep, hBasis⟩
      let X : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := p,
           leftType := Obs.one, rightType := Obs.one }, hKeep⟩
      exact Or.inr ⟨X, ⟨hA, rfl, rfl⟩, hBasis⟩

/-- Consequently the paper basis generates exactly the original SSBNF language. -/
theorem paperBasisLanguage_iff_untyped
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    BasisLanguage
        (paperReconstructionBasis Obs terminal binary start epsilonStart) w ↔
      UntypedStartLanguage terminal binary start epsilonStart w := by
  exact (paperBasisLanguage_iff_trimmed
    Obs terminal binary start epsilonStart w).trans
      (lemma_4_5_iii_trimmed_language
        Obs terminal binary start epsilonStart w)

/-- The exact paper characteristic sample lies inside its reconstruction-basis language. -/
theorem paperCS_subset_basisLanguage
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    (paperReconstructionBasis Obs terminal binary start epsilonStart).CS ⊆
      BasisLanguage
        (paperReconstructionBasis Obs terminal binary start epsilonStart) := by
  intro w hw
  apply (paperBasisLanguage_iff_trimmed
    Obs terminal binary start epsilonStart w).mpr
  exact lemma_4_7_paperCS_subset_trimmed
    Obs terminal binary start epsilonStart hw

/--
Corollary 5.8 with the manuscript characteristic sample itself: on every text
for a fixed-h-substitutable SSBNF target, the canonical learner eventually
stabilizes semantically to the target language.
-/
theorem corollary_5_8_from_ssbnf_paperCS
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
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
  let B := paperReconstructionBasis Obs terminal binary start epsilonStart
  have hLangEq : BasisLanguage B =
      UntypedStartLanguage terminal binary start epsilonStart := by
    apply Set.ext
    intro w
    exact paperBasisLanguage_iff_untyped
      Obs terminal binary start epsilonStart w
  have hFinite : B.CS.Finite := by
    simpa [B, paperReconstructionBasis] using
      (paperCS_finite
        (Obs := Obs) (terminal := terminal) (binary := binary)
        (start := start) epsilonStart)
  have hCS : B.CS ⊆ BasisLanguage B := by
    simpa [B] using
      (paperCS_subset_basisLanguage
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
