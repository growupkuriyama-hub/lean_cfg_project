import LeanCfgProject.FixedHCFGv44.ClarkCongruentialCoreV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Language-level packaging of the inclusion half of TCS v49 Proposition
`prop:clark-congruential-comparison`.

The paper replaces the separated start symbol by the finitely many retained
yield-typed states licensed by a start rule.  Each such state's terminal
language is contained in one syntactic congruence class by
`typedNonterminal_yields_syntactically_congruent_v49`.  If epsilon belongs to
the target, a fresh initial epsilon-only component is added.

We formalize exactly that finite-initial-set argument here, without introducing
a second general CFG datatype merely to re-encode the already verified reduced
typed grammar.
-/

/-- Terminal language generated from one retained yield-typed non-start state. -/
def KeptStateLanguageV49
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    (X : KeptState Obs terminal binary start) : Language Sigma :=
  fun w => KeptDerives Obs terminal binary start X.1 w

/-- Retained typed states that are licensed by an original start rule. -/
def TypedInitialSetV49
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) : Set (KeptState Obs terminal binary start) :=
  {X | keptStart X}

/-- Union of the terminal languages of the finite typed initial set. -/
def TypedInitialUnionV49
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) : Language Sigma :=
  fun w => ∃ X : KeptState Obs terminal binary start,
    X ∈ TypedInitialSetV49 Obs terminal binary start ∧
      w ∈ KeptStateLanguageV49 Obs terminal binary start X

/-- The epsilon-only language used for the fresh Clark initial component. -/
def EpsilonOnlyV49 {Sigma : Type u} : Language Sigma :=
  fun w => w = []

/-- Pairwise form of “contained in one syntactic congruence class”. -/
def SyntacticallyHomogeneousV49
    {Sigma : Type u} (L K : Language Sigma) : Prop :=
  ∀ ⦃x : Word Sigma⦄, x ∈ K →
    ∀ ⦃y : Word Sigma⦄, y ∈ K → SameDistribution L x y

/-- Every retained typed nonterminal language is syntactically homogeneous. -/
theorem keptStateLanguage_syntacticallyHomogeneous_v49
    {N : Type v} {Sigma : Type u}
    [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart))
    (X : KeptState Obs terminal binary start) :
    SyntacticallyHomogeneousV49
      (UntypedStartLanguage terminal binary start epsilonStart)
      (KeptStateLanguageV49 Obs terminal binary start X) := by
  intro x hx y hy
  exact typedNonterminal_yields_syntactically_congruent_v49
    Obs terminal binary start epsilonStart hSub X
    (kept_to_full Obs terminal binary start hx)
    (kept_to_full Obs terminal binary start hy)

/-- The fresh epsilon-only component is trivially one syntactic class. -/
theorem epsilonOnly_syntacticallyHomogeneous_v49
    {Sigma : Type u} (L : Language Sigma) :
    SyntacticallyHomogeneousV49 L (EpsilonOnlyV49 : Language Sigma) := by
  intro x hx y hy
  change x = [] at hx
  change y = [] at hy
  subst x
  subst y
  intro p q
  rfl

/-- The typed initial set is finite whenever the original nonterminal set is finite. -/
theorem typedInitialSet_finite_v49
    {N : Type v} {Sigma : Type u}
    [Finite N]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) :
    (TypedInitialSetV49 Obs terminal binary start).Finite := by
  let encode : KeptState Obs terminal binary start → N × Obs.M :=
    fun X => (X.1.label, X.1.yieldType)
  have hEncode : Function.Injective encode := by
    intro X Y hXY
    apply Subtype.ext
    apply TypedNT.ext
    · exact congrArg Prod.fst hXY
    · exact congrArg Prod.snd hXY
  letI : Finite (KeptState Obs terminal binary start) :=
    Finite.of_injective encode hEncode
  exact Set.toFinite _

/--
The finite typed initial set generates exactly the non-epsilon part of the
original SSBNF target.
-/
theorem typedInitialUnion_iff_nonempty_target_v49
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (w : Word Sigma) :
    TypedInitialUnionV49 Obs terminal binary start w ↔
      Internal w ∧ UntypedStartLanguage terminal binary start epsilonStart w := by
  constructor
  · rintro ⟨X, hStart, hDeriv⟩
    have hFull := kept_to_full Obs terminal binary start hDeriv
    refine ⟨typed_derives_internal Obs terminal binary hFull, ?_⟩
    exact Or.inr ⟨X.1.label, hStart,
      erase_typed_derivation Obs terminal binary hFull⟩
  · rintro ⟨hInternal, hTarget⟩
    rcases hTarget with hEps | hNonempty
    · exact (hInternal hEps.1).elim
    · rcases hNonempty with ⟨A, hStart, hUntyped⟩
      let mu : Obs.M := obsValue Obs w
      have hTyped : TypedDerives Obs terminal binary
          { label := A, yieldType := mu } w := by
        simpa [mu] using
          full_yield_typed_lift Obs terminal binary hUntyped
      have hOcc : TypedOccurs Obs terminal binary start
          { label := A, yieldType := mu } [] [] :=
        TypedOccurs.start (mu := mu) hStart
      have hKeptDeriv := successful_derivation_survives
        Obs terminal binary start hOcc hTyped
      have hKeep : TypedKept Obs terminal binary start
          { label := A, yieldType := mu } :=
        keptDerives_root_kept Obs terminal binary start hKeptDeriv
      let X : KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := mu }, hKeep⟩
      exact ⟨X, hStart, hKeptDeriv⟩

/--
Adding the fresh epsilon-only initial component when required recovers the full
target language exactly.
-/
theorem typedInitialUnion_with_epsilon_eq_target_v49
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    (fun w : Word Sigma =>
      TypedInitialUnionV49 Obs terminal binary start w ∨
        (w ∈ EpsilonOnlyV49 ∧ epsilonStart)) =
      UntypedStartLanguage terminal binary start epsilonStart := by
  ext w
  constructor
  · intro hw
    rcases hw with hTyped | hEps
    · exact (typedInitialUnion_iff_nonempty_target_v49
        Obs terminal binary start epsilonStart w).mp hTyped |>.2
    · exact Or.inl ⟨hEps.1, hEps.2⟩
  · intro hw
    rcases hw with hEps | hNonempty
    · exact Or.inr ⟨hEps.1, hEps.2⟩
    · left
      have hInternal : Internal w := by
        rcases hNonempty with ⟨A, hStart, hDeriv⟩
        exact typed_derives_internal Obs terminal binary
          (full_yield_typed_lift Obs terminal binary hDeriv)
      exact (typedInitialUnion_iff_nonempty_target_v49
        Obs terminal binary start epsilonStart w).mpr
          ⟨hInternal, Or.inr hNonempty⟩

/--
Formal inclusion package underlying v49 Proposition
`prop:clark-congruential-comparison` for a fixed reduced SSBNF presentation.
It supplies the finite initial set, congruentiality of every retained typed
state language, and exact generation of the target after the optional fresh
epsilon component is added.
-/
theorem clark_congruential_inclusion_package_v49
    {N : Type v} {Sigma : Type u}
    [Finite N] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    (TypedInitialSetV49 Obs terminal binary start).Finite ∧
    (∀ X : KeptState Obs terminal binary start,
      SyntacticallyHomogeneousV49
        (UntypedStartLanguage terminal binary start epsilonStart)
        (KeptStateLanguageV49 Obs terminal binary start X)) ∧
    SyntacticallyHomogeneousV49
      (UntypedStartLanguage terminal binary start epsilonStart)
      (EpsilonOnlyV49 : Language Sigma) ∧
    (fun w : Word Sigma =>
      TypedInitialUnionV49 Obs terminal binary start w ∨
        (w ∈ EpsilonOnlyV49 ∧ epsilonStart)) =
      UntypedStartLanguage terminal binary start epsilonStart := by
  refine ⟨typedInitialSet_finite_v49 Obs terminal binary start, ?_, ?_, ?_⟩
  · intro X
    exact keptStateLanguage_syntacticallyHomogeneous_v49
      Obs terminal binary start epsilonStart hSub X
  · exact epsilonOnly_syntacticallyHomogeneous_v49 _
  · exact typedInitialUnion_with_epsilon_eq_target_v49
      Obs terminal binary start epsilonStart

end FixedHCFGv44
end LeanCfgProject
