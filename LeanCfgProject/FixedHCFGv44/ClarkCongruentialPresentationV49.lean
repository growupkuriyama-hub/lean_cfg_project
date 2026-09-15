import LeanCfgProject.FixedHCFGv44.ClarkCongruentialInitialSetV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Actual grammar-object packaging for the inclusion half of TCS v49 Proposition
`prop:clark-congruential-comparison`.

The earlier Clark files prove the semantic core using retained yield-typed
states.  Here we turn that core into an ordinary finite SSBNF presentation:
its nonterminals are the yield-typed states themselves, while its productions
are restricted to retained states.  Thus every nonterminal language of the
constructed grammar lies in one syntactic congruence class of the target.
-/

/-- Terminal rules of the retained typed grammar, viewed as ordinary SSBNF
rules on `TypedNT`. -/
def ClarkTypedTerminalV49
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) :
    TerminalRules (TypedNT N Obs) Sigma :=
  fun X a =>
    terminal X.label a ∧
      obsValue Obs [a] = X.yieldType ∧
      TypedKept Obs terminal binary start X

/-- Binary rules of the retained typed grammar, viewed as ordinary SSBNF
rules on `TypedNT`. -/
def ClarkTypedBinaryV49
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) :
    BinaryRules (TypedNT N Obs) :=
  fun X Y Z =>
    binary X.label Y.label Z.label ∧
      Obs.mul Y.yieldType Z.yieldType = X.yieldType ∧
      TypedKept Obs terminal binary start X

/-- Initial states are precisely retained typed copies licensed by an original
start rule. -/
def ClarkTypedStartV49
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) :
    StartRules (TypedNT N Obs) :=
  fun X => start X.label ∧ TypedKept Obs terminal binary start X

/-- Ordinary derivations of the constructed grammar are exactly derivations in
the retained yield-typed grammar. -/
theorem clarkTyped_derives_iff_kept_v49
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N)
    (X : TypedNT N Obs) (w : Word Sigma) :
    UntypedDerives
        (ClarkTypedTerminalV49 Obs terminal binary start)
        (ClarkTypedBinaryV49 Obs terminal binary start) X w ↔
      KeptDerives Obs terminal binary start X w := by
  constructor
  · intro d
    induction d with
    | @terminal X a hrule =>
        rcases hrule with ⟨hterm, htype, hkeep⟩
        rcases X with ⟨A, mu⟩
        change obsValue Obs [a] = mu at htype
        subst mu
        exact KeptDerives.terminal hterm hkeep
    | @binary X Y Z x y hrule left right ihLeft ihRight =>
        rcases hrule with ⟨hbin, htype, hkeep⟩
        rcases X with ⟨A, rho⟩
        rcases Y with ⟨B, mu⟩
        rcases Z with ⟨C, nu⟩
        change Obs.mul mu nu = rho at htype
        subst rho
        exact KeptDerives.binary hbin hkeep ihLeft ihRight
  · intro d
    induction d with
    | @terminal A a hrule hkeep =>
        apply UntypedDerives.terminal
        exact ⟨hrule, rfl, hkeep⟩
    | @binary A B C mu nu x y hrule hkeep left right ihLeft ihRight =>
        refine UntypedDerives.binary
          (A := { label := A, yieldType := Obs.mul mu nu })
          (B := { label := B, yieldType := mu })
          (C := { label := C, yieldType := nu }) ?_ ihLeft ihRight
        exact ⟨hrule, rfl, hkeep⟩

/-- The start language of the constructed ordinary grammar is exactly the
reduced typed-refinement language. -/
theorem clarkTyped_start_language_eq_trimmed_v49
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    UntypedStartLanguage
        (ClarkTypedTerminalV49 Obs terminal binary start)
        (ClarkTypedBinaryV49 Obs terminal binary start)
        (ClarkTypedStartV49 Obs terminal binary start)
        epsilonStart =
      TrimmedTypedStartLanguage Obs terminal binary start epsilonStart := by
  ext w
  constructor
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨X, hStart, hDeriv⟩
      exact Or.inr ⟨X.label, X.yieldType, hStart.1,
        (clarkTyped_derives_iff_kept_v49
          Obs terminal binary start X w).mp hDeriv⟩
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨A, mu, hStart, hDeriv⟩
      let X : TypedNT N Obs := { label := A, yieldType := mu }
      have hKeep : TypedKept Obs terminal binary start X :=
        keptDerives_root_kept Obs terminal binary start hDeriv
      exact Or.inr ⟨X, ⟨hStart, hKeep⟩,
        (clarkTyped_derives_iff_kept_v49
          Obs terminal binary start X w).mpr hDeriv⟩

/-- The constructed ordinary grammar generates exactly the original target. -/
theorem clarkTyped_start_language_eq_target_v49
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    UntypedStartLanguage
        (ClarkTypedTerminalV49 Obs terminal binary start)
        (ClarkTypedBinaryV49 Obs terminal binary start)
        (ClarkTypedStartV49 Obs terminal binary start)
        epsilonStart =
      UntypedStartLanguage terminal binary start epsilonStart := by
  calc
    UntypedStartLanguage
        (ClarkTypedTerminalV49 Obs terminal binary start)
        (ClarkTypedBinaryV49 Obs terminal binary start)
        (ClarkTypedStartV49 Obs terminal binary start)
        epsilonStart =
      TrimmedTypedStartLanguage Obs terminal binary start epsilonStart :=
        clarkTyped_start_language_eq_trimmed_v49
          Obs terminal binary start epsilonStart
    _ = UntypedStartLanguage terminal binary start epsilonStart := by
      ext w
      exact typed_refinement_language_iff
        Obs terminal binary start epsilonStart w

/-- Terminal language of one nonterminal in an ordinary SSBNF presentation. -/
def SSBNFNonterminalLanguageV49
    {Q : Type v} {Sigma : Type u}
    (terminal : TerminalRules Q Sigma) (binary : BinaryRules Q)
    (A : Q) : Language Sigma :=
  fun w => UntypedDerives terminal binary A w

/-- A finite SSBNF presentation is congruential for `L` when it generates `L`
and every nonterminal language is contained in one syntactic congruence class
of `L`. -/
structure CongruentialSSBNFPresentationV49
    {Sigma : Type u} (L : Language Sigma) where
  Q : Type v
  finiteQ : Finite Q
  terminal : TerminalRules Q Sigma
  binary : BinaryRules Q
  start : StartRules Q
  epsilonStart : Prop
  languageEq : UntypedStartLanguage terminal binary start epsilonStart = L
  homogeneous : ∀ A : Q,
    SyntacticallyHomogeneousV49 L
      (SSBNFNonterminalLanguageV49 terminal binary A)

/-- Language-family packaging of Clark-style congruential SSBNF presentations. -/
def CongruentialLanguageV49
    {Sigma : Type u} (L : Language Sigma) : Prop :=
  Nonempty (CongruentialSSBNFPresentationV49.{u, v} L)

/-- The retained typed construction is an actual finite congruential SSBNF
presentation of every fixed-`h` substitutable CFL already given in SSBNF form. -/
theorem clark_congruential_presentation_v49
    {N : Type v} {Sigma : Type u}
    [Finite N] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    CongruentialLanguageV49
      (UntypedStartLanguage terminal binary start epsilonStart) := by
  let encode : TypedNT N Obs → N × Obs.M :=
    fun X => (X.label, X.yieldType)
  have hEncode : Function.Injective encode := by
    intro X Y hXY
    rcases X with ⟨xl, xt⟩
    rcases Y with ⟨yl, yt⟩
    change (xl, xt) = (yl, yt) at hXY
    have hl : xl = yl := congrArg Prod.fst hXY
    have ht : xt = yt := congrArg Prod.snd hXY
    subst yl
    subst yt
    rfl
  letI : Finite (TypedNT N Obs) := Finite.of_injective encode hEncode
  refine ⟨{
    Q := TypedNT N Obs
    finiteQ := inferInstance
    terminal := ClarkTypedTerminalV49 Obs terminal binary start
    binary := ClarkTypedBinaryV49 Obs terminal binary start
    start := ClarkTypedStartV49 Obs terminal binary start
    epsilonStart := epsilonStart
    languageEq := clarkTyped_start_language_eq_target_v49
      Obs terminal binary start epsilonStart
    homogeneous := ?_ }⟩
  intro X
  by_cases hX : TypedKept Obs terminal binary start X
  · let KX : KeptState Obs terminal binary start := ⟨X, hX⟩
    intro x hx y hy
    have hHom := keptStateLanguage_syntacticallyHomogeneous_v49
      Obs terminal binary start epsilonStart hSub KX
    apply hHom
    · exact (clarkTyped_derives_iff_kept_v49
        Obs terminal binary start X x).mp hx
    · exact (clarkTyped_derives_iff_kept_v49
        Obs terminal binary start X y).mp hy
  · intro x hx
    have hDeriv := (clarkTyped_derives_iff_kept_v49
      Obs terminal binary start X x).mp hx
    exact (hX (keptDerives_root_kept
      Obs terminal binary start hDeriv)).elim

/-- Manuscript-facing inclusion theorem in actual grammar-presentation form. -/
theorem proposition_clark_congruential_inclusion_v49
    {N : Type v} {Sigma : Type u}
    [Finite N] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop)
    (hSub : HSubstitutable Obs
      (UntypedStartLanguage terminal binary start epsilonStart)) :
    CongruentialLanguageV49
      (UntypedStartLanguage terminal binary start epsilonStart) :=
  clark_congruential_presentation_v49
    Obs terminal binary start epsilonStart hSub

end FixedHCFGv44
end LeanCfgProject
