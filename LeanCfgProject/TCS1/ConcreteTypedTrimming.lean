import LeanCfgProject.TCS1.SuccessfulTypedTrimClosureBridge
import LeanCfgProject.TCS1.ActiveTypedReachabilityBridge

/-!
# TCS #1 v68: concrete productive/reachable trimming of the typed refinement

The manuscript trims the full yield-typed refinement by productivity and then
by reachability from a non-start child of the start symbol.  This file gives a
direct semantic model of exactly that operation.

A typed symbol is retained when it is reachable through binary child edges in
the productive typed grammar.  The start case therefore requires a successful
typed yield, and every binary reachability step requires successful yields for
both children.

From this concrete definition we prove the two representation-level facts
needed by Lemmas 7.1 and 7.2:

* every successful full typed derivation rooted at a retained symbol restricts
  to the reduced typed refinement; and
* every retained typed symbol has ordinary active-symbol reachability, hence an
  explicit reaching spine once canonical productive yields are supplied.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section ConcreteTypedTrimming

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- A typed symbol has at least one successful terminal yield. -/
def TypedProductive
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (X : N × M) : Prop :=
  ∃ word : Word α,
    TypedDerives H terminalRule binaryRule X word

/--
Reachability inside the productive typed grammar.

A binary child edge may be followed only when both children are productive.
Thus every symbol occurring on a reachability proof is useful in the standard
productive-then-reachable sense.
-/
inductive ProductiveTypedReachable
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    N × M → Prop
  | start
      {A : N} {μ : M}
      (hstart : startRule A)
      (hprod :
        TypedProductive
          H terminalRule binaryRule (A, μ)) :
      ProductiveTypedReachable
        H terminalRule binaryRule startRule (A, μ)
  | left
      {A B C : N} {μ ν : M}
      (hparent :
        ProductiveTypedReachable
          H terminalRule binaryRule startRule
          (A, μ * ν))
      (hbin : binaryRule A B C)
      (hprodB :
        TypedProductive
          H terminalRule binaryRule (B, μ))
      (hprodC :
        TypedProductive
          H terminalRule binaryRule (C, ν)) :
      ProductiveTypedReachable
        H terminalRule binaryRule startRule (B, μ)
  | right
      {A B C : N} {μ ν : M}
      (hparent :
        ProductiveTypedReachable
          H terminalRule binaryRule startRule
          (A, μ * ν))
      (hbin : binaryRule A B C)
      (hprodB :
        TypedProductive
          H terminalRule binaryRule (B, μ))
      (hprodC :
        TypedProductive
          H terminalRule binaryRule (C, ν)) :
      ProductiveTypedReachable
        H terminalRule binaryRule startRule (C, ν)

/-- Concrete active predicate for the productive/reachable typed trim. -/
abbrev ConcreteTypedActive
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :=
  ProductiveTypedReachable
    H terminalRule binaryRule startRule

/-- Every concretely retained typed symbol is productive. -/
theorem concreteTypedActive_productive
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    {X : N × M}
    (hX :
      ConcreteTypedActive
        H terminalRule binaryRule startRule X) :
    TypedProductive
      H terminalRule binaryRule X := by
  induction hX with
  | start hstart hprod =>
      exact hprod
  | left hparent hbin hprodB hprodC ih =>
      exact hprodB
  | right hparent hbin hprodB hprodC ih =>
      exact hprodC

/--
The concrete productive/reachable trim is locally downward closed along every
binary node of a successful typed derivation.
-/
theorem concreteTypedActive_localClosure
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    SuccessfulTypedTrimLocalClosure
      H terminalRule binaryRule
      (ConcreteTypedActive
        H terminalRule binaryRule startRule) where
  binary_children := by
    intro A B C μ ν wB wC
      hbin hparent dB dC
    let hprodB :
        TypedProductive
          H terminalRule binaryRule (B, μ) :=
      ⟨wB, dB⟩
    let hprodC :
        TypedProductive
          H terminalRule binaryRule (C, ν) :=
      ⟨wC, dC⟩
    exact
      ⟨ProductiveTypedReachable.left
          hparent hbin hprodB hprodC,
        ProductiveTypedReachable.right
          hparent hbin hprodB hprodC⟩

/--
Hence every successful typed derivation rooted at a concretely active symbol
survives the productive/reachable trim.
-/
theorem concreteTypedActive_trimClosure
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    SuccessfulTypedTrimClosure
      H terminalRule binaryRule
      (ConcreteTypedActive
        H terminalRule binaryRule startRule) := by
  exact
    successfulTypedTrimClosure_of_localClosure
      H terminalRule binaryRule
      (ConcreteTypedActive
        H terminalRule binaryRule startRule)
      (concreteTypedActive_localClosure
        H terminalRule binaryRule startRule)

/--
Concrete productive/reachable activity implies reachability in the active
typed child graph.
-/
theorem concreteTypedActive_reachable
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (X : N × M)
    (hX :
      ConcreteTypedActive
        H terminalRule binaryRule startRule X) :
    ActiveTypedReachable
      binaryRule startRule
      (ConcreteTypedActive
        H terminalRule binaryRule startRule)
      ⟨X, hX⟩ := by
  induction hX with
  | @start A μ hstart hprod =>
      exact
        ActiveTypedReachable.start hstart

  | @left A B C μ ν hparent hbin hprodB hprodC ih =>
      let hB :
          ConcreteTypedActive
            H terminalRule binaryRule startRule (B, μ) :=
        ProductiveTypedReachable.left
          hparent hbin hprodB hprodC
      let hC :
          ConcreteTypedActive
            H terminalRule binaryRule startRule (C, ν) :=
        ProductiveTypedReachable.right
          hparent hbin hprodB hprodC
      let parent :
          ActiveTypedSymbol
            (ConcreteTypedActive
              H terminalRule binaryRule startRule) :=
        ⟨(A, μ * ν), hparent⟩
      let leftChild :
          ActiveTypedSymbol
            (ConcreteTypedActive
              H terminalRule binaryRule startRule) :=
        ⟨(B, μ), hB⟩
      let rightChild :
          ActiveTypedSymbol
            (ConcreteTypedActive
              H terminalRule binaryRule startRule) :=
        ⟨(C, ν), hC⟩
      have hrule :
          ActiveTypedBinaryRule binaryRule
            (ConcreteTypedActive
              H terminalRule binaryRule startRule)
            parent leftChild rightChild :=
        ActiveTypedBinaryRule.intro
          hbin hparent hB hC
      have ih' :
          ActiveTypedReachable
            binaryRule startRule
            (ConcreteTypedActive
              H terminalRule binaryRule startRule)
            parent := by
        simpa [parent] using ih
      have hout :=
        ActiveTypedReachable.left ih' hrule
      simpa [leftChild, hB] using hout

  | @right A B C μ ν hparent hbin hprodB hprodC ih =>
      let hB :
          ConcreteTypedActive
            H terminalRule binaryRule startRule (B, μ) :=
        ProductiveTypedReachable.left
          hparent hbin hprodB hprodC
      let hC :
          ConcreteTypedActive
            H terminalRule binaryRule startRule (C, ν) :=
        ProductiveTypedReachable.right
          hparent hbin hprodB hprodC
      let parent :
          ActiveTypedSymbol
            (ConcreteTypedActive
              H terminalRule binaryRule startRule) :=
        ⟨(A, μ * ν), hparent⟩
      let leftChild :
          ActiveTypedSymbol
            (ConcreteTypedActive
              H terminalRule binaryRule startRule) :=
        ⟨(B, μ), hB⟩
      let rightChild :
          ActiveTypedSymbol
            (ConcreteTypedActive
              H terminalRule binaryRule startRule) :=
        ⟨(C, ν), hC⟩
      have hrule :
          ActiveTypedBinaryRule binaryRule
            (ConcreteTypedActive
              H terminalRule binaryRule startRule)
            parent leftChild rightChild :=
        ActiveTypedBinaryRule.intro
          hbin hparent hB hC
      have ih' :
          ActiveTypedReachable
            binaryRule startRule
            (ConcreteTypedActive
              H terminalRule binaryRule startRule)
            parent := by
        simpa [parent] using ih
      have hout :=
        ActiveTypedReachable.right ih' hrule
      simpa [rightChild, hC] using hout

/-- Every concretely retained typed symbol is active-graph reachable. -/
theorem concreteTypedActive_all_reachable
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    ∀ X :
      ActiveTypedSymbol
        (ConcreteTypedActive
          H terminalRule binaryRule startRule),
      ActiveTypedReachable
        binaryRule startRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule)
        X := by
  intro X
  exact
    concreteTypedActive_reachable
      H terminalRule binaryRule startRule
      X.1 X.2

/--
Canonical productive yields turn the concrete active reachability relation
into the structural reaching-spine certificate used in Lemma 7.2.
-/
theorem concreteTypedActive_structuralReachability
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (choices :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule)) :
    ActiveTypedStructuralReachability
      H terminalRule binaryRule startRule
      (ConcreteTypedActive
        H terminalRule binaryRule startRule) := by
  exact
    activeTypedStructuralReachability_of_reachable
      H terminalRule binaryRule startRule epsilonStart
      (ConcreteTypedActive
        H terminalRule binaryRule startRule)
      choices
      (concreteTypedActive_all_reachable
        H terminalRule binaryRule startRule)

/--
For the concrete productive/reachable trim, the representation-level trimming
and reachability obligations disappear completely.

Thus canonical minimality, the fixed-window summary contract, and the
underlying thickness witness bound imply the Lemma 7.2 common bound for every
actual canonical witness word.
-/
theorem concreteTypedActive_canonicalWitnessWords_length_le_fixedWindow
    [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    [Fintype
      (ActiveTypedSymbol
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    (choices :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule)
        choices)
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    {word : Word α}
    (hword :
      word ∈
        CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart
          (ConcreteTypedActive
            H terminalRule binaryRule startRule)
          choices) :
    word.length ≤
      fixedWindowWitnessLengthEnvelope
        (Fintype.card
          (ActiveTypedSymbol
            (ConcreteTypedActive
              H terminalRule binaryRule startRule)))
        (k + l) (Fintype.card N) τ := by
  classical
  letI : DecidableEq N := Classical.decEq N
  have trim :=
    concreteTypedActive_trimClosure
      H terminalRule binaryRule startRule
  have reach :=
    concreteTypedActive_structuralReachability
      H terminalRule binaryRule startRule epsilonStart
      choices
  exact
    canonicalWitnessWords_length_le_fixedWindow_of_structural_reachability
      (ConcreteTypedActive
        H terminalRule binaryRule startRule)
      H terminalRule binaryRule startRule epsilonStart
      choices minimal trim reach
      k l hrespect τ hshort hword

end ConcreteTypedTrimming

end TCS1
end LeanCfgProject
