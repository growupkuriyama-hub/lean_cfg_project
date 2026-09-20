import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage
import LeanCfgProject.TCS1.LinearTypedShapeBridge

/-!
# TCS #1: untyped productive/reachable trim for separated-start grammars

Proposition `linear-normal` states that the normalized grammar is reduced.
The specialized linear construction already preserves the source language and
has the required one-wrapper-child shape; this module formalizes the final
useless-symbol trim on the untyped separated-start presentation.

A retained non-start symbol is productive and is reachable from a start child
through binary child edges for which both children are productive.  This is
the ordinary productive-then-reachable trim specialized to terminal/binary
non-start grammars.

We prove:

* exact preservation of the separated-start language;
* every retained symbol is productive and graph-reachable, hence the output is
  reduced in the standard CFG sense; and
* the linear-spine wrapper shape is inherited by the trim.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section UntypedUsefulTrim

variable {N : Type u}
variable {α : Type v}

/-- A non-start symbol has some terminal yield. -/
def UntypedProductive
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (A : N) : Prop :=
  ∃ word : Word α,
    UntypedDerives terminalRule binaryRule A word

/--
Reachability inside the productive non-start grammar.

At a followed binary edge both children must be productive.  This is exactly
what is needed for every successful derivation rooted at a retained symbol to
survive the trim.
-/
inductive ProductiveUntypedReachable
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    N → Prop
  | start
      {A : N}
      (hstart : startRule A)
      (hprod :
        UntypedProductive terminalRule binaryRule A) :
      ProductiveUntypedReachable
        terminalRule binaryRule startRule A
  | left
      {A B C : N}
      (hparent :
        ProductiveUntypedReachable
          terminalRule binaryRule startRule A)
      (hbin : binaryRule A B C)
      (hprodB :
        UntypedProductive terminalRule binaryRule B)
      (hprodC :
        UntypedProductive terminalRule binaryRule C) :
      ProductiveUntypedReachable
        terminalRule binaryRule startRule B
  | right
      {A B C : N}
      (hparent :
        ProductiveUntypedReachable
          terminalRule binaryRule startRule A)
      (hbin : binaryRule A B C)
      (hprodB :
        UntypedProductive terminalRule binaryRule B)
      (hprodC :
        UntypedProductive terminalRule binaryRule C) :
      ProductiveUntypedReachable
        terminalRule binaryRule startRule C

/-- Every productively reachable symbol is productive. -/
theorem productiveUntypedReachable_productive
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    {A : N}
    (hA :
      ProductiveUntypedReachable
        terminalRule binaryRule startRule A) :
    UntypedProductive terminalRule binaryRule A := by
  induction hA with
  | start hstart hprod =>
      exact hprod
  | left hparent hbin hprodB hprodC ih =>
      exact hprodB
  | right hparent hbin hprodB hprodC ih =>
      exact hprodC

/-- Non-start state type of the final productive/reachable trim. -/
abbrev UntypedUsefulState
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :=
  {A : N //
    ProductiveUntypedReachable
      terminalRule binaryRule startRule A}

/-- Terminal rules restricted to useful states. -/
def untypedUsefulTerminalRule
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    UntypedUsefulState terminalRule binaryRule startRule →
      α → Prop :=
  fun A a => terminalRule A.1 a

/-- Binary rules restricted to useful states. -/
def untypedUsefulBinaryRule
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    UntypedUsefulState terminalRule binaryRule startRule →
    UntypedUsefulState terminalRule binaryRule startRule →
    UntypedUsefulState terminalRule binaryRule startRule →
    Prop :=
  fun A B C => binaryRule A.1 B.1 C.1

/-- Start-child relation restricted to useful states. -/
def untypedUsefulStartRule
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    UntypedUsefulState terminalRule binaryRule startRule →
      Prop :=
  fun A => startRule A.1

/--
Every full derivation rooted at a useful symbol restricts to the useful
subgrammar.
-/
theorem untypedDerives_to_useful
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    {A : N}
    {word : Word α}
    (hA :
      ProductiveUntypedReachable
        terminalRule binaryRule startRule A)
    (d :
      UntypedDerives
        terminalRule binaryRule A word) :
    UntypedDerives
      (untypedUsefulTerminalRule
        terminalRule binaryRule startRule)
      (untypedUsefulBinaryRule
        terminalRule binaryRule startRule)
      ⟨A, hA⟩ word := by
  induction d with
  | @terminal A a hterm =>
      exact UntypedDerives.terminal hterm
  | @binary A B C wB wC hbin dB dC ihB ihC =>
      let hprodB :
          UntypedProductive terminalRule binaryRule B :=
        ⟨wB, dB⟩
      let hprodC :
          UntypedProductive terminalRule binaryRule C :=
        ⟨wC, dC⟩
      let hB :
          ProductiveUntypedReachable
            terminalRule binaryRule startRule B :=
        ProductiveUntypedReachable.left
          hA hbin hprodB hprodC
      let hC :
          ProductiveUntypedReachable
            terminalRule binaryRule startRule C :=
        ProductiveUntypedReachable.right
          hA hbin hprodB hprodC
      have hbinUseful :
          untypedUsefulBinaryRule
            terminalRule binaryRule startRule
            ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ :=
        hbin
      exact
        UntypedDerives.binary
          hbinUseful
          (ihB hB)
          (ihC hC)

/-- Erasing useful-state certificates recovers a derivation in the source grammar. -/
theorem untypedUsefulDerives_erase
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    {A :
      UntypedUsefulState
        terminalRule binaryRule startRule}
    {word : Word α}
    (d :
      UntypedDerives
        (untypedUsefulTerminalRule
          terminalRule binaryRule startRule)
        (untypedUsefulBinaryRule
          terminalRule binaryRule startRule)
        A word) :
    UntypedDerives terminalRule binaryRule A.1 word := by
  induction d with
  | terminal hterm =>
      exact UntypedDerives.terminal hterm
  | binary hbin dB dC ihB ihC =>
      exact UntypedDerives.binary hbin ihB ihC

/-- Every source start derivation survives the useful-state trim. -/
theorem untypedStartDerives_to_useful
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    {word : Word α}
    (d :
      UntypedStartDerives
        terminalRule binaryRule startRule epsilonStart
        word) :
    UntypedStartDerives
      (untypedUsefulTerminalRule
        terminalRule binaryRule startRule)
      (untypedUsefulBinaryRule
        terminalRule binaryRule startRule)
      (untypedUsefulStartRule
        terminalRule binaryRule startRule)
      epsilonStart
      word := by
  cases d with
  | @nonempty A word hstart dA =>
      let hA :
          ProductiveUntypedReachable
            terminalRule binaryRule startRule A :=
        ProductiveUntypedReachable.start
          hstart ⟨word, dA⟩
      have hstartUseful :
          untypedUsefulStartRule
            terminalRule binaryRule startRule ⟨A, hA⟩ :=
        hstart
      exact
        UntypedStartDerives.nonempty
          hstartUseful
          (untypedDerives_to_useful
            terminalRule binaryRule startRule hA dA)
  | epsilon heps =>
      exact UntypedStartDerives.epsilon heps

/-- Every useful-state start derivation erases to a source start derivation. -/
theorem untypedUsefulStartDerives_erase
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    {word : Word α}
    (d :
      UntypedStartDerives
        (untypedUsefulTerminalRule
          terminalRule binaryRule startRule)
        (untypedUsefulBinaryRule
          terminalRule binaryRule startRule)
        (untypedUsefulStartRule
          terminalRule binaryRule startRule)
        epsilonStart
        word) :
    UntypedStartDerives
      terminalRule binaryRule startRule epsilonStart
      word := by
  cases d with
  | @nonempty A word hstart dA =>
      exact
        UntypedStartDerives.nonempty
          hstart
          (untypedUsefulDerives_erase
            terminalRule binaryRule startRule dA)
  | epsilon heps =>
      exact UntypedStartDerives.epsilon heps

/-- The final productive/reachable trim preserves the complete start language. -/
theorem untypedUsefulStartLanguage_eq
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop) :
    UntypedStartLanguage
        (untypedUsefulTerminalRule
          terminalRule binaryRule startRule)
        (untypedUsefulBinaryRule
          terminalRule binaryRule startRule)
        (untypedUsefulStartRule
          terminalRule binaryRule startRule)
        epsilonStart
      =
    UntypedStartLanguage
      terminalRule binaryRule startRule epsilonStart := by
  apply Set.ext
  intro word
  constructor
  · exact
      untypedUsefulStartDerives_erase
        terminalRule binaryRule startRule epsilonStart
  · exact
      untypedStartDerives_to_useful
        terminalRule binaryRule startRule epsilonStart

/-- Ordinary child-edge reachability from a separated start child. -/
inductive UntypedGraphReachable
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    N → Prop
  | start
      {A : N}
      (hstart : startRule A) :
      UntypedGraphReachable binaryRule startRule A
  | left
      {A B C : N}
      (hparent :
        UntypedGraphReachable binaryRule startRule A)
      (hbin : binaryRule A B C) :
      UntypedGraphReachable binaryRule startRule B
  | right
      {A B C : N}
      (hparent :
        UntypedGraphReachable binaryRule startRule A)
      (hbin : binaryRule A B C) :
      UntypedGraphReachable binaryRule startRule C

/--
Productive reachability yields ordinary reachability in the useful-state
grammar.
-/
theorem productiveUntypedReachable_to_usefulGraph
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    {A : N}
    (hA :
      ProductiveUntypedReachable
        terminalRule binaryRule startRule A) :
    UntypedGraphReachable
      (untypedUsefulBinaryRule
        terminalRule binaryRule startRule)
      (untypedUsefulStartRule
        terminalRule binaryRule startRule)
      ⟨A, hA⟩ := by
  induction hA with
  | @start A hstart hprod =>
      exact UntypedGraphReachable.start hstart
  | @left A B C hparent hbin hprodB hprodC ih =>
      let hB :
          ProductiveUntypedReachable
            terminalRule binaryRule startRule B :=
        ProductiveUntypedReachable.left
          hparent hbin hprodB hprodC
      let hC :
          ProductiveUntypedReachable
            terminalRule binaryRule startRule C :=
        ProductiveUntypedReachable.right
          hparent hbin hprodB hprodC
      have hrule :
          untypedUsefulBinaryRule
            terminalRule binaryRule startRule
            ⟨A, hparent⟩ ⟨B, hB⟩ ⟨C, hC⟩ :=
        hbin
      have hout :=
        UntypedGraphReachable.left ih hrule
      simpa [hB] using hout
  | @right A B C hparent hbin hprodB hprodC ih =>
      let hB :
          ProductiveUntypedReachable
            terminalRule binaryRule startRule B :=
        ProductiveUntypedReachable.left
          hparent hbin hprodB hprodC
      let hC :
          ProductiveUntypedReachable
            terminalRule binaryRule startRule C :=
        ProductiveUntypedReachable.right
          hparent hbin hprodB hprodC
      have hrule :
          untypedUsefulBinaryRule
            terminalRule binaryRule startRule
            ⟨A, hparent⟩ ⟨B, hB⟩ ⟨C, hC⟩ :=
        hbin
      have hout :=
        UntypedGraphReachable.right ih hrule
      simpa [hC] using hout

/--
Standard semantic reducedness for a separated-start terminal/binary grammar:
every non-start symbol is productive and reachable from a start child.
-/
structure UntypedReducedPresentation
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) : Prop where
  productive :
    ∀ A : N,
      UntypedProductive terminalRule binaryRule A
  reachable :
    ∀ A : N,
      UntypedGraphReachable binaryRule startRule A

/-- The useful-state grammar is reduced by construction. -/
theorem untypedUseful_reduced
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    UntypedReducedPresentation
      (untypedUsefulTerminalRule
        terminalRule binaryRule startRule)
      (untypedUsefulBinaryRule
        terminalRule binaryRule startRule)
      (untypedUsefulStartRule
        terminalRule binaryRule startRule) := by
  refine
    { productive := ?_
      reachable := ?_ }
  · intro A
    obtain ⟨word, d⟩ :=
      productiveUntypedReachable_productive
        terminalRule binaryRule startRule A.2
    exact
      ⟨word,
        untypedDerives_to_useful
          terminalRule binaryRule startRule A.2 d⟩
  · intro A
    exact
      productiveUntypedReachable_to_usefulGraph
        terminalRule binaryRule startRule A.2

/-- Wrapper predicate inherited by the useful-state subtype. -/
def untypedUsefulWrapper
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (Wrapper : N → Prop) :
    UntypedUsefulState terminalRule binaryRule startRule →
      Prop :=
  fun A => Wrapper A.1

/-- Productive/reachable trimming preserves the one-wrapper-child spine shape. -/
theorem untypedUseful_linearSpineShape
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (Wrapper : N → Prop)
    (shape :
      UntypedLinearSpineShape
        terminalRule binaryRule Wrapper) :
    UntypedLinearSpineShape
      (untypedUsefulTerminalRule
        terminalRule binaryRule startRule)
      (untypedUsefulBinaryRule
        terminalRule binaryRule startRule)
      (untypedUsefulWrapper
        terminalRule binaryRule startRule Wrapper) := by
  refine
    { wrapper_terminal := ?_
      wrapper_no_binary := ?_
      binary_children := ?_ }
  · intro A hwrap
    obtain ⟨a, hterm⟩ :=
      shape.wrapper_terminal A.1 hwrap
    exact ⟨a, hterm⟩
  · intro A B C hwrap hbin
    exact
      shape.wrapper_no_binary hwrap hbin
  · intro A B C hbin
    exact
      shape.binary_children hbin

noncomputable instance untypedUsefulStateFintype
    [Fintype N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    Fintype
      (UntypedUsefulState
        terminalRule binaryRule startRule) :=
  Fintype.ofFinite _

/-- Final trimming never increases the non-start state count. -/
theorem untypedUsefulState_card_le
    [Fintype N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :
    Fintype.card
        (UntypedUsefulState
          terminalRule binaryRule startRule)
      ≤
    Fintype.card N := by
  exact Fintype.card_subtype_le _

end UntypedUsefulTrim

end TCS1
end LeanCfgProject
