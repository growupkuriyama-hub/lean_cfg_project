import LeanCfgProject.TCS1.ReconstructionFactorSlotGrammar
import LeanCfgProject.TCS1.FiniteUnitReachability
import LeanCfgProject.TCS1.BinaryMembershipDecision
import LeanCfgProject.TCS1.ConservativeMembershipCost

/-!
# TCS #1 v79: executable factor-slot CYK reconstruction learner

The previous reconstruction-to-CYK bridge used the proof-carrying subtype of
observed paper-facing nonterminals and therefore chose its finite enumeration
classically.  This module replaces that last representation boundary by the
concrete two-cut occurrence space `ReconstructionFactorSlot K`.

The state type is computably finite.  R2/R3 are eliminated by the verified
finite unit-closure machinery, and the resulting terminal/binary grammar is
fed directly to the executable CYK chart.

Under decidable equality on the fixed finite monoid, the final Boolean
membership test below is an ordinary computable definition (not
`noncomputable`) and accepts exactly `BatchLanguage H K`.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ReconstructionFactorSlotCYK

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]

/-- Decidability of observed decoded factor slots. -/
instance instDecidableReconstructionFactorSlotObserved
    (K : Finset (Word α)) :
    DecidablePred (ReconstructionFactorSlotObserved K) := by
  intro A
  unfold ReconstructionFactorSlotObserved
  dsimp only [reconstructionFactorSlotSymbol]
  unfold Observed
  infer_instance

/-- The factor-slot terminal relation is decidable. -/
instance instDecidableReconstructionFactorSlotTerminalRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    DecidableRel
      (reconstructionFactorSlotGrammar H K).terminalRule := by
  intro A a
  change
    Decidable
      (ReconstructionFactorSlotObserved K A ∧
        (reconstructionFactorSlotSymbol A).factor = [a])
  infer_instance

/-- The factor-slot binary relation is decidable. -/
instance instDecidableReconstructionFactorSlotBinaryRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ∀ A B : ReconstructionFactorSlot K,
      DecidablePred
        ((reconstructionFactorSlotGrammar H K).binaryRule A B) := by
  intro A B C
  change Decidable
    (ReconstructionFactorSlotObserved K A ∧
     ReconstructionFactorSlotObserved K B ∧
     ReconstructionFactorSlotObserved K C ∧
     (reconstructionFactorSlotSymbol A).factor =
       (reconstructionFactorSlotSymbol B).factor ++
         (reconstructionFactorSlotSymbol C).factor ∧
     (reconstructionFactorSlotSymbol B).leftContext =
       (reconstructionFactorSlotSymbol A).leftContext ∧
     (reconstructionFactorSlotSymbol B).rightContext =
       (reconstructionFactorSlotSymbol C).factor ++
         (reconstructionFactorSlotSymbol A).rightContext ∧
     (reconstructionFactorSlotSymbol C).leftContext =
       (reconstructionFactorSlotSymbol A).leftContext ++
         (reconstructionFactorSlotSymbol B).factor ∧
     (reconstructionFactorSlotSymbol C).rightContext =
       (reconstructionFactorSlotSymbol A).rightContext)
  infer_instance

/-- The factor-slot unary relation R2/R3 is decidable. -/
instance instDecidableReconstructionFactorSlotUnitRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    DecidableRel
      (reconstructionFactorSlotGrammar H K).unitRule := by
  intro A B
  change Decidable
    (ReconstructionFactorSlotObserved K A ∧
     ReconstructionFactorSlotObserved K B ∧
     ((reconstructionFactorSlotSymbol A).factor =
        (reconstructionFactorSlotSymbol B).factor ∨
      ((reconstructionFactorSlotSymbol A).leftContext =
          (reconstructionFactorSlotSymbol B).leftContext ∧
       (reconstructionFactorSlotSymbol A).rightContext =
          (reconstructionFactorSlotSymbol B).rightContext ∧
       H.h (reconstructionFactorSlotSymbol A).factor =
          H.h (reconstructionFactorSlotSymbol B).factor)))
  infer_instance

/-- The factor-slot start-child relation is decidable. -/
instance instDecidableReconstructionFactorSlotStartRule
    (K : Finset (Word α)) :
    DecidablePred (reconstructionFactorSlotStartRule K) := by
  intro A
  unfold reconstructionFactorSlotStartRule
  infer_instance

/-- Terminal relation after executable finite unit closure. -/
def reconstructionFactorSlotUnitFreeTerminalRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ReconstructionFactorSlot K → α → Prop :=
  UnitFreeTerminalRule
    (reconstructionFactorSlotGrammar H K)

/-- Binary relation after executable finite unit closure. -/
def reconstructionFactorSlotUnitFreeBinaryRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ReconstructionFactorSlot K →
      ReconstructionFactorSlot K →
      ReconstructionFactorSlot K → Prop :=
  UnitFreeBinaryRule
    (reconstructionFactorSlotGrammar H K)

/--
The finite unit-free terminal relation is decidable through
`instDecidableUnitReachFinite`.
-/
instance instDecidableReconstructionFactorSlotUnitFreeTerminalRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    DecidableRel
      (reconstructionFactorSlotUnitFreeTerminalRule H K) := by
  intro A a
  unfold reconstructionFactorSlotUnitFreeTerminalRule
  unfold UnitFreeTerminalRule
  infer_instance

/-- The finite unit-free binary relation is decidable by the same closure. -/
instance instDecidableReconstructionFactorSlotUnitFreeBinaryRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ∀ A B : ReconstructionFactorSlot K,
      DecidablePred
        (reconstructionFactorSlotUnitFreeBinaryRule H K A B) := by
  intro A B C
  unfold reconstructionFactorSlotUnitFreeBinaryRule
  unfold UnitFreeBinaryRule
  infer_instance

/-- Terminal/binary derivations are literally unit-free derivations. -/
theorem factorSlotUntyped_to_unitFree
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {A : ReconstructionFactorSlot K}
    {w : Word α}
    (d :
      UntypedDerives
        (reconstructionFactorSlotUnitFreeTerminalRule H K)
        (reconstructionFactorSlotUnitFreeBinaryRule H K)
        A w) :
    UnitFreeDerives
      (reconstructionFactorSlotGrammar H K)
      A w := by
  induction d with
  | terminal h =>
      exact UnitFreeDerives.terminal h
  | binary h _ _ ihB ihC =>
      exact UnitFreeDerives.binary h ihB ihC

/-- Unit-free derivations erase to the CYK terminal/binary derivation type. -/
theorem factorSlotUnitFree_to_untyped
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {A : ReconstructionFactorSlot K}
    {w : Word α}
    (d :
      UnitFreeDerives
        (reconstructionFactorSlotGrammar H K)
        A w) :
    UntypedDerives
      (reconstructionFactorSlotUnitFreeTerminalRule H K)
      (reconstructionFactorSlotUnitFreeBinaryRule H K)
      A w := by
  induction d with
  | terminal h =>
      exact UntypedDerives.terminal h
  | binary h _ _ ihB ihC =>
      exact UntypedDerives.binary h ihB ihC

/--
Exact start-language identity for the fully finite, unit-free factor-slot
presentation.
-/
theorem reconstructionFactorSlotUnitFree_untypedStartLanguage_eq_batchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    UntypedStartLanguage
        (reconstructionFactorSlotUnitFreeTerminalRule H K)
        (reconstructionFactorSlotUnitFreeBinaryRule H K)
        (reconstructionFactorSlotStartRule K)
        (([] : Word α) ∈ K)
      =
    BatchLanguage H K := by
  apply Set.ext
  intro w
  constructor
  · intro h
    cases h with
    | @nonempty A _ hstart hder =>
        rcases hstart with ⟨hobs, hleft, hright⟩
        change
          Observed K
            (reconstructionFactorSlotSymbol A).factor
            (reconstructionFactorSlotSymbol A).leftContext
            (reconstructionFactorSlotSymbol A).rightContext
          at hobs
        have dUnit :
            UnitFreeDerives
              (reconstructionFactorSlotGrammar H K)
              A w :=
          factorSlotUntyped_to_unitFree H K hder
        have dEps :
            EpsilonFreeDerives
              (reconstructionFactorSlotGrammar H K)
              A w :=
          unitFreeDerives_to_epsilonFree
            (reconstructionFactorSlotGrammar H K)
            dUnit
        have dBin :
            BinaryNullableDerives
              (reconstructionFactorSlotGrammar H K)
              A w :=
          epsilonFreeDerives_to_binaryNullable
            (reconstructionFactorSlotGrammar H K)
            dEps
        have hhyp :=
          factorSlotGrammar_to_hypDerives H K dBin
        have hs :
            (reconstructionFactorSlotSymbol A).factor ∈ K := by
          simpa [hleft, hright] using hobs.2
        exact
          BatchDerives.nonempty
            hs hobs.1
            (by simpa [hleft, hright] using hhyp)
    | epsilon heps =>
        exact BatchDerives.epsilon heps
  · intro h
    cases h with
    | @nonempty s _ hs hsne hder =>
        have hobs : Observed K s [] [] := by
          exact ⟨hsne, by simpa using hs⟩
        let A : ReconstructionFactorSlot K :=
          observedReconstructionFactorSlot K hobs
        have dBin :
            BinaryNullableDerives
              (reconstructionFactorSlotGrammar H K)
              A w := by
          simpa [A] using
            (hypDerives_to_factorSlotGrammar H K hder)
        have hne : w ≠ [] :=
          hypDerives_nonempty H K hder
        have dEps :
            EpsilonFreeDerives
              (reconstructionFactorSlotGrammar H K)
              A w :=
          binaryNullableDerives_to_epsilonFree
            (reconstructionFactorSlotGrammar H K)
            dBin hne
        have dUnit :
            UnitFreeDerives
              (reconstructionFactorSlotGrammar H K)
              A w :=
          epsilonFreeDerives_to_unitFree
            (reconstructionFactorSlotGrammar H K)
            dEps
        have hstart :
            reconstructionFactorSlotStartRule K A := by
          refine
            ⟨observedReconstructionFactorSlot_isObserved K hobs, ?_, ?_⟩
          · have hdecode :=
              reconstructionFactorSlotNonterminal_observed K hobs
            exact congrArg ReconstructionNonterminal.leftContext hdecode
          · have hdecode :=
              reconstructionFactorSlotNonterminal_observed K hobs
            exact congrArg ReconstructionNonterminal.rightContext hdecode
        exact
          UntypedStartDerives.nonempty
            hstart
            (factorSlotUnitFree_to_untyped H K dUnit)
    | epsilon heps =>
        exact UntypedStartDerives.epsilon heps

/--
Fully executable CYK Boolean test for the actual reconstructed hypothesis.
No `noncomputable` wrapper remains.
-/
def reconstructionFactorSlotCYKMember
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (w : Word α) : Bool :=
  cykStartMember
    (reconstructionFactorSlotUnitFreeTerminalRule H K)
    (reconstructionFactorSlotUnitFreeBinaryRule H K)
    (reconstructionFactorSlotStartRule K)
    (([] : Word α) ∈ K)
    w

/-- Exact correctness of the fully executable reconstructed-hypothesis parser. -/
theorem reconstructionFactorSlotCYKMember_eq_true_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (w : Word α) :
    reconstructionFactorSlotCYKMember H K w = true
      ↔
    w ∈ BatchLanguage H K := by
  rw [reconstructionFactorSlotCYKMember]
  rw [cykStartMember_eq_true_iff]
  rw [reconstructionFactorSlotUnitFree_untypedStartLanguage_eq_batchLanguage]

/--
The exact finite state count consumed by this executable parser is the
two-cut factor-slot cardinality already used in the conservative cost bridge.
-/
theorem reconstructionFactorSlotCYK_conservativeComparison_le_prefix
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    cykNaiveComparisonEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (concreteConservativeHypothesis H datum n)))
        (datum (n + 1)).length
      ≤
    conservativeCYKPrefixEnvelope
      (positiveDataPrefixNorm datum (n + 1)) :=
  concreteConservative_occurrenceIndexed_membershipComparison_le_prefix
    H datum n

/-- All-source unit-closure precomputation has the explicit quartic scan count. -/
def reconstructionUnitClosureTableScanEnvelope
    (stateCount : Nat) : Nat :=
  stateCount * finiteUnitReachScanEnvelope stateCount

theorem reconstructionUnitClosureTableScanEnvelope_eq
    (m : Nat) :
    reconstructionUnitClosureTableScanEnvelope m = m ^ 4 := by
  unfold reconstructionUnitClosureTableScanEnvelope
  rw [finiteUnitReachScanEnvelope_eq]
  ring

end ReconstructionFactorSlotCYK

end TCS1
end LeanCfgProject
