import LeanCfgProject.TCS1.WitnessSetConstruction
import LeanCfgProject.TCS1.ReducedTypedRuleBridge

/-!
# TCS #1 v68: cardinality of the canonical witness set

The fixed-window size theorem counts four witness families:

* one anchor for each active typed nonterminal;
* one witness for each active typed terminal production;
* one witness for each active typed binary production; and
* at most one epsilon witness.

This file connects that paper count to the actual
`canonicalWitnessFinset` used by the reconstruction development.  Possible
collisions between witness words only decrease the cardinality.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section CanonicalWitnessCounting

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- Active typed terminal productions, counted once each. -/
abbrev ActiveTypedTerminalIndex
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (Active : N × M → Prop) :=
  {p : N × α //
    terminalRule p.1 p.2 ∧
      Active (p.1, H.h [p.2])}

/-- Active typed binary productions, counted once for each pair of child types. -/
abbrev ActiveTypedBinaryIndex
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop) :=
  {p : (N × N × N) × (M × M) //
    binaryRule p.1.1 p.1.2.1 p.1.2.2 ∧
      Active (p.1.1, p.2.1 * p.2.2) ∧
      Active (p.1.2.1, p.2.1) ∧
      Active (p.1.2.2, p.2.2)}

/-- One finite indexing type covering all four canonical witness families. -/
abbrev CanonicalWitnessIndex
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop) :=
  Sum
    (ActiveTypedSymbol Active)
    (Sum
      (ActiveTypedTerminalIndex H terminalRule Active)
      (Sum
        (ActiveTypedBinaryIndex binaryRule Active)
        Unit))

/-- Word represented by one witness-family index. -/
def canonicalWitnessIndexWord
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active) :
    CanonicalWitnessIndex H terminalRule binaryRule Active →
      Word α
  | Sum.inl X =>
      C.left X.1 ++ C.omega X.1 ++ C.right X.1
  | Sum.inr (Sum.inl p) =>
      C.left (p.1.1, H.h [p.1.2]) ++
        [p.1.2] ++
        C.right (p.1.1, H.h [p.1.2])
  | Sum.inr (Sum.inr (Sum.inl p)) =>
      C.left (p.1.1.1, p.1.2.1 * p.1.2.2) ++
        C.omega (p.1.1.2.1, p.1.2.1) ++
        C.omega (p.1.1.2.2, p.1.2.2) ++
        C.right (p.1.1.1, p.1.2.1 * p.1.2.2)
  | Sum.inr (Sum.inr (Sum.inr _)) =>
      []

/--
Every actual canonical witness word is the image of one family index.
The Unit summand harmlessly covers epsilon even when epsilon is absent.
-/
theorem canonicalWitnessFinset_card_le_index
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    [Fintype (ActiveTypedSymbol Active)]
    [Fintype (ActiveTypedTerminalIndex H terminalRule Active)]
    [Fintype (ActiveTypedBinaryIndex binaryRule Active)]
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active) :
    (canonicalWitnessFinset
      H terminalRule binaryRule startRule epsilonStart Active C).card
      ≤
    Fintype.card
      (CanonicalWitnessIndex
        H terminalRule binaryRule Active) := by
  classical
  let f :=
    canonicalWitnessIndexWord
      H terminalRule binaryRule startRule epsilonStart Active C
  let cover :
      Finset (Word α) :=
    Finset.univ.image f

  have hsub :
      canonicalWitnessFinset
          H terminalRule binaryRule startRule epsilonStart Active C
        ⊆ cover := by
    intro word hword
    have hw :
        word ∈
          CanonicalWitnessWords
            H terminalRule binaryRule startRule epsilonStart Active C :=
      (mem_canonicalWitnessFinset_iff
        H terminalRule binaryRule startRule epsilonStart Active C word).1
        hword
    rcases hw with
      ⟨X, hX, rfl⟩
      | ⟨A, a, hterm, hactive, rfl⟩
      | ⟨A, B, Cn, μ, ν, hbin, hA, hB, hC, rfl⟩
      | ⟨heps, rfl⟩
    · apply Finset.mem_image.mpr
      refine
        ⟨Sum.inl (⟨X, hX⟩ : ActiveTypedSymbol Active),
          Finset.mem_univ _, ?_⟩
      rfl
    · apply Finset.mem_image.mpr
      refine
        ⟨Sum.inr
            (Sum.inl
              (⟨(A, a), ⟨hterm, hactive⟩⟩ :
                ActiveTypedTerminalIndex H terminalRule Active)),
          Finset.mem_univ _, ?_⟩
      rfl
    · apply Finset.mem_image.mpr
      refine
        ⟨Sum.inr
            (Sum.inr
              (Sum.inl
                (⟨((A, (B, Cn)), (μ, ν)),
                    ⟨hbin, hA, hB, hC⟩⟩ :
                  ActiveTypedBinaryIndex binaryRule Active))),
          Finset.mem_univ _, ?_⟩
      rfl
    · apply Finset.mem_image.mpr
      refine
        ⟨Sum.inr (Sum.inr (Sum.inr Unit.unit)),
          Finset.mem_univ _, ?_⟩
      rfl

  have hcardCover :
      cover.card ≤
        Fintype.card
          (CanonicalWitnessIndex
            H terminalRule binaryRule Active) := by
    dsimp [cover]
    simpa using
      (Finset.card_image_le
        (s :=
          (Finset.univ :
            Finset
              (CanonicalWitnessIndex
                H terminalRule binaryRule Active)))
        (f := f))

  exact
    le_trans
      (Finset.card_le_card hsub)
      hcardCover

/-- Paper-facing four-family cardinality bound. -/
theorem canonicalWitnessFinset_card_le_families
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    [Fintype (ActiveTypedSymbol Active)]
    [Fintype (ActiveTypedTerminalIndex H terminalRule Active)]
    [Fintype (ActiveTypedBinaryIndex binaryRule Active)]
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active) :
    (canonicalWitnessFinset
      H terminalRule binaryRule startRule epsilonStart Active C).card
      ≤
    Fintype.card (ActiveTypedSymbol Active) +
      Fintype.card
        (ActiveTypedTerminalIndex H terminalRule Active) +
      Fintype.card
        (ActiveTypedBinaryIndex binaryRule Active) +
      1 := by
  have h :=
    canonicalWitnessFinset_card_le_index
      H terminalRule binaryRule startRule epsilonStart Active C
  simp only [CanonicalWitnessIndex, Fintype.card_sum,
    Fintype.card_unit] at h
  omega

end CanonicalWitnessCounting

end TCS1
end LeanCfgProject
