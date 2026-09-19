import LeanCfgProject.TCS1.MarkedBoundaryGapSemantic

/-!
# TCS #1 v68: gap-aware marked-boundary normalization

This module lifts the central-gap invariant from individual reaching spines to
the full marked-boundary normalization used in Lemma 7.1.

The first layer below handles a normalized unary head attached to a base.  It
records that:

* every omitted sibling on the head lies in the unique global gap k; and
* every omission already contained in the base lies in that same gap.

The later recursive layer will use this attachment theorem to cycle-shorten a
whole marked-boundary kernel without losing the first-k / last-l positional
invariant.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section MarkedBoundaryGapNormalization

variable {N : Type u}
variable {α : Type v}

/-- Central-gap invariant for the endpoint base of a unary head. -/
def MarkedBoundaryBaseAllOmissionsAtAux
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset k : Nat) :
    {A : N} →
    MarkedBoundaryBase terminalRule binaryRule A →
    Prop
  | _, MarkedBoundaryBase.marked _ _ =>
      True
  | _, MarkedBoundaryBase.branch _ left right =>
      MarkedBoundaryKernel.AllOmissionsAtAux
          offset left k
        ∧
      MarkedBoundaryKernel.AllOmissionsAtAux
          (offset + MarkedBoundaryKernel.markedLeafCount left)
          right k

/-- Forgetting the base wrapper preserves its central-gap invariant. -/
theorem markedBoundaryBase_toKernel_preserves_gap
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset k : Nat)
    {A : N}
    (base :
      MarkedBoundaryBase terminalRule binaryRule A)
    (hgap :
      MarkedBoundaryBaseAllOmissionsAtAux
        terminalRule binaryRule offset k base) :
    MarkedBoundaryKernel.AllOmissionsAtAux
      offset (MarkedBoundaryBase.toKernel base) k := by
  cases base with
  | marked a hterm =>
      intro j hj
      simp [MarkedBoundaryBase.toKernel,
        MarkedBoundaryKernel.AllOmissionsAtAux,
        MarkedBoundaryKernel.omissionRanksAux] at hj
  | branch hbin left right =>
      exact
        (MarkedBoundaryKernel.allOmissionsAtAux_branch_iff
          hbin left right offset k).2 hgap

/--
Attach a gap-certified unary head above a gap-certified base.

Besides the ordinary count/word identities, the resulting marked-boundary
kernel keeps every omission in the same global gap k.
-/
theorem exists_attachGapHead
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset k : Nat)
    {A X : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (base :
      MarkedBoundaryBase terminalRule binaryRule X)
    (spine :
      GapReachingSpine terminalRule binaryRule
        offset (MarkedBoundaryBase.markedLeafCount base) k
        A X left right path siblings)
    (hbase :
      MarkedBoundaryBaseAllOmissionsAtAux
        terminalRule binaryRule offset k base) :
    ∃ K : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedLeafCount K =
        MarkedBoundaryBase.markedLeafCount base
      ∧
      MarkedBoundaryKernel.omittedCount K =
        siblings.length +
          MarkedBoundaryBase.omittedBelow base
      ∧
      MarkedBoundaryKernel.markedWord K =
        MarkedBoundaryBase.markedWord base
      ∧
      MarkedBoundaryKernel.AllOmissionsAtAux
        offset K k := by
  induction spine generalizing base with
  | hole =>
      refine
        ⟨MarkedBoundaryBase.toKernel base,
          MarkedBoundaryBase.toKernel_markedLeafCount
            terminalRule binaryRule base,
          ?_,
          MarkedBoundaryBase.toKernel_markedWord
            terminalRule binaryRule base,
          ?_⟩
      · simpa using
          MarkedBoundaryBase.toKernel_omittedCount
            terminalRule binaryRule base
      · exact
          markedBoundaryBase_toKernel_preserves_gap
            terminalRule binaryRule offset k base hbase

  | @binaryLeft A B C X left right z path siblings
      hbin child sibling hgap ih =>
      obtain ⟨K, hmarks, homit, hword, hKgap⟩ :=
        ih base hbase
      refine
        ⟨MarkedBoundaryKernel.unaryLeft
            hbin K z sibling,
          ?_, ?_, ?_, ?_⟩
      · simpa [MarkedBoundaryKernel.markedLeafCount]
          using hmarks
      · simp only [MarkedBoundaryKernel.omittedCount,
          List.length_cons]
        rw [homit]
        omega
      · simpa [MarkedBoundaryKernel.markedWord]
          using hword
      · apply
          (MarkedBoundaryKernel.allOmissionsAtAux_unaryLeft_iff
            hbin K z sibling offset k).2
        refine ⟨hKgap, ?_⟩
        rw [hmarks]
        exact hgap

  | @binaryRight A B C X left right y path siblings
      hbin sibling child hgap ih =>
      obtain ⟨K, hmarks, homit, hword, hKgap⟩ :=
        ih base hbase
      refine
        ⟨MarkedBoundaryKernel.unaryRight
            hbin y sibling K,
          ?_, ?_, ?_, ?_⟩
      · simpa [MarkedBoundaryKernel.markedLeafCount]
          using hmarks
      · simp only [MarkedBoundaryKernel.omittedCount,
          List.length_cons]
        rw [homit]
        omega
      · simpa [MarkedBoundaryKernel.markedWord]
          using hword
      · apply
          (MarkedBoundaryKernel.allOmissionsAtAux_unaryRight_iff
            hbin y sibling K offset k).2
        exact ⟨hgap, hKgap⟩

end MarkedBoundaryGapNormalization

end TCS1
end LeanCfgProject
