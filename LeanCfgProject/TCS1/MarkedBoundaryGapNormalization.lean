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

The explicit `marks` parameter keeps the base independent of the spine
during induction; `hbaseMarks` identifies it with the number of marked leaves
carried by the base.
-/
theorem exists_attachGapHead
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset marks k : Nat)
    {A X : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (spine :
      GapReachingSpine terminalRule binaryRule
        offset marks k
        A X left right path siblings)
    (base :
      MarkedBoundaryBase terminalRule binaryRule X)
    (hbaseMarks :
      MarkedBoundaryBase.markedLeafCount base = marks)
    (hbase :
      MarkedBoundaryBaseAllOmissionsAtAux
        terminalRule binaryRule offset k base) :
    ∃ K : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedLeafCount K = marks
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
  induction spine with
  | hole =>
      refine
        ⟨MarkedBoundaryBase.toKernel base,
          ?_, ?_,
          MarkedBoundaryBase.toKernel_markedWord
            terminalRule binaryRule base,
          ?_⟩
      · rw [MarkedBoundaryBase.toKernel_markedLeafCount
          terminalRule binaryRule base]
        exact hbaseMarks
      · simpa using
          MarkedBoundaryBase.toKernel_omittedCount
            terminalRule binaryRule base
      · exact
          markedBoundaryBase_toKernel_preserves_gap
            terminalRule binaryRule offset k base hbase

  | @binaryLeft A B C X left right z path siblings
      hbin child sibling hgap ih =>
      obtain ⟨K, hmarks, homit, hword, hKgap⟩ :=
        ih base hbaseMarks hbase
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
        ih base hbaseMarks hbase
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

/--
Gap-aware normalized head/base decomposition.

The unary head has already been cycle-shortened to a repetition-free path.
Both the head and the base carry the same global central-gap invariant.
-/
structure GapNormalizedHeadData
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset k : Nat)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) where
  target : N
  left : Word α
  right : Word α
  path : List N
  siblings : List Nat
  base :
    MarkedBoundaryBase terminalRule binaryRule target
  spine :
    GapReachingSpine terminalRule binaryRule
      offset (MarkedBoundaryBase.markedLeafCount base) k
      A target left right path siblings
  path_nodup : path.Nodup
  marks_eq :
    MarkedBoundaryBase.markedLeafCount base =
      MarkedBoundaryKernel.markedLeafCount K
  word_eq :
    MarkedBoundaryBase.markedWord base =
      MarkedBoundaryKernel.markedWord K
  base_gap :
    MarkedBoundaryBaseAllOmissionsAtAux
      terminalRule binaryRule offset k base
  tail_bound :
    MarkedBoundaryBase.omittedBelow base ≤
      (2 * MarkedBoundaryKernel.markedLeafCount K - 2) *
        Fintype.card N

/-- A gap-aware normalized unary head contains at most |N| omissions. -/
theorem gapNormalizedHead_siblings_le_card
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset k : Nat)
    {A : N}
    {K : MarkedBoundaryKernel terminalRule binaryRule A}
    (D :
      GapNormalizedHeadData
        terminalRule binaryRule offset k K) :
    D.siblings.length ≤ Fintype.card N := by
  have hpath :
      D.path.length ≤ Fintype.card N :=
    dependency_path_vertices_le
      D.path D.path_nodup
  have hstep :
      D.siblings.length + 1 = D.path.length :=
    gapReachingSpine_siblings_length_add_one_eq_path
      terminalRule binaryRule
      offset
      (MarkedBoundaryBase.markedLeafCount D.base)
      k D.spine
  omega

/--
Attach gap-aware normalized head data.

The result simultaneously preserves the marked word, satisfies the manuscript
omitted-sibling bound, and retains the central-gap invariant.
-/
theorem gapNormalizedHead_attach_bound
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset k : Nat)
    {A : N}
    {K : MarkedBoundaryKernel terminalRule binaryRule A}
    (D :
      GapNormalizedHeadData
        terminalRule binaryRule offset k K) :
    ∃ K' : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedLeafCount K' =
        MarkedBoundaryKernel.markedLeafCount K
      ∧
      MarkedBoundaryKernel.markedWord K' =
        MarkedBoundaryKernel.markedWord K
      ∧
      MarkedBoundaryKernel.omittedCount K' ≤
        (2 * MarkedBoundaryKernel.markedLeafCount K - 1) *
          Fintype.card N
      ∧
      MarkedBoundaryKernel.AllOmissionsAtAux
        offset K' k := by
  obtain ⟨K', hmarks, homit, hword, hgap⟩ :=
    exists_attachGapHead
      terminalRule binaryRule
      offset
      (MarkedBoundaryBase.markedLeafCount D.base)
      k D.spine D.base rfl D.base_gap
  have hhead :
      D.siblings.length ≤ Fintype.card N :=
    gapNormalizedHead_siblings_le_card
      terminalRule binaryRule offset k D
  have hsum :
      D.siblings.length +
          MarkedBoundaryBase.omittedBelow D.base
        ≤
      Fintype.card N +
        (2 * MarkedBoundaryKernel.markedLeafCount K - 2) *
          Fintype.card N :=
    Nat.add_le_add hhead D.tail_bound
  have hpos :
      0 < MarkedBoundaryKernel.markedLeafCount K :=
    MarkedBoundaryKernel.markedLeafCount_pos
      terminalRule binaryRule K
  have hcoeff :
      1 + (2 * MarkedBoundaryKernel.markedLeafCount K - 2) =
        2 * MarkedBoundaryKernel.markedLeafCount K - 1 := by
    omega
  have hfactor :
      Fintype.card N +
          (2 * MarkedBoundaryKernel.markedLeafCount K - 2) *
            Fintype.card N
        =
      (2 * MarkedBoundaryKernel.markedLeafCount K - 1) *
        Fintype.card N := by
    calc
      Fintype.card N +
          (2 * MarkedBoundaryKernel.markedLeafCount K - 2) *
            Fintype.card N
          =
        (1 +
          (2 * MarkedBoundaryKernel.markedLeafCount K - 2)) *
            Fintype.card N := by
              simp [Nat.add_mul]
      _ =
        (2 * MarkedBoundaryKernel.markedLeafCount K - 1) *
          Fintype.card N := by
            rw [hcoeff]
  refine ⟨K', ?_, ?_, ?_, hgap⟩
  · rw [hmarks, D.marks_eq]
  · rw [hword, D.word_eq]
  · rw [homit]
    exact le_trans hsum (le_of_eq hfactor)

end MarkedBoundaryGapNormalization

end TCS1
end LeanCfgProject
