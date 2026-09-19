import LeanCfgProject.TCS1.MarkedBoundaryNormalization

/-!
# TCS #1 v68: central-gap preservation on shortened reaching spines

The long-word proof of Lemma 7.1 must preserve more than the number of marked
leaves: every omitted sibling subtree has to remain in the single middle gap
between the first k and last l marked terminals.

This file supplies that invariant for one maximal one-child chain.

For a reaching spine whose retained base contains r marked leaves, an omitted
right sibling (the retained child is left) lies after all r marked leaves,
while an omitted left sibling lies before all r marked leaves.  The list
`reachingSpineOmissionRanks` records these marked-leaf ranks.

The main theorem proves that the cycle-shortening normalization already used
for Lemma 7.1 preserves the property that every such rank is the same global
gap k.  Thus shortcutting repeated nonterminal labels cannot move an omitted
subtree across a marked boundary.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section MarkedBoundaryGapSemantic

variable {N : Type u}
variable {α : Type v}

/--
Marked-leaf ranks of omitted sibling subtrees along one reaching spine.

`offset` is the number of marked leaves lying globally before the retained
base, and `marks` is the number of marked leaves in that base.
-/
def reachingSpineOmissionRanks
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop}
    (offset marks : Nat) :
    {A X : N} →
    {left right : Word α} →
    {path : List N} →
    {siblings : List Nat} →
    ReachingSpine terminalRule binaryRule
      A X left right path siblings →
    List Nat
  | _, _, _, _, _, _, ReachingSpine.hole => []
  | _, _, _, _, _, _,
      ReachingSpine.binaryLeft _ child _ =>
      reachingSpineOmissionRanks offset marks child ++
        [offset + marks]
  | _, _, _, _, _, _,
      ReachingSpine.binaryRight _ _ child =>
      offset ::
        reachingSpineOmissionRanks offset marks child

/-- Every omitted sibling on the reaching spine occurs at the same gap k. -/
def ReachingSpineAllOmissionsAt
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop}
    {A X : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (offset marks k : Nat)
    (spine :
      ReachingSpine terminalRule binaryRule
        A X left right path siblings) : Prop :=
  ∀ j ∈ reachingSpineOmissionRanks offset marks spine,
    j = k

/-- Decompose the gap invariant through a retained-left spine step. -/
theorem reachingSpineAllOmissionsAt_binaryLeft_iff
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A B C X : N}
    {left right z : Word α}
    {path : List N}
    {siblings : List Nat}
    (hbin : binaryRule A B C)
    (child :
      ReachingSpine terminalRule binaryRule
        B X left right path siblings)
    (sibling :
      UntypedDerives terminalRule binaryRule C z)
    (offset marks k : Nat) :
    ReachingSpineAllOmissionsAt offset marks k
      (ReachingSpine.binaryLeft hbin child sibling)
      ↔
    ReachingSpineAllOmissionsAt offset marks k child
      ∧ offset + marks = k := by
  constructor
  · intro h
    constructor
    · intro j hj
      exact h j
        (List.mem_append_left _ hj)
    · exact h (offset + marks)
        (by
          simp [reachingSpineOmissionRanks])
  · rintro ⟨hchild, hlast⟩ j hj
    simp only [reachingSpineOmissionRanks,
      List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | hj
    · exact hchild j hj
    · simpa [hj] using hlast

/-- Decompose the gap invariant through a retained-right spine step. -/
theorem reachingSpineAllOmissionsAt_binaryRight_iff
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A B C X : N}
    {left right y : Word α}
    {path : List N}
    {siblings : List Nat}
    (hbin : binaryRule A B C)
    (sibling :
      UntypedDerives terminalRule binaryRule B y)
    (child :
      ReachingSpine terminalRule binaryRule
        C X left right path siblings)
    (offset marks k : Nat) :
    ReachingSpineAllOmissionsAt offset marks k
      (ReachingSpine.binaryRight hbin sibling child)
      ↔
    offset = k
      ∧ ReachingSpineAllOmissionsAt offset marks k child := by
  constructor
  · intro h
    constructor
    · exact h offset
        (by simp [reachingSpineOmissionRanks])
    · intro j hj
      exact h j
        (by
          simp [reachingSpineOmissionRanks, hj])
  · rintro ⟨hoffset, hchild⟩ j hj
    simp only [reachingSpineOmissionRanks,
      List.mem_cons] at hj
    rcases hj with hj | hj
    · simpa [hj] using hoffset
    · exact hchild j hj

/--
Taking a repetition-free suffix of a reaching spine preserves the central-gap
invariant.
-/
theorem reachingSubspine_preserves_allOmissionsAt
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset marks k : Nat)
    {A X Y : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (spine :
      ReachingSpine terminalRule binaryRule
        A X left right path siblings)
    (hnodup : path.Nodup)
    (hgap :
      ReachingSpineAllOmissionsAt
        offset marks k spine)
    (hmem : Y ∈ path) :
    ∃ left' right' path' siblings',
      ReachingSpine terminalRule binaryRule
        Y X left' right' path' siblings'
      ∧ path'.Nodup
      ∧ ReachingSpineAllOmissionsAt
          offset marks k
          (show ReachingSpine terminalRule binaryRule
            Y X left' right' path' siblings' from by
              assumption) := by
  induction spine generalizing Y with
  | @hole A =>
      simp only [List.mem_singleton] at hmem
      subst Y
      refine ⟨[], [], [A], [], ReachingSpine.hole, by simp, ?_⟩
      intro j hj
      simp [reachingSpineOmissionRanks] at hj

  | @binaryLeft A B C X left right z path siblings
      hbin child sibling ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      have hparts :=
        (reachingSpineAllOmissionsAt_binaryLeft_iff
          terminalRule binaryRule hbin child sibling
          offset marks k).1 hgap
      rcases hparts with ⟨hchildGap, hlast⟩
      rcases hmem with hYA | hYtail
      · subst Y
        exact
          ⟨left, right ++ z, A :: path,
            z.length :: siblings,
            ReachingSpine.binaryLeft hbin child sibling,
            (by rw [List.nodup_cons]; exact hnodup),
            hgap⟩
      · exact ih hnodup.2 hchildGap hYtail

  | @binaryRight A B C X left right y path siblings
      hbin sibling child ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      have hparts :=
        (reachingSpineAllOmissionsAt_binaryRight_iff
          terminalRule binaryRule hbin sibling child
          offset marks k).1 hgap
      rcases hparts with ⟨hfirst, hchildGap⟩
      rcases hmem with hYA | hYtail
      · subst Y
        exact
          ⟨y ++ left, right, A :: path,
            y.length :: siblings,
            ReachingSpine.binaryRight hbin sibling child,
            (by rw [List.nodup_cons]; exact hnodup),
            hgap⟩
      · exact ih hnodup.2 hchildGap hYtail

/--
Cycle shortening of a reaching spine preserves the single central omission
gap.

This is the positional counterpart of
`normalize_reachingSpine_to_nodup_unbounded`.
-/
theorem normalize_reachingSpine_preserves_allOmissionsAt
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset marks k : Nat)
    {A X : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (spine :
      ReachingSpine terminalRule binaryRule
        A X left right path siblings)
    (hgap :
      ReachingSpineAllOmissionsAt
        offset marks k spine) :
    ∃ left' right' path' siblings',
      ReachingSpine terminalRule binaryRule
        A X left' right' path' siblings'
      ∧ path'.Nodup
      ∧ ReachingSpineAllOmissionsAt
          offset marks k
          (show ReachingSpine terminalRule binaryRule
            A X left' right' path' siblings' from by
              assumption) := by
  induction spine with
  | @hole A =>
      refine ⟨[], [], [A], [], ReachingSpine.hole, by simp, ?_⟩
      intro j hj
      simp [reachingSpineOmissionRanks] at hj

  | @binaryLeft A B C X left right z path siblings
      hbin child sibling ih =>
      have hparts :=
        (reachingSpineAllOmissionsAt_binaryLeft_iff
          terminalRule binaryRule hbin child sibling
          offset marks k).1 hgap
      rcases hparts with ⟨hchildGap, hlast⟩
      obtain ⟨left', right', path', siblings',
          child', hnodup, hchildGap'⟩ :=
        ih hchildGap
      by_cases hmem : A ∈ path'
      · exact
          reachingSubspine_preserves_allOmissionsAt
            terminalRule binaryRule
            offset marks k
            child' hnodup hchildGap' hmem
      · let spine' :
            ReachingSpine terminalRule binaryRule
              A X left' (right' ++ z)
              (A :: path') (z.length :: siblings') :=
          ReachingSpine.binaryLeft hbin child' sibling
        have hgap' :
            ReachingSpineAllOmissionsAt
              offset marks k spine' := by
          apply
            (reachingSpineAllOmissionsAt_binaryLeft_iff
              terminalRule binaryRule
              hbin child' sibling
              offset marks k).2
          exact ⟨hchildGap', hlast⟩
        exact
          ⟨left', right' ++ z, A :: path',
            z.length :: siblings',
            spine',
            (by rw [List.nodup_cons]; exact ⟨hmem, hnodup⟩),
            hgap'⟩

  | @binaryRight A B C X left right y path siblings
      hbin sibling child ih =>
      have hparts :=
        (reachingSpineAllOmissionsAt_binaryRight_iff
          terminalRule binaryRule hbin sibling child
          offset marks k).1 hgap
      rcases hparts with ⟨hfirst, hchildGap⟩
      obtain ⟨left', right', path', siblings',
          child', hnodup, hchildGap'⟩ :=
        ih hchildGap
      by_cases hmem : A ∈ path'
      · exact
          reachingSubspine_preserves_allOmissionsAt
            terminalRule binaryRule
            offset marks k
            child' hnodup hchildGap' hmem
      · let spine' :
            ReachingSpine terminalRule binaryRule
              A X (y ++ left') right'
              (A :: path') (y.length :: siblings') :=
          ReachingSpine.binaryRight hbin sibling child'
        have hgap' :
            ReachingSpineAllOmissionsAt
              offset marks k spine' := by
          apply
            (reachingSpineAllOmissionsAt_binaryRight_iff
              terminalRule binaryRule
              hbin sibling child'
              offset marks k).2
          exact ⟨hfirst, hchildGap'⟩
        exact
          ⟨y ++ left', right', A :: path',
            y.length :: siblings',
            spine',
            (by rw [List.nodup_cons]; exact ⟨hmem, hnodup⟩),
            hgap'⟩

end MarkedBoundaryGapSemantic

end TCS1
end LeanCfgProject
