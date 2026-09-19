import LeanCfgProject.TCS1.MarkedBoundaryNormalization

/-!
# TCS #1 v68: central-gap preservation on shortened reaching spines

The long-word proof of Lemma 7.1 must preserve more than the number of marked
leaves: every omitted sibling subtree has to remain in the single middle gap
between the first k and last l marked terminals.

For one maximal one-child chain, the positional information is simple.  If the
retained child is the left child, the omitted right sibling lies after all
marked leaves carried by the retained base.  If the retained child is the
right child, the omitted left sibling lies before all those marked leaves.

Because `ReachingSpine` is proposition-valued, the invariant below is also
proposition-valued rather than computed as data from a proof object.  This
lets us prove directly that repeated-label shortcutting preserves the unique
central gap.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section MarkedBoundaryGapSemantic

variable {N : Type u}
variable {α : Type v}

/--
Every omitted sibling on one reaching spine occurs at the same global marked
leaf gap k.

`offset` is the number of marked leaves globally before the retained base,
and `marks` is the number of marked leaves in that base.
-/
def ReachingSpineAllOmissionsAt
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop}
    (offset marks k : Nat) :
    {A X : N} →
    {left right : Word α} →
    {path : List N} →
    {siblings : List Nat} →
    (spine :
      ReachingSpine terminalRule binaryRule
        A X left right path siblings) →
    Prop
  | _, _, _, _, _, _, ReachingSpine.hole =>
      True
  | _, _, _, _, _, _,
      ReachingSpine.binaryLeft _ child _ =>
      ReachingSpineAllOmissionsAt offset marks k child
        ∧ offset + marks = k
  | _, _, _, _, _, _,
      ReachingSpine.binaryRight _ _ child =>
      offset = k
        ∧ ReachingSpineAllOmissionsAt offset marks k child

@[simp] theorem reachingSpineAllOmissionsAt_hole
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset marks k : Nat)
    {A : N} :
    ReachingSpineAllOmissionsAt offset marks k
      (ReachingSpine.hole :
        ReachingSpine terminalRule binaryRule
          A A [] [] [A] []) := by
  trivial

@[simp] theorem reachingSpineAllOmissionsAt_binaryLeft
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
  rfl

@[simp] theorem reachingSpineAllOmissionsAt_binaryRight
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
  rfl

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
      ∃ spine' :
        ReachingSpine terminalRule binaryRule
          Y X left' right' path' siblings',
        path'.Nodup
        ∧ ReachingSpineAllOmissionsAt
            offset marks k spine' := by
  induction spine generalizing Y with
  | @hole A =>
      simp only [List.mem_singleton] at hmem
      subst Y
      exact
        ⟨[], [], [A], [], ReachingSpine.hole,
          by simp,
          by trivial⟩

  | @binaryLeft A B C X left right z path siblings
      hbin child sibling ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      have hchildGap :
          ReachingSpineAllOmissionsAt
            offset marks k child :=
        hgap.1
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
      have hchildGap :
          ReachingSpineAllOmissionsAt
            offset marks k child :=
        hgap.2
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
      ∃ spine' :
        ReachingSpine terminalRule binaryRule
          A X left' right' path' siblings',
        path'.Nodup
        ∧ ReachingSpineAllOmissionsAt
            offset marks k spine' := by
  induction spine with
  | @hole A =>
      exact
        ⟨[], [], [A], [], ReachingSpine.hole,
          by simp,
          by trivial⟩

  | @binaryLeft A B C X left right z path siblings
      hbin child sibling ih =>
      have hchildGap :
          ReachingSpineAllOmissionsAt
            offset marks k child :=
        hgap.1
      have hlast : offset + marks = k :=
        hgap.2
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
          exact ⟨hchildGap', hlast⟩
        exact
          ⟨left', right' ++ z, A :: path',
            z.length :: siblings',
            spine',
            (by
              rw [List.nodup_cons]
              exact ⟨hmem, hnodup⟩),
            hgap'⟩

  | @binaryRight A B C X left right y path siblings
      hbin sibling child ih =>
      have hfirst : offset = k :=
        hgap.1
      have hchildGap :
          ReachingSpineAllOmissionsAt
            offset marks k child :=
        hgap.2
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
          exact ⟨hfirst, hchildGap'⟩
        exact
          ⟨y ++ left', right', A :: path',
            y.length :: siblings',
            spine',
            (by
              rw [List.nodup_cons]
              exact ⟨hmem, hnodup⟩),
            hgap'⟩

end MarkedBoundaryGapSemantic

end TCS1
end LeanCfgProject
