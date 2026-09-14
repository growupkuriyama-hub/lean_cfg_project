import LeanCfgProject.FixedHCFGv44.LinearNormalizationTypedShapeV49
import LeanCfgProject.FixedHCFGv44.LinearRetainedCardBridgeV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Finite active-state bridge for the explicit v49 Appendix A normalization.

`LinearNormNT` is intentionally an extensional ambient type: a stage constructor
can carry an arbitrary list of remaining spine operations.  Hence the ambient
type is infinite even for a finite source grammar.  Reachable normalized stages,
however, have bounded remaining programs.  This file records that bound in a
finite active-label set, proves that every retained yield-typed state lies over
that set, and obtains the `Fintype` instance needed by Appendix B from the finite
retained state space itself.
-/

/-- All spine-operation lists of length at most `n`, explicitly enumerated. -/
noncomputable def linearSpineOpsUpToV49
    {Sigma : Type u} [Fintype Sigma] : Nat → Finset (List (LinearSpineOp Sigma))
  | 0 => {[]}
  | n + 1 => by
      classical
      let prev := linearSpineOpsUpToV49 (Sigma := Sigma) n
      let lefts := (Finset.univ : Finset Sigma).biUnion
        (fun a => prev.image (fun ops => LinearSpineOp.left a :: ops))
      let rights := (Finset.univ : Finset Sigma).biUnion
        (fun a => prev.image (fun ops => LinearSpineOp.right a :: ops))
      exact {[]} ∪ lefts ∪ rights

/-- The explicit enumeration contains exactly the lists of bounded length. -/
theorem mem_linearSpineOpsUpToV49_iff
    {Sigma : Type u} [Fintype Sigma]
    (n : Nat) (ops : List (LinearSpineOp Sigma)) :
    ops ∈ linearSpineOpsUpToV49 (Sigma := Sigma) n ↔ ops.length ≤ n := by
  classical
  induction n generalizing ops with
  | zero =>
      simp [linearSpineOpsUpToV49]
  | succ n ih =>
      cases ops with
      | nil =>
          simp [linearSpineOpsUpToV49]
      | cons op rest =>
          cases op with
          | left a =>
              simp [linearSpineOpsUpToV49, ih]
          | right a =>
              simp [linearSpineOpsUpToV49, ih]

/--
Finite ambient support for every reachable normalized label.  Old symbols and
wrappers are globally finite; stage programs are truncated at the total
prepared RHS length; terminal endpoints are indexed by the finite prepared
rule list.
-/
noncomputable def linearNormActiveLabelsV49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma)) :
    Finset (LinearNormNT N Sigma) := by
  classical
  let oldLabels : Finset (LinearNormNT N Sigma) :=
    (Finset.univ : Finset N).image (fun A => LinearNormNT.old A)
  let wrapperLabels : Finset (LinearNormNT N Sigma) :=
    (Finset.univ : Finset Sigma).image (fun a => LinearNormNT.wrap a)
  let stageLabels : Finset (LinearNormNT N Sigma) :=
    rules.toFinset.biUnion (fun r =>
      (linearSpineOpsUpToV49 (Sigma := Sigma) (preparedTotalRhsLength rules)).image
        (fun ops => LinearNormNT.stage r ops))
  let endLabels : Finset (LinearNormNT N Sigma) :=
    rules.toFinset.image (fun r => LinearNormNT.terminalEnd r)
  exact oldLabels ∪ wrapperLabels ∪ stageLabels ∪ endLabels

@[simp] theorem linearNorm_old_mem_activeLabels_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma)) (A : N) :
    LinearNormNT.old (Sigma := Sigma) A ∈ linearNormActiveLabelsV49 rules := by
  classical
  simp [linearNormActiveLabelsV49]

@[simp] theorem linearNorm_wrap_mem_activeLabels_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma)) (a : Sigma) :
    LinearNormNT.wrap (N := N) a ∈ linearNormActiveLabelsV49 rules := by
  classical
  simp [linearNormActiveLabelsV49]

@[simp] theorem linearNorm_terminalEnd_mem_activeLabels_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma))
    {r : PreparedLinearRule N Sigma} (hr : r ∈ rules) :
    LinearNormNT.terminalEnd r ∈ linearNormActiveLabelsV49 rules := by
  classical
  simp [linearNormActiveLabelsV49, hr]

/-- Membership of a stage label is exactly rule membership plus the global length bound. -/
theorem linearNorm_stage_mem_activeLabels_iff_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma))
    (r : PreparedLinearRule N Sigma) (ops : List (LinearSpineOp Sigma)) :
    LinearNormNT.stage r ops ∈ linearNormActiveLabelsV49 rules ↔
      r ∈ rules ∧ ops.length ≤ preparedTotalRhsLength rules := by
  classical
  simp [linearNormActiveLabelsV49, mem_linearSpineOpsUpToV49_iff]

/-- A member rule's RHS length is bounded by the total prepared RHS length. -/
theorem preparedRule_rhsLength_le_total_of_mem_v49
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {r : PreparedLinearRule N Sigma}
    (hr : r ∈ rules) :
    r.rhsLength ≤ preparedTotalRhsLength rules := by
  induction rules with
  | nil =>
      simp at hr
  | cons q qs ih =>
      simp only [List.mem_cons] at hr
      simp [preparedTotalRhsLength]
      rcases hr with rfl | hr
      · omega
      · have h := ih hr
        omega

/-- A context spine is no longer than its prepared RHS encoding. -/
theorem context_spineOps_length_le_rhsLength_v49
    {N : Type v} {Sigma : Type u}
    {A : N} (body : LinearContextBody N Sigma) (h : body.Nonunit) :
    body.spineOps.length ≤
      (PreparedLinearRule.context A body h).rhsLength := by
  simp [PreparedLinearRule.rhsLength, LinearContextBody.spineOps,
    contextSpineOps_length]

/-- A terminal-only spine is no longer than its prepared RHS encoding. -/
theorem terminal_spineOps_length_le_rhsLength_v49
    {N : Type v} {Sigma : Type u}
    {A : N} (body : NonemptyTerminalBody Sigma) :
    body.spineOps.length ≤
      (PreparedLinearRule.terminal A body).rhsLength := by
  simp [PreparedLinearRule.rhsLength, NonemptyTerminalBody.spineOps,
    NonemptyTerminalBody.word]

/-- A bounded remaining program always names an active entry state. -/
theorem linearNorm_entry_mem_activeLabels_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma))
    {r : PreparedLinearRule N Sigma}
    (hr : r ∈ rules) (ops : List (LinearSpineOp Sigma))
    (hlen : ops.length ≤ preparedTotalRhsLength rules) :
    LinearNormNT.entry r ops ∈ linearNormActiveLabelsV49 rules := by
  cases ops with
  | nil =>
      cases r with
      | context A body h =>
          simpa [LinearNormNT.entry, LinearNormNT.ruleCore] using
            (linearNorm_old_mem_activeLabels_v49 rules body.center)
      | terminal A body =>
          simpa [LinearNormNT.entry, LinearNormNT.ruleCore] using
            (linearNorm_terminalEnd_mem_activeLabels_v49 rules hr)
  | cons op rest =>
      exact (linearNorm_stage_mem_activeLabels_iff_v49 rules _ _).2 ⟨hr, hlen⟩

/--
If the parent of an explicit normalized binary rule is active, both children
are active as well.
-/
theorem linearNormBinary_children_active_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    {rules : List (PreparedLinearRule N Sigma)}
    {X Y Z : LinearNormNT N Sigma}
    (hX : X ∈ linearNormActiveLabelsV49 rules)
    (hRule : LinearNormBinary rules X Y Z) :
    Y ∈ linearNormActiveLabelsV49 rules ∧
      Z ∈ linearNormActiveLabelsV49 rules := by
  cases hRule with
  | @contextRootLeft A body h a rest hrule hops =>
      have hLocal := context_spineOps_length_le_rhsLength_v49
        (A := A) body h
      have hTotal := preparedRule_rhsLength_le_total_of_mem_v49 hrule
      have hRest : rest.length ≤ preparedTotalRhsLength rules := by
        rw [hops] at hLocal
        simp only [List.length_cons] at hLocal
        omega
      exact ⟨linearNorm_wrap_mem_activeLabels_v49 rules a,
        linearNorm_entry_mem_activeLabels_v49 rules hrule rest hRest⟩
  | @contextRootRight A body h a rest hrule hops =>
      have hLocal := context_spineOps_length_le_rhsLength_v49
        (A := A) body h
      have hTotal := preparedRule_rhsLength_le_total_of_mem_v49 hrule
      have hRest : rest.length ≤ preparedTotalRhsLength rules := by
        rw [hops] at hLocal
        simp only [List.length_cons] at hLocal
        omega
      exact ⟨linearNorm_entry_mem_activeLabels_v49 rules hrule rest hRest,
        linearNorm_wrap_mem_activeLabels_v49 rules a⟩
  | @terminalRootLeft A body a rest hrule hops =>
      have hLocal := terminal_spineOps_length_le_rhsLength_v49
        (A := A) body
      have hTotal := preparedRule_rhsLength_le_total_of_mem_v49 hrule
      have hRest : rest.length ≤ preparedTotalRhsLength rules := by
        rw [hops] at hLocal
        simp only [List.length_cons] at hLocal
        omega
      exact ⟨linearNorm_wrap_mem_activeLabels_v49 rules a,
        linearNorm_entry_mem_activeLabels_v49 rules hrule rest hRest⟩
  | @stageLeft r a rest hrule =>
      have hParent :=
        (linearNorm_stage_mem_activeLabels_iff_v49 rules
          r (LinearSpineOp.left a :: rest)).1 hX
      have hRest : rest.length ≤ preparedTotalRhsLength rules := by
        simpa using Nat.le_of_succ_le_succ hParent.2
      exact ⟨linearNorm_wrap_mem_activeLabels_v49 rules a,
        linearNorm_entry_mem_activeLabels_v49 rules hrule rest hRest⟩
  | @stageRight r a rest hrule =>
      have hParent :=
        (linearNorm_stage_mem_activeLabels_iff_v49 rules
          r (LinearSpineOp.right a :: rest)).1 hX
      have hRest : rest.length ≤ preparedTotalRhsLength rules := by
        simpa using Nat.le_of_succ_le_succ hParent.2
      exact ⟨linearNorm_entry_mem_activeLabels_v49 rules hrule rest hRest,
        linearNorm_wrap_mem_activeLabels_v49 rules a⟩

/-- Every typed state reachable in the trimmed normalized grammar has an active label. -/
theorem trimmedLinearNorm_typedOccurs_label_active_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    {rules : List (PreparedLinearRule N Sigma)} {start : N → Prop}
    {X : TypedNT (LinearNormNT N Sigma) Obs} {u v : Word Sigma}
    (hOcc : TypedOccurs Obs
      (TrimmedLinearNormTerminal rules start)
      (TrimmedLinearNormBinary rules start)
      (TrimmedLinearNormStart rules start) X u v) :
    X.label ∈ linearNormActiveLabelsV49 rules := by
  induction hOcc with
  | @start A mu hStart =>
      have hBase : LinearNormStartRules start A := hStart.1
      cases A with
      | old A0 =>
          exact linearNorm_old_mem_activeLabels_v49 rules A0
      | wrap a =>
          exact (by simpa [LinearNormStartRules] using hBase : False).elim
      | stage r ops =>
          exact (by simpa [LinearNormStartRules] using hBase : False).elim
      | terminalEnd r =>
          exact (by simpa [LinearNormStartRules] using hBase : False).elim
  | @left A B C mu nu u v y parent hRule rightDeriv ih =>
      exact (linearNormBinary_children_active_v49 ih hRule.1).1
  | @right A B C mu nu u v x parent hRule leftDeriv ih =>
      exact (linearNormBinary_children_active_v49 ih hRule.1).2

/-- Every retained typed state lies over the finite active-label support. -/
theorem trimmedLinearNorm_typedKept_label_active_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    {rules : List (PreparedLinearRule N Sigma)} {start : N → Prop}
    {X : TypedNT (LinearNormNT N Sigma) Obs}
    (hKeep : TypedKept Obs
      (TrimmedLinearNormTerminal rules start)
      (TrimmedLinearNormBinary rules start)
      (TrimmedLinearNormStart rules start) X) :
    X.label ∈ linearNormActiveLabelsV49 rules := by
  rcases hKeep.2 with ⟨u, v, hOcc⟩
  exact trimmedLinearNorm_typedOccurs_label_active_v49 Obs hOcc

/-- All typed states whose labels lie in the active support. -/
noncomputable def linearNormActiveTypedNTFinsetV49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma) (rules : List (PreparedLinearRule N Sigma)) :
    Finset (TypedNT (LinearNormNT N Sigma) Obs) := by
  classical
  exact ((linearNormActiveLabelsV49 rules).product
    (Finset.univ : Finset Obs.M)).image
      (fun p => { label := p.1, yieldType := p.2 })

/-- A typed state belongs to the typed active support whenever its label is active. -/
theorem typedNT_mem_activeTypedNTFinset_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma) (rules : List (PreparedLinearRule N Sigma))
    (X : TypedNT (LinearNormNT N Sigma) Obs)
    (hLabel : X.label ∈ linearNormActiveLabelsV49 rules) :
    X ∈ linearNormActiveTypedNTFinsetV49 Obs rules := by
  classical
  rcases X with ⟨label, mu⟩
  simp [linearNormActiveTypedNTFinsetV49, hLabel]

/-- Embed a retained typed state into the finite active typed support. -/
noncomputable def keptStateToActiveTypedV49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    (rules : List (PreparedLinearRule N Sigma)) (start : N → Prop)
    (X : KeptState Obs
      (TrimmedLinearNormTerminal rules start)
      (TrimmedLinearNormBinary rules start)
      (TrimmedLinearNormStart rules start)) :
    ↥(linearNormActiveTypedNTFinsetV49 Obs rules) :=
  ⟨X.1, typedNT_mem_activeTypedNTFinset_v49 Obs rules X.1
    (trimmedLinearNorm_typedKept_label_active_v49 Obs X.property)⟩

/-- The active-support embedding is injective. -/
theorem keptStateToActiveTypedV49_injective
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    (rules : List (PreparedLinearRule N Sigma)) (start : N → Prop) :
    Function.Injective (keptStateToActiveTypedV49 Obs rules start) := by
  intro X Y h
  apply Subtype.ext
  exact congrArg Subtype.val h

/--
The retained yield-typed state type of every finite trimmed normalized grammar
is finite, even though the ambient `LinearNormNT` type is not.
-/
noncomputable def trimmedLinearNormKeptStateFintypeV49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    (rules : List (PreparedLinearRule N Sigma)) (start : N → Prop) :
    Fintype (KeptState Obs
      (TrimmedLinearNormTerminal rules start)
      (TrimmedLinearNormBinary rules start)
      (TrimmedLinearNormStart rules start)) := by
  classical
  let f := keptStateToActiveTypedV49 Obs rules start
  letI : Finite (KeptState Obs
      (TrimmedLinearNormTerminal rules start)
      (TrimmedLinearNormBinary rules start)
      (TrimmedLinearNormStart rules start)) :=
    Finite.of_injective f (keptStateToActiveTypedV49_injective Obs rules start)
  exact Fintype.ofFinite _

/-- Source-normalization specialization of the retained-state `Fintype` construction. -/
noncomputable def sourceNormalizedKeptStateFintypeV49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    Fintype (KeptState Obs
      (SourceNormalizedTerminalV49 sourceRules S)
      (SourceNormalizedBinaryV49 sourceRules S)
      (SourceNormalizedStartV49 sourceRules S)) := by
  change Fintype (KeptState Obs
    (TrimmedLinearNormTerminal (enumeratePreparedLinearRules sourceRules)
      (SourceSeparatedStart S))
    (TrimmedLinearNormBinary (enumeratePreparedLinearRules sourceRules)
      (SourceSeparatedStart S))
    (TrimmedLinearNormStart (enumeratePreparedLinearRules sourceRules)
      (SourceSeparatedStart S)))
  exact trimmedLinearNormKeptStateFintypeV49 Obs
    (enumeratePreparedLinearRules sourceRules) (SourceSeparatedStart S)

/--
Appendix B's short-witness inequalities now apply directly to the explicit
source normalization, with no ambient-finiteness assumption on `LinearNormNT`.
-/
theorem sourceNormalized_short_canonical_witnesses_v49
    {N : Type v} {Sigma : Type u}
    [Fintype N] [Fintype Sigma] [LinearOrder Sigma] [WellFoundedLT Sigma]
    (Obs : Observer Sigma)
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    let terminal := SourceNormalizedTerminalV49 sourceRules S
    let binary := SourceNormalizedBinaryV49 sourceRules S
    let start := SourceNormalizedStartV49 sourceRules S
    (∀ X : KeptState Obs terminal binary start,
      (canonicalOmega X).length ≤ Fintype.card (KeptState Obs terminal binary start)) ∧
    (∀ X : KeptState Obs terminal binary start,
      (canonicalLeftCtx X).length + (canonicalRightCtx X).length ≤
        2 * Fintype.card (KeptState Obs terminal binary start)) := by
  letI := sourceNormalizedKeptStateFintypeV49 Obs sourceRules S
  exact short_canonical_witnesses_from_retained_finite_shape_v49
    (sourceNormalizedTypedLinearSpineShapeV49 Obs sourceRules S)

end FixedHCFGv44
end LeanCfgProject
