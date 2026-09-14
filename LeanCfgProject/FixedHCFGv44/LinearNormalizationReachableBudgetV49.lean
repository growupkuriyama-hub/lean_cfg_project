import LeanCfgProject.FixedHCFGv44.LinearNormalizationTightBudgetV49
import LeanCfgProject.FixedHCFGv44.LinearNormalizationSourceSizeV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Polynomial reachable-state budget for the explicit v49 linear normalization.

The extensional ambient type `LinearNormNT` is infinite because `stage` accepts
an arbitrary remaining spine program.  Only suffixes of the finitely many
prepared spine programs are reachable from an old source state.  This file
records a deliberately slightly loose finite support containing every such
suffix entry, proves that reachability/retention stays inside it, and derives a
source-polynomial cardinality bound for retained yield-typed states.

The support here is larger than the exact fresh-state budget from
`LinearNormalizationTightBudgetV49`: for each prepared rule it also records the
rule core and the full entry state.  Its size is nevertheless linear in the
prepared grammar encoding, which makes the successor-closure proof transparent
and is sufficient for the polynomial characteristic-data theorem.
-/

/-- The spine program attached to one prepared production. -/
def preparedSpineOpsV49
    {N : Type v} {Sigma : Type u} :
    PreparedLinearRule N Sigma → List (LinearSpineOp Sigma)
  | .context _ body _ => body.spineOps
  | .terminal _ body => body.spineOps

/--
All entry states obtained while consuming a spine program, including the full
entry and the final rule core.  A program of length `k` contributes `k+1`
entries before quotienting duplicates.
-/
def linearNormEntriesV49
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma) :
    List (LinearSpineOp Sigma) → List (LinearNormNT N Sigma)
  | [] => [LinearNormNT.entry r []]
  | op :: rest =>
      LinearNormNT.entry r (op :: rest) :: linearNormEntriesV49 r rest

/-- Exact entry-list length. -/
theorem linearNormEntriesV49_length
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma) (ops : List (LinearSpineOp Sigma)) :
    (linearNormEntriesV49 r ops).length = ops.length + 1 := by
  induction ops with
  | nil => simp [linearNormEntriesV49]
  | cons op rest ih => simp [linearNormEntriesV49, ih]

/-- The next entry after a stage entry remains in the same suffix-entry list. -/
theorem linearNormEntriesV49_stage_successor
    {N : Type v} {Sigma : Type u}
    (q r : PreparedLinearRule N Sigma)
    (ops : List (LinearSpineOp Sigma))
    (op : LinearSpineOp Sigma) (rest : List (LinearSpineOp Sigma))
    (hmem : LinearNormNT.stage r (op :: rest) ∈
      linearNormEntriesV49 q ops) :
    LinearNormNT.entry r rest ∈ linearNormEntriesV49 q ops := by
  induction ops with
  | nil =>
      simp [linearNormEntriesV49, LinearNormNT.entry, LinearNormNT.ruleCore] at hmem
  | cons head tail ih =>
      simp only [linearNormEntriesV49, List.mem_cons] at hmem ⊢
      rcases hmem with hEq | hTail
      · have hEntry :
          LinearNormNT.entry q (head :: tail) = LinearNormNT.stage q (head :: tail) := rfl
        rw [hEntry] at hEq
        cases hEq
        exact Or.inr (by simp [linearNormEntriesV49])
      · exact Or.inr (ih hTail)

/-- Concatenation of all rule-local suffix-entry lists. -/
def normalizationReachableEntriesV49
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    List (LinearNormNT N Sigma) :=
  rules.flatMap (fun r => linearNormEntriesV49 r (preparedSpineOpsV49 r))

/-- A rule member contributes all of its suffix entries to the global list. -/
theorem linearNormEntriesV49_subset_global
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {r : PreparedLinearRule N Sigma}
    (hr : r ∈ rules) :
    ∀ {X : LinearNormNT N Sigma},
      X ∈ linearNormEntriesV49 r (preparedSpineOpsV49 r) →
        X ∈ normalizationReachableEntriesV49 rules := by
  intro X hX
  unfold normalizationReachableEntriesV49
  exact List.mem_flatMap.mpr ⟨r, hr, hX⟩

/-- Global suffix-entry support is closed under one stage continuation. -/
theorem normalizationReachableEntriesV49_stage_successor
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {r : PreparedLinearRule N Sigma}
    {op : LinearSpineOp Sigma} {rest : List (LinearSpineOp Sigma)}
    (hmem : LinearNormNT.stage r (op :: rest) ∈
      normalizationReachableEntriesV49 rules) :
    LinearNormNT.entry r rest ∈ normalizationReachableEntriesV49 rules := by
  unfold normalizationReachableEntriesV49 at hmem ⊢
  rcases List.mem_flatMap.mp hmem with ⟨q, hq, hlocal⟩
  exact List.mem_flatMap.mpr ⟨q, hq,
    linearNormEntriesV49_stage_successor q r (preparedSpineOpsV49 q)
      op rest hlocal⟩

/-- Every rule-local immediate continuation occurs in the global entry support. -/
theorem linearNorm_rule_continuation_mem_global_v49
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {r : PreparedLinearRule N Sigma}
    (hr : r ∈ rules)
    {op : LinearSpineOp Sigma} {rest : List (LinearSpineOp Sigma)}
    (hops : preparedSpineOpsV49 r = op :: rest) :
    LinearNormNT.entry r rest ∈ normalizationReachableEntriesV49 rules := by
  apply linearNormEntriesV49_subset_global hr
  rw [hops]
  simp [linearNormEntriesV49]

/-- Finite quotient of the reachable suffix-entry list. -/
noncomputable def linearNormReachableEntriesFinsetV49
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    Finset (LinearNormNT N Sigma) := by
  classical
  exact (normalizationReachableEntriesV49 rules).toFinset

/-- Polynomial finite support used for all actually reachable normalized labels. -/
noncomputable def linearNormReachableLabelsV49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma)) :
    Finset (LinearNormNT N Sigma) := by
  classical
  exact linearNormOldLabelsV49 ∪ linearNormWrapperLabelsV49 ∪
    linearNormReachableEntriesFinsetV49 rules

@[simp] theorem linearNorm_old_mem_reachableLabels_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma)) (A : N) :
    LinearNormNT.old (Sigma := Sigma) A ∈ linearNormReachableLabelsV49 rules := by
  classical
  simp [linearNormReachableLabelsV49, linearNormOldLabelsV49]

@[simp] theorem linearNorm_wrap_mem_reachableLabels_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma)) (a : Sigma) :
    LinearNormNT.wrap (N := N) a ∈ linearNormReachableLabelsV49 rules := by
  classical
  simp [linearNormReachableLabelsV49, linearNormWrapperLabelsV49]

/-- Any globally enumerated suffix entry lies in the finite label support. -/
theorem linearNorm_globalEntry_mem_reachableLabels_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma))
    {X : LinearNormNT N Sigma}
    (hX : X ∈ normalizationReachableEntriesV49 rules) :
    X ∈ linearNormReachableLabelsV49 rules := by
  classical
  simp [linearNormReachableLabelsV49, linearNormReachableEntriesFinsetV49,
    hX]

/--
If the parent of a normalized binary rule is reachable, both children remain
inside the polynomial reachable-label support.
-/
theorem linearNormBinary_children_reachable_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    {rules : List (PreparedLinearRule N Sigma)}
    {X Y Z : LinearNormNT N Sigma}
    (hX : X ∈ linearNormReachableLabelsV49 rules)
    (hRule : LinearNormBinary rules X Y Z) :
    Y ∈ linearNormReachableLabelsV49 rules ∧
      Z ∈ linearNormReachableLabelsV49 rules := by
  cases hRule with
  | @contextRootLeft A body h a rest hrule hops =>
      have hCont := linearNorm_rule_continuation_mem_global_v49
        (rules := rules) hrule (op := LinearSpineOp.left a) (rest := rest)
        (by simpa [preparedSpineOpsV49] using hops)
      exact ⟨linearNorm_wrap_mem_reachableLabels_v49 rules a,
        linearNorm_globalEntry_mem_reachableLabels_v49 rules hCont⟩
  | @contextRootRight A body h a rest hrule hops =>
      have hCont := linearNorm_rule_continuation_mem_global_v49
        (rules := rules) hrule (op := LinearSpineOp.right a) (rest := rest)
        (by simpa [preparedSpineOpsV49] using hops)
      exact ⟨linearNorm_globalEntry_mem_reachableLabels_v49 rules hCont,
        linearNorm_wrap_mem_reachableLabels_v49 rules a⟩
  | @terminalRootLeft A body a rest hrule hops =>
      have hCont := linearNorm_rule_continuation_mem_global_v49
        (rules := rules) hrule (op := LinearSpineOp.left a) (rest := rest)
        (by simpa [preparedSpineOpsV49] using hops)
      exact ⟨linearNorm_wrap_mem_reachableLabels_v49 rules a,
        linearNorm_globalEntry_mem_reachableLabels_v49 rules hCont⟩
  | @stageLeft r a rest hrule =>
      have hStageEntries : LinearNormNT.stage r (LinearSpineOp.left a :: rest) ∈
          normalizationReachableEntriesV49 rules := by
        classical
        have : LinearNormNT.stage r (LinearSpineOp.left a :: rest) ∉
            linearNormOldLabelsV49 (N := N) (Sigma := Sigma) := by
          simp [linearNormOldLabelsV49]
        have : LinearNormNT.stage r (LinearSpineOp.left a :: rest) ∉
            linearNormWrapperLabelsV49 (N := N) (Sigma := Sigma) := by
          simp [linearNormWrapperLabelsV49]
        simpa [linearNormReachableLabelsV49, linearNormReachableEntriesFinsetV49,
          linearNormOldLabelsV49, linearNormWrapperLabelsV49] using hX
      have hCont := normalizationReachableEntriesV49_stage_successor hStageEntries
      exact ⟨linearNorm_wrap_mem_reachableLabels_v49 rules a,
        linearNorm_globalEntry_mem_reachableLabels_v49 rules hCont⟩
  | @stageRight r a rest hrule =>
      have hStageEntries : LinearNormNT.stage r (LinearSpineOp.right a :: rest) ∈
          normalizationReachableEntriesV49 rules := by
        classical
        simpa [linearNormReachableLabelsV49, linearNormReachableEntriesFinsetV49,
          linearNormOldLabelsV49, linearNormWrapperLabelsV49] using hX
      have hCont := normalizationReachableEntriesV49_stage_successor hStageEntries
      exact ⟨linearNorm_globalEntry_mem_reachableLabels_v49 rules hCont,
        linearNorm_wrap_mem_reachableLabels_v49 rules a⟩

/-- Every typed state reachable in the trimmed normalized grammar has a reachable label. -/
theorem trimmedLinearNorm_typedOccurs_label_reachable_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    {rules : List (PreparedLinearRule N Sigma)} {start : N → Prop}
    {X : TypedNT (LinearNormNT N Sigma) Obs} {u v : Word Sigma}
    (hOcc : TypedOccurs Obs
      (TrimmedLinearNormTerminal rules start)
      (TrimmedLinearNormBinary rules start)
      (TrimmedLinearNormStart rules start) X u v) :
    X.label ∈ linearNormReachableLabelsV49 rules := by
  induction hOcc with
  | @start A mu hStart =>
      have hBase : LinearNormStartRules start A := hStart.1
      cases A with
      | old A0 => exact linearNorm_old_mem_reachableLabels_v49 rules A0
      | wrap a => exact (by simpa [LinearNormStartRules] using hBase : False).elim
      | stage r ops => exact (by simpa [LinearNormStartRules] using hBase : False).elim
      | terminalEnd r => exact (by simpa [LinearNormStartRules] using hBase : False).elim
  | @left A B C mu nu u v y parent hRule rightDeriv ih =>
      exact (linearNormBinary_children_reachable_v49 ih hRule.1).1
  | @right A B C mu nu u v x parent hRule leftDeriv ih =>
      exact (linearNormBinary_children_reachable_v49 ih hRule.1).2

/-- Every retained yield-typed state lies over the polynomial label support. -/
theorem trimmedLinearNorm_typedKept_label_reachable_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    {rules : List (PreparedLinearRule N Sigma)} {start : N → Prop}
    {X : TypedNT (LinearNormNT N Sigma) Obs}
    (hKeep : TypedKept Obs
      (TrimmedLinearNormTerminal rules start)
      (TrimmedLinearNormBinary rules start)
      (TrimmedLinearNormStart rules start) X) :
    X.label ∈ linearNormReachableLabelsV49 rules := by
  rcases hKeep.2 with ⟨u, v, hOcc⟩
  exact trimmedLinearNorm_typedOccurs_label_reachable_v49 Obs hOcc

/-- Every prepared spine length is at most its encoded RHS length. -/
theorem preparedSpineOpsV49_length_le_rhsLength
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma) :
    (preparedSpineOpsV49 r).length ≤ r.rhsLength := by
  cases r with
  | context A body h =>
      exact context_spineOps_length_le_rhsLength_v49 (A := A) body h
  | terminal A body =>
      exact terminal_spineOps_length_le_rhsLength_v49 (A := A) body

/-- Total length of all suffix-entry lists is linearly bounded by rules plus RHS size. -/
theorem normalizationReachableEntriesV49_length_le
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    (normalizationReachableEntriesV49 rules).length ≤
      rules.length + preparedTotalRhsLength rules := by
  induction rules with
  | nil => simp [normalizationReachableEntriesV49, preparedTotalRhsLength]
  | cons r rs ih =>
      have hLocal := preparedSpineOpsV49_length_le_rhsLength r
      simp only [normalizationReachableEntriesV49, List.flatMap_cons,
        List.length_append, linearNormEntriesV49_length, List.length_cons,
        preparedTotalRhsLength, List.map_cons, List.sum_cons]
      omega

/-- Reachable normalized labels are linearly bounded by the prepared grammar size. -/
theorem linearNormReachableLabelsV49_card_le_preparedGrammarSize
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (rules : List (PreparedLinearRule N Sigma)) :
    (linearNormReachableLabelsV49 rules).card ≤ preparedGrammarSize rules 1 := by
  classical
  have hOld : (linearNormOldLabelsV49 (N := N) (Sigma := Sigma)).card ≤
      Fintype.card N := by
    unfold linearNormOldLabelsV49
    exact Finset.card_image_le
  have hWrap : (linearNormWrapperLabelsV49 (N := N) (Sigma := Sigma)).card ≤
      Fintype.card Sigma := by
    unfold linearNormWrapperLabelsV49
    exact Finset.card_image_le
  have hEntriesFinset : (linearNormReachableEntriesFinsetV49 rules).card ≤
      (normalizationReachableEntriesV49 rules).length := by
    unfold linearNormReachableEntriesFinsetV49
    exact List.toFinset_card_le _
  have hEntries := normalizationReachableEntriesV49_length_le rules
  have hFirst := Finset.card_union_le
    (linearNormOldLabelsV49 (N := N) (Sigma := Sigma))
    (linearNormWrapperLabelsV49 (N := N) (Sigma := Sigma))
  have hSecond := Finset.card_union_le
    (linearNormOldLabelsV49 (N := N) (Sigma := Sigma) ∪
      linearNormWrapperLabelsV49 (N := N) (Sigma := Sigma))
    (linearNormReachableEntriesFinsetV49 rules)
  unfold linearNormReachableLabelsV49 preparedGrammarSize
  omega

/-- Typed reachable support: polynomial labels crossed with the fixed observer monoid. -/
noncomputable def linearNormReachableTypedFinsetV49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma) (rules : List (PreparedLinearRule N Sigma)) :
    Finset (TypedNT (LinearNormNT N Sigma) Obs) := by
  classical
  exact ((linearNormReachableLabelsV49 rules).product
    (Finset.univ : Finset Obs.M)).image
      (fun p => { label := p.1, yieldType := p.2 })

/-- A retained typed state belongs to the polynomial typed support. -/
theorem typedKept_mem_reachableTypedFinset_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    (rules : List (PreparedLinearRule N Sigma)) (start : N → Prop)
    (X : KeptState Obs
      (TrimmedLinearNormTerminal rules start)
      (TrimmedLinearNormBinary rules start)
      (TrimmedLinearNormStart rules start)) :
    X.1 ∈ linearNormReachableTypedFinsetV49 Obs rules := by
  classical
  rcases X.1 with ⟨label, mu⟩
  have hLabel := trimmedLinearNorm_typedKept_label_reachable_v49 Obs X.property
  simp [linearNormReachableTypedFinsetV49, hLabel]

/-- Inject retained typed states into the polynomial typed support. -/
noncomputable def keptStateToReachableTypedV49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    (rules : List (PreparedLinearRule N Sigma)) (start : N → Prop)
    (X : KeptState Obs
      (TrimmedLinearNormTerminal rules start)
      (TrimmedLinearNormBinary rules start)
      (TrimmedLinearNormStart rules start)) :
    ↥(linearNormReachableTypedFinsetV49 Obs rules) :=
  ⟨X.1, typedKept_mem_reachableTypedFinset_v49 Obs rules start X⟩

/-- The reachable-support embedding is injective. -/
theorem keptStateToReachableTypedV49_injective
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    (rules : List (PreparedLinearRule N Sigma)) (start : N → Prop) :
    Function.Injective (keptStateToReachableTypedV49 Obs rules start) := by
  intro X Y h
  apply Subtype.ext
  exact congrArg Subtype.val h

/-- The typed support has at most `labels * |M|` elements. -/
theorem linearNormReachableTypedFinsetV49_card_le
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma) (rules : List (PreparedLinearRule N Sigma)) :
    (linearNormReachableTypedFinsetV49 Obs rules).card ≤
      (linearNormReachableLabelsV49 rules).card * Fintype.card Obs.M := by
  classical
  unfold linearNormReachableTypedFinsetV49
  exact le_trans Finset.card_image_le (by simp)

/-- Retained typed-state cardinality is polynomially controlled by prepared size. -/
theorem trimmedLinearNorm_keptState_card_le_prepared_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    (rules : List (PreparedLinearRule N Sigma)) (start : N → Prop) :
    letI := trimmedLinearNormKeptStateFintypeV49 Obs rules start
    Fintype.card (KeptState Obs
      (TrimmedLinearNormTerminal rules start)
      (TrimmedLinearNormBinary rules start)
      (TrimmedLinearNormStart rules start)) ≤
      preparedGrammarSize rules 1 * Fintype.card Obs.M := by
  letI := trimmedLinearNormKeptStateFintypeV49 Obs rules start
  have hInject :
      Fintype.card (KeptState Obs
        (TrimmedLinearNormTerminal rules start)
        (TrimmedLinearNormBinary rules start)
        (TrimmedLinearNormStart rules start)) ≤
        Fintype.card ↥(linearNormReachableTypedFinsetV49 Obs rules) := by
    exact Fintype.card_le_of_injective
      (keptStateToReachableTypedV49 Obs rules start)
      (keptStateToReachableTypedV49_injective Obs rules start)
  have hTyped := linearNormReachableTypedFinsetV49_card_le Obs rules
  have hLabels := linearNormReachableLabelsV49_card_le_preparedGrammarSize rules
  simpa using le_trans hInject
    (le_trans (by simpa using hTyped)
      (Nat.mul_le_mul_right (Fintype.card Obs.M) hLabels))

/--
Source-level retained-state bound.  For fixed `h` the monoid factor is a
constant, while the normalization factor is the explicit quadratic source
envelope from `LinearNormalizationSourceSizeV49`.
-/
theorem sourceNormalized_keptState_card_le_sourcePolynomial_v49
    {N : Type v} {Sigma : Type u} [Fintype N] [Fintype Sigma]
    (Obs : Observer Sigma)
    (sourceRules : List (SourceLinearRule N Sigma)) (S : N) :
    letI := sourceNormalizedKeptStateFintypeV49 Obs sourceRules S
    Fintype.card (KeptState Obs
      (SourceNormalizedTerminalV49 sourceRules S)
      (SourceNormalizedBinaryV49 sourceRules S)
      (SourceNormalizedStartV49 sourceRules S)) ≤
      sourceLinearNormalizationPolynomial sourceRules * Fintype.card Obs.M := by
  letI := sourceNormalizedKeptStateFintypeV49 Obs sourceRules S
  have hPrepared := trimmedLinearNorm_keptState_card_le_prepared_v49
    Obs (enumeratePreparedLinearRules sourceRules) (SourceSeparatedStart S)
  have hSize := enumerated_preparedGrammarSize_le_sourcePolynomial_v49 sourceRules
  exact le_trans hPrepared
    (Nat.mul_le_mul_right (Fintype.card Obs.M) hSize)

end FixedHCFGv44
end LeanCfgProject
