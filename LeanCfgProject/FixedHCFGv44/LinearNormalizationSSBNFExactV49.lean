import LeanCfgProject.FixedHCFGv44.LinearNormalizationSSBNFReificationV49

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Exactness of the explicit SSBNF reification for Appendix A of TCS v49.

`LinearNormalizationSSBNFReificationV49` constructs genuine terminal/binary
rules and proves the forward inclusion from the contracted normalization.
Here we prove that those explicit rules have no spurious derivations.  The key
invariant interprets every auxiliary stage state by the remaining contracted
spine program, so a single induction on an SSBNF derivation covers old
nonterminals, wrappers, intermediate stages, and terminal-chain endpoints.
-/

/-- Contracted meaning of the final core state of one prepared production. -/
def LinearNormCoreSemantics
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (r : PreparedLinearRule N Sigma)
    (w : Word Sigma) : Prop :=
  match r with
  | .context _ body _ => ContractedLinearDerives rules body.center w
  | .terminal _ body => w = [body.finalSymbol]

/-- Semantic invariant for every nonterminal of the explicit SSBNF grammar. -/
def LinearNormNTSemantics
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    LinearNormNT N Sigma → Word Sigma → Prop
  | .old A, w => ContractedLinearDerives rules A w
  | .wrap a, w => w = [a]
  | .stage r ops, w =>
      ∃ z, LinearNormCoreSemantics rules r z ∧
        w = evalLinearSpineOps ops z
  | .terminalEnd r, w => LinearNormCoreSemantics rules r w

/-- The explicit `ruleCore` state has exactly the contracted core semantics. -/
theorem linearNorm_ruleCore_semantics_iff
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (r : PreparedLinearRule N Sigma)
    (w : Word Sigma) :
    LinearNormNTSemantics rules (LinearNormNT.ruleCore r) w ↔
      LinearNormCoreSemantics rules r w := by
  cases r <;> rfl

/-- The `entry` state denotes evaluation of precisely the remaining spine. -/
theorem linearNorm_entry_semantics_iff
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (r : PreparedLinearRule N Sigma)
    (ops : List (LinearSpineOp Sigma))
    (w : Word Sigma) :
    LinearNormNTSemantics rules (LinearNormNT.entry r ops) w ↔
      ∃ z, LinearNormCoreSemantics rules r z ∧
        w = evalLinearSpineOps ops z := by
  cases ops with
  | nil =>
      constructor
      · intro h
        have hc : LinearNormCoreSemantics rules r w :=
          (linearNorm_ruleCore_semantics_iff rules r w).1
            (by simpa [LinearNormNT.entry] using h)
        exact ⟨w, hc, by simp [evalLinearSpineOps]⟩
      · rintro ⟨z, hz, hw⟩
        have hwz : w = z := by simpa [evalLinearSpineOps] using hw
        subst z
        have hs :
            LinearNormNTSemantics rules (LinearNormNT.ruleCore r) w :=
          (linearNorm_ruleCore_semantics_iff rules r w).2 hz
        simpa [LinearNormNT.entry] using hs
  | cons op rest =>
      rfl

/--
Every derivation in the explicit terminal/binary grammar satisfies the
contracted semantic invariant attached to its root nonterminal.
-/
theorem linearNorm_explicit_derivation_sound
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {X : LinearNormNT N Sigma} {w : Word Sigma}
    (d : LinearNormDerives rules X w) :
    LinearNormNTSemantics rules X w := by
  induction d with
  | @terminal X a hrule =>
      cases hrule with
      | wrapper a =>
          rfl
      | @terminalDirect A body hrule hempty =>
          have hd : ContractedLinearDerives rules A
              (evalLinearSpineOps body.spineOps [body.finalSymbol]) :=
            ContractedLinearDerives.terminal hrule
          simpa [LinearNormNTSemantics, NonemptyTerminalBody.spineOps,
            hempty, evalLinearSpineOps] using hd
      | @terminalEnd A body hrule =>
          rfl
  | @binary X Y Z x y hrule left right ihLeft ihRight =>
      cases hrule with
      | @contextRootLeft A body h a rest hrule hops =>
          have hx : x = [a] := by
            simpa [LinearNormNTSemantics] using ihLeft
          rcases
              (linearNorm_entry_semantics_iff rules
                (PreparedLinearRule.context A body h) rest y).1 ihRight with
            ⟨z, hcore, hy⟩
          have hcenter : ContractedLinearDerives rules body.center z := by
            simpa [LinearNormCoreSemantics] using hcore
          have hd : ContractedLinearDerives rules A
              (evalLinearSpineOps body.spineOps z) :=
            ContractedLinearDerives.context hrule hcenter
          change ContractedLinearDerives rules A (x ++ y)
          rw [hx, hy]
          simpa [hops, evalLinearSpineOps, applyLinearSpineOp] using hd
      | @contextRootRight A body h a rest hrule hops =>
          rcases
              (linearNorm_entry_semantics_iff rules
                (PreparedLinearRule.context A body h) rest x).1 ihLeft with
            ⟨z, hcore, hx⟩
          have hy : y = [a] := by
            simpa [LinearNormNTSemantics] using ihRight
          have hcenter : ContractedLinearDerives rules body.center z := by
            simpa [LinearNormCoreSemantics] using hcore
          have hd : ContractedLinearDerives rules A
              (evalLinearSpineOps body.spineOps z) :=
            ContractedLinearDerives.context hrule hcenter
          change ContractedLinearDerives rules A (x ++ y)
          rw [hx, hy]
          simpa [hops, evalLinearSpineOps, applyLinearSpineOp,
            List.append_assoc] using hd
      | @terminalRootLeft A body a rest hrule hops =>
          have hx : x = [a] := by
            simpa [LinearNormNTSemantics] using ihLeft
          rcases
              (linearNorm_entry_semantics_iff rules
                (PreparedLinearRule.terminal A body) rest y).1 ihRight with
            ⟨z, hcore, hy⟩
          have hz : z = [body.finalSymbol] := by
            simpa [LinearNormCoreSemantics] using hcore
          have hd : ContractedLinearDerives rules A
              (evalLinearSpineOps body.spineOps [body.finalSymbol]) :=
            ContractedLinearDerives.terminal hrule
          change ContractedLinearDerives rules A (x ++ y)
          rw [hx, hy, hz]
          simpa [hops, evalLinearSpineOps, applyLinearSpineOp] using hd
      | @stageLeft r a rest hrule =>
          have hx : x = [a] := by
            simpa [LinearNormNTSemantics] using ihLeft
          rcases
              (linearNorm_entry_semantics_iff rules r rest y).1 ihRight with
            ⟨z, hcore, hy⟩
          change ∃ z, LinearNormCoreSemantics rules r z ∧
            x ++ y = evalLinearSpineOps (LinearSpineOp.left a :: rest) z
          refine ⟨z, hcore, ?_⟩
          rw [hx, hy]
          simp [evalLinearSpineOps, applyLinearSpineOp]
      | @stageRight r a rest hrule =>
          rcases
              (linearNorm_entry_semantics_iff rules r rest x).1 ihLeft with
            ⟨z, hcore, hx⟩
          have hy : y = [a] := by
            simpa [LinearNormNTSemantics] using ihRight
          change ∃ z, LinearNormCoreSemantics rules r z ∧
            x ++ y = evalLinearSpineOps (LinearSpineOp.right a :: rest) z
          refine ⟨z, hcore, ?_⟩
          rw [hx, hy]
          simp [evalLinearSpineOps, applyLinearSpineOp, List.append_assoc]

/-- No explicit SSBNF derivation rooted at an old symbol is spurious. -/
theorem explicit_ssbnf_to_contracted
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {A : N} {w : Word Sigma}
    (d : LinearNormDerives rules (.old A) w) :
    ContractedLinearDerives rules A w := by
  simpa [LinearNormNTSemantics] using
    (linearNorm_explicit_derivation_sound d)

/-- Explicit start derivations erase exactly to the contracted normalization. -/
theorem explicit_start_to_contracted
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {start : N → Prop} {epsilonStart : Prop}
    {w : Word Sigma}
    (d : ExplicitLinearNormStartDerives rules start epsilonStart w) :
    ContractedLinearStartDerives rules start epsilonStart w := by
  cases d with
  | epsilon h => exact ContractedLinearStartDerives.epsilon h
  | nonempty hrule hder =>
      exact ContractedLinearStartDerives.nonempty hrule
        (explicit_ssbnf_to_contracted hder)

/-- Exact language equivalence between the explicit SSBNF and contracted semantics. -/
theorem explicitSSBNF_language_eq_contracted_v49
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) :
    ExplicitLinearNormLanguage rules start epsilonStart =
      ContractedLinearLanguage rules start epsilonStart := by
  ext w
  constructor
  · exact explicit_start_to_contracted
  · exact contracted_start_to_explicit_ssbnf

/--
The actual terminal/binary SSBNF reification preserves the whole prepared
start language exactly.
-/
theorem linearNormalization_explicitSSBNF_language_eq_v49
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) :
    ExplicitLinearNormLanguage rules start epsilonStart =
      PreparedLinearLanguage rules start epsilonStart := by
  calc
    ExplicitLinearNormLanguage rules start epsilonStart =
        ContractedLinearLanguage rules start epsilonStart :=
      explicitSSBNF_language_eq_contracted_v49 rules start epsilonStart
    _ = PreparedLinearLanguage rules start epsilonStart :=
      linearNormalization_prepared_language_eq_v49 rules start epsilonStart

end FixedHCFGv44
end LeanCfgProject
