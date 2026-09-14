import LeanCfgProject.FixedHCFGv44.LinearNormalizationPreparedSemanticsV49
import LeanCfgProject.FixedHCFGv44.YieldTypedCore

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Explicit SSBNF reification layer for Appendix A of TCS v49.

The preceding files prove the wrapper-chain factorization semantically and
bound its grammar-level size.  This file turns the contracted spine programs
into genuine terminal/binary productions over an enlarged nonterminal type.

The construction uses shared wrapper symbols `W_a`, a production-local stage
symbol carrying the unconsumed spine program, and a final terminal state for
terminal-only productions.  The stage representation is extensional rather
than an implementation of the manuscript's concrete `R/J/Theta` names, but
its terminal/binary rule shape is exactly SSBNF: every non-start production is
of the form `X -> a` or `X -> Y Z`.

This first reification layer proves the forward semantic direction: every
contracted prepared derivation has an explicit SSBNF derivation with the same
yield.  The converse/no-spurious-derivations direction is isolated for the
next layer.
-/

/-- Explicit nonterminals used by the reified wrapper-chain grammar. -/
inductive LinearNormNT (N : Type v) (Sigma : Type u) where
  | old (A : N)
  | wrap (a : Sigma)
  | stage (r : PreparedLinearRule N Sigma) (ops : List (LinearSpineOp Sigma))
  | terminalEnd (r : PreparedLinearRule N Sigma)

namespace LinearNormNT

/-- Final continuing state after all spine operations of one production. -/
def ruleCore
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma) : LinearNormNT N Sigma :=
  match r with
  | .context _ body _ => .old body.center
  | .terminal _ _ => .terminalEnd r

/-- State at which a remaining spine program begins. -/
def entry
    {N : Type v} {Sigma : Type u}
    (r : PreparedLinearRule N Sigma) :
    List (LinearSpineOp Sigma) → LinearNormNT N Sigma
  | [] => ruleCore r
  | ops => .stage r ops

end LinearNormNT

/-- Terminal productions of the explicit normalized grammar. -/
inductive LinearNormTerminal
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    LinearNormNT N Sigma → Sigma → Prop
  | wrapper (a : Sigma) :
      LinearNormTerminal rules (.wrap a) a
  | terminalDirect
      {A : N} {body : NonemptyTerminalBody Sigma}
      (hrule : PreparedLinearRule.terminal A body ∈ rules)
      (hempty : body.initial = []) :
      LinearNormTerminal rules (.old A) body.finalSymbol
  | terminalEnd
      {A : N} {body : NonemptyTerminalBody Sigma}
      (hrule : PreparedLinearRule.terminal A body ∈ rules) :
      LinearNormTerminal rules
        (.terminalEnd (PreparedLinearRule.terminal A body)) body.finalSymbol

/-- Binary productions of the explicit normalized grammar. -/
inductive LinearNormBinary
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    LinearNormNT N Sigma → LinearNormNT N Sigma → LinearNormNT N Sigma → Prop
  | contextRootLeft
      {A : N} {body : LinearContextBody N Sigma} {h : body.Nonunit}
      {a : Sigma} {rest : List (LinearSpineOp Sigma)}
      (hrule : PreparedLinearRule.context A body h ∈ rules)
      (hops : body.spineOps = LinearSpineOp.left a :: rest) :
      LinearNormBinary rules (.old A) (.wrap a)
        (LinearNormNT.entry (PreparedLinearRule.context A body h) rest)
  | contextRootRight
      {A : N} {body : LinearContextBody N Sigma} {h : body.Nonunit}
      {a : Sigma} {rest : List (LinearSpineOp Sigma)}
      (hrule : PreparedLinearRule.context A body h ∈ rules)
      (hops : body.spineOps = LinearSpineOp.right a :: rest) :
      LinearNormBinary rules (.old A)
        (LinearNormNT.entry (PreparedLinearRule.context A body h) rest)
        (.wrap a)
  | terminalRootLeft
      {A : N} {body : NonemptyTerminalBody Sigma}
      {a : Sigma} {rest : List (LinearSpineOp Sigma)}
      (hrule : PreparedLinearRule.terminal A body ∈ rules)
      (hops : body.spineOps = LinearSpineOp.left a :: rest) :
      LinearNormBinary rules (.old A) (.wrap a)
        (LinearNormNT.entry (PreparedLinearRule.terminal A body) rest)
  | stageLeft
      {r : PreparedLinearRule N Sigma}
      {a : Sigma} {rest : List (LinearSpineOp Sigma)}
      (hrule : r ∈ rules) :
      LinearNormBinary rules (.stage r (LinearSpineOp.left a :: rest))
        (.wrap a) (LinearNormNT.entry r rest)
  | stageRight
      {r : PreparedLinearRule N Sigma}
      {a : Sigma} {rest : List (LinearSpineOp Sigma)}
      (hrule : r ∈ rules) :
      LinearNormBinary rules (.stage r (LinearSpineOp.right a :: rest))
        (LinearNormNT.entry r rest) (.wrap a)

/-- Genuine SSBNF derivation relation of the reified normalization. -/
abbrev LinearNormDerives
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :=
  UntypedDerives (LinearNormTerminal rules) (LinearNormBinary rules)

/-- Every wrapper symbol derives exactly its one terminal in the forward construction. -/
theorem linearNorm_wrap_derives
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) (a : Sigma) :
    LinearNormDerives rules (.wrap a) [a] := by
  exact UntypedDerives.terminal (LinearNormTerminal.wrapper a)

/--
A remaining spine program can be realized by actual binary SSBNF rules once
its core state has a derivation.
-/
theorem linearNorm_entry_derives
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {r : PreparedLinearRule N Sigma}
    (hrule : r ∈ rules)
    (ops : List (LinearSpineOp Sigma))
    {z : Word Sigma}
    (hcore : LinearNormDerives rules (LinearNormNT.ruleCore r) z) :
    LinearNormDerives rules (LinearNormNT.entry r ops)
      (evalLinearSpineOps ops z) := by
  induction ops with
  | nil =>
      simpa [LinearNormNT.entry, evalLinearSpineOps] using hcore
  | cons op rest ih =>
      cases op with
      | left a =>
          have hwrap := linearNorm_wrap_derives rules a
          have hbin :
              LinearNormBinary rules
                (.stage r (LinearSpineOp.left a :: rest))
                (.wrap a) (LinearNormNT.entry r rest) :=
            LinearNormBinary.stageLeft hrule
          have hd := UntypedDerives.binary hbin hwrap ih
          simpa [LinearNormNT.entry, evalLinearSpineOps,
            applyLinearSpineOp] using hd
      | right a =>
          have hwrap := linearNorm_wrap_derives rules a
          have hbin :
              LinearNormBinary rules
                (.stage r (LinearSpineOp.right a :: rest))
                (LinearNormNT.entry r rest) (.wrap a) :=
            LinearNormBinary.stageRight hrule
          have hd := UntypedDerives.binary hbin ih hwrap
          simpa [LinearNormNT.entry, evalLinearSpineOps,
            applyLinearSpineOp] using hd

/-- Reify one non-unit context production at its original left-hand side. -/
theorem linearNorm_context_root_derives
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {A : N} {body : LinearContextBody N Sigma} {h : body.Nonunit}
    {z : Word Sigma}
    (hrule : PreparedLinearRule.context A body h ∈ rules)
    (hcenter : LinearNormDerives rules (.old body.center) z) :
    LinearNormDerives rules (.old A)
      (evalLinearSpineOps body.spineOps z) := by
  have hpos := body.spineOps_length_pos_of_nonunit h
  cases hops : body.spineOps with
  | nil =>
      simp [hops] at hpos
  | cons op rest =>
      have htail :
          LinearNormDerives rules
            (LinearNormNT.entry (PreparedLinearRule.context A body h) rest)
            (evalLinearSpineOps rest z) := by
        apply linearNorm_entry_derives hrule rest
        simpa [LinearNormNT.ruleCore] using hcenter
      cases op with
      | left a =>
          have hwrap := linearNorm_wrap_derives rules a
          have hbin :
              LinearNormBinary rules (.old A) (.wrap a)
                (LinearNormNT.entry (PreparedLinearRule.context A body h) rest) :=
            LinearNormBinary.contextRootLeft hrule hops
          have hd := UntypedDerives.binary hbin hwrap htail
          simpa [hops, evalLinearSpineOps, applyLinearSpineOp] using hd
      | right a =>
          have hwrap := linearNorm_wrap_derives rules a
          have hbin :
              LinearNormBinary rules (.old A)
                (LinearNormNT.entry (PreparedLinearRule.context A body h) rest)
                (.wrap a) :=
            LinearNormBinary.contextRootRight hrule hops
          have hd := UntypedDerives.binary hbin htail hwrap
          simpa [hops, evalLinearSpineOps, applyLinearSpineOp] using hd

/-- Reify one terminal-only prepared production at its original left-hand side. -/
theorem linearNorm_terminal_root_derives
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {A : N} {body : NonemptyTerminalBody Sigma}
    (hrule : PreparedLinearRule.terminal A body ∈ rules) :
    LinearNormDerives rules (.old A)
      (evalLinearSpineOps body.spineOps [body.finalSymbol]) := by
  cases hinit : body.initial with
  | nil =>
      have hterm : LinearNormTerminal rules (.old A) body.finalSymbol :=
        LinearNormTerminal.terminalDirect hrule hinit
      have hd : LinearNormDerives rules (.old A) [body.finalSymbol] :=
        UntypedDerives.terminal hterm
      simpa [NonemptyTerminalBody.spineOps, hinit, evalLinearSpineOps] using hd
  | cons a tail =>
      have hcore :
          LinearNormDerives rules
            (.terminalEnd (PreparedLinearRule.terminal A body))
            [body.finalSymbol] := by
        exact UntypedDerives.terminal (LinearNormTerminal.terminalEnd hrule)
      have htail :
          LinearNormDerives rules
            (LinearNormNT.entry (PreparedLinearRule.terminal A body)
              (tail.map LinearSpineOp.left))
            (evalLinearSpineOps (tail.map LinearSpineOp.left)
              [body.finalSymbol]) := by
        apply linearNorm_entry_derives hrule
          (tail.map LinearSpineOp.left)
        simpa [LinearNormNT.ruleCore] using hcore
      have hwrap := linearNorm_wrap_derives rules a
      have hops :
          body.spineOps =
            LinearSpineOp.left a :: tail.map LinearSpineOp.left := by
        simp [NonemptyTerminalBody.spineOps, hinit]
      have hbin :
          LinearNormBinary rules (.old A) (.wrap a)
            (LinearNormNT.entry (PreparedLinearRule.terminal A body)
              (tail.map LinearSpineOp.left)) :=
        LinearNormBinary.terminalRootLeft hrule hops
      have hd := UntypedDerives.binary hbin hwrap htail
      simpa [hops, evalLinearSpineOps, applyLinearSpineOp] using hd

/--
Every contracted prepared derivation reifies to an actual terminal/binary
SSBNF derivation over `LinearNormNT`.
-/
theorem contracted_to_explicit_ssbnf
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {A : N} {w : Word Sigma}
    (d : ContractedLinearDerives rules A w) :
    LinearNormDerives rules (.old A) w := by
  induction d with
  | @context A body h z hrule center ih =>
      exact linearNorm_context_root_derives hrule ih
  | @terminal A body hrule =>
      exact linearNorm_terminal_root_derives hrule

/-- Start semantics of the explicit SSBNF reification. -/
inductive ExplicitLinearNormStartDerives
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) : Word Sigma → Prop
  | epsilon (h : epsilonStart) :
      ExplicitLinearNormStartDerives rules start epsilonStart []
  | nonempty
      {A : N} {w : Word Sigma}
      (hrule : start A)
      (hder : LinearNormDerives rules (.old A) w) :
      ExplicitLinearNormStartDerives rules start epsilonStart w

/-- Every contracted normalized start derivation has an explicit SSBNF derivation. -/
theorem contracted_start_to_explicit_ssbnf
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {start : N → Prop} {epsilonStart : Prop}
    {w : Word Sigma}
    (d : ContractedLinearStartDerives rules start epsilonStart w) :
    ExplicitLinearNormStartDerives rules start epsilonStart w := by
  cases d with
  | epsilon h => exact ExplicitLinearNormStartDerives.epsilon h
  | nonempty hrule hder =>
      exact ExplicitLinearNormStartDerives.nonempty hrule
        (contracted_to_explicit_ssbnf hder)

/-- Language generated by the explicit SSBNF reification. -/
def ExplicitLinearNormLanguage
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) : Language Sigma :=
  fun w => ExplicitLinearNormStartDerives rules start epsilonStart w

/-- Forward language inclusion for the actual SSBNF reification. -/
theorem contractedLanguage_subset_explicitSSBNF_v49
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) :
    ContractedLinearLanguage rules start epsilonStart ⊆
      ExplicitLinearNormLanguage rules start epsilonStart := by
  intro w hw
  exact contracted_start_to_explicit_ssbnf hw

/-- Consequently the prepared grammar is included in its explicit SSBNF reification. -/
theorem preparedLanguage_subset_explicitSSBNF_v49
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) :
    PreparedLinearLanguage rules start epsilonStart ⊆
      ExplicitLinearNormLanguage rules start epsilonStart := by
  intro w hw
  have hc : ContractedLinearLanguage rules start epsilonStart w :=
    (contracted_linear_start_language_iff rules start epsilonStart w).2 hw
  exact contracted_start_to_explicit_ssbnf hc

end FixedHCFGv44
end LeanCfgProject
