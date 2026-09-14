import LeanCfgProject.FixedHCFGv44.LinearNormalizationGrammarSizeV49
import LeanCfgProject.FixedHCFGv44.Language

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
Recursive semantic layer for the prepared-grammar phase of Appendix A.

`LinearNormalizationCoreV49` verifies each individual wrapper-chain
factorization, and `LinearNormalizationGrammarSizeV49` verifies the summed
post-preprocessing size bounds.  Here we lift the local yield equalities through
arbitrarily deep recursive derivations of a finite prepared linear grammar.

This is still deliberately one layer short of the final SSBNF construction:
we use the contracted spine semantics rather than explicit fresh `R/J/Theta`
nonterminals.  Thus this file proves whole-prepared-grammar language
preservation of the factorization, while the later construction layer must
reify those contracted steps as actual terminal/binary SSBNF rules.
-/

/-- Ordinary derivation semantics of a prepared linear grammar. -/
inductive PreparedLinearDerives
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    N → Word Sigma → Prop
  | context
      {A : N} {body : LinearContextBody N Sigma}
      {h : body.Nonunit} {z : Word Sigma}
      (hrule : PreparedLinearRule.context A body h ∈ rules)
      (center : PreparedLinearDerives rules body.center z) :
      PreparedLinearDerives rules A (body.left ++ z ++ body.right)
  | terminal
      {A : N} {body : NonemptyTerminalBody Sigma}
      (hrule : PreparedLinearRule.terminal A body ∈ rules) :
      PreparedLinearDerives rules A body.word

/--
Contracted normalization semantics: every prepared production is interpreted
through the exact spine program proved correct in `LinearNormalizationCoreV49`.
-/
inductive ContractedLinearDerives
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma)) :
    N → Word Sigma → Prop
  | context
      {A : N} {body : LinearContextBody N Sigma}
      {h : body.Nonunit} {z : Word Sigma}
      (hrule : PreparedLinearRule.context A body h ∈ rules)
      (center : ContractedLinearDerives rules body.center z) :
      ContractedLinearDerives rules A
        (evalLinearSpineOps body.spineOps z)
  | terminal
      {A : N} {body : NonemptyTerminalBody Sigma}
      (hrule : PreparedLinearRule.terminal A body ∈ rules) :
      ContractedLinearDerives rules A
        (evalLinearSpineOps body.spineOps [body.finalSymbol])

/-- One prepared derivation lifts to the contracted normalized semantics. -/
theorem prepared_to_contracted
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {A : N} {w : Word Sigma}
    (d : PreparedLinearDerives rules A w) :
    ContractedLinearDerives rules A w := by
  induction d with
  | @context A body h z hrule center ih =>
      have hd : ContractedLinearDerives rules A
          (evalLinearSpineOps body.spineOps z) :=
        ContractedLinearDerives.context hrule ih
      have hEq :
          evalLinearSpineOps body.spineOps z =
            body.left ++ z ++ body.right := by
        simpa [LinearContextBody.spineOps] using
          (eval_contextSpineOps body.left body.right z)
      simpa [hEq] using hd
  | @terminal A body hrule =>
      have hd : ContractedLinearDerives rules A
          (evalLinearSpineOps body.spineOps [body.finalSymbol]) :=
        ContractedLinearDerives.terminal hrule
      have hEq :
          evalLinearSpineOps body.spineOps [body.finalSymbol] = body.word :=
        body.eval_spineOps
      simpa [hEq] using hd

/-- Contracted normalized semantics erases back to the prepared derivation. -/
theorem contracted_to_prepared
    {N : Type v} {Sigma : Type u}
    {rules : List (PreparedLinearRule N Sigma)}
    {A : N} {w : Word Sigma}
    (d : ContractedLinearDerives rules A w) :
    PreparedLinearDerives rules A w := by
  induction d with
  | @context A body h z hrule center ih =>
      have hd : PreparedLinearDerives rules A
          (body.left ++ z ++ body.right) :=
        PreparedLinearDerives.context hrule ih
      have hEq :
          evalLinearSpineOps body.spineOps z =
            body.left ++ z ++ body.right := by
        simpa [LinearContextBody.spineOps] using
          (eval_contextSpineOps body.left body.right z)
      simpa [hEq] using hd
  | @terminal A body hrule =>
      have hd : PreparedLinearDerives rules A body.word :=
        PreparedLinearDerives.terminal hrule
      have hEq :
          evalLinearSpineOps body.spineOps [body.finalSymbol] = body.word :=
        body.eval_spineOps
      simpa [hEq] using hd

/-- Exact non-start language preservation for every prepared nonterminal. -/
theorem contracted_linear_language_iff
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (A : N) (w : Word Sigma) :
    ContractedLinearDerives rules A w ↔ PreparedLinearDerives rules A w := by
  constructor
  · exact contracted_to_prepared
  · exact prepared_to_contracted

/-- Start semantics of a prepared grammar after the manuscript's separation. -/
inductive PreparedLinearStartDerives
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) : Word Sigma → Prop
  | epsilon (h : epsilonStart) :
      PreparedLinearStartDerives rules start epsilonStart []
  | nonempty
      {A : N} {w : Word Sigma}
      (hrule : start A)
      (hder : PreparedLinearDerives rules A w) :
      PreparedLinearStartDerives rules start epsilonStart w

/-- Start semantics after contracting all Appendix A wrapper chains. -/
inductive ContractedLinearStartDerives
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) : Word Sigma → Prop
  | epsilon (h : epsilonStart) :
      ContractedLinearStartDerives rules start epsilonStart []
  | nonempty
      {A : N} {w : Word Sigma}
      (hrule : start A)
      (hder : ContractedLinearDerives rules A w) :
      ContractedLinearStartDerives rules start epsilonStart w

/-- Whole prepared start language is preserved by the contracted normalization. -/
theorem contracted_linear_start_language_iff
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop)
    (w : Word Sigma) :
    ContractedLinearStartDerives rules start epsilonStart w ↔
      PreparedLinearStartDerives rules start epsilonStart w := by
  constructor
  · intro d
    cases d with
    | epsilon h => exact PreparedLinearStartDerives.epsilon h
    | nonempty hrule hder =>
        exact PreparedLinearStartDerives.nonempty hrule
          (contracted_to_prepared hder)
  · intro d
    cases d with
    | epsilon h => exact ContractedLinearStartDerives.epsilon h
    | nonempty hrule hder =>
        exact ContractedLinearStartDerives.nonempty hrule
          (prepared_to_contracted hder)

/-- Language-valued form of the prepared normalization equivalence. -/
def PreparedLinearLanguage
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) : Language Sigma :=
  fun w => PreparedLinearStartDerives rules start epsilonStart w

/-- Language-valued form of the contracted normalization. -/
def ContractedLinearLanguage
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) : Language Sigma :=
  fun w => ContractedLinearStartDerives rules start epsilonStart w

/--
Whole-grammar semantic contract for the post-preprocessing wrapper-chain phase
of Appendix A.
-/
theorem linearNormalization_prepared_language_eq_v49
    {N : Type v} {Sigma : Type u}
    (rules : List (PreparedLinearRule N Sigma))
    (start : N → Prop) (epsilonStart : Prop) :
    ContractedLinearLanguage rules start epsilonStart =
      PreparedLinearLanguage rules start epsilonStart := by
  ext w
  exact contracted_linear_start_language_iff
    rules start epsilonStart w

end FixedHCFGv44
end LeanCfgProject
