import LeanCfgProject.MCFGv4.Basic

/-!
# MCFGv4.StandardMCFG

Paper-facing syntax kernel for Definition `def:standard-mcfg` of the frozen
2026-09-07 manuscript.

A deliberate design choice is that rule children are a finite `List`, so rule
rank is arbitrary finite rank.  This avoids inheriting the terminal/binary
specialization used in early stages of the legacy `MCFG2` experiment.

The frozen manuscript builds linearity (each child-component variable occurs at
most once) into the standard MCFG presentation itself, while nondeletion is an
additional property.  It also requires the start symbol to have fan-out one.
Those two points are represented explicitly below.
-/

namespace MCFGv4

universe u v

/-- The nonterminal signature of a standard MCFG presentation. -/
structure MCFGSignature (N : Type v) where
  start : N
  arity : N → Nat
  arity_pos : ∀ A : N, 0 < arity A
  start_arity : arity start = 1

/-- A child-component variable `x_j^k` for one arbitrary-rank rule. -/
structure RuleVariable {N : Type v} (sig : MCFGSignature N) (children : List N) where
  child : Fin children.length
  component : Fin (sig.arity (children.get child))

/-- Atoms occurring in one MCFG rule template. -/
inductive TemplateAtom {N : Type v} (sig : MCFGSignature N)
    (α : Type u) (children : List N) where
  | terminal : α → TemplateAtom sig α children
  | variable : RuleVariable sig children → TemplateAtom sig α children

/-- A raw arbitrary-finite-rank MCFG rule template.

`components` represents the parent template tuple.  Its stored length equality
ensures that the number of template components is exactly the fan-out of the
left-hand side. -/
structure MCFGRule {N : Type v} (sig : MCFGSignature N) (α : Type u) where
  lhs : N
  children : List N
  components : List (List (TemplateAtom sig α children))
  components_length : components.length = sig.arity lhs

namespace MCFGRule

variable {N : Type v} {α : Type u} {sig : MCFGSignature N}

/-- Rule rank is the number of nonterminal children. -/
def rank (r : MCFGRule sig α) : Nat := r.children.length

/-- Variables occurring in the complete parent template, in scan order. -/
def usedVariables (r : MCFGRule sig α) : List (RuleVariable sig r.children) :=
  r.components.flatMap fun component =>
    component.filterMap fun atom =>
      match atom with
      | TemplateAtom.terminal _ => none
      | TemplateAtom.variable rv => some rv

/-- Linearity: no child-component variable occurs more than once in the complete
parent template tuple.  This is the manuscript's "at most once" requirement. -/
def Linear (r : MCFGRule sig α) : Prop :=
  r.usedVariables.Pairwise (fun x y => x ≠ y)

/-- Nondeletion: every component variable of every child occurs in the parent
template.  For a standard (hence linear) rule this is the manuscript's
"exactly once" condition. -/
def Nondeleting (r : MCFGRule sig α) : Prop :=
  ∀ (j : Fin r.children.length)
    (k : Fin (sig.arity (r.children.get j))),
    ({ child := j, component := k } : RuleVariable sig r.children) ∈ r.usedVariables

end MCFGRule

/-- A finite standard MCFG presentation matching Definition
`def:standard-mcfg` at the syntactic level.

The rule list is finite by construction; `Fintype N` and `Fintype α` record the
finiteness of the nonterminal and terminal alphabets.  `linear_rules` records the
linearity condition built into the manuscript's standard presentation. -/
structure StandardMCFG (N : Type v) (α : Type u) [Fintype N] [Fintype α] where
  sig : MCFGSignature N
  rules : List (MCFGRule sig α)
  linear_rules : ∀ r ∈ rules, r.Linear

namespace StandardMCFG

variable {N : Type v} {α : Type u} [Fintype N] [Fintype α]

/-- Maximum-rule-rank cap for a finite presentation. -/
def HasRuleRankCap (G : StandardMCFG N α) (b : Nat) : Prop :=
  ∀ r ∈ G.rules, r.rank ≤ b

/-- The fan-out is bounded by `f`. -/
def HasFanoutCap (G : StandardMCFG N α) (f : Nat) : Prop :=
  ∀ A : N, G.sig.arity A ≤ f

/-- All rules are nondeleting. -/
def IsNondeleting (G : StandardMCFG N α) : Prop :=
  ∀ r ∈ G.rules, r.Nondeleting

/-- Standard presentations are linear by definition. -/
theorem isLinear (G : StandardMCFG N α) :
    ∀ r ∈ G.rules, r.Linear := G.linear_rules

end StandardMCFG

end MCFGv4
