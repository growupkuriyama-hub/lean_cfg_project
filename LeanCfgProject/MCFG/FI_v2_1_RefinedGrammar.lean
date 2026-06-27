import LeanCfgProject.MCFG.FI_v2_1_OutputTypedDerivationSummary

/-!
# FI v2.1 Lean experiment: output-type refined grammar skeleton

This file is the seventeenth formalization layer for the FI v2.1 MCFG paper.

The previous layers introduced output-refined nonterminals and showed that
ordinary terminal, binary, and start derivation steps have output-typed
counterparts.  This file packages those refined steps into a lightweight
refined grammar skeleton.

The scope is still conservative: we do not yet construct a finite enumerated
refined grammar by ranging over a finite monoid.  Instead, we define an
output-type refined grammar as a predicate over packaged refined terminal,
binary, and start rules.  This is the semantic skeleton that a later finite
construction should instantiate by enumeration.

The main checked statement is soundness: every derivation in such a refined
rule system forgets to an ordinary derivation in the base grammar and has the
advertised componentwise output type.
-/

namespace FIv21

universe u v w

section RefinedGrammarSkeleton

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M]

/-- A lightweight output-type refined grammar over a fixed base grammar and
observation.

Instead of immediately enumerating all refined rules as finite lists, this
record stores predicates selecting which packaged refined terminal, binary, and
start rules are present.  A later file can instantiate these predicates by
finite enumeration when `[Fintype M]` and finite nonterminal/rule data are
available. -/
structure OutputTypeRefinedGrammar
    (G : WorkingMCFG N α) (obs : α → M) where
  HasTerminal : RefinedTerminalRule G obs → Prop
  HasBinary : RefinedBinaryRule G obs → Prop
  HasStart : RefinedStartRule G obs → Prop

namespace OutputTypeRefinedGrammar

/-- The maximal refined grammar skeleton: every packaged refined rule is
present.  This is useful as a semantic reference object before finite
enumeration is introduced. -/
def all (G : WorkingMCFG N α) (obs : α → M) :
    OutputTypeRefinedGrammar G obs :=
  { HasTerminal := fun _ => True
    HasBinary := fun _ => True
    HasStart := fun _ => True }

@[simp] theorem all_hasTerminal
    (G : WorkingMCFG N α) (obs : α → M)
    (ρ : RefinedTerminalRule G obs) :
    (all G obs).HasTerminal ρ := by
  trivial

@[simp] theorem all_hasBinary
    (G : WorkingMCFG N α) (obs : α → M)
    (ρ : RefinedBinaryRule G obs) :
    (all G obs).HasBinary ρ := by
  trivial

@[simp] theorem all_hasStart
    (G : WorkingMCFG N α) (obs : α → M)
    (ρ : RefinedStartRule G obs) :
    (all G obs).HasStart ρ := by
  trivial

/-- A refined grammar contains all refinements of the ordinary listed rules.

This is the natural completeness condition for the output-type refinement
skeleton: every well-typed/listed ordinary rule is available at every compatible
choice of output types. -/
def ContainsAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M}
    (RG : OutputTypeRefinedGrammar G obs) : Prop :=
  (∀ (ρ : TerminalRule N α) (hρ : ρ ∈ G.terminalRules),
      ∀ hwt : ρ.WellTyped G.arity,
        RG.HasTerminal
          { rule := ρ
            mem := hρ
            wellTyped := hwt }) ∧
  (∀ (ρ : BinaryRule N α G.arity) (hρ : ρ ∈ G.binaryRules),
      ∀ leftTy : Fin (G.arity ρ.left) → M,
      ∀ rightTy : Fin (G.arity ρ.right) → M,
        RG.HasBinary
          { rule := ρ
            mem := hρ
            leftTy := leftTy
            rightTy := rightTy }) ∧
  (∀ (ρ : StartRule N) (hρ : ρ ∈ G.startRules),
      ∀ hwt : ρ.WellTyped G,
      ∀ childTy : Fin (G.arity ρ.child) → M,
        RG.HasStart
          { rule := ρ
            mem := hρ
            wellTyped := hwt
            childTy := childTy })

/-- The maximal refined grammar contains all ordinary rule refinements. -/
theorem all_containsAllOrdinaryRuleRefinements
    (G : WorkingMCFG N α) (obs : α → M) :
    ContainsAllOrdinaryRuleRefinements (all G obs) := by
  constructor
  · intro ρ hρ hwt
    trivial
  constructor
  · intro ρ hρ leftTy rightTy
    trivial
  · intro ρ hρ hwt childTy
    trivial

end OutputTypeRefinedGrammar

/-- Derivability in an output-type refined grammar skeleton.

The constructors mirror the three refined rule kinds.  The target nonterminal
is already refined by its output type, so every constructor preserves the
advertised componentwise observation type by construction. -/
inductive RefinedDerivesTuple
    {G : WorkingMCFG N α} {obs : α → M}
    (RG : OutputTypeRefinedGrammar G obs) :
    (A : RefinedNonterminal G M) → Tuple α (G.arity A.base) → Prop
  | terminal (ρ : RefinedTerminalRule G obs)
      (hρ : RG.HasTerminal ρ) :
      RefinedDerivesTuple RG ρ.lhs ρ.outputTuple
  | binary (ρ : RefinedBinaryRule G obs)
      (hρ : RG.HasBinary ρ)
      (x : Tuple α (G.arity ρ.rule.left))
      (y : Tuple α (G.arity ρ.rule.right)) :
      RefinedDerivesTuple RG ρ.left x →
      RefinedDerivesTuple RG ρ.right y →
      RefinedDerivesTuple RG ρ.lhs (ρ.rule.apply x y)
  | start (ρ : RefinedStartRule G obs)
      (hρ : RG.HasStart ρ)
      (x : Tuple α (G.arity ρ.rule.child)) :
      RefinedDerivesTuple RG ρ.child x →
      RefinedDerivesTuple RG ρ.start (castTuple ρ.wellTyped x)

namespace RefinedDerivesTuple

/-- Forgetting a refined derivation gives an ordinary derivation together with
the advertised output type. -/
theorem sound
    {G : WorkingMCFG N α} {obs : α → M}
    {RG : OutputTypeRefinedGrammar G obs}
    {A : RefinedNonterminal G M}
    {x : Tuple α (G.arity A.base)}
    (h : RefinedDerivesTuple RG A x) :
    DerivesOutputTypedTuple G obs A x := by
  induction h with
  | terminal ρ hρ =>
      exact RefinedTerminalRule.derives ρ
  | binary ρ hρ x y hx hy ihx ihy =>
      exact RefinedBinaryRule.derives ρ x y ihx ihy
  | start ρ hρ x hx ihx =>
      exact RefinedStartRule.derives ρ x ihx

/-- The ordinary derivation obtained by forgetting the refined grammar. -/
theorem forgets_to_derivation
    {G : WorkingMCFG N α} {obs : α → M}
    {RG : OutputTypeRefinedGrammar G obs}
    {A : RefinedNonterminal G M}
    {x : Tuple α (G.arity A.base)}
    (h : RefinedDerivesTuple RG A x) :
    DerivesTuple G A.base x :=
  DerivesOutputTypedTuple.derives (sound h)

/-- A refined derivation has the output type attached to its refined
nonterminal. -/
theorem has_output_type
    {G : WorkingMCFG N α} {obs : α → M}
    {RG : OutputTypeRefinedGrammar G obs}
    {A : RefinedNonterminal G M}
    {x : Tuple α (G.arity A.base)}
    (h : RefinedDerivesTuple RG A x) :
    tupleType obs x = A.outTy :=
  DerivesOutputTypedTuple.has_output_type (sound h)

end RefinedDerivesTuple

namespace OutputTypeRefinedGrammar

/-- The tuple language generated by a refined grammar at a refined nonterminal. -/
def TupleLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (RG : OutputTypeRefinedGrammar G obs)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  { x | RefinedDerivesTuple RG A x }

/-- The tuple language of a refined grammar is sound with respect to the
semantic output-typed tuple language of the base grammar. -/
theorem tupleLanguage_sound
    {G : WorkingMCFG N α} {obs : α → M}
    (RG : OutputTypeRefinedGrammar G obs)
    (A : RefinedNonterminal G M) :
    TupleLanguage RG A ⊆ OutputTypedTupleLanguage G obs A := by
  intro x hx
  exact RefinedDerivesTuple.sound hx

/-- Forgetting output types maps the refined tuple language into the ordinary
tuple language of the base nonterminal. -/
theorem tupleLanguage_forgets_to_base
    {G : WorkingMCFG N α} {obs : α → M}
    (RG : OutputTypeRefinedGrammar G obs)
    (A : RefinedNonterminal G M) :
    TupleLanguage RG A ⊆ FIv21.TupleLanguage G A.base := by
  intro x hx
  exact RefinedDerivesTuple.forgets_to_derivation hx

/-- Every tuple generated by the refined grammar at `A` has `A`'s advertised
output type. -/
theorem tupleLanguage_has_output_type
    {G : WorkingMCFG N α} {obs : α → M}
    (RG : OutputTypeRefinedGrammar G obs)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ TupleLanguage RG A) :
    tupleType obs x = A.outTy :=
  RefinedDerivesTuple.has_output_type hx

end OutputTypeRefinedGrammar

section OrdinaryRuleLifts

variable {G : WorkingMCFG N α} {obs : α → M}
variable {RG : OutputTypeRefinedGrammar G obs}

/-- If a refined grammar contains all ordinary rule refinements, then every
listed well-typed terminal rule is available as a refined derivation step. -/
theorem refined_terminal_step_of_containsAll
    (hRG : RG.ContainsAllOrdinaryRuleRefinements)
    (ρ : TerminalRule N α) (hρ : ρ ∈ G.terminalRules)
    (hwt : ρ.WellTyped G.arity) :
    RefinedDerivesTuple RG
      (TerminalRule.refinedLHS obs ρ hwt)
      (castTuple hwt.symm ρ.outputTuple) := by
  exact RefinedDerivesTuple.terminal
    { rule := ρ
      mem := hρ
      wellTyped := hwt }
    (hRG.1 ρ hρ hwt)

/-- If a refined grammar contains all ordinary rule refinements, then every
listed binary rule can be used at every pair of child output types. -/
theorem refined_binary_step_of_containsAll
    (hRG : RG.ContainsAllOrdinaryRuleRefinements)
    (ρ : BinaryRule N α G.arity) (hρ : ρ ∈ G.binaryRules)
    (leftTy : Fin (G.arity ρ.left) → M)
    (rightTy : Fin (G.arity ρ.right) → M)
    (x : Tuple α (G.arity ρ.left))
    (y : Tuple α (G.arity ρ.right))
    (hx : RefinedDerivesTuple RG (BinaryRule.refinedLeft ρ leftTy) x)
    (hy : RefinedDerivesTuple RG (BinaryRule.refinedRight ρ rightTy) y) :
    RefinedDerivesTuple RG
      (BinaryRule.refinedLHS obs ρ leftTy rightTy)
      (ρ.apply x y) := by
  exact RefinedDerivesTuple.binary
    { rule := ρ
      mem := hρ
      leftTy := leftTy
      rightTy := rightTy }
    (hRG.2.1 ρ hρ leftTy rightTy) x y hx hy

/-- If a refined grammar contains all ordinary rule refinements, then every
well-typed listed start rule can be used at every child output type. -/
theorem refined_start_step_of_containsAll
    (hRG : RG.ContainsAllOrdinaryRuleRefinements)
    (ρ : StartRule N) (hρ : ρ ∈ G.startRules)
    (hwt : ρ.WellTyped G)
    (childTy : Fin (G.arity ρ.child) → M)
    (x : Tuple α (G.arity ρ.child))
    (hx : RefinedDerivesTuple RG (StartRule.refinedChild ρ childTy) x) :
    RefinedDerivesTuple RG
      (StartRule.refinedStart ρ hwt childTy)
      (castTuple hwt x) := by
  exact RefinedDerivesTuple.start
    { rule := ρ
      mem := hρ
      wellTyped := hwt
      childTy := childTy }
    (hRG.2.2 ρ hρ hwt childTy) x hx

end OrdinaryRuleLifts

end RefinedGrammarSkeleton

end FIv21
