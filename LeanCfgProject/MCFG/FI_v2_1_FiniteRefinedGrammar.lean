import LeanCfgProject.MCFG.FI_v2_1_RefinedGrammar

/-!
# FI v2.1 Lean experiment: finite output-type refined grammar certificates

This file is the eighteenth formalization layer for the FI v2.1 MCFG paper.

The previous layer introduced an output-type refined grammar as predicates over
packaged refined terminal, binary, and start rules.  This file adds a finite
certificate layer: a refined grammar can be represented by explicit finite
lists of packaged refined rules, and its predicate-style grammar is obtained by
list membership.

The point is deliberately modest but useful.  We do not yet construct the
complete finite enumeration from `[Fintype M]` and finite base-rule data.
Instead, we isolate the exact certificate that such an enumeration must supply:
it must list every ordinary rule refinement needed by the output-type refined
skeleton.  Once this coverage certificate is present, the existing soundness and
rule-lifting theorems for `OutputTypeRefinedGrammar` apply immediately.
-/

namespace FIv21

universe u v w

section FiniteRefinedGrammar

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M]

/-- A finite output-type refined grammar over a fixed base grammar and
observation.

The three fields are explicit finite lists of packaged refined terminal, binary,
and start rules.  No decidable equality is needed: membership is the ordinary
propositional list-membership relation. -/
structure FiniteOutputTypeRefinedGrammar
    (G : WorkingMCFG N α) (obs : α → M) where
  terminalRules : List (RefinedTerminalRule G obs)
  binaryRules : List (RefinedBinaryRule G obs)
  startRules : List (RefinedStartRule G obs)

namespace FiniteOutputTypeRefinedGrammar

/-- Forget the finite lists to the predicate-style refined grammar skeleton. -/
def toOutputTypeRefinedGrammar
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs) :
    OutputTypeRefinedGrammar G obs :=
  { HasTerminal := fun ρ => ρ ∈ FG.terminalRules
    HasBinary := fun ρ => ρ ∈ FG.binaryRules
    HasStart := fun ρ => ρ ∈ FG.startRules }

/-- Number of listed refined terminal rules. -/
def terminalRuleCount
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs) : Nat :=
  FG.terminalRules.length

/-- Number of listed refined binary rules. -/
def binaryRuleCount
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs) : Nat :=
  FG.binaryRules.length

/-- Number of listed refined start rules. -/
def startRuleCount
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs) : Nat :=
  FG.startRules.length

/-- Total number of listed refined rules. -/
def ruleCount
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs) : Nat :=
  FG.terminalRuleCount + FG.binaryRuleCount + FG.startRuleCount

@[simp] theorem hasTerminal_iff_mem
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (ρ : RefinedTerminalRule G obs) :
    FG.toOutputTypeRefinedGrammar.HasTerminal ρ ↔ ρ ∈ FG.terminalRules := by
  rfl

@[simp] theorem hasBinary_iff_mem
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (ρ : RefinedBinaryRule G obs) :
    FG.toOutputTypeRefinedGrammar.HasBinary ρ ↔ ρ ∈ FG.binaryRules := by
  rfl

@[simp] theorem hasStart_iff_mem
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (ρ : RefinedStartRule G obs) :
    FG.toOutputTypeRefinedGrammar.HasStart ρ ↔ ρ ∈ FG.startRules := by
  rfl

/-- The finite-list version of containing all ordinary output-type rule
refinements.

This is the certificate that a later concrete enumeration procedure must prove:
every listed ordinary base rule, at every compatible output-type choice, occurs
in the corresponding finite refined-rule list. -/
def CoversAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs) : Prop :=
  (∀ (ρ : TerminalRule N α) (hρ : ρ ∈ G.terminalRules),
      ∀ hwt : ρ.WellTyped G.arity,
        { rule := ρ
          mem := hρ
          wellTyped := hwt } ∈ FG.terminalRules) ∧
  (∀ (ρ : BinaryRule N α G.arity) (hρ : ρ ∈ G.binaryRules),
      ∀ leftTy : Fin (G.arity ρ.left) → M,
      ∀ rightTy : Fin (G.arity ρ.right) → M,
        { rule := ρ
          mem := hρ
          leftTy := leftTy
          rightTy := rightTy } ∈ FG.binaryRules) ∧
  (∀ (ρ : StartRule N) (hρ : ρ ∈ G.startRules),
      ∀ hwt : ρ.WellTyped G,
      ∀ childTy : Fin (G.arity ρ.child) → M,
        { rule := ρ
          mem := hρ
          wellTyped := hwt
          childTy := childTy } ∈ FG.startRules)

/-- A finite coverage certificate induces the predicate-style coverage property
used by the previous refined-grammar layer. -/
theorem coversAll_to_containsAll
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (hFG : FG.CoversAllOrdinaryRuleRefinements) :
    FG.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  constructor
  · intro ρ hρ hwt
    exact hFG.1 ρ hρ hwt
  constructor
  · intro ρ hρ leftTy rightTy
    exact hFG.2.1 ρ hρ leftTy rightTy
  · intro ρ hρ hwt childTy
    exact hFG.2.2 ρ hρ hwt childTy

/-- Tuple language generated by the finite refined grammar. -/
def TupleLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  OutputTypeRefinedGrammar.TupleLanguage FG.toOutputTypeRefinedGrammar A

/-- The finite refined tuple language is sound for the output-typed tuple
language of the base grammar. -/
theorem tupleLanguage_sound
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (A : RefinedNonterminal G M) :
    FG.TupleLanguage A ⊆ OutputTypedTupleLanguage G obs A := by
  intro x hx
  exact OutputTypeRefinedGrammar.tupleLanguage_sound
    FG.toOutputTypeRefinedGrammar A hx

/-- Forgetting output types maps the finite refined tuple language into the
ordinary base tuple language. -/
theorem tupleLanguage_forgets_to_base
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (A : RefinedNonterminal G M) :
    FG.TupleLanguage A ⊆ FIv21.TupleLanguage G A.base := by
  intro x hx
  exact OutputTypeRefinedGrammar.tupleLanguage_forgets_to_base
    FG.toOutputTypeRefinedGrammar A hx

/-- Every tuple generated by the finite refined grammar at `A` has the output
type advertised by `A`. -/
theorem tupleLanguage_has_output_type
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ FG.TupleLanguage A) :
    tupleType obs x = A.outTy := by
  exact OutputTypeRefinedGrammar.tupleLanguage_has_output_type
    FG.toOutputTypeRefinedGrammar A hx

/-- Terminal-step lifting for finite refined grammars with a coverage
certificate. -/
theorem refined_terminal_step_of_coversAll
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (hFG : FG.CoversAllOrdinaryRuleRefinements)
    (ρ : TerminalRule N α) (hρ : ρ ∈ G.terminalRules)
    (hwt : ρ.WellTyped G.arity) :
    RefinedDerivesTuple FG.toOutputTypeRefinedGrammar
      (TerminalRule.refinedLHS obs ρ hwt)
      (castTuple hwt.symm ρ.outputTuple) := by
  exact refined_terminal_step_of_containsAll
    (FG.coversAll_to_containsAll hFG) ρ hρ hwt

/-- Binary-step lifting for finite refined grammars with a coverage
certificate. -/
theorem refined_binary_step_of_coversAll
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (hFG : FG.CoversAllOrdinaryRuleRefinements)
    (ρ : BinaryRule N α G.arity) (hρ : ρ ∈ G.binaryRules)
    (leftTy : Fin (G.arity ρ.left) → M)
    (rightTy : Fin (G.arity ρ.right) → M)
    (x : Tuple α (G.arity ρ.left))
    (y : Tuple α (G.arity ρ.right))
    (hx : RefinedDerivesTuple FG.toOutputTypeRefinedGrammar
      (BinaryRule.refinedLeft ρ leftTy) x)
    (hy : RefinedDerivesTuple FG.toOutputTypeRefinedGrammar
      (BinaryRule.refinedRight ρ rightTy) y) :
    RefinedDerivesTuple FG.toOutputTypeRefinedGrammar
      (BinaryRule.refinedLHS obs ρ leftTy rightTy)
      (ρ.apply x y) := by
  exact refined_binary_step_of_containsAll
    (FG.coversAll_to_containsAll hFG) ρ hρ leftTy rightTy x y hx hy

/-- Start-step lifting for finite refined grammars with a coverage certificate. -/
theorem refined_start_step_of_coversAll
    {G : WorkingMCFG N α} {obs : α → M}
    (FG : FiniteOutputTypeRefinedGrammar G obs)
    (hFG : FG.CoversAllOrdinaryRuleRefinements)
    (ρ : StartRule N) (hρ : ρ ∈ G.startRules)
    (hwt : ρ.WellTyped G)
    (childTy : Fin (G.arity ρ.child) → M)
    (x : Tuple α (G.arity ρ.child))
    (hx : RefinedDerivesTuple FG.toOutputTypeRefinedGrammar
      (StartRule.refinedChild ρ childTy) x) :
    RefinedDerivesTuple FG.toOutputTypeRefinedGrammar
      (StartRule.refinedStart ρ hwt childTy)
      (castTuple hwt x) := by
  exact refined_start_step_of_containsAll
    (FG.coversAll_to_containsAll hFG) ρ hρ hwt childTy x hx

end FiniteOutputTypeRefinedGrammar

/-- A finite output-type refinement certificate: finite lists of refined rules
together with the proof that they cover every ordinary output-type rule
refinement needed by the semantic skeleton. -/
structure FiniteOutputTypeRefinementCertificate
    (G : WorkingMCFG N α) (obs : α → M) where
  grammar : FiniteOutputTypeRefinedGrammar G obs
  coversAll : grammar.CoversAllOrdinaryRuleRefinements

namespace FiniteOutputTypeRefinementCertificate

/-- The predicate-style refined grammar associated with the finite certificate. -/
def toOutputTypeRefinedGrammar
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeRefinementCertificate G obs) :
    OutputTypeRefinedGrammar G obs :=
  C.grammar.toOutputTypeRefinedGrammar

/-- The associated predicate-style refined grammar contains all ordinary rule
refinements. -/
theorem containsAllOrdinaryRuleRefinements
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeRefinementCertificate G obs) :
    C.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements :=
  C.grammar.coversAll_to_containsAll C.coversAll

/-- Tuple language generated by a finite refinement certificate. -/
def TupleLanguage
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeRefinementCertificate G obs)
    (A : RefinedNonterminal G M) : Set (Tuple α (G.arity A.base)) :=
  C.grammar.TupleLanguage A

/-- Soundness of the finite refinement certificate. -/
theorem tupleLanguage_sound
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeRefinementCertificate G obs)
    (A : RefinedNonterminal G M) :
    C.TupleLanguage A ⊆ OutputTypedTupleLanguage G obs A := by
  intro x hx
  exact C.grammar.tupleLanguage_sound A hx

/-- Forgetting output types maps the certified finite refined tuple language
into the ordinary base tuple language. -/
theorem tupleLanguage_forgets_to_base
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeRefinementCertificate G obs)
    (A : RefinedNonterminal G M) :
    C.TupleLanguage A ⊆ FIv21.TupleLanguage G A.base := by
  intro x hx
  exact C.grammar.tupleLanguage_forgets_to_base A hx

/-- Every tuple generated by the certificate at `A` has the advertised output
type of `A`. -/
theorem tupleLanguage_has_output_type
    {G : WorkingMCFG N α} {obs : α → M}
    (C : FiniteOutputTypeRefinementCertificate G obs)
    (A : RefinedNonterminal G M)
    {x : Tuple α (G.arity A.base)}
    (hx : x ∈ C.TupleLanguage A) :
    tupleType obs x = A.outTy := by
  exact C.grammar.tupleLanguage_has_output_type A hx

end FiniteOutputTypeRefinementCertificate

end FiniteRefinedGrammar

end FIv21
