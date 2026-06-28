import LeanCfgProject.MCFG.FI_v2_1_FintypeEnumerationCertificate

/-!
# FI v2.1 Lean experiment: finite base-rule support

This file is the twenty-third formalization layer for the FI v2.1 MCFG
experiment.

The preceding files showed that, once a finite monoid supplies finite lists of
output-type vectors, output-type refined grammars can be represented by finite
certificates.  This file records the other finite ingredient: the base working
MCFG presentation already stores its terminal, binary, and start rules as
finite lists.

The layer is intentionally certificate-oriented.  It does not yet build the
full refined rule lists by nested list products.  Instead it isolates the base
finite support datum that such an enumerator will consume.
-/

namespace FIv21

universe u v w

section FiniteBaseRuleSupport

variable {N : Type w} {α : Type u}

namespace WorkingMCFG

/-- Number of ordinary terminal rules listed by a working grammar. -/
def terminalRuleCount (G : WorkingMCFG N α) : Nat :=
  G.terminalRules.length

/-- Number of ordinary binary rules listed by a working grammar. -/
def binaryRuleCount (G : WorkingMCFG N α) : Nat :=
  G.binaryRules.length

/-- Number of ordinary start rules listed by a working grammar. -/
def startRuleCount (G : WorkingMCFG N α) : Nat :=
  G.startRules.length

/-- Total number of ordinary rules listed by a working grammar. -/
def ordinaryRuleCount (G : WorkingMCFG N α) : Nat :=
  G.terminalRuleCount + G.binaryRuleCount + G.startRuleCount

@[simp] theorem terminalRuleCount_def (G : WorkingMCFG N α) :
    G.terminalRuleCount = G.terminalRules.length := rfl

@[simp] theorem binaryRuleCount_def (G : WorkingMCFG N α) :
    G.binaryRuleCount = G.binaryRules.length := rfl

@[simp] theorem startRuleCount_def (G : WorkingMCFG N α) :
    G.startRuleCount = G.startRules.length := rfl

end WorkingMCFG

/-- A finite support list for the ordinary rules of a working grammar.

For the canonical support this is just the rule lists already stored in `G`.
The explicit certificate form is useful because later algorithmic layers can
replace these lists by filtered or normalized enumerations while retaining the
same completeness interface. -/
structure FiniteBaseRuleSupport (G : WorkingMCFG N α) where
  terminalRules : List (TerminalRule N α)
  binaryRules : List (BinaryRule N α G.arity)
  startRules : List (StartRule N)
  terminal_complete :
    ∀ ρ : TerminalRule N α, ρ ∈ G.terminalRules → ρ ∈ terminalRules
  binary_complete :
    ∀ ρ : BinaryRule N α G.arity, ρ ∈ G.binaryRules → ρ ∈ binaryRules
  start_complete :
    ∀ ρ : StartRule N, ρ ∈ G.startRules → ρ ∈ startRules

namespace FiniteBaseRuleSupport

/-- The canonical finite base-rule support of a working grammar. -/
def canonical (G : WorkingMCFG N α) : FiniteBaseRuleSupport G :=
  { terminalRules := G.terminalRules
    binaryRules := G.binaryRules
    startRules := G.startRules
    terminal_complete := by intro ρ hρ; exact hρ
    binary_complete := by intro ρ hρ; exact hρ
    start_complete := by intro ρ hρ; exact hρ }

/-- Number of terminal rules in a base support. -/
def terminalRuleCount {G : WorkingMCFG N α}
    (S : FiniteBaseRuleSupport G) : Nat :=
  S.terminalRules.length

/-- Number of binary rules in a base support. -/
def binaryRuleCount {G : WorkingMCFG N α}
    (S : FiniteBaseRuleSupport G) : Nat :=
  S.binaryRules.length

/-- Number of start rules in a base support. -/
def startRuleCount {G : WorkingMCFG N α}
    (S : FiniteBaseRuleSupport G) : Nat :=
  S.startRules.length

/-- Total number of ordinary rules in a base support. -/
def ordinaryRuleCount {G : WorkingMCFG N α}
    (S : FiniteBaseRuleSupport G) : Nat :=
  S.terminalRuleCount + S.binaryRuleCount + S.startRuleCount

@[simp] theorem canonical_terminalRules (G : WorkingMCFG N α) :
    (canonical G).terminalRules = G.terminalRules := rfl

@[simp] theorem canonical_binaryRules (G : WorkingMCFG N α) :
    (canonical G).binaryRules = G.binaryRules := rfl

@[simp] theorem canonical_startRules (G : WorkingMCFG N α) :
    (canonical G).startRules = G.startRules := rfl

/-- Completeness for canonical terminal-rule support. -/
theorem canonical_terminal_complete
    (G : WorkingMCFG N α)
    (ρ : TerminalRule N α) (hρ : ρ ∈ G.terminalRules) :
    ρ ∈ (canonical G).terminalRules :=
  hρ

/-- Completeness for canonical binary-rule support. -/
theorem canonical_binary_complete
    (G : WorkingMCFG N α)
    (ρ : BinaryRule N α G.arity) (hρ : ρ ∈ G.binaryRules) :
    ρ ∈ (canonical G).binaryRules :=
  hρ

/-- Completeness for canonical start-rule support. -/
theorem canonical_start_complete
    (G : WorkingMCFG N α)
    (ρ : StartRule N) (hρ : ρ ∈ G.startRules) :
    ρ ∈ (canonical G).startRules :=
  hρ

/-- A listed terminal rule is supported by `S`. -/
def SupportsTerminalRule {G : WorkingMCFG N α}
    (S : FiniteBaseRuleSupport G) (ρ : TerminalRule N α) : Prop :=
  ρ ∈ S.terminalRules

/-- A listed binary rule is supported by `S`. -/
def SupportsBinaryRule {G : WorkingMCFG N α}
    (S : FiniteBaseRuleSupport G) (ρ : BinaryRule N α G.arity) : Prop :=
  ρ ∈ S.binaryRules

/-- A listed start rule is supported by `S`. -/
def SupportsStartRule {G : WorkingMCFG N α}
    (S : FiniteBaseRuleSupport G) (ρ : StartRule N) : Prop :=
  ρ ∈ S.startRules

/-- Every ordinary terminal rule of the grammar is supported. -/
theorem supports_terminal_of_mem
    {G : WorkingMCFG N α}
    (S : FiniteBaseRuleSupport G)
    (ρ : TerminalRule N α) (hρ : ρ ∈ G.terminalRules) :
    S.SupportsTerminalRule ρ :=
  S.terminal_complete ρ hρ

/-- Every ordinary binary rule of the grammar is supported. -/
theorem supports_binary_of_mem
    {G : WorkingMCFG N α}
    (S : FiniteBaseRuleSupport G)
    (ρ : BinaryRule N α G.arity) (hρ : ρ ∈ G.binaryRules) :
    S.SupportsBinaryRule ρ :=
  S.binary_complete ρ hρ

/-- Every ordinary start rule of the grammar is supported. -/
theorem supports_start_of_mem
    {G : WorkingMCFG N α}
    (S : FiniteBaseRuleSupport G)
    (ρ : StartRule N) (hρ : ρ ∈ G.startRules) :
    S.SupportsStartRule ρ :=
  S.start_complete ρ hρ

end FiniteBaseRuleSupport

end FiniteBaseRuleSupport

end FIv21
