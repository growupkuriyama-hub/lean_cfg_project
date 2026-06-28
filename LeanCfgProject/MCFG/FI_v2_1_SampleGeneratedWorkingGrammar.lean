import LeanCfgProject.MCFG.FI_v2_1_SampleGeneratedRuleSkeletonGold

/-!
# FI v2.1 Lean experiment: sample-generated working grammar shell

This file is the next vertical step after the sample-generated rule skeleton.
The preceding layer produced concrete start, terminal, binary-concatenation,
and unit-rule *candidates*.  Here we turn the start/terminal/binary candidates
into actual finite rule lists and package them as a lightweight `WorkingMCFG`.

The construction is intentionally conservative.  The nonterminal type of this
working grammar is restricted to the root and the listed decomposition nodes, so
all arities are one.  Unit candidates are still kept in the separate unit-closure
pipeline; they are not inserted as ordinary binary MCFG rules.
-/

namespace FIv21

universe u v w

section SampleGeneratedWorkingGrammar

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Nonterminals of the sample-generated working grammar shell.

This is deliberately smaller than `CanonicalLearnerNonterminal`: it contains
only the root and the listed one-hole decomposition nodes.  Hence every
nonterminal has arity one, which lets us build a genuine `WorkingMCFG` shell
without needing positivity proofs for arbitrary canonical nonterminals. -/
inductive SampleGeneratedGrammarNonterminal
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (S : SampleGeneratedLearnerGrammarSkeleton G obs K) where
  | root : SampleGeneratedGrammarNonterminal S
  | node : SampleGeneratedDecompositionNode S → SampleGeneratedGrammarNonterminal S

namespace SampleGeneratedGrammarNonterminal

/-- The generated working grammar shell is currently one-fanout throughout. -/
def arity
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K} :
    SampleGeneratedGrammarNonterminal S → Nat :=
  fun _ => 1

@[simp] theorem arity_root
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K} :
    arity (S := S) root = 1 := by
  rfl

@[simp] theorem arity_node
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (X : SampleGeneratedDecompositionNode S) :
    arity (S := S) (node X) = 1 := by
  rfl

end SampleGeneratedGrammarNonterminal

/-- Convert a generated start candidate into a syntactic start rule of the
working grammar shell. -/
def startRuleOfCandidate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedStartCandidate S) :
    StartRule (SampleGeneratedGrammarNonterminal S) :=
  { child := SampleGeneratedGrammarNonterminal.node C.node }

/-- Convert a singleton-middle terminal candidate into a terminal rule of the
working grammar shell. -/
def terminalRuleOfCandidate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedTerminalCandidate S) :
    TerminalRule (SampleGeneratedGrammarNonterminal S) α :=
  { lhs := SampleGeneratedGrammarNonterminal.node C.node
    terminal := C.terminal }

/-- Convert a concatenation candidate into a binary rule of the working grammar
shell. -/
def binaryRuleOfConcatCandidate
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedConcatCandidate S) :
    BinaryRule (SampleGeneratedGrammarNonterminal S) α
      (SampleGeneratedGrammarNonterminal.arity (S := S)) :=
  { lhs := SampleGeneratedGrammarNonterminal.node C.result
    left := SampleGeneratedGrammarNonterminal.node C.left
    right := SampleGeneratedGrammarNonterminal.node C.right
    body := singletonConcatTemplate (α := α) }

@[simp] theorem terminalRuleOfCandidate_wellTyped
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedTerminalCandidate S) :
    (terminalRuleOfCandidate (M := M) C).WellTyped
      (SampleGeneratedGrammarNonterminal.arity (S := S)) := by
  rfl

/-- Binary rules generated from concatenation candidates are nondeleting. -/
theorem binaryRuleOfConcatCandidate_nondeleting
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    {S : SampleGeneratedLearnerGrammarSkeleton G obs K}
    (C : SampleGeneratedConcatCandidate S) :
    (binaryRuleOfConcatCandidate (M := M) C).Nondeleting := by
  constructor
  · intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    refine ⟨0, ?_⟩
    simp [binaryRuleOfConcatCandidate, singletonConcatTemplate,
      BinaryRule.Nondeleting, TemplateTuple.Nondeleting]
  · intro j
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    refine ⟨0, ?_⟩
    simp [binaryRuleOfConcatCandidate, singletonConcatTemplate,
      BinaryRule.Nondeleting, TemplateTuple.Nondeleting]

/-- Finite rule lists extracted from a sample-generated rule skeleton.

Start candidates are generated canonically from the listed decomposition nodes.
Terminal and binary-concatenation candidates are carried as explicit lists; later
layers can replace these fields by automatic finite enumerators. -/
structure SampleGeneratedRuleListPackage
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α)) where
  ruleSkeleton : SampleGeneratedRuleSkeleton G obs K
  terminalCandidates : List (SampleGeneratedTerminalCandidate ruleSkeleton.skeleton)
  concatCandidates : List (SampleGeneratedConcatCandidate ruleSkeleton.skeleton)

namespace SampleGeneratedRuleListPackage

/-- Start rules of the generated working grammar shell. -/
noncomputable def startRules
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedRuleListPackage G obs K) :
    List (StartRule (SampleGeneratedGrammarNonterminal P.ruleSkeleton.skeleton)) :=
  P.ruleSkeleton.startCandidates.map (fun C => startRuleOfCandidate (M := M) C)

/-- Terminal rules of the generated working grammar shell. -/
noncomputable def terminalRules
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedRuleListPackage G obs K) :
    List (TerminalRule (SampleGeneratedGrammarNonterminal P.ruleSkeleton.skeleton) α) :=
  P.terminalCandidates.map (fun C => terminalRuleOfCandidate (M := M) C)

/-- Binary concatenation rules of the generated working grammar shell. -/
noncomputable def binaryRules
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedRuleListPackage G obs K) :
    List (BinaryRule (SampleGeneratedGrammarNonterminal P.ruleSkeleton.skeleton) α
      (SampleGeneratedGrammarNonterminal.arity (S := P.ruleSkeleton.skeleton))) :=
  P.concatCandidates.map (fun C => binaryRuleOfConcatCandidate (M := M) C)

/-- The actual `WorkingMCFG` shell generated by the finite rule-list package. -/
noncomputable def toWorkingMCFG
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedRuleListPackage G obs K) :
    WorkingMCFG (SampleGeneratedGrammarNonterminal P.ruleSkeleton.skeleton) α :=
  { start := SampleGeneratedGrammarNonterminal.root
    arity := SampleGeneratedGrammarNonterminal.arity (S := P.ruleSkeleton.skeleton)
    arity_pos := by
      intro A
      exact Nat.succ_pos 0
    startRules := P.startRules
    terminalRules := P.terminalRules
    binaryRules := P.binaryRules }

/-- The generated working grammar shell has start arity one. -/
theorem toWorkingMCFG_startArityOne
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedRuleListPackage G obs K) :
    P.toWorkingMCFG.StartArityOne := by
  rfl

/-- All generated terminal rules are well-typed. -/
theorem toWorkingMCFG_terminalRulesWellTyped
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedRuleListPackage G obs K) :
    P.toWorkingMCFG.TerminalRulesWellTyped := by
  intro ρ hρ
  unfold toWorkingMCFG terminalRules at hρ
  rcases List.mem_map.mp hρ with ⟨C, _hC, hEq⟩
  cases hEq
  exact terminalRuleOfCandidate_wellTyped (M := M) C

/-- All generated binary concatenation rules are nondeleting. -/
theorem toWorkingMCFG_binaryRulesNondeleting
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedRuleListPackage G obs K) :
    P.toWorkingMCFG.BinaryRulesNondeleting := by
  intro ρ hρ
  unfold toWorkingMCFG binaryRules at hρ
  rcases List.mem_map.mp hρ with ⟨C, _hC, hEq⟩
  cases hEq
  exact binaryRuleOfConcatCandidate_nondeleting (M := M) C

/-- The generated working grammar shell satisfies the basic syntactic working
conditions represented by `WorkingMCFG.BasicWorkingConditions`. -/
theorem toWorkingMCFG_basicWorkingConditions
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedRuleListPackage G obs K) :
    P.toWorkingMCFG.BasicWorkingConditions := by
  exact ⟨P.toWorkingMCFG_startArityOne,
    P.toWorkingMCFG_terminalRulesWellTyped,
    P.toWorkingMCFG_binaryRulesNondeleting⟩

/-- A listed generated start candidate contributes a start rule to the generated
rule list. -/
theorem startRule_mem_of_candidate_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedRuleListPackage G obs K)
    {C : SampleGeneratedStartCandidate P.ruleSkeleton.skeleton}
    (hC : C ∈ P.ruleSkeleton.startCandidates) :
    startRuleOfCandidate (M := M) C ∈ P.startRules := by
  unfold startRules
  exact List.mem_map.mpr ⟨C, hC, rfl⟩

/-- A listed generated terminal candidate contributes a terminal rule. -/
theorem terminalRule_mem_of_candidate_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedRuleListPackage G obs K)
    {C : SampleGeneratedTerminalCandidate P.ruleSkeleton.skeleton}
    (hC : C ∈ P.terminalCandidates) :
    terminalRuleOfCandidate (M := M) C ∈ P.terminalRules := by
  unfold terminalRules
  exact List.mem_map.mpr ⟨C, hC, rfl⟩

/-- A listed generated concatenation candidate contributes a binary rule. -/
theorem binaryRule_mem_of_candidate_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (P : SampleGeneratedRuleListPackage G obs K)
    {C : SampleGeneratedConcatCandidate P.ruleSkeleton.skeleton}
    (hC : C ∈ P.concatCandidates) :
    binaryRuleOfConcatCandidate (M := M) C ∈ P.binaryRules := by
  unfold binaryRules
  exact List.mem_map.mpr ⟨C, hC, rfl⟩

end SampleGeneratedRuleListPackage

/-- Every decomposition node of a rule skeleton occurs in its generated node
list. -/
theorem decompositionNode_mem_decompositionNodes
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (R : SampleGeneratedRuleSkeleton G obs K)
    (X : SampleGeneratedDecompositionNode R.skeleton) :
    X ∈ R.decompositionNodes := by
  unfold SampleGeneratedRuleSkeleton.decompositionNodes
  refine List.mem_map.mpr ?_
  refine ⟨⟨X.decomposition, X.mem⟩, ?_, ?_⟩
  · simp
  · cases X
    rfl

/-- The fully enumerated rule-list package with no extra terminal or binary
concat candidates supplied yet.  It already contains the canonical start-rule
list coming from the enumerated decomposition nodes. -/
noncomputable def enumeratedSampleGeneratedRuleListPackage
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    SampleGeneratedRuleListPackage G obs K :=
  { ruleSkeleton := enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG
    terminalCandidates := []
    concatCandidates := [] }

/-- The enumerated package yields a genuine working grammar shell satisfying the
basic syntactic side conditions. -/
theorem enumeratedSampleGeneratedWorkingGrammar_basic
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions) :
    (enumeratedSampleGeneratedRuleListPackage G obs K f hfanout hG)
      .toWorkingMCFG.BasicWorkingConditions := by
  exact (enumeratedSampleGeneratedRuleListPackage G obs K f hfanout hG)
    .toWorkingMCFG_basicWorkingConditions

/-- For every sampled word, the enumerated rule-list package contains a start
candidate and hence a start rule pointing at a listed decomposition node. -/
theorem enumeratedRuleListPackage_startRule_exists_of_mem
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    {w : Word α} (hw : w ∈ K) :
    ∃ C : SampleGeneratedStartCandidate
        (enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG).skeleton,
      C ∈ (enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG).startCandidates ∧
      C.node.decomposition.sampleWord = w ∧
      startRuleOfCandidate (M := M) C ∈
        (enumeratedSampleGeneratedRuleListPackage G obs K f hfanout hG).startRules := by
  rcases enumeratedSkeleton_sample_word_node G obs K f hfanout hG hw with
    ⟨X, hWord, _hTuple, _hContext, _hTyped, _hDist⟩
  let R := enumeratedSampleGeneratedRuleSkeleton G obs K f hfanout hG
  let P := enumeratedSampleGeneratedRuleListPackage G obs K f hfanout hG
  let C : SampleGeneratedStartCandidate R.skeleton := { node := X }
  have hX : X ∈ R.decompositionNodes := decompositionNode_mem_decompositionNodes R X
  have hC : C ∈ R.startCandidates := R.startCandidate_mem_of_node_mem hX
  have hRule : startRuleOfCandidate (M := M) C ∈ P.startRules :=
    P.startRule_mem_of_candidate_mem hC
  exact ⟨C, hC, hWord, hRule⟩

end SampleGeneratedWorkingGrammar

end FIv21
