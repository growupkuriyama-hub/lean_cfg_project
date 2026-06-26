import LeanCfgProject.MCFG.FI_v2_1_MCFG_Syntax

/-!
# FI v2.1 Lean experiment: first derivation semantics for working MCFGs

This file is the fourth formalization layer for the FI v2.1 MCFG paper.

The previous file introduced a lightweight syntax of working binary MCFG
presentations: terminal rules, binary rules, template tuples, and the
simultaneous substitution operation.  This file adds the first semantic layer:
an inductive tuple-derivation predicate for nonterminals and the associated
string language of the start symbol.

The scope is still intentionally modest.  We do not yet formalize derivation
trees as explicit finite objects, reducedness, productivity, reachability, or
the canonical learner.  Instead, we give the least derivation relation generated
by terminal, binary, and start rules.  This is the right landing point before
formalizing occurrence witnesses and characteristic samples.
-/

namespace FIv21

universe u v

section TupleCasts

variable {α : Type u}

/-- Transport a tuple across an equality of arities. -/
def castTuple {d e : Nat} (h : d = e) (x : Tuple α d) : Tuple α e := by
  subst h
  exact x

@[simp] theorem castTuple_rfl {d : Nat} (x : Tuple α d) :
    castTuple (rfl : d = d) x = x := rfl

/-- The one-component tuple containing a single word. -/
def singletonTuple (w : Word α) : Tuple α 1 :=
  fun _ => w

@[simp] theorem singletonTuple_apply (w : Word α) (i : Fin 1) :
    singletonTuple w i = w := rfl

end TupleCasts

section StartRuleTyping

variable {N : Type v} {α : Type u}

namespace StartRule

/-- A start rule is well-typed when its child has the same arity as the start
symbol.  Under the paper's working assumptions both arities are one, but this
form is more convenient for the first semantic layer. -/
def WellTyped (G : WorkingMCFG N α) (ρ : StartRule N) : Prop :=
  G.arity ρ.child = G.arity G.start

end StartRule

namespace WorkingMCFG

/-- All start rules are well-typed relative to the grammar's arity map. -/
def StartRulesWellTyped (G : WorkingMCFG N α) : Prop :=
  ∀ ρ : StartRule N, ρ ∈ G.startRules → ρ.WellTyped G

/-- A strengthened working-condition package that also records well-typed start
rules.  This supplements `BasicWorkingConditions` from the syntax layer without
changing that earlier definition. -/
def SemanticWorkingConditions (G : WorkingMCFG N α) : Prop :=
  G.BasicWorkingConditions ∧ G.StartRulesWellTyped

end WorkingMCFG

end StartRuleTyping

section DerivationSemantics

variable {N : Type v} {α : Type u}

/-- Tuple derivability for a working MCFG.

`DerivesTuple G A x` means that the nonterminal `A` derives the tuple `x`.
The tuple type itself enforces that `x` has arity `G.arity A`.  The constructors
mirror the three rule kinds in the paper's working binary presentation: terminal
rules, binary rules, and start rules.

For terminal and start rules we explicitly pass the needed well-typedness
proofs and cast the resulting tuple across the corresponding arity equality.
For binary rules no cast is needed, because the rule body is already indexed by
`G.arity ρ.lhs`, `G.arity ρ.left`, and `G.arity ρ.right`. -/
inductive DerivesTuple (G : WorkingMCFG N α) :
    (A : N) → Tuple α (G.arity A) → Prop where
  | terminal
      (ρ : TerminalRule N α)
      (hρ : ρ ∈ G.terminalRules)
      (hwt : ρ.WellTyped G.arity) :
      DerivesTuple G ρ.lhs (castTuple hwt.symm (TerminalRule.outputTuple ρ))
  | binary
      (ρ : BinaryRule N α G.arity)
      (hρ : ρ ∈ G.binaryRules)
      (x : Tuple α (G.arity ρ.left))
      (y : Tuple α (G.arity ρ.right))
      (hx : DerivesTuple G ρ.left x)
      (hy : DerivesTuple G ρ.right y) :
      DerivesTuple G ρ.lhs (ρ.apply x y)
  | start
      (ρ : StartRule N)
      (hρ : ρ ∈ G.startRules)
      (hwt : ρ.WellTyped G)
      (x : Tuple α (G.arity ρ.child))
      (hx : DerivesTuple G ρ.child x) :
      DerivesTuple G G.start (castTuple hwt x)

namespace DerivesTuple

variable {G : WorkingMCFG N α}

/-- Convenience wrapper for terminal derivations using the grammar's well-typed
terminal-rule condition. -/
theorem terminal_of_mem
    (hG : G.TerminalRulesWellTyped)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules) :
    DerivesTuple G ρ.lhs (castTuple (hG ρ hρ).symm (TerminalRule.outputTuple ρ)) := by
  exact DerivesTuple.terminal ρ hρ (hG ρ hρ)

/-- Convenience wrapper for start derivations using the grammar's well-typed
start-rule condition. -/
theorem start_of_mem
    (hG : G.StartRulesWellTyped)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (x : Tuple α (G.arity ρ.child))
    (hx : DerivesTuple G ρ.child x) :
    DerivesTuple G G.start (castTuple (hG ρ hρ) x) := by
  exact DerivesTuple.start ρ hρ (hG ρ hρ) x hx

/-- Convenience wrapper for binary derivations. -/
theorem binary_of_mem
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules)
    (x : Tuple α (G.arity ρ.left))
    (y : Tuple α (G.arity ρ.right))
    (hx : DerivesTuple G ρ.left x)
    (hy : DerivesTuple G ρ.right y) :
    DerivesTuple G ρ.lhs (ρ.apply x y) := by
  exact DerivesTuple.binary ρ hρ x y hx hy

end DerivesTuple

/-- The tuple language generated by a nonterminal. -/
def TupleLanguage (G : WorkingMCFG N α) (A : N) : Set (Tuple α (G.arity A)) :=
  { x | DerivesTuple G A x }

/-- The string language generated by the start symbol.

The paper assumes the start symbol has fan-out one.  Here that condition is
represented by the existential equality `1 = G.arity G.start`, which transports
the singleton word tuple into the start-symbol tuple type. -/
def StringLanguage (G : WorkingMCFG N α) : Set (Word α) :=
  { w | ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) }

namespace WorkingMCFG

/-- Namespace alias for the generated string language.

This alias enables projection notation such as `G.StringLanguage` in later
files while keeping the original definition `FIv21.StringLanguage` available as
the canonical top-level declaration. -/
abbrev StringLanguage (G : WorkingMCFG N α) : Set (Word α) :=
  FIv21.StringLanguage G

end WorkingMCFG

/-- If the start symbol derives the singleton tuple corresponding to `w`, then
`w` belongs to the string language. -/
theorem mem_StringLanguage_of_start_derives
    (G : WorkingMCFG N α) (w : Word α)
    (hstart : 1 = G.arity G.start)
    (hw : DerivesTuple G G.start (castTuple hstart (singletonTuple w))) :
    w ∈ G.StringLanguage := by
  exact ⟨hstart, hw⟩

/-- Unpack membership in the string language. -/
theorem start_derives_of_mem_StringLanguage
    (G : WorkingMCFG N α) (w : Word α)
    (hw : w ∈ G.StringLanguage) :
    ∃ h : 1 = G.arity G.start,
      DerivesTuple G G.start (castTuple h (singletonTuple w)) := by
  exact hw

end DerivationSemantics

end FIv21
