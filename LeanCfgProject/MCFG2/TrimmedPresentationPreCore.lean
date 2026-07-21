/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.OutputTypeTrimmedPresentationSkeleton

/-!
# TrimmedPresentationPreCore.lean

Forty-second clean Lean experiment for the fixed-observation MCFG project.

`OutputTypeTrimmedPresentationSkeleton.lean` introduced a trimmed finite
output-type presentation with anchors and exposing contexts for typed
nonterminals present in the presentation.

The reachable blueprint layer, however, is indexed by the original base
nonterminals `A : N`.  This file adds an intermediate bridge:

* choose, for every base nonterminal `A`, a present typed representative;
* provide base-indexed anchors and exposing contexts;
* record that the base anchor has the representative's output type;
* package the base-indexed data into `ReachableBlueprintPreCore`.

This is still a skeleton: it does not yet prove that such representatives come
from the actual trimmed presentation.  It isolates the exact data needed to
descend from typed representatives to the base nonterminal interface required
by the reachable theorem.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section BaseRepresentatives

variable {N : Type v} {α : Type u} {M : Type w}
variable [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Base-indexed representatives chosen from a trimmed output-type presentation.

For each base nonterminal `A`, we choose a present typed nonterminal whose base
is `A`, together with a base-indexed anchor and exposing context.  The separate
base-indexed anchor/expose fields avoid dependent casts on named contexts. -/
structure TrimmedBaseRepresentatives
    (T : TrimmedOutputTypePresentation G obs) where
  rep : ∀ A : N, T.Present
  rep_base_eq :
    ∀ A : N, (rep A).node.base = A

  anchor : ∀ A : N, Tuple α (G.arity A)
  expose : ∀ A : N, NamedSentenceContext α (G.arity A)

  anchor_matches_rep :
    ∀ A : N,
      tupleType obs (anchor A) =
        castTuple (congrArg G.arity (rep_base_eq A)) ((rep A).node.out)

  expose_accepts :
    ∀ A : N,
      namedFill (G.arity A) (expose A) (anchor A) ∈ G.StringLanguage

namespace TrimmedBaseRepresentatives

variable {T : TrimmedOutputTypePresentation G obs}

/-- The arity equality induced by the representative's base equality. -/
def repArityEq
    (R : TrimmedBaseRepresentatives T)
    (A : N) :
    G.arity (R.rep A).node.base = G.arity A :=
  congrArg G.arity (R.rep_base_eq A)

/-- The output type of the representative, transported to the base arity. -/
def transportedRepOutput
    (R : TrimmedBaseRepresentatives T)
    (A : N) : Tuple M (G.arity A) :=
  castTuple (R.repArityEq A) ((R.rep A).node.out)

/-- The exposed word associated with a base nonterminal. -/
def exposedWord
    (R : TrimmedBaseRepresentatives T)
    (A : N) : Word α :=
  namedFill (G.arity A) (R.expose A) (R.anchor A)

/-- The base anchor has the transported output type of its typed
representative. -/
theorem anchor_tupleType
    (R : TrimmedBaseRepresentatives T)
    (A : N) :
    tupleType obs (R.anchor A) = R.transportedRepOutput A :=
  R.anchor_matches_rep A

/-- The exposed base word is accepted by the original grammar. -/
theorem exposedWord_mem
    (R : TrimmedBaseRepresentatives T)
    (A : N) :
    R.exposedWord A ∈ G.StringLanguage :=
  R.expose_accepts A

/-- The chosen typed representative is present in the underlying finite
presentation. -/
theorem rep_present
    (R : TrimmedBaseRepresentatives T)
    (A : N) :
    T.presentation.HasNonterminal (R.rep A).node :=
  (R.rep A).mem

end TrimmedBaseRepresentatives

end BaseRepresentatives


section PreCoreFromTrimmedPresentation

variable {N : Type v} {α : Type u} {M : Type w}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}
variable {f : Nat}

/-- Data needed to turn a trimmed output-type presentation into the pre-core
used by the reachable splicing blueprint.

This record deliberately stops before finite sample membership and binary
splicing witnesses.  Those will be separate construction layers. -/
structure TrimmedPresentationPreCoreData
    (T : TrimmedOutputTypePresentation G obs) (f : Nat) where
  representatives : TrimmedBaseRepresentatives T

  terminal_type_eq :
    ∀ (ρ : TerminalRule N α),
      ρ ∈ G.terminalRules →
      ∀ hwt : G.arity ρ.lhs = 1,
        tupleType obs (representatives.anchor ρ.lhs) =
          tupleType obs (castTuple hwt.symm ρ.outputTuple)

  binary_type_eq :
    ∀ (ρ : BinaryRule N α G.arity),
      ρ ∈ G.binaryRules →
        tupleType obs (representatives.anchor ρ.lhs) =
          tupleType obs
            (ρ.apply
              (representatives.anchor ρ.left)
              (representatives.anchor ρ.right))

  start_type_eq :
    ∀ (ρ : StartRule N),
      ρ ∈ G.startRules →
      ∀ hwt : G.arity ρ.child = G.arity G.start,
        tupleType obs (representatives.anchor G.start) =
          tupleType obs (castTuple hwt (representatives.anchor ρ.child))

  startWord : Word α
  start_arity : 1 = G.arity G.start
  start_anchor_eq :
    representatives.anchor G.start =
      castTuple start_arity (singletonTuple startWord)

namespace TrimmedPresentationPreCoreData

variable {T : TrimmedOutputTypePresentation G obs}

/-- The base anchor induced by the representatives. -/
def anchor
    (D : TrimmedPresentationPreCoreData T f)
    (A : N) : Tuple α (G.arity A) :=
  D.representatives.anchor A

/-- The base exposing context induced by the representatives. -/
def expose
    (D : TrimmedPresentationPreCoreData T f)
    (A : N) : NamedSentenceContext α (G.arity A) :=
  D.representatives.expose A

/-- Convert trimmed-presentation pre-core data into the reachable blueprint
pre-core used by the already verified main theorem. -/
def toReachablePreCore
    (D : TrimmedPresentationPreCoreData T f) :
    ReachableBlueprintPreCore G obs f where
  anchor := D.anchor
  expose := D.expose
  terminal_type_eq := D.terminal_type_eq
  binary_type_eq := D.binary_type_eq
  start_type_eq := D.start_type_eq
  startWord := D.startWord
  start_arity := D.start_arity
  start_anchor_eq := D.start_anchor_eq

@[simp] theorem toReachablePreCore_anchor
    (D : TrimmedPresentationPreCoreData T f)
    (A : N) :
    D.toReachablePreCore.anchor A = D.anchor A :=
  rfl

@[simp] theorem toReachablePreCore_expose
    (D : TrimmedPresentationPreCoreData T f)
    (A : N) :
    D.toReachablePreCore.expose A = D.expose A :=
  rfl

/-- The exposed base word associated with a nonterminal. -/
def exposedWord
    (D : TrimmedPresentationPreCoreData T f)
    (A : N) : Word α :=
  D.representatives.exposedWord A

/-- The exposed base word is accepted by the original grammar. -/
theorem exposedWord_mem
    (D : TrimmedPresentationPreCoreData T f)
    (A : N) :
    D.exposedWord A ∈ G.StringLanguage :=
  D.representatives.exposedWord_mem A

/-- The base anchor has the transported output type of its chosen typed
representative. -/
theorem anchor_tupleType_rep
    (D : TrimmedPresentationPreCoreData T f)
    (A : N) :
    tupleType obs (D.anchor A) =
      D.representatives.transportedRepOutput A :=
  D.representatives.anchor_tupleType A

/-- Terminal type equality in pre-core form. -/
theorem terminal_type
    (D : TrimmedPresentationPreCoreData T f)
    (ρ : TerminalRule N α)
    (hρ : ρ ∈ G.terminalRules)
    (hwt : G.arity ρ.lhs = 1) :
    tupleType obs (D.anchor ρ.lhs) =
      tupleType obs (castTuple hwt.symm ρ.outputTuple) :=
  D.terminal_type_eq ρ hρ hwt

/-- Binary type equality in pre-core form. -/
theorem binary_type
    (D : TrimmedPresentationPreCoreData T f)
    (ρ : BinaryRule N α G.arity)
    (hρ : ρ ∈ G.binaryRules) :
    tupleType obs (D.anchor ρ.lhs) =
      tupleType obs (ρ.apply (D.anchor ρ.left) (D.anchor ρ.right)) :=
  D.binary_type_eq ρ hρ

/-- Start type equality in pre-core form. -/
theorem start_type
    (D : TrimmedPresentationPreCoreData T f)
    (ρ : StartRule N)
    (hρ : ρ ∈ G.startRules)
    (hwt : G.arity ρ.child = G.arity G.start) :
    tupleType obs (D.anchor G.start) =
      tupleType obs (castTuple hwt (D.anchor ρ.child)) :=
  D.start_type_eq ρ hρ hwt

end TrimmedPresentationPreCoreData

end PreCoreFromTrimmedPresentation

end MCFG
