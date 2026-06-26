import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Defs

/-
  FI v2.1 Lean experiment: fixed finite-monoid observations and tuple
  substitutability.

  This file is intentionally the first, small formalization layer for the paper

    Fixed-Monoid Tuple Substitution for Positive-Data Learning of
    Multiple Context-Free Grammars

  It formalizes the observation morphism as a letter observation `obs : α → M`,
  extended to words by multiplication.  This avoids committing, at this early
  stage, to a concrete encoding of the free monoid.  A tuple is represented as
  `Fin d → List α`, and sentence contexts are abstracted by a family `Ctx d`
  together with a filling operation.

  The main checked target in this first file is the paper's monotonicity under
  refinement of the observation morphism:

      if obs' refines obs, then (f, obs)-tuple-substitutability implies
      (f, obs')-tuple-substitutability.

  Next files can refine the abstract `Ctx` into named sentence contexts and then
  add the canonical grammar construction.
-/

namespace FIv21

universe u v w z

/-- Words over an alphabet.  We use `List α` as the free monoid carrier. -/
abbrev Word (α : Type u) := List α

/-- A tuple of arity `d` is a `Fin d`-indexed family of words. -/
abbrev Tuple (α : Type u) (d : Nat) := Fin d → Word α

section Observation

variable {α : Type u} {M : Type v} [Monoid M]

/-- Extend a letter observation `obs : α → M` multiplicatively to words. -/
def evalObs (obs : α → M) : Word α → M
  | [] => 1
  | a :: w => obs a * evalObs obs w

@[simp] theorem evalObs_nil (obs : α → M) : evalObs obs ([] : Word α) = 1 := rfl

@[simp] theorem evalObs_cons (obs : α → M) (a : α) (w : Word α) :
    evalObs obs (a :: w) = obs a * evalObs obs w := rfl

/-- Multiplicativity of the word observation. -/
theorem evalObs_append (obs : α → M) (u v : Word α) :
    evalObs obs (u ++ v) = evalObs obs u * evalObs obs v := by
  induction u with
  | nil =>
      simp [evalObs]
  | cons a u ih =>
      simp [evalObs, ih, mul_assoc]

/-- Componentwise observation type of a tuple. -/
def tupleType {d : Nat} (obs : α → M) (x : Tuple α d) : Fin d → M :=
  fun i => evalObs obs (x i)

end Observation

section Contexts

variable {α : Type u} {M : Type v} [Monoid M]
variable {Ctx : Nat → Type w}

/-- A filling operation for arity-indexed contexts.

For the paper's named sentence contexts, `Ctx d` will later be instantiated by a
record containing named holes, an exposure order/permutation, and intervening
terminal material.  This first file keeps that representation abstract. -/
variable (fill : ∀ d : Nat, Ctx d → Tuple α d → Word α)

/-- The distribution of an arity-`d` tuple: all contexts that accept it. -/
def Distribution {d : Nat} (L : Set (Word α)) (x : Tuple α d) : Set (Ctx d) :=
  { c | fill d c x ∈ L }

/-- Two tuples share at least one accepting context. -/
def SharesContext {d : Nat} (L : Set (Word α)) (x y : Tuple α d) : Prop :=
  ∃ c : Ctx d, fill d c x ∈ L ∧ fill d c y ∈ L

/-- Abstract version of `(f,h)`-tuple substitutability.

`obs : α → M` is the fixed finite observation on letters.  The condition is
semantic: inside a fixed componentwise observation fiber, one shared accepting
context forces equality of all accepting contexts. -/
def FixedTupleSubstitutable (f : Nat) (obs : α → M) (L : Set (Word α)) : Prop :=
  ∀ {d : Nat}, d ≤ f → 0 < d →
    ∀ x y : Tuple α d,
      tupleType obs x = tupleType obs y →
      SharesContext fill L x y →
      Distribution fill L x = Distribution fill L y

end Contexts

section Refinement

variable {α : Type u}
variable {M : Type v} {M' : Type w}
variable [Monoid M] [Monoid M']

/-- `obs'` refines `obs` if there is a monoid map from the finer monoid to the
coarser monoid that commutes with the letter observations. -/
structure Refines (obs : α → M) (obs' : α → M') where
  map : M' →* M
  comm : ∀ a : α, map (obs' a) = obs a

variable {obs : α → M} {obs' : α → M'}

/-- Evaluation commutes with refinement. -/
theorem evalObs_refines (r : Refines obs obs') (w : Word α) :
    r.map (evalObs obs' w) = evalObs obs w := by
  induction w with
  | nil =>
      simp [evalObs]
  | cons a w ih =>
      simp [evalObs, r.comm a, ih]

/-- Componentwise tuple types commute with refinement. -/
theorem tupleType_refines {d : Nat} (r : Refines obs obs') (x : Tuple α d) :
    (fun i : Fin d => r.map (tupleType obs' x i)) = tupleType obs x := by
  ext i
  exact evalObs_refines r (x i)

variable {Ctx : Nat → Type z}
variable (fill : ∀ d : Nat, Ctx d → Tuple α d → Word α)

/-- Monotonicity under refinement of the fixed observation morphism.

This is the Lean version of the paper's observation-refinement monotonicity:
refining the finite observation can only enlarge the fixed-monoid substitutable
class. -/
theorem fixedTupleSubstitutable_of_refines
    {f : Nat} {L : Set (Word α)}
    (r : Refines obs obs')
    (hL : FixedTupleSubstitutable fill f obs L) :
    FixedTupleSubstitutable fill f obs' L := by
  intro d hd hpos x y htype hshare
  apply hL hd hpos x y
  · -- Transport equality of the finer tuple types through the refinement map.
    calc
      tupleType obs x = (fun i : Fin d => r.map (tupleType obs' x i)) := by
        exact (tupleType_refines r x).symm
      _ = (fun i : Fin d => r.map (tupleType obs' y i)) := by
        rw [htype]
      _ = tupleType obs y := by
        exact tupleType_refines r y
  · exact hshare

end Refinement

section OneHoleContexts

variable {α : Type u}

/-- Ordinary two-sided contexts, useful for checking the fan-out-one/CFL case. -/
abbrev TwoSidedContext (α : Type u) := Word α × Word α

/-- The unique index of a one-component tuple. -/
def finOne : Fin 1 := ⟨0, by decide⟩

/-- Filling a one-hole two-sided context. -/
def fillOne (c : TwoSidedContext α) (x : Tuple α 1) : Word α :=
  c.1 ++ x finOne ++ c.2

/-- Arity-indexed context family that has two-sided contexts at arity one and
unit contexts elsewhere.  This is only a sandbox for fan-out-one experiments. -/
def SandboxCtx (α : Type u) : Nat → Type u
  | 1 => TwoSidedContext α
  | _ => PUnit

/-- Filling operation for `SandboxCtx`.  Non-one arities are deliberately
uninformative; the real MCFG file should replace this by named sentence
contexts. -/
def sandboxFill : ∀ d : Nat, SandboxCtx α d → Tuple α d → Word α
  | 1, c, x => fillOne c x
  | _, _, _ => []

end OneHoleContexts

section LearningSkeleton

variable {α : Type u}
variable {Hyp : Type v}

/-- A language-valued hypothesis interpretation. -/
abbrev HypLanguage (α : Type u) (Hyp : Type v) := Hyp → Set (Word α)

/-- Characteristic sample condition for a set-driven learner on finite samples.

This is deliberately minimal: it is the exact statement used in the paper's
positive-data argument, without formalizing computability or infinite texts yet. -/
def CharacteristicSample
    [DecidableEq α]
    (lang : HypLanguage α Hyp)
    (learner : Finset (Word α) → Hyp)
    (S : Finset (Word α))
    (L : Set (Word α)) : Prop :=
  (S : Set (Word α)) ⊆ L ∧
  ∀ K : Finset (Word α),
    (S : Set (Word α)) ⊆ (K : Set (Word α)) →
    (K : Set (Word α)) ⊆ L →
    lang (learner K) = L

/-- Once a finite sample contains a characteristic sample and remains positive,
the learner's hypothesis is exactly the target language. -/
theorem characteristicSample_correct
    [DecidableEq α]
    (lang : HypLanguage α Hyp)
    (learner : Finset (Word α) → Hyp)
    {S K : Finset (Word α)} {L : Set (Word α)}
    (hS : CharacteristicSample lang learner S L)
    (hSK : (S : Set (Word α)) ⊆ (K : Set (Word α)))
    (hKL : (K : Set (Word α)) ⊆ L) :
    lang (learner K) = L := by
  exact hS.2 K hSK hKL

end LearningSkeleton

end FIv21
