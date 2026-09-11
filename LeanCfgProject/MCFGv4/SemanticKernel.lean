import LeanCfgProject.MCFGv4.Basic
import Mathlib.Data.Set.Basic

/-!
# MCFGv4.SemanticKernel

Small source-independent semantic kernel used by the current-v4 paper-facing
orientation layer.

The manuscript's substitutability relation is sector-indexed by an orientation.
This file deliberately abstracts the concrete sector context type as `Ctx d`.
That lets us verify the logical core of observation refinement and the
shared-context implication before committing to the concrete orientation
encoding.

These results are support lemmas only.  The corresponding manuscript items
remain `PENDING` until the concrete oriented-context layer instantiates this
kernel and CI checks the exact paper-facing statements.
-/

namespace MCFGv4

universe u v w z

section AbstractContexts

variable {α : Type u} {M : Type v} [Monoid M]
variable {Ctx : Nat → Type w}

variable (fill : ∀ d : Nat, Ctx d → Tuple α d → Word α)

/-- Distribution of a tuple relative to an abstract arity-indexed context type. -/
def Distribution {d : Nat} (L : Set (Word α)) (x : Tuple α d) : Set (Ctx d) :=
  { c | fill d c x ∈ L }

/-- Two tuples share at least one accepting context. -/
def SharesContext {d : Nat} (L : Set (Word α)) (x y : Tuple α d) : Prop :=
  ∃ c : Ctx d, fill d c x ∈ L ∧ fill d c y ∈ L

/-- Abstract fixed-observation substitutability kernel.

The concrete v4 relation will instantiate `Ctx d` with one orientation sector at
a time. -/
def FixedTupleSubstitutable (f : Nat) (obs : α → M) (L : Set (Word α)) : Prop :=
  ∀ {d : Nat}, d ≤ f → 0 < d →
    ∀ x y : Tuple α d,
      tupleType obs x = tupleType obs y →
      SharesContext fill L x y →
      Distribution fill L x = Distribution fill L y

/-- Once the abstract substitutability premises are available, a concrete shared
accepting context yields equality of the corresponding distributions. -/
theorem sharedContext_distribution_eq
    {f d : Nat} {obs : α → M} {L : Set (Word α)}
    (hL : FixedTupleSubstitutable fill f obs L)
    (hd : d ≤ f) (hpos : 0 < d)
    (x y : Tuple α d)
    (htype : tupleType obs x = tupleType obs y)
    (hshare : SharesContext fill L x y) :
    Distribution fill L x = Distribution fill L y :=
  hL hd hpos x y htype hshare

end AbstractContexts

section Refinement

variable {α : Type u}
variable {M : Type v} {M' : Type w}
variable [Monoid M] [Monoid M']

/-- `obs'` refines `obs` when a multiplicative map from the finer observation
monoid to the coarser one commutes with all letter observations. -/
structure Refines (obs : α → M) (obs' : α → M') where
  map : M' → M
  map_one : map 1 = 1
  map_mul : ∀ x y : M', map (x * y) = map x * map y
  comm : ∀ a : α, map (obs' a) = obs a

variable {obs : α → M} {obs' : α → M'}

/-- Word observations commute with a refinement map. -/
theorem evalObs_refines (r : Refines obs obs') (word : Word α) :
    r.map (evalObs obs' word) = evalObs obs word := by
  induction word with
  | nil =>
      exact r.map_one
  | cons a rest ih =>
      change r.map (obs' a * evalObs obs' rest) = obs a * evalObs obs rest
      rw [r.map_mul, r.comm a, ih]

/-- Componentwise tuple observations commute with refinement. -/
theorem tupleType_refines_apply {d : Nat} (r : Refines obs obs')
    (x : Tuple α d) (i : Fin d) :
    r.map (tupleType obs' x i) = tupleType obs x i := by
  exact evalObs_refines r (x i)

variable {Ctx : Nat → Type z}
variable (fill : ∀ d : Nat, Ctx d → Tuple α d → Word α)

/-- Logical kernel for manuscript Proposition `prop:h-refinement-monotonicity`:
substitutability for a coarser observation implies substitutability for any
refining observation, for any fixed context family. -/
theorem fixedTupleSubstitutable_of_refines
    {f : Nat} {L : Set (Word α)}
    (r : Refines obs obs')
    (hL : FixedTupleSubstitutable fill f obs L) :
    FixedTupleSubstitutable fill f obs' L := by
  intro d hd hpos x y htype hshare
  have hcoarse : tupleType obs x = tupleType obs y := by
    funext i
    calc
      tupleType obs x i = r.map (tupleType obs' x i) :=
        (tupleType_refines_apply r x i).symm
      _ = r.map (tupleType obs' y i) := by
        exact congrArg r.map (congrFun htype i)
      _ = tupleType obs y i := tupleType_refines_apply r y i
  exact hL hd hpos x y hcoarse hshare

end Refinement

end MCFGv4
