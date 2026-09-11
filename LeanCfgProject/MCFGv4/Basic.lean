/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Defs

/-!
# MCFGv4.Basic

Independent finite-observation foundation for the 2026-09-07 MCFG v4
manuscript baseline.

This module deliberately does not import `LeanCfgProject.MCFG2.*` or
`LeanCfgProject.FixedHCFG.*`.  The purpose is to prevent legacy experimental
interfaces from silently becoming assumptions of the current paper-facing
formalization.

The definitions here correspond to the stable part of Section 2:

* words over a terminal alphabet;
* finite monoid observations induced by letter values;
* tuples of words and their componentwise observation type;
* an explicit finite-observation wrapper.

No theorem in this file is yet claimed to discharge one of the 42 theorem-like
items in `THEOREM_INVENTORY.md`.
-/

namespace MCFGv4

universe u v

/-- Words over a terminal alphabet. -/
abbrev Word (α : Type u) := List α

/-- A tuple of arity `d` is a `Fin d`-indexed family of words. -/
abbrev Tuple (α : Type u) (d : Nat) := Fin d → Word α

section Observation

variable {α : Type u} {M : Type v} [Monoid M]

/-- Extend the values of a finite observation on letters multiplicatively to words. -/
def evalObs (obs : α → M) : Word α → M
  | [] => 1
  | a :: rest => obs a * evalObs obs rest

@[simp] theorem evalObs_nil (obs : α → M) :
    evalObs obs ([] : Word α) = 1 := rfl

@[simp] theorem evalObs_cons (obs : α → M) (a : α) (rest : Word α) :
    evalObs obs (a :: rest) = obs a * evalObs obs rest := rfl

/-- The induced observation is multiplicative with respect to word concatenation. -/
theorem evalObs_append (obs : α → M) (u v : Word α) :
    evalObs obs (u ++ v) = evalObs obs u * evalObs obs v := by
  induction u with
  | nil =>
      simp [evalObs]
  | cons a rest ih =>
      simp [evalObs, ih, mul_assoc]

/-- Componentwise observation value of a tuple, corresponding to `h^(d)`. -/
def tupleType {d : Nat} (obs : α → M) (x : Tuple α d) : Fin d → M :=
  fun i => evalObs obs (x i)

/-- Explicit finite observation data at the letter level.

The monoid structure supplies the multiplication table abstractly and `Fintype M`
records finiteness.  `evalObs` is the induced homomorphism on words. -/
structure ExplicitFiniteObservation (α : Type u) (M : Type v)
    [Monoid M] [Fintype M] where
  obs : α → M

end Observation

end MCFGv4
