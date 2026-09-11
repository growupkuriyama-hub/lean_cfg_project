import LeanCfgProject.MCFGv4.TupleSubstitutability

/-!
# MCFGv4.RecognizableSlice

Semantic core of Proposition `prop:h-recognizable-in-slice` from the frozen
2026-09-07 manuscript.

The full paper proposition also states membership in the `f`-MCFL target class,
using the standard fact that a language recognized by a finite monoid is regular.
The present module verifies the nontrivial fixed-observation substitutability
part directly at the oriented-tuple level.  The regular/MCFL wrapper will be
connected once the current-v4 grammar semantics layer is available.
-/

namespace MCFGv4

universe u v

section

variable {α : Type u}
variable {M : Type v} [Monoid M]

/-- Evaluation of a concatenated list of words is the product of their
individual observation values. -/
theorem evalObs_foldr_append (obs : α → M) (words : List (Word α)) :
    evalObs obs (words.foldr (· ++ ·) []) =
      (words.map (evalObs obs)).foldr (· * ·) 1 := by
  induction words with
  | nil => simp
  | cons w rest ih =>
      simp [evalObs_append, ih]

/-- Observation value of an oriented tuple filling, written as the ordered
product of spacer and component observation values. -/
theorem evalObs_sectorFill_formula {d : Nat}
    (obs : α → M) (σ : Equiv.Perm (Fin d))
    (E : SectorContext α d σ) (x : Tuple α d) :
    evalObs obs (sectorFill E x) =
      ((List.ofFn fun i : Fin d =>
          evalObs obs (E.spacers i.castSucc) * evalObs obs (x (σ i))).foldr
        (· * ·) 1) *
      evalObs obs (E.spacers (Fin.last d)) := by
  rw [sectorFill, evalObs_append, evalObs_foldr_append, List.map_ofFn]
  have hfun :
      (evalObs obs ∘ fun i : Fin d => E.spacers i.castSucc ++ x (σ i)) =
        (fun i : Fin d =>
          evalObs obs (E.spacers i.castSucc) * evalObs obs (x (σ i))) := by
    funext i
    exact evalObs_append obs (E.spacers i.castSucc) (x (σ i))
  rw [hfun]

/-- Equal componentwise observation type makes every fixed oriented context
have the same total observation value after filling. -/
theorem evalObs_sectorFill_eq_of_tupleType_eq {d : Nat}
    (obs : α → M) (σ : Equiv.Perm (Fin d))
    (E : SectorContext α d σ) (x y : Tuple α d)
    (htype : tupleType obs x = tupleType obs y) :
    evalObs obs (sectorFill E x) = evalObs obs (sectorFill E y) := by
  rw [evalObs_sectorFill_formula, evalObs_sectorFill_formula]
  have hcomp : ∀ i : Fin d,
      evalObs obs (x (σ i)) = evalObs obs (y (σ i)) := by
    intro i
    exact congrFun htype (σ i)
  simp_rw [hcomp]

/-- Language recognized by the fixed observation and accepting set `P`. -/
def RecognizedLanguage (obs : α → M) (P : Set M) : Set (Word α) :=
  { w | evalObs obs w ∈ P }

/-- Semantic content of Proposition `prop:h-recognizable-in-slice`:
for every fan-out cap, an `h`-recognized language is orientation-aware
`(f,h)`-tuple-substitutable.  The shared-context premise is not needed. -/
theorem recognizedLanguage_tupleSubstitutable
    (f : Nat) (obs : α → M) (P : Set M) :
    TupleSubstitutable f obs (RecognizedLanguage obs P) := by
  intro d hpos hdf σ x y htype hshare
  ext E
  change evalObs obs (sectorFill E x) ∈ P ↔
    evalObs obs (sectorFill E y) ∈ P
  rw [evalObs_sectorFill_eq_of_tupleType_eq obs σ E x y htype]

end

end MCFGv4
