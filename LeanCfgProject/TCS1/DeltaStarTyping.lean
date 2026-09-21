import LeanCfgProject.TCS1.DeltaStarFixedWindow
import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v78: finite h_star typing for the Delta-star example

The manuscript types a word by three pieces of finite boundary information:
its first symbol, its last symbol, and whether the factor ba occurs.  This
module gives that summary an explicit nine-element monoid structure.

The empty word is one state.  A nonempty state stores first/last symbols and a
Boolean ba flag.  Multiplication is exactly concatenation of summaries:
first comes from the left factor, last from the right factor, and the ba flag
is the disjunction of the two internal flags with the boundary test
left.last=b and right.first=a.

This is the finite homomorphism h_star used by the nonlinear Delta-star
proposition.  Substitutability is proved in a later layer.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

/-- Exact finite boundary summary used by h_star. -/
inductive StarType where
  | empty
  | nonempty
      (first : Symbol)
      (last : Symbol)
      (hasBA : Bool)
  deriving DecidableEq, Fintype, Repr

/-- Concatenation product on boundary summaries. -/
def starMul : StarType → StarType → StarType
  | .empty, y => y
  | x, .empty => x
  | .nonempty f l p,
      .nonempty f' l' q =>
      .nonempty f l'
        (p || q || ((l == b) && (f' == a)))

/-- Empty-word summary. -/
def starOne : StarType :=
  .empty

theorem starMul_one_left
    (x : StarType) :
    starMul starOne x = x := by
  cases x <;> rfl

theorem starMul_one_right
    (x : StarType) :
    starMul x starOne = x := by
  cases x <;> rfl

/-- Associativity is a finite check on the nine summary states. -/
theorem starMul_assoc
    (x y z : StarType) :
    starMul (starMul x y) z =
      starMul x (starMul y z) := by
  native_decide

instance starTypeMonoid :
    Monoid StarType where
  one := starOne
  mul := starMul
  one_mul := starMul_one_left
  mul_one := starMul_one_right
  mul_assoc := starMul_assoc

/-- Summary of a single terminal. -/
def letterType
    (s : Symbol) :
    StarType :=
  .nonempty s s false

/-- Word summary h_star. -/
def starSummary :
    Word Symbol → StarType
  | [] => .empty
  | s :: w =>
      letterType s * starSummary w

@[simp] theorem starSummary_nil :
    starSummary ([] : Word Symbol) = 1 := by
  rfl

theorem starSummary_append
    (u v : Word Symbol) :
    starSummary (u ++ v) =
      starSummary u * starSummary v := by
  induction u with
  | nil =>
      simp [starSummary]
  | cons s u ih =>
      simp only [List.cons_append, starSummary]
      rw [ih]
      exact (mul_assoc _ _ _).symm

/-- Concrete finite-monoid homomorphism h_star. -/
def starTyping :
    FixedFiniteMonoidHom
      Symbol StarType where
  h := starSummary
  map_nil := starSummary_nil
  map_append := starSummary_append

/-- First symbol of a word, with none on the empty word. -/
def firstSymbol? :
    Word Symbol → Option Symbol
  | [] => none
  | s :: _ => some s

/-- Last symbol of a word, with none on the empty word. -/
def lastSymbol? :
    Word Symbol → Option Symbol
  | [] => none
  | s :: w =>
      match lastSymbol? w with
      | none => some s
      | some t => some t

/-- Whether the adjacent factor ba occurs in the word. -/
def containsBA :
    Word Symbol → Bool
  | [] => false
  | s :: w =>
      ((s == b) &&
        (firstSymbol? w == some a)) ||
      containsBA w

/-- Read the first-symbol component out of a summary. -/
def StarType.first? : StarType → Option Symbol
  | .empty => none
  | .nonempty f _ _ => some f

/-- Read the last-symbol component out of a summary. -/
def StarType.last? : StarType → Option Symbol
  | .empty => none
  | .nonempty _ l _ => some l

/-- Read the ba flag out of a summary. -/
def StarType.ba : StarType → Bool
  | .empty => false
  | .nonempty _ _ q => q

theorem starSummary_eq_empty_iff
    (w : Word Symbol) :
    starSummary w = .empty ↔
      w = [] := by
  cases w with
  | nil =>
      simp [starSummary]
  | cons s w =>
      cases h : starSummary w <;>
        simp [starSummary, letterType,
          starMul, h]

/-- The first component of h_star is exactly the first terminal. -/
theorem starType_first_summary
    (w : Word Symbol) :
    (starSummary w).first? =
      firstSymbol? w := by
  cases w with
  | nil =>
      rfl
  | cons s w =>
      cases h : starSummary w <;>
        simp [starSummary, letterType,
          starMul, StarType.first?,
          firstSymbol?, h]

/-- Nonempty words have nonempty h_star state. -/
theorem starSummary_ne_empty_of_ne_nil
    {w : Word Symbol}
    (hw : w ≠ []) :
    starSummary w ≠ .empty := by
  intro h
  exact hw
    ((starSummary_eq_empty_iff w).1 h)

/-- The last component of h_star is exactly the last terminal. -/
theorem starType_last_summary
    (w : Word Symbol) :
    (starSummary w).last? =
      lastSymbol? w := by
  induction w with
  | nil =>
      rfl
  | cons s w ih =>
      cases w with
      | nil =>
          rfl
      | cons t w =>
          have hne :
              starSummary (t :: w) ≠
                StarType.empty :=
            starSummary_ne_empty_of_ne_nil
              (by simp)
          cases hq :
              starSummary (t :: w) with
          | empty =>
              exact False.elim (hne hq)
          | nonempty f l q =>
              have ih' := ih
              simp [starSummary, letterType,
                starMul, StarType.last?,
                lastSymbol?, hq] at ih' ⊢
              exact ih'

/-- The Boolean component of h_star is exactly occurrence of ba. -/
theorem starType_ba_summary
    (w : Word Symbol) :
    (starSummary w).ba =
      containsBA w := by
  induction w with
  | nil =>
      rfl
  | cons s w ih =>
      cases hq : starSummary w with
      | empty =>
          have hw0 :
              w = [] :=
            (starSummary_eq_empty_iff w).1 hq
          subst w
          simp [starSummary, letterType,
            starMul, StarType.ba,
            containsBA, firstSymbol?]
      | nonempty f l q =>
          have hf :=
            starType_first_summary w
          rw [hq] at hf
          simp [StarType.first?] at hf
          simp [starSummary, letterType,
            starMul, StarType.ba,
            containsBA, hq, ← hf, ih]

/--
Equality of h_star types gives exactly the three finite features used in the
manuscript.
-/
theorem starTyping_eq_features
    {x y : Word Symbol}
    (hxy :
      starTyping.h x =
        starTyping.h y) :
    firstSymbol? x = firstSymbol? y
      ∧
    lastSymbol? x = lastSymbol? y
      ∧
    containsBA x = containsBA y := by
  change starSummary x = starSummary y at hxy
  constructor
  · calc
      firstSymbol? x =
          (starSummary x).first? :=
        (starType_first_summary x).symm
      _ =
          (starSummary y).first? := by
        rw [hxy]
      _ =
          firstSymbol? y :=
        starType_first_summary y
  constructor
  · calc
      lastSymbol? x =
          (starSummary x).last? :=
        (starType_last_summary x).symm
      _ =
          (starSummary y).last? := by
        rw [hxy]
      _ =
          lastSymbol? y :=
        starType_last_summary y
  · calc
      containsBA x =
          (starSummary x).ba :=
        (starType_ba_summary x).symm
      _ =
          (starSummary y).ba := by
        rw [hxy]
      _ =
          containsBA y :=
        starType_ba_summary y

end DeltaStar
end TCS1
end LeanCfgProject
