import LeanCfgProject.TCS1.LinearRawFinitePreprocessing
import LeanCfgProject.TCS1.PreparedLinearGrammarSemantics

/-!
# TCS #1: semantic bridge from raw unit-free rules to the finite prepared CFG

LinearRawFinitePreprocessing constructs the finite prepared grammar obtained
after linear epsilon elimination and unit-closure copying.  This module proves
that the construction has exactly the semantic unit-free derivation relation
from LinearRawEpsilonUnitSemantics.

Consequently the arbitrary indexed linear source can now pass through

  raw representation -> epsilon elimination -> unit elimination
  -> finite prepared grammar

without any semantic gap before the specialized linear-spine normalization.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearRawUnitFreePreparedBridge

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype P]

/-- Deterministic false-variant RHS is the prepared source RHS itself. -/
theorem rawLinearCorePreparedRhs_false_eq
    (G : RawLinearIndexedCFG N α P)
    (p : P)
    (rhs : PreparedLinearRhs N α)
    (hrhs :
      G.rhs p = RawLinearRhs.prepared rhs)
    (hvalid :
      RawLinearCoreVariantValid G (p, false)) :
    rawLinearCorePreparedRhs G
        (⟨(p, false), hvalid⟩ :
          RawLinearCoreRuleIndex G)
      =
    rhs := by
  cases hraw : G.rhs p with
  | epsilon =>
      simp [hraw] at hrhs
  | unit B =>
      simp [hraw] at hrhs
  | prepared rhs₀ =>
      have heq : rhs₀ = rhs := by
        injection hrhs
      subst rhs₀
      simp [rawLinearCorePreparedRhs, hraw]

/-- Deterministic true-variant RHS is the terminal dropped-core rule. -/
theorem rawLinearCorePreparedRhs_true_eq
    (G : RawLinearIndexedCFG N α P)
    (p : P)
    (left : List α)
    (core : N)
    (right : List α)
    (hnonunit : left ≠ [] ∨ right ≠ [])
    (hrhs :
      G.rhs p =
        RawLinearRhs.prepared
          (PreparedLinearRhs.around
            left core right hnonunit))
    (hnullable :
      RawLinearNullable G core)
    (hvalid :
      RawLinearCoreVariantValid G (p, true)) :
    rawLinearCorePreparedRhs G
        (⟨(p, true), hvalid⟩ :
          RawLinearCoreRuleIndex G)
      =
    droppedCorePreparedRhs
      (N := N) left right hnonunit := by
  cases hraw : G.rhs p with
  | epsilon =>
      simp [hraw] at hrhs
  | unit B =>
      simp [hraw] at hrhs
  | prepared rhs₀ =>
      cases rhs₀ with
      | terminals head tail =>
          simp [hraw] at hrhs
      | around left₀ core₀ right₀ hnonunit₀ =>
          have heq :
              PreparedLinearRhs.around
                  left₀ core₀ right₀ hnonunit₀
                =
              PreparedLinearRhs.around
                  left core right hnonunit := by
            injection hrhs
          cases heq
          simp [rawLinearCorePreparedRhs, hraw]

/--
A prepared grammar rule whose RHS is the deterministic dropped-core rule
derives exactly the surviving terminal context.
-/
theorem preparedLinearDerives_droppedCore
    (G : RawLinearIndexedCFG N α P)
    (q : RawLinearPreparedRuleIndex G)
    (left right : List α)
    (hnonunit : left ≠ [] ∨ right ≠ [])
    (hrhs :
      (rawLinearPreparedGrammar G).rhs q =
        droppedCorePreparedRhs
          (N := N) left right hnonunit) :
    PreparedLinearDerives
      (rawLinearPreparedGrammar G)
      ((rawLinearPreparedGrammar G).lhs q)
      (left ++ right) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact False.elim
            (hnonunit.elim
              (fun h => h rfl)
              (fun h => h rfl))
      | cons b rest =>
          exact
            PreparedLinearDerives.terminals
              q b rest
              (by
                simpa [droppedCorePreparedRhs]
                  using hrhs)
  | cons a rest =>
      have d :=
        PreparedLinearDerives.terminals
          (G := rawLinearPreparedGrammar G)
          q a (rest ++ right)
          (by
            simpa [droppedCorePreparedRhs]
              using hrhs)
      simpa using d

/--
Every semantic unit-free derivation is reproduced by the finite prepared
grammar.
-/
theorem rawLinearUnitFreeDerives_to_prepared
    (G : RawLinearIndexedCFG N α P)
    {A : N}
    {word : List α}
    (d : RawLinearUnitFreeDerives G A word) :
    PreparedLinearDerives
      (rawLinearPreparedGrammar G) A word := by
  induction d with
  | terminals A p head tail hreach hrhs =>
      have hvalid :
          RawLinearCoreVariantValid G (p, false) := by
        change ∃ rhs : PreparedLinearRhs N α,
          G.rhs p = RawLinearRhs.prepared rhs
        exact
          ⟨PreparedLinearRhs.terminals head tail,
            hrhs⟩
      let coreq : RawLinearCoreRuleIndex G :=
        ⟨(p, false), hvalid⟩
      let q : RawLinearPreparedRuleIndex G :=
        ⟨(A, coreq), hreach⟩
      have hcore :
          rawLinearCorePreparedRhs G coreq =
            PreparedLinearRhs.terminals
              head tail := by
        simpa [coreq] using
          (rawLinearCorePreparedRhs_false_eq
            G p
            (PreparedLinearRhs.terminals head tail)
            hrhs hvalid)
      have dq :
          PreparedLinearDerives
            (rawLinearPreparedGrammar G)
            ((rawLinearPreparedGrammar G).lhs q)
            (head :: tail) :=
        PreparedLinearDerives.terminals
          q head tail
          (by
            change
              rawLinearCorePreparedRhs G coreq =
                PreparedLinearRhs.terminals head tail
            exact hcore)
      simpa [rawLinearPreparedGrammar, q, coreq]
        using dq

  | @around A p left core right hnonunit hreach hrhs word child ih =>
      have hvalid :
          RawLinearCoreVariantValid G (p, false) := by
        change ∃ rhs : PreparedLinearRhs N α,
          G.rhs p = RawLinearRhs.prepared rhs
        exact
          ⟨PreparedLinearRhs.around
              left core right hnonunit,
            hrhs⟩
      let coreq : RawLinearCoreRuleIndex G :=
        ⟨(p, false), hvalid⟩
      let q : RawLinearPreparedRuleIndex G :=
        ⟨(A, coreq), hreach⟩
      have hcore :
          rawLinearCorePreparedRhs G coreq =
            PreparedLinearRhs.around
              left core right hnonunit := by
        simpa [coreq] using
          (rawLinearCorePreparedRhs_false_eq
            G p
            (PreparedLinearRhs.around
              left core right hnonunit)
            hrhs hvalid)
      have dq :
          PreparedLinearDerives
            (rawLinearPreparedGrammar G)
            ((rawLinearPreparedGrammar G).lhs q)
            (left ++ word ++ right) :=
        PreparedLinearDerives.around
          q left core right hnonunit
          (by
            change
              rawLinearCorePreparedRhs G coreq =
                PreparedLinearRhs.around
                  left core right hnonunit
            exact hcore)
          ih
      simpa [rawLinearPreparedGrammar, q, coreq]
        using dq

  | dropCore A p left core right hnonunit hreach hrhs hnullable =>
      have hvalid :
          RawLinearCoreVariantValid G (p, true) := by
        change
          ∃ left' : List α,
          ∃ core' : N,
          ∃ right' : List α,
          ∃ hnonunit' : left' ≠ [] ∨ right' ≠ [],
            G.rhs p =
              RawLinearRhs.prepared
                (PreparedLinearRhs.around
                  left' core' right' hnonunit')
            ∧
            RawLinearNullable G core'
        exact
          ⟨left, core, right, hnonunit,
            hrhs, hnullable⟩
      let coreq : RawLinearCoreRuleIndex G :=
        ⟨(p, true), hvalid⟩
      let q : RawLinearPreparedRuleIndex G :=
        ⟨(A, coreq), hreach⟩
      have hcore :
          rawLinearCorePreparedRhs G coreq =
            droppedCorePreparedRhs
              (N := N) left right hnonunit := by
        simpa [coreq] using
          (rawLinearCorePreparedRhs_true_eq
            G p left core right hnonunit
            hrhs hnullable hvalid)
      have dq :=
        preparedLinearDerives_droppedCore
          G q left right hnonunit
          (by
            change
              rawLinearCorePreparedRhs G coreq =
                droppedCorePreparedRhs
                  (N := N) left right hnonunit
            exact hcore)
      simpa [rawLinearPreparedGrammar, q, coreq]
        using dq

/--
Every finite-prepared derivation expands to the semantic unit-free derivation
relation.
-/
theorem preparedDerives_to_rawLinearUnitFree
    (G : RawLinearIndexedCFG N α P)
    {A : N}
    {word : List α}
    (d :
      PreparedLinearDerives
        (rawLinearPreparedGrammar G) A word) :
    RawLinearUnitFreeDerives G A word := by
  induction d with
  | terminals q head tail hrhs =>
      rcases q with ⟨⟨A, coreq⟩, hreach⟩
      rcases coreq with
        ⟨⟨p, variant⟩, hvalid⟩
      cases variant with
      | false =>
          have hvalid0 := hvalid
          change
            ∃ rhs : PreparedLinearRhs N α,
              G.rhs p = RawLinearRhs.prepared rhs
            at hvalid
          rcases hvalid with ⟨rhs, hsource⟩
          have hdet :
              rawLinearCorePreparedRhs G
                  (⟨(p, false), hvalid0⟩ :
                    RawLinearCoreRuleIndex G)
                =
              rhs :=
            rawLinearCorePreparedRhs_false_eq
              G p rhs hsource hvalid0
          change
            rawLinearCorePreparedRhs G
                (⟨(p, false), hvalid0⟩ :
                  RawLinearCoreRuleIndex G)
              =
            PreparedLinearRhs.terminals head tail
            at hrhs
          have hrhsSource :
              G.rhs p =
                RawLinearRhs.prepared
                  (PreparedLinearRhs.terminals
                    head tail) := by
            rw [hsource, ← hdet, hrhs]
          exact
            RawLinearUnitFreeDerives.terminals
              A p head tail hreach hrhsSource

      | true =>
          change
            RawLinearUnitFreeDerives G A
              (head :: tail)
          have hvalid0 := hvalid
          change
            ∃ left : List α,
            ∃ core : N,
            ∃ right : List α,
            ∃ hnonunit : left ≠ [] ∨ right ≠ [],
              G.rhs p =
                RawLinearRhs.prepared
                  (PreparedLinearRhs.around
                    left core right hnonunit)
              ∧
              RawLinearNullable G core
            at hvalid
          rcases hvalid with
            ⟨left, core, right, hnonunit,
              hsource, hnullable⟩
          have hdet :
              rawLinearCorePreparedRhs G
                  (⟨(p, true), hvalid0⟩ :
                    RawLinearCoreRuleIndex G)
                =
              droppedCorePreparedRhs
                (N := N) left right hnonunit :=
            rawLinearCorePreparedRhs_true_eq
              G p left core right hnonunit
              hsource hnullable hvalid0
          change
            rawLinearCorePreparedRhs G
                (⟨(p, true), hvalid0⟩ :
                  RawLinearCoreRuleIndex G)
              =
            PreparedLinearRhs.terminals head tail
            at hrhs
          have hdrop :
              droppedCorePreparedRhs
                  (N := N) left right hnonunit
                =
              PreparedLinearRhs.terminals
                head tail := by
            rw [← hdet]
            exact hrhs
          have ddrop :=
            RawLinearUnitFreeDerives.dropCore
              A p left core right hnonunit
              hreach hsource hnullable
          cases left with
          | nil =>
              cases right with
              | nil =>
                  exact False.elim
                    (hnonunit.elim
                      (fun h => h rfl)
                      (fun h => h rfl))
              | cons b rest =>
                  simp [droppedCorePreparedRhs] at hdrop
                  cases hdrop
                  simpa using ddrop
          | cons a rest =>
              simp [droppedCorePreparedRhs] at hdrop
              cases hdrop
              simpa using ddrop

  | @around q left core right hnonunit hrhs word child ih =>
      rcases q with ⟨⟨A, coreq⟩, hreach⟩
      rcases coreq with
        ⟨⟨p, variant⟩, hvalid⟩
      cases variant with
      | false =>
          have hvalid0 := hvalid
          change
            ∃ rhs : PreparedLinearRhs N α,
              G.rhs p = RawLinearRhs.prepared rhs
            at hvalid
          rcases hvalid with ⟨rhs, hsource⟩
          have hdet :
              rawLinearCorePreparedRhs G
                  (⟨(p, false), hvalid0⟩ :
                    RawLinearCoreRuleIndex G)
                =
              rhs :=
            rawLinearCorePreparedRhs_false_eq
              G p rhs hsource hvalid0
          change
            rawLinearCorePreparedRhs G
                (⟨(p, false), hvalid0⟩ :
                  RawLinearCoreRuleIndex G)
              =
            PreparedLinearRhs.around
              left core right hnonunit
            at hrhs
          have hrhsSource :
              G.rhs p =
                RawLinearRhs.prepared
                  (PreparedLinearRhs.around
                    left core right hnonunit) := by
            rw [hsource, ← hdet, hrhs]
          exact
            RawLinearUnitFreeDerives.around
              A p left core right hnonunit
              hreach hrhsSource ih

      | true =>
          have hvalid0 := hvalid
          change
            ∃ left' : List α,
            ∃ core' : N,
            ∃ right' : List α,
            ∃ hnonunit' : left' ≠ [] ∨ right' ≠ [],
              G.rhs p =
                RawLinearRhs.prepared
                  (PreparedLinearRhs.around
                    left' core' right' hnonunit')
              ∧
              RawLinearNullable G core'
            at hvalid
          rcases hvalid with
            ⟨left', core', right', hnonunit',
              hsource, hnullable⟩
          have hdet :
              rawLinearCorePreparedRhs G
                  (⟨(p, true), hvalid0⟩ :
                    RawLinearCoreRuleIndex G)
                =
              droppedCorePreparedRhs
                (N := N) left' right' hnonunit' :=
            rawLinearCorePreparedRhs_true_eq
              G p left' core' right' hnonunit'
              hsource hnullable hvalid0
          change
            rawLinearCorePreparedRhs G
                (⟨(p, true), hvalid0⟩ :
                  RawLinearCoreRuleIndex G)
              =
            PreparedLinearRhs.around
              left core right hnonunit
            at hrhs
          have himpossible :
              droppedCorePreparedRhs
                  (N := N) left' right' hnonunit'
                =
              PreparedLinearRhs.around
                left core right hnonunit := by
            rw [← hdet]
            exact hrhs
          cases left' with
          | nil =>
              cases right' with
              | nil =>
                  exact False.elim
                    (hnonunit'.elim
                      (fun h => h rfl)
                      (fun h => h rfl))
              | cons b rest =>
                  simp [droppedCorePreparedRhs]
                    at himpossible
          | cons a rest =>
              simp [droppedCorePreparedRhs]
                at himpossible

/-- Exact derivation equivalence for the finite prepared preprocessing output. -/
theorem rawLinearUnitFreeDerives_iff_prepared
    (G : RawLinearIndexedCFG N α P)
    (A : N)
    (word : List α) :
    RawLinearUnitFreeDerives G A word
      ↔
    PreparedLinearDerives
      (rawLinearPreparedGrammar G) A word := by
  constructor
  · exact rawLinearUnitFreeDerives_to_prepared G
  · exact preparedDerives_to_rawLinearUnitFree G

end LinearRawUnitFreePreparedBridge

end TCS1
end LeanCfgProject
