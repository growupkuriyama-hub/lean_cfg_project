import LeanCfgProject.TCS1.LinearRawPreprocessingFacade
import LeanCfgProject.TCS1.PreparedLinearGrammarSemantics

/-!
# TCS #1: finite prepared presentation after raw epsilon/unit elimination

The semantic unit-free grammar from LinearRawEpsilonUnitSemantics still has
rules described by unit-closure witnesses. This module turns that rule family
back into the finite indexed PreparedLinearIndexedCFG representation used by
the verified linear-spine normalization.

A finite rule slot is either

* a copied non-unit source production, or
* the terminal-only rule obtained by deleting a nullable core from u B v.

The slot space is just two copies of N x P. Validity is a proposition, so its
subtype is finite whenever N and P are finite. A chosen prepared RHS is
attached to each valid slot, and the choice is harmless because the produced
RHS is functional for a fixed slot.

The main theorem proves exact equivalence between the semantic unit-free
derivation relation and derivations of the finite prepared grammar.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearRawUnitFreePreparedBridge

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- A terminal-only prepared RHS representing one known nonempty word. -/
def preparedTerminalRhsOfNonempty
    (xs : List α)
    (hne : xs ≠ []) :
    PreparedLinearRhs N α :=
  match hxs : xs with
  | [] => False.elim (hne hxs)
  | head :: tail =>
      PreparedLinearRhs.terminals head tail

/-- The prepared terminal RHS realizes exactly the supplied terminal word. -/
theorem preparedTerminalRhsOfNonempty_realizes
    (L : N → Set (List α))
    (xs : List α)
    (hne : xs ≠ [])
    (word : List α) :
    PreparedLinearRhs.realizes L
        (preparedTerminalRhsOfNonempty
          (N := N) xs hne) word
      ↔
    word = xs := by
  cases hxs : xs with
  | nil =>
      exact False.elim (hne hxs)
  | cons head tail =>
      subst xs
      rfl

/-- A non-unit context produces a nonempty terminal word after core deletion. -/
theorem linearContext_append_ne_nil
    (left right : List α)
    (hnonunit : left ≠ [] ∨ right ≠ []) :
    left ++ right ≠ [] := by
  intro hnil
  have hparts :
      left = [] ∧ right = [] :=
    List.append_eq_nil_iff.mp hnil
  exact hnonunit.elim
    (fun h => h hparts.1)
    (fun h => h hparts.2)

/--
Finite ambient slots for copied and nullable-core-deletion rules.
Left slots are copied source rules; right slots are deletion rules.
-/
abbrev RawLinearUnitFreeRuleSlot
    (N : Type u)
    (P : Type w) :=
  (N × P) ⊕ (N × P)

/-- The left-hand side encoded by one finite rule slot. -/
def rawLinearUnitFreeRuleSlotLhs :
    RawLinearUnitFreeRuleSlot N P → N
  | Sum.inl q => q.1
  | Sum.inr q => q.1

/--
A slot produces one prepared RHS.

For copied rules the source raw RHS is already prepared. For deletion rules
the source is u B v, B is nullable, and the produced RHS is the deterministic
terminal representation of u v.
-/
inductive RawLinearUnitFreeSlotProduces
    (G : RawLinearIndexedCFG N α P) :
    RawLinearUnitFreeRuleSlot N P →
    PreparedLinearRhs N α → Prop
  | keep
      (A : N)
      (p : P)
      (rhs : PreparedLinearRhs N α)
      (hreach :
        RawLinearUnitReach G A (G.lhs p))
      (hrhs :
        G.rhs p = RawLinearRhs.prepared rhs) :
      RawLinearUnitFreeSlotProduces G
        (Sum.inl (A, p)) rhs
  | drop
      (A : N)
      (p : P)
      (left : List α)
      (core : N)
      (right : List α)
      (hnonunit : left ≠ [] ∨ right ≠ [])
      (hreach :
        RawLinearUnitReach G A (G.lhs p))
      (hrhs :
        G.rhs p =
          RawLinearRhs.prepared
            (PreparedLinearRhs.around
              left core right hnonunit))
      (hnullable :
        RawLinearNullable G core) :
      RawLinearUnitFreeSlotProduces G
        (Sum.inr (A, p))
        (preparedTerminalRhsOfNonempty
          (N := N)
          (left ++ right)
          (linearContext_append_ne_nil
            left right hnonunit))

/-- A valid finite slot is one that produces some prepared RHS. -/
abbrev RawLinearUnitFreeRuleIndex
    (G : RawLinearIndexedCFG N α P) :=
  {slot : RawLinearUnitFreeRuleSlot N P //
    ∃ rhs : PreparedLinearRhs N α,
      RawLinearUnitFreeSlotProduces G slot rhs}

noncomputable instance rawLinearUnitFreeRuleIndexFintype
    [Fintype N] [Fintype P]
    (G : RawLinearIndexedCFG N α P) :
    Fintype (RawLinearUnitFreeRuleIndex G) :=
  Fintype.ofFinite _

/-- Chosen RHS of a valid finite unit-free slot. -/
noncomputable def rawLinearUnitFreeChosenRhs
    (G : RawLinearIndexedCFG N α P)
    (q : RawLinearUnitFreeRuleIndex G) :
    PreparedLinearRhs N α :=
  Classical.choose q.2

theorem rawLinearUnitFreeChosenRhs_spec
    (G : RawLinearIndexedCFG N α P)
    (q : RawLinearUnitFreeRuleIndex G) :
    RawLinearUnitFreeSlotProduces G q.1
      (rawLinearUnitFreeChosenRhs G q) :=
  Classical.choose_spec q.2

/-- A fixed slot can produce only one prepared RHS. -/
theorem rawLinearUnitFreeSlotProduces_functional
    (G : RawLinearIndexedCFG N α P)
    {slot : RawLinearUnitFreeRuleSlot N P}
    {rhs₁ rhs₂ : PreparedLinearRhs N α}
    (h₁ : RawLinearUnitFreeSlotProduces G slot rhs₁)
    (h₂ : RawLinearUnitFreeSlotProduces G slot rhs₂) :
    rhs₁ = rhs₂ := by
  cases h₁ with
  | keep A p rhs hreach hrhs =>
      cases h₂ with
      | keep A' p' rhs' hreach' hrhs' =>
          have hsource := hrhs.trans hrhs'.symm
          injection hsource
  | drop A p left core right hnonunit hreach hrhs hnullable =>
      cases h₂ with
      | drop A' p' left' core' right' hnonunit' hreach' hrhs' hnullable' =>
          have hsource := hrhs.trans hrhs'.symm
          injection hsource with hprepared
          cases hprepared
          rfl

/-- The chosen RHS equals any RHS proved to be produced by the same slot. -/
theorem rawLinearUnitFreeChosenRhs_eq_of_produces
    (G : RawLinearIndexedCFG N α P)
    (q : RawLinearUnitFreeRuleIndex G)
    {rhs : PreparedLinearRhs N α}
    (hproduce :
      RawLinearUnitFreeSlotProduces G q.1 rhs) :
    rawLinearUnitFreeChosenRhs G q = rhs :=
  rawLinearUnitFreeSlotProduces_functional
    G
    (rawLinearUnitFreeChosenRhs_spec G q)
    hproduce

/-- Finite prepared grammar after epsilon and unit elimination. -/
noncomputable def rawLinearUnitFreePreparedCFG
    (G : RawLinearIndexedCFG N α P) :
    PreparedLinearIndexedCFG
      N α (RawLinearUnitFreeRuleIndex G) where
  lhs q :=
    rawLinearUnitFreeRuleSlotLhs q.1
  rhs q :=
    rawLinearUnitFreeChosenRhs G q

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
      (rawLinearUnitFreePreparedCFG G) A word := by
  induction d with
  | terminals A p head tail hreach hrhs =>
      let slot : RawLinearUnitFreeRuleSlot N P :=
        Sum.inl (A, p)
      have hproduce :
          RawLinearUnitFreeSlotProduces G slot
            (PreparedLinearRhs.terminals head tail) :=
        RawLinearUnitFreeSlotProduces.keep
          A p _ hreach hrhs
      let q : RawLinearUnitFreeRuleIndex G :=
        ⟨slot, ⟨_, hproduce⟩⟩
      have hrhsChosen :
          (rawLinearUnitFreePreparedCFG G).rhs q =
            PreparedLinearRhs.terminals head tail := by
        exact
          rawLinearUnitFreeChosenRhs_eq_of_produces
            G q hproduce
      exact
        PreparedLinearDerives.terminals
          q head tail hrhsChosen
  | @around A p left core right hnonunit hreach hrhs word child ih =>
      let slot : RawLinearUnitFreeRuleSlot N P :=
        Sum.inl (A, p)
      have hproduce :
          RawLinearUnitFreeSlotProduces G slot
            (PreparedLinearRhs.around
              left core right hnonunit) :=
        RawLinearUnitFreeSlotProduces.keep
          A p _ hreach hrhs
      let q : RawLinearUnitFreeRuleIndex G :=
        ⟨slot, ⟨_, hproduce⟩⟩
      have hrhsChosen :
          (rawLinearUnitFreePreparedCFG G).rhs q =
            PreparedLinearRhs.around
              left core right hnonunit := by
        exact
          rawLinearUnitFreeChosenRhs_eq_of_produces
            G q hproduce
      exact
        PreparedLinearDerives.around
          q left core right hnonunit
          hrhsChosen ih
  | dropCore A p left core right hnonunit hreach hrhs hnullable =>
      let slot : RawLinearUnitFreeRuleSlot N P :=
        Sum.inr (A, p)
      let rhs :=
        preparedTerminalRhsOfNonempty
          (N := N)
          (left ++ right)
          (linearContext_append_ne_nil
            left right hnonunit)
      have hproduce :
          RawLinearUnitFreeSlotProduces G slot rhs :=
        RawLinearUnitFreeSlotProduces.drop
          A p left core right hnonunit
          hreach hrhs hnullable
      let q : RawLinearUnitFreeRuleIndex G :=
        ⟨slot, ⟨rhs, hproduce⟩⟩
      have hrhsChosen :
          (rawLinearUnitFreePreparedCFG G).rhs q = rhs := by
        exact
          rawLinearUnitFreeChosenRhs_eq_of_produces
            G q hproduce
      cases hword : left ++ right with
      | nil =>
          exact False.elim
            ((linearContext_append_ne_nil
              left right hnonunit) hword)
      | cons head tail =>
          have hrhsForm :
              rhs =
                PreparedLinearRhs.terminals
                  head tail := by
            simp [rhs, preparedTerminalRhsOfNonempty,
              hword]
          have hrhsFinal :
              (rawLinearUnitFreePreparedCFG G).rhs q =
                PreparedLinearRhs.terminals
                  head tail := by
            rw [hrhsChosen, hrhsForm]
          have dterm :=
            PreparedLinearDerives.terminals
              q head tail hrhsFinal
          simpa [hword] using dterm

/--
Every derivation of the finite prepared grammar expands to the semantic
unit-free derivation relation.
-/
theorem preparedDerives_to_rawLinearUnitFree
    (G : RawLinearIndexedCFG N α P)
    {A : N}
    {word : List α}
    (d :
      PreparedLinearDerives
        (rawLinearUnitFreePreparedCFG G) A word) :
    RawLinearUnitFreeDerives G A word := by
  induction d with
  | terminals q head tail hrhs =>
      have hspec :=
        rawLinearUnitFreeChosenRhs_spec G q
      change
        rawLinearUnitFreeChosenRhs G q =
          PreparedLinearRhs.terminals head tail at hrhs
      cases hspec with
      | keep A p rhs hreach hraw =>
          have hraw' :
              G.rhs p =
                RawLinearRhs.prepared
                  (PreparedLinearRhs.terminals
                    head tail) := by
            rw [hraw, hrhs]
          exact
            RawLinearUnitFreeDerives.terminals
              A p head tail hreach hraw'
      | drop A p left core right hnonunit hreach hraw hnullable =>
          have hreal :
              head :: tail = left ++ right := by
            have hsem :=
              (preparedTerminalRhsOfNonempty_realizes
                (N := N)
                (fun _ => Set.univ)
                (left ++ right)
                (linearContext_append_ne_nil
                  left right hnonunit)
                (head :: tail)).1
            apply hsem
            rw [hrhs]
            rfl
          have ddrop :=
            RawLinearUnitFreeDerives.dropCore
              A p left core right hnonunit
              hreach hraw hnullable
          simpa [hreal] using ddrop
  | @around q left core right hnonunit hrhs word child ih =>
      have hspec :=
        rawLinearUnitFreeChosenRhs_spec G q
      change
        rawLinearUnitFreeChosenRhs G q =
          PreparedLinearRhs.around
            left core right hnonunit at hrhs
      cases hspec with
      | keep A p rhs hreach hraw =>
          have hraw' :
              G.rhs p =
                RawLinearRhs.prepared
                  (PreparedLinearRhs.around
                    left core right hnonunit) := by
            rw [hraw, hrhs]
          exact
            RawLinearUnitFreeDerives.around
              A p left core right hnonunit
              hreach hraw' ih
      | drop A p left' core' right' hnonunit' hreach hraw hnullable =>
          have himpossible :
              preparedTerminalRhsOfNonempty
                  (N := N)
                  (left' ++ right')
                  (linearContext_append_ne_nil
                    left' right' hnonunit')
                =
              PreparedLinearRhs.around
                left core right hnonunit := by
            exact hrhs
          cases hword : left' ++ right' with
          | nil =>
              exact False.elim
                ((linearContext_append_ne_nil
                  left' right' hnonunit') hword)
          | cons head tail =>
              simp [preparedTerminalRhsOfNonempty,
                hword] at himpossible

/-- Exact derivation equivalence for the finite prepared presentation. -/
theorem rawLinearUnitFreeDerives_iff_prepared
    (G : RawLinearIndexedCFG N α P)
    (A : N)
    (word : List α) :
    RawLinearUnitFreeDerives G A word
      ↔
    PreparedLinearDerives
      (rawLinearUnitFreePreparedCFG G) A word := by
  constructor
  · exact rawLinearUnitFreeDerives_to_prepared G
  · exact preparedDerives_to_rawLinearUnitFree G

end LinearRawUnitFreePreparedBridge

end TCS1
end LeanCfgProject
