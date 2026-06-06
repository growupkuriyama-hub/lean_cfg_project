import LeanCfgProject.Step25_Test

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject.JALC

open TwoSidedTypedCFG

universe u v w

abbrev Language (Sigma : Type u) := Set (Word Sigma)

def ImageOfLanguage
    {Sigma : Type u} {Q : Type v}
    (q : Word Sigma → Q)
    (Y : Set (Word Sigma)) : Set Q :=
  { a | ∃ w : Word Sigma, w ∈ Y ∧ a = q w }

def LangMul
    {Sigma : Type u}
    (Y Z : Set (Word Sigma)) : Set (Word Sigma) :=
  { w | ∃ u : Word Sigma, u ∈ Y ∧
       ∃ v : Word Sigma, v ∈ Z ∧
       w = u ++ v }

def SetMul
    {Q : Type v} [Mul Q]
    (A B : Set Q) : Set Q :=
  { c | ∃ a : Q, a ∈ A ∧
       ∃ b : Q, b ∈ B ∧
       c = a * b }

def StateSemantics
    {Sigma : Type u} {Q : Type v} {State : Type w}
    (q : Word Sigma → Q)
    (Yield : State → Set (Word Sigma))
    (X : State) : Set Q :=
  ImageOfLanguage q (Yield X)

theorem image_langMul_eq_setMul
    {Sigma : Type u} {Q : Type v} [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (Y Z : Set (Word Sigma)) :
    ImageOfLanguage q (LangMul Y Z)
      =
    SetMul (ImageOfLanguage q Y) (ImageOfLanguage q Z) := by
  ext c
  constructor
  · intro hc
    rcases hc with ⟨w, hw, hc_eq⟩
    rcases hw with ⟨u, hu, v, hv, hw_eq⟩
    refine ⟨q u, ?_, q v, ?_, ?_⟩
    · exact ⟨u, hu, rfl⟩
    · exact ⟨v, hv, rfl⟩
    · rw [hc_eq, hw_eq, q_mul]
  · intro hc
    rcases hc with ⟨a, ha, b, hb, hc_eq⟩
    rcases ha with ⟨u, hu, ha_eq⟩
    rcases hb with ⟨v, hv, hb_eq⟩
    refine ⟨u ++ v, ?_, ?_⟩
    · exact ⟨u, hu, v, hv, rfl⟩
    · rw [hc_eq, ha_eq, hb_eq, ← q_mul]

theorem terminal_sound
    {Sigma : Type u} {Q : Type v} {State : Type w}
    (q : Word Sigma → Q)
    (Yield : State → Set (Word Sigma))
    (X : State)
    (a : Word Sigma)
    (ha : a ∈ Yield X) :
    q a ∈ StateSemantics q Yield X := by
  exact ⟨a, ha, rfl⟩

theorem binary_sound
    {Sigma : Type u} {Q : Type v} {State : Type w}
    [Monoid Q]
    (q : Word Sigma → Q)
    (q_mul : ∀ u v : Word Sigma, q (u ++ v) = q u * q v)
    (Yield : State → Set (Word Sigma))
    (X Y Z : State)
    (hbin : ∀ u v : Word Sigma,
      u ∈ Yield Y →
      v ∈ Yield Z →
      u ++ v ∈ Yield X) :
    SetMul (StateSemantics q Yield Y)
           (StateSemantics q Yield Z)
      ⊆
    StateSemantics q Yield X := by
  intro c hc
  rcases hc with ⟨a, ha, b, hb, hc_eq⟩
  rcases ha with ⟨u, hu, ha_eq⟩
  rcases hb with ⟨v, hv, hb_eq⟩
  refine ⟨u ++ v, hbin u v hu hv, ?_⟩
  rw [hc_eq, ha_eq, hb_eq, ← q_mul]

end LeanCfgProject.JALC