/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.OutputTypePresentationLanguage

/-!
# OutputTypePresentationMonotone.lean

Thirty-ninth clean Lean experiment for the fixed-observation MCFG project.

`OutputTypePresentationLanguage.lean` attached a string language to a finite
typed presentation and proved soundness with respect to the original grammar.

This file adds monotonicity for finite typed presentations.

If a presentation `Q` contains all typed nonterminals and typed rules of a
presentation `P`, then every `P`-derivation is also a `Q`-derivation, and
therefore

```lean
PresentationStringLanguage P ⊆ PresentationStringLanguage Q
```

This is useful for trimmed-output-refinement arguments: once a core finite
presentation is known to work, adding harmless reachable or saturated typed
rules cannot destroy the generated language.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PresentationExtension

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Inclusion of finite output-type presentations.

`PresentationExtends P Q` means that `Q` contains every typed nonterminal and
typed rule of `P`. -/
structure PresentationExtends
    (P Q : OutputTypeRefinementPresentation G obs) where
  nonterminal_subset :
    ∀ {X : TypedNonterminal G M},
      P.HasNonterminal X → Q.HasNonterminal X
  terminal_subset :
    ∀ {τ : TypedTerminalRule G},
      P.HasTerminalRule τ → Q.HasTerminalRule τ
  binary_subset :
    ∀ {τ : TypedBinaryRule G M},
      P.HasBinaryRule τ → Q.HasBinaryRule τ
  start_subset :
    ∀ {σ : TypedStartRule G M},
      P.HasStartRule σ → Q.HasStartRule σ

namespace PresentationExtends

variable {P Q R : OutputTypeRefinementPresentation G obs}

/-- Reflexivity of presentation extension. -/
def refl
    (P : OutputTypeRefinementPresentation G obs) :
    PresentationExtends P P where
  nonterminal_subset := by
    intro X hX
    exact hX
  terminal_subset := by
    intro τ hτ
    exact hτ
  binary_subset := by
    intro τ hτ
    exact hτ
  start_subset := by
    intro σ hσ
    exact hσ

/-- Transitivity of presentation extension. -/
def trans
    (hPQ : PresentationExtends P Q)
    (hQR : PresentationExtends Q R) :
    PresentationExtends P R where
  nonterminal_subset := by
    intro X hX
    exact hQR.nonterminal_subset (hPQ.nonterminal_subset hX)
  terminal_subset := by
    intro τ hτ
    exact hQR.terminal_subset (hPQ.terminal_subset hτ)
  binary_subset := by
    intro τ hτ
    exact hQR.binary_subset (hPQ.binary_subset hτ)
  start_subset := by
    intro σ hσ
    exact hQR.start_subset (hPQ.start_subset hσ)

/-- A present nonterminal remains present under extension. -/
theorem hasNonterminal
    (hPQ : PresentationExtends P Q)
    {X : TypedNonterminal G M}
    (hX : P.HasNonterminal X) :
    Q.HasNonterminal X :=
  hPQ.nonterminal_subset hX

/-- A present terminal rule remains present under extension. -/
theorem hasTerminalRule
    (hPQ : PresentationExtends P Q)
    {τ : TypedTerminalRule G}
    (hτ : P.HasTerminalRule τ) :
    Q.HasTerminalRule τ :=
  hPQ.terminal_subset hτ

/-- A present binary rule remains present under extension. -/
theorem hasBinaryRule
    (hPQ : PresentationExtends P Q)
    {τ : TypedBinaryRule G M}
    (hτ : P.HasBinaryRule τ) :
    Q.HasBinaryRule τ :=
  hPQ.binary_subset hτ

/-- A present start rule remains present under extension. -/
theorem hasStartRule
    (hPQ : PresentationExtends P Q)
    {σ : TypedStartRule G M}
    (hσ : P.HasStartRule σ) :
    Q.HasStartRule σ :=
  hPQ.start_subset hσ

/-- Typed presentation derivations are monotone under presentation extension. -/
theorem derives
    (hPQ : PresentationExtends P Q)
    {X : TypedNonterminal G M}
    {x : Tuple α (G.arity X.base)}
    (h : PresentationDerives P X x) :
    PresentationDerives Q X x := by
  induction h with
  | terminal hτ =>
      exact PresentationDerives.terminal
        (hPQ.hasTerminalRule hτ)
  | binary hτ hx hy ihx ihy =>
      exact PresentationDerives.binary
        (hPQ.hasBinaryRule hτ) ihx ihy

/-- String derivations are monotone under presentation extension. -/
def stringDerives
    (hPQ : PresentationExtends P Q)
    {word : Word α}
    (D : PresentationStringDerives P word) :
    PresentationStringDerives Q word where
  startRule := D.startRule
  start_mem := hPQ.hasStartRule D.start_mem
  childTuple := D.childTuple
  child_derives := hPQ.derives D.child_derives
  start_arity := D.start_arity
  word_eq := D.word_eq

/-- Presentation string languages are monotone under presentation extension. -/
theorem language_subset
    (hPQ : PresentationExtends P Q) :
    PresentationStringLanguage P ⊆ PresentationStringLanguage Q := by
  intro word hword
  rcases hword with ⟨D⟩
  exact ⟨hPQ.stringDerives D⟩

/-- Pointwise membership transport for presentation string languages. -/
theorem mem_language
    (hPQ : PresentationExtends P Q)
    {word : Word α}
    (hword : word ∈ PresentationStringLanguage P) :
    word ∈ PresentationStringLanguage Q :=
  hPQ.language_subset hword

/-- If two presentations extend each other, then they generate the same string
language. -/
theorem language_eq_of_mutual
    (hPQ : PresentationExtends P Q)
    (hQP : PresentationExtends Q P) :
    PresentationStringLanguage P = PresentationStringLanguage Q := by
  apply Set.Subset.antisymm
  · exact hPQ.language_subset
  · exact hQP.language_subset

/-- Soundness is preserved after extending the presentation. -/
theorem sound_after_extension
    (hPQ : PresentationExtends P Q)
    (hQsound : PresentationStringLanguage Q ⊆ G.StringLanguage) :
    PresentationStringLanguage P ⊆ G.StringLanguage := by
  intro word hword
  exact hQsound (hPQ.mem_language hword)

end PresentationExtends

end PresentationExtension

end MCFG
