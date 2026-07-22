/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.OutputTypePresentationMonotone

/-!
# OutputTypePresentationCompleteness.lean

Fortieth clean Lean experiment for the fixed-observation MCFG project.

`OutputTypePresentationLanguage.lean` proved the soundness inclusion

```lean
PresentationStringLanguage P ⊆ G.StringLanguage
```

for every finite output-type presentation `P`.

This file packages the missing converse direction as an explicit completeness
interface:

```lean
PresentationCompleteFor P
```

meaning

```lean
G.StringLanguage ⊆ PresentationStringLanguage P.
```

From this interface we immediately obtain equality of the presentation language
with the original grammar language.  We also prove that completeness is
preserved when a presentation is extended.

This does not yet construct the complete presentation.  It isolates the exact
goal needed from the future `G^h` / `G̃₀` construction.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section PresentationCompleteness

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- Completeness of a finite output-type presentation for the original grammar.

Soundness is already automatic for every presentation; this record stores the
converse inclusion. -/
structure PresentationCompleteFor
    (P : OutputTypeRefinementPresentation G obs) : Prop where
  complete :
    G.StringLanguage ⊆ PresentationStringLanguage P

namespace PresentationCompleteFor

variable {P Q : OutputTypeRefinementPresentation G obs}

/-- Pointwise form of presentation completeness. -/
theorem mem_presentation
    (C : PresentationCompleteFor P)
    {word : Word α}
    (hword : word ∈ G.StringLanguage) :
    word ∈ PresentationStringLanguage P :=
  C.complete hword

/-- Soundness is available for every presentation. -/
theorem sound
    (C : PresentationCompleteFor P) :
    PresentationStringLanguage P ⊆ G.StringLanguage :=
  presentationStringLanguage_sound P

/-- A complete finite presentation generates exactly the original grammar
language. -/
theorem language_eq
    (C : PresentationCompleteFor P) :
    PresentationStringLanguage P = G.StringLanguage := by
  apply Set.Subset.antisymm
  · exact C.sound
  · exact C.complete

/-- Membership equivalence for a complete finite presentation. -/
theorem mem_iff
    (C : PresentationCompleteFor P)
    {word : Word α} :
    word ∈ PresentationStringLanguage P ↔ word ∈ G.StringLanguage := by
  constructor
  · intro hword
    exact C.sound hword
  · intro hword
    exact C.complete hword

/-- Completeness is preserved when the presentation is extended. -/
def extend
    (C : PresentationCompleteFor P)
    (hPQ : PresentationExtends P Q) :
    PresentationCompleteFor Q where
  complete := by
    intro word hword
    exact hPQ.mem_language (C.complete hword)

/-- Language equality after extending a complete presentation. -/
theorem language_eq_after_extension
    (C : PresentationCompleteFor P)
    (hPQ : PresentationExtends P Q) :
    PresentationStringLanguage Q = G.StringLanguage :=
  (C.extend hPQ).language_eq

/-- If two presentations extend each other, completeness transfers backward. -/
def of_mutual_extension
    (C : PresentationCompleteFor P)
    (hPQ : PresentationExtends P Q)
    (_hQP : PresentationExtends Q P) :
    PresentationCompleteFor Q :=
  C.extend hPQ

/-- Mutual extension preserves exact presentation language. -/
theorem language_eq_of_mutual_extension
    (C : PresentationCompleteFor P)
    (hPQ : PresentationExtends P Q)
    (hQP : PresentationExtends Q P) :
    PresentationStringLanguage Q = G.StringLanguage :=
  (C.of_mutual_extension hPQ hQP).language_eq

end PresentationCompleteFor

/-- Build completeness directly from the converse language inclusion. -/
def presentationCompleteFor_of_subset
    (P : OutputTypeRefinementPresentation G obs)
    (hcomplete : G.StringLanguage ⊆ PresentationStringLanguage P) :
    PresentationCompleteFor P where
  complete := hcomplete

/-- Equality form from a direct converse inclusion. -/
theorem presentationStringLanguage_eq_original_of_subset
    (P : OutputTypeRefinementPresentation G obs)
    (hcomplete : G.StringLanguage ⊆ PresentationStringLanguage P) :
    PresentationStringLanguage P = G.StringLanguage :=
  (presentationCompleteFor_of_subset P hcomplete).language_eq

/-- Converse inclusion extracted from language equality. -/
def presentationCompleteFor_of_language_eq
    (P : OutputTypeRefinementPresentation G obs)
    (heq : PresentationStringLanguage P = G.StringLanguage) :
    PresentationCompleteFor P where
  complete := by
    intro word hword
    rw [heq]
    exact hword

/-- A complete presentation gives both inclusions as a pair. -/
theorem presentation_language_inclusions
    (P : OutputTypeRefinementPresentation G obs)
    (C : PresentationCompleteFor P) :
    PresentationStringLanguage P ⊆ G.StringLanguage ∧
      G.StringLanguage ⊆ PresentationStringLanguage P :=
  ⟨presentationStringLanguage_sound P, C.complete⟩

/-- Exactness of a complete presentation, phrased as a top-level theorem. -/
theorem presentation_language_exact
    (P : OutputTypeRefinementPresentation G obs)
    (C : PresentationCompleteFor P) :
    PresentationStringLanguage P = G.StringLanguage :=
  C.language_eq

end PresentationCompleteness


section CompletePresentationData

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M}

/-- A finite output-type presentation together with its completeness proof.

This is a convenient package for future files representing `G^h` or a trimmed
presentation `G̃₀`. -/
structure CompleteOutputTypePresentation
    (G : WorkingMCFG N α) (obs : α → M) where
  presentation : OutputTypeRefinementPresentation G obs
  complete : PresentationCompleteFor presentation

namespace CompleteOutputTypePresentation

/-- The language generated by the stored finite presentation. -/
def language
    (C : CompleteOutputTypePresentation G obs) : Set (Word α) :=
  PresentationStringLanguage C.presentation

/-- The stored presentation is sound. -/
theorem sound
    (C : CompleteOutputTypePresentation G obs) :
    C.language ⊆ G.StringLanguage :=
  presentationStringLanguage_sound C.presentation

/-- The stored presentation is complete. -/
theorem complete_subset
    (C : CompleteOutputTypePresentation G obs) :
    G.StringLanguage ⊆ C.language :=
  C.complete.complete

/-- The stored presentation generates exactly the original grammar language. -/
theorem language_eq
    (C : CompleteOutputTypePresentation G obs) :
    C.language = G.StringLanguage :=
  C.complete.language_eq

/-- Membership equivalence for the stored complete presentation. -/
theorem mem_iff
    (C : CompleteOutputTypePresentation G obs)
    {word : Word α} :
    word ∈ C.language ↔ word ∈ G.StringLanguage :=
  C.complete.mem_iff

/-- Extend a complete presentation along a presentation extension. -/
def extend
    (C : CompleteOutputTypePresentation G obs)
    (Q : OutputTypeRefinementPresentation G obs)
    (hPQ : PresentationExtends C.presentation Q) :
    CompleteOutputTypePresentation G obs where
  presentation := Q
  complete := C.complete.extend hPQ

/-- The extended presentation still generates the original language exactly. -/
theorem extend_language_eq
    (C : CompleteOutputTypePresentation G obs)
    (Q : OutputTypeRefinementPresentation G obs)
    (hPQ : PresentationExtends C.presentation Q) :
    PresentationStringLanguage Q = G.StringLanguage :=
  (C.extend Q hPQ).language_eq

end CompleteOutputTypePresentation

end CompletePresentationData

end MCFG
