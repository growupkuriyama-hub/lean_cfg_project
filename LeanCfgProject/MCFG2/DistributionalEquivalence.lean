/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG2.OutputTypeLift

/-!
# DistributionalEquivalence.lean

Fifth clean Lean experiment for the fixed-observation MCFG project.

This file isolates the semantic equivalence relation used in the learner
soundness argument.  It corresponds to the paper's fixed-`h` distributional
equivalence and the "shared-context substitutability" lemma.

The main point is simple:

If a language is `(f,h)`-tuple-substitutable, then two arity-`d` tuples with
the same componentwise observation type and one shared accepting context have
the same full distribution of accepting contexts.

No theorem here uses `sorry`.
-/

namespace MCFG

universe u v w

section AbstractDistributionalEquivalence

variable {α : Type u} {M : Type v} [Monoid M]
variable {Ctx : Nat → Type w}

variable (fill : ∀ d : Nat, Ctx d → Tuple α d → Word α)

/-- Fixed-observation distributional equivalence of two tuples.

This is the Lean version of the paper notation
`u ≡_L^d x`: same componentwise observation type and the same accepting-context
distribution. -/
def FixedDistributionalEquivalent
    {d : Nat} (obs : α → M) (L : Set (Word α))
    (x y : Tuple α d) : Prop :=
  tupleType obs x = tupleType obs y ∧
  Distribution fill L x = Distribution fill L y

namespace FixedDistributionalEquivalent

variable {fill}
variable {obs : α → M} {L : Set (Word α)}

/-- Reflexivity. -/
theorem refl {d : Nat} (x : Tuple α d) :
    FixedDistributionalEquivalent fill obs L x x := by
  exact ⟨rfl, rfl⟩

/-- Symmetry. -/
theorem symm {d : Nat} {x y : Tuple α d}
    (h : FixedDistributionalEquivalent fill obs L x y) :
    FixedDistributionalEquivalent fill obs L y x := by
  exact ⟨h.1.symm, h.2.symm⟩

/-- Transitivity. -/
theorem trans {d : Nat} {x y z : Tuple α d}
    (hxy : FixedDistributionalEquivalent fill obs L x y)
    (hyz : FixedDistributionalEquivalent fill obs L y z) :
    FixedDistributionalEquivalent fill obs L x z := by
  exact ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

/-- Extract equality of componentwise observation types. -/
theorem tupleType_eq {d : Nat} {x y : Tuple α d}
    (h : FixedDistributionalEquivalent fill obs L x y) :
    tupleType obs x = tupleType obs y :=
  h.1

/-- Extract equality of accepting-context distributions. -/
theorem distribution_eq {d : Nat} {x y : Tuple α d}
    (h : FixedDistributionalEquivalent fill obs L x y) :
    Distribution fill L x = Distribution fill L y :=
  h.2

/-- Equivalent tuples are accepted by exactly the same contexts. -/
theorem fill_mem_iff {d : Nat} {x y : Tuple α d}
    (h : FixedDistributionalEquivalent fill obs L x y)
    (c : Ctx d) :
    fill d c x ∈ L ↔ fill d c y ∈ L := by
  change c ∈ Distribution fill L x ↔ c ∈ Distribution fill L y
  rw [h.distribution_eq]

/-- Transport acceptance of one context from left to right. -/
theorem fill_mem_right {d : Nat} {x y : Tuple α d}
    (h : FixedDistributionalEquivalent fill obs L x y)
    {c : Ctx d}
    (hc : fill d c x ∈ L) :
    fill d c y ∈ L :=
  (h.fill_mem_iff c).1 hc

/-- Transport acceptance of one context from right to left. -/
theorem fill_mem_left {d : Nat} {x y : Tuple α d}
    (h : FixedDistributionalEquivalent fill obs L x y)
    {c : Ctx d}
    (hc : fill d c y ∈ L) :
    fill d c x ∈ L :=
  (h.fill_mem_iff c).2 hc

end FixedDistributionalEquivalent

/-- Shared-context substitutability.

This is the key semantic bridge: under the `(f,h)` promise, same observation
type plus one shared accepting context implies full distributional equivalence. -/
theorem fixedDistributionalEquivalent_of_sharedContext
    {f d : Nat} {obs : α → M} {L : Set (Word α)}
    (hL : FixedTupleSubstitutable fill f obs L)
    (hd : d ≤ f)
    (hpos : 0 < d)
    {x y : Tuple α d}
    (htype : tupleType obs x = tupleType obs y)
    (hshare : SharesContext fill L x y) :
    FixedDistributionalEquivalent fill obs L x y := by
  exact ⟨htype, hL hd hpos x y htype hshare⟩

/-- A version with the shared context written out explicitly. -/
theorem fixedDistributionalEquivalent_of_common_context
    {f d : Nat} {obs : α → M} {L : Set (Word α)}
    (hL : FixedTupleSubstitutable fill f obs L)
    (hd : d ≤ f)
    (hpos : 0 < d)
    {x y : Tuple α d}
    (htype : tupleType obs x = tupleType obs y)
    {c : Ctx d}
    (hcx : fill d c x ∈ L)
    (hcy : fill d c y ∈ L) :
    FixedDistributionalEquivalent fill obs L x y := by
  exact fixedDistributionalEquivalent_of_sharedContext
    (fill := fill) hL hd hpos htype ⟨c, hcx, hcy⟩

end AbstractDistributionalEquivalence


section NamedDistributionalEquivalence

variable {α : Type u} {M : Type v} [Monoid M]

/-- Named-context specialization of fixed distributional equivalence. -/
abbrev FixedNamedDistributionalEquivalent
    {d : Nat} (obs : α → M) (L : Set (Word α))
    (x y : Tuple α d) : Prop :=
  FixedDistributionalEquivalent namedFill obs L x y

namespace FixedNamedDistributionalEquivalent

variable {obs : α → M} {L : Set (Word α)}

/-- Named-context equivalence transports acceptance of named sentence contexts. -/
theorem namedFill_mem_iff {d : Nat} {x y : Tuple α d}
    (h : FixedNamedDistributionalEquivalent obs L x y)
    (c : NamedSentenceContext α d) :
    namedFill d c x ∈ L ↔ namedFill d c y ∈ L :=
  FixedDistributionalEquivalent.fill_mem_iff (fill := namedFill) h c

/-- Named-context equivalence transports acceptance from left to right. -/
theorem namedFill_mem_right {d : Nat} {x y : Tuple α d}
    (h : FixedNamedDistributionalEquivalent obs L x y)
    {c : NamedSentenceContext α d}
    (hc : namedFill d c x ∈ L) :
    namedFill d c y ∈ L :=
  (h.namedFill_mem_iff c).1 hc

/-- Named-context equivalence transports acceptance from right to left. -/
theorem namedFill_mem_left {d : Nat} {x y : Tuple α d}
    (h : FixedNamedDistributionalEquivalent obs L x y)
    {c : NamedSentenceContext α d}
    (hc : namedFill d c y ∈ L) :
    namedFill d c x ∈ L :=
  (h.namedFill_mem_iff c).2 hc

end FixedNamedDistributionalEquivalent

/-- Named-context version of shared-context substitutability. -/
theorem fixedNamedDistributionalEquivalent_of_sharedContext
    {f d : Nat} {obs : α → M} {L : Set (Word α)}
    (hL : FixedNamedTupleSubstitutable f obs L)
    (hd : d ≤ f)
    (hpos : 0 < d)
    {x y : Tuple α d}
    (htype : tupleType obs x = tupleType obs y)
    (hshare : NamedSharesContext L x y) :
    FixedNamedDistributionalEquivalent obs L x y := by
  exact fixedDistributionalEquivalent_of_sharedContext
    (fill := namedFill) hL hd hpos htype hshare

/-- Named-context version with the shared context written explicitly. -/
theorem fixedNamedDistributionalEquivalent_of_common_context
    {f d : Nat} {obs : α → M} {L : Set (Word α)}
    (hL : FixedNamedTupleSubstitutable f obs L)
    (hd : d ≤ f)
    (hpos : 0 < d)
    {x y : Tuple α d}
    (htype : tupleType obs x = tupleType obs y)
    {c : NamedSentenceContext α d}
    (hcx : namedFill d c x ∈ L)
    (hcy : namedFill d c y ∈ L) :
    FixedNamedDistributionalEquivalent obs L x y := by
  exact fixedDistributionalEquivalent_of_common_context
    (fill := namedFill) hL hd hpos htype hcx hcy

end NamedDistributionalEquivalence


section GrammarDistributionalEquivalence

variable {N : Type v} {α : Type u} {M : Type w} [Monoid M]

/-- Grammar-level named distributional equivalence. -/
abbrev GrammarNamedDistributionalEquivalent
    (G : WorkingMCFG N α) {d : Nat} (obs : α → M)
    (x y : Tuple α d) : Prop :=
  FixedNamedDistributionalEquivalent obs G.StringLanguage x y

/-- Under the fixed-observation promise for the grammar language, a shared
grammar context gives grammar-level distributional equivalence. -/
theorem grammarNamedDistributionalEquivalent_of_sharedContext
    (G : WorkingMCFG N α)
    {f d : Nat} {obs : α → M}
    (hd : d ≤ f)
    (hpos : 0 < d)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {x y : Tuple α d}
    (htype : tupleType obs x = tupleType obs y)
    (hshare : GrammarNamedSharesContext G x y) :
    GrammarNamedDistributionalEquivalent G obs x y := by
  exact fixedNamedDistributionalEquivalent_of_sharedContext
    hL hd hpos htype hshare

/-- A grammar-level common named context gives distributional equivalence under
the fixed-observation promise. -/
theorem grammarNamedDistributionalEquivalent_of_common_context
    (G : WorkingMCFG N α)
    {f d : Nat} {obs : α → M}
    (hd : d ≤ f)
    (hpos : 0 < d)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {x y : Tuple α d}
    (htype : tupleType obs x = tupleType obs y)
    {c : NamedSentenceContext α d}
    (hcx : namedFill d c x ∈ G.StringLanguage)
    (hcy : namedFill d c y ∈ G.StringLanguage) :
    GrammarNamedDistributionalEquivalent G obs x y := by
  exact fixedNamedDistributionalEquivalent_of_common_context
    hL hd hpos htype hcx hcy

/-- Exposed tuples at the same named context are distributionally equivalent
whenever their output types agree and the grammar language satisfies the promise. -/
theorem grammarNamedDistributionalEquivalent_of_two_exposures
    (G : WorkingMCFG N α) (A : N)
    {f : Nat} {obs : α → M}
    (hfan : G.FanoutAtMost f)
    (hL : FixedNamedTupleSubstitutable f obs G.StringLanguage)
    {x y : Tuple α (G.arity A)}
    {c : NamedSentenceContext α (G.arity A)}
    (htype : tupleType obs x = tupleType obs y)
    (hx : ExposedWithContext G A x c)
    (hy : ExposedWithContext G A y c) :
    GrammarNamedDistributionalEquivalent G obs x y := by
  exact grammarNamedDistributionalEquivalent_of_common_context
    G (hfan A) (G.arity_pos A) hL htype hx.2 hy.2

end GrammarDistributionalEquivalence

end MCFG
