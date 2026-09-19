import LeanCfgProject.TCS1.MarkedBoundaryGapNormalization

/-!
# TCS #1 v68: expansion witnesses for marked-boundary reconstruction

A marked-boundary kernel contains marked terminal leaves and omitted sibling
subtrees.  Its `boundaryTemplate` replaces every omitted sibling by a
`none` placeholder.

This module makes the reconstruction step explicit.  A `BoundaryExpansion`
replaces the placeholders, from left to right, by a list of terminal words.
For every marked-boundary kernel, if every nonterminal has a terminal yield of
length at most tau, we construct:

* a genuine reconstructed derivation;
* the ordered list of replacement blocks;
* an expansion certificate against the kernel template;
* the exact number of blocks; and
* the uniform tau length bound.

The remaining positional lemma can therefore reason purely about the template
and its unique central gap.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section MarkedBoundaryExpansion

variable {N : Type u}
variable {α : Type v}

/-- Replace `none` placeholders by terminal blocks, preserving all `some`
terminals. -/
inductive BoundaryExpansion :
    List (Option α) → List (Word α) → Word α → Prop
  | nil :
      BoundaryExpansion [] [] []
  | some
      {a : α}
      {template : List (Option α)}
      {blocks : List (Word α)}
      {w : Word α}
      (tail :
        BoundaryExpansion template blocks w) :
      BoundaryExpansion
        (Option.some a :: template)
        blocks
        (a :: w)
  | none
      {template : List (Option α)}
      {blocks : List (Word α)}
      {w block : Word α}
      (tail :
        BoundaryExpansion template blocks w) :
      BoundaryExpansion
        (Option.none :: template)
        (block :: blocks)
        (block ++ w)

/-- Concatenate two independent template expansions. -/
theorem boundaryExpansion_append
    {t₁ t₂ : List (Option α)}
    {b₁ b₂ : List (Word α)}
    {w₁ w₂ : Word α}
    (e₁ : BoundaryExpansion t₁ b₁ w₁)
    (e₂ : BoundaryExpansion t₂ b₂ w₂) :
    BoundaryExpansion
      (t₁ ++ t₂) (b₁ ++ b₂) (w₁ ++ w₂) := by
  induction e₁ with
  | nil =>
      simpa using e₂
  | @some a template blocks w tail ih =>
      simpa using BoundaryExpansion.some ih
  | @none template blocks w block tail ih =>
      simpa only [List.append_assoc] using
        BoundaryExpansion.none (block := block) ih

/-- A single omitted placeholder expands to its chosen block. -/
theorem boundaryExpansion_single_none
    (block : Word α) :
    BoundaryExpansion [Option.none] [block] block := by
  simpa using
    (BoundaryExpansion.none
      (block := block)
      (BoundaryExpansion.nil :
        BoundaryExpansion ([] : List (Option α))
          ([] : List (Word α)) ([] : Word α)))

/--
Every marked-boundary kernel admits a tau-short block expansion whenever every
nonterminal has a tau-short terminal yield.
-/
theorem exists_rebuilt_short_expansion
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (τ : Nat)
    (hshort :
      ∀ X : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule X z
          ∧ z.length ≤ τ)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    ∃ blocks : List (Word α),
      ∃ w : Word α,
        BoundaryExpansion
          (MarkedBoundaryKernel.boundaryTemplate K)
          blocks w
        ∧
        UntypedDerives terminalRule binaryRule A w
        ∧
        blocks.length =
          MarkedBoundaryKernel.omittedCount K
        ∧
        (∀ block ∈ blocks, block.length ≤ τ) := by
  induction K with
  | marked a hterm =>
      refine
        ⟨[], [a], ?_,
          UntypedDerives.terminal hterm,
          by simp [MarkedBoundaryKernel.omittedCount],
          ?_⟩
      · exact
          BoundaryExpansion.some
            (BoundaryExpansion.nil :
              BoundaryExpansion ([] : List (Option α))
                ([] : List (Word α)) ([] : Word α))
      · intro block hmem
        simp at hmem

  | @unaryLeft A B C hbin child siblingWord sibling ih =>
      obtain ⟨blocks, w, hexpand, dChild,
          hcount, hlen⟩ := ih
      obtain ⟨z, dZ, hz⟩ := hshort C
      refine
        ⟨blocks ++ [z], w ++ z, ?_,
          UntypedDerives.binary hbin dChild dZ,
          ?_, ?_⟩
      · exact
          boundaryExpansion_append
            hexpand
            (boundaryExpansion_single_none z)
      · simp only [List.length_append,
          List.length_singleton,
          MarkedBoundaryKernel.omittedCount]
        rw [hcount]
      · intro block hmem
        simp only [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | hmem
        · exact hlen block hmem
        · subst block
          exact hz

  | @unaryRight A B C hbin siblingWord sibling child ih =>
      obtain ⟨blocks, w, hexpand, dChild,
          hcount, hlen⟩ := ih
      obtain ⟨y, dY, hy⟩ := hshort B
      refine
        ⟨y :: blocks, y ++ w, ?_,
          UntypedDerives.binary hbin dY dChild,
          ?_, ?_⟩
      · exact BoundaryExpansion.none hexpand
      · simp [MarkedBoundaryKernel.omittedCount, hcount]
      · intro block hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · subst block
          exact hy
        · exact hlen block hmem

  | branch hbin left right ihL ihR =>
      obtain ⟨blocksL, wL, hExpandL, dL,
          hCountL, hLenL⟩ := ihL
      obtain ⟨blocksR, wR, hExpandR, dR,
          hCountR, hLenR⟩ := ihR
      refine
        ⟨blocksL ++ blocksR, wL ++ wR, ?_,
          UntypedDerives.binary hbin dL dR,
          ?_, ?_⟩
      · exact
          boundaryExpansion_append
            hExpandL hExpandR
      · simp only [List.length_append,
          MarkedBoundaryKernel.omittedCount]
        rw [hCountL, hCountR]
      · intro block hmem
        simp only [List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · exact hLenL block hmem
        · exact hLenR block hmem

end MarkedBoundaryExpansion

end TCS1
end LeanCfgProject
