import LeanCfgProject.TCS1.YieldTypedRefinementCore
import LeanCfgProject.TCS1.FixedWindowTreeCombinatorics

/-!
# TCS #1 v68: fixed-window boundary-preservation semantic kernel

Lemma 7.1 of the v68 manuscript shortens a derivation tree while preserving
the first k and last l marked terminal leaves.  After the marked-path
shortcuts, omitted sibling subtrees are replaced by short terminal yields.
The resulting word therefore has the same fixed-window boundary summary and
the same h_{k,l}-type.

This module isolates the word-level semantic part of that argument.

* `concatBlocks` concatenates replacement sibling yields.
* `boundaryAssembly` inserts those blocks between a fixed prefix and suffix.
* `BoundaryTyping` abstracts the defining long-word property of h_{k,l}:
  once the boundary prefix/suffix are fixed, replacing the middle preserves
  type.
* the reconstructed word keeps that type;
* if it is still derivable from the same underlying nonterminal, the generic
  yield-typed lifting theorem lifts it to the prescribed typed symbol; and
* the actual reconstructed word length is bounded by the same
  r + (2r-1) N tau envelope as the manuscript.

The remaining grammar-tree obligation is therefore sharply separated:
construct a derivable `boundaryAssembly` after marked-path shortcutting and
sibling replacement.  No boundary/type or length arithmetic remains hidden in
that step.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section FixedWindowBoundarySemantic

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- Concatenate a list of terminal blocks. -/
def concatBlocks : List (Word α) → Word α
  | [] => []
  | b :: bs => b ++ concatBlocks bs

@[simp] theorem concatBlocks_nil :
    concatBlocks ([] : List (Word α)) = [] := rfl

@[simp] theorem concatBlocks_cons
    (b : Word α)
    (bs : List (Word α)) :
    concatBlocks (b :: bs) = b ++ concatBlocks bs := rfl

/-- Length of the concatenated replacement blocks. -/
theorem concatBlocks_length
    (blocks : List (Word α)) :
    (concatBlocks blocks).length =
      (blocks.map (fun b => b.length)).sum := by
  induction blocks with
  | nil =>
      simp [concatBlocks]
  | cons b bs ih =>
      simp [concatBlocks, ih]

/-- Assemble a word with fixed left/right boundary and replaceable middle blocks. -/
def boundaryAssembly
    (p q : Word α)
    (blocks : List (Word α)) : Word α :=
  p ++ concatBlocks blocks ++ q

/-- Exact length of a boundary-preserving assembly. -/
theorem boundaryAssembly_length
    (p q : Word α)
    (blocks : List (Word α)) :
    (boundaryAssembly p q blocks).length =
      p.length +
        (blocks.map (fun b => b.length)).sum +
        q.length := by
  simp [boundaryAssembly, concatBlocks_length, Nat.add_assoc]

/--
Abstract long-word fixed-window property.

For the concrete h_{k,l}, this is exactly the statement that two long words
with the same length-k prefix and length-l suffix have the same type.
We formulate it using an explicit decomposition p ++ middle ++ q, which is the
shape produced by the marked-boundary derivation surgery.
-/
def BoundaryTyping
    (H : FixedFiniteMonoidHom α M)
    (k l : Nat) : Prop :=
  ∀ (p q : Word α),
    p.length = k →
    q.length = l →
    ∀ m₁ m₂ : Word α,
      H.h (p ++ m₁ ++ q) =
        H.h (p ++ m₂ ++ q)

/-- Replacing the middle blocks preserves the fixed boundary type. -/
theorem boundaryAssembly_type_eq
    (H : FixedFiniteMonoidHom α M)
    {k l : Nat}
    (hBoundary : BoundaryTyping H k l)
    (p q : Word α)
    (hp : p.length = k)
    (hq : q.length = l)
    (blocks₁ blocks₂ : List (Word α)) :
    H.h (boundaryAssembly p q blocks₁) =
      H.h (boundaryAssembly p q blocks₂) := by
  exact
    hBoundary p q hp hq
      (concatBlocks blocks₁)
      (concatBlocks blocks₂)

/--
Paper-facing form: if a reference word p ++ middle ++ q has type mu, then
every boundary-preserving assembly has type mu.
-/
theorem boundaryAssembly_has_reference_type
    (H : FixedFiniteMonoidHom α M)
    {k l : Nat}
    (hBoundary : BoundaryTyping H k l)
    (p q middle : Word α)
    (blocks : List (Word α))
    (hp : p.length = k)
    (hq : q.length = l)
    {μ : M}
    (href : H.h (p ++ middle ++ q) = μ) :
    H.h (boundaryAssembly p q blocks) = μ := by
  have hsame :
      H.h (boundaryAssembly p q blocks) =
        H.h (boundaryAssembly p q [middle]) := by
    exact
      boundaryAssembly_type_eq
        H hBoundary p q hp hq blocks [middle]
  have hsingle :
      boundaryAssembly p q [middle] =
        p ++ middle ++ q := by
    simp [boundaryAssembly, concatBlocks, Nat.add_assoc]
  rw [hsingle] at hsame
  exact hsame.trans href

/--
Typed lifting after the boundary-preserving tree surgery.

Once the transformed word is still an untyped derivation from A and its
boundary gives the prescribed type mu, Proposition 5.2's generic lifting
theorem produces a derivation from the typed symbol (A,mu).
-/
theorem boundaryAssembly_typed_lift
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {k l : Nat}
    (hBoundary : BoundaryTyping H k l)
    (p q middle : Word α)
    (blocks : List (Word α))
    (hp : p.length = k)
    (hq : q.length = l)
    {A : N}
    {μ : M}
    (href : H.h (p ++ middle ++ q) = μ)
    (d :
      UntypedDerives terminalRule binaryRule A
        (boundaryAssembly p q blocks)) :
    TypedDerives H terminalRule binaryRule
      (A, μ) (boundaryAssembly p q blocks) := by
  have htype :
      H.h (boundaryAssembly p q blocks) = μ :=
    boundaryAssembly_has_reference_type
      H hBoundary p q middle blocks hp hq href
  have hd :
      TypedDerives H terminalRule binaryRule
        (A, H.h (boundaryAssembly p q blocks))
        (boundaryAssembly p q blocks) :=
    untypedDerives_lift
      H terminalRule binaryRule d
  simpa [htype] using hd

/-- Sum of actual replacement-block lengths under a uniform block bound. -/
theorem concatBlocks_length_le
    (blocks : List (Word α))
    (V τ : Nat)
    (hcount : blocks.length ≤ V)
    (heach : ∀ b ∈ blocks, b.length ≤ τ) :
    (concatBlocks blocks).length ≤ V * τ := by
  rw [concatBlocks_length]
  apply
    chainExpansion_sum_le
      (blocks.map (fun b => b.length))
      V τ
  · simpa using hcount
  · intro c hc
    rcases List.mem_map.mp hc with ⟨b, hb, rfl⟩
    exact heach b hb

/--
Semantic length version of the long-state estimate.

The prefix and suffix together account for exactly r marked boundary
terminals.  There are at most `retained` replacement blocks, and the marked
tree combinatorics bounds `retained` by (2r-1)N.  If every replacement block
has length at most tau, the assembled word satisfies the v68 Lemma 7.1 bound.
-/
theorem boundaryAssembly_fixedWindow_length_le
    (p q : Word α)
    (blocks : List (Word α))
    (r N τ retained : Nat)
    (hboundary : p.length + q.length = r)
    (hcount : blocks.length ≤ retained)
    (hretained : retained ≤ (2 * r - 1) * N)
    (heach : ∀ b ∈ blocks, b.length ≤ τ) :
    (boundaryAssembly p q blocks).length ≤
      r + (2 * r - 1) * N * τ := by
  have hmiddle :
      (concatBlocks blocks).length ≤ retained * τ :=
    concatBlocks_length_le
      blocks retained τ hcount heach
  have hretMul :
      retained * τ ≤ ((2 * r - 1) * N) * τ :=
    Nat.mul_le_mul_right τ hretained
  have hmiddle' :
      (concatBlocks blocks).length ≤
        ((2 * r - 1) * N) * τ :=
    le_trans hmiddle hretMul
  have hlen :
      (boundaryAssembly p q blocks).length =
        p.length + (concatBlocks blocks).length + q.length := by
    simp [boundaryAssembly, Nat.add_assoc]
  rw [hlen]
  calc
    p.length + (concatBlocks blocks).length + q.length
        =
      (p.length + q.length) +
        (concatBlocks blocks).length := by
          ring
    _ = r + (concatBlocks blocks).length := by
          rw [hboundary]
    _ ≤ r + ((2 * r - 1) * N) * τ :=
          Nat.add_le_add_left hmiddle' r

/--
The exact manuscript endpoint with r=k+l.
-/
theorem boundaryAssembly_fixedWindow_kl_length_le
    (p q : Word α)
    (blocks : List (Word α))
    (k l N τ retained : Nat)
    (hp : p.length = k)
    (hq : q.length = l)
    (hcount : blocks.length ≤ retained)
    (hretained : retained ≤ (2 * (k + l) - 1) * N)
    (heach : ∀ b ∈ blocks, b.length ≤ τ) :
    (boundaryAssembly p q blocks).length ≤
      (k + l) + (2 * (k + l) - 1) * N * τ := by
  apply
    boundaryAssembly_fixedWindow_length_le
      p q blocks (k + l) N τ retained
  · omega
  · exact hcount
  · exact hretained
  · exact heach

end FixedWindowBoundarySemantic

end TCS1
end LeanCfgProject
