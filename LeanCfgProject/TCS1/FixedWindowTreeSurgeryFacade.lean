import LeanCfgProject.TCS1.FixedWindowBoundaryMarking
import LeanCfgProject.TCS1.MarkedBoundaryNormalization
import LeanCfgProject.TCS1.MarkedBoundaryGapNormalization

/-!
# TCS #1 v68: fixed-window tree-surgery facade

This module composes the three mechanical pieces of the long-word branch of
Lemma 7.1:

1. select the first k and last l terminal leaves;
2. cycle-shorten every maximal one-child chain;
3. replace omitted sibling subtrees by tau-short terminal yields.

The resulting theorem already gives the exact manuscript length envelope and a
genuine untyped derivation from the original nonterminal.

The only semantic fact intentionally left out of this facade is preservation
of the central fixed-window gap through cycle shortening.  Once that invariant
is transported from the ranked boundary kernel to the shortened kernel, the
existing FixedWindowBoundarySemantic layer lifts the derivation to the same
h_{k,l}-typed symbol.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FixedWindowTreeSurgeryFacade

variable {N : Type u}
variable {α : Type v}

/--
Boundary selection followed by cycle shortening gives a kernel with exactly
k+l marked leaves and at most (2(k+l)-1)|N| omitted sibling subtrees.
-/
theorem exists_fixedWindow_cycle_shortened_kernel
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α}
    (d : UntypedDerives terminalRule binaryRule A w)
    (k l : Nat)
    (hr : 0 < k + l)
    (hfit : k + l ≤ w.length) :
    ∃ K' : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedWord K' =
        w.take k ++ w.drop (w.length - l)
      ∧
      MarkedBoundaryKernel.markedLeafCount K' = k + l
      ∧
      MarkedBoundaryKernel.omittedCount K' ≤
        (2 * (k + l) - 1) * Fintype.card N := by
  obtain ⟨K, hYield, hWord, hCount⟩ :=
    exists_fixedWindow_boundary_kernel
      terminalRule binaryRule d k l hr hfit
  obtain ⟨K', hCount', hWord', hOmit⟩ :=
    exists_cycle_shortened_kernel
      terminalRule binaryRule K
  refine ⟨K', ?_, ?_, ?_⟩
  · rw [hWord', hWord]
  · rw [hCount', hCount]
  · rw [hCount] at hOmit
    exact hOmit

/--
Boundary selection followed by gap-preserving cycle shortening.

In addition to the numerical bound, every omitted sibling remains in the
single central gap after the first k marked leaves.
-/
theorem exists_fixedWindow_cycle_shortened_kernel_ranked
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α}
    (d : UntypedDerives terminalRule binaryRule A w)
    (k l : Nat)
    (hr : 0 < k + l)
    (hfit : k + l ≤ w.length) :
    ∃ K' : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedWord K' =
        w.take k ++ w.drop (w.length - l)
      ∧
      MarkedBoundaryKernel.markedLeafCount K' = k + l
      ∧
      MarkedBoundaryKernel.omittedCount K' ≤
        (2 * (k + l) - 1) * Fintype.card N
      ∧
      MarkedBoundaryKernel.AllOmissionsAt K' k := by
  obtain ⟨K, hYield, hWord, hCount, hGap⟩ :=
    exists_fixedWindow_boundary_kernel_ranked
      terminalRule binaryRule d k l hr hfit
  obtain ⟨K', hCount', hWord', hOmit, hGap'⟩ :=
    exists_cycle_shortened_kernel_preserving_allOmissionsAt
      terminalRule binaryRule K k hGap
  refine ⟨K', ?_, ?_, ?_, hGap'⟩
  · rw [hWord', hWord]
  · rw [hCount', hCount]
  · rw [hCount] at hOmit
    exact hOmit

/--
Untyped long-word reconstruction with the exact Lemma 7.1 numerical bound.

This closes the combinatorial/derivational part of the long case.  The
remaining fixed-window obligation is solely that the shortened reconstruction
still places every replacement between the preserved prefix and suffix.
-/
theorem exists_fixedWindow_shortened_reconstruction
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α}
    (d : UntypedDerives terminalRule binaryRule A w)
    (k l : Nat)
    (hr : 0 < k + l)
    (hfit : k + l ≤ w.length)
    (τ : Nat)
    (hshort :
      ∀ X : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule X z
          ∧ z.length ≤ τ) :
    ∃ w' : Word α,
      UntypedDerives terminalRule binaryRule A w'
      ∧
      w'.length ≤
        (k + l) +
          (2 * (k + l) - 1) * Fintype.card N * τ := by
  obtain ⟨K', hWord, hCount, hOmit⟩ :=
    exists_fixedWindow_cycle_shortened_kernel
      terminalRule binaryRule d k l hr hfit
  obtain ⟨w', d', hlen⟩ :=
    MarkedBoundaryKernel.exists_rebuilt_short_yield
      terminalRule binaryRule τ hshort K'
  have hmul :
      MarkedBoundaryKernel.omittedCount K' * τ ≤
        ((2 * (k + l) - 1) * Fintype.card N) * τ :=
    Nat.mul_le_mul_right τ hOmit
  rw [hCount] at hlen
  refine ⟨w', d', ?_⟩
  exact le_trans hlen
    (Nat.add_le_add_left hmul (k + l))

end FixedWindowTreeSurgeryFacade

end TCS1
end LeanCfgProject
