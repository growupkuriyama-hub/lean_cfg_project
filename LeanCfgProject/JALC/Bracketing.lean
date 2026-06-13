import Mathlib

namespace LeanCfgProject
namespace JALC
namespace Bracketing

/-
Arithmetic check for the bracketing non-rigidity witness.

The paper compares two reduced SSBNF presentations of the same one-word
language {abc}:

  G1: a(bc)
  G2: (ab)c

over M = ZMod 2, written additively, with h(a)=h(b)=h(c)=1.

This file checks the type-triple calculations used in the non-rigidity
proposition.  It does not formalize the whole extraction theorem; it checks
the finite arithmetic kernel of the witness.
-/


/-- Type triples `(yield, left frame, right frame)` over `ZMod 2`. -/
abbrev Tri := ZMod 2 × ZMod 2 × ZMod 2


/-- Left child of a binary rule in additive notation over `ZMod 2`.

For a parent frame `(m,n)` and child yield types `q,r`, the left child has
type triple `(q, m, r+n)`.
-/
def leftChildTri (m n q r : ZMod 2) : Tri :=
  (q, m, r + n)


/-- Right child of a binary rule in additive notation over `ZMod 2`.

For a parent frame `(m,n)` and child yield types `q,r`, the right child has
type triple `(r, m+q, n)`.
-/
def rightChildTri (m n q r : ZMod 2) : Tri :=
  (r, m + q, n)


/-
Local checks for the hand calculations in the paper.
-/

example : leftChildTri 0 0 1 0 = (1, 0, 0) := by
  decide

example : rightChildTri 0 0 1 0 = (0, 1, 0) := by
  decide

example : leftChildTri 1 0 1 1 = (1, 1, 1) := by
  decide

example : rightChildTri 1 0 1 1 = (1, 0, 0) := by
  decide

example : leftChildTri 0 0 0 1 = (0, 0, 1) := by
  decide

example : rightChildTri 0 0 0 1 = (1, 0, 0) := by
  decide

example : leftChildTri 0 1 1 1 = (1, 0, 0) := by
  decide

example : rightChildTri 0 1 1 1 = (1, 1, 1) := by
  decide


/-- G1 = `a(bc)`: extracted type triples. -/
def G1states : List Tri :=
  [
    (1, 0, 0),                 -- X = abc
    leftChildTri 0 0 1 0,      -- A = a
    rightChildTri 0 0 1 0,     -- T = bc
    leftChildTri 1 0 1 1,      -- B = b
    rightChildTri 1 0 1 1      -- C = c
  ]


/-- G2 = `(ab)c`: extracted type triples. -/
def G2states : List Tri :=
  [
    (1, 0, 0),                 -- Y = abc
    leftChildTri 0 0 0 1,      -- U = ab
    rightChildTri 0 0 0 1,     -- C = c
    leftChildTri 0 1 1 1,      -- A = a
    rightChildTri 0 1 1 1      -- B = b
  ]


/-- G1 contains the internal constituent type `(0,1,0)`. -/
theorem g1_has_internal_010 :
    (0, 1, 0) ∈ G1states := by
  decide


/-- G2 does not contain the G1 internal constituent type `(0,1,0)`. -/
theorem g2_lacks_internal_010 :
    (0, 1, 0) ∉ G2states := by
  decide


/-- G2 contains the internal constituent type `(0,0,1)`. -/
theorem g2_has_internal_001 :
    (0, 0, 1) ∈ G2states := by
  decide


/-- G1 does not contain the G2 internal constituent type `(0,0,1)`. -/
theorem g1_lacks_internal_001 :
    (0, 0, 1) ∉ G1states := by
  decide


/-- The two presentations have the same number of extracted states. -/
theorem same_number_of_states :
    G1states.length = G2states.length := by
  decide


/-- The witness is not a cardinality artifact: both lists have length five. -/
theorem both_have_five_states :
    G1states.length = 5 ∧ G2states.length = 5 := by
  decide


/--
Arithmetic separation for the bracketing witness.

The type triple `(0,1,0)` occurs among the extracted type triples for
`a(bc)` but not among those for `(ab)c`.
-/
theorem bracketing_separates_by_010 :
    (0, 1, 0) ∈ G1states ∧ (0, 1, 0) ∉ G2states := by
  decide


/--
The opposite separating triple is also checked.

The type triple `(0,0,1)` occurs among the extracted type triples for
`(ab)c` but not among those for `a(bc)`.
-/
theorem bracketing_separates_by_001 :
    (0, 0, 1) ∈ G2states ∧ (0, 0, 1) ∉ G1states := by
  decide


/--
Paper-facing kernel of the bracketing non-rigidity example.

Any type-preserving isomorphism of finite typed structures would preserve
membership of type triples in the extracted state set.  The checked membership
separation below is the finite arithmetic core of the non-isomorphism proof.
-/
theorem bracketing_nonrigidity_arithmetic_kernel :
    ((0, 1, 0) ∈ G1states ∧ (0, 1, 0) ∉ G2states) ∧
    ((0, 0, 1) ∈ G2states ∧ (0, 0, 1) ∉ G1states) := by
  decide

end Bracketing
end JALC
end LeanCfgProject
