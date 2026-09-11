import LeanCfgProject.FixedHCFG.Language

namespace LeanCfgProject
namespace FixedHCFG

universe u

/-- A learner nonterminal `[x : u, v]`. -/
structure LearnerNT (Sigma : Type u) where
  x : Word Sigma
  u : Word Sigma
  v : Word Sigma

/-- `[x : u, v]` is visible in the positive sample exactly when `uxv ∈ K`. -/
def Visible {Sigma : Type u} (K : Language Sigma)
    (q : LearnerNT Sigma) : Prop :=
  q.u ++ q.x ++ q.v ∈ K

/--
Terminal-yield derivations of the non-start part of the canonical learner.

The four constructors are the paper's rule families (4), (2), (3), and (1),
respectively.  The start rules (5) are kept separate below.  This presentation
is deliberately theorem-facing: every premise saying that a learner
nonterminal belongs to `V̂(K)` appears explicitly as a `Visible` premise.
-/
inductive Derives {Sigma : Type u} (Obs : Observer Sigma)
    (K : Language Sigma) : LearnerNT Sigma → Word Sigma → Prop
  | terminal (a : Sigma) (u v : Word Sigma)
      (hvis : Visible K { x := [a], u := u, v := v }) :
      Derives Obs K { x := [a], u := u, v := v } [a]
  | contextTransport (x u v u' v' w : Word Sigma)
      (hsrc : Visible K { x := x, u := u, v := v })
      (hdst : Visible K { x := x, u := u', v := v' })
      (hder : Derives Obs K { x := x, u := u', v := v' } w) :
      Derives Obs K { x := x, u := u, v := v } w
  | typedSubstitution (x x' u v w : Word Sigma)
      (hsrc : Visible K { x := x, u := u, v := v })
      (hdst : Visible K { x := x', u := u, v := v })
      (htype : Obs.value x = Obs.value x')
      (hder : Derives Obs K { x := x', u := u, v := v } w) :
      Derives Obs K { x := x, u := u, v := v } w
  | split (x y u v w₁ w₂ : Word Sigma)
      (hparent : Visible K { x := x ++ y, u := u, v := v })
      (hleft : Visible K { x := x, u := u, v := y ++ v })
      (hright : Visible K { x := y, u := u ++ x, v := v })
      (hder₁ : Derives Obs K { x := x, u := u, v := y ++ v } w₁)
      (hder₂ : Derives Obs K { x := y, u := u ++ x, v := v } w₂) :
      Derives Obs K { x := x ++ y, u := u, v := v } (w₁ ++ w₂)

/-- Terminal yields obtainable from the learner start symbol (Rule family (5)). -/
inductive StartDerives {Sigma : Type u} (Obs : Observer Sigma)
    (K : Language Sigma) : Word Sigma → Prop
  | epsilon (hmem : ([] : Word Sigma) ∈ K) :
      StartDerives Obs K []
  | sample (x w : Word Sigma)
      (hmem : x ∈ K)
      (hder : Derives Obs K { x := x, u := [], v := [] } w) :
      StartDerives Obs K w

end FixedHCFG
end LeanCfgProject
