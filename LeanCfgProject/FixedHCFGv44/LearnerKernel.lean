import LeanCfgProject.FixedHCFGv44.Language

namespace LeanCfgProject
namespace FixedHCFGv44

universe u

/-- A hypothesis nonterminal `[x : u, v]`. -/
structure LearnerNT (Sigma : Type u) where
  x : Word Sigma
  u : Word Sigma
  v : Word Sigma

/-- `[x : u, v]` is observed in the positive sample. -/
def Visible {Sigma : Type u} (K : Language Sigma)
    (q : LearnerNT Sigma) : Prop :=
  q.u ++ q.x ++ q.v ∈ K

/-- The v44 side condition saying that a learner core is a nonempty factor. -/
def AdmissibleNT {Sigma : Type u} (q : LearnerNT Sigma) : Prop :=
  Internal q.x

/--
Terminal-yield derivations of the non-start part of the v44 batch grammar.

The constructors correspond exactly to production families (4), (2), (3),
and (1).  Nonemptiness premises make the manuscript's `x,y ∈ Sigma+`
restriction explicit, so every application of fixed-h substitutability is
legally typed.
-/
inductive Derives {Sigma : Type u} (Obs : Observer Sigma)
    (K : Language Sigma) : LearnerNT Sigma → Word Sigma → Prop
  | terminal (a : Sigma) (u v : Word Sigma)
      (hvis : Visible K { x := [a], u := u, v := v }) :
      Derives Obs K { x := [a], u := u, v := v } [a]
  | contextTransport (x u v u' v' w : Word Sigma)
      (hx : Internal x)
      (hsrc : Visible K { x := x, u := u, v := v })
      (hdst : Visible K { x := x, u := u', v := v' })
      (hder : Derives Obs K { x := x, u := u', v := v' } w) :
      Derives Obs K { x := x, u := u, v := v } w
  | typedSubstitution (x x' u v w : Word Sigma)
      (hx : Internal x)
      (hx' : Internal x')
      (hsrc : Visible K { x := x, u := u, v := v })
      (hdst : Visible K { x := x', u := u, v := v })
      (htype : obsValue Obs x = obsValue Obs x')
      (hder : Derives Obs K { x := x', u := u, v := v } w) :
      Derives Obs K { x := x, u := u, v := v } w
  | split (x y u v w₁ w₂ : Word Sigma)
      (hx : Internal x)
      (hy : Internal y)
      (hparent : Visible K { x := x ++ y, u := u, v := v })
      (hleft : Visible K { x := x, u := u, v := y ++ v })
      (hright : Visible K { x := y, u := u ++ x, v := v })
      (hder₁ : Derives Obs K { x := x, u := u, v := y ++ v } w₁)
      (hder₂ : Derives Obs K { x := y, u := u ++ x, v := v } w₂) :
      Derives Obs K { x := x ++ y, u := u, v := v } (w₁ ++ w₂)

/-- Terminal yields obtainable from the v44 hypothesis start symbol (Rule (5)). -/
inductive StartDerives {Sigma : Type u} (Obs : Observer Sigma)
    (K : Language Sigma) : Word Sigma → Prop
  | epsilon (hmem : ([] : Word Sigma) ∈ K) :
      StartDerives Obs K []
  | sample (x w : Word Sigma)
      (hx : Internal x)
      (hmem : x ∈ K)
      (hder : Derives Obs K { x := x, u := [], v := [] } w) :
      StartDerives Obs K w

end FixedHCFGv44
end LeanCfgProject
