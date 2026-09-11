import LeanCfgProject.MCFGv4.StandardSemantics
import Mathlib.GroupTheory.Perm.Basic

/-!
# MCFGv4.InducedOrientation

Arbitrary-rank syntax infrastructure for Definition `def:induced-orientation`
and Lemma `lem:permutation-decoration` in the frozen 2026-09-07 manuscript.

The key representation choice is to expose, for every parent orientation, the
left-to-right scan order of child-component indices.  For a linear nondeleting
rule this list is a permutation of `0, ..., d_j-1`; the conversion of that scan
order into an actual `Equiv.Perm` is the next proof layer.
-/

namespace MCFGv4

universe u v

namespace MCFGRule

variable {N : Type v} {α : Type u} {sig : MCFGSignature N}

/-- Access a parent template component by its manuscript fan-out index. -/
def componentAt (r : MCFGRule sig α) (i : Fin (sig.arity r.lhs)) :
    List (TemplateAtom sig α r.children) :=
  r.components.get (Fin.cast r.components_length.symm i)

/-- Parent template components scanned in orientation `π`. -/
def orientedComponents (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs))) :
    List (List (TemplateAtom sig α r.children)) :=
  List.ofFn fun i => r.componentAt (π i)

/-- Complete template-atom scan in parent orientation `π`. -/
def orientedAtoms (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs))) :
    List (TemplateAtom sig α r.children) :=
  (r.orientedComponents π).foldr (· ++ ·) []

/-- Variables encountered in the oriented parent scan. -/
def orientedVariables (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs))) :
    List (RuleVariable sig r.children) :=
  (r.orientedAtoms π).filterMap fun atom =>
    match atom with
    | TemplateAtom.terminal _ => none
    | TemplateAtom.variable rv => some rv

/-- The superscripts of variables belonging to child `j`, in the order in which
they occur while scanning the parent tuple with orientation `π`.

Using natural-number superscripts here avoids dependent casts between component
index types while retaining exactly the finite order data needed to construct
the manuscript's induced permutation. -/
def childComponentOrder (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (j : Fin r.children.length) : List Nat :=
  (r.orientedVariables π).filterMap fun rv =>
    if rv.child = j then some rv.component.val else none

/-- The identity-order criterion for a nonpermuting rule.  On a linear
nondeleting rule, this says precisely that child variables occur as
`x_j^1, ..., x_j^{d_j}` from left to right. -/
def Nonpermuting (r : MCFGRule sig α) : Prop :=
  ∀ j : Fin r.children.length,
    r.childComponentOrder (Equiv.refl _) j =
      List.range (sig.arity (r.children.get j))

@[simp] theorem orientedComponents_length (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs))) :
    (r.orientedComponents π).length = sig.arity r.lhs := by
  simp [orientedComponents]

end MCFGRule

/-- A nonterminal decorated by an orientation of its output components, as in
the construction of Lemma `lem:permutation-decoration`. -/
structure OrientedNonterminal {N : Type v} (sig : MCFGSignature N) where
  base : N
  orientation : Equiv.Perm (Fin (sig.arity base))

/-- Signature obtained by permutation-decoration.  Decorations change only the
finite structural state; they do not change fan-out. -/
def permutationDecoratedSignature {N : Type v} (sig : MCFGSignature N) :
    MCFGSignature (OrientedNonterminal sig) where
  start := ⟨sig.start, Equiv.refl _⟩
  arity A := sig.arity A.base
  arity_pos A := sig.arity_pos A.base
  start_arity := sig.start_arity

@[simp] theorem permutationDecorated_arity {N : Type v}
    (sig : MCFGSignature N) (A : OrientedNonterminal sig) :
    (permutationDecoratedSignature sig).arity A = sig.arity A.base := rfl

/-- Identity-decorated copy of an original nonterminal. -/
def identityDecorated {N : Type v} (sig : MCFGSignature N) (A : N) :
    OrientedNonterminal sig :=
  ⟨A, Equiv.refl _⟩

end MCFGv4
