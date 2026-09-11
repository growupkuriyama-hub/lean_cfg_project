import LeanCfgProject.MCFGv4.InducedOrientation
import Mathlib.Data.List.OfFn

/-!
# MCFGv4.PermutationDecoration

Rule-level construction for Lemma `lem:permutation-decoration` in the frozen
2026-09-07 manuscript.

For an original linear nondeleting rule and a chosen orientation of its parent
components, the induced child orientations are now available as genuine finite
permutations from `InducedOrientation.lean`.  This module begins the actual
syntax transformation: decorate the parent and children, permute the parent
components, and reindex each child-component variable by the inverse induced
orientation so that the transformed scan is in natural order.
-/

namespace MCFGv4

universe u v

namespace MCFGRule

variable {N : Type v} {α : Type u} {sig : MCFGSignature N}

/-- Child `j` decorated by the orientation induced from parent orientation `π`. -/
noncomputable def decoratedChild (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting)
    (j : Fin r.children.length) : OrientedNonterminal sig :=
  ⟨r.children.get j, r.inducedOrientation π j hlin hnd⟩

/-- The child list of the decorated rule.  The number and order of child
occurrences are unchanged. -/
noncomputable def decoratedChildren (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    List (OrientedNonterminal sig) :=
  List.ofFn fun j => r.decoratedChild π hlin hnd j

@[simp] theorem decoratedChildren_length (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    (r.decoratedChildren π hlin hnd).length = r.children.length := by
  simp [decoratedChildren]

/-- The `j`-th decorated child has the same underlying nonterminal as the
`j`-th original child. -/
@[simp] theorem decoratedChildren_get_base (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting)
    (j : Fin (r.decoratedChildren π hlin hnd).length) :
    ((r.decoratedChildren π hlin hnd).get j).base =
      r.children.get (Fin.cast (r.decoratedChildren_length π hlin hnd) j) := by
  simp [decoratedChildren, decoratedChild]

/-- The child-index cast from an original rule into its decorated child list. -/
noncomputable def decoratedChildIndex (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting)
    (j : Fin r.children.length) :
    Fin (r.decoratedChildren π hlin hnd).length :=
  Fin.cast (r.decoratedChildren_length π hlin hnd).symm j

@[simp] theorem decoratedChildIndex_val (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting)
    (j : Fin r.children.length) :
    (r.decoratedChildIndex π hlin hnd j).val = j.val := rfl

/-- Reindex one original child-component variable for the decorated rule.
If the induced orientation sends new position `i` to old component `k`, the
old occurrence `x_j^k` is renamed to the new variable `x_j^i`; hence the
inverse induced orientation occurs here. -/
noncomputable def decorateVariable (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting)
    (rv : RuleVariable sig r.children) :
    RuleVariable (permutationDecoratedSignature sig)
      (r.decoratedChildren π hlin hnd) := by
  let j' := r.decoratedChildIndex π hlin hnd rv.child
  let k := (r.inducedOrientation π rv.child hlin hnd).symm rv.component
  refine { child := j', component := ?_ }
  have hArity :
      sig.arity (r.children.get rv.child) =
        (permutationDecoratedSignature sig).arity
          ((r.decoratedChildren π hlin hnd).get j') := by
    simp [j', decoratedChildIndex, decoratedChildren, decoratedChild,
      permutationDecoratedSignature]
  exact Fin.cast hArity k

/-- Transform one template atom. -/
noncomputable def decorateAtom (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    TemplateAtom sig α r.children →
      TemplateAtom (permutationDecoratedSignature sig) α
        (r.decoratedChildren π hlin hnd)
  | TemplateAtom.terminal a => TemplateAtom.terminal a
  | TemplateAtom.variable rv => TemplateAtom.variable
      (r.decorateVariable π hlin hnd rv)

/-- Transform one parent template component. -/
noncomputable def decorateComponent (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting)
    (component : List (TemplateAtom sig α r.children)) :
    List (TemplateAtom (permutationDecoratedSignature sig) α
      (r.decoratedChildren π hlin hnd)) :=
  component.map (r.decorateAtom π hlin hnd)

/-- Parent components of the decorated rule: first expose the parent in
orientation `π`, then rename all child variables according to the inverse
induced child orientations. -/
noncomputable def decoratedComponents (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    List (List (TemplateAtom (permutationDecoratedSignature sig) α
      (r.decoratedChildren π hlin hnd))) :=
  (r.orientedComponents π).map (r.decorateComponent π hlin hnd)

@[simp] theorem decoratedComponents_length (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    (r.decoratedComponents π hlin hnd).length = sig.arity r.lhs := by
  simp [decoratedComponents]

/-- One rule copy in the permutation-decoration construction. -/
noncomputable def permutationDecorate (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    MCFGRule (permutationDecoratedSignature sig) α where
  lhs := ⟨r.lhs, π⟩
  children := r.decoratedChildren π hlin hnd
  components := r.decoratedComponents π hlin hnd
  components_length := by
    simpa [permutationDecoratedSignature] using
      r.decoratedComponents_length π hlin hnd

/-- Decoration itself preserves rule rank exactly. -/
theorem permutationDecorate_rank (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    (r.permutationDecorate π hlin hnd).rank = r.rank := by
  simp [permutationDecorate, rank]

/-- Decoration itself preserves the parent fan-out exactly. -/
theorem permutationDecorate_lhs_arity (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    (permutationDecoratedSignature sig).arity
      (r.permutationDecorate π hlin hnd).lhs = sig.arity r.lhs := rfl

end MCFGRule

end MCFGv4
