import LeanCfgProject.MCFGv4.StandardSemantics
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.Perm.Basic

/-!
# MCFGv4.InducedOrientation

Arbitrary-rank syntax infrastructure for Definition `def:induced-orientation`
and Lemma `lem:permutation-decoration` in the frozen 2026-09-07 manuscript.

The key representation choice is to expose, for every parent orientation, the
left-to-right scan order of child-component indices.  For a linear nondeleting
rule this list is a permutation of `0, ..., d_j-1`; the results below establish
that fact directly from the manuscript hypotheses.
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

/-- Filtering variables after concatenating a list of template components is
the same as filtering each component and concatenating the resulting lists. -/
private theorem filterMap_foldr_append {β γ : Type*}
    (f : β → Option γ) (xs : List (List β)) :
    (xs.foldr (· ++ ·) []).filterMap f =
      xs.flatMap (fun ys => ys.filterMap f) := by
  induction xs with
  | nil => rfl
  | cons ys rest ih =>
      simp [ih]

/-- Reordering the parent components by an orientation changes only their list
order, not the multiset of components. -/
theorem orientedComponents_perm_components (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs))) :
    r.orientedComponents π ~ r.components := by
  have hbase :
      List.ofFn (fun i : Fin (sig.arity r.lhs) => r.componentAt i) =
        r.components := by
    calc
      List.ofFn (fun i : Fin (sig.arity r.lhs) => r.componentAt i) =
          List.ofFn (List.get r.components) := by
            symm
            simpa [componentAt] using
              (List.ofFn_congr r.components_length (List.get r.components))
      _ = r.components := List.ofFn_get _
  calc
    r.orientedComponents π =
        List.ofFn ((fun i : Fin (sig.arity r.lhs) => r.componentAt i) ∘ π) := by
          rfl
    _ ~ List.ofFn (fun i : Fin (sig.arity r.lhs) => r.componentAt i) :=
      π.ofFn_comp_perm _
    _ = r.components := hbase

/-- The oriented variable scan is a permutation of the rule's ordinary
left-to-right variable list.  Thus parent orientation cannot create or delete a
child-component occurrence. -/
theorem orientedVariables_perm_usedVariables (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs))) :
    r.orientedVariables π ~ r.usedVariables := by
  have hflat :=
    (r.orientedComponents_perm_components π).flatMap
      (f := fun component =>
        component.filterMap fun atom =>
          match atom with
          | TemplateAtom.terminal _ => none
          | TemplateAtom.variable rv => some rv)
      (g := fun component =>
        component.filterMap fun atom =>
          match atom with
          | TemplateAtom.terminal _ => none
          | TemplateAtom.variable rv => some rv)
      (fun _ _ => List.Perm.refl _)
  simpa [orientedVariables, orientedAtoms, usedVariables,
    filterMap_foldr_append] using hflat

/-- Linearity remains visible after an arbitrary parent-orientation scan. -/
theorem orientedVariables_nodup (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs))) (hlin : r.Linear) :
    (r.orientedVariables π).Nodup := by
  have hused : r.usedVariables.Nodup := by
    simpa [Linear] using hlin
  exact (r.orientedVariables_perm_usedVariables π).nodup_iff.mpr hused

/-- Under linearity, the recorded superscripts for one child have no
repetitions. -/
theorem childComponentOrder_nodup (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (j : Fin r.children.length) (hlin : r.Linear) :
    (r.childComponentOrder π j).Nodup := by
  unfold childComponentOrder
  apply (r.orientedVariables_nodup π hlin).filterMap
  intro rv rv' b hb hb'
  by_cases hrv : rv.child = j
  · by_cases hrv' : rv'.child = j
    · rcases rv with ⟨c, k⟩
      rcases rv' with ⟨c', k'⟩
      dsimp at hrv hrv' hb hb' ⊢
      subst c
      subst c'
      simp at hb hb'
      have hval : k.val = k'.val := hb.symm.trans hb'
      have hk : k = k' := Fin.ext hval
      subst k'
      rfl
    · simp [hrv'] at hb'
  · simp [hrv] at hb

/-- Every superscript recorded for child `j` lies in that child's fan-out
range. -/
theorem childComponentOrder_bounded (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (j : Fin r.children.length) {k : Nat}
    (hk : k ∈ r.childComponentOrder π j) :
    k < sig.arity (r.children.get j) := by
  unfold childComponentOrder at hk
  rcases List.mem_filterMap.1 hk with ⟨rv, hrv, hmem⟩
  by_cases hc : rv.child = j
  · have hlt := rv.component.isLt
    rw [hc] at hlt
    simp [hc] at hmem
    simpa [hmem] using hlt
  · simp [hc] at hmem

/-- Nondeletion guarantees that every component superscript of child `j`
actually occurs in every oriented parent scan. -/
theorem childComponentOrder_complete (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (j : Fin r.children.length) (hnd : r.Nondeleting)
    (k : Nat) (hk : k < sig.arity (r.children.get j)) :
    k ∈ r.childComponentOrder π j := by
  let component : Fin (sig.arity (r.children.get j)) := ⟨k, hk⟩
  let rv : RuleVariable sig r.children :=
    { child := j, component := component }
  have hused : rv ∈ r.usedVariables := hnd j component
  have horiented : rv ∈ r.orientedVariables π :=
    (r.orientedVariables_perm_usedVariables π).mem_iff.mpr hused
  unfold childComponentOrder
  apply List.mem_filterMap.2
  refine ⟨rv, horiented, ?_⟩
  simp [rv, component]

/-- Membership in the child scan order is exactly membership in the finite
component-index range. -/
theorem childComponentOrder_mem_iff (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (j : Fin r.children.length) (hnd : r.Nondeleting) (k : Nat) :
    k ∈ r.childComponentOrder π j ↔
      k < sig.arity (r.children.get j) := by
  constructor
  · exact r.childComponentOrder_bounded π j
  · exact r.childComponentOrder_complete π j hnd k

/-- Formal content of Definition `def:induced-orientation`: for a linear
nondeleting rule, scanning child `j` in any parent orientation records each
component superscript exactly once, hence yields a permutation of the natural
component order. -/
theorem childComponentOrder_perm_range (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (j : Fin r.children.length) (hlin : r.Linear) (hnd : r.Nondeleting) :
    r.childComponentOrder π j ~
      List.range (sig.arity (r.children.get j)) := by
  refine (List.perm_ext_iff_of_nodup
    (r.childComponentOrder_nodup π j hlin) (by simp)).2 ?_
  intro k
  rw [r.childComponentOrder_mem_iff π j hnd k]
  simp

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
