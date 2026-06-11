import LeanCfgProject.JALC.Descriptor

namespace LeanCfgProject
namespace JALC

universe u v

/-
Residual/concept layer for the JALC algebra experiment.

This file gives a lightweight finite formal-concept style interface over
typed nonterminals and observed two-sided contexts.

The goal is paper-facing:
  * typed states form a finite carrier;
  * observed contexts form a finite carrier;
  * extents and intents are definable by finite filtering;
  * the resulting closure operators are mechanically well-typed.

This is not yet a full formalization of the mathematical theory in the
paper.  It is a Lean-checked finite architecture for the residual/concept
layer.
-/


/-- The finite typed-state carrier used by the residual/concept layer. -/
abbrev TypedState (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) :=
  TypedNonterminal N Obs


/-- The finite observed-context carrier used by the residual/concept layer. -/
abbrev ContextState {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) :=
  ObservedContext Obs


/-- A finite incidence relation between typed states and observed contexts. -/
abbrev Incidence (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) :=
  TypedState N Obs → ContextState Obs → Prop


/-- The full finite typed-state universe. -/
def allTypedStates (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N] :
    Finset (TypedState N Obs) :=
  Finset.univ


/-- The full finite context universe. -/
def allContextStates {Sigma : Type u}
    (Obs : FixedFiniteMonoidHom Sigma) :
    Finset (ContextState Obs) :=
  Finset.univ


/-- The extent of a finite set of contexts.

A typed state belongs to the extent when it is incident with every
context in the given finite context family.
-/
def extent (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R]
    (C : Finset (ContextState Obs)) :
    Finset (TypedState N Obs) :=
  (allTypedStates N Obs).filter
    (fun q => ∀ c ∈ C, R q c)


/-- The intent of a finite set of typed states.

A context belongs to the intent when every typed state in the given
finite state family is incident with it.
-/
def intent (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R]
    (S : Finset (TypedState N Obs)) :
    Finset (ContextState Obs) :=
  (allContextStates Obs).filter
    (fun c => ∀ q ∈ S, R q c)


/-- State-side concept closure: take the intent and then the extent. -/
def stateClosure (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R]
    (S : Finset (TypedState N Obs)) :
    Finset (TypedState N Obs) :=
  extent N Obs R (intent N Obs R S)


/-- Context-side concept closure: take the extent and then the intent. -/
def contextClosure (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R]
    (C : Finset (ContextState Obs)) :
    Finset (ContextState Obs) :=
  intent N Obs R (extent N Obs R C)


/-- A finite residual concept consists of a finite extent and a finite intent,
together with the two closure equations. -/
structure ResidualConcept (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R] where
  states : Finset (TypedState N Obs)
  contexts : Finset (ContextState Obs)
  states_closed : states = extent N Obs R contexts
  contexts_closed : contexts = intent N Obs R states


/-- The incidence induced by exact boundary agreement.

This simple incidence is useful as a sanity-check model: a typed state is
incident with a context exactly when the context has the same observed
left and right boundary as the state's two-sided type.
-/
def boundaryIncidence (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) :
    Incidence N Obs :=
  fun q c => q.ty.left = c.left ∧ q.ty.right = c.right


instance boundaryIncidenceDecidable (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma) :
    DecidableRel (boundaryIncidence N Obs) := by
  intro q c
  unfold boundaryIncidence
  infer_instance


/-- The singleton context corresponding to a typed state's boundary. -/
def boundaryContextOfState (N : Type u) {Sigma : Type v}
    {Obs : FixedFiniteMonoidHom Sigma}
    (q : TypedState N Obs) : ContextState Obs :=
  {
    left := q.ty.left
    right := q.ty.right
  }


/-- A typed state is incident with its own boundary context. -/
theorem boundaryIncidence_self (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    (q : TypedState N Obs) :
    boundaryIncidence N Obs q (boundaryContextOfState N q) := by
  unfold boundaryIncidence boundaryContextOfState
  constructor
  · rfl
  · rfl


/-- Membership characterization for the finite extent. -/
theorem mem_extent_iff (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R]
    (C : Finset (ContextState Obs))
    (q : TypedState N Obs) :
    q ∈ extent N Obs R C ↔ ∀ c ∈ C, R q c := by
  unfold extent allTypedStates
  simp


/-- Membership characterization for the finite intent. -/
theorem mem_intent_iff (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R]
    (S : Finset (TypedState N Obs))
    (c : ContextState Obs) :
    c ∈ intent N Obs R S ↔ ∀ q ∈ S, R q c := by
  unfold intent allContextStates
  simp


/-- The extent is always a subset of the full typed-state universe. -/
theorem extent_subset_univ (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R]
    (C : Finset (ContextState Obs)) :
    extent N Obs R C ⊆ allTypedStates N Obs := by
  intro q hq
  unfold extent
  exact Finset.mem_of_mem_filter hq


/-- The intent is always a subset of the full observed-context universe. -/
theorem intent_subset_univ (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R]
    (S : Finset (TypedState N Obs)) :
    intent N Obs R S ⊆ allContextStates Obs := by
  intro c hc
  unfold intent
  exact Finset.mem_of_mem_filter hc


/-- Context families are contravariant with respect to extents.

If `C₁ ⊆ C₂`, then every state satisfying all contexts in `C₂` also
satisfies all contexts in `C₁`.
-/
theorem extent_antitone (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R]
    {C₁ C₂ : Finset (ContextState Obs)}
    (hsub : C₁ ⊆ C₂) :
    extent N Obs R C₂ ⊆ extent N Obs R C₁ := by
  intro q hq
  rw [mem_extent_iff] at hq
  rw [mem_extent_iff]
  intro c hc
  exact hq c (hsub hc)


/-- State families are contravariant with respect to intents.

If `S₁ ⊆ S₂`, then every context satisfying all states in `S₂` also
satisfies all states in `S₁`.
-/
theorem intent_antitone (N : Type u) {Sigma : Type v}
    (Obs : FixedFiniteMonoidHom Sigma)
    [Fintype N] [DecidableEq N]
    (R : Incidence N Obs) [DecidableRel R]
    {S₁ S₂ : Finset (TypedState N Obs)}
    (hsub : S₁ ⊆ S₂) :
    intent N Obs R S₂ ⊆ intent N Obs R S₁ := by
  intro c hc
  rw [mem_intent_iff] at hc
  rw [mem_intent_iff]
  intro q hq
  exact hc q (hsub hq)


end JALC
end LeanCfgProject