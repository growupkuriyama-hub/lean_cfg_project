import LeanCfgProject.FixedHCFG.TrimmedLanguage
import LeanCfgProject.FixedHCFG.Reconstruction

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-- A retained typed state after reachable/productive trimming. -/
abbrev KeptState {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) :=
  {X : TypedNT N Obs // TypedKept Obs terminal binary start X}

/-- Terminal rule relation inherited by retained typed states. -/
def keptTerminal {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) (a : Sigma) : Prop :=
  terminal X.1.label a ∧ Obs.value [a] = X.1.yieldType

/-- Binary rule relation inherited by retained typed states. -/
def keptBinary {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X Y Z : KeptState Obs terminal binary start) : Prop :=
  binary X.1.label Y.1.label Z.1.label ∧
    Obs.mul Y.1.yieldType Z.1.yieldType = X.1.yieldType ∧
    Y.1.leftType = X.1.leftType ∧
    Y.1.rightType = Obs.mul Z.1.yieldType X.1.rightType ∧
    Z.1.leftType = Obs.mul X.1.leftType Y.1.yieldType ∧
    Z.1.rightType = X.1.rightType

/-- Typed states which occur directly under the start interface. -/
def keptStart {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Prop :=
  start X.1.label ∧
    X.1.leftType = Obs.one ∧ X.1.rightType = Obs.one

/-- Every retained state has at least one terminal yield. -/
noncomputable def chosenOmega {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma :=
  Classical.choose X.property.1

/-- The chosen yield is genuinely derived by the retained state's full typed copy. -/
theorem chosenOmega_spec {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    TypedDerives Obs terminal binary X.1 (chosenOmega X) := by
  exact Classical.choose_spec X.property.1

/-- Direct start states have the empty two-sided occurrence. -/
theorem keptStart_occurs_empty {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start)
    (hStart : keptStart X) :
    TypedOccurs Obs terminal binary start X.1 [] [] := by
  rcases X with ⟨⟨A, p, m, n⟩, hkeep⟩
  change start A ∧ m = Obs.one ∧ n = Obs.one at hStart
  rcases hStart with ⟨hA, hm, hn⟩
  subst m
  subst n
  exact TypedOccurs.start (p := p) hA

/--
Each retained state admits a context witness, chosen so that a direct start
state uses the empty context.  This is the only normalization needed by the
learning proof; shortlex minimality is a further canonicality condition.
-/
theorem exists_preferred_context {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    ∃ u v : Word Sigma,
      TypedOccurs Obs terminal binary start X.1 u v ∧
        (keptStart X → u = [] ∧ v = []) := by
  classical
  by_cases hStart : keptStart X
  · exact ⟨[], [], keptStart_occurs_empty X hStart,
      fun _ => ⟨rfl, rfl⟩⟩
  · rcases X.property.2 with ⟨u, v, hOcc⟩
    exact ⟨u, v, hOcc, fun hs => (hStart hs).elim⟩

noncomputable def chosenLeftCtx {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma :=
  Classical.choose (exists_preferred_context X)

noncomputable def chosenRightCtx {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma :=
  Classical.choose (Classical.choose_spec (exists_preferred_context X))

/-- Specification of the preferred chosen context. -/
theorem chosenContext_spec {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) :
    TypedOccurs Obs terminal binary start X.1
      (chosenLeftCtx X) (chosenRightCtx X) ∧
    (keptStart X → chosenLeftCtx X = [] ∧ chosenRightCtx X = []) := by
  exact Classical.choose_spec
    (Classical.choose_spec (exists_preferred_context X))

/-- Anchor observation associated with a retained state. -/
def anchorWord {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) : Word Sigma :=
  chosenLeftCtx X ++ chosenOmega X ++ chosenRightCtx X

/-- Observation associated with a retained terminal rule. -/
def terminalObservationWord {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X : KeptState Obs terminal binary start) (a : Sigma) : Word Sigma :=
  chosenLeftCtx X ++ [a] ++ chosenRightCtx X

/-- Observation associated with a retained binary rule. -/
def binaryObservationWord {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (X Y Z : KeptState Obs terminal binary start) : Word Sigma :=
  chosenLeftCtx X ++ chosenOmega Y ++ chosenOmega Z ++ chosenRightCtx X

/--
An enriched characteristic observation set.  Compared with the manuscript's
minimal `CS`, this set includes anchors explicitly.  This avoids using shortlex
root-decomposition in the extraction bridge while preserving finiteness and all
reconstruction guarantees.
-/
def EnrichedCS {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    (epsilonStart : Prop) : Language Sigma :=
  fun z =>
    (∃ X : KeptState Obs terminal binary start, z = anchorWord X) ∨
    (∃ (X : KeptState Obs terminal binary start) (a : Sigma),
      keptTerminal X a ∧ z = terminalObservationWord X a) ∨
    (∃ X Y Z : KeptState Obs terminal binary start,
      keptBinary X Y Z ∧ z = binaryObservationWord X Y Z) ∨
    (z = [] ∧ epsilonStart)

/--
Build the reconstruction interface from the actual retained typed states using
the enriched finite observation set.
-/
noncomputable def enrichedReconstructionBasis
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : TerminalRules N Sigma) (binary : BinaryRules N)
    (start : StartRules N) (epsilonStart : Prop) :
    ReconstructionBasis Obs (KeptState Obs terminal binary start) where
  terminal := keptTerminal
  binary := keptBinary
  startState := keptStart
  hasEpsilon := epsilonStart
  omega := chosenOmega
  leftCtx := chosenLeftCtx
  rightCtx := chosenRightCtx
  yieldType := fun X => X.1.yieldType
  leftType := fun X => X.1.leftType
  rightType := fun X => X.1.rightType
  CS := EnrichedCS epsilonStart
  omega_type := by
    intro X
    exact lemma_4_5_i_yield_type Obs terminal binary (chosenOmega_spec X)
  left_context_type := by
    intro X
    exact (lemma_4_5_ii_context_type Obs terminal binary start
      (chosenContext_spec X).1).1
  right_context_type := by
    intro X
    exact (lemma_4_5_ii_context_type Obs terminal binary start
      (chosenContext_spec X).1).2
  terminal_type := by
    intro X a h
    exact h.2
  binary_yield_type := by
    intro X Y Z h
    exact h.2.1
  anchor_mem := by
    intro X
    exact Or.inl ⟨X, rfl⟩
  terminal_observation_mem := by
    intro X a h
    exact Or.inr (Or.inl ⟨X, a, h, rfl⟩)
  binary_observation_mem := by
    intro X Y Z h
    exact Or.inr (Or.inr (Or.inl ⟨X, Y, Z, h, rfl⟩))
  start_context := by
    intro X h
    exact (chosenContext_spec X).2 h
  epsilon_mem := by
    intro h
    exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))

/-- Injective finite encoding of a typed state by its four components. -/
def typedNTKey {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma} (X : TypedNT N Obs) :
    N × Obs.M × Obs.M × Obs.M :=
  (X.label, X.yieldType, X.leftType, X.rightType)

/-- The component encoding of typed states is injective. -/
theorem typedNTKey_injective {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma} :
    Function.Injective (typedNTKey (N := N) (Obs := Obs)) := by
  intro X Y h
  rcases X with ⟨xl, xp, xm, xn⟩
  rcases Y with ⟨yl, yp, ym, yn⟩
  simp only [typedNTKey] at h
  cases h
  rfl

/-- Typed state space is finite whenever the untyped state space is finite. -/
noncomputable instance typedNTFinite
    {N : Type v} {Sigma : Type u} {Obs : Observer Sigma}
    [Finite N] : Finite (TypedNT N Obs) :=
  Finite.of_injective (typedNTKey (N := N) (Obs := Obs))
    typedNTKey_injective

/--
The enriched observation set is finite for finite grammars and finite terminal
alphabets.  No decidability of productivity/reachability is needed.
-/
theorem enrichedCS_finite
    {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : TerminalRules N Sigma} {binary : BinaryRules N}
    {start : StartRules N}
    [Finite N] [Finite Sigma]
    (epsilonStart : Prop) :
    (EnrichedCS (Obs := Obs) (terminal := terminal) (binary := binary)
      (start := start) epsilonStart).Finite := by
  let W := KeptState Obs terminal binary start
  let A : Set (Word Sigma) := Set.range
    (fun X : W => anchorWord X)
  let T : Set (Word Sigma) := Set.range
    (fun p : W × Sigma => terminalObservationWord p.1 p.2)
  let R : Set (Word Sigma) := Set.range
    (fun p : W × W × W => binaryObservationWord p.1 p.2.1 p.2.2)
  have hA : A.Finite := Set.finite_range _
  have hT : T.Finite := Set.finite_range _
  have hR : R.Finite := Set.finite_range _
  have hAll : (A ∪ T ∪ R ∪ ({[]} : Set (Word Sigma))).Finite :=
    (((hA.union hT).union hR).union (Set.finite_singleton []))
  refine hAll.subset ?_
  intro z hz
  rcases hz with hAnchor | hTerminal | hBinary | hEps
  · rcases hAnchor with ⟨X, rfl⟩
    exact Or.inl (Or.inl (Or.inl ⟨X, rfl⟩))
  · rcases hTerminal with ⟨X, a, hRule, rfl⟩
    exact Or.inl (Or.inl (Or.inr ⟨(X, a), rfl⟩))
  · rcases hBinary with ⟨X, Y, Z, hRule, rfl⟩
    exact Or.inl (Or.inr ⟨(X, Y, Z), rfl⟩)
  · rcases hEps with ⟨rfl, hStart⟩
    exact Or.inr (Set.mem_singleton [])

end FixedHCFG
end LeanCfgProject
