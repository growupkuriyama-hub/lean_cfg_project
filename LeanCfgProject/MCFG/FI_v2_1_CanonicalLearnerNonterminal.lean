import LeanCfgProject.MCFG.FI_v2_1_SubwordUnitEdgeEnumerationGold

/-!
# FI v2.1 Lean experiment: canonical learner nonterminals

This file starts the concrete learner-grammar side after the subword and unit
edge enumeration layers.  The goal is not yet to build the full `WorkingMCFG`.
Instead we introduce a concrete nonterminal universe for the sample-generated
learner and prove that the finite support produced by the preceding layers
really gives finite lists of learner nonterminals.

This is a vertical bridge: sample-derived tuples, contexts, and unit-edge
endpoints can now be regarded as nonterminal names of the learner-to-be.
-/

namespace FIv21

universe u v w

section CanonicalLearnerNonterminal

variable {N : Type w} {α : Type u}
variable [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M]

/-- Nonterminal names for the sample-generated canonical learner skeleton.

The constructors are intentionally implementation-facing:

* `root` is the future start nonterminal;
* `tuple d x` names the tuple exposed by a sample decomposition;
* `context d c` names the surrounding named context;
* `typed d τ` names an output-type state for the fixed finite monoid.

The full learner grammar is still future work.  This type is the finite
nonterminal universe on which that grammar construction can be layered. -/
inductive CanonicalLearnerNonterminal (α : Type u) (M : Type v) where
  | root : CanonicalLearnerNonterminal α M
  | tuple : (d : Nat) → Tuple α d → CanonicalLearnerNonterminal α M
  | context : (d : Nat) → NamedSentenceContext α d → CanonicalLearnerNonterminal α M
  | typed : (d : Nat) → (Fin d → M) → CanonicalLearnerNonterminal α M

namespace CanonicalLearnerNonterminal

/-- Arity of a canonical learner nonterminal. -/
def arity : CanonicalLearnerNonterminal α M → Nat
  | root => 1
  | tuple d _ => d
  | context d _ => d
  | typed d _ => d

/-- The observation type carried by tuple and typed nonterminals, when present. -/
def outputType? (obs : α → M) :
    (A : CanonicalLearnerNonterminal α M) → Option (Fin A.arity → M)
  | root => none
  | tuple d x => some (tupleType obs x)
  | context _ _ => none
  | typed _ τ => some τ

@[simp] theorem arity_root :
    (CanonicalLearnerNonterminal.root : CanonicalLearnerNonterminal α M).arity = 1 := by
  rfl

@[simp] theorem arity_tuple {d : Nat} (x : Tuple α d) :
    (CanonicalLearnerNonterminal.tuple d x : CanonicalLearnerNonterminal α M).arity = d := by
  rfl

@[simp] theorem arity_context {d : Nat} (c : NamedSentenceContext α d) :
    (CanonicalLearnerNonterminal.context d c : CanonicalLearnerNonterminal α M).arity = d := by
  rfl

@[simp] theorem arity_typed {d : Nat} (τ : Fin d → M) :
    (CanonicalLearnerNonterminal.typed d τ : CanonicalLearnerNonterminal α M).arity = d := by
  rfl

@[simp] theorem outputType_tuple (obs : α → M) {d : Nat} (x : Tuple α d) :
    outputType? (α := α) (M := M) obs
      (CanonicalLearnerNonterminal.tuple d x) = some (tupleType obs x) := by
  rfl

@[simp] theorem outputType_typed (obs : α → M) {d : Nat} (τ : Fin d → M) :
    outputType? (α := α) (M := M) obs
      (CanonicalLearnerNonterminal.typed d τ) = some τ := by
  rfl

end CanonicalLearnerNonterminal

/-- Tuple atoms of a finite learner support, viewed as learner nonterminals. -/
def supportTupleNonterminals
    (S : FiniteLearnerSupport α) : List (CanonicalLearnerNonterminal α M) :=
  S.tuples.map (fun X => CanonicalLearnerNonterminal.tuple X.1 X.2)

/-- Context atoms of a finite learner support, viewed as learner nonterminals. -/
def supportContextNonterminals
    (S : FiniteLearnerSupport α) : List (CanonicalLearnerNonterminal α M) :=
  S.contexts.map (fun C => CanonicalLearnerNonterminal.context C.1 C.2)

/-- Endpoints of listed unit edges, viewed as tuple nonterminals. -/
def supportUnitEdgeEndpointNonterminals
    (S : FiniteLearnerSupport α) : List (CanonicalLearnerNonterminal α M) :=
  S.unitEdges.bind (fun E =>
    [CanonicalLearnerNonterminal.tuple E.1 E.2.1,
     CanonicalLearnerNonterminal.tuple E.1 E.2.2])

/-- Output-typed versions of supported tuples. -/
def supportTypedTupleNonterminals
    (obs : α → M) (S : FiniteLearnerSupport α) :
    List (CanonicalLearnerNonterminal α M) :=
  S.tuples.map (fun X => CanonicalLearnerNonterminal.typed X.1 (tupleType obs X.2))

/-- The finite nonterminal list generated from a finite learner support. -/
def supportCanonicalNonterminals
    (obs : α → M) (S : FiniteLearnerSupport α) :
    List (CanonicalLearnerNonterminal α M) :=
  [CanonicalLearnerNonterminal.root] ++
    supportTupleNonterminals (M := M) S ++
    supportContextNonterminals (M := M) S ++
    supportUnitEdgeEndpointNonterminals (M := M) S ++
    supportTypedTupleNonterminals (M := M) obs S

/-- The learner root is always listed. -/
theorem root_mem_supportCanonicalNonterminals
    (obs : α → M) (S : FiniteLearnerSupport α) :
    CanonicalLearnerNonterminal.root ∈ supportCanonicalNonterminals (M := M) obs S := by
  unfold supportCanonicalNonterminals
  simp

/-- Supported tuples give listed tuple nonterminals. -/
theorem tupleNonterminal_mem_of_support
    {S : FiniteLearnerSupport α} {d : Nat} {x : Tuple α d}
    (hx : S.SupportsTuple x) :
    CanonicalLearnerNonterminal.tuple d x ∈
      supportTupleNonterminals (M := M) S := by
  unfold supportTupleNonterminals FiniteLearnerSupport.SupportsTuple at *
  exact List.mem_map.mpr ⟨Sigma.mk d x, hx, rfl⟩

/-- Supported contexts give listed context nonterminals. -/
theorem contextNonterminal_mem_of_support
    {S : FiniteLearnerSupport α} {d : Nat} {c : NamedSentenceContext α d}
    (hc : S.SupportsContext c) :
    CanonicalLearnerNonterminal.context d c ∈
      supportContextNonterminals (M := M) S := by
  unfold supportContextNonterminals FiniteLearnerSupport.SupportsContext at *
  exact List.mem_map.mpr ⟨Sigma.mk d c, hc, rfl⟩

/-- Supported tuples also give listed typed nonterminals carrying their fixed
observation type. -/
theorem typedNonterminal_mem_of_support
    (obs : α → M)
    {S : FiniteLearnerSupport α} {d : Nat} {x : Tuple α d}
    (hx : S.SupportsTuple x) :
    CanonicalLearnerNonterminal.typed d (tupleType obs x) ∈
      supportTypedTupleNonterminals (M := M) obs S := by
  unfold supportTypedTupleNonterminals FiniteLearnerSupport.SupportsTuple at *
  exact List.mem_map.mpr ⟨Sigma.mk d x, hx, rfl⟩

/-- Source endpoint of a listed unit edge is listed as a tuple nonterminal. -/
theorem unitEdge_srcNonterminal_mem_of_support
    {S : FiniteLearnerSupport α} {d : Nat} {x y : Tuple α d}
    (hxy : S.SupportsUnitEdge x y) :
    CanonicalLearnerNonterminal.tuple d x ∈
      supportUnitEdgeEndpointNonterminals (M := M) S := by
  unfold supportUnitEdgeEndpointNonterminals FiniteLearnerSupport.SupportsUnitEdge at *
  exact List.mem_bind.mpr ⟨Sigma.mk d (x, y), hxy, by simp⟩

/-- Target endpoint of a listed unit edge is listed as a tuple nonterminal. -/
theorem unitEdge_tgtNonterminal_mem_of_support
    {S : FiniteLearnerSupport α} {d : Nat} {x y : Tuple α d}
    (hxy : S.SupportsUnitEdge x y) :
    CanonicalLearnerNonterminal.tuple d y ∈
      supportUnitEdgeEndpointNonterminals (M := M) S := by
  unfold supportUnitEdgeEndpointNonterminals FiniteLearnerSupport.SupportsUnitEdge at *
  exact List.mem_bind.mpr ⟨Sigma.mk d (x, y), hxy, by simp⟩

/-- Supported tuples occur in the full generated nonterminal list. -/
theorem tupleNonterminal_mem_supportCanonical
    (obs : α → M)
    {S : FiniteLearnerSupport α} {d : Nat} {x : Tuple α d}
    (hx : S.SupportsTuple x) :
    CanonicalLearnerNonterminal.tuple d x ∈
      supportCanonicalNonterminals (M := M) obs S := by
  have h : CanonicalLearnerNonterminal.tuple d x ∈
      supportTupleNonterminals (M := M) S :=
    tupleNonterminal_mem_of_support (M := M) hx
  unfold supportCanonicalNonterminals
  simp [h]

/-- Supported contexts occur in the full generated nonterminal list. -/
theorem contextNonterminal_mem_supportCanonical
    (obs : α → M)
    {S : FiniteLearnerSupport α} {d : Nat} {c : NamedSentenceContext α d}
    (hc : S.SupportsContext c) :
    CanonicalLearnerNonterminal.context d c ∈
      supportCanonicalNonterminals (M := M) obs S := by
  have h : CanonicalLearnerNonterminal.context d c ∈
      supportContextNonterminals (M := M) S :=
    contextNonterminal_mem_of_support (M := M) hc
  unfold supportCanonicalNonterminals
  simp [h]

/-- Typed versions of supported tuples occur in the full generated nonterminal
list. -/
theorem typedNonterminal_mem_supportCanonical
    (obs : α → M)
    {S : FiniteLearnerSupport α} {d : Nat} {x : Tuple α d}
    (hx : S.SupportsTuple x) :
    CanonicalLearnerNonterminal.typed d (tupleType obs x) ∈
      supportCanonicalNonterminals (M := M) obs S := by
  have h : CanonicalLearnerNonterminal.typed d (tupleType obs x) ∈
      supportTypedTupleNonterminals (M := M) obs S :=
    typedNonterminal_mem_of_support (M := M) obs hx
  unfold supportCanonicalNonterminals
  simp [h]

/-- Source endpoints of supported unit edges occur in the full generated
nonterminal list. -/
theorem unitEdge_srcNonterminal_mem_supportCanonical
    (obs : α → M)
    {S : FiniteLearnerSupport α} {d : Nat} {x y : Tuple α d}
    (hxy : S.SupportsUnitEdge x y) :
    CanonicalLearnerNonterminal.tuple d x ∈
      supportCanonicalNonterminals (M := M) obs S := by
  have h : CanonicalLearnerNonterminal.tuple d x ∈
      supportUnitEdgeEndpointNonterminals (M := M) S :=
    unitEdge_srcNonterminal_mem_of_support (M := M) hxy
  unfold supportCanonicalNonterminals
  simp [h]

/-- Target endpoints of supported unit edges occur in the full generated
nonterminal list. -/
theorem unitEdge_tgtNonterminal_mem_supportCanonical
    (obs : α → M)
    {S : FiniteLearnerSupport α} {d : Nat} {x y : Tuple α d}
    (hxy : S.SupportsUnitEdge x y) :
    CanonicalLearnerNonterminal.tuple d y ∈
      supportCanonicalNonterminals (M := M) obs S := by
  have h : CanonicalLearnerNonterminal.tuple d y ∈
      supportUnitEdgeEndpointNonterminals (M := M) S :=
    unitEdge_tgtNonterminal_mem_of_support (M := M) hxy
  unfold supportCanonicalNonterminals
  simp [h]

namespace SubwordUnitEdgeEnumerationData

/-- The concrete learner nonterminal list generated by subword-unit-edge data. -/
noncomputable def learnerNonterminals
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K) :
    List (CanonicalLearnerNonterminal α M) :=
  supportCanonicalNonterminals (M := M) obs D.support

/-- Listed subword decompositions produce tuple nonterminals. -/
theorem tupleNonterminal_mem_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    CanonicalLearnerNonterminal.tuple 1 S.tuple ∈ D.learnerNonterminals := by
  exact tupleNonterminal_mem_supportCanonical (M := M) obs
    (D.supportsTuple_of_subword_mem hS)

/-- Listed subword decompositions produce context nonterminals. -/
theorem contextNonterminal_mem_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    CanonicalLearnerNonterminal.context 1 S.context ∈ D.learnerNonterminals := by
  exact contextNonterminal_mem_supportCanonical (M := M) obs
    (D.supportsContext_of_subword_mem hS)

/-- Listed subword decompositions produce typed nonterminals carrying their
observed tuple type. -/
theorem typedNonterminal_mem_of_subword_mem
    {G : WorkingMCFG N α} {obs : α → M} {K : Finset (Word α)}
    (D : SubwordUnitEdgeEnumerationData G obs K)
    {S : SubwordSampleDecomposition (α := α) K}
    (hS : S ∈ D.subwordDecompositions) :
    CanonicalLearnerNonterminal.typed 1 (tupleType obs S.tuple) ∈
      D.learnerNonterminals := by
  exact typedNonterminal_mem_supportCanonical (M := M) obs
    (D.supportsTuple_of_subword_mem hS)

/-- Every sampled word represented by the concrete enumerator gives tuple,
context, and typed nonterminals in the generated learner list. -/
theorem enumerated_sample_word_nonterminals
    (G : WorkingMCFG N α) (obs : α → M) (K : Finset (Word α))
    (f : Nat) (hfanout : 1 ≤ f) (hG : G.SemanticWorkingConditions)
    {w : Word α} (hw : w ∈ K) :
    ∃ S : SubwordSampleDecomposition (α := α) K,
      S ∈ (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).subwordDecompositions ∧
      S.sampleWord = w ∧
      CanonicalLearnerNonterminal.tuple 1 S.tuple ∈
        (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).learnerNonterminals ∧
      CanonicalLearnerNonterminal.context 1 S.context ∈
        (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).learnerNonterminals ∧
      CanonicalLearnerNonterminal.typed 1 (tupleType obs S.tuple) ∈
        (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG).learnerNonterminals := by
  rcases enumeratedSubwordUnitEdgeEnumerationData_supported_sample_word
      G obs K f hfanout hG hw with
    ⟨S, hS, hWord, _hTuple, _hContext, _hDist⟩
  refine ⟨S, hS, hWord, ?_, ?_, ?_⟩
  · exact (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG)
      .tupleNonterminal_mem_of_subword_mem hS
  · exact (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG)
      .contextNonterminal_mem_of_subword_mem hS
  · exact (enumeratedSubwordUnitEdgeEnumerationData G obs K f hfanout hG)
      .typedNonterminal_mem_of_subword_mem hS

end SubwordUnitEdgeEnumerationData

end CanonicalLearnerNonterminal

end FIv21
