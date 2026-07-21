/-
Copyright (c) 2026 Takayuki Kuriyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Takayuki Kuriyama
-/
import LeanCfgProject.MCFG.ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSerializedStandardMachineRealization

/-!
# ConcreteCanonicalLearnerWorkingGrammarObservationSelectionEncodedSemanticOracleBoundary.lean

The preceding files prove a complete serialized NP-style witness theorem for an
input that already contains the full ordinary/Pareto feasibility bit tables.
This file makes the semantic-oracle boundary explicit.

Two input types are deliberately separated.

```text
CorrectedConcreteObservationSelectionMaterializedTableInput
CorrectedConcreteObservationSelectionCompactInput
```

A materialized table input is a checked `List Nat` containing

```text
budget,
codeBound,
cost membership bits,
Pareto membership bits.
```

Its two bit vectors have length `codeBound`; on canonical instances this bound
is `2 ^ U.card`.  The existing serialized verifier, polynomial witness theorem,
NP-style language class, and standard-machine realization apply to this
materialized table input.

A compact input is intentionally left as a distinct wrapper.  The intended
grammar/observation/weight instance will be defined in a later file without
embedding every feasibility answer.

The bridge between the two sides is isolated in

```text
CorrectedConcreteObservationSelectionSemanticOracleBoundary
```

whose `Materializes compact table` relation must be total, functional, and
membership preserving.  A deterministic materializer chooses the table, and a
polynomial materializer additionally proves output-size and construction-work
bounds in the compact payload length.

This file constructs only a payload-identity reference boundary.  That
reference proves the API coherent, but it is not the desired compact
observation-design construction: its “compact” payload is already the complete
table payload.  A future compact-instance theorem must supply a nontrivial
materializer or, preferably, a direct compact certificate verifier.

At the exact semantic positive-additive minimum rank, the final theorem records
the exact scope of the current result:

* the canonical payload belongs to the materialized Pareto table language;
* it successfully decodes to the complete bit-table record;
* its length is `2 + 2 * 2 ^ U.card`;
* the canonical least Pareto code is accepted by the current standard-machine
  reference realization;
* all preceding resource, decoding, and Pareto-optimality conclusions remain
  valid.

No compact-input NP-membership, NP-hardness, or NP-completeness claim is made.
No target grammar is supplied to any learner.
No `sorry`, `admit`, or `axiom` is used.
-/

namespace MCFG

universe u v w z


/-- Input wrapper for a fully materialized ordinary/Pareto feasibility table. -/
structure CorrectedConcreteObservationSelectionMaterializedTableInput where

  payload : List Nat


/-- Input wrapper reserved for a future compact grammar-level
observation-selection instance.

The separate type prevents the existing table-input theorem from being applied
to the compact problem by definitional equality. -/
structure CorrectedConcreteObservationSelectionCompactInput where

  payload : List Nat


namespace CorrectedConcreteObservationSelectionMaterializedTableInput

section MaterializedTableLanguages

/-- A materialized input contains a successfully decoded complete finite
feasibility-table record. -/
def HasDecodedFeasibilityTable
    (input :
      CorrectedConcreteObservationSelectionMaterializedTableInput) : Prop :=
  ∃ data : CorrectedConcreteEncodedObservationSelectionData,
    CorrectedConcreteEncodedObservationSelectionData.decode
        input.payload =
      some data

/-- Ordinary-cost language on wrapped materialized table inputs. -/
def costLanguage :
    Set CorrectedConcreteObservationSelectionMaterializedTableInput :=
  {input |
    input.payload ∈
      CorrectedConcreteEncodedObservationSelectionData.serializedCostNPStyleLanguage}

/-- Pareto-scalar language on wrapped materialized table inputs. -/
def paretoLanguage :
    Set CorrectedConcreteObservationSelectionMaterializedTableInput :=
  {input |
    input.payload ∈
      CorrectedConcreteEncodedObservationSelectionData.serializedParetoNPStyleLanguage}

/-- Exact ordinary wrapped-language decision equation. -/
theorem mem_costLanguage_iff
    (input :
      CorrectedConcreteObservationSelectionMaterializedTableInput) :
    input ∈ costLanguage ↔
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
          input.payload =
        true := by

  rfl

/-- Exact Pareto wrapped-language decision equation. -/
theorem mem_paretoLanguage_iff
    (input :
      CorrectedConcreteObservationSelectionMaterializedTableInput) :
    input ∈ paretoLanguage ↔
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
          input.payload =
        true := by

  rfl

/-- Every accepted ordinary table input really contains a successfully decoded
feasibility-table record. -/
theorem hasDecodedFeasibilityTable_of_mem_costLanguage
    {input :
      CorrectedConcreteObservationSelectionMaterializedTableInput}
    (hInput :
      input ∈ costLanguage) :
    input.HasDecodedFeasibilityTable := by

  have hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision
            input.payload =
          true :=
    (mem_costLanguage_iff input).mp
      hInput

  rcases
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedCostDecision_eq_true_iff
        input.payload).mp
        hDecision with
    ⟨data, hDecode, hOne⟩

  exact ⟨data, hDecode⟩

/-- Every accepted Pareto table input really contains a successfully decoded
feasibility-table record. -/
theorem hasDecodedFeasibilityTable_of_mem_paretoLanguage
    {input :
      CorrectedConcreteObservationSelectionMaterializedTableInput}
    (hInput :
      input ∈ paretoLanguage) :
    input.HasDecodedFeasibilityTable := by

  have hDecision :
      CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision
            input.payload =
          true :=
    (mem_paretoLanguage_iff input).mp
      hInput

  rcases
      (CorrectedConcreteEncodedObservationSelectionData.runSerializedParetoDecision_eq_true_iff
        input.payload).mp
        hDecision with
    ⟨data, hDecode, hOne⟩

  exact ⟨data, hDecode⟩

/-- Successful table decoding exposes exact ordinary and Pareto bit-vector
lengths. -/
theorem decodedFeasibilityTable_exact_lengths
    {input :
      CorrectedConcreteObservationSelectionMaterializedTableInput}
    (hInput :
      input.HasDecodedFeasibilityTable) :
    ∃ data : CorrectedConcreteEncodedObservationSelectionData,
      CorrectedConcreteEncodedObservationSelectionData.decode
            input.payload =
          some data ∧
        data.costBits.length =
          data.codeBound ∧
        data.paretoBits.length =
          data.codeBound := by

  rcases hInput with
    ⟨data, hDecode⟩

  have hWellFormed :
      data.WellFormed :=
    CorrectedConcreteEncodedObservationSelectionData.wellFormed_of_decode_eq_some
      hDecode

  exact
    ⟨data,
      hDecode,
      hWellFormed.1,
      hWellFormed.2⟩

/-- Successful table decoding determines the complete payload length. -/
theorem payload_length_eq_of_hasDecodedFeasibilityTable
    {input :
      CorrectedConcreteObservationSelectionMaterializedTableInput}
    (hInput :
      input.HasDecodedFeasibilityTable) :
    ∃ data : CorrectedConcreteEncodedObservationSelectionData,
      CorrectedConcreteEncodedObservationSelectionData.decode
            input.payload =
          some data ∧
        input.payload.length =
          2 + (data.codeBound + data.codeBound) := by

  rcases hInput with
    ⟨data, hDecode⟩

  exact
    ⟨data,
      hDecode,
      CorrectedConcreteEncodedObservationSelectionData.input_length_eq_of_decode_eq_some
        hDecode⟩

/-- Complete materialized-table boundary package. -/
theorem materializedTableInput_package
    (input :
      CorrectedConcreteObservationSelectionMaterializedTableInput) :
    (input ∈ costLanguage →
      input.HasDecodedFeasibilityTable) ∧
      (input ∈ paretoLanguage →
        input.HasDecodedFeasibilityTable) ∧
      (input.HasDecodedFeasibilityTable →
        ∃ data : CorrectedConcreteEncodedObservationSelectionData,
          CorrectedConcreteEncodedObservationSelectionData.decode
                input.payload =
              some data ∧
            data.costBits.length =
              data.codeBound ∧
            data.paretoBits.length =
              data.codeBound ∧
            input.payload.length =
              2 + (data.codeBound + data.codeBound)) := by

  constructor

  · exact
      hasDecodedFeasibilityTable_of_mem_costLanguage

  · constructor

    · exact
        hasDecodedFeasibilityTable_of_mem_paretoLanguage

    · intro hDecoded

      rcases
          decodedFeasibilityTable_exact_lengths
            hDecoded with
        ⟨data, hDecode, hCostLength, hParetoLength⟩

      exact
        ⟨data,
          hDecode,
          hCostLength,
          hParetoLength,
          CorrectedConcreteEncodedObservationSelectionData.input_length_eq_of_decode_eq_some
            hDecode⟩

end MaterializedTableLanguages

end CorrectedConcreteObservationSelectionMaterializedTableInput


/-- Semantic boundary between a future compact problem and a materialized
truth-table problem.

`Materializes compact table` may initially be semantic/noncomputable.  The
separate deterministic and polynomial records below state the stronger
construction obligations. -/
structure CorrectedConcreteObservationSelectionSemanticOracleBoundary
    (compactLanguage :
      Set CorrectedConcreteObservationSelectionCompactInput)
    (tableLanguage :
      Set CorrectedConcreteObservationSelectionMaterializedTableInput) where

  Materializes :
    CorrectedConcreteObservationSelectionCompactInput →
      CorrectedConcreteObservationSelectionMaterializedTableInput →
        Prop

  total :
    ∀ compact :
        CorrectedConcreteObservationSelectionCompactInput,
      ∃ table :
          CorrectedConcreteObservationSelectionMaterializedTableInput,
        Materializes compact table

  functional :
    ∀ compact :
        CorrectedConcreteObservationSelectionCompactInput,
      ∀ first second :
          CorrectedConcreteObservationSelectionMaterializedTableInput,
        Materializes compact first →
          Materializes compact second →
            first = second

  membership_iff :
    ∀ compact :
        CorrectedConcreteObservationSelectionCompactInput,
      ∀ table :
          CorrectedConcreteObservationSelectionMaterializedTableInput,
        Materializes compact table →
          (compact ∈ compactLanguage ↔
            table ∈ tableLanguage)


namespace CorrectedConcreteObservationSelectionSemanticOracleBoundary

section GenericBoundary

variable
  {compactLanguage :
    Set CorrectedConcreteObservationSelectionCompactInput}
variable
  {tableLanguage :
    Set CorrectedConcreteObservationSelectionMaterializedTableInput}
variable
  (boundary :
    CorrectedConcreteObservationSelectionSemanticOracleBoundary
      compactLanguage
      tableLanguage)

/-- Compact-language membership is exactly the existence of an accepted
materialized table related by the boundary. -/
theorem mem_compactLanguage_iff_exists_materialized
    (compact :
      CorrectedConcreteObservationSelectionCompactInput) :
    compact ∈ compactLanguage ↔
      ∃ table :
          CorrectedConcreteObservationSelectionMaterializedTableInput,
        boundary.Materializes compact table ∧
          table ∈ tableLanguage := by

  constructor

  · intro hCompact

    rcases boundary.total compact with
      ⟨table, hMaterializes⟩

    exact
      ⟨table,
        hMaterializes,
        (boundary.membership_iff
          compact
          table
          hMaterializes).mp
          hCompact⟩

  · rintro ⟨table, hMaterializes, hTable⟩

    exact
      (boundary.membership_iff
        compact
        table
        hMaterializes).mpr
        hTable

/-- A materialized table associated with one compact input is unique. -/
theorem materialized_unique
    {compact :
      CorrectedConcreteObservationSelectionCompactInput}
    {first second :
      CorrectedConcreteObservationSelectionMaterializedTableInput}
    (hFirst :
      boundary.Materializes compact first)
    (hSecond :
      boundary.Materializes compact second) :
    first = second := by

  exact
    boundary.functional
      compact
      first
      second
      hFirst
      hSecond

/-- Rejection of the compact input is equivalent to rejection of every related
materialized table. -/
theorem not_mem_compactLanguage_iff_all_materialized_rejected
    (compact :
      CorrectedConcreteObservationSelectionCompactInput) :
    compact ∉ compactLanguage ↔
      ∀ table :
          CorrectedConcreteObservationSelectionMaterializedTableInput,
        boundary.Materializes compact table →
          table ∉ tableLanguage := by

  constructor

  · intro hCompact table hMaterializes hTable

    exact
      hCompact
        ((boundary.membership_iff
          compact
          table
          hMaterializes).mpr
          hTable)

  · intro hAll hCompact

    rcases boundary.total compact with
      ⟨table, hMaterializes⟩

    have hTable :
        table ∈ tableLanguage :=
      (boundary.membership_iff
        compact
        table
        hMaterializes).mp
        hCompact

    exact
      hAll
        table
        hMaterializes
        hTable

end GenericBoundary

end CorrectedConcreteObservationSelectionSemanticOracleBoundary


/-- Deterministic realization of a semantic oracle boundary. -/
structure CorrectedConcreteObservationSelectionSemanticOracleMaterializer
    (compactLanguage :
      Set CorrectedConcreteObservationSelectionCompactInput)
    (tableLanguage :
      Set CorrectedConcreteObservationSelectionMaterializedTableInput) where

  boundary :
    CorrectedConcreteObservationSelectionSemanticOracleBoundary
      compactLanguage
      tableLanguage

  materialize :
    CorrectedConcreteObservationSelectionCompactInput →
      CorrectedConcreteObservationSelectionMaterializedTableInput

  materialize_spec :
    ∀ compact :
        CorrectedConcreteObservationSelectionCompactInput,
      boundary.Materializes compact
        (materialize compact)


namespace CorrectedConcreteObservationSelectionSemanticOracleMaterializer

section GenericMaterializer

variable
  {compactLanguage :
    Set CorrectedConcreteObservationSelectionCompactInput}
variable
  {tableLanguage :
    Set CorrectedConcreteObservationSelectionMaterializedTableInput}
variable
  (materializer :
    CorrectedConcreteObservationSelectionSemanticOracleMaterializer
      compactLanguage
      tableLanguage)

/-- A deterministic materializer reduces compact membership exactly to
membership of its produced table. -/
theorem mem_compactLanguage_iff_materialize_mem
    (compact :
      CorrectedConcreteObservationSelectionCompactInput) :
    compact ∈ compactLanguage ↔
      materializer.materialize compact ∈
        tableLanguage := by

  exact
    materializer.boundary.membership_iff
      compact
      (materializer.materialize compact)
      (materializer.materialize_spec compact)

/-- The deterministic output is the unique table permitted by the boundary. -/
theorem materialize_eq_of_relation
    {compact :
      CorrectedConcreteObservationSelectionCompactInput}
    {table :
      CorrectedConcreteObservationSelectionMaterializedTableInput}
    (hTable :
      materializer.boundary.Materializes compact table) :
    materializer.materialize compact = table := by

  exact
    materializer.boundary.functional
      compact
      (materializer.materialize compact)
      table
      (materializer.materialize_spec compact)
      hTable

end GenericMaterializer

end CorrectedConcreteObservationSelectionSemanticOracleMaterializer


/-- Polynomial construction obligation for crossing from compact input to the
materialized table input.

This record is deliberately stronger than the semantic boundary.  In
particular, it bounds the complete output table length by a polynomial in the
compact payload length.  A genuine compact construction may fail this
obligation if it must explicitly emit `2 ^ U.card` bits; in that case the
correct route is a direct compact verifier rather than table materialization. -/
structure CorrectedConcreteObservationSelectionPolynomialSemanticOracleMaterializer
    (compactLanguage :
      Set CorrectedConcreteObservationSelectionCompactInput)
    (tableLanguage :
      Set CorrectedConcreteObservationSelectionMaterializedTableInput) where

  materializer :
    CorrectedConcreteObservationSelectionSemanticOracleMaterializer
      compactLanguage
      tableLanguage

  work :
    CorrectedConcreteObservationSelectionCompactInput →
      Nat

  outputCoefficient : Nat

  outputDegree : Nat

  workCoefficient : Nat

  workDegree : Nat

  outputSize_le :
    ∀ compact :
        CorrectedConcreteObservationSelectionCompactInput,
      (materializer.materialize compact).payload.length + 1 <=
        outputCoefficient *
          (compact.payload.length + 1) ^
            outputDegree

  work_le :
    ∀ compact :
        CorrectedConcreteObservationSelectionCompactInput,
      work compact <=
        workCoefficient *
          (compact.payload.length + 1) ^
            workDegree


namespace CorrectedConcreteObservationSelectionPolynomialSemanticOracleMaterializer

section GenericPolynomialMaterializer

variable
  {compactLanguage :
    Set CorrectedConcreteObservationSelectionCompactInput}
variable
  {tableLanguage :
    Set CorrectedConcreteObservationSelectionMaterializedTableInput}
variable
  (materializer :
    CorrectedConcreteObservationSelectionPolynomialSemanticOracleMaterializer
      compactLanguage
      tableLanguage)

/-- Complete logical and resource package for one compact input. -/
theorem package
    (compact :
      CorrectedConcreteObservationSelectionCompactInput) :
    (compact ∈ compactLanguage ↔
      materializer.materializer.materialize compact ∈
        tableLanguage) ∧
      (materializer.materializer.materialize compact).payload.length + 1 <=
        materializer.outputCoefficient *
          (compact.payload.length + 1) ^
            materializer.outputDegree ∧
      materializer.work compact <=
        materializer.workCoefficient *
          (compact.payload.length + 1) ^
            materializer.workDegree := by

  exact
    ⟨materializer.materializer.mem_compactLanguage_iff_materialize_mem
      compact,
      materializer.outputSize_le compact,
      materializer.work_le compact⟩

end GenericPolynomialMaterializer

end CorrectedConcreteObservationSelectionPolynomialSemanticOracleMaterializer


namespace CorrectedConcreteObservationSelectionCompactInput

section PayloadIdentityReferenceBoundary

/-- Reference “compact view” of the ordinary table language.

This is intentionally not claimed to be a genuine compact representation: its
payload is the complete table payload. -/
def tablePayloadCostViewLanguage :
    Set CorrectedConcreteObservationSelectionCompactInput :=
  {compact |
    compact.payload ∈
      CorrectedConcreteEncodedObservationSelectionData.serializedCostNPStyleLanguage}

/-- Reference “compact view” of the Pareto table language. -/
def tablePayloadParetoViewLanguage :
    Set CorrectedConcreteObservationSelectionCompactInput :=
  {compact |
    compact.payload ∈
      CorrectedConcreteEncodedObservationSelectionData.serializedParetoNPStyleLanguage}

/-- Payload-identity boundary for the ordinary table language. -/
def tablePayloadCostViewBoundary :
    CorrectedConcreteObservationSelectionSemanticOracleBoundary
      tablePayloadCostViewLanguage
      CorrectedConcreteObservationSelectionMaterializedTableInput.costLanguage :=
  {
    Materializes :=
      fun compact table =>
        table.payload = compact.payload

    total := by
      intro compact

      exact
        ⟨⟨compact.payload⟩, rfl⟩

    functional := by
      intro compact first second hFirst hSecond

      cases first with
      | mk firstPayload =>
          cases second with
          | mk secondPayload =>
              simp only at hFirst hSecond
              subst firstPayload
              subst secondPayload
              rfl

    membership_iff := by
      intro compact table hPayload

      change
        compact.payload ∈
            CorrectedConcreteEncodedObservationSelectionData.serializedCostNPStyleLanguage ↔
          table.payload ∈
            CorrectedConcreteEncodedObservationSelectionData.serializedCostNPStyleLanguage

      rw [hPayload]
  }

/-- Payload-identity boundary for the Pareto table language. -/
def tablePayloadParetoViewBoundary :
    CorrectedConcreteObservationSelectionSemanticOracleBoundary
      tablePayloadParetoViewLanguage
      CorrectedConcreteObservationSelectionMaterializedTableInput.paretoLanguage :=
  {
    Materializes :=
      fun compact table =>
        table.payload = compact.payload

    total := by
      intro compact

      exact
        ⟨⟨compact.payload⟩, rfl⟩

    functional := by
      intro compact first second hFirst hSecond

      cases first with
      | mk firstPayload =>
          cases second with
          | mk secondPayload =>
              simp only at hFirst hSecond
              subst firstPayload
              subst secondPayload
              rfl

    membership_iff := by
      intro compact table hPayload

      change
        compact.payload ∈
            CorrectedConcreteEncodedObservationSelectionData.serializedParetoNPStyleLanguage ↔
          table.payload ∈
            CorrectedConcreteEncodedObservationSelectionData.serializedParetoNPStyleLanguage

      rw [hPayload]
  }

/-- Deterministic payload-identity ordinary materializer. -/
def tablePayloadCostViewMaterializer :
    CorrectedConcreteObservationSelectionSemanticOracleMaterializer
      tablePayloadCostViewLanguage
      CorrectedConcreteObservationSelectionMaterializedTableInput.costLanguage :=
  {
    boundary :=
      tablePayloadCostViewBoundary

    materialize :=
      fun compact =>
        ⟨compact.payload⟩

    materialize_spec := by
      intro compact

      rfl
  }

/-- Deterministic payload-identity Pareto materializer. -/
def tablePayloadParetoViewMaterializer :
    CorrectedConcreteObservationSelectionSemanticOracleMaterializer
      tablePayloadParetoViewLanguage
      CorrectedConcreteObservationSelectionMaterializedTableInput.paretoLanguage :=
  {
    boundary :=
      tablePayloadParetoViewBoundary

    materialize :=
      fun compact =>
        ⟨compact.payload⟩

    materialize_spec := by
      intro compact

      rfl
  }

/-- Linear reference polynomial materializer for the ordinary payload view. -/
def tablePayloadCostViewPolynomialMaterializer :
    CorrectedConcreteObservationSelectionPolynomialSemanticOracleMaterializer
      tablePayloadCostViewLanguage
      CorrectedConcreteObservationSelectionMaterializedTableInput.costLanguage :=
  {
    materializer :=
      tablePayloadCostViewMaterializer

    work :=
      fun compact =>
        compact.payload.length + 1

    outputCoefficient := 1

    outputDegree := 1

    workCoefficient := 1

    workDegree := 1

    outputSize_le := by
      intro compact

      change
        compact.payload.length + 1 <=
          1 * (compact.payload.length + 1) ^ 1

      simp

    work_le := by
      intro compact

      change
        compact.payload.length + 1 <=
          1 * (compact.payload.length + 1) ^ 1

      simp
  }

/-- Linear reference polynomial materializer for the Pareto payload view. -/
def tablePayloadParetoViewPolynomialMaterializer :
    CorrectedConcreteObservationSelectionPolynomialSemanticOracleMaterializer
      tablePayloadParetoViewLanguage
      CorrectedConcreteObservationSelectionMaterializedTableInput.paretoLanguage :=
  {
    materializer :=
      tablePayloadParetoViewMaterializer

    work :=
      fun compact =>
        compact.payload.length + 1

    outputCoefficient := 1

    outputDegree := 1

    workCoefficient := 1

    workDegree := 1

    outputSize_le := by
      intro compact

      change
        compact.payload.length + 1 <=
          1 * (compact.payload.length + 1) ^ 1

      simp

    work_le := by
      intro compact

      change
        compact.payload.length + 1 <=
          1 * (compact.payload.length + 1) ^ 1

      simp
  }

/-- Reference-boundary package.

This proves only that the boundary API is inhabited when the “compact” payload
is already the table payload. -/
theorem tablePayloadViewBoundary_package
    (compact :
      CorrectedConcreteObservationSelectionCompactInput) :
    (compact ∈ tablePayloadCostViewLanguage ↔
      (tablePayloadCostViewMaterializer.materialize compact) ∈
        CorrectedConcreteObservationSelectionMaterializedTableInput.costLanguage) ∧
      (compact ∈ tablePayloadParetoViewLanguage ↔
        (tablePayloadParetoViewMaterializer.materialize compact) ∈
          CorrectedConcreteObservationSelectionMaterializedTableInput.paretoLanguage) ∧
      (tablePayloadCostViewMaterializer.materialize compact).payload =
        compact.payload ∧
      (tablePayloadParetoViewMaterializer.materialize compact).payload =
        compact.payload := by

  exact
    ⟨tablePayloadCostViewMaterializer.mem_compactLanguage_iff_materialize_mem
      compact,
      tablePayloadParetoViewMaterializer.mem_compactLanguage_iff_materialize_mem
        compact,
      rfl,
      rfl⟩

end PayloadIdentityReferenceBoundary

end CorrectedConcreteObservationSelectionCompactInput


section EncodedSemanticOracleBoundaryFinalPackage

variable {α : Type u}
variable {ι : Type v}
variable {M : Type w}
variable [DecidableEq ι]
variable [Monoid M]
variable (obsFamily : ι → α → M)
variable (f : Nat)
variable (coordinateWeight : ι → Nat)
variable (U : Finset ι)

/-- Final theorem recording the exact scope of the current serialized
complexity result.

The accepted input below is explicitly wrapped as a materialized table input.
The theorem does not construct a genuine compact grammar-level input or a
compact feasibility verifier. -/
theorem
    correctedConcreteWorkingGrammar_observationSelectionEncodedSemanticOracleBoundary_package
    (language : Set (Word α))
    (hTarget :
      language ∈
        StartRootedCorrectedConcreteTargetClass
          (v := z)
          α
          (↥U → M)
          (selectedObservationProduct obsFamily U)
          f) :
    let table :=
      correctedConcreteObservationSelectionSemanticDecisionTable
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
    let minimumRank :=
      table.serializedNPStyleMinimumRank hTarget
    let instance :=
      table.encodedObservationSelectionInstance minimumRank
    let tableInput :
        CorrectedConcreteObservationSelectionMaterializedTableInput :=
      ⟨instance.serialize⟩
    let problem :=
      CorrectedConcreteEncodedObservationSelectionData.serializedParetoPolynomialWitnessDecisionProblem
    let semantics :=
      CorrectedConcreteEncodedObservationSelectionData.serializedParetoStandardMachineSemantics
    let realization :=
      CorrectedConcreteEncodedObservationSelectionData.serializedParetoStandardMachineRealization
    let npLanguage :=
      CorrectedConcreteEncodedObservationSelectionData.serializedParetoNPStyleLanguage
    let maxBudget :=
      correctedConcreteObservationSelectionPositiveAdditiveCost
        coordinateWeight
        U
    let hBound :
        minimumRank <= maxBudget :=
      ambientTargetObservationSelectionPositiveAdditiveMinimumCost_le
        (z := z)
        obsFamily
        f
        coordinateWeight
        U
        hTarget
    let hAccepted :=
      table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
        hTarget
        maxBudget
        hBound
    let canonicalCode :=
      table.selectedCanonicalDenseMinimumParetoScalarCode
        maxBudget
        hAccepted
    CorrectedConcreteSerializedStandardMachineNPStyleLanguage
        npLanguage ∧
      tableInput ∈
        CorrectedConcreteObservationSelectionMaterializedTableInput.paretoLanguage ∧
      tableInput.HasDecodedFeasibilityTable ∧
      tableInput.payload.length =
        2 + (2 ^ U.card + 2 ^ U.card) ∧
      semantics.Accepts
          realization.program
          tableInput.payload
          canonicalCode ∧
      (∀ competingCode : Nat,
        semantics.Accepts
              realization.program
              tableInput.payload
              competingCode →
          canonicalCode <= competingCode) ∧
      semantics.certificateLength canonicalCode <=
        problem.certificateCoefficient *
          semantics.inputLength tableInput.payload ^
            problem.certificateDegree ∧
      semantics.steps
            realization.program
            tableInput.payload
            canonicalCode <=
        problem.verifierCoefficient *
          semantics.inputLength tableInput.payload ^
            problem.verifierDegree ∧
      canonicalCode < 2 ^ U.card ∧
      correctedConcreteDenseCertificateDecode
            U
            canonicalCode =
        some
          (table.canonicalMinimumParetoScalarCertificate
            (correctedConcreteDenseCertificateCode U)
            maxBudget
            hAccepted) ∧
      CorrectedConcreteObservationSelectionParetoOptimal
        (z := z)
        obsFamily
        f
        (correctedConcreteObservationSelectionAdditiveCost
          coordinateWeight)
        U
        language
        (table.canonicalMinimumParetoScalarCertificate
          (correctedConcreteDenseCertificateCode U)
          maxBudget
          hAccepted) := by

  let table :=
    correctedConcreteObservationSelectionSemanticDecisionTable
      (z := z)
      obsFamily
      f
      (correctedConcreteObservationSelectionAdditiveCost
        coordinateWeight)
      U
      language

  let minimumRank :=
    table.serializedNPStyleMinimumRank hTarget

  let instance :=
    table.encodedObservationSelectionInstance minimumRank

  let tableInput :
      CorrectedConcreteObservationSelectionMaterializedTableInput :=
    ⟨instance.serialize⟩

  let problem :=
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoPolynomialWitnessDecisionProblem

  let semantics :=
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoStandardMachineSemantics

  let realization :=
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoStandardMachineRealization

  let npLanguage :=
    CorrectedConcreteEncodedObservationSelectionData.serializedParetoNPStyleLanguage

  let maxBudget :=
    correctedConcreteObservationSelectionPositiveAdditiveCost
      coordinateWeight
      U

  let hBound :
      minimumRank <= maxBudget :=
    ambientTargetObservationSelectionPositiveAdditiveMinimumCost_le
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      hTarget

  let hAccepted :=
    table.hasAcceptedParetoScalarBudgetUpTo_of_positiveAdditiveMinimum_le
      hTarget
      maxBudget
      hBound

  let canonicalCode :=
    table.selectedCanonicalDenseMinimumParetoScalarCode
      maxBudget
      hAccepted

  have hPrevious :=
    correctedConcreteWorkingGrammar_observationSelectionEncodedSerializedStandardMachineRealization_package
      (z := z)
      obsFamily
      f
      coordinateWeight
      U
      language
      hTarget

  rcases hPrevious with
    ⟨hClass,
      hInput,
      hMachineAccepts,
      hLeast,
      hCertificateLength,
      hSteps,
      hCertificateCoefficient,
      hCertificateDegree,
      hVerifierCoefficient,
      hVerifierDegree,
      hCodeBound,
      hDecode,
      hPareto⟩

  have hTableInput :
      tableInput ∈
        CorrectedConcreteObservationSelectionMaterializedTableInput.paretoLanguage :=
    hInput

  have hHasDecoded :
      tableInput.HasDecodedFeasibilityTable :=
    ⟨instance.toSerializedData,
      instance.decode_serialize⟩

  have hPayloadLength :
      tableInput.payload.length =
        2 + (2 ^ U.card + 2 ^ U.card) := by

    change
      instance.serialize.length =
        2 + (2 ^ U.card + 2 ^ U.card)

    simpa [instance.codeBound_correct] using
      instance.serialize_length

  exact
    ⟨hClass,
      hTableInput,
      hHasDecoded,
      hPayloadLength,
      hMachineAccepts,
      hLeast,
      hCertificateLength,
      hSteps,
      hCodeBound,
      hDecode,
      hPareto⟩

end EncodedSemanticOracleBoundaryFinalPackage

end MCFG
