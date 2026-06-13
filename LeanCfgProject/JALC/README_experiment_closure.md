# JALC Lean experiment closure package, fixed

This package fixes the previous AlgorithmicFiniteMainKernel failure by making
the finite-main part a boundary package rather than rebuilding the existing
FullFiniteMainKernel record internally.

The key checked point is:

```text
DecidablePred (computedKept E)
+ fullAlgorithmicComputedKept_agrees tau G E
⇒ Nonempty (DecidablePred (FullKept tau G))
```

Thus the decidability boundary needed by the finite-main theorem package is
moved from abstract FullKept to the computed kept predicate of a certified
Algorithm 1 run.

## Placement

Copy the `.lean` files into:

```text
LeanCfgProject/JALC/
```

Use the fixed files to replace the previous versions:

```text
FullKeptDecidabilityKernel.lean
AlgorithmicFiniteMainKernel.lean
ExecutableFullKeptExtraction.lean
DescriptorReconstructionKernel.lean
ContextClosureCoincidenceKernel.lean
ShortlexWitnessKernel.lean
PaperFacingExperimentClosure.lean
```

## CI command

```yaml
      - name: Build JALC experiment closure target
        run: lake build LeanCfgProject.JALC.PaperFacingExperimentClosure
```

## Suggested commit message

```text
Fix JALC experiment closure boundary kernels
```
