# JALC Lean experiment closure package

This package corresponds to the six recommended experiment directions:

```text
FullKeptDecidabilityKernel.lean
AlgorithmicFiniteMainKernel.lean
ExecutableFullKeptExtraction.lean
DescriptorReconstructionKernel.lean
ContextClosureCoincidenceKernel.lean
ShortlexWitnessKernel.lean
```

It also adds:

```text
PaperFacingExperimentClosure.lean
```

## Intended interpretation

The first two modules use the CI #304 Algorithm 1 / FullKept agreement to move
the finite-main decidability boundary from `FullKept` to the computed kept
predicate of a certified Algorithm 1 run.

The third module isolates the exact payload that a later executable extraction
phase would need to produce.

The fourth module packages the full-kept kept-state structure as the current
descriptor-level output.

The fifth and sixth modules deliberately record context-closure coincidence and
shortlex witness normalization as future phases rather than opening another
large proof campaign now.

## Placement

Copy all `.lean` files into:

```text
LeanCfgProject/JALC/
```

## CI command

```yaml
      - name: Build JALC experiment closure target
        run: lake build LeanCfgProject.JALC.PaperFacingExperimentClosure
```

## Suggested commit message

```text
Add JALC experiment closure kernels
```
