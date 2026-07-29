# V11 limitations and claim boundary

## What V11 implements

- A fan-out-3, trace-specialized, binary-witness learner over a structural
  occurrence basis.
- Explicit finite observers and their direct products.
- Mutation-guided greedy observer selection.
- OpenTelemetry Jaeger collection, explicit CLIENT/SERVER pairing, run-disjoint
  evaluation, and six offline server-side mutation families.

## What V11 does not implement

- A general-purpose MCFG parser.
- Every named interval and empty-component occurrence from the theoretical
  canonical learner.
- Online adaptation while the application is running.
- Root-cause localization beyond the mutated projection block.
- A claim that an arbitrary unknown finite monoid can be recovered.
- A claim that official OpenTelemetry Demo traces have already produced the
  controlled V11 result.

## Controlled versus real-trace evidence

The included numerical results use deterministic Jaeger-format traces generated
from the same CLIENT/SERVER structure expected from Checkout. They validate the
pipeline and the mathematical trade-off. They must be called a controlled
trace-derived benchmark, not an empirical result on the official Demo.

The official-Demo experiment will collect only normal traces. Mutants are made
offline, so service nodes, source commit, and normal telemetry are authentic,
while the anomaly label is controlled. This design tests structural detection;
it does not estimate the prevalence of these anomalies in real deployments.

## Potential threats

- The current projection assumes the Checkout workflow exposes Product Catalog
  and Currency CLIENT/SERVER pairs with explicit parent links.
- Load-generator traffic may not cover cart sizes 1 and 2 in every run.
- The selected modular observer may be specific to this projection.
- Multiple traces with the same cart size map to one word, so trace-level sample
  counts do not create additional language evidence.
- Offline timestamp/order mutations may not reproduce all runtime scheduling
  artefacts.
- Greedy selection can miss interacting observer subsets.

## Required reporting discipline

Report route-preserving fault performance separately from route mismatch.
Report seen-size and unseen-size normals and faults separately. Record skipped
traces and the reasons for skipping them. Never use mutation labels or
`mcfg.*` audit attributes as grammar tokens.
