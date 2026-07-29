# ADP MCFG v5 / internal V12 experiment protocol

## Purpose

V12 replaces the V11 random run-disjoint evaluation with a count-held-out,
projected-word-disjoint design.  The external workflow remains “ADP MCFG v5”;
“V12” is the next internal repository protocol number after V11.

## Fixed split

- Training item counts: 1 and 2.
- Validation item count: 3.
- Test item counts: 4 through 10.
- Default replication: five independently issued checkout transactions per item count.
- Exactly one canonical checkout projection must be recovered from every run.

The learner receives only the two unique normal training words.  Observer
selection uses the unique normal word at count 3 and the unique
`currency-server-phase-inversion` word at count 3.  No validation word may occur
in testing.

## Three-layer separation

The validator fails unless all three layers are disjoint across split roles:

1. count-controlled run IDs;
2. source Jaeger trace IDs;
3. projected words seen by the learner.

The third condition is the crucial correction to V11: different raw traces do
not count as different learning inputs after an intentionally lossy projection.

## Reporting units

Results are written twice:

- trace-instance-weighted metrics, which preserve repeated raw transactions;
- unique-projection-weighted metrics, which count each model-visible labeled
  projection once.

The manuscript should treat the unique-projection table as the primary
generalization result and the instance table as a stability/repetition result.

## Mutation coverage

The six V11 route-preserving offline mutation families are required at every
validation and test count.  Deletion mutations are not required at count 1,
because deleting the only occurrence would not preserve the service edge.

## Fail-closed conditions

Collection/build/evaluation stops when any of the following occurs:

- zero or multiple canonical traces match a controlled run;
- a required count or mutation family is missing;
- fewer than the requested replicas are recovered;
- run IDs, source trace IDs, or projected words overlap across roles;
- the validation diagnostic word reappears in test.
