# V11 progress report

## Status

V11 converts the V10 proof-of-concept into a reproducible **run-disjoint
OpenTelemetry Demo experiment**.  It does not claim that official Demo traces
have already been collected in this environment; Docker is unavailable here.
The deterministic Jaeger fixture exercises the same collection, projection,
mutation, split, selection, and evaluation code paths.

## Main changes

1. **No application patching.** The official Demo is started unchanged.
2. **Current Demo startup support.** `compose.yaml` is preferred; the legacy
   name is accepted only as a fallback. Full and minimal modes are supported.
3. **Jaeger service discovery.** The collector queries `/api/services` and
   resolves current names such as `checkout-service` instead of hard-coding one
   spelling.
4. **Run-labelled dataset.** Every projection and mutant retains `run_id` and
   source trace ID.
5. **Strict run-disjoint splits.** Training, observer selection, and testing use
   disjoint run sets for every seed.
6. **Six route-preserving mutation families.** The Checkout caller schedule is
   retained while downstream server order or occurrence counts are changed.
7. **Seen-size versus unseen-size reporting.** This separates anomaly rejection
   from failure to extrapolate to a new cart size.
8. **Five-seed aggregation.** The package writes seed-level metrics, mean,
   standard deviation, minimum, maximum, and model-complexity tables.
9. **One-command runner.** Collection, dataset building, validation, and
   evaluation can be launched by `run_v11_end_to_end.py`.

## Projection

For a Checkout trace with `n` product items, the three synchronized components
are

\[
  p^n \# c^n s \# (pc)^n s.
\]

The blocks encode Product Catalog SERVER occurrences, Currency SERVER order,
and the Checkout CLIENT call schedule.  CLIENT-to-SERVER pairing is accepted
only when explicit parent span IDs are present; missing links are not guessed.

## Mutation families

All mutations keep the caller schedule block unchanged.

- Currency server phase inversion.
- Product server occurrence deletion.
- Product server occurrence duplication.
- Product-price Currency server occurrence deletion.
- Product-price Currency server occurrence duplication.
- Shipping Currency server occurrence duplication.

For deletion, another occurrence of the same service edge must remain, so the
coarse service graph is unchanged.

## Deterministic run-disjoint fixture

The fixture contains seven independent Jaeger run exports. Every run contains
cart sizes 1, 2, and 3; subsets also contain sizes 4 and 5. The learner uses
normal sizes 1 and 2 as positive anchors. Observer selection sees the smallest
unseen normal size and one seen-size phase inversion.

Across five run-split seeds, the selector chose exactly

```text
shipping-phase-count-mod-2
```

in every seed.

### Key trade-off

| Model | Unseen-normal acceptance | Seen-size phase recall | All-mutation recall |
|---|---:|---:|---:|
| Adaptive fan-out-3 MCFG | 1.000 | 1.000 | 1.000 |
| Trivial-observation fan-out-3 MCFG | 1.000 | 0.500 | 0.953 |
| Full-product fan-out-3 MCFG | 0.000 | 1.000 | 1.000 |
| Exact template | 0.000 | 1.000 | 1.000 |
| 2-gram | 0.547 | 1.000 | 0.439 |
| 3-gram | 0.547 | 1.000 | 0.439 |

The adaptive grammar had 22 unit rules and 9 observed types.  The trivial model
had 62 unit rules and 3 types; the full product had only 2 unit rules but 93
types and lost all unseen-size normal acceptance.

## Interpretation

The controlled result exhibits the intended three-way distinction:

- a coarse observation preserves extrapolation but permits a phase-confused
  substitution;
- the complete observer product blocks the mutation but fragments the positive
  structure so strongly that cart-size extrapolation disappears;
- sparse selection retains one finite observation and preserves both goals.

The result is not yet evidence about the frequency of these faults in production
systems. It validates the experimental mechanism that will be applied to
unmodified official Demo traces.

## Remaining decisive experiment

Run the official Demo for at least five independent collection windows and
execute the V11 one-command pipeline.  The paper proceeds only if:

1. normal projections with cart sizes 1 and 2 occur in at least three runs;
2. one or more test runs contain larger normal cart sizes;
3. the sparse observer is selected in a majority of seeds;
4. adaptive MCFG improves seen-size phase-fault recall over trivial observation;
5. adaptive MCFG retains higher unseen-size normal acceptance than the full
   product and exact-template baselines.

## Regression status

```text
6 passed in 3.95s
```
