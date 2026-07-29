# Adaptive finite-observation MCFG prototype — V11

V11 is the executable OpenTelemetry Demo experiment for sparse finite-observer
selection.  It leaves the application unchanged, collects normal Jaeger traces,
creates route-preserving offline span mutations, and evaluates all models with
strictly run-disjoint splits.

## One-command official-Demo experiment

Prerequisites are Docker, Docker Compose v2, Python 3.11+, and an official
OpenTelemetry Demo checkout.

```bash
python run_v11_end_to_end.py /path/to/opentelemetry-demo \
  --output /path/to/mcfg-v11-experiment \
  --runs 5 --seeds 5
```

For machines with limited memory:

```bash
python run_v11_end_to_end.py /path/to/opentelemetry-demo \
  --output /path/to/mcfg-v11-experiment \
  --runs 5 --seeds 5 --minimal
```

The runner performs:

1. unmodified Demo startup and five timestamp-bounded Jaeger collections;
2. run-labelled Checkout projection and six offline mutation families;
3. dataset coverage validation;
4. five strict run-disjoint evaluations;
5. seed and aggregate CSV/JSON output.

## Resume without recollecting

```bash
python run_v11_end_to_end.py /path/to/opentelemetry-demo \
  --output /path/to/mcfg-v11-experiment \
  --skip-collection --seeds 5
```

## Individual stages

```bash
python otel_demo/run_normal_v11.py /path/to/opentelemetry-demo \
  --output normal-runs --runs 5

python otel_demo/build_v11_dataset.py normal-runs --output dataset

python validate_v11_dataset.py dataset/projections.csv \
  --output dataset/validation_report.json

python run_real_multiseed_v11.py dataset/projections.csv \
  --output results --seeds 5
```

## Controlled regression result

The included seven-run Jaeger fixture produces the following five-seed mean
rates:

| Model | Unseen-normal acceptance | Seen-size phase recall | All-mutation recall |
|---|---:|---:|---:|
| Adaptive fan-out-3 MCFG | 1.000 | 1.000 | 1.000 |
| Trivial-observation fan-out-3 MCFG | 1.000 | 0.500 | 0.953 |
| Full-product fan-out-3 MCFG | 0.000 | 1.000 | 1.000 |
| Exact template | 0.000 | 1.000 | 1.000 |
| 2-gram | 0.547 | 1.000 | 0.439 |
| 3-gram | 0.547 | 1.000 | 0.439 |

The fixture is controlled trace-derived evidence, not an official-Demo result.

## Output files

- `dataset/projections.csv`: run-labelled normal and mutated projections.
- `dataset/validation_report.json`: cart-size and mutation coverage.
- `results/seed_metrics.csv`: trace-level metrics for every split seed.
- `results/aggregate_metrics.csv`: mean, SD, minimum, and maximum.
- `results/model_complexity.csv`: grammar complexity by seed.
- `results/summary.json`: complete split and selection provenance.

## Tests

```bash
python -m pytest -q
```

Expected:

```text
6 passed
```

## Scope

The learner is a fan-out-3, trace-specialized, structural-occurrence
approximation to the theoretical fixed-observation canonical learner.  It is not
a complete general-purpose MCFG parser.  See `V11_LIMITATIONS.md`.

## GitHub Actions (no local Docker required)

Upload this repository to GitHub and run the manually triggered workflow:

```text
.github/workflows/opentelemetry-v11.yml
```

See `GITHUB_ACTIONS_SETUP.md`.  The workflow starts the official Demo in minimal
mode, collects five independent runs, evaluates five seeds, and uploads all raw
traces and results as a workflow artifact.
