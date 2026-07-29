# Next action: collect official OpenTelemetry Demo traces

## Windows / PowerShell

1. Install and start Docker Desktop.
2. Clone the official Demo:

```powershell
git clone https://github.com/open-telemetry/opentelemetry-demo.git
```

3. From the V11 package directory, run:

```powershell
.\run_v11_windows.ps1 `
  -DemoRoot "C:\path\to\opentelemetry-demo" `
  -Output "C:\path\to\mcfg-v11-experiment" `
  -Runs 5 -Seeds 5
```

Use `-Minimal` if the full Demo exceeds available memory.  The official minimal
mode removes several services but retains the checkout path used here.

## Expected stopping conditions

The dataset validator should report:

```json
"ready_for_default_5_seed_pilot": true
```

If false, do not interpret model performance.  Increase the number or length of
collection runs until at least five independent runs exist and cart sizes 1 and
2 occur in enough training candidates.

## Files to return to this conversation

ZIP the whole output folder, or at minimum include:

```text
mcfg-v11-experiment/
├── normal-runs/
│   ├── manifest.json
│   └── run-*.json
├── dataset/
│   ├── projections.csv
│   ├── dataset_summary.json
│   └── validation_report.json
└── results/
    ├── summary.json
    ├── seed_metrics.csv
    ├── aggregate_metrics.csv
    └── model_complexity.csv
```

The raw normal runs are important: they allow the projection and mutation code
to be audited independently of the result tables.
