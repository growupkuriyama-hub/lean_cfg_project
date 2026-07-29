# Run the OpenTelemetry V11 experiment on GitHub Actions

No local Docker installation is required.

## 1. Create a repository

1. On GitHub, create a new repository.
2. A **public repository is recommended** because its standard Ubuntu runner has
   more CPU/RAM and does not consume private-repository Actions minutes.
3. Upload all files from this package, including the hidden `.github` folder.

The workflow file must appear at:

```text
.github/workflows/opentelemetry-v11.yml
```

## 2. Start the experiment

1. Open the repository's **Actions** tab.
2. Choose **OpenTelemetry V11 experiment**.
3. Click **Run workflow**.
4. Keep the defaults for the first run:
   - runs: 5
   - seeds: 5
   - warmup_seconds: 45
   - collect_seconds: 90
   - demo_ref: main
5. Click the green **Run workflow** button.

The workflow uses the official OpenTelemetry Demo in minimal mode.  It records
its exact Git commit in the output.

## 3. Download the result

After the workflow completes:

1. Open the completed workflow run.
2. Scroll to **Artifacts**.
3. Download `mcfg-v11-experiment-<run id>`.
4. Upload that downloaded ZIP to the ChatGPT conversation.

The artifact contains raw normal Jaeger traces, projected/mutated data, five-seed
metrics, grammar complexity, the Demo commit, Docker logs, and runner diagnostics.

## If the first run fails

Download the artifact anyway.  The workflow uploads partial output and diagnostics
even after a failed step.  Upload that ZIP so the failure can be diagnosed.

A common reason is insufficient disk space while pulling Demo images.  The
workflow already removes unused Android, .NET, GHC, Boost, and CodeQL files before
starting.  If the standard runner is still insufficient, the next options are a
larger GitHub runner or a self-hosted runner.
