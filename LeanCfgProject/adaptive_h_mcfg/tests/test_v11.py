from __future__ import annotations

import json
from pathlib import Path

from adaptive_h_mcfg.otel_v10 import checkout_phase_projection, make_paired_checkout_trace
from adaptive_h_mcfg.otel_v11 import mutation_family_words, projection_mutations
from otel_demo.collect_jaeger_v11 import choose_service


def test_projection_mutation_families_preserve_caller_schedule() -> None:
    projection = checkout_phase_projection(make_paired_checkout_trace(2, "v11"))
    assert projection is not None
    normal_schedule = projection.word.split("#")[2]
    mutations = projection_mutations(projection)
    names = {mutation.name for mutation in mutations}
    assert "currency-server-phase-inversion" in names
    assert "drop-product-server-occurrence" in names
    assert "duplicate-shipping-currency-server-occurrence" in names
    assert all(mutation.word.split("#")[2] == normal_schedule for mutation in mutations)
    assert all(mutation.route_preserving for mutation in mutations)


def test_abstract_phase_mutation_is_the_v10_diagnostic_word() -> None:
    words = mutation_family_words(2)
    assert words["currency-server-phase-inversion"] == "pp#csc#pcpcs"


def test_jaeger_service_resolution_tolerates_current_service_naming() -> None:
    services = ["frontend", "checkout-service", "currency-service"]
    assert choose_service(services, "checkout") == "checkout-service"


def test_fixture_multiseed_result_selected_sparse_observer() -> None:
    summary_path = Path(__file__).resolve().parents[1] / "results" / "v11_fixture_summary.json"
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    selected = summary["selected_observers_by_seed"]
    assert len(selected) == 5
    assert all(value == ["shipping-phase-count-mod-2"] for value in selected.values())
