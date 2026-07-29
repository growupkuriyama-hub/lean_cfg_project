from __future__ import annotations

from adaptive_h_mcfg.v12_baselines import CheckoutCountPhaseInvariantModel, KTailsAutomatonModel
from adaptive_h_mcfg.v12_protocol import ProjectionRow, audit_word_disjoint_protocol, parse_int_spec

MUTATIONS = (
    "currency-server-phase-inversion",
    "drop-product-server-occurrence",
    "duplicate-product-server-occurrence",
    "drop-product-currency-server-occurrence",
    "duplicate-product-currency-server-occurrence",
    "duplicate-shipping-currency-server-occurrence",
)


def normal_word(n: int) -> str:
    return f"{'p' * n}#{'c' * n}s#{'pc' * n}s"


def mutant_word(n: int, mutation: str) -> str:
    p = "p" * n
    c = "c" * n + "s"
    schedule = "pc" * n + "s"
    if mutation == "currency-server-phase-inversion":
        return f"{p}#{c[:-2]}sc#{schedule}"
    if mutation == "drop-product-server-occurrence":
        return f"{p[:-1]}#{c}#{schedule}"
    if mutation == "duplicate-product-server-occurrence":
        return f"{p}p#{c}#{schedule}"
    if mutation == "drop-product-currency-server-occurrence":
        index = c.rfind("c")
        return f"{p}#{c[:index]}{c[index + 1:]}#{schedule}"
    if mutation == "duplicate-product-currency-server-occurrence":
        index = c.rfind("s")
        return f"{p}#{c[:index]}c{c[index:]}#{schedule}"
    if mutation == "duplicate-shipping-currency-server-occurrence":
        return f"{p}#{c}s#{schedule}"
    raise AssertionError(mutation)


def synthetic_rows(replicas: int = 2) -> list[ProjectionRow]:
    rows: list[ProjectionRow] = []
    for n in range(1, 11):
        role = "train" if n <= 2 else "validation" if n == 3 else "test"
        for replica in range(replicas):
            run_id = f"run-c{n:02d}-r{replica:02d}"
            source_trace_id = f"trace-c{n:02d}-r{replica:02d}"
            rows.append(ProjectionRow(
                source=f"{run_id}.json", run_id=run_id,
                source_trace_id=source_trace_id, trace_id=source_trace_id,
                label="normal", item_count=n, word=normal_word(n), mutation="none",
                route_preserving=True, description="", split_role=role, replica=replica,
            ))
            # Deletions are not route-preserving at n=1 and are intentionally absent.
            available = MUTATIONS if n >= 2 else tuple(m for m in MUTATIONS if not m.startswith("drop-"))
            for mutation in available:
                rows.append(ProjectionRow(
                    source=f"{run_id}.json", run_id=run_id,
                    source_trace_id=source_trace_id,
                    trace_id=f"{source_trace_id}-{mutation}", label="anomaly",
                    item_count=n, word=mutant_word(n, mutation), mutation=mutation,
                    route_preserving=True, description="", split_role=role, replica=replica,
                ))
    return rows


def test_parse_int_spec() -> None:
    assert parse_int_spec("1,3-5,5") == (1, 3, 4, 5)


def test_protocol_accepts_disjoint_count_holdout() -> None:
    report = audit_word_disjoint_protocol(
        synthetic_rows(), (1, 2), (3,), tuple(range(4, 11)),
        "currency-server-phase-inversion", MUTATIONS, minimum_replicas_per_count=2,
    )
    assert report["ready_for_word_disjoint_evaluation"]
    assert report["unique_normal_words"] == 10
    assert report["unique_words_total"] == 68


def test_protocol_rejects_projection_overlap() -> None:
    rows = synthetic_rows()
    bad = rows[-1]
    rows[-1] = ProjectionRow(**{**bad.__dict__, "word": normal_word(1)})
    report = audit_word_disjoint_protocol(
        rows, (1, 2), (3,), tuple(range(4, 11)),
        "currency-server-phase-inversion", MUTATIONS, minimum_replicas_per_count=2,
    )
    assert not report["ready_for_word_disjoint_evaluation"]
    assert "projected words overlap across train/validation/test" in report["errors"]


def test_direct_invariant_baseline() -> None:
    model = CheckoutCountPhaseInvariantModel.fit((normal_word(1), normal_word(2)))
    assert model.accepts(normal_word(8))
    for mutation in MUTATIONS:
        assert not model.accepts(mutant_word(4, mutation))


def test_k_tails_accepts_training_words() -> None:
    model = KTailsAutomatonModel.fit((normal_word(1), normal_word(2)), k=2)
    assert model.accepts(normal_word(1))
    assert model.accepts(normal_word(2))
    assert model.state_count > 0
