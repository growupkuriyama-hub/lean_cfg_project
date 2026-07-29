from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable, Mapping, Sequence


def _field(mapping: Mapping[str, Any], camel: str, snake: str | None = None, default: Any = None) -> Any:
    if camel in mapping:
        return mapping[camel]
    if snake is not None and snake in mapping:
        return mapping[snake]
    return default


def _otlp_any_value(value: Mapping[str, Any] | None) -> Any:
    if not value:
        return None
    aliases = (
        ("stringValue", "string_value"),
        ("boolValue", "bool_value"),
        ("intValue", "int_value"),
        ("doubleValue", "double_value"),
        ("bytesValue", "bytes_value"),
    )
    for camel, snake in aliases:
        if camel in value:
            return value[camel]
        if snake in value:
            return value[snake]
    array_value = _field(value, "arrayValue", "array_value")
    if array_value is not None:
        return [
            _otlp_any_value(item)
            for item in _field(array_value, "values", default=[])
        ]
    kvlist_value = _field(value, "kvlistValue", "kvlist_value")
    if kvlist_value is not None:
        return _otlp_attributes(_field(kvlist_value, "values", default=[]))
    return None


def _otlp_attributes(items: Iterable[Mapping[str, Any]] | None) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for item in items or ():
        key = str(_field(item, "key", default=""))
        if key:
            result[key] = _otlp_any_value(_field(item, "value", default={}))
    return result


@dataclass(frozen=True)
class SpanRecord:
    trace_id: str
    span_id: str
    parent_span_id: str
    service: str
    operation: str
    kind: str
    start_ns: int
    end_ns: int
    status: str
    attributes: tuple[tuple[str, Any], ...] = ()

    @property
    def duration_ns(self) -> int:
        return self.end_ns - self.start_ns


@dataclass(frozen=True)
class TraceRecord:
    trace_id: str
    spans: tuple[SpanRecord, ...]

    def services(self) -> tuple[str, ...]:
        return tuple(sorted({span.service for span in self.spans}))


_KIND_BY_NUMBER = {
    0: "UNSPECIFIED",
    1: "INTERNAL",
    2: "SERVER",
    3: "CLIENT",
    4: "PRODUCER",
    5: "CONSUMER",
}
_STATUS_BY_NUMBER = {0: "UNSET", 1: "OK", 2: "ERROR"}


def _normalize_enum(value: Any, numeric_map: Mapping[int, str], prefix: str) -> str:
    if value is None:
        return numeric_map.get(0, "UNSPECIFIED")
    if isinstance(value, str):
        try:
            return numeric_map[int(value)]
        except (ValueError, KeyError):
            return value.removeprefix(prefix)
    return numeric_map.get(int(value), str(value))


def parse_otlp_json(payload: Mapping[str, Any]) -> list[TraceRecord]:
    """Parse the OTLP/JSON trace envelope into normalized trace records.

    Both protobuf JSON lowerCamelCase and snake_case field spellings are
    accepted to make stored research datasets easier to ingest.
    """
    grouped: dict[str, list[SpanRecord]] = {}
    resource_spans = _field(payload, "resourceSpans", "resource_spans", [])
    for resource_group in resource_spans:
        resource = _field(resource_group, "resource", default={}) or {}
        resource_attributes = _otlp_attributes(_field(resource, "attributes", default=[]))
        service = str(resource_attributes.get("service.name", "unknown-service"))
        scope_spans = _field(resource_group, "scopeSpans", "scope_spans", [])
        for scope_group in scope_spans:
            for span in _field(scope_group, "spans", default=[]):
                trace_id = str(_field(span, "traceId", "trace_id", ""))
                span_id = str(_field(span, "spanId", "span_id", ""))
                parent_span_id = str(_field(span, "parentSpanId", "parent_span_id", ""))
                attributes = _otlp_attributes(_field(span, "attributes", default=[]))
                status_object = _field(span, "status", default={}) or {}
                status = _normalize_enum(
                    _field(status_object, "code", default=0),
                    _STATUS_BY_NUMBER,
                    "STATUS_CODE_",
                )
                record = SpanRecord(
                    trace_id=trace_id,
                    span_id=span_id,
                    parent_span_id=parent_span_id,
                    service=service,
                    operation=str(_field(span, "name", default="unknown-operation")),
                    kind=_normalize_enum(
                        _field(span, "kind", default=0),
                        _KIND_BY_NUMBER,
                        "SPAN_KIND_",
                    ),
                    start_ns=int(_field(span, "startTimeUnixNano", "start_time_unix_nano", 0)),
                    end_ns=int(_field(span, "endTimeUnixNano", "end_time_unix_nano", 0)),
                    status=status,
                    attributes=tuple(sorted(attributes.items())),
                )
                grouped.setdefault(trace_id, []).append(record)
    return _finalize_traces(grouped)


def _jaeger_tags(items: Iterable[Mapping[str, Any]] | None) -> dict[str, Any]:
    return {
        str(item.get("key", "")): item.get("value")
        for item in items or ()
        if item.get("key")
    }


def parse_jaeger_json(payload: Mapping[str, Any]) -> list[TraceRecord]:
    """Parse Jaeger Query API-style JSON into normalized trace records."""
    grouped: dict[str, list[SpanRecord]] = {}
    for trace in payload.get("data", []):
        processes = trace.get("processes", {})
        for span in trace.get("spans", []):
            trace_id = str(span.get("traceID", trace.get("traceID", "")))
            process = processes.get(span.get("processID", ""), {})
            service = str(process.get("serviceName", "unknown-service"))
            tags = _jaeger_tags(span.get("tags"))
            parent_span_id = ""
            for reference in span.get("references", []):
                if reference.get("refType") == "CHILD_OF":
                    parent_span_id = str(reference.get("spanID", ""))
                    break
            start_us = int(span.get("startTime", 0))
            duration_us = int(span.get("duration", 0))
            error_value = tags.get("error", False)
            status = "ERROR" if error_value in (True, "true", 1, "1") else "UNSET"
            kind = str(tags.get("span.kind", "UNSPECIFIED")).upper()
            record = SpanRecord(
                trace_id=trace_id,
                span_id=str(span.get("spanID", "")),
                parent_span_id=parent_span_id,
                service=service,
                operation=str(span.get("operationName", "unknown-operation")),
                kind=kind,
                start_ns=start_us * 1_000,
                end_ns=(start_us + duration_us) * 1_000,
                status=status,
                attributes=tuple(sorted(tags.items())),
            )
            grouped.setdefault(trace_id, []).append(record)
    return _finalize_traces(grouped)


def _finalize_traces(grouped: Mapping[str, Sequence[SpanRecord]]) -> list[TraceRecord]:
    traces = []
    for trace_id, spans in grouped.items():
        ordered = tuple(sorted(spans, key=lambda span: (span.start_ns, span.end_ns, span.service, span.span_id)))
        traces.append(TraceRecord(trace_id=trace_id, spans=ordered))
    return sorted(traces, key=lambda trace: trace.trace_id)


EventKey = tuple[str, str, str, str, str]


@dataclass
class LifelineEncoder:
    """Encode normalized traces as fixed-order service lifeline strings.

    Each span contributes a start and end event to its service block.  Event
    labels are mapped to one Unicode private-use code point, keeping the grammar
    implementation character-based while retaining token semantics in a reverse
    dictionary.  ``#`` separates service lifelines.
    """

    service_order: tuple[str, ...] | None = None
    include_status: bool = False
    include_duration_bucket: bool = False
    duration_multiplier: float = 2.0
    separator: str = "#"
    phases: tuple[str, ...] = ("START", "END")

    def __post_init__(self) -> None:
        if self.duration_multiplier <= 1.0:
            raise ValueError("duration_multiplier must be greater than one")
        self._key_to_token: dict[EventKey, str] = {}
        self._token_to_key: dict[str, EventKey] = {}
        self._duration_thresholds: dict[tuple[str, str, str], float] = {}
        self.unknown_token = chr(0xE000)
        self._token_to_key[self.unknown_token] = ("<UNK>", "<UNK>", "<UNK>", "<UNK>", "<UNK>")
        self._fitted = False

    def _event_key(self, span: SpanRecord, phase: str) -> EventKey:
        annotations: list[str] = []
        if self.include_status:
            annotations.append(span.status)
        if self.include_duration_bucket:
            signature = (span.service, span.operation, span.kind)
            threshold = self._duration_thresholds.get(signature)
            bucket = "SLOW" if threshold is not None and span.duration_ns > threshold else "NORMAL"
            annotations.append(f"duration={bucket}")
        return (
            span.service,
            span.operation,
            span.kind,
            phase,
            "|".join(annotations) if annotations else "*",
        )

    def fit(self, traces: Iterable[TraceRecord]) -> "LifelineEncoder":
        traces_tuple = tuple(traces)
        if self.service_order is None:
            self.service_order = tuple(sorted({span.service for trace in traces_tuple for span in trace.spans}))
        invalid_phases = set(self.phases) - {"START", "END"}
        if invalid_phases:
            raise ValueError(f"unsupported phases: {sorted(invalid_phases)}")
        if self.include_duration_bucket:
            maxima: dict[tuple[str, str, str], int] = {}
            for trace in traces_tuple:
                for span in trace.spans:
                    signature = (span.service, span.operation, span.kind)
                    maxima[signature] = max(maxima.get(signature, 0), span.duration_ns)
            self._duration_thresholds = {
                signature: max(1.0, duration * self.duration_multiplier)
                for signature, duration in maxima.items()
            }
        keys = {
            self._event_key(span, phase)
            for trace in traces_tuple
            for span in trace.spans
            for phase in self.phases
        }
        for offset, key in enumerate(sorted(keys), start=1):
            token = chr(0xE000 + offset)
            if token == self.separator:
                raise AssertionError("private-use token collided with separator")
            self._key_to_token[key] = token
            self._token_to_key[token] = key
        self._fitted = True
        return self

    def encode(self, trace: TraceRecord) -> str:
        if not self._fitted or self.service_order is None:
            raise RuntimeError("fit the encoder on training traces first")
        events_by_service: dict[str, list[tuple[int, int, EventKey]]] = {
            service: [] for service in self.service_order
        }
        for span in trace.spans:
            if span.service not in events_by_service:
                continue
            if "START" in self.phases:
                start_key = self._event_key(span, "START")
                events_by_service[span.service].append((span.start_ns, 0, start_key))
            if "END" in self.phases:
                end_key = self._event_key(span, "END")
                events_by_service[span.service].append((span.end_ns, 1, end_key))
        blocks: list[str] = []
        for service in self.service_order:
            events = sorted(events_by_service[service], key=lambda event: (event[0], event[1], event[2]))
            blocks.append("".join(self._key_to_token.get(key, self.unknown_token) for _, _, key in events))
        return self.separator.join(blocks)

    def decode_tokens(self, encoded: str) -> list[str | EventKey]:
        return [
            self.separator if token == self.separator else self._token_to_key.get(token, self._token_to_key[self.unknown_token])
            for token in encoded
        ]

    @property
    def duration_thresholds(self) -> dict[tuple[str, str, str], float]:
        return dict(self._duration_thresholds)

    @property
    def vocabulary_size(self) -> int:
        return len(self._key_to_token) + 1

    @property
    def token_to_key(self) -> dict[str, EventKey]:
        return dict(self._token_to_key)

    @property
    def service_tokens(self) -> dict[str, set[str]]:
        if self.service_order is None:
            return {}
        result = {service: set() for service in self.service_order}
        for token, key in self._token_to_key.items():
            service = key[0]
            if service in result and token != self.unknown_token:
                result[service].add(token)
        return result

    @property
    def alphabet(self) -> tuple[str, ...]:
        return tuple(sorted(self._token_to_key))
