from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from .observers import (
    ModularCountObserver,
    Observer,
    alternating_phase_observer,
    block_envelope_observer,
)
from .traces import LifelineEncoder


@dataclass(frozen=True)
class ObserverLibrary:
    candidates: tuple[Observer, ...]
    block_tokens: tuple[tuple[str, ...], ...]


def observers_from_encoder(
    encoder: LifelineEncoder,
    include_phase: bool = True,
    moduli: Sequence[int] = (2, 3),
) -> ObserverLibrary:
    """Generate a finite observer library from the training trace schema only."""
    if encoder.service_order is None:
        raise RuntimeError("fit the encoder before generating observers")
    service_tokens = encoder.service_tokens
    blocks = tuple(tuple(sorted(service_tokens[service])) for service in encoder.service_order)
    alphabet = tuple(sorted(set().union(*(set(block) for block in blocks)) | {encoder.separator}))

    candidates: list[Observer] = [
        block_envelope_observer(
            blocks,
            separator=encoder.separator,
            name="route-lifeline-envelope",
        )
    ]
    for service, tokens in zip(encoder.service_order, blocks):
        for modulus in moduli:
            candidates.append(
                ModularCountObserver(tokens, modulus, f"count[{service}]_mod_{modulus}")
            )
        if include_phase:
            start_tokens = [
                token for token in tokens
                if encoder.token_to_key[token][3] == "START"
            ]
            end_tokens = [
                token for token in tokens
                if encoder.token_to_key[token][3] == "END"
            ]
            if start_tokens and end_tokens:
                candidates.append(
                    alternating_phase_observer(
                        start_tokens,
                        end_tokens,
                        alphabet,
                        f"phase[{service}]",
                    )
                )

    candidates.append(
        ModularCountObserver((encoder.separator,), 2, "separator_parity_decoy")
    )
    return ObserverLibrary(tuple(candidates), blocks)
