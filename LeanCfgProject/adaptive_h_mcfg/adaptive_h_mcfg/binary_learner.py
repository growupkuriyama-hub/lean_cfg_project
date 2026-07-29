from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
from typing import ClassVar, Hashable, Iterable, Sequence

from .observers import Observer
from .occurrences import Context, Occurrence, enumerate_occurrences

TupleValue = tuple[str, ...]


@dataclass(frozen=True, order=True)
class ChildRef:
    side: int  # 0 = left child, 1 = right child
    index: int


TemplateToken = str | ChildRef
TemplateComponent = tuple[TemplateToken, ...]


@dataclass(frozen=True)
class BinaryRule:
    parent: TupleValue
    left: TupleValue
    right: TupleValue
    template: tuple[TemplateComponent, ...]

    def apply(self, left_value: TupleValue, right_value: TupleValue) -> TupleValue:
        if len(left_value) != len(self.left) or len(right_value) != len(self.right):
            raise ValueError("child arity mismatch")
        output: list[str] = []
        for component in self.template:
            pieces: list[str] = []
            for token in component:
                if isinstance(token, str):
                    pieces.append(token)
                elif token.side == 0:
                    pieces.append(left_value[token.index])
                else:
                    pieces.append(right_value[token.index])
            output.append("".join(pieces))
        return tuple(output)


@dataclass(frozen=True)
class StartRule:
    word: str
    child: TupleValue


@dataclass
class CanonicalBinaryModel:
    observer_name: str
    training_words: tuple[str, ...]
    nonterminals: tuple[TupleValue, ...]
    unit_rules: dict[TupleValue, set[TupleValue]]
    binary_rules: tuple[BinaryRule, ...]
    terminal_nonterminals: tuple[TupleValue, ...]
    occurrence_count: int
    observed_type_count: int

    @property
    def rule_count(self) -> int:
        return (
            len(self.training_words)
            + len(self.terminal_nonterminals)
            + sum(len(targets) for targets in self.unit_rules.values())
            + len(self.binary_rules)
        )

    @staticmethod
    def _embeds_disjointly(value: TupleValue, target: str) -> bool:
        """Whether tuple components can occupy pairwise disjoint target spans.

        For fan-out at most two this is a cheap necessary condition for any
        successful linear nondeleting derivation into ``target``.  Applying it
        only removes impossible intermediate values; it does not add derivations.
        """
        if len(value) == 1:
            return value[0] in target
        if len(value) > 3:
            raise ValueError("guided recognizer currently supports fan-out at most three")

        occurrences: list[list[tuple[int, int]]] = []
        for component in value:
            if component == "":
                occurrences.append([(0, 0)])
                continue
            hits: list[tuple[int, int]] = []
            cursor = target.find(component)
            while cursor >= 0:
                hits.append((cursor, cursor + len(component)))
                cursor = target.find(component, cursor + 1)
            if not hits:
                return False
            occurrences.append(hits)

        chosen: list[tuple[int, int]] = []
        def visit(index: int) -> bool:
            if index == len(occurrences):
                return True
            for start, end in occurrences[index]:
                if start == end or all(end <= a or b <= start for a, b in chosen if a != b):
                    chosen.append((start, end))
                    if visit(index + 1):
                        return True
                    chosen.pop()
            return False
        return visit(0)

    def derive_bounded(
        self,
        max_length: int,
        max_values_per_nt: int = 25000,
        max_total_values: int = 2_000_000,
        target_filter: str | None = None,
    ) -> dict[TupleValue, set[TupleValue]]:
        """Semi-naive bounded generation for the finite learned MCFG.

        The grammar may be cyclic.  Since every binary rule is nondeleting and
        terminal values are nonempty, a total yield-length bound makes the
        generated closure finite.  Per-nonterminal and global safeguards prevent
        pathological coarse observations from exhausting memory.
        """

        values: dict[TupleValue, set[TupleValue]] = {nt: set() for nt in self.nonterminals}
        unit_predecessors: dict[TupleValue, set[TupleValue]] = defaultdict(set)
        left_uses: dict[TupleValue, list[BinaryRule]] = defaultdict(list)
        right_uses: dict[TupleValue, list[BinaryRule]] = defaultdict(list)

        for source, targets in self.unit_rules.items():
            for target in targets:
                unit_predecessors[target].add(source)
        for rule in self.binary_rules:
            left_uses[rule.left].append(rule)
            right_uses[rule.right].append(rule)

        queue: deque[tuple[TupleValue, TupleValue]] = deque()
        total_values = 0

        def within_bound(value: TupleValue) -> bool:
            return sum(len(component) for component in value) <= max_length

        def add(nt: TupleValue, value: TupleValue) -> bool:
            nonlocal total_values
            if not within_bound(value):
                return False
            if target_filter is not None and not self._embeds_disjointly(value, target_filter):
                return False
            bucket = values[nt]
            if value in bucket:
                return False
            if len(bucket) >= max_values_per_nt or total_values >= max_total_values:
                return False
            bucket.add(value)
            total_values += 1
            queue.append((nt, value))
            return True

        for nt in self.terminal_nonterminals:
            add(nt, nt)

        while queue:
            nt, value = queue.popleft()

            for source in unit_predecessors.get(nt, ()):
                add(source, value)

            for rule in left_uses.get(nt, ()):
                for right_value in tuple(values[rule.right]):
                    add(rule.parent, rule.apply(value, right_value))

            for rule in right_uses.get(nt, ()):
                for left_value in tuple(values[rule.left]):
                    add(rule.parent, rule.apply(left_value, value))

        return values


    def accepts_one_guided(
        self,
        word: str,
        max_values_per_nt: int = 25000,
        max_total_values: int = 2_000_000,
    ) -> bool:
        """Recognize one word with target-substring/disjointness pruning."""
        derived = self.derive_bounded(
            len(word),
            max_values_per_nt=max_values_per_nt,
            max_total_values=max_total_values,
            target_filter=word,
        )
        return any(value == (word,) for start in self.training_words for value in derived.get((start,), ()))

    def accepts_many_guided(
        self,
        words: Iterable[str],
        max_values_per_nt: int = 25000,
        max_total_values: int = 2_000_000,
    ) -> dict[str, bool]:
        # Recognition is language-level and repeated traces often share the same
        # encoding. Evaluate each distinct word once, then let callers count
        # trace multiplicities from the returned map.
        unique_words = tuple(dict.fromkeys(words))
        return {
            word: self.accepts_one_guided(
                word,
                max_values_per_nt=max_values_per_nt,
                max_total_values=max_total_values,
            )
            for word in unique_words
        }

    def accepts_many(
        self,
        words: Iterable[str],
        max_length: int | None = None,
        **derive_kwargs: int,
    ) -> dict[str, bool]:
        words_tuple = tuple(words)
        bound = max_length or max((len(word) for word in words_tuple), default=0)
        derived = self.derive_bounded(bound, **derive_kwargs)
        accepted: set[str] = set()
        for word in self.training_words:
            for value in derived.get((word,), ()):
                if len(value) == 1:
                    accepted.add(value[0])
        return {word: word in accepted for word in words_tuple}


@dataclass(frozen=True)
class PreparedCanonicalBasis:
    training_words: tuple[str, ...]
    contexts_by_tuple: dict[TupleValue, set[Context]]
    nonterminals: tuple[TupleValue, ...]
    binary_rules: tuple[BinaryRule, ...]
    terminal_nonterminals: tuple[TupleValue, ...]
    occurrence_count: int


@dataclass(frozen=True)
class _Placement:
    component_index: int
    start: int
    end: int
    ref: ChildRef


class BoundedCanonicalMCFGLearner:
    _shared_basis_cache: ClassVar[dict[tuple[int, tuple[str, ...]], PreparedCanonicalBasis]] = {}
    """Binary-witness fixed-observation learner over a finite occurrence basis.

    This implements the canonical rule schema much more faithfully than the
    first restricted prototype:

    * only observed letter tuples receive terminal rules;
    * all type-guarded common-context unit rules are included;
    * every nonempty binary witness over the enumerated occurrence basis is
      included, for child fan-out at most ``fanout``.

    The remaining difference from the theorem is explicit and controlled:
    ``enumerate_occurrences`` currently uses a trace-oriented structural interval
    basis rather than every possible named interval/cut occurrence, and empty
    child components are omitted from binary witnesses.  Thus the implementation
    is complete relative to that finite nonempty basis, not yet relative to all
    theoretical occurrences.
    """

    def __init__(self, fanout: int = 2):
        if fanout not in (1, 2, 3):
            raise ValueError("prototype currently supports fanout 1, 2, or 3")
        self.fanout = fanout
        self._basis_cache: dict[tuple[str, ...], PreparedCanonicalBasis] = {}

    @staticmethod
    def _contexts_and_occurrences(
        occurrences: Sequence[Occurrence],
    ) -> tuple[dict[TupleValue, set[Context]], dict[str, list[Occurrence]]]:
        contexts_by_tuple: dict[TupleValue, set[Context]] = defaultdict(set)
        occurrences_by_word: dict[str, list[Occurrence]] = defaultdict(list)
        for occurrence in occurrences:
            # Empty tuple components are retained for unit-rule fidelity but are
            # excluded from binary-witness construction below.
            contexts_by_tuple[occurrence.components].add(occurrence.context)
            occurrences_by_word[occurrence.word].append(occurrence)
        return contexts_by_tuple, occurrences_by_word

    @staticmethod
    def _unit_rules(
        nonterminals: Sequence[TupleValue],
        contexts_by_tuple: dict[TupleValue, set[Context]],
        observer: Observer,
    ) -> dict[TupleValue, set[TupleValue]]:
        by_arity_and_type: dict[tuple[int, Hashable], list[TupleValue]] = defaultdict(list)
        for nt in nonterminals:
            by_arity_and_type[(len(nt), observer.tuple_type(nt))].append(nt)

        unit_rules: dict[TupleValue, set[TupleValue]] = defaultdict(set)
        for group in by_arity_and_type.values():
            for source in group:
                source_contexts = contexts_by_tuple[source]
                for target in group:
                    if source != target and source_contexts.intersection(contexts_by_tuple[target]):
                        unit_rules[source].add(target)
        return {source: set(targets) for source, targets in unit_rules.items()}

    @staticmethod
    def _component_interval_index(
        parent: TupleValue,
        allowed_values: dict[tuple[int, int], set[str]],
        child_arity: int,
        side: int,
    ) -> dict[ChildRef, list[tuple[int, int, int]]]:
        result: dict[ChildRef, list[tuple[int, int, int]]] = {}
        for index in range(child_arity):
            ref = ChildRef(side, index)
            allowed = allowed_values[(child_arity, index)]
            candidates: list[tuple[int, int, int]] = []
            for component_index, component in enumerate(parent):
                n = len(component)
                for start in range(n):
                    for end in range(start + 1, n + 1):
                        if component[start:end] in allowed:
                            candidates.append((component_index, start, end))
            result[ref] = candidates
        return result

    @staticmethod
    def _build_template(parent: TupleValue, placements: Sequence[_Placement]) -> tuple[TemplateComponent, ...]:
        by_component: dict[int, list[_Placement]] = defaultdict(list)
        for placement in placements:
            by_component[placement.component_index].append(placement)

        output: list[TemplateComponent] = []
        for component_index, component in enumerate(parent):
            tokens: list[TemplateToken] = []
            cursor = 0
            for placement in sorted(by_component.get(component_index, ()), key=lambda p: (p.start, p.end, p.ref)):
                if cursor < placement.start:
                    tokens.append(component[cursor:placement.start])
                tokens.append(placement.ref)
                cursor = placement.end
            if cursor < len(component):
                tokens.append(component[cursor:])
            if not tokens:
                tokens.append(component)
            # Coalesce adjacent terminal strings for stable hashing/printing.
            coalesced: list[TemplateToken] = []
            for token in tokens:
                if isinstance(token, str) and coalesced and isinstance(coalesced[-1], str):
                    coalesced[-1] = str(coalesced[-1]) + token
                else:
                    coalesced.append(token)
            output.append(tuple(coalesced))
        return tuple(output)

    def _binary_rules(self, nonterminals: Sequence[TupleValue]) -> tuple[BinaryRule, ...]:
        nt_set = set(nonterminals)
        nts_by_arity: dict[int, list[TupleValue]] = defaultdict(list)
        allowed_values: dict[tuple[int, int], set[str]] = defaultdict(set)
        for nt in nonterminals:
            if any(component == "" for component in nt):
                continue
            nts_by_arity[len(nt)].append(nt)
            for index, component in enumerate(nt):
                allowed_values[(len(nt), index)].add(component)

        rules: set[BinaryRule] = set()

        for parent in nonterminals:
            if any(component == "" for component in parent):
                continue
            parent_total = sum(map(len, parent))
            if parent_total < 2:
                continue

            for left_arity in range(1, self.fanout + 1):
                for right_arity in range(1, self.fanout + 1):
                    refs = [ChildRef(0, i) for i in range(left_arity)] + [
                        ChildRef(1, i) for i in range(right_arity)
                    ]
                    candidate_map = {}
                    candidate_map.update(
                        self._component_interval_index(parent, allowed_values, left_arity, 0)
                    )
                    candidate_map.update(
                        self._component_interval_index(parent, allowed_values, right_arity, 1)
                    )
                    if any(not candidate_map[ref] for ref in refs):
                        continue

                    # Place the most constrained variables first.
                    ordered_refs = sorted(refs, key=lambda ref: (len(candidate_map[ref]), ref))
                    occupied: dict[int, list[tuple[int, int]]] = defaultdict(list)
                    chosen: dict[ChildRef, _Placement] = {}

                    def overlaps(component_index: int, start: int, end: int) -> bool:
                        return any(not (end <= a or b <= start) for a, b in occupied[component_index])

                    def visit(position: int) -> None:
                        if position == len(ordered_refs):
                            left = tuple(
                                parent[chosen[ChildRef(0, i)].component_index][
                                    chosen[ChildRef(0, i)].start : chosen[ChildRef(0, i)].end
                                ]
                                for i in range(left_arity)
                            )
                            right = tuple(
                                parent[chosen[ChildRef(1, i)].component_index][
                                    chosen[ChildRef(1, i)].start : chosen[ChildRef(1, i)].end
                                ]
                                for i in range(right_arity)
                            )
                            if left not in nt_set or right not in nt_set:
                                return
                            placements = tuple(chosen[ref] for ref in refs)
                            template = self._build_template(parent, placements)
                            rule = BinaryRule(parent, left, right, template)
                            # Defensive exactness check.
                            if rule.apply(left, right) != parent:
                                raise AssertionError("induced binary template does not reconstruct parent")
                            rules.add(rule)
                            return

                        ref = ordered_refs[position]
                        for component_index, start, end in candidate_map[ref]:
                            if overlaps(component_index, start, end):
                                continue
                            placement = _Placement(component_index, start, end, ref)
                            chosen[ref] = placement
                            occupied[component_index].append((start, end))
                            visit(position + 1)
                            occupied[component_index].pop()
                            del chosen[ref]

                    visit(0)

        return tuple(sorted(rules, key=repr))

    def prepare(self, words: Iterable[str]) -> PreparedCanonicalBasis:
        """Precompute observer-independent structure once per positive sample.

        Binary witnesses, observed tuples, and terminal rules depend only on the
        sample and fan-out. Adaptive observer selection changes only the typed
        unit rules. Caching this basis avoids rebuilding roughly 100k binary
        rules for every candidate product.
        """
        training_words = tuple(sorted(set(words)))
        if not training_words:
            raise ValueError("at least one positive training word is required")
        cached = self._basis_cache.get(training_words)
        if cached is not None:
            return cached
        shared_key = (self.fanout, training_words)
        shared = self._shared_basis_cache.get(shared_key)
        if shared is not None:
            self._basis_cache[training_words] = shared
            return shared

        occurrences = enumerate_occurrences(training_words, fanout=self.fanout)
        contexts_by_tuple, _ = self._contexts_and_occurrences(occurrences)
        nonterminals = tuple(sorted(contexts_by_tuple, key=lambda x: (len(x), x)))
        binary_rules = self._binary_rules(nonterminals)
        alphabet = sorted(set("".join(training_words)))
        terminal_nonterminals = tuple((symbol,) for symbol in alphabet if (symbol,) in contexts_by_tuple)
        basis = PreparedCanonicalBasis(
            training_words=training_words,
            contexts_by_tuple=contexts_by_tuple,
            nonterminals=nonterminals,
            binary_rules=binary_rules,
            terminal_nonterminals=terminal_nonterminals,
            occurrence_count=len(occurrences),
        )
        self._basis_cache[training_words] = basis
        self._shared_basis_cache[shared_key] = basis
        return basis

    def fit_prepared(self, basis: PreparedCanonicalBasis, observer: Observer) -> CanonicalBinaryModel:
        unit_rules = self._unit_rules(basis.nonterminals, basis.contexts_by_tuple, observer)
        return CanonicalBinaryModel(
            observer_name=observer.name,
            training_words=basis.training_words,
            nonterminals=basis.nonterminals,
            unit_rules=unit_rules,
            binary_rules=basis.binary_rules,
            terminal_nonterminals=basis.terminal_nonterminals,
            occurrence_count=basis.occurrence_count,
            observed_type_count=len({(len(nt), observer.tuple_type(nt)) for nt in basis.nonterminals}),
        )

    def fit(self, words: Iterable[str], observer: Observer) -> CanonicalBinaryModel:
        return self.fit_prepared(self.prepare(words), observer)
