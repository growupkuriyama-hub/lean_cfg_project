from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
from typing import Iterable

from .observers import Observer
from .occurrences import Context, Occurrence, enumerate_occurrences

TupleValue = tuple[str, ...]


@dataclass(frozen=True)
class WrapRule:
    parent: TupleValue
    child: TupleValue
    prefixes: tuple[str, ...]
    suffixes: tuple[str, ...]

    def apply(self, value: TupleValue) -> TupleValue:
        return tuple(
            prefix + component + suffix
            for prefix, component, suffix in zip(self.prefixes, value, self.suffixes)
        )


@dataclass(frozen=True)
class AssemblyRule:
    parent: TupleValue  # unary observed word tuple
    child: TupleValue
    context: Context

    def apply(self, value: TupleValue) -> TupleValue:
        return (self.context.fill(value),)


@dataclass
class LearnedModel:
    observer_name: str
    training_words: tuple[str, ...]
    nonterminals: tuple[TupleValue, ...]
    unit_rules: dict[TupleValue, set[TupleValue]]
    wrap_rules: tuple[WrapRule, ...]
    assembly_rules: tuple[AssemblyRule, ...]
    occurrence_count: int
    observed_type_count: int

    def derive_bounded(self, max_length: int, max_values_per_nt: int = 20000) -> dict[TupleValue, set[TupleValue]]:
        """Enumerate the restricted grammar's tuple yields up to max_length.

        This is a bounded experimental recognizer.  It is complete for this
        restricted grammar below the supplied length bound, but it is not a
        general polynomial-time MCFG parser.
        """

        values: dict[TupleValue, set[TupleValue]] = {
            nt: {nt} for nt in self.nonterminals
        }
        unit_predecessors: dict[TupleValue, set[TupleValue]] = defaultdict(set)
        wrap_by_child: dict[TupleValue, list[WrapRule]] = defaultdict(list)
        assembly_by_child: dict[TupleValue, list[AssemblyRule]] = defaultdict(list)

        for source, targets in self.unit_rules.items():
            for target in targets:
                unit_predecessors[target].add(source)
        for rule in self.wrap_rules:
            wrap_by_child[rule.child].append(rule)
        for rule in self.assembly_rules:
            assembly_by_child[rule.child].append(rule)

        queue: deque[tuple[TupleValue, TupleValue]] = deque(
            (nt, nt) for nt in self.nonterminals
        )

        def within_bound(value: TupleValue) -> bool:
            return sum(len(component) for component in value) <= max_length

        def add(nt: TupleValue, value: TupleValue) -> None:
            if not within_bound(value):
                return
            bucket = values[nt]
            if value in bucket:
                return
            if len(bucket) >= max_values_per_nt:
                # Coarse observers can create explosive bounded closures.  The
                # prototype truncates such buckets instead of crashing; the
                # resulting loss of coverage is itself a useful signal against
                # an over-coarse observation in the outer selection loop.
                return
            bucket.add(value)
            queue.append((nt, value))

        while queue:
            nt, value = queue.popleft()
            for source in unit_predecessors.get(nt, ()):
                add(source, value)
            for rule in wrap_by_child.get(nt, ()):
                add(rule.parent, rule.apply(value))
            for rule in assembly_by_child.get(nt, ()):
                add(rule.parent, rule.apply(value))

        return values

    def accepts_many(self, words: Iterable[str], max_length: int | None = None) -> dict[str, bool]:
        words_tuple = tuple(words)
        bound = max_length or max((len(word) for word in words_tuple), default=0)
        derived = self.derive_bounded(bound)
        start_nts = {(word,) for word in self.training_words}
        accepted: set[str] = set()
        for nt in start_nts:
            for value in derived.get(nt, ()):
                if len(value) == 1:
                    accepted.add(value[0])
        return {word: word in accepted for word in words_tuple}

    @property
    def rule_count(self) -> int:
        return (
            sum(len(targets) for targets in self.unit_rules.values())
            + len(self.wrap_rules)
            + len(self.assembly_rules)
            + len(self.nonterminals)  # ground rules
        )


class RestrictedTypedTupleLearner:
    """A controlled prototype of the fixed-h tuple-substitution construction.

    Implemented fragments:
      * observed arity-1/2 tuple occurrences and named sentence contexts;
      * type-guarded shared-context unit rules;
      * context assembly rules from observed tuples to complete sample words;
      * one-child terminal-wrap rules between same-arity observed tuples;
      * lexical ground rules for every observed tuple.

    The full canonical learner additionally enumerates all binary witnesses.
    That extension is deliberately left as the next implementation milestone.
    """

    def __init__(self, fanout: int = 2, max_wrap_delta: int = 8):
        self.fanout = fanout
        self.max_wrap_delta = max_wrap_delta

    def fit(self, words: Iterable[str], observer: Observer) -> LearnedModel:
        training_words = tuple(sorted(set(words)))
        if not training_words:
            raise ValueError("at least one positive training word is required")

        occurrences = enumerate_occurrences(training_words, fanout=self.fanout)
        contexts_by_tuple: dict[TupleValue, set[Context]] = defaultdict(set)
        occurrences_by_word: dict[str, list[Occurrence]] = defaultdict(list)
        for occurrence in occurrences:
            contexts_by_tuple[occurrence.components].add(occurrence.context)
            occurrences_by_word[occurrence.word].append(occurrence)

        nonterminals = tuple(sorted(contexts_by_tuple, key=lambda x: (len(x), x)))
        by_arity_and_type: dict[tuple[int, object], list[TupleValue]] = defaultdict(list)
        for nt in nonterminals:
            by_arity_and_type[(len(nt), observer.tuple_type(nt))].append(nt)

        unit_rules: dict[TupleValue, set[TupleValue]] = defaultdict(set)
        for group in by_arity_and_type.values():
            for source in group:
                source_contexts = contexts_by_tuple[source]
                for target in group:
                    if source == target:
                        continue
                    if source_contexts.intersection(contexts_by_tuple[target]):
                        unit_rules[source].add(target)

        assembly_set: set[AssemblyRule] = set()
        for word, word_occurrences in occurrences_by_word.items():
            parent = (word,)
            for occurrence in word_occurrences:
                child = occurrence.components
                if child == parent and occurrence.context.tokens == ("", 0, ""):
                    continue
                assembly_set.add(AssemblyRule(parent, child, occurrence.context))

        wrap_set: set[WrapRule] = set()
        nts_by_arity: dict[int, list[TupleValue]] = defaultdict(list)
        for nt in nonterminals:
            nts_by_arity[len(nt)].append(nt)

        for arity, group in nts_by_arity.items():
            for parent in group:
                for child in group:
                    if parent == child:
                        continue
                    delta = sum(map(len, parent)) - sum(map(len, child))
                    if delta <= 0 or delta > self.max_wrap_delta:
                        continue
                    prefixes: list[str] = []
                    suffixes: list[str] = []
                    valid = True
                    for parent_component, child_component in zip(parent, child):
                        if child_component == "":
                            valid = False
                            break
                        position = parent_component.find(child_component)
                        if position < 0:
                            valid = False
                            break
                        prefixes.append(parent_component[:position])
                        suffixes.append(parent_component[position + len(child_component):])
                    if valid:
                        wrap_set.add(
                            WrapRule(parent, child, tuple(prefixes), tuple(suffixes))
                        )

        return LearnedModel(
            observer_name=observer.name,
            training_words=training_words,
            nonterminals=nonterminals,
            unit_rules={key: set(value) for key, value in unit_rules.items()},
            wrap_rules=tuple(sorted(wrap_set, key=repr)),
            assembly_rules=tuple(sorted(assembly_set, key=repr)),
            occurrence_count=len(occurrences),
            observed_type_count=len({(len(nt), observer.tuple_type(nt)) for nt in nonterminals}),
        )
