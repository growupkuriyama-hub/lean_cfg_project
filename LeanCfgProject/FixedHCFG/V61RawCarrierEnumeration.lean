import LeanCfgProject.FixedHCFG.V61CarrierCoverage

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Exact finite enumeration of the two fresh-symbol families used by the v61
terminal-isolation/right-binarization front end.

This file complements `V61RawGrammarSize`: instead of only counting terminal
occurrences and chain symbols arithmetically, it exhibits lists whose lengths
are exactly those counts.  These lists will support a concrete finite carrier
for the normalization grammar without identifying duplicate source
productions or repeated terminal occurrences.
-/

/-- Terminal atoms occurring in one raw right-hand side, with multiplicity. -/
def v61TerminalAtoms
    {N : Type v} {Sigma : Type u} :
    List (V61SourceAtom N Sigma) → List Sigma
  | [] => []
  | V61SourceAtom.nonterminal _ :: rest => v61TerminalAtoms rest
  | V61SourceAtom.terminal a :: rest => a :: v61TerminalAtoms rest

/-- The explicit terminal list realizes the terminal-occurrence counter. -/
theorem v61_terminal_atoms_length
    {N : Type v} {Sigma : Type u}
    (rhs : List (V61SourceAtom N Sigma)) :
    (v61TerminalAtoms rhs).length = v61TerminalOccurrences rhs := by
  induction rhs with
  | nil => simp [v61TerminalAtoms, v61TerminalOccurrences]
  | cons a rest ih =>
      cases a with
      | nonterminal A =>
          simp [v61TerminalAtoms, v61TerminalOccurrences, ih]
      | terminal a =>
          simp [v61TerminalAtoms, v61TerminalOccurrences, ih, Nat.add_comm]

/--
Proper suffixes that receive fresh symbols in standard right binarization.
For an RHS of length `m`, these are exactly the suffixes of lengths
`m-1, m-2, ..., 2`; hence there are `m-2` of them.
-/
def v61ProperChainSuffixes {Alpha : Type u} :
    List Alpha → List (List Alpha)
  | [] => []
  | _ :: rest =>
      match rest with
      | [] => []
      | [_] => []
      | b :: c :: tail =>
          (b :: c :: tail) :: v61ProperChainSuffixes (b :: c :: tail)

/-- The explicit proper-suffix list realizes `rhs.length - 2`. -/
theorem v61_proper_chain_suffixes_length
    {Alpha : Type u} (xs : List Alpha) :
    (v61ProperChainSuffixes xs).length = xs.length - 2 := by
  induction xs with
  | nil => simp [v61ProperChainSuffixes]
  | cons a rest ih =>
      cases rest with
      | nil => simp [v61ProperChainSuffixes]
      | cons b rest =>
          cases rest with
          | nil => simp [v61ProperChainSuffixes]
          | cons c tail =>
              simp [v61ProperChainSuffixes, ih]

/-- Every enumerated chain suffix has at least two source atoms. -/
theorem v61_two_le_length_of_mem_proper_chain_suffixes
    {Alpha : Type u} {xs suffix : List Alpha}
    (h : suffix ∈ v61ProperChainSuffixes xs) :
    2 ≤ suffix.length := by
  induction xs with
  | nil => simp [v61ProperChainSuffixes] at h
  | cons a rest ih =>
      cases rest with
      | nil => simp [v61ProperChainSuffixes] at h
      | cons b rest =>
          cases rest with
          | nil => simp [v61ProperChainSuffixes] at h
          | cons c tail =>
              simp only [v61ProperChainSuffixes, List.mem_cons] at h
              rcases h with rfl | h
              · simp
              · exact ih h

/-- Every enumerated chain suffix is a proper suffix in length. -/
theorem v61_length_lt_of_mem_proper_chain_suffixes
    {Alpha : Type u} {xs suffix : List Alpha}
    (h : suffix ∈ v61ProperChainSuffixes xs) :
    suffix.length < xs.length := by
  induction xs with
  | nil => simp [v61ProperChainSuffixes] at h
  | cons a rest ih =>
      cases rest with
      | nil => simp [v61ProperChainSuffixes] at h
      | cons b rest =>
          cases rest with
          | nil => simp [v61ProperChainSuffixes] at h
          | cons c tail =>
              simp only [v61ProperChainSuffixes, List.mem_cons] at h
              rcases h with rfl | h
              · simp
              · have hlt := ih h
                simp only [List.length_cons] at hlt ⊢
                omega

/-- One chain-slot entry keeps the source production occurrence and its suffix. -/
structure V61RawChainEntry (N : Type v) (Sigma : Type u) where
  production : V61RawProduction N Sigma
  suffix : List (V61SourceAtom N Sigma)

namespace V61RawGrammar

variable {N : Type v} {Sigma : Type u}

/-- Terminal-wrapper slots across the production list, preserving multiplicity. -/
def wrapperAtoms : List (V61RawProduction N Sigma) → List Sigma
  | [] => []
  | p :: rest => v61TerminalAtoms p.rhs ++ wrapperAtoms rest

/-- The wrapper-slot enumeration has exactly the previously defined count. -/
theorem wrapperAtoms_length (ps : List (V61RawProduction N Sigma)) :
    (wrapperAtoms ps).length = wrapperCount ps := by
  induction ps with
  | nil => simp [wrapperAtoms, wrapperCount]
  | cons p rest ih =>
      simp [wrapperAtoms, wrapperCount, v61_terminal_atoms_length, ih]

/-- Right-binarization chain slots across the production list. -/
def chainEntries :
    List (V61RawProduction N Sigma) → List (V61RawChainEntry N Sigma)
  | [] => []
  | p :: rest =>
      (v61ProperChainSuffixes p.rhs).map
          (fun suffix => ⟨p, suffix⟩) ++
        chainEntries rest

/-- The chain-slot enumeration has exactly `chainCount`. -/
theorem chainEntries_length (ps : List (V61RawProduction N Sigma)) :
    (chainEntries ps).length = chainCount ps := by
  induction ps with
  | nil => simp [chainEntries, chainCount]
  | cons p rest ih =>
      simp [chainEntries, chainCount, v61BinarizationChainCount,
        v61_proper_chain_suffixes_length, ih]

/--
A finite slot carrier with one fresh start slot, all source nonterminals, one
slot per terminal occurrence, and one slot per proper chain suffix.
-/
abbrev carrierSlots [Fintype N] (G : V61RawGrammar N Sigma) :=
  Sum Unit
    (Sum N
      (Sum (Fin (wrapperAtoms G.productions).length)
        (Fin (chainEntries G.productions).length)))

/-- Its cardinality is exactly the manuscript's four-family count. -/
theorem carrierSlots_card [Fintype N] (G : V61RawGrammar N Sigma) :
    Fintype.card (carrierSlots G) =
      1 + Fintype.card N + wrapperCount G.productions +
        chainCount G.productions := by
  simp [carrierSlots, wrapperAtoms_length, chainEntries_length,
    Nat.add_assoc]

/-- In particular the concrete slot carrier obeys the established `4n` bound. -/
theorem carrierSlots_card_le_four_size [Fintype N]
    (G : V61RawGrammar N Sigma) :
    Fintype.card (carrierSlots G) ≤ 4 * symbolSize G := by
  rw [carrierSlots_card]
  exact intermediate_family_count_le_four_size G

end V61RawGrammar

end FixedHCFG
end LeanCfgProject
