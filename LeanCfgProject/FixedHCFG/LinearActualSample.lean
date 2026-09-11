import LeanCfgProject.FixedHCFG.LinearBasisExtraction
import LeanCfgProject.FixedHCFG.LinearRuleSlots

namespace LeanCfgProject
namespace FixedHCFG

universe u v w

/-!
Concrete finite rule slots and characteristic-sample witnesses for the actual
Section-7 grammar `H = trim(fullTypedLinearGrammar Obs G)`.

A slot records a source SSLNF production together with the three genuinely free
monoid coordinates `(q,m,n)`.  Realisation additionally requires the parent and,
when present, the unique child typed state to survive reachable/productive
trimming.  This is the concrete finite indexing family needed to remove the
remaining abstract rule/sample index from the Theorem-7.9 envelope.
-/

/-- The child typed state prescribed by a source slot, when the source rule is nonterminal-bearing. -/
def actualLinearSlotChild?
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : LinearTypedRuleSlot Obs P) : Option (TypedNT N Obs) :=
  linearSlotChild? Obs G s

/-- A finite source slot is realised exactly when all typed states used by its rule survive trimming. -/
def ActualLinearSlotRealized
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    (s : LinearTypedRuleSlot Obs P) : Prop :=
  let F := fullTypedLinearGrammar Obs G
  let X := linearSlotParent Obs G s
  match actualLinearSlotChild? Obs G s with
  | none => StrictLinearKept F X
  | some Y => StrictLinearKept F X ∧ StrictLinearKept F Y

/-- Realised typed non-start rules, indexed by source production and `(q,m,n)`. -/
abbrev ActualLinearRuleSlot
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :=
  {s : LinearTypedRuleSlot Obs P // ActualLinearSlotRealized Obs G s}

/-- The realised-slot encoding into `P × M^3` is just the subtype projection. -/
def actualLinearRuleEncode
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :
    ActualLinearRuleSlot Obs G → P × Obs.M × Obs.M × Obs.M :=
  fun s => s.1

/-- The concrete rule-slot encoding is injective. -/
theorem actualLinearRuleEncode_injective
    {N : Type v} {Sigma : Type u} {P : Type w}
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P) :
    Function.Injective (actualLinearRuleEncode Obs G) := by
  intro s t h
  exact Subtype.ext h

/-- Proposition 7.7(ii) for the actual realised rule-slot family. -/
theorem actualLinearRuleSlot_card_le
    {N : Type v} {Sigma : Type u} {P : Type w}
    [Fintype P]
    (Obs : Observer Sigma) (G : IndexedSSLNF N Sigma P)
    [Fintype (ActualLinearRuleSlot Obs G)] :
    Fintype.card (ActualLinearRuleSlot Obs G) ≤
      Fintype.card P * Fintype.card Obs.M ^ 3 := by
  exact linear_typed_rule_card_le
    (actualLinearRuleEncode Obs G)
    (actualLinearRuleEncode_injective Obs G)

end FixedHCFG
end LeanCfgProject
