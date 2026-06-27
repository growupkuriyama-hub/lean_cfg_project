import LeanCfgProject.MCFG.FI_v2_1_ActualRefinedRuleLists

/-!
# FI v2.1 Lean experiment: actual refined rule lists in the finite-monoid case

This file specializes the actual refined-rule list construction to the
canonical plan obtained from `[Fintype M]`.  Together with the semantic working
conditions for the base grammar, it gives an actual `FintypeConcreteRuleEnumeration`:
the finite-monoid concrete refined-rule enumeration is no longer merely an
interface here.
-/

namespace FIv21

universe u v w

section ActualRefinedRuleListsFintype

variable {N : Type w} {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- The actual finite output-type refined grammar generated from the canonical
finite-monoid rule-enumeration plan. -/
noncomputable def actualFiniteOutputTypeRefinedGrammarOfFintype
    (G : WorkingMCFG N α) (obs : α → M)
    (hG : G.SemanticWorkingConditions) :
    FiniteOutputTypeRefinedGrammar G obs :=
  actualFiniteOutputTypeRefinedGrammar
    (FiniteRuleEnumerationPlan.ofFintype G obs)
    hG.1.2.1
    hG.2

/-- The actual finite-monoid refined grammar covers all ordinary output-type
rule refinements. -/
theorem actualFiniteOutputTypeRefinedGrammarOfFintype_coversAll
    (G : WorkingMCFG N α) (obs : α → M)
    (hG : G.SemanticWorkingConditions) :
    (actualFiniteOutputTypeRefinedGrammarOfFintype G obs hG).CoversAllOrdinaryRuleRefinements := by
  exact actualFiniteOutputTypeRefinedGrammar_coversAll
    (FiniteRuleEnumerationPlan.ofFintype G obs)
    hG.1.2.1
    hG.2

/-- The actual concrete refined-rule enumeration for the canonical finite-monoid
plan. -/
noncomputable def actualConcreteRefinedRuleEnumerationOfFintype
    (G : WorkingMCFG N α) (obs : α → M)
    (hG : G.SemanticWorkingConditions) :
    ConcreteRefinedRuleEnumeration (FiniteRuleEnumerationPlan.ofFintype G obs) :=
  actualConcreteRefinedRuleEnumeration
    (FiniteRuleEnumerationPlan.ofFintype G obs)
    hG.1.2.1
    hG.2

/-- The actual finite-monoid concrete refined-rule enumeration packaged in the
existing finite-monoid interface. -/
noncomputable def actualFintypeConcreteRuleEnumeration
    (G : WorkingMCFG N α) (obs : α → M)
    (hG : G.SemanticWorkingConditions) :
    FintypeConcreteRuleEnumeration G obs :=
  { concrete := actualConcreteRefinedRuleEnumerationOfFintype G obs hG }

/-- The actual finite-monoid concrete enumeration contains all ordinary
output-type rule refinements. -/
theorem actualFintypeConcreteRuleEnumeration_containsAll
    (G : WorkingMCFG N α) (obs : α → M)
    (hG : G.SemanticWorkingConditions) :
    (actualFintypeConcreteRuleEnumeration G obs hG).toFintypeOutputTypeRefinementCertificate.toOutputTypeRefinedGrammar.ContainsAllOrdinaryRuleRefinements := by
  exact (actualFintypeConcreteRuleEnumeration G obs hG).containsAllOrdinaryRuleRefinements

/-- The listed rules of the actual finite-monoid enumeration are supported by
the canonical finite-monoid plan. -/
theorem actualFintypeConcreteRuleEnumeration_supportedByPlan
    (G : WorkingMCFG N α) (obs : α → M)
    (hG : G.SemanticWorkingConditions) :
    (actualFintypeConcreteRuleEnumeration G obs hG).grammar.AllRulesSupportedByPlan
      (FiniteRuleEnumerationPlan.ofFintype G obs) := by
  exact (actualFintypeConcreteRuleEnumeration G obs hG).allRulesSupportedByPlan

end ActualRefinedRuleListsFintype

end FIv21
