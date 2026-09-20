import LeanCfgProject.TCS1.LinearSeparatorFixedH

/-!
# TCS #1 v78: Proposition 8.6 separation package

This facade bundles the parts of Proposition 8.6 that are currently verified
inside Lean: the concrete four-element fixed-h positive result, failure of
Clark--Eyraud substitutability, and failure of every fixed (k,l) window.

The displayed linear grammar and the external nonregularity argument are kept
as separate targets; this theorem does not overstate those two components.
-/

namespace LeanCfgProject
namespace TCS1

/-- Lean-verified substitutability/separation core of Proposition 8.6. -/
theorem lpm_proposition86_substitutability_core :
    FixedHSubstitutable lpmTyping LpmLanguage ∧
      ¬ ClarkEyraudSubstitutable LpmLanguage ∧
      ∀ k l : Nat,
        ¬ FixedWindowSubstitutable k l LpmLanguage := by
  refine ⟨lpm_fixedHSubstitutable, lpm_not_clarkEyraud, ?_⟩
  intro k l
  exact lpm_not_fixedWindowSubstitutable k l

end TCS1
end LeanCfgProject
