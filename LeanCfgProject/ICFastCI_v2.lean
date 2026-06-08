import LeanCfgProject.ICReproducibilitySummary

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

namespace LeanCfgProject

/-
ICFastCI_v2.lean

Second fast-CI target.

This is a single import target for ordinary iteration after adding the
freeze-index and reproducibility layers.
-/

theorem icFastCI_v2_reproducibility_available :
    True := by
  trivial

theorem icFastCI_v2_available :
    True := by
  trivial

end LeanCfgProject
