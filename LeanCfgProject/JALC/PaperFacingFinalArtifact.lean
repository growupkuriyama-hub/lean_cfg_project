import LeanCfgProject.JALC.FinalArtifactKernel

namespace LeanCfgProject
namespace JALC
namespace PaperFacingFinalArtifact

/-
Paper-facing final aggregation target for the JALC artifact.

Building this target checks the final imported chain:

  LeanCfgProject.JALC.Summary
  LeanCfgProject.JALC.PaperFacingFullFiniteMain
  LeanCfgProject.JALC.PaperFacingFullAlgorithmicAgreement

This is intended as the final CI target after the Algorithm 1 / FullKept
agreement experiment.
-/

open FinalArtifactKernel

/-- Paper-facing marker that the final JALC artifact target builds. -/
theorem checked_final_artifact :
    FinalArtifactChecked :=
  final_artifact_checked

/-- Paper-facing checklist for the imported high-level targets. -/
theorem checked_final_artifact_checklist :
    includes_original_summary_target ∧
      includes_full_finite_main_target ∧
        includes_algorithmic_agreement_target :=
  final_artifact_checklist

end PaperFacingFinalArtifact
end JALC
end LeanCfgProject
