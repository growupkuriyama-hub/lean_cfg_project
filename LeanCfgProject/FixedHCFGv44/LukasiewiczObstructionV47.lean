import LeanCfgProject.FixedHCFGv44.DyckObstructionV47

namespace LeanCfgProject
namespace FixedHCFGv44

universe u v

/-!
The final Section 8 quotient argument from the current TCS v47 manuscript.

The paper uses the standard coding `L_Luk = D_1 b`.  We isolate the elementary
language-theoretic part of that statement: appending a fixed suffix and then
taking the right quotient by the same suffix recovers the original language.
Combining this with the already formalized quotient closure and the Dyck
obstruction yields the manuscript's Lukasiewicz obstruction.
-/

/-- Pointwise extension of a language by one fixed suffix word. -/
def SuffixExtension {Sigma : Type u} (L : Language Sigma) (z : Word Sigma) :
    Language Sigma :=
  fun w => ∃ x : Word Sigma, x ∈ L ∧ w = x ++ z

/-- Appending a fixed suffix and quotienting by it recovers the language. -/
theorem rightQuotient_suffixExtension
    {Sigma : Type u} (L : Language Sigma) (z : Word Sigma) :
    RightQuotient (SuffixExtension L z) z = L := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨x, hx, hEq⟩
    have hwx : w = x := by
      exact List.append_right_cancel hEq
    simpa [hwx] using hx
  · intro hw
    exact ⟨w, hw, rfl⟩

/-- The paper's coded Lukasiewicz language `D_1 b`. -/
def LukasiewiczV47 : Language DyckLetter :=
  SuffixExtension Dyck1 [DyckLetter.b]

/-- Under the manuscript coding, quotient by the final `b` gives `D_1`. -/
theorem lukasiewicz_rightQuotient_eq_dyck1 :
    RightQuotient LukasiewiczV47 [DyckLetter.b] = Dyck1 := by
  exact rightQuotient_suffixExtension Dyck1 [DyckLetter.b]

/-- Manuscript Section 8: the coded Lukasiewicz language is outside `RS`. -/
theorem corollary_lukasiewicz_not_rs_v47 :
    ¬ RecognizablySubstitutableAt.{0, v} LukasiewiczV47 := by
  intro hLuk
  have hQuot :=
    recognizablySubstitutable_rightQuotient_v47
      (v := v) [DyckLetter.b] hLuk
  rw [lukasiewicz_rightQuotient_eq_dyck1] at hQuot
  exact corollary_dyck_not_rs_v47 hQuot

end FixedHCFGv44
end LeanCfgProject
