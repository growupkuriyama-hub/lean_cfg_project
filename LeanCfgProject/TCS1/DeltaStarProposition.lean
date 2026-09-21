import LeanCfgProject.TCS1.DeltaStarBinaryGrammar
import LeanCfgProject.TCS1.DeltaStarNonregular

/-!
# TCS #1 v78: paper-facing Delta-star proposition package

This module packages the machine-checked components of the manuscript's
nonlinear Delta-star example.

Verified here, by reference to the preceding modules:

* the displayed CFG `S -> T S | epsilon`, `T -> a T b | epsilon`
  generates exactly the parser language;
* an explicit finite binary CFG has exactly the same initial language;
* the language is nonregular;
* it is substitutable for the finite monoid homomorphism `h_star`;
* it lies outside every fixed prefix--suffix window class.

The manuscript's separate claim that Delta-star is *non-linear* uses the
external theorem that linear languages are closed under intersection with
regular languages together with the cited non-linearity of Delta Delta.
That external linear-language theorem is not represented in the current Lean
library, so this package deliberately does not encode that clause as if it had
been machine checked.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

/--
Paper-facing verified core of the nonlinear fixed-h-star example.

The only proposition clause intentionally omitted from this conjunction is
non-linearity, whose manuscript proof depends on an external linear-language
closure/non-linearity theorem not formalized in this repository.
-/
theorem nonlinear_rs_example_verified_core :
    (∀ w : Word Symbol,
      SDerives w ↔ w ∈ Language)
    ∧
    (initial.Finite ∧
      InitialSetLanguage
        binaryGrammar initial =
      Language)
    ∧
    (¬ FormalLanguage.IsRegular)
    ∧
    FixedHSubstitutable
      starTyping Language
    ∧
    (∀ k l : Nat,
      ¬ FixedWindowSubstitutable
        k l Language) := by
  refine ⟨displayedDerives_iff_language, ?_⟩
  refine ⟨finite_cfg_witness, ?_⟩
  refine ⟨not_regular, ?_⟩
  exact
    deltaStar_fixedH_and_outside_all_fixedWindows

end DeltaStar
end TCS1
end LeanCfgProject
