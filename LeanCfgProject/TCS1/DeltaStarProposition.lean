import LeanCfgProject.TCS1.DeltaStarBinaryGrammar
import LeanCfgProject.TCS1.DeltaStarNonregular
import LeanCfgProject.TCS1.DeltaStarNonlinearityBridge
import LeanCfgProject.TCS1.DeltaStarNonlinearityReduction

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
* it lies outside every fixed prefix--suffix window class;
* the manuscript's non-linearity reduction identity
  `Delta* ∩ a* b* a* b* = Delta Delta` holds extensionally.

The manuscript's separate claim that Delta-star is *non-linear* reduces to
the cited non-linearity of Delta Delta.  The regular four-block filter, exact
intersection identity, and closure of finite raw-linear presentations under
DFA intersection are now machine checked in the local development.  The cited
Double-Delta non-linearity theorem itself remains an explicit external
mathematical input rather than an encoded axiom.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

/--
Paper-facing verified core of the nonlinear fixed-h-star example.

The only proposition clause intentionally omitted from this conjunction is
the final unconditional non-linearity assertion.  Its internal reduction is
machine checked; only the cited Double-Delta non-linearity fact remains
external.
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
    (Language ∩ FourBlockLanguage =
      DoubleDeltaLanguage)
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
  refine ⟨language_inter_fourBlock_eq_doubleDelta, ?_⟩
  exact
    deltaStar_fixedH_and_outside_all_fixedWindows


universe u w

/--
Paper-facing non-linearity reduction for Proposition 9.1.

Supplying the cited Double-Delta non-linearity fact in the repository's
finite raw-linear presentation form yields the Delta-star non-linearity
conclusion in the same form.  All other steps of the manuscript reduction
are discharged internally.
-/
theorem nonlinear_rs_example_nonlinearity_reduction
    (hDouble :
      ¬ RawLinearInitialRepresentable.{u, 0, w}
        DoubleDeltaLanguage) :
    ¬ RawLinearInitialRepresentable.{u, 0, w}
        Language :=
  deltaStar_not_rawLinearRepresentable_of_doubleDelta
    hDouble

end DeltaStar
end TCS1
end LeanCfgProject
