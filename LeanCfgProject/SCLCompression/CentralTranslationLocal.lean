import LeanCfgProject.SCLCompression.ReesMatrixLocal

namespace LeanCfgProject
namespace SCLCompression

universe u v w

namespace ReesMatrix

variable {I : Type u} {Lambda : Type v} {G : Type w} [Group G]
variable (D : ReesData I Lambda G)

/-- The local kernel induced on the distinguished maximal subgroup. -/
abbrev localKernel
    (tau : ReesMatrix D → ReesMatrix D → Prop)
    (htau : IsSemigroupCompatibleTolerance tau) : Subgroup G :=
  toleranceKernelSubgroup (barRelation D tau)
    (barRelation_isCompatibleTolerance D tau htau)

/--
Once row and column rigidity are known, every related pair differs by a unique
local central-translation parameter.  This is the algebraic core of
Corollary `cr:cor:local-translation`.
-/
theorem local_central_translation_form_core
    (tau : ReesMatrix D → ReesMatrix D → Prop)
    (htau : IsSemigroupCompatibleTolerance tau)
    {x y : ReesMatrix D} (hxy : tau x y)
    (hrow : x.row = y.row) (hcol : x.col = y.col) :
    ∃! n : G,
      n ∈ localKernel D tau htau ∧ y = centralTranslate D n x := by
  let K := localKernel D tau htau
  have hdef : x.group * y.group⁻¹ ∈ K := by
    exact left_defect_mem_kernel D tau htau hxy
  have hn : y.group * x.group⁻¹ ∈ K := by
    have hinv := K.inv_mem hdef
    simpa using hinv
  have htranslate :
      y = centralTranslate D (y.group * x.group⁻¹) x := by
    apply rees_ext D
    · exact hrow.symm
    · simp [centralTranslate, mul_assoc]
    · exact hcol.symm
  refine ⟨y.group * x.group⁻¹, ⟨hn, htranslate⟩, ?_⟩
  intro m hm
  exact centralTranslate_free D (hm.2.symm.trans htranslate)

/--
Corollary `cr:cor:local-translation` with the equalizing-context outputs left
explicit: the two rigidity equations imply the unique translation form.
-/
theorem local_central_translation_from_equalizing_core
    (tau : ReesMatrix D → ReesMatrix D → Prop)
    (htau : IsSemigroupCompatibleTolerance tau)
    {x y : ReesMatrix D} (hxy : tau x y)
    (hrowEq : x * e D = y * bar D (y.group⁻¹ * x.group))
    (hcolEq : e D * x = bar D (x.group * y.group⁻¹) * y) :
    ∃! n : G,
      n ∈ localKernel D tau htau ∧ y = centralTranslate D n x := by
  have hrig := local_index_rigidity_core D tau htau hxy hrowEq hcolEq
  exact local_central_translation_form_core D tau htau hxy hrig.1 hrig.2.1

/-- Freeness specialized to a fixed point: only the identity translation fixes it. -/
theorem centralTranslate_eq_self_iff (n : G) (x : ReesMatrix D) :
    centralTranslate D n x = x ↔ n = 1 := by
  constructor
  · intro h
    have h1 : centralTranslate D n x = centralTranslate D 1 x := by
      simpa using h
    exact centralTranslate_free D h1
  · intro hn
    subst hn
    exact centralTranslate_one D x

/-- Equality of two translates is equivalent to equality of their parameters. -/
theorem centralTranslate_eq_iff {m n : G} (x : ReesMatrix D) :
    centralTranslate D m x = centralTranslate D n x ↔ m = n := by
  constructor
  · exact centralTranslate_free D
  · intro h
    simpa [h]

end ReesMatrix

end SCLCompression
end LeanCfgProject
