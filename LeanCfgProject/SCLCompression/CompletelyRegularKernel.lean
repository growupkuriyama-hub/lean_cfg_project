import LeanCfgProject.SCLCompression.CompatibleTolerance

namespace LeanCfgProject
namespace SCLCompression

universe u

/--
Group-kernel form of the local kernel `N_beta` from the completely-regular
arity-two argument.  The ambient relation is only required to be a compatible
tolerance on the group multiplication.
-/
def toleranceKernelSubgroup
    {G : Type u} [Group G]
    (tau : G → G → Prop) (htau : IsCompatibleTolerance tau) : Subgroup G where
  carrier := {g | tau 1 g}
  one_mem' := htau.1 1
  mul_mem' := by
    intro a b ha hb
    have hmul := htau.2.2 (1 : G) a 1 b ha hb
    simpa using hmul
  inv_mem' := by
    intro a ha
    have hrefl : tau a⁻¹ a⁻¹ := htau.1 a⁻¹
    have hmul := htau.2.2 (1 : G) a a⁻¹ a⁻¹ ha hrefl
    have hback : tau a⁻¹ 1 := by
      simpa using hmul
    exact htau.2.1 a⁻¹ 1 hback

@[simp] theorem mem_toleranceKernelSubgroup_iff
    {G : Type u} [Group G]
    (tau : G → G → Prop) (htau : IsCompatibleTolerance tau) (g : G) :
    g ∈ toleranceKernelSubgroup tau htau ↔ tau 1 g := by
  rfl

/--
The local kernel is closed under conjugation.  Together with its subgroup
structure this is the normality assertion of Lemma `cr:lem:local-kernel`.
-/
theorem toleranceKernel_conj_mem
    {G : Type u} [Group G]
    (tau : G → G → Prop) (htau : IsCompatibleTolerance tau)
    {n : G} (hn : n ∈ toleranceKernelSubgroup tau htau) (g : G) :
    g * n * g⁻¹ ∈ toleranceKernelSubgroup tau htau := by
  change tau 1 (g * n * g⁻¹)
  have hg : tau g g := htau.1 g
  have hginv : tau g⁻¹ g⁻¹ := htau.1 g⁻¹
  have hleft : tau g (g * n) := by
    have hmul := htau.2.2 g g (1 : G) n hg hn
    simpa using hmul
  have hconj := htau.2.2 g (g * n) g⁻¹ g⁻¹ hleft hginv
  simpa [mul_assoc] using hconj

/-- Explicit normality criterion for the tolerance kernel. -/
theorem toleranceKernel_normality
    {G : Type u} [Group G]
    (tau : G → G → Prop) (htau : IsCompatibleTolerance tau) :
    ∀ n : G, n ∈ toleranceKernelSubgroup tau htau → ∀ g : G,
      g * n * g⁻¹ ∈ toleranceKernelSubgroup tau htau := by
  intro n hn g
  exact toleranceKernel_conj_mem tau htau hn g

/--
Binary-context rigidity specialized to a group.  This is the exact local
consequence of the manuscript's equalizing-context principle used in the proof
of Lemma `cr:lem:local-central`: coordinatewise related pairs with the same
empty-context product remain equal after inserting arbitrary fixed group
factors around and between the two coordinates.
-/
def BinaryContextRigid
    {G : Type u} [Group G] (tau : G → G → Prop) : Prop :=
  ∀ x₁ x₂ y₁ y₂ : G,
    tau x₁ y₁ → tau x₂ y₂ → x₁ * x₂ = y₁ * y₂ →
      ∀ q₀ q₁ q₂ : G,
        q₀ * x₁ * q₁ * x₂ * q₂ = q₀ * y₁ * q₁ * y₂ * q₂

/--
Local centrality, elementwise form.  If the binary equalizing-context
principle holds, every element of the tolerance kernel commutes with every
group element.
-/
theorem toleranceKernel_commutes
    {G : Type u} [Group G]
    (tau : G → G → Prop) (htau : IsCompatibleTolerance tau)
    (hrigid : BinaryContextRigid tau)
    {n : G} (hn : n ∈ toleranceKernelSubgroup tau htau) (g : G) :
    n * g = g * n := by
  have hninv : n⁻¹ ∈ toleranceKernelSubgroup tau htau :=
    (toleranceKernelSubgroup tau htau).inv_mem hn
  have hctx := hrigid (1 : G) 1 n n⁻¹ hn hninv (by simp) 1 g g⁻¹
  have hcommutator : (1 : G) = n * g * n⁻¹ * g⁻¹ := by
    simpa [mul_assoc] using hctx
  have hrightg := congrArg (fun z : G => z * g) hcommutator
  have hconj : g = n * g * n⁻¹ := by
    simpa [mul_assoc] using hrightg
  have hrightn := congrArg (fun z : G => z * n) hconj
  have hswap : g * n = n * g := by
    simpa [mul_assoc] using hrightn
  exact hswap.symm

/--
Local centrality in the subgroup form stated in the manuscript:
`N_beta ≤ Z(G_beta)`.
-/
theorem toleranceKernel_le_center
    {G : Type u} [Group G]
    (tau : G → G → Prop) (htau : IsCompatibleTolerance tau)
    (hrigid : BinaryContextRigid tau) :
    toleranceKernelSubgroup tau htau ≤ Subgroup.center G := by
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro g
  exact (toleranceKernel_commutes tau htau hrigid hn g).symm

end SCLCompression
end LeanCfgProject
