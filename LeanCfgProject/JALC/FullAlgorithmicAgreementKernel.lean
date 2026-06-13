import LeanCfgProject.JALC.PaperFacingAlgorithmicFullBridge

namespace LeanCfgProject
namespace JALC
namespace FullAlgorithmicAgreementKernel

/-
Direct agreement between the full all-copy rule universe and Algorithm 1.

The rule data below is obtained directly from fullTypedStructure tau G.  The
main theorem says that a certified run of Algorithm 1 over this rule data
computes exactly FullKept tau G.
-/

universe u v w

open InverseKernel RoundTripKernel
open DerivationLiftKernel
open ReachableProductiveKernel
open FullRefinementKernel
open FullYieldKernel
open FullFrameReachabilityKernel FullKeptCorrectnessKernel
open ProductiveReachableClosureKernel
open AlgorithmicExtractionKernel AlgorithmicFullBridgeKernel


/-- Algorithm 1 rule data induced by the full all-copy typed refinement. -/
def fullExtractionRuleData
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    ExtractionRuleData (TypedState V M) :=
  { terminal := fun s =>
      ∃ a : Sigma,
        (fullTypedStructure tau G).terminal
          { lhs := s, terminal := a },
    binary := fun parent left right =>
      (fullTypedStructure tau G).binary
        { parent := parent, left := left, right := right },
    start := fun s =>
      (fullTypedStructure tau G).start { state := s } }


/--
The inductive typed productivity predicate is pre-fixed for the full rule data.
-/
theorem full_typedProductive_prefixed
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma) :
    FiniteClosureKernel.PredPreFixed
      (ProductiveStep
        (fullExtractionRuleData tau G).terminal
        (fullExtractionRuleData tau G).binary)
      (TypedProductive (fullTypedStructure tau G)) := by
  intro s h
  rcases h with hprod | hterm | hbin
  · exact hprod
  · rcases hterm with ⟨a, ht⟩
    exact ⟨[a], TypedRuleDeriv.terminal ht⟩
  · rcases hbin with ⟨y, z, hb, hy, hz⟩
    rcases hy with ⟨u, dy⟩
    rcases hz with ⟨v, dz⟩
    exact ⟨u ++ v, by
      simpa using (TypedRuleDeriv.binary hb dy dz)⟩


/--
The certified productive closure over the full rule data agrees with typed
productivity in fullTypedStructure.
-/
theorem full_computedProductive_agrees
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) :
    ∀ s : TypedState V M,
      computedProductive E s ↔
        TypedProductive (fullTypedStructure tau G) s := by
  intro s
  constructor
  · intro h
    exact
      computedProductive_least_prefixed E
        (full_typedProductive_prefixed tau G) s h
  · intro h
    rcases h with ⟨word, d⟩
    induction d with
    | terminal (r := r) ht =>
        have hstep :
            ProductiveStep
              (fullExtractionRuleData tau G).terminal
              (fullExtractionRuleData tau G).binary
              (computedProductive E) r.lhs := by
          exact Or.inr (Or.inl ⟨r.terminal, ht⟩)
        exact (computedProductive_fixed E r.lhs).1 hstep
    | binary (r := br) hb left right ihLeft ihRight =>
        have hstep :
            ProductiveStep
              (fullExtractionRuleData tau G).terminal
              (fullExtractionRuleData tau G).binary
              (computedProductive E) br.parent := by
          exact Or.inr (Or.inr ⟨br.left, br.right, hb, ihLeft, ihRight⟩)
        exact (computedProductive_fixed E br.parent).1 hstep


/--
Productive-part reachability in the full refinement is pre-fixed for the
computed productive predicate.
-/
theorem full_productiveReachable_prefixed
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) :
    FiniteClosureKernel.PredPreFixed
      (ReachableStep
        (fullExtractionRuleData tau G).start
        (fullExtractionRuleData tau G).binary
        (computedProductive E))
      (ProductiveReachableFull tau G) := by
  intro s h
  rcases h with hr | hs | hleft | hright
  · exact hr
  · rcases hs with ⟨_hp, hstart⟩
    exact ProductiveReachableFull.start hstart
  · rcases hleft with ⟨_hs, parent, right, hparent, hb, hrightProd⟩
    have hrightTyped :
        TypedProductive (fullTypedStructure tau G) right :=
      (full_computedProductive_agrees tau G E right).1 hrightProd
    exact ProductiveReachableFull.left hb hparent hrightTyped
  · rcases hright with ⟨_hs, parent, left, hparent, hb, hleftProd⟩
    have hleftTyped :
        TypedProductive (fullTypedStructure tau G) left :=
      (full_computedProductive_agrees tau G E left).1 hleftProd
    exact ProductiveReachableFull.right hb hparent hleftTyped


/--
Computed reachability is included in productive-part reachability of the full
typed refinement.
-/
theorem full_computedReachable_to_productiveReachable
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) :
    ∀ s : TypedState V M,
      computedReachable E s → ProductiveReachableFull tau G s := by
  intro s h
  exact
    computedReachable_least_prefixed E
      (full_productiveReachable_prefixed tau G E) s h


/-- A typed binary step with productive children gives a productive parent. -/
theorem full_parent_productive_of_children
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    {br : TypedBinaryRule V M}
    (hb : (fullTypedStructure tau G).binary br)
    (hleft :
      TypedProductive (fullTypedStructure tau G) br.left)
    (hright :
      TypedProductive (fullTypedStructure tau G) br.right) :
    TypedProductive (fullTypedStructure tau G) br.parent := by
  rcases hleft with ⟨u, du⟩
  rcases hright with ⟨v, dv⟩
  exact ⟨u ++ v, by
    simpa using (TypedRuleDeriv.binary hb du dv)⟩


/--
Productive-part reachability of a productive state is included in the computed
reachable predicate.
-/
theorem full_productiveReachable_to_computedReachable_of_productive
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) :
    ∀ {s : TypedState V M},
      ProductiveReachableFull tau G s →
      TypedProductive (fullTypedStructure tau G) s →
      computedReachable E s := by
  intro s hr
  induction hr with
  | start (r := sr) hs =>
      intro hp
      have hprod : computedProductive E sr.state :=
        (full_computedProductive_agrees tau G E sr.state).2 hp
      have hstep :
          ReachableStep
            (fullExtractionRuleData tau G).start
            (fullExtractionRuleData tau G).binary
            (computedProductive E)
            (computedReachable E) sr.state := by
        exact Or.inr (Or.inl ⟨hprod, hs⟩)
      exact (computedReachable_fixed E sr.state).1 hstep
  | left (r := br) hb parentReach rightProd ih =>
      intro hpLeft
      have hpParent :
          TypedProductive (fullTypedStructure tau G) br.parent :=
        full_parent_productive_of_children tau G hb hpLeft rightProd
      have hParentReach : computedReachable E br.parent := ih hpParent
      have hLeftComp : computedProductive E br.left :=
        (full_computedProductive_agrees tau G E br.left).2 hpLeft
      have hRightComp : computedProductive E br.right :=
        (full_computedProductive_agrees tau G E br.right).2 rightProd
      have hstep :
          ReachableStep
            (fullExtractionRuleData tau G).start
            (fullExtractionRuleData tau G).binary
            (computedProductive E)
            (computedReachable E) br.left := by
        exact Or.inr (Or.inr (Or.inl
          ⟨hLeftComp, br.parent, br.right, hParentReach, hb, hRightComp⟩))
      exact (computedReachable_fixed E br.left).1 hstep
  | right (r := br) hb parentReach leftProd ih =>
      intro hpRight
      have hpParent :
          TypedProductive (fullTypedStructure tau G) br.parent :=
        full_parent_productive_of_children tau G hb leftProd hpRight
      have hParentReach : computedReachable E br.parent := ih hpParent
      have hLeftComp : computedProductive E br.left :=
        (full_computedProductive_agrees tau G E br.left).2 leftProd
      have hRightComp : computedProductive E br.right :=
        (full_computedProductive_agrees tau G E br.right).2 hpRight
      have hstep :
          ReachableStep
            (fullExtractionRuleData tau G).start
            (fullExtractionRuleData tau G).binary
            (computedProductive E)
            (computedReachable E) br.right := by
        exact Or.inr (Or.inr (Or.inr
          ⟨hRightComp, br.parent, br.left, hParentReach, hb, hLeftComp⟩))
      exact (computedReachable_fixed E br.right).1 hstep


/--
A certified run of Algorithm 1 over the full all-copy rule data computes exactly
FullKept.
-/
theorem fullAlgorithmicComputedKept_agrees
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G)) :
    ComputedAgreesWithFullKept E tau G := by
  intro s
  constructor
  · intro h
    rcases h with ⟨hp, hr⟩
    exact ⟨
      (full_computedProductive_agrees tau G E s).1 hp,
      full_computedReachable_to_productiveReachable tau G E s hr⟩
  · intro h
    rcases h with ⟨hp, hr⟩
    exact ⟨
      (full_computedProductive_agrees tau G E s).2 hp,
      full_productiveReachable_to_computedReachable_of_productive
        tau G E hr hp⟩


/--
The previously conditional bridge is closed for the concrete full all-copy rule
data.
-/
theorem closed_algorithmic_full_bridge_kernel
    {V : Type u} {M : Type v} {Sigma : Type w}
    [Monoid M]
    (tau : Sigma → M)
    (G : UntypedStructure V Sigma)
    (E : CertifiedExtraction (fullExtractionRuleData tau G))
    (T : StateTyping V M)
    (comp : TypingCompatible tau T G)
    (sound : UntypedYieldSound tau T G)
    (red : UntypedReduced G) :
    AlgorithmicFullBridge E T tau G comp sound red
      (fullAlgorithmicComputedKept_agrees tau G E) :=
  algorithmic_full_bridge_kernel E T tau G comp sound red
    (fullAlgorithmicComputedKept_agrees tau G E)

end FullAlgorithmicAgreementKernel
end JALC
end LeanCfgProject
