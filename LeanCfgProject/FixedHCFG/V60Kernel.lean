import LeanCfgProject.FixedHCFG.Observer
import LeanCfgProject.FixedHCFG.Language

namespace LeanCfgProject
namespace FixedHCFG

universe u

/-!
Exact v60 kernel for the finite-sample reconstruction operator.

The earlier fixed-h Lean development used a stronger substitutability predicate
quantifying also over the empty word and a learner kernel whose observed factor
was not explicitly required to be nonempty.  The v60 manuscript instead uses
only internal factors in `Sigma+` and handles epsilon solely at the start
symbol.  This file mirrors that convention literally.
-/

/-- Fixed-h substitutability exactly in the v60 nonempty-factor convention. -/
def HSubstitutableV60 {Sigma : Type u} (Obs : Observer Sigma)
    (L : Language Sigma) : Prop :=
  ∀ x y : Word Sigma,
    x ≠ [] → y ≠ [] →
    Obs.value x = Obs.value y →
    ShareContext L x y →
    SameDistribution L x y

/-- A v60 learner nonterminal `[x:u,v]`; nonemptiness is enforced by visibility. -/
structure V60LearnerNT (Sigma : Type u) where
  x : Word Sigma
  u : Word Sigma
  v : Word Sigma

/-- `q` belongs to `V-hat(K)` exactly when its factor is nonempty and `uxv ∈ K`. -/
def VisibleV60 {Sigma : Type u} (K : Language Sigma)
    (q : V60LearnerNT Sigma) : Prop :=
  q.x ≠ [] ∧ q.u ++ q.x ++ q.v ∈ K

/-- Rules (R1)--(R4) of the v60 batch grammar. -/
inductive V60Derives {Sigma : Type u} (Obs : Observer Sigma)
    (K : Language Sigma) : V60LearnerNT Sigma → Word Sigma → Prop
  | terminal (a : Sigma) (u v : Word Sigma)
      (hvis : VisibleV60 K { x := [a], u := u, v := v }) :
      V60Derives Obs K { x := [a], u := u, v := v } [a]
  | contextTransport (x u v u' v' w : Word Sigma)
      (hsrc : VisibleV60 K { x := x, u := u, v := v })
      (hdst : VisibleV60 K { x := x, u := u', v := v' })
      (hder : V60Derives Obs K { x := x, u := u', v := v' } w) :
      V60Derives Obs K { x := x, u := u, v := v } w
  | typedSubstitution (x x' u v w : Word Sigma)
      (hsrc : VisibleV60 K { x := x, u := u, v := v })
      (hdst : VisibleV60 K { x := x', u := u, v := v })
      (htype : Obs.value x = Obs.value x')
      (hder : V60Derives Obs K { x := x', u := u, v := v } w) :
      V60Derives Obs K { x := x, u := u, v := v } w
  | split (x y u v w₁ w₂ : Word Sigma)
      (hparent : VisibleV60 K { x := x ++ y, u := u, v := v })
      (hleft : VisibleV60 K { x := x, u := u, v := y ++ v })
      (hright : VisibleV60 K { x := y, u := u ++ x, v := v })
      (hder₁ : V60Derives Obs K { x := x, u := u, v := y ++ v } w₁)
      (hder₂ : V60Derives Obs K { x := y, u := u ++ x, v := v } w₂) :
      V60Derives Obs K { x := x ++ y, u := u, v := v } (w₁ ++ w₂)

/-- Rule (R5), with epsilon handled only at the start symbol. -/
inductive V60StartDerives {Sigma : Type u} (Obs : Observer Sigma)
    (K : Language Sigma) : Word Sigma → Prop
  | epsilon (hmem : ([] : Word Sigma) ∈ K) :
      V60StartDerives Obs K []
  | sample (x w : Word Sigma)
      (hx : x ≠ [])
      (hmem : x ∈ K)
      (hder : V60Derives Obs K { x := x, u := [], v := [] } w) :
      V60StartDerives Obs K w

/-- Strong v60 soundness invariant, including nonemptiness of every internal yield. -/
theorem v60_derives_sound
    {Sigma : Type u}
    (Obs : Observer Sigma)
    (K L : Language Sigma)
    (hKL : K ⊆ L)
    (hSub : HSubstitutableV60 Obs L)
    {q : V60LearnerNT Sigma} {w : Word Sigma}
    (hder : V60Derives Obs K q w) :
    q.u ++ w ++ q.v ∈ L ∧
      Obs.value w = Obs.value q.x ∧
      w ≠ [] := by
  induction hder with
  | terminal a u v hvis =>
      exact ⟨hKL hvis.2, rfl, by simp⟩
  | contextTransport x u v u' v' w hsrc hdst htail ih =>
      rcases ih with ⟨hmem, hval, hwne⟩
      have hshare : ShareContext L x w := by
        refine ⟨u', v', ?_, ?_⟩
        · exact hKL hdst.2
        · exact hmem
      have hdist : SameDistribution L x w :=
        hSub x w hsrc.1 hwne hval.symm hshare
      exact ⟨(hdist u v).mp (hKL hsrc.2), hval, hwne⟩
  | typedSubstitution x x' u v w hsrc hdst htype htail ih =>
      rcases ih with ⟨hmem, hval, hwne⟩
      exact ⟨hmem, hval.trans htype.symm, hwne⟩
  | split x y u v w₁ w₂ hparent hleft hright hder₁ hder₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨hmem₁, hval₁, hw₁ne⟩
      rcases ih₂ with ⟨hmem₂, hval₂, hw₂ne⟩
      have hxCommon : InDistribution L x u (y ++ v) := by
        change u ++ x ++ (y ++ v) ∈ L
        simpa [List.append_assoc] using hKL hparent.2
      have hwCommon : InDistribution L w₁ u (y ++ v) := by
        change u ++ w₁ ++ (y ++ v) ∈ L
        simpa [List.append_assoc] using hmem₁
      have hshare : ShareContext L x w₁ :=
        ⟨u, y ++ v, hxCommon, hwCommon⟩
      have hdist : SameDistribution L x w₁ :=
        hSub x w₁ hleft.1 hw₁ne hval₁.symm hshare
      have hxSecond : InDistribution L x u (w₂ ++ v) := by
        change u ++ x ++ (w₂ ++ v) ∈ L
        simpa [List.append_assoc] using hmem₂
      have hwSecond : InDistribution L w₁ u (w₂ ++ v) :=
        (hdist u (w₂ ++ v)).mp hxSecond
      have hword : u ++ (w₁ ++ w₂) ++ v ∈ L := by
        change u ++ w₁ ++ (w₂ ++ v) ∈ L at hwSecond
        simpa [List.append_assoc] using hwSecond
      have htype : Obs.value (w₁ ++ w₂) = Obs.value (x ++ y) := by
        calc
          Obs.value (w₁ ++ w₂) = Obs.mul (Obs.value w₁) (Obs.value w₂) :=
            Obs.value_append w₁ w₂
          _ = Obs.mul (Obs.value x) (Obs.value y) := by rw [hval₁, hval₂]
          _ = Obs.value (x ++ y) := (Obs.value_append x y).symm
      have hwne : w₁ ++ w₂ ≠ [] := by
        intro hnil
        cases w₁ with
        | nil => exact hw₁ne rfl
        | cons a as => simp at hnil
      exact ⟨hword, htype, hwne⟩

/-- Theorem `soundness` of v60 for the exact nonempty-factor kernel. -/
theorem v60_start_soundness
    {Sigma : Type u}
    (Obs : Observer Sigma)
    (K L : Language Sigma)
    (hKL : K ⊆ L)
    (hSub : HSubstitutableV60 Obs L)
    {w : Word Sigma}
    (hstart : V60StartDerives Obs K w) :
    w ∈ L := by
  cases hstart with
  | epsilon hmem => exact hKL hmem
  | sample x w hx hmem hder =>
      have hs := v60_derives_sound Obs K L hKL hSub hder
      simpa using hs.1

/-- Every visible nonempty observed factor derives itself. -/
theorem v60_visible_self_derives
    {Sigma : Type u} (Obs : Observer Sigma) (K : Language Sigma) :
    ∀ (x u v : Word Sigma),
      VisibleV60 K { x := x, u := u, v := v } →
      V60Derives Obs K { x := x, u := u, v := v } x := by
  intro x
  induction x with
  | nil =>
      intro u v hvis
      exact (hvis.1 rfl).elim
  | cons a xs ih =>
      intro u v hvis
      cases xs with
      | nil =>
          exact V60Derives.terminal a u v (by simpa using hvis)
      | cons b bs =>
          let y : Word Sigma := b :: bs
          have hleft : VisibleV60 K
              { x := [a], u := u, v := y ++ v } := by
            constructor
            · simp
            · simpa [VisibleV60, y, List.append_assoc] using hvis.2
          have hright : VisibleV60 K
              { x := y, u := u ++ [a], v := v } := by
            constructor
            · simp [y]
            · simpa [VisibleV60, y, List.append_assoc] using hvis.2
          have dleft : V60Derives Obs K
              { x := [a], u := u, v := y ++ v } [a] :=
            V60Derives.terminal a u (y ++ v) hleft
          have dright : V60Derives Obs K
              { x := y, u := u ++ [a], v := v } y :=
            ih (u ++ [a]) v hright
          have hparent : VisibleV60 K
              { x := [a] ++ y, u := u, v := v } := by
            simpa [y] using hvis
          have dsplit := V60Derives.split [a] y u v [a] y
            hparent hleft hright dleft dright
          simpa [y] using dsplit

/-- Lemma `sample-consistency` for the exact v60 kernel. -/
theorem v60_sample_consistency
    {Sigma : Type u} (Obs : Observer Sigma) (K : Language Sigma) :
    K ⊆ fun w => V60StartDerives Obs K w := by
  intro w hw
  by_cases hnil : w = []
  · subst w
    exact V60StartDerives.epsilon hw
  · have hvis : VisibleV60 K { x := w, u := [], v := [] } := by
      exact ⟨hnil, by simpa using hw⟩
    exact V60StartDerives.sample w w hnil hw
      (v60_visible_self_derives Obs K w [] [] hvis)

/-- Visibility is monotone in the positive sample. -/
theorem visibleV60_mono
    {Sigma : Type u} {K K' : Language Sigma}
    (hKK' : K ⊆ K') {q : V60LearnerNT Sigma}
    (hq : VisibleV60 K q) : VisibleV60 K' q :=
  ⟨hq.1, hKK' hq.2⟩

/-- The batch grammar is monotone under sample inclusion, as stated in v60. -/
theorem v60_derives_mono
    {Sigma : Type u} (Obs : Observer Sigma)
    {K K' : Language Sigma} (hKK' : K ⊆ K')
    {q : V60LearnerNT Sigma} {w : Word Sigma}
    (hder : V60Derives Obs K q w) :
    V60Derives Obs K' q w := by
  induction hder with
  | terminal a u v hvis =>
      exact V60Derives.terminal a u v (visibleV60_mono hKK' hvis)
  | contextTransport x u v u' v' w hsrc hdst htail ih =>
      exact V60Derives.contextTransport x u v u' v' w
        (visibleV60_mono hKK' hsrc) (visibleV60_mono hKK' hdst) ih
  | typedSubstitution x x' u v w hsrc hdst htype htail ih =>
      exact V60Derives.typedSubstitution x x' u v w
        (visibleV60_mono hKK' hsrc) (visibleV60_mono hKK' hdst) htype ih
  | split x y u v w₁ w₂ hparent hleft hright hder₁ hder₂ ih₁ ih₂ =>
      exact V60Derives.split x y u v w₁ w₂
        (visibleV60_mono hKK' hparent)
        (visibleV60_mono hKK' hleft)
        (visibleV60_mono hKK' hright) ih₁ ih₂

/-- Monotonicity of the v60 batch hypothesis language. -/
theorem v60_start_derives_mono
    {Sigma : Type u} (Obs : Observer Sigma)
    {K K' : Language Sigma} (hKK' : K ⊆ K')
    {w : Word Sigma}
    (hder : V60StartDerives Obs K w) :
    V60StartDerives Obs K' w := by
  cases hder with
  | epsilon hmem =>
      exact V60StartDerives.epsilon (hKK' hmem)
  | sample x w hx hmem htail =>
      exact V60StartDerives.sample x w hx (hKK' hmem)
        (v60_derives_mono Obs hKK' htail)

end FixedHCFG
end LeanCfgProject
