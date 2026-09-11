import LeanCfgProject.SCLCompression.FiniteProfiles
import LeanCfgProject.SCLCompression.CompatibleTolerance

namespace LeanCfgProject
namespace SCLCompression

universe u

/--
Point-separation property of a pointed monoid `(T,P)`: distinct elements can
be distinguished by a two-sided context.  This is the abstract form of the
manuscript's syntactic property (Syn).
-/
def PointedSyntacticSeparation
    {T : Type u} [Monoid T] (P : Set T) : Prop :=
  ∀ s t : T, s ≠ t → ∃ a b : T,
    (a * s * b ∈ P) ≠ (a * t * b ∈ P)

/-- Multiply the first gap of a syntactic tuple context on the left. -/
def leftWrapSyntacticContext
    {T : Type u} [Monoid T] {d : Nat}
    (a : T) (q : SyntacticContext T d) : SyntacticContext T d :=
  fun j => if j = 0 then a * q j else q j

/-- Multiply the final gap of a syntactic tuple context on the right. -/
def rightWrapSyntacticContext
    {T : Type u} [Monoid T] {d : Nat}
    (q : SyntacticContext T d) (b : T) : SyntacticContext T d :=
  fun j => if j = Fin.last d then q j * b else q j

/-- Two-sided wrapping of a syntactic tuple context. -/
def wrapSyntacticContext
    {T : Type u} [Monoid T] {d : Nat}
    (a : T) (q : SyntacticContext T d) (b : T) : SyntacticContext T d :=
  rightWrapSyntacticContext (leftWrapSyntacticContext a q) b

/-- Moving a fixed right factor through a right-associated multiplication fold. -/
theorem foldr_mul_seed_right
    {T : Type u} [Monoid T] (xs : List T) (z b : T) :
    xs.foldr (· * ·) (z * b) = xs.foldr (· * ·) z * b := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [ih, mul_assoc]

/-- Right wrapping multiplies the value of every tuple substitution on the right. -/
theorem plug_rightWrapSyntacticContext
    {T : Type u} [Monoid T] {d : Nat}
    (q : SyntacticContext T d) (s : Tuple T d) (b : T) :
    plugSyntacticContext (rightWrapSyntacticContext q b) s =
      plugSyntacticContext q s * b := by
  unfold plugSyntacticContext rightWrapSyntacticContext
  have hlist :
      List.ofFn (fun i : Fin d =>
        (if i.castSucc = Fin.last d then q i.castSucc * b else q i.castSucc) * s i) =
      List.ofFn (fun i : Fin d => q i.castSucc * s i) := by
    apply congrArg List.ofFn
    funext i
    simp [Fin.castSucc_ne_last]
  rw [hlist]
  simp only [if_pos]
  exact foldr_mul_seed_right _ _ _

/-- For positive arity, left wrapping multiplies every tuple substitution on the left. -/
theorem plug_leftWrapSyntacticContext
    {T : Type u} [Monoid T] {d : Nat}
    (hd : 1 ≤ d) (a : T) (q : SyntacticContext T d) (s : Tuple T d) :
    plugSyntacticContext (leftWrapSyntacticContext a q) s =
      a * plugSyntacticContext q s := by
  cases d with
  | zero =>
      omega
  | succ n =>
      unfold plugSyntacticContext leftWrapSyntacticContext
      simp [List.ofFn_succ, mul_assoc]

/-- Two-sided wrapping realizes ordinary multiplication by fixed outer factors. -/
theorem plug_wrapSyntacticContext
    {T : Type u} [Monoid T] {d : Nat}
    (hd : 1 ≤ d) (a : T) (q : SyntacticContext T d) (b : T)
    (s : Tuple T d) :
    plugSyntacticContext (wrapSyntacticContext a q b) s =
      a * plugSyntacticContext q s * b := by
  unfold wrapSyntacticContext
  rw [plug_rightWrapSyntacticContext]
  rw [plug_leftWrapSyntacticContext hd]

/-- Two tuples share an accepting finite syntactic context. -/
def ShareAcceptingSyntacticContext
    {T : Type u} [Monoid T] (P : Set T) {d : Nat}
    (s t : Tuple T d) : Prop :=
  ∃ q : SyntacticContext T d,
    plugSyntacticContext q s ∈ P ∧ plugSyntacticContext q t ∈ P

/--
A safe compatible tolerance cannot distinguish the finite profiles of two
coordinatewise-related tuples once they share an accepting context.
-/
theorem safe_shared_implies_finiteProfile_eq
    {T : Type u} [Monoid T]
    (P : Set T) (tau : T → T → Prop) (f d : Nat)
    (hsafe : ToleranceSafeThrough (SyntacticUnsafe P) tau f)
    (hdpos : 1 ≤ d) (hdf : d ≤ f)
    (s t : Tuple T d)
    (hcoord : ∀ i, tau (s i) (t i))
    (hshared : ShareAcceptingSyntacticContext P s t) :
    FiniteProfile P s = FiniteProfile P t := by
  by_contra hne
  rcases hshared with ⟨q, hqs, hqt⟩
  have hunsafe : SyntacticUnsafe P d s t := by
    exact ⟨⟨q, hqs, hqt⟩, hne⟩
  obtain ⟨i, hi⟩ := hsafe d hdpos hdf s t hunsafe
  exact hi (hcoord i)

/--
Syntactic-lifting principle from the completely-regular section: under (Syn),
safety upgrades equality of finite profiles to equality of the actual
syntactic values produced by every tuple context.
-/
theorem syntacticLifting
    {T : Type u} [Monoid T]
    (P : Set T) (tau : T → T → Prop) (f d : Nat)
    (hSyn : PointedSyntacticSeparation P)
    (hsafe : ToleranceSafeThrough (SyntacticUnsafe P) tau f)
    (hdpos : 1 ≤ d) (hdf : d ≤ f)
    (s t : Tuple T d)
    (hcoord : ∀ i, tau (s i) (t i))
    (hshared : ShareAcceptingSyntacticContext P s t)
    (F : SyntacticContext T d) :
    plugSyntacticContext F s = plugSyntacticContext F t := by
  classical
  have hprofile := safe_shared_implies_finiteProfile_eq
    P tau f d hsafe hdpos hdf s t hcoord hshared
  by_contra hne
  obtain ⟨a, b, hab⟩ := hSyn
    (plugSyntacticContext F s) (plugSyntacticContext F t) hne
  let W := wrapSyntacticContext a F b
  have hmem :
      (plugSyntacticContext W s ∈ P) ↔ (plugSyntacticContext W t ∈ P) := by
    change W ∈ FiniteProfile P s ↔ W ∈ FiniteProfile P t
    rw [hprofile]
  have hws := plug_wrapSyntacticContext hdpos a F b s
  have hwt := plug_wrapSyntacticContext hdpos a F b t
  rw [hws, hwt] at hmem
  exact hab (propext hmem)

/--
Equalizing-context principle, abstracting Lemma `cr:lem:equalizing-context`.
The sandwich-ideal argument of the manuscript is represented by the explicit
outer factors `a,b` sending the common value `c` into `P`.
-/
theorem equalizingContextPrinciple
    {T : Type u} [Monoid T]
    (P : Set T) (tau : T → T → Prop) (f d : Nat)
    (hSyn : PointedSyntacticSeparation P)
    (hsafe : ToleranceSafeThrough (SyntacticUnsafe P) tau f)
    (hdpos : 1 ≤ d) (hdf : d ≤ f)
    (s t : Tuple T d)
    (hcoord : ∀ i, tau (s i) (t i))
    (E0 : SyntacticContext T d) (c a b : T)
    (hs0 : plugSyntacticContext E0 s = c)
    (ht0 : plugSyntacticContext E0 t = c)
    (haccept : a * c * b ∈ P)
    (F : SyntacticContext T d) :
    plugSyntacticContext F s = plugSyntacticContext F t := by
  have hshared : ShareAcceptingSyntacticContext P s t := by
    refine ⟨wrapSyntacticContext a E0 b, ?_, ?_⟩
    · rw [plug_wrapSyntacticContext hdpos, hs0]
      exact haccept
    · rw [plug_wrapSyntacticContext hdpos, ht0]
      exact haccept
  exact syntacticLifting P tau f d hSyn hsafe hdpos hdf s t hcoord hshared F

end SCLCompression
end LeanCfgProject
