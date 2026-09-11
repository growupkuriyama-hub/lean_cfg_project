import LeanCfgProject.SCLCompression.TupleContexts

namespace LeanCfgProject
namespace SCLCompression

universe u v

/-- A finite tuple-context profile over a monoid has `d+1` coordinates. -/
abbrev SyntacticContext (T : Type v) (d : Nat) := Fin (d + 1) → T

/-- Componentwise syntactic image of a tuple of words. -/
def tupleImage
    {Sigma : Type u} {T : Type v} [Monoid T]
    (eta : Word Sigma →* T) {d : Nat}
    (x : Tuple (Word Sigma) d) : Tuple T d :=
  fun i => eta (x i)

/-- Syntactic image of a concrete fixed-order tuple context. -/
def contextImage
    {Sigma : Type u} {T : Type v} [Monoid T]
    (eta : Word Sigma →* T) {d : Nat}
    (c : TupleContext Sigma d) : SyntacticContext T d :=
  fun j => eta (c j)

/--
Evaluate the finite monoid profile corresponding to
`q₀ s₁ q₁ ... s_d q_d`.
-/
def plugSyntacticContext
    {T : Type v} [Monoid T] {d : Nat}
    (q : SyntacticContext T d) (s : Tuple T d) : T :=
  (List.ofFn (fun i : Fin d => q i.castSucc * s i)).foldr (· * ·) (q (Fin.last d))

/-- The finite profile `Phi_d(s)` of the manuscript. -/
def FiniteProfile
    {T : Type v} [Monoid T] (P : Set T) {d : Nat}
    (s : Tuple T d) : Set (SyntacticContext T d) :=
  {q | plugSyntacticContext q s ∈ P}

/-- Unsafe syntactic tuple pair from Definition `U_d(T,P)`. -/
def SyntacticUnsafe
    {T : Type v} [Monoid T] (P : Set T) (d : Nat)
    (s t : Tuple T d) : Prop :=
  (FiniteProfile P s ∩ FiniteProfile P t).Nonempty ∧
    FiniteProfile P s ≠ FiniteProfile P t

/--
Choose concrete word representatives for every coordinate of an abstract
syntactic context.  Surjectivity of the syntactic morphism is the only input.
-/
noncomputable def liftContext
    {Sigma : Type u} {T : Type v} [Monoid T]
    (eta : Word Sigma →* T) (heta : Function.Surjective eta)
    {d : Nat} (q : SyntacticContext T d) : TupleContext Sigma d :=
  fun j => Classical.choose (heta (q j))

/-- Every abstract finite profile has a concrete tuple-context representative. -/
theorem contextImage_liftContext
    {Sigma : Type u} {T : Type v} [Monoid T]
    (eta : Word Sigma →* T) (heta : Function.Surjective eta)
    {d : Nat} (q : SyntacticContext T d) :
    contextImage eta (liftContext eta heta q) = q := by
  funext j
  exact Classical.choose_spec (heta (q j))

end SCLCompression
end LeanCfgProject
