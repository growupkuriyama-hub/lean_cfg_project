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

/-- A monoid homomorphism transports a right-associated word concatenation fold. -/
theorem map_word_foldr
    {Sigma : Type u} {T : Type v} [Monoid T]
    (eta : Word Sigma →* T) (xs : List (Word Sigma)) (z : Word Sigma) :
    eta (xs.foldr (· ++ ·) z) =
      (xs.map eta).foldr (· * ·) (eta z) := by
  induction xs with
  | nil =>
      rfl
  | cons a tail ih =>
      change eta (a * tail.foldr (· ++ ·) z) =
        eta a * (tail.map eta).foldr (· * ·) (eta z)
      rw [eta.map_mul, ih]

/--
Part (i), algebraic core, of Lemma `alg:lem:profile`: applying `eta` after
plugging a concrete tuple context is exactly the finite monoid profile product.
-/
theorem map_plugTupleContext
    {Sigma : Type u} {T : Type v} [Monoid T]
    (eta : Word Sigma →* T) {d : Nat}
    (c : TupleContext Sigma d) (x : Tuple (Word Sigma) d) :
    eta (plugTupleContext c x) =
      plugSyntacticContext (contextImage eta c) (tupleImage eta x) := by
  unfold plugTupleContext plugSyntacticContext contextImage tupleImage
  rw [map_word_foldr eta]
  have hlist :
      (List.ofFn (fun i : Fin d => c i.castSucc ++ x i)).map eta =
        List.ofFn (fun i : Fin d => eta (c i.castSucc) * eta (x i)) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    change eta (c i.castSucc * x i) = eta (c i.castSucc) * eta (x i)
    exact eta.map_mul _ _
  rw [hlist]

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
