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

/--
Part (i) of Lemma `alg:lem:profile`: membership in a complete tuple
distribution is exactly membership of the syntactic context image in the finite
profile of the tuple image.
-/
theorem inTupleDistribution_iff_finiteProfile
    {Sigma : Type u} {T : Type v} [Monoid T]
    (L : Language Sigma) (eta : Word Sigma →* T) (P : Set T)
    (hL : ∀ w : Word Sigma, w ∈ L ↔ eta w ∈ P)
    {d : Nat} (x : Tuple (Word Sigma) d) (c : TupleContext Sigma d) :
    InTupleDistribution L x c ↔
      contextImage eta c ∈ FiniteProfile P (tupleImage eta x) := by
  unfold InTupleDistribution FiniteProfile
  rw [hL (plugTupleContext c x), map_plugTupleContext eta c x]
  rfl

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

/--
Part (ii) of Lemma `alg:lem:profile`: complete tuple distributions agree
exactly when the corresponding finite syntactic profiles agree.
-/
theorem sameTupleDistribution_iff_finiteProfile_eq
    {Sigma : Type u} {T : Type v} [Monoid T]
    (L : Language Sigma) (eta : Word Sigma →* T) (P : Set T)
    (hL : ∀ w : Word Sigma, w ∈ L ↔ eta w ∈ P)
    (heta : Function.Surjective eta)
    {d : Nat} (x y : Tuple (Word Sigma) d) :
    SameTupleDistribution L x y ↔
      FiniteProfile P (tupleImage eta x) =
        FiniteProfile P (tupleImage eta y) := by
  constructor
  · intro hsame
    apply Set.ext
    intro q
    have hc : contextImage eta (liftContext eta heta q) = q :=
      contextImage_liftContext eta heta q
    constructor
    · intro hqx
      have hxprof :
          contextImage eta (liftContext eta heta q) ∈
            FiniteProfile P (tupleImage eta x) := by
        rw [hc]
        exact hqx
      have hxmem : InTupleDistribution L x (liftContext eta heta q) :=
        (inTupleDistribution_iff_finiteProfile L eta P hL x
          (liftContext eta heta q)).mpr hxprof
      have hymem : InTupleDistribution L y (liftContext eta heta q) :=
        (hsame (liftContext eta heta q)).mp hxmem
      have hyprof :=
        (inTupleDistribution_iff_finiteProfile L eta P hL y
          (liftContext eta heta q)).mp hymem
      rw [hc] at hyprof
      exact hyprof
    · intro hqy
      have hyprof :
          contextImage eta (liftContext eta heta q) ∈
            FiniteProfile P (tupleImage eta y) := by
        rw [hc]
        exact hqy
      have hymem : InTupleDistribution L y (liftContext eta heta q) :=
        (inTupleDistribution_iff_finiteProfile L eta P hL y
          (liftContext eta heta q)).mpr hyprof
      have hxmem : InTupleDistribution L x (liftContext eta heta q) :=
        (hsame (liftContext eta heta q)).mpr hymem
      have hxprof :=
        (inTupleDistribution_iff_finiteProfile L eta P hL x
          (liftContext eta heta q)).mp hxmem
      rw [hc] at hxprof
      exact hxprof
  · intro hprof c
    constructor
    · intro hxmem
      have hxprof :=
        (inTupleDistribution_iff_finiteProfile L eta P hL x c).mp hxmem
      apply (inTupleDistribution_iff_finiteProfile L eta P hL y c).mpr
      rw [← hprof]
      exact hxprof
    · intro hymem
      have hyprof :=
        (inTupleDistribution_iff_finiteProfile L eta P hL y c).mp hymem
      apply (inTupleDistribution_iff_finiteProfile L eta P hL x c).mpr
      rw [hprof]
      exact hyprof

/--
Part (iii) of Lemma `alg:lem:profile`: two tuples share an accepting concrete
context exactly when their finite syntactic profiles intersect.
-/
theorem shareTupleContext_iff_finiteProfiles_inter_nonempty
    {Sigma : Type u} {T : Type v} [Monoid T]
    (L : Language Sigma) (eta : Word Sigma →* T) (P : Set T)
    (hL : ∀ w : Word Sigma, w ∈ L ↔ eta w ∈ P)
    (heta : Function.Surjective eta)
    {d : Nat} (x y : Tuple (Word Sigma) d) :
    ShareTupleContext L x y ↔
      (FiniteProfile P (tupleImage eta x) ∩
        FiniteProfile P (tupleImage eta y)).Nonempty := by
  constructor
  · rintro ⟨c, hxc, hyc⟩
    refine ⟨contextImage eta c, ?_⟩
    exact ⟨
      (inTupleDistribution_iff_finiteProfile L eta P hL x c).mp hxc,
      (inTupleDistribution_iff_finiteProfile L eta P hL y c).mp hyc⟩
  · rintro ⟨q, hqx, hqy⟩
    refine ⟨liftContext eta heta q, ?_, ?_⟩
    · apply (inTupleDistribution_iff_finiteProfile L eta P hL x
        (liftContext eta heta q)).mpr
      rw [contextImage_liftContext eta heta q]
      exact hqx
    · apply (inTupleDistribution_iff_finiteProfile L eta P hL y
        (liftContext eta heta q)).mpr
      rw [contextImage_liftContext eta heta q]
      exact hqy

/--
The semantic unsafe-pair relation is exactly carried to the finite syntactic
unsafe relation by the componentwise syntactic morphism.
-/
theorem semanticUnsafe_iff_syntacticUnsafe
    {Sigma : Type u} {T : Type v} [Monoid T]
    (L : Language Sigma) (eta : Word Sigma →* T) (P : Set T)
    (hL : ∀ w : Word Sigma, w ∈ L ↔ eta w ∈ P)
    (heta : Function.Surjective eta)
    (d : Nat) (x y : Tuple (Word Sigma) d) :
    SemanticUnsafe L d x y ↔
      SyntacticUnsafe P d (tupleImage eta x) (tupleImage eta y) := by
  unfold SemanticUnsafe SyntacticUnsafe
  have hshare :=
    shareTupleContext_iff_finiteProfiles_inter_nonempty L eta P hL heta x y
  have hsame :=
    sameTupleDistribution_iff_finiteProfile_eq L eta P hL heta x y
  constructor
  · rintro ⟨hshared, hnotSame⟩
    refine ⟨hshare.mp hshared, ?_⟩
    intro hprofiles
    exact hnotSame (hsame.mpr hprofiles)
  · rintro ⟨hinter, hprofilesNe⟩
    refine ⟨hshare.mpr hinter, ?_⟩
    intro hsameDist
    exact hprofilesNe (hsame.mp hsameDist)

end SCLCompression
end LeanCfgProject
