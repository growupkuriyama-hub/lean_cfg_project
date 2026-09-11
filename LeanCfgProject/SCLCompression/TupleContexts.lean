import LeanCfgProject.SCLCompression.SafetyInterface

namespace LeanCfgProject
namespace SCLCompression

universe u v

/-- Words are lists over the terminal alphabet. -/
abbrev Word (Σ : Type u) := List Σ

/-- A language over `Σ`. -/
abbrev Language (Σ : Type u) := Set (Word Σ)

/-- A fixed-order Clark--Wurm tuple context has `d+1` word gaps. -/
abbrev TupleContext (Σ : Type u) (d : Nat) := Fin (d + 1) → Word Σ

/--
Fill a fixed-order tuple context
`u₀ □₁ u₁ ... □d u_d` with a `d`-tuple of words.
-/
def plugTupleContext {Σ : Type u} {d : Nat}
    (c : TupleContext Σ d) (x : Tuple (Word Σ) d) : Word Σ :=
  (List.ofFn (fun i : Fin d => c i.castSucc ++ x i)).foldr (· ++ ·) (c (Fin.last d))

/-- Membership of a context in the complete tuple distribution. -/
def InTupleDistribution {Σ : Type u} (L : Language Σ) {d : Nat}
    (x : Tuple (Word Σ) d) (c : TupleContext Σ d) : Prop :=
  plugTupleContext c x ∈ L

/-- Equality of complete Clark--Wurm tuple distributions. -/
def SameTupleDistribution {Σ : Type u} (L : Language Σ) {d : Nat}
    (x y : Tuple (Word Σ) d) : Prop :=
  ∀ c : TupleContext Σ d,
    InTupleDistribution L x c ↔ InTupleDistribution L y c

/-- Two tuples share at least one accepting fixed-order tuple context. -/
def ShareTupleContext {Σ : Type u} (L : Language Σ) {d : Nat}
    (x y : Tuple (Word Σ) d) : Prop :=
  ∃ c : TupleContext Σ d,
    InTupleDistribution L x c ∧ InTupleDistribution L y c

/-- Semantic unsafe pair `𝔘_d(L)` from the manuscript. -/
def SemanticUnsafe {Σ : Type u} (L : Language Σ) (d : Nat)
    (x y : Tuple (Word Σ) d) : Prop :=
  ShareTupleContext L x y ∧ ¬ SameTupleDistribution L x y

/-- Shared-context family in the abstract Safety Interface kernel. -/
def SharedFamily {Σ : Type u} (L : Language Σ) :
    (d : Nat) → Tuple (Word Σ) d → Tuple (Word Σ) d → Prop :=
  fun _ x y => ShareTupleContext L x y

/-- Distribution-equality family in the abstract Safety Interface kernel. -/
def EqualDistFamily {Σ : Type u} (L : Language Σ) :
    (d : Nat) → Tuple (Word Σ) d → Tuple (Word Σ) d → Prop :=
  fun _ x y => SameTupleDistribution L x y

@[simp] theorem unsafe_family_iff_semanticUnsafe {Σ : Type u}
    (L : Language Σ) (d : Nat) (x y : Tuple (Word Σ) d) :
    Unsafe (SharedFamily L) (EqualDistFamily L) d x y ↔ SemanticUnsafe L d x y := by
  rfl

/--
Concrete condition (ii) of the Safety Interface Theorem, using a finite-monoid
homomorphism as the observer.
-/
def WordContextSafeThrough {Σ : Type u} {M : Type v} [Monoid M]
    (L : Language Σ) (h : Word Σ →* M) (f : Nat) : Prop :=
  GuardedSafeThrough (SharedFamily L) (EqualDistFamily L) h f

/-- Concrete condition (iii): every semantic unsafe pair is separated. -/
def SemanticSeparationThrough {Σ : Type u} {M : Type v} [Monoid M]
    (L : Language Σ) (h : Word Σ →* M) (f : Nat) : Prop :=
  SeparatesUnsafeThrough (SharedFamily L) (EqualDistFamily L) h f

/-- Concrete conditions (ii) and (iii) are exactly equivalent. -/
theorem wordContextSafe_iff_semanticSeparation
    {Σ : Type u} {M : Type v} [Monoid M]
    (L : Language Σ) (h : Word Σ →* M) (f : Nat) :
    WordContextSafeThrough L h f ↔ SemanticSeparationThrough L h f := by
  exact guardedSafe_iff_separatesUnsafe (SharedFamily L) (EqualDistFamily L) h f

/-- The concrete kernel-congruence interface, abstracting condition (iv). -/
def KernelSeparationThrough {Σ : Type u} {M : Type v} [Monoid M]
    (L : Language Σ) (h : Word Σ →* M) (f : Nat) : Prop :=
  RelationSeparatesUnsafeThrough (SharedFamily L) (EqualDistFamily L) (KernelRel h) f

/-- Concrete conditions (ii)--(iv) of the Safety Interface Theorem coincide. -/
theorem wordContextSafe_iff_kernelSeparation
    {Σ : Type u} {M : Type v} [Monoid M]
    (L : Language Σ) (h : Word Σ →* M) (f : Nat) :
    WordContextSafeThrough L h f ↔ KernelSeparationThrough L h f := by
  exact safety_kernel_dictionary (SharedFamily L) (EqualDistFamily L) h f

end SCLCompression
end LeanCfgProject
