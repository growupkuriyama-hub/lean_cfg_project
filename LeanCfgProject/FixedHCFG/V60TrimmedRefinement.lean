import LeanCfgProject.FixedHCFG.V60TypedRefinement

namespace LeanCfgProject
namespace FixedHCFG

universe u v

/-!
Successful-occurrence trimming for the v60 yield-only refinement.

A retained typed state is productive and occurs in some successful typed start
derivation.  This realizes the manuscript's trim without introducing the old
left/right monoid annotations.
-/

/--
A yield-typed state occurring with concrete terminal context in a successful
start derivation.
-/
inductive V60TypedOccurs {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N) :
    V60TypedNT N Obs → Word Sigma → Word Sigma → Prop
  | start {A : N} {p : Obs.M}
      (hrule : start A) :
      V60TypedOccurs Obs terminal binary start
        { label := A, yieldType := p } [] []
  | left {A B C : N} {p q r : Obs.M} {u v y : Word Sigma}
      (parent : V60TypedOccurs Obs terminal binary start
        { label := A, yieldType := p } u v)
      (hrule : binary A B C)
      (hproduct : Obs.mul q r = p)
      (rightDeriv : V60YieldTypedDerives Obs terminal binary
        { label := C, yieldType := r } y) :
      V60TypedOccurs Obs terminal binary start
        { label := B, yieldType := q } u (y ++ v)
  | right {A B C : N} {p q r : Obs.M} {u v x : Word Sigma}
      (parent : V60TypedOccurs Obs terminal binary start
        { label := A, yieldType := p } u v)
      (hrule : binary A B C)
      (hproduct : Obs.mul q r = p)
      (leftDeriv : V60YieldTypedDerives Obs terminal binary
        { label := B, yieldType := q } x) :
      V60TypedOccurs Obs terminal binary start
        { label := C, yieldType := r } (u ++ x) v

/-- A state survives the trim iff it is productive and has a successful terminal occurrence. -/
def V60TypedKept {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (X : V60TypedNT N Obs) : Prop :=
  (∃ w : Word Sigma, V60YieldTypedDerives Obs terminal binary X w) ∧
    ∃ u v : Word Sigma, V60TypedOccurs Obs terminal binary start X u v

/-- Non-start symbols of the trimmed yield-only refinement. -/
abbrev V60KeptState {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N) :=
  {X : V60TypedNT N Obs // V60TypedKept Obs terminal binary start X}

/-- A retained terminal production. -/
def V60KeptTerminal {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) (a : Sigma) : Prop :=
  terminal X.1.label a ∧ Obs.value [a] = X.1.yieldType

/-- A retained binary production. -/
def V60KeptBinary {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X Y Z : V60KeptState Obs terminal binary start) : Prop :=
  binary X.1.label Y.1.label Z.1.label ∧
    Obs.mul Y.1.yieldType Z.1.yieldType = X.1.yieldType

/-- A retained state accessible directly from the isolated start symbol. -/
def V60KeptStart {N : Type v} {Sigma : Type u}
    {Obs : Observer Sigma}
    {terminal : V60TerminalRules N Sigma}
    {binary : V60BinaryRules N} {start : V60StartRules N}
    (X : V60KeptState Obs terminal binary start) : Prop :=
  start X.1.label

/-- Derivations in the trimmed yield-only refinement. -/
inductive V60KeptDerives {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N) :
    V60KeptState Obs terminal binary start → Word Sigma → Prop
  | terminal {X : V60KeptState Obs terminal binary start} {a : Sigma}
      (hrule : V60KeptTerminal X a) :
      V60KeptDerives Obs terminal binary start X [a]
  | binary {X Y Z : V60KeptState Obs terminal binary start}
      {x y : Word Sigma}
      (hrule : V60KeptBinary X Y Z)
      (left : V60KeptDerives Obs terminal binary start Y x)
      (right : V60KeptDerives Obs terminal binary start Z y) :
      V60KeptDerives Obs terminal binary start X (x ++ y)

/-- Forgetting trim witnesses yields an ordinary full-refinement derivation. -/
theorem v60_kept_derivation_to_typed
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    {X : V60KeptState Obs terminal binary start} {w : Word Sigma}
    (d : V60KeptDerives Obs terminal binary start X w) :
    V60YieldTypedDerives Obs terminal binary X.1 w := by
  induction d with
  | terminal hrule =>
      exact V60YieldTypedDerives.terminal hrule.1 hrule.2
  | binary hrule left right ihLeft ihRight =>
      exact V60YieldTypedDerives.binary hrule.1 hrule.2 ihLeft ihRight

/-- Every successful typed derivation from a retained root survives in the trimmed grammar. -/
theorem v60_typed_derivation_to_kept
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    {X : V60TypedNT N Obs} {w : Word Sigma}
    (hKeep : V60TypedKept Obs terminal binary start X)
    (d : V60YieldTypedDerives Obs terminal binary X w) :
    V60KeptDerives Obs terminal binary start ⟨X, hKeep⟩ w := by
  induction d with
  | @terminal A a p hrule htype =>
      exact V60KeptDerives.terminal ⟨hrule, htype⟩
  | @binary A B C p q r x y hrule hproduct left right ihLeft ihRight =>
      rcases hKeep.2 with ⟨u, v, hOcc⟩
      have hLeftKeep : V60TypedKept Obs terminal binary start
          { label := B, yieldType := q } := by
        constructor
        · exact ⟨x, left⟩
        · exact ⟨u, y ++ v,
            V60TypedOccurs.left hOcc hrule hproduct right⟩
      have hRightKeep : V60TypedKept Obs terminal binary start
          { label := C, yieldType := r } := by
        constructor
        · exact ⟨y, right⟩
        · exact ⟨u ++ x, v,
            V60TypedOccurs.right hOcc hrule hproduct left⟩
      let Y : V60KeptState Obs terminal binary start :=
        ⟨{ label := B, yieldType := q }, hLeftKeep⟩
      let Z : V60KeptState Obs terminal binary start :=
        ⟨{ label := C, yieldType := r }, hRightKeep⟩
      have hRule : V60KeptBinary
          (⟨{ label := A, yieldType := p }, hKeep⟩ :
            V60KeptState Obs terminal binary start) Y Z := by
        exact ⟨hrule, hproduct⟩
      have hLeftDeriv : V60KeptDerives Obs terminal binary start Y x := by
        simpa [Y] using ihLeft hLeftKeep
      have hRightDeriv : V60KeptDerives Obs terminal binary start Z y := by
        simpa [Z] using ihRight hRightKeep
      exact V60KeptDerives.binary hRule hLeftDeriv hRightDeriv

/-- The retained direct-start state has the empty terminal context. -/
theorem v60_kept_start_occurs_empty
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (X : V60KeptState Obs terminal binary start)
    (hStart : V60KeptStart X) :
    V60TypedOccurs Obs terminal binary start X.1 [] [] := by
  rcases X with ⟨⟨A, p⟩, hKeep⟩
  exact V60TypedOccurs.start (p := p) hStart

/-- Language of the trimmed yield-only refinement. -/
def V60TrimmedTypedStartLanguage
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) : Language Sigma :=
  fun w =>
    (w = [] ∧ epsilonStart) ∨
      ∃ X : V60KeptState Obs terminal binary start,
        V60KeptStart X ∧ V60KeptDerives Obs terminal binary start X w

/-- Trimming preserves exactly the full typed language. -/
theorem v60_trimmed_typed_language_iff_full
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) (w : Word Sigma) :
    V60TrimmedTypedStartLanguage Obs terminal binary start epsilonStart w ↔
      V60FullTypedStartLanguage Obs terminal binary start epsilonStart w := by
  constructor
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨X, hStart, hDeriv⟩
      exact Or.inr ⟨X.1.label, X.1.yieldType, hStart,
        v60_kept_derivation_to_typed Obs terminal binary start hDeriv⟩
  · intro h
    rcases h with hEps | hNonempty
    · exact Or.inl hEps
    · rcases hNonempty with ⟨A, p, hStart, hDeriv⟩
      have hKeep : V60TypedKept Obs terminal binary start
          { label := A, yieldType := p } := by
        constructor
        · exact ⟨w, hDeriv⟩
        · exact ⟨[], [], V60TypedOccurs.start (p := p) hStart⟩
      let X : V60KeptState Obs terminal binary start :=
        ⟨{ label := A, yieldType := p }, hKeep⟩
      exact Or.inr ⟨X, hStart, by
        simpa [X] using
          v60_typed_derivation_to_kept Obs terminal binary start hKeep hDeriv⟩

/-- Proposition `typed-core`, language statement after trim. -/
theorem v60_trimmed_typed_language_iff_untyped
    {N : Type v} {Sigma : Type u}
    (Obs : Observer Sigma)
    (terminal : V60TerminalRules N Sigma)
    (binary : V60BinaryRules N) (start : V60StartRules N)
    (epsilonStart : Prop) (w : Word Sigma) :
    V60TrimmedTypedStartLanguage Obs terminal binary start epsilonStart w ↔
      V60UntypedStartLanguage terminal binary start epsilonStart w := by
  exact (v60_trimmed_typed_language_iff_full
    Obs terminal binary start epsilonStart w).trans
      (v60_full_typed_language_iff_untyped
        Obs terminal binary start epsilonStart w)

end FixedHCFG
end LeanCfgProject
