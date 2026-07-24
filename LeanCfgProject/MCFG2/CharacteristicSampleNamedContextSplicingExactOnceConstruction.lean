/-
CharacteristicSampleNamedContextSplicingExactOnceConstruction.lean

Corrected named-context splicing for the MCFG fixed-observation development.

This file PROVES that the universal `NamedContextSplicingConstructor` assumed by
the current clean chain is FALSE without an exact-once hypothesis, and REPLACES
it with a concrete, fully proved `ExactNamedContextSplicingConstructor` built
from `TemplateTuple.ExactlyOnce` (equivalently, from `G.BinaryRulesExactlyOnce`
on each binary rule).

All proofs reuse the project's own definitions (`namedFill`, `fillNamedAux`,
`RawNamedSentenceContext.WellFormed`, `TemplateTuple.ExactlyOnce`,
`BinaryNamedContextSplicing`).  No `sorry`, `admit`, or `axiom`.

NOTE ON PROVENANCE: every declaration below was machine-checked verbatim in a
self-contained mathlib-free file under Lean 4.15.0 (definitions copied faithfully
from Basic.lean / ExactOnce.lean / NamedContextSplicingSkeleton.lean).  This
project-facing version was NOT re-run through `lake build` in that environment
because the sandbox had no Mathlib toolchain; the `simp` steps that are not
`simp only` may need trivial adjustment against Mathlib's larger simp set.
-/
import LeanCfgProject.MCFG2.NamedContextSplicingConstructor

universe u v w

namespace MCFG.ExactSplicing

open MCFG

/-! ##########################################################################
    PART 1 : AUDIT.  The universal constructor is FALSE without exact-once.

    Counterexample: e = dB = 1, dC = 0, parent = □₀ (trivial arity-1 context),
    body 0 = x¹ x¹ (the square / copy template).  This template is NOT
    exact-once (leftVar 0 occurs twice), and no well-formed arity-1 left
    context can satisfy `left_fill_eq`, because a well-formed arity-1 context
    inserts `x 0` exactly once whereas the target word inserts it twice.
    ########################################################################## -/

/-- Every element of `Fin 1` is `0`. -/
theorem fin1_eq_zero (a : Fin 1) : a = 0 := by
  have := a.isLt; ext; omega

/-- Trivial arity-1 parent context `□₀`. -/
def trivParent : NamedSentenceContext Unit 1 :=
  ⟨{ chunks := [[], []], holes := [0] }, by
    refine ⟨rfl, ?_, ?_⟩
    · simp
    · intro i; rw [fin1_eq_zero i]; simp⟩

/-- Square template `body 0 = [leftVar 0, leftVar 0]`. -/
def squareBody : TemplateTuple Unit 1 1 0 := fun _ => [TemplateAtom.leftVar 0, TemplateAtom.leftVar 0]

/-- The square template is not exact-once (leftVar 0 occurs twice, not once). -/
theorem squareBody_not_exactlyOnce : ¬ TemplateTuple.ExactlyOnce squareBody := by
  rintro ⟨_, hleft, _⟩
  obtain ⟨o, ho1, _⟩ := hleft 0
  -- leftVarCount 0 (squareBody o) = 2, contradicting = 1
  have : leftVarCount (0 : Fin 1) (squareBody o) = 2 := by
    simp [squareBody, leftVarCount]
  omega

/-- A well-formed arity-1 raw context has hole list exactly `[0]`. -/
theorem wf1_holes (c : RawNamedSentenceContext Unit 1) (h : c.WellFormed) :
    c.holes = [0] := by
  obtain ⟨_, hnodup, hcov⟩ := h
  have h0 : (0 : Fin 1) ∈ c.holes := hcov 0
  match hm : c.holes with
  | [] => rw [hm] at h0; exact absurd h0 (by simp)
  | [a] => rw [fin1_eq_zero a]
  | a :: b :: t =>
      have ha : a = 0 := fin1_eq_zero a
      have hb : b = 0 := fin1_eq_zero b
      rw [hm] at hnodup
      rw [List.nodup_cons] at hnodup
      have hab : a ∈ b :: t := by
        rw [ha, hb]
        exact List.mem_cons_self
      exact (hnodup.1 hab).elim

/-- On a well-formed arity-1 context, filling with the constant tuple `w`
gives `p ++ w ++ q` for chunks `[p, q]` determined by the context. -/
theorem wf1_fill (c : RawNamedSentenceContext Unit 1) (h : c.WellFormed) :
    ∃ p q, ∀ w : Word Unit, rawNamedFill c (fun _ => w) = p ++ w ++ q := by
  have hh : c.holes = [0] := wf1_holes c h
  have hlen : c.chunks.length = 2 := by
    obtain ⟨hl, _, _⟩ := h; rw [hh] at hl; simpa using hl
  match hc : c.chunks with
  | [] => rw [hc] at hlen; simp at hlen
  | [p] => rw [hc] at hlen; simp at hlen
  | [p, q] =>
      refine ⟨p, q, fun w => ?_⟩
      unfold rawNamedFill
      rw [hh, hc]
      simp [fillNamedAux]
  | p :: q :: r :: t => rw [hc] at hlen; simp at hlen

/-- **Audit theorem.**  No `BinaryNamedContextSplicing` exists for the trivial
parent and the (non-exact-once) square template.  Hence a *universal* splicing
constructor quantified over all templates is false; exact-once is necessary. -/
theorem square_template_no_splicing :
    ¬ Nonempty (BinaryNamedContextSplicing trivParent squareBody) := by
  rintro ⟨S⟩
  -- the empty right tuple
  let y : Tuple Unit 0 := fun i => i.elim0
  let c := S.leftContext y
  -- the fill equation, specialised, says: namedFill (S.leftContext y) x = x 0 ++ x 0
  have key : ∀ x : Tuple Unit 1, namedFill 1 c x = x 0 ++ x 0 := by
    intro x
    have := S.left_fill_eq y x
    -- compute the RHS
    have hrhs : namedFill 1 trivParent (evalTemplateTuple squareBody x y) = x 0 ++ x 0 := by
      unfold namedFill rawNamedFill trivParent evalTemplateTuple squareBody
      simp [fillNamedAux, evalTemplateWord, evalTemplateAtom]
    simpa [c, hrhs] using this
  -- structural form of c
  obtain ⟨p, q, hpq⟩ := wf1_fill c.1 c.2
  -- specialise the two filling identities to constant tuples
  have e0 : rawNamedFill c.1 (fun _ => ([] : Word Unit)) = ([] : Word Unit) := by
    have := key (fun _ => []); simpa [namedFill] using this
  have e1 : rawNamedFill c.1 (fun _ => ([()] : Word Unit)) = [(), ()] := by
    have := key (fun _ => [()]); simpa [namedFill] using this
  -- `p ++ q = []` forces `p = q = []`
  have hp : p = [] ∧ q = [] := by
    have h := (hpq []).symm.trans e0
    simp only [List.append_nil] at h
    have hp0 : p = [] := by
      cases p with
      | nil => rfl
      | cons a t => simp at h
    have hq0 : q = [] := by
      simpa [hp0] using h
    exact ⟨hp0, hq0⟩
  obtain ⟨hp0, hq0⟩ := hp
  -- then the length-one filling forces `[()] = [(), ()]`, impossible
  have h1 := (hpq [()]).symm.trans e1
  rw [hp0, hq0] at h1
  have hlen := congrArg List.length h1
  simp at hlen

end MCFG.ExactSplicing


/-! ##########################################################################
    PART 2 : CONSTRUCTION.  Concrete left/right child contexts from an
    exact-once template, with proved `namedFill` equations.

    Strategy (per the roadmap): tokenise the parent fill into a flat list of
    "fixed word" / "hole" tokens, normalise it into a `chunks`/`holes` context,
    and prove the fill equation through the flat `realizeTokens` semantics.
    ########################################################################## -/


namespace MCFG.ExactSplicing

/-- A flat token: fixed material (`inl`) or a named hole (`inr`). -/
abbrev Tok (α : Type u) (d : Nat) := Word α ⊕ Fin d

/-- Flat fill of a token list. -/
def realizeTokens {α d} (x : Tuple α d) : List (Tok α d) → Word α
  | [] => []
  | Sum.inl w :: rest => w ++ realizeTokens x rest
  | Sum.inr h :: rest => x h ++ realizeTokens x rest

theorem realizeTokens_append {α d} (x : Tuple α d) (a b : List (Tok α d)) :
    realizeTokens x (a ++ b) = realizeTokens x a ++ realizeTokens x b := by
  induction a with
  | nil => simp [realizeTokens]
  | cons t rest ih => cases t <;> simp [realizeTokens, ih, List.append_assoc]

/-- The ordered sequence of holes in a token list. -/
def holeSeq {α d} : List (Tok α d) → List (Fin d)
  | [] => []
  | Sum.inl _ :: rest => holeSeq rest
  | Sum.inr h :: rest => h :: holeSeq rest

theorem holeSeq_append {α d} (a b : List (Tok α d)) :
    holeSeq (a ++ b) = holeSeq a ++ holeSeq b := by
  induction a with
  | nil => simp [holeSeq]
  | cons t rest ih => cases t <;> simp [holeSeq, ih]

/-- Normal form for a named context: a head chunk and a list of (hole, chunk)
pairs.  The length invariant `chunks = holes + 1` is automatic. -/
structure NF (α : Type u) (d : Nat) where
  head : Word α
  pairs : List (Fin d × Word α)

def NF.toRaw {α d} (nf : NF α d) : RawNamedSentenceContext α d :=
  ⟨nf.head :: nf.pairs.map Prod.snd, nf.pairs.map Prod.fst⟩

def fillPairs {α d} (x : Tuple α d) : List (Fin d × Word α) → Word α
  | [] => []
  | (k, c) :: ps => x k ++ c ++ fillPairs x ps

def NF.fill {α d} (nf : NF α d) (x : Tuple α d) : Word α :=
  nf.head ++ fillPairs x nf.pairs

/-- `rawNamedFill ∘ toRaw` agrees with the direct `NF.fill`. -/
theorem rawNamedFill_toRaw {α d} (nf : NF α d) (x : Tuple α d) :
    rawNamedFill nf.toRaw x = nf.fill x := by
  unfold rawNamedFill NF.toRaw NF.fill
  -- prove:  fillNamedAux x (map fst pairs) (head :: map snd pairs) = head ++ fillPairs x pairs
  suffices h : ∀ (c0 : Word α) (ps : List (Fin d × Word α)),
      fillNamedAux x (ps.map Prod.fst) (c0 :: ps.map Prod.snd) = c0 ++ fillPairs x ps by
    simpa using h nf.head nf.pairs
  intro c0 ps
  induction ps generalizing c0 with
  | nil => simp [fillNamedAux, fillPairs]
  | cons p ps ih =>
      obtain ⟨k, c⟩ := p
      simp only [List.map_cons, fillNamedAux, fillPairs, ih c]
      simp [List.append_assoc]

/-- Building the normal form from a token list. -/
def build {α d} : List (Tok α d) → NF α d
  | [] => ⟨[], []⟩
  | Sum.inl w :: rest =>
      let nf := build rest
      ⟨w ++ nf.head, nf.pairs⟩
  | Sum.inr h :: rest =>
      let nf := build rest
      ⟨[], (h, nf.head) :: nf.pairs⟩

/-- `build` realises exactly the flat token semantics. -/
theorem build_fill {α d} (x : Tuple α d) (ts : List (Tok α d)) :
    (build ts).fill x = realizeTokens x ts := by
  induction ts with
  | nil => simp [build, NF.fill, fillPairs, realizeTokens]
  | cons t rest ih =>
      cases t with
      | inl w =>
          simp only [build, NF.fill, realizeTokens]
          have : (build rest).head ++ fillPairs x (build rest).pairs = realizeTokens x rest := ih
          rw [List.append_assoc, this]
      | inr h =>
          simp only [build, NF.fill, fillPairs, realizeTokens, List.nil_append]
          have : (build rest).head ++ fillPairs x (build rest).pairs = realizeTokens x rest := ih
          rw [List.append_assoc, this]

/-- The holes produced by `build` are exactly the hole sequence of the tokens. -/
theorem build_holes {α d} (ts : List (Tok α d)) :
    (build ts).toRaw.holes = holeSeq ts := by
  unfold NF.toRaw
  simp only []
  induction ts with
  | nil => simp [build, holeSeq]
  | cons t rest ih =>
      cases t with
      | inl w => simpa [build, holeSeq] using ih
      | inr h => simp [build, holeSeq, ih]

/-- The chunk/hole length invariant holds for any `build` output. -/
theorem build_len {α d} (ts : List (Tok α d)) :
    (build ts).toRaw.chunks.length = (build ts).toRaw.holes.length + 1 := by
  unfold NF.toRaw
  simp

end MCFG.ExactSplicing

namespace MCFG.ExactSplicing

/-! ### Generic list helpers -/

theorem sum_map_zero {β} (f : β → Nat) :
    ∀ (l : List β), (∀ b ∈ l, f b = 0) → (l.map f).sum = 0
  | [], _ => by simp
  | b :: t, h => by
      have hb : f b = 0 := h b (by simp)
      have ht : (t.map f).sum = 0 := sum_map_zero f t (fun c hc => h c (by simp [hc]))
      simp [hb, ht]

/-- A `Nat`-valued function that is `1` at a single point `o0` and `0` elsewhere
sums to `1` over a duplicate-free list containing `o0`. -/
theorem sum_one_of_nodup_mem {β} [DecidableEq β] (f : β → Nat) (o0 : β) :
    ∀ (l : List β), l.Nodup → o0 ∈ l → f o0 = 1 → (∀ o', o' ≠ o0 → f o' = 0) →
      (l.map f).sum = 1
  | [], _, hmem, _, _ => by simp at hmem
  | a :: t, hnd, hmem, h1, h0 => by
      rw [List.nodup_cons] at hnd
      obtain ⟨hat, hndt⟩ := hnd
      by_cases ha : a = o0
      · subst ha
        have hz : (t.map f).sum = 0 :=
          sum_map_zero f t (fun c hc => h0 c (fun hce => hat (hce ▸ hc)))
        simp [h1, hz]
      · have hmemt : o0 ∈ t := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm ha
          · exact h
        have hfa : f a = 0 := h0 a ha
        have := sum_one_of_nodup_mem f o0 t hndt hmemt h1 h0
        simp [hfa, this]

theorem nodup_of_count_le_one {β} [DecidableEq β] :
    ∀ (l : List β), (∀ a, l.count a ≤ 1) → l.Nodup
  | [], _ => List.nodup_nil
  | b :: t, h => by
      rw [List.nodup_cons]
      refine ⟨?_, ?_⟩
      · -- b ∉ t
        have hb := h b
        rw [List.count_cons] at hb
        simp only [beq_self_eq_true, if_true] at hb
        have : t.count b = 0 := by omega
        intro hmem
        have : 0 < t.count b := List.count_pos_iff.mpr hmem
        omega
      · -- t.Nodup
        refine nodup_of_count_le_one t (fun a => ?_)
        have ha := h a
        rw [List.count_cons] at ha
        omega

/-! ### Left child context construction -/

/-- Tokenise a template word for the *left* context: right-variables are baked
in from the fixed sibling `y`; left-variables become holes. -/
def bodyLeftTokens {α dB dC} (y : Tuple α dC) : TemplateWord α dB dC → List (Tok α dB)
  | [] => []
  | TemplateAtom.terminal a :: r => Sum.inl [a] :: bodyLeftTokens y r
  | TemplateAtom.leftVar i :: r => Sum.inr i :: bodyLeftTokens y r
  | TemplateAtom.rightVar j :: r => Sum.inl (y j) :: bodyLeftTokens y r

theorem realize_bodyLeftTokens {α dB dC} (x : Tuple α dB) (y : Tuple α dC)
    (w : TemplateWord α dB dC) :
    realizeTokens x (bodyLeftTokens y w) = evalTemplateWord x y w := by
  induction w with
  | nil => simp [bodyLeftTokens, realizeTokens, evalTemplateWord]
  | cons a r ih =>
      cases a <;>
        simp [bodyLeftTokens, realizeTokens, evalTemplateWord, evalTemplateAtom, ih]

theorem count_holeSeq_bodyLeftTokens {α dB dC} (y : Tuple α dC) (i : Fin dB)
    (w : TemplateWord α dB dC) :
    (holeSeq (bodyLeftTokens y w)).count i = leftVarCount i w := by
  induction w with
  | nil => simp [bodyLeftTokens, holeSeq, leftVarCount]
  | cons a r ih =>
      cases a with
      | terminal c => simp [bodyLeftTokens, holeSeq, leftVarCount, ih]
      | leftVar k =>
          simp only [bodyLeftTokens, holeSeq, leftVarCount, List.count_cons, ih]
          by_cases hk : k = i
          · subst hk; simp
          · simp [hk, Ne.symm hk, beq_eq_false_iff_ne.mpr]
      | rightVar j => simp [bodyLeftTokens, holeSeq, leftVarCount, ih]

/-- Tokenise the whole parent fill, mirroring `fillNamedAux`. -/
def leftTokens {α e dB dC} (body : TemplateTuple α e dB dC) (y : Tuple α dC) :
    List (Fin e) → List (Word α) → List (Tok α dB)
  | [], [] => []
  | [], chunk :: _ => [Sum.inl chunk]
  | h :: hs, [] => bodyLeftTokens y (body h) ++ leftTokens body y hs []
  | h :: hs, chunk :: chunks =>
      Sum.inl chunk :: (bodyLeftTokens y (body h) ++ leftTokens body y hs chunks)

/-- The core left equation: the tokenised parent fill realises exactly the
named parent fill of the evaluated template tuple. -/
theorem realize_leftTokens {α e dB dC} (body : TemplateTuple α e dB dC)
    (x : Tuple α dB) (y : Tuple α dC) :
    ∀ (holes : List (Fin e)) (chunks : List (Word α)),
      realizeTokens x (leftTokens body y holes chunks)
        = fillNamedAux (evalTemplateTuple body x y) holes chunks
  | [], [] => by simp [leftTokens, realizeTokens, fillNamedAux]
  | [], chunk :: _ => by simp [leftTokens, realizeTokens, fillNamedAux]
  | h :: hs, [] => by
      simp only [leftTokens, fillNamedAux, realizeTokens_append, realize_bodyLeftTokens,
        realize_leftTokens body x y hs []]
      rfl
  | h :: hs, chunk :: chunks => by
      simp only [leftTokens, fillNamedAux, realizeTokens, realizeTokens_append,
        realize_bodyLeftTokens, realize_leftTokens body x y hs chunks]
      simp [evalTemplateTuple, List.append_assoc]

/-- Count of a fixed hole in the left hole-sequence equals the total
left-variable count over the parent's visited components. -/
theorem count_holeSeq_leftTokens {α e dB dC} (body : TemplateTuple α e dB dC)
    (y : Tuple α dC) (i : Fin dB) :
    ∀ (holes : List (Fin e)) (chunks : List (Word α)),
      (holeSeq (leftTokens body y holes chunks)).count i
        = (holes.map (fun o => leftVarCount i (body o))).sum
  | [], [] => by simp [leftTokens, holeSeq]
  | [], _ :: _ => by simp [leftTokens, holeSeq]
  | h :: hs, [] => by
      simp only [leftTokens, holeSeq_append, List.count_append,
        count_holeSeq_bodyLeftTokens, count_holeSeq_leftTokens body y i hs [],
        List.map_cons, List.sum_cons]
  | h :: hs, chunk :: chunks => by
      simp only [leftTokens, holeSeq, holeSeq_append, List.count_append,
        count_holeSeq_bodyLeftTokens, count_holeSeq_leftTokens body y i hs chunks,
        List.map_cons, List.sum_cons]

end MCFG.ExactSplicing

namespace MCFG.ExactSplicing

/-- Every hole of `Fin dB` occurs exactly once in the left hole-sequence,
given exact-once left-variables and a well-formed parent. -/
theorem leftCount_eq_one {α : Type u} {e dB dC : Nat}
    (parent : NamedSentenceContext α e) (body : TemplateTuple α e dB dC)
    (hbody : ∀ i, LeftOccursExactlyOnce body i) (y : Tuple α dC) (i : Fin dB) :
    (holeSeq (leftTokens body y parent.1.holes parent.1.chunks)).count i = 1 := by
  rw [count_holeSeq_leftTokens]
  obtain ⟨o0, ho1, ho0⟩ := hbody i
  obtain ⟨_, hnd, hcov⟩ := parent.2
  exact sum_one_of_nodup_mem (fun o => leftVarCount i (body o)) o0 parent.1.holes hnd (hcov o0) ho1 ho0

/-- The built left context is well-formed. -/
theorem leftWF {α : Type u} {e dB dC : Nat}
    (parent : NamedSentenceContext α e) (body : TemplateTuple α e dB dC)
    (hbody : ∀ i, LeftOccursExactlyOnce body i) (y : Tuple α dC) :
    ((build (leftTokens body y parent.1.holes parent.1.chunks)).toRaw).WellFormed := by
  constructor
  · exact build_len _
  constructor
  · apply nodup_of_count_le_one
    intro a
    have hc : ((build (leftTokens body y parent.1.holes parent.1.chunks)).toRaw).holes.count a = 1 := by
      rw [build_holes]
      exact leftCount_eq_one parent body hbody y a
    omega
  · intro i
    have hc : ((build (leftTokens body y parent.1.holes parent.1.chunks)).toRaw).holes.count i = 1 := by
      rw [build_holes]
      exact leftCount_eq_one parent body hbody y i
    exact List.count_pos_iff.mp (by omega)

/-- The concrete left child context. -/
def leftContextNSC {α : Type u} {e dB dC : Nat}
    (parent : NamedSentenceContext α e) (body : TemplateTuple α e dB dC)
    (hbody : ∀ i, LeftOccursExactlyOnce body i) (y : Tuple α dC) :
    NamedSentenceContext α dB :=
  ⟨(build (leftTokens body y parent.1.holes parent.1.chunks)).toRaw, leftWF parent body hbody y⟩

/-- **Left `namedFill` equation** (the load-bearing Stage 1 result, left half). -/
theorem leftContext_fill_eq {α : Type u} {e dB dC : Nat}
    (parent : NamedSentenceContext α e) (body : TemplateTuple α e dB dC)
    (hbody : ∀ i, LeftOccursExactlyOnce body i) (y : Tuple α dC) (x : Tuple α dB) :
    namedFill dB (leftContextNSC parent body hbody y) x
      = namedFill e parent (evalTemplateTuple body x y) := by
  change rawNamedFill (build (leftTokens body y parent.1.holes parent.1.chunks)).toRaw x
      = namedFill e parent (evalTemplateTuple body x y)
  rw [rawNamedFill_toRaw, build_fill, realize_leftTokens]
  rfl

end MCFG.ExactSplicing

namespace MCFG.ExactSplicing

/-! ### Right child context construction (symmetric) -/

/-- Tokenise a template word for the *right* context: left-variables are baked
in from the fixed sibling `u`; right-variables become holes. -/
def bodyRightTokens {α dB dC} (u : Tuple α dB) : TemplateWord α dB dC → List (Tok α dC)
  | [] => []
  | TemplateAtom.terminal a :: r => Sum.inl [a] :: bodyRightTokens u r
  | TemplateAtom.leftVar i :: r => Sum.inl (u i) :: bodyRightTokens u r
  | TemplateAtom.rightVar j :: r => Sum.inr j :: bodyRightTokens u r

theorem realize_bodyRightTokens {α dB dC} (u : Tuple α dB) (v : Tuple α dC)
    (w : TemplateWord α dB dC) :
    realizeTokens v (bodyRightTokens u w) = evalTemplateWord u v w := by
  induction w with
  | nil => simp [bodyRightTokens, realizeTokens, evalTemplateWord]
  | cons a r ih =>
      cases a <;>
        simp [bodyRightTokens, realizeTokens, evalTemplateWord, evalTemplateAtom, ih]

theorem count_holeSeq_bodyRightTokens {α dB dC} (u : Tuple α dB) (j : Fin dC)
    (w : TemplateWord α dB dC) :
    (holeSeq (bodyRightTokens u w)).count j = rightVarCount j w := by
  induction w with
  | nil => simp [bodyRightTokens, holeSeq, rightVarCount]
  | cons a r ih =>
      cases a with
      | terminal c => simp [bodyRightTokens, holeSeq, rightVarCount, ih]
      | leftVar i => simp [bodyRightTokens, holeSeq, rightVarCount, ih]
      | rightVar k =>
          simp only [bodyRightTokens, holeSeq, rightVarCount, List.count_cons, ih]
          by_cases hk : k = j
          · subst hk; simp
          · simp [hk, Ne.symm hk, beq_eq_false_iff_ne.mpr]

def rightTokens {α e dB dC} (body : TemplateTuple α e dB dC) (u : Tuple α dB) :
    List (Fin e) → List (Word α) → List (Tok α dC)
  | [], [] => []
  | [], chunk :: _ => [Sum.inl chunk]
  | h :: hs, [] => bodyRightTokens u (body h) ++ rightTokens body u hs []
  | h :: hs, chunk :: chunks =>
      Sum.inl chunk :: (bodyRightTokens u (body h) ++ rightTokens body u hs chunks)

theorem realize_rightTokens {α e dB dC} (body : TemplateTuple α e dB dC)
    (u : Tuple α dB) (v : Tuple α dC) :
    ∀ (holes : List (Fin e)) (chunks : List (Word α)),
      realizeTokens v (rightTokens body u holes chunks)
        = fillNamedAux (evalTemplateTuple body u v) holes chunks
  | [], [] => by simp [rightTokens, realizeTokens, fillNamedAux]
  | [], chunk :: _ => by simp [rightTokens, realizeTokens, fillNamedAux]
  | h :: hs, [] => by
      simp only [rightTokens, fillNamedAux, realizeTokens_append, realize_bodyRightTokens,
        realize_rightTokens body u v hs []]
      rfl
  | h :: hs, chunk :: chunks => by
      simp only [rightTokens, fillNamedAux, realizeTokens, realizeTokens_append,
        realize_bodyRightTokens, realize_rightTokens body u v hs chunks]
      simp [evalTemplateTuple, List.append_assoc]

theorem count_holeSeq_rightTokens {α e dB dC} (body : TemplateTuple α e dB dC)
    (u : Tuple α dB) (j : Fin dC) :
    ∀ (holes : List (Fin e)) (chunks : List (Word α)),
      (holeSeq (rightTokens body u holes chunks)).count j
        = (holes.map (fun o => rightVarCount j (body o))).sum
  | [], [] => by simp [rightTokens, holeSeq]
  | [], _ :: _ => by simp [rightTokens, holeSeq]
  | h :: hs, [] => by
      simp only [rightTokens, holeSeq_append, List.count_append,
        count_holeSeq_bodyRightTokens, count_holeSeq_rightTokens body u j hs [],
        List.map_cons, List.sum_cons]
  | h :: hs, chunk :: chunks => by
      simp only [rightTokens, holeSeq, holeSeq_append, List.count_append,
        count_holeSeq_bodyRightTokens, count_holeSeq_rightTokens body u j hs chunks,
        List.map_cons, List.sum_cons]

theorem rightCount_eq_one {α : Type u} {e dB dC : Nat}
    (parent : NamedSentenceContext α e) (body : TemplateTuple α e dB dC)
    (hbody : ∀ j, RightOccursExactlyOnce body j) (u : Tuple α dB) (j : Fin dC) :
    (holeSeq (rightTokens body u parent.1.holes parent.1.chunks)).count j = 1 := by
  rw [count_holeSeq_rightTokens]
  obtain ⟨o0, ho1, ho0⟩ := hbody j
  obtain ⟨_, hnd, hcov⟩ := parent.2
  exact sum_one_of_nodup_mem (fun o => rightVarCount j (body o)) o0 parent.1.holes hnd (hcov o0) ho1 ho0

theorem rightWF {α : Type u} {e dB dC : Nat}
    (parent : NamedSentenceContext α e) (body : TemplateTuple α e dB dC)
    (hbody : ∀ j, RightOccursExactlyOnce body j) (u : Tuple α dB) :
    ((build (rightTokens body u parent.1.holes parent.1.chunks)).toRaw).WellFormed := by
  constructor
  · exact build_len _
  constructor
  · apply nodup_of_count_le_one
    intro a
    have hc : ((build (rightTokens body u parent.1.holes parent.1.chunks)).toRaw).holes.count a = 1 := by
      rw [build_holes]
      exact rightCount_eq_one parent body hbody u a
    omega
  · intro j
    have hc : ((build (rightTokens body u parent.1.holes parent.1.chunks)).toRaw).holes.count j = 1 := by
      rw [build_holes]
      exact rightCount_eq_one parent body hbody u j
    exact List.count_pos_iff.mp (by omega)

def rightContextNSC {α : Type u} {e dB dC : Nat}
    (parent : NamedSentenceContext α e) (body : TemplateTuple α e dB dC)
    (hbody : ∀ j, RightOccursExactlyOnce body j) (u : Tuple α dB) :
    NamedSentenceContext α dC :=
  ⟨(build (rightTokens body u parent.1.holes parent.1.chunks)).toRaw, rightWF parent body hbody u⟩

/-- **Right `namedFill` equation** (Stage 1 result, right half). -/
theorem rightContext_fill_eq {α : Type u} {e dB dC : Nat}
    (parent : NamedSentenceContext α e) (body : TemplateTuple α e dB dC)
    (hbody : ∀ j, RightOccursExactlyOnce body j) (u : Tuple α dB) (v : Tuple α dC) :
    namedFill dC (rightContextNSC parent body hbody u) v
      = namedFill e parent (evalTemplateTuple body u v) := by
  change rawNamedFill (build (rightTokens body u parent.1.holes parent.1.chunks)).toRaw v
      = namedFill e parent (evalTemplateTuple body u v)
  rw [rawNamedFill_toRaw, build_fill, realize_rightTokens]
  rfl

end MCFG.ExactSplicing

namespace MCFG.ExactSplicing

/-! ##########################################################################
    PART 3 : the exact-once splicing constructor (the corrected replacement
    for the false universal `NamedContextSplicingConstructor`).
    ########################################################################## -/

/-- Corrected splicing constructor: it produces a splicing witness for *every*
parent context and *exact-once* template.  The exact-once hypothesis is exactly
what the audit (Part 1) shows to be necessary. -/
structure ExactNamedContextSplicingConstructor (α : Type u) where
  splice : {e dB dC : Nat} →
    (parent : NamedSentenceContext α e) →
    (body : TemplateTuple α e dB dC) →
    TemplateTuple.ExactlyOnce body →
    BinaryNamedContextSplicing parent body

/-- Bundle the concrete left/right constructions into a splicing witness. -/
def exactSplice {α : Type u} {e dB dC : Nat}
    (parent : NamedSentenceContext α e) (body : TemplateTuple α e dB dC)
    (hexact : TemplateTuple.ExactlyOnce body) :
    BinaryNamedContextSplicing parent body where
  leftContext := fun y => leftContextNSC parent body hexact.2.1 y
  left_fill_eq := fun y x => leftContext_fill_eq parent body hexact.2.1 y x
  rightContext := fun u => rightContextNSC parent body hexact.2.2 u
  right_fill_eq := fun u v => rightContext_fill_eq parent body hexact.2.2 u v

/-- **Main Stage 1 theorem.**  A concrete exact-once splicing constructor exists
for every alphabet `α`.  No `sorry`, no unproven existence assumption. -/
def exact_namedContextSplicingConstructor (α : Type u) :
    ExactNamedContextSplicingConstructor α where
  splice := fun parent body hexact => exactSplice parent body hexact

end MCFG.ExactSplicing

/-! ##########################################################################
    PART 4 : MIGRATION.  Replace the (false) universal constructor at its single
    call site by the exact-once constructor, threading `G.BinaryRulesExactlyOnce`.

    Original (unsatisfiable-premise) definition in
    `NamedContextSplicingConstructor.lean`:

        def toRuleSplicingEvidence (U : NamedContextSplicingConstructor α)
            (ρ : BinaryRule N α G.arity) (hρ : ρ ∈ G.binaryRules) :
            BinaryRuleSplicingEvidence (G := G) (C := C) ρ hρ where
          splicing := U.splice (C.expose ρ.lhs) ρ.body

    Corrected version: take the exact-once constructor plus the working-grammar
    exact-once hypothesis, and pass `hexact ρ hρ : ρ.ExactlyOnce` (definitionally
    `TemplateTuple.ExactlyOnce ρ.body`) to `splice`.  Uncomment once this module
    is on the import path of `BinaryRuleSplicingEvidence`.
    ########################################################################## -/

/-
section Migration
variable {N : Type w} {M : Type v} {α : Type u}
variable [DecidableEq α] [Monoid M]
variable {G : WorkingMCFG N α} {obs : α → M} {f : Nat}
variable {C : ReachableBlueprintPreCore G obs f}

def toRuleSplicingEvidenceExact
    (U : ExactNamedContextSplicingConstructor α)
    (hexact : G.BinaryRulesExactlyOnce)
    (ρ : BinaryRule N α G.arity) (hρ : ρ ∈ G.binaryRules) :
    BinaryRuleSplicingEvidence (G := G) (C := C) ρ hρ where
  splicing := U.splice (C.expose ρ.lhs) ρ.body (hexact ρ hρ)

end Migration
-/

-- Existence witness that discharges the constructor field of the paper-facing
-- endpoints: supply `exact_namedContextSplicingConstructor α` for
-- `splicingConstructor` and `G.BinaryRulesExactlyOnce` (already part of
-- `ExactWorkingConditions`) for the exact-once side condition.

