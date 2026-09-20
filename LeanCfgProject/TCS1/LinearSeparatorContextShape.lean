import LeanCfgProject.TCS1.LinearSeparatorDistribution

/-!
# TCS #1 v78: context shape for center-containing separator factors

This module isolates the structural lemma used in the fixed-h proof for
L_{±,e}.  If a factor containing one of the center symbols c,d,e occurs
inside a word of L_{±,e}, then everything to its left is a pure a-power and
everything to its right is a pure b-power.

The proof is deliberately independent of balance/parity arithmetic.  A
generic prefix lemma strips the ambient a-prefix.  The suffix statement is
obtained by reversing the word and reusing the same lemma.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

/-- The three center letters of the separator language. -/
def LpmCenterSymbol (z : LpmSymbol) : Prop :=
  z = c ∨ z = d ∨ z = e

theorem center_ne_a
    {z : LpmSymbol}
    (hz : LpmCenterSymbol z) :
    z ≠ a := by
  rcases hz with rfl | rfl | rfl <;> decide

theorem center_ne_b
    {z : LpmSymbol}
    (hz : LpmCenterSymbol z) :
    z ≠ b := by
  rcases hz with rfl | rfl | rfl <;> decide

/--
Generic left-shape lemma.

If a factor left^i z right^j, with z distinct from right, occurs in a word of
the form left^p z' right^q, then the context before that factor is a pure
left-power.
-/
theorem prefix_context_is_power
    (left right z z' : LpmSymbol)
    (hzright : z ≠ right)
    {i j p q : Nat}
    {u v : Word LpmSymbol}
    (h :
      u ++
          (List.replicate i left ++ [z] ++
            List.replicate j right) ++
          v =
        List.replicate p left ++ [z'] ++
          List.replicate q right) :
    ∃ m : Nat, u = List.replicate m left := by
  induction u generalizing p with
  | nil =>
      exact ⟨0, rfl⟩
  | cons t u ih =>
      cases p with
      | zero =>
          have hcons :
              t ::
                  (u ++
                    (List.replicate i left ++ [z] ++
                      List.replicate j right) ++
                    v) =
                z' :: List.replicate q right := by
            simpa [List.append_assoc] using h
          have htail :
              u ++
                  (List.replicate i left ++ [z] ++
                    List.replicate j right) ++
                  v =
                List.replicate q right :=
            (List.cons.inj hcons).2
          have hzmem :
              z ∈
                u ++
                  (List.replicate i left ++ [z] ++
                    List.replicate j right) ++
                  v := by
            simp
          rw [htail] at hzmem
          simp [List.mem_replicate, hzright] at hzmem
      | succ p =>
          have hcons :
              t ::
                  (u ++
                    (List.replicate i left ++ [z] ++
                      List.replicate j right) ++
                    v) =
                left ::
                  (List.replicate p left ++ [z'] ++
                    List.replicate q right) := by
            simpa [List.replicate_succ, List.append_assoc] using h
          have ht : t = left :=
            (List.cons.inj hcons).1
          have htail :
              u ++
                  (List.replicate i left ++ [z] ++
                    List.replicate j right) ++
                  v =
                List.replicate p left ++ [z'] ++
                  List.replicate q right :=
            (List.cons.inj hcons).2
          obtain ⟨m, hum⟩ := ih htail
          refine ⟨m + 1, ?_⟩
          subst t
          rw [hum]
          simp [List.replicate_succ, Nat.add_comm]

/--
A center-containing factor inside an L_{±,e} word has a pure-a left context
and a pure-b right context.
-/
theorem lpm_center_context_shape
    {u v : Word LpmSymbol}
    {i j : Nat}
    {z : LpmSymbol}
    (hz : LpmCenterSymbol z)
    (hmem :
      u ++ lpmOneCenter i z j ++ v ∈
        LpmLanguage) :
    ∃ m n : Nat,
      u = List.replicate m a ∧
      v = List.replicate n b := by
  rcases hmem with ⟨N, z', hword, hacc⟩
  have hleft :
      ∃ m : Nat, u = List.replicate m a := by
    apply
      prefix_context_is_power
        a b z z' (center_ne_b hz)
        (i := i) (j := j) (p := N) (q := N)
        (u := u) (v := v)
    simpa [lpmOneCenter, lpmCore, List.append_assoc]
      using hword
  obtain ⟨m, hum⟩ := hleft

  have hrev :
      v.reverse ++
          (List.replicate j b ++ [z] ++
            List.replicate i a) ++
          u.reverse =
        List.replicate N b ++ [z'] ++
          List.replicate N a := by
    have hr := congrArg List.reverse hword
    simpa [lpmOneCenter, lpmCore, List.reverse_append,
      List.append_assoc] using hr

  have hrightRev :
      ∃ n : Nat, v.reverse = List.replicate n b := by
    exact
      prefix_context_is_power
        b a z z' (center_ne_a hz)
        (i := j) (j := i) (p := N) (q := N)
        (u := v.reverse) (v := u.reverse)
        hrev
  obtain ⟨n, hvrev⟩ := hrightRev
  have hvn : v = List.replicate n b := by
    have hrv := congrArg List.reverse hvrev
    simpa using hrv
  exact ⟨m, n, hum, hvn⟩

/-- Distribution-facing form of the context-shape lemma. -/
theorem lpm_distribution_context_shape
    {u v : Word LpmSymbol}
    {i j : Nat}
    {z : LpmSymbol}
    (hz : LpmCenterSymbol z)
    (hctx :
      (u, v) ∈
        Distribution LpmLanguage
          (lpmOneCenter i z j)) :
    ∃ m n : Nat,
      u = List.replicate m a ∧
      v = List.replicate n b := by
  exact
    lpm_center_context_shape hz hctx

end TCS1
end LeanCfgProject
