import LeanCfgProject.MCFGv4.PermutationDecoration

/-!
# MCFGv4.PermutationDecorationProperties

Structural preservation lemmas for the rule-level permutation-decoration
construction.  The first bridge identifies the variable scan of a decorated
rule with the original variable scan in the chosen parent orientation, followed
by the variable-renaming map.
-/

namespace MCFGv4

universe u v

namespace MCFGRule

variable {N : Type v} {α : Type u} {sig : MCFGSignature N}

/-- A plain-list transport lemma used to keep the dependent MCFG indices out of
the component-list induction below. -/
private theorem flatMap_map_filterMap
    {A B X Y : Type*}
    (d : A → B) (f : A → Option X) (g : B → Option Y) (e : X → Y)
    (h : ∀ a, g (d a) = (f a).map e)
    (components : List (List A)) :
    (components.map (fun component => component.map d)).flatMap
        (fun component => component.filterMap g) =
      (components.flatMap (fun component => component.filterMap f)).map e := by
  induction components with
  | nil => rfl
  | cons component rest ih =>
      have hhead :
          (component.map d).filterMap g =
            (component.filterMap f).map e := by
        rw [List.filterMap_map, List.map_filterMap]
        apply congrArg (fun q => component.filterMap q)
        funext a
        exact h a
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [hhead, ih]

private theorem orientedVariables_eq_flatMap (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs))) :
    r.orientedVariables π =
      (r.orientedComponents π).flatMap
        (fun component =>
          component.filterMap fun atom =>
            match atom with
            | TemplateAtom.terminal _ => none
            | TemplateAtom.variable rv => some rv) := by
  unfold orientedVariables orientedAtoms
  generalize r.orientedComponents π = components
  induction components with
  | nil => rfl
  | cons component rest ih =>
      rw [List.foldr_cons, List.filterMap_append, ih]
      rfl

/-- The complete variable scan of a decorated rule is exactly the original
parent-oriented scan with the induced child-variable renaming applied. -/
theorem permutationDecorate_usedVariables (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    (r.permutationDecorate π hlin hnd).usedVariables =
      (r.orientedVariables π).map (r.decorateVariable π hlin hnd) := by
  simp only [usedVariables, permutationDecorate]
  rw [orientedVariables_eq_flatMap]
  unfold decoratedComponents decorateComponent
  apply flatMap_map_filterMap
  intro atom
  cases atom <;> rfl

end MCFGRule

end MCFGv4
