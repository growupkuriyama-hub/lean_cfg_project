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

private theorem filterMap_decorateComponent (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting)
    (component : List (TemplateAtom sig α r.children)) :
    (r.decorateComponent π hlin hnd component).filterMap
        (fun atom =>
          match atom with
          | TemplateAtom.terminal _ => none
          | TemplateAtom.variable rv => some rv) =
      (component.filterMap
        (fun atom =>
          match atom with
          | TemplateAtom.terminal _ => none
          | TemplateAtom.variable rv => some rv)).map
        (r.decorateVariable π hlin hnd) := by
  unfold decorateComponent
  rw [List.filterMap_map, List.map_filterMap]
  apply congrArg (fun f => component.filterMap f)
  funext atom
  cases atom <;> rfl

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
  unfold decoratedComponents
  generalize r.orientedComponents π = components
  induction components with
  | nil => rfl
  | cons component rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [filterMap_decorateComponent]
      rw [ih]

end MCFGRule

end MCFGv4
