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

/-- Uniform projection of the variable carried by a template atom. -/
private def variableOfAtom {N' : Type*} {α' : Type*}
    {sig' : MCFGSignature N'} {children : List N'} :
    TemplateAtom sig' α' children → Option (RuleVariable sig' children)
  | TemplateAtom.terminal _ => none
  | TemplateAtom.variable rv => some rv

private theorem filterMap_decorateComponent (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting)
    (component : List (TemplateAtom sig α r.children)) :
    (r.decorateComponent π hlin hnd component).filterMap variableOfAtom =
      (component.filterMap variableOfAtom).map
        (r.decorateVariable π hlin hnd) := by
  unfold decorateComponent
  rw [List.filterMap_map, List.map_filterMap]
  apply congrArg (fun f => component.filterMap f)
  funext atom
  cases atom <;> rfl

private theorem decoratedComponentList_variables (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting)
    (components : List (List (TemplateAtom sig α r.children))) :
    ((components.map (r.decorateComponent π hlin hnd)).flatMap
        (fun component => component.filterMap variableOfAtom)) =
      (components.flatMap
        (fun component => component.filterMap variableOfAtom)).map
        (r.decorateVariable π hlin hnd) := by
  induction components with
  | nil => rfl
  | cons component rest ih =>
      simp [filterMap_decorateComponent, ih]

private theorem orientedVariables_eq_flatMap (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs))) :
    r.orientedVariables π =
      (r.orientedComponents π).flatMap
        (fun component => component.filterMap variableOfAtom) := by
  unfold orientedVariables orientedAtoms
  have hproj :
      (fun atom : TemplateAtom sig α r.children =>
        match atom with
        | TemplateAtom.terminal _ => none
        | TemplateAtom.variable rv => some rv) = variableOfAtom := by
    funext atom
    cases atom <;> rfl
  rw [hproj]
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
  have hproj :
      (fun atom : TemplateAtom (permutationDecoratedSignature sig) α
          (r.decoratedChildren π hlin hnd) =>
        match atom with
        | TemplateAtom.terminal _ => none
        | TemplateAtom.variable rv => some rv) = variableOfAtom := by
    funext atom
    cases atom <;> rfl
  rw [hproj, orientedVariables_eq_flatMap]
  unfold decoratedComponents
  exact decoratedComponentList_variables r π hlin hnd (r.orientedComponents π)

end MCFGRule

end MCFGv4
