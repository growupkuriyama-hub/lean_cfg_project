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

@[simp] theorem decorateVariable_child_val (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting)
    (rv : RuleVariable sig r.children) :
    (r.decorateVariable π hlin hnd rv).child.val = rv.child.val := by
  simp [decorateVariable, decoratedChildIndex]

/-- Casting a finite index along an equality of bounds never changes its value. -/
@[simp] private theorem finCast_val {m n : Nat} (h : m = n) (i : Fin m) :
    (Fin.cast h i).val = i.val := by
  cases h
  rfl

@[simp] theorem decorateVariable_component_val (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting)
    (rv : RuleVariable sig r.children) :
    (r.decorateVariable π hlin hnd rv).component.val =
      ((r.inducedOrientation π rv.child hlin hnd).symm rv.component).val := by
  simp [decorateVariable, decoratedChildIndex, decoratedChildren, decoratedChild,
    permutationDecoratedSignature]

/-- Two rule variables with the same stored child and component values are equal.
This formulation avoids dependent casts in the component field. -/
private theorem ruleVariable_ext_val {N' : Type*} {sig' : MCFGSignature N'}
    {children : List N'} (x y : RuleVariable sig' children)
    (hchild : x.child.val = y.child.val)
    (hcomponent : x.component.val = y.component.val) : x = y := by
  cases x with
  | mk j k =>
      cases y with
      | mk j' k' =>
          dsimp at hchild hcomponent ⊢
          have hj : j = j' := Fin.ext hchild
          subst j'
          have hk : k = k' := Fin.ext hcomponent
          subst k'
          rfl

/-- The child-variable renaming used by permutation decoration is injective. -/
theorem decorateVariable_injective (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    Function.Injective (r.decorateVariable π hlin hnd) := by
  intro rv rv' h
  have hchildVal : rv.child.val = rv'.child.val := by
    have := congrArg (fun z => z.child.val) h
    simpa using this
  have hchild : rv.child = rv'.child := Fin.ext hchildVal
  cases rv with
  | mk j k =>
      cases rv' with
      | mk j' k' =>
          dsimp at hchild ⊢
          subst j'
          have hcomponentVal := congrArg (fun z => z.component.val) h
          have horiented :
              (r.inducedOrientation π j hlin hnd).symm k =
                (r.inducedOrientation π j hlin hnd).symm k' := by
            apply Fin.ext
            simpa using hcomponentVal
          have hk : k = k' :=
            (r.inducedOrientation π j hlin hnd).symm.injective horiented
          subst k'
          rfl

/-- Every child-component variable of the decorated rule has an original
preimage.  The inverse reindexing uses the forward induced orientation. -/
theorem decorateVariable_surjective (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    Function.Surjective (r.decorateVariable π hlin hnd) := by
  intro z
  let j : Fin r.children.length :=
    Fin.cast (r.decoratedChildren_length π hlin hnd) z.child
  have hbase :
      ((r.decoratedChildren π hlin hnd).get z.child).base =
        r.children.get j := by
    simpa [j] using
      (r.decoratedChildren_get_base π hlin hnd z.child)
  have hArity :
      (permutationDecoratedSignature sig).arity
          ((r.decoratedChildren π hlin hnd).get z.child) =
        sig.arity (r.children.get j) := by
    rw [permutationDecorated_arity]
    exact congrArg sig.arity hbase
  let k0 : Fin (sig.arity (r.children.get j)) := Fin.cast hArity z.component
  let k : Fin (sig.arity (r.children.get j)) :=
    r.inducedOrientation π j hlin hnd k0
  let rv : RuleVariable sig r.children := { child := j, component := k }
  refine ⟨rv, ?_⟩
  apply ruleVariable_ext_val
  · simp [rv, j]
  · rw [r.decorateVariable_component_val π hlin hnd rv]
    change
      ((r.inducedOrientation π j hlin hnd).symm
        (r.inducedOrientation π j hlin hnd k0)).val = z.component.val
    rw [Equiv.symm_apply_apply]
    exact finCast_val hArity z.component

/-- Permutation decoration preserves the manuscript's rule-linearity property. -/
theorem permutationDecorate_linear (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    (r.permutationDecorate π hlin hnd).Linear := by
  unfold Linear
  rw [r.permutationDecorate_usedVariables π hlin hnd]
  have hnodup :
      ((r.orientedVariables π).map (r.decorateVariable π hlin hnd)).Nodup :=
    (r.orientedVariables_nodup π hlin).map
      (r.decorateVariable_injective π hlin hnd)
  exact hnodup.pairwise_of_forall_ne (by
    intro a ha b hb hab
    exact hab)

/-- Permutation decoration preserves nondeletion. -/
theorem permutationDecorate_nondeleting (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (hlin : r.Linear) (hnd : r.Nondeleting) :
    (r.permutationDecorate π hlin hnd).Nondeleting := by
  intro j k
  rw [r.permutationDecorate_usedVariables π hlin hnd]
  rcases r.decorateVariable_surjective π hlin hnd
      ({ child := j, component := k }) with ⟨rv, hrv⟩
  apply List.mem_map.2
  refine ⟨rv, ?_, hrv⟩
  have hused : rv ∈ r.usedVariables := hnd rv.child rv.component
  exact (r.orientedVariables_perm_usedVariables π).mem_iff.mpr hused

/-- The inverse induced orientation sends the element encountered at scan
position `i` back to that position.  This is the list-level normalization fact
needed for the nonpermuting part of permutation decoration. -/
private theorem inducedOrientation_symm_get_val (r : MCFGRule sig α)
    (π : Equiv.Perm (Fin (sig.arity r.lhs)))
    (j : Fin r.children.length) (hlin : r.Linear) (hnd : r.Nondeleting)
    (i : Fin (r.childComponentFinOrder π j).length) :
    ((r.inducedOrientation π j hlin hnd).symm
      ((r.childComponentFinOrder π j).get i)).val = i.val := by
  unfold inducedOrientation
  dsimp
  simp [r.childComponentFinOrder_nodup π j hlin]

end MCFGRule

end MCFGv4
