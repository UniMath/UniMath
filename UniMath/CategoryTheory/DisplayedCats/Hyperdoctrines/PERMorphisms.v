(******************************************************************************************

 Morphisms between partial setoids

 Every first-order hyperdoctrine gives rise to a category of partial setoids, which are
 types equipped with a partial equivalence relation. In this file, we define the morphisms
 of this category. For this we follow Definition 3.1 in "Tripos Theory in Retrospect" by
 Andrew Pitts.

 To understand the definition of a morphism between partial setoids, we introduce the
 following terminology. Given a partial setoid `X`, we say that a term `x : tm Γ X` is
 defined in context `Δ` if `Δ ⊢ x ~ x`. A morphism from a partial setoid `X` to `Y` is
 given by a formula `φ` on `X` and `Y` that satisfies several laws.
 1. `φ` is strict. If `φ x y` holds, then `x ~ x` and `y ~ y`, so both `x` and `y` are
    defined in context `Δ`. These laws are expressed in [partial_setoid_mor_dom_defined_law]
    and in [partial_setoid_mor_cod_defined_law].
 2. `φ` is relational. If we have that `x₁ ~ x₂`, `y₁ ~ y₂`, and that `φ x₁ y₁`, then we must
    also have that `φ x₂ y₂`. This expresses that `φ` is well-defined with respect to the
    partial equivalence relations of `X` and `Y`.
 3. `φ` is functional. If `φ x y₁` and φ x y₂`, then we also have that `y₁ ~ y₂`. This means
    that every `x` gets mapped to at most one element. This law is expressed below in
    [partial_setoid_mor_unique_im_law].
 4. `φ` is total. If `x ~ x` (i.e., `x` is defined), then there is a `y` such that we have
    `φ x y`. This is expressed in [partial_setoid_mor_hom_exists_law].
 The intution behind these laws is taken from in Section 2.2 of "Realizability: an introduction
 to its categorical side" by Jaap van Oosten.

 We also give accessors for morphisms of partial setoids. These accessors have suitable
 weakenings built in, and they apply the elimination rules of implication and universal
 quantification. Examples of morphisms between partial setoids can be found in other files.

 References
 - "Tripos Theory in Retrospect" by Andrew Pitts
 - "Realizability: an introduction to its categorical side" by Jaap van Oosten

 Content
 1. Laws of partial setoid morphisms
 2. Partial setoid morphisms
 3. Accessors for partial setoid morphisms

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.DisplayedCats.Hyperdoctrines.PERs.

Local Open Scope cat.
Local Open Scope hd.

Section PartialEquivalenceRelationMorphisms.
  Context {H : first_order_hyperdoctrine}
          {X Y : partial_setoid H}.

  (** * 1. Laws of partial setoid morphisms *)

  (**
     The first law expresses strictness with regards to the domain
   *)
  Definition partial_setoid_mor_dom_defined_law
             (φ : form (X ×h Y))
    : UU
    := let x := π₂ (π₁ (tm_var _)) : tm ((𝟙 ×h X) ×h Y) X in
       let y := π₂ (tm_var _) : tm ((𝟙 ×h X) ×h Y) Y in
       ⊤ ⊢ (∀h ∀h (φ [ ⟨ x , y ⟩ ] ⇒ x ~ x)).

  (**
     The second law expresses strictness with regards to the codomain
   *)
  Definition partial_setoid_mor_cod_defined_law
             (φ : form (X ×h Y))
    : UU
    := let x := π₂ (π₁ (tm_var _)) : tm ((𝟙 ×h X) ×h Y) X in
       let y := π₂ (tm_var _) : tm ((𝟙 ×h X) ×h Y) Y in
       ⊤ ⊢ (∀h ∀h (φ [ ⟨ x , y ⟩ ] ⇒ y ~ y)).

  (**
     The third law expresses that the formula is relational.
   *)
  Definition partial_setoid_mor_eq_defined_law
             (φ : form (X ×h Y))
    : UU
    := let x₁ := π₂ (π₁ (π₁ (π₁ (tm_var _)))) : tm ((((𝟙 ×h X) ×h X) ×h Y) ×h Y) X in
       let x₂ := π₂ (π₁ (π₁ (tm_var _))) : tm ((((𝟙 ×h X) ×h X) ×h Y) ×h Y) X in
       let y₁ := π₂ (π₁ (tm_var _)) : tm ((((𝟙 ×h X) ×h X) ×h Y) ×h Y) Y in
       let y₂ := π₂ (tm_var _) : tm ((((𝟙 ×h X) ×h X) ×h Y) ×h Y) Y in
       ⊤ ⊢ (∀h ∀h ∀h ∀h (x₁ ~ x₂
                         ⇒ y₁ ~ y₂
                         ⇒ φ [ ⟨ x₁ , y₁ ⟩ ]
                         ⇒ φ [ ⟨ x₂ , y₂ ⟩ ])).

  (**
     The fourth law expresses that the formula is functional.
   *)
  Definition partial_setoid_mor_unique_im_law
             (φ : form (X ×h Y))
    : UU
    := let x := π₂ (π₁ (π₁ (tm_var _))) : tm (((𝟙 ×h X) ×h Y) ×h Y) X in
       let y₁ := π₂ (π₁ (tm_var _)) : tm (((𝟙 ×h X) ×h Y) ×h Y) Y in
       let y₂ := π₂ (tm_var _) : tm (((𝟙 ×h X) ×h Y) ×h Y) Y in
       ⊤ ⊢ (∀h ∀h ∀h (φ [ ⟨ x , y₁ ⟩ ] ⇒ φ [ ⟨ x , y₂ ⟩ ] ⇒ y₁ ~ y₂)).

  (**
     The final law expresses that the formula is total.
   *)
  Definition partial_setoid_mor_hom_exists_law
             (φ : form (X ×h Y))
    : UU
    := let x := π₂ (tm_var _) : tm (𝟙 ×h X) X in
       let y := π₂ (tm_var _) : tm ((𝟙 ×h X) ×h Y) Y in
       ⊤ ⊢ (∀h (x ~ x ⇒ ∃h (φ [ ⟨ x [ π₁ (tm_var _) ]tm , y ⟩ ]))).

  Definition partial_setoid_morphism_laws
             (φ : form (X ×h Y))
    : UU
    := partial_setoid_mor_dom_defined_law φ
       ×
       partial_setoid_mor_cod_defined_law φ
       ×
       partial_setoid_mor_eq_defined_law φ
       ×
       partial_setoid_mor_unique_im_law φ
       ×
       partial_setoid_mor_hom_exists_law φ.

  Proposition isaprop_partial_setoid_morphism_laws
              (φ : form (X ×h Y))
    : isaprop (partial_setoid_morphism_laws φ).
  Proof.
    repeat (use isapropdirprod) ;
    apply invproofirrelevance ;
    intros ? ? ;
    apply hyperdoctrine_proof_eq.
  Qed.

  (** * 2. Partial setoid morphisms *)
  Definition partial_setoid_morphism
    : UU
    := ∑ (φ : form (X ×h Y)),
       partial_setoid_morphism_laws φ.

  Proposition isaset_partial_setoid_morphism
    : isaset partial_setoid_morphism.
  Proof.
    use isaset_total2.
    - apply isaset_hyperdoctrine_formula.
    - intro.
      apply isasetaprop.
      apply isaprop_partial_setoid_morphism_laws.
  Qed.

  Definition make_partial_setoid_morphism
             (φ : form (X ×h Y))
             (Hφ : partial_setoid_morphism_laws φ)
    : partial_setoid_morphism
    := φ ,, Hφ.

  Coercion partial_setoid_morphism_to_form
           (φ : partial_setoid_morphism)
    : form (X ×h Y).
  Proof.
    exact (pr1 φ).
  Defined.

  Proposition eq_partial_setoid_morphism
              {φ₁ φ₂ : partial_setoid_morphism}
              (p : φ₁ ⊢ φ₂)
              (q : φ₂ ⊢ φ₁)
    : φ₁ = φ₂.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_partial_setoid_morphism_laws.
    }
    use hyperdoctrine_formula_eq.
    - exact p.
    - exact q.
  Qed.

  Proposition from_eq_partial_setoid_morphism_f
              {φ₁ φ₂ : partial_setoid_morphism}
              (p : φ₁ = φ₂)
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ : tm Γ X}
              {t₂ : tm Γ Y}
              (q : Δ ⊢ φ₁ [ ⟨ t₁ , t₂ ⟩ ])
    : Δ ⊢ φ₂ [ ⟨ t₁ , t₂ ⟩ ].
  Proof.
    refine (hyperdoctrine_cut q _).
    use hyperdoctrine_proof_subst.
    exact (hyperdoctrine_formula_eq_f (maponpaths pr1 p)).
  Qed.

  Proposition from_eq_partial_setoid_morphism_b
              {φ₁ φ₂ : partial_setoid_morphism}
              (p : φ₁ = φ₂)
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ : tm Γ X}
              {t₂ : tm Γ Y}
              (q : Δ ⊢ φ₂ [ ⟨ t₁ , t₂ ⟩ ])
    : Δ ⊢ φ₁ [ ⟨ t₁ , t₂ ⟩ ].
  Proof.
    refine (hyperdoctrine_cut q _).
    use hyperdoctrine_proof_subst.
    exact (hyperdoctrine_formula_eq_b (maponpaths pr1 p)).
  Qed.

  (** * 3. Accessors for partial setoid morphisms *)

  (**
     For each law we have a corresponding accessor. The accessors below are designed in such
     a way that they are more convenient to use. The substitutions are already calculated,
     and the necessary elimination rules for the universal quantifier and the implication are
     already instantiated. Finally, it is sufficiently weakened, so that one can apply them
     with an arbitrary context of assumptions.
   *)
  Proposition partial_setoid_mor_dom_defined
              (φ : partial_setoid_morphism)
              {Γ : ty H}
              {Δ : form Γ}
              (x : tm Γ X)
              (y : tm Γ Y)
              (p : Δ ⊢ φ [ ⟨ x , y ⟩ ])
    : Δ ⊢ x ~ x.
  Proof.
    pose (q := pr12 φ).
    unfold partial_setoid_mor_dom_defined_law in q ; cbn in q.
    pose (x' := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h Y)))).
    pose (y' := π₂ (tm_var ((𝟙 ×h X) ×h Y))).
    fold x' y' in q.
    pose proof (hyperdoctrine_proof_subst (!! : tm Γ 𝟙) q) as q'.
    clear q.
    rename q' into q.
    rewrite truth_subst in q.
    rewrite !forall_subst in q.
    rewrite impl_subst in q.
    rewrite partial_setoid_subst in q.
    rewrite !hyperdoctrine_pair_subst in q.
    rewrite !hyperdoctrine_unit_tm_subst in q.
    rewrite !hyperdoctrine_comp_subst in q.
    rewrite !hyperdoctrine_pair_subst in q.
    unfold x', y' in q ; clear x' y'.
    rewrite !hyperdoctrine_pr2_subst in q.
    rewrite !hyperdoctrine_pr1_subst in q.
    rewrite !var_tm_subst in q.
    rewrite hyperdoctrine_pair_pr1 in q.
    rewrite !hyperdoctrine_pair_pr2 in q.
    pose (x' := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
    pose (y' := π₂ (tm_var ((Γ ×h X) ×h Y))).
    fold x' y' in q.
    pose proof (forall_elim q x) as q'.
    clear q.
    rename q' into q.
    rewrite !forall_subst in q.
    rewrite impl_subst in q.
    rewrite partial_setoid_subst in q.
    rewrite !hyperdoctrine_pair_subst in q.
    rewrite var_tm_subst in q.
    rewrite !hyperdoctrine_comp_subst in q.
    rewrite !hyperdoctrine_pair_subst in q.
    unfold x', y' in q ;clear x' y'.
    rewrite !hyperdoctrine_pr2_subst in q.
    rewrite hyperdoctrine_pr1_subst in q.
    rewrite var_tm_subst in q.
    rewrite hyperdoctrine_pair_pr1 in q.
    rewrite !hyperdoctrine_pair_pr2 in q.
    pose proof (forall_elim q y) as q'.
    clear q.
    rename q' into q.
    rewrite impl_subst in q.
    rewrite partial_setoid_subst in q.
    rewrite !hyperdoctrine_comp_subst in q.
    rewrite !hyperdoctrine_pair_subst in q.
    rewrite !hyperdoctrine_pr2_subst in q.
    rewrite var_tm_subst in q.
    rewrite !hyperdoctrine_pair_pr2 in q.
    rewrite tm_subst_comp in q.
    rewrite hyperdoctrine_pr1_subst in q.
    rewrite var_tm_subst in q.
    rewrite hyperdoctrine_pair_pr1 in q.
    rewrite !tm_subst_var in q.
    pose proof (weaken_to_empty q : Δ ⊢ _) as q'.
    clear q.
    rename q' into q.
    exact (impl_elim p q).
  Qed.

  Proposition partial_setoid_mor_cod_defined
              (φ : partial_setoid_morphism)
              {Γ : ty H}
              {Δ : form Γ}
              (x : tm Γ X)
              (y : tm Γ Y)
              (p : Δ ⊢ φ [ ⟨ x , y ⟩ ])
    : Δ ⊢ y ~ y.
  Proof.
    pose (q := pr122 φ).
    unfold partial_setoid_mor_cod_defined_law in q ; cbn in q.
    pose (x' := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h Y)))).
    pose (y' := π₂ (tm_var ((𝟙 ×h X) ×h Y))).
    fold x' y' in q.
    pose proof (hyperdoctrine_proof_subst (!! : tm Γ 𝟙) q) as q'.
    clear q.
    rename q' into q.
    rewrite truth_subst in q.
    rewrite !forall_subst in q.
    rewrite impl_subst in q.
    rewrite partial_setoid_subst in q.
    rewrite !hyperdoctrine_pair_subst in q.
    rewrite !hyperdoctrine_unit_tm_subst in q.
    rewrite !hyperdoctrine_comp_subst in q.
    rewrite !hyperdoctrine_pair_subst in q.
    unfold x', y' in q ; clear x' y'.
    rewrite !hyperdoctrine_pr2_subst in q.
    rewrite !hyperdoctrine_pr1_subst in q.
    rewrite !var_tm_subst in q.
    rewrite hyperdoctrine_pair_pr1 in q.
    rewrite !hyperdoctrine_pair_pr2 in q.
    pose (x' := π₂ (π₁ (tm_var ((Γ ×h X) ×h Y)))).
    pose (y' := π₂ (tm_var ((Γ ×h X) ×h Y))).
    fold x' y' in q.
    pose proof (forall_elim q x) as q'.
    clear q.
    rename q' into q.
    rewrite !forall_subst in q.
    rewrite impl_subst in q.
    rewrite partial_setoid_subst in q.
    rewrite !hyperdoctrine_pair_subst in q.
    rewrite var_tm_subst in q.
    rewrite !hyperdoctrine_comp_subst in q.
    rewrite !hyperdoctrine_pair_subst in q.
    unfold x', y' in q ;clear x' y'.
    rewrite !hyperdoctrine_pr2_subst in q.
    rewrite hyperdoctrine_pr1_subst in q.
    rewrite var_tm_subst in q.
    rewrite hyperdoctrine_pair_pr1 in q.
    rewrite !hyperdoctrine_pair_pr2 in q.
    pose proof (forall_elim q y) as q'.
    clear q.
    rename q' into q.
    rewrite impl_subst in q.
    rewrite partial_setoid_subst in q.
    rewrite !hyperdoctrine_comp_subst in q.
    rewrite !hyperdoctrine_pair_subst in q.
    rewrite !hyperdoctrine_pr2_subst in q.
    rewrite var_tm_subst in q.
    rewrite !hyperdoctrine_pair_pr2 in q.
    rewrite tm_subst_comp in q.
    rewrite hyperdoctrine_pr1_subst in q.
    rewrite var_tm_subst in q.
    rewrite hyperdoctrine_pair_pr1 in q.
    rewrite !tm_subst_var in q.
    pose proof (weaken_to_empty q : Δ ⊢ _) as q'.
    clear q.
    rename q' into q.
    exact (impl_elim p q).
  Qed.

  Proposition partial_setoid_mor_eq_defined
              (φ : partial_setoid_morphism)
              {Γ : ty H}
              {Δ : form Γ}
              {x₁ x₂ : tm Γ X}
              {y₁ y₂ : tm Γ Y}
              (px : Δ ⊢ x₁ ~ x₂)
              (py : Δ ⊢ y₁ ~ y₂)
              (q : Δ ⊢ φ [ ⟨ x₁ , y₁ ⟩ ])
    : Δ ⊢ φ [ ⟨ x₂ , y₂ ⟩ ].
  Proof.
    pose (r := pr1 (pr222 φ)).
    unfold partial_setoid_mor_eq_defined_law in r ; cbn in r.
    pose (x₁' := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h X) ×h X) ×h Y) ×h Y)))))).
    pose (x₂' := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h X) ×h X) ×h Y) ×h Y))))).
    pose (y₁' := π₂ (π₁ (tm_var ((((𝟙 ×h X) ×h X) ×h Y) ×h Y)))).
    pose (y₂' := π₂ (tm_var ((((𝟙 ×h X) ×h X) ×h Y) ×h Y))).
    fold x₁' x₂' y₁' y₂' in r.
    pose proof (hyperdoctrine_proof_subst (!! : tm Γ 𝟙) r) as r'.
    clear r.
    rename r' into r.
    rewrite truth_subst in r.
    rewrite !forall_subst in r.
    rewrite !impl_subst in r.
    rewrite !partial_setoid_subst in r.
    rewrite !hyperdoctrine_comp_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_unit_tm_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    unfold x₁', x₂', y₁', y₂' in r ; clear x₁' x₂' y₁' y₂'.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    pose (x₁' := π₂ (π₁ (π₁ (π₁ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y)))))).
    pose (x₂' := π₂ (π₁ (π₁ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y))))).
    pose (y₁' := π₂ (π₁ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y)))).
    pose (y₂' := π₂ (tm_var ((((Γ ×h X) ×h X) ×h Y) ×h Y))).
    fold x₁' x₂' y₁' y₂' in r.
    pose proof (forall_elim r x₁) as r'.
    clear r.
    rename r' into r.
    rewrite !forall_subst in r.
    rewrite !impl_subst in r.
    rewrite !partial_setoid_subst in r.
    rewrite !hyperdoctrine_comp_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    unfold x₁', x₂', y₁', y₂' in r ; clear x₁' x₂' y₁' y₂'.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    rewrite !tm_subst_comp in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    pose proof (forall_elim r x₂) as r'.
    clear r.
    rename r' into r.
    rewrite !forall_subst in r.
    rewrite !impl_subst in r.
    rewrite !partial_setoid_subst in r.
    rewrite !hyperdoctrine_comp_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !tm_subst_comp in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    pose proof (forall_elim r y₁) as r'.
    clear r.
    rename r' into r.
    rewrite !forall_subst in r.
    rewrite !impl_subst in r.
    rewrite !partial_setoid_subst in r.
    rewrite !hyperdoctrine_comp_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !tm_subst_comp in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    pose proof (forall_elim r y₂) as r'.
    clear r.
    rename r' into r.
    rewrite !impl_subst in r.
    rewrite !partial_setoid_subst in r.
    rewrite !hyperdoctrine_comp_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !tm_subst_comp in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    rewrite !tm_subst_var in r.
    pose proof (weaken_to_empty r : Δ ⊢ _) as r'.
    clear r.
    rename r' into r.
    pose proof (impl_elim px r) as r'.
    clear r.
    rename r' into r.
    pose proof (impl_elim py r) as r'.
    clear r.
    rename r' into r.
    exact (impl_elim q r).
  Qed.

  Proposition partial_setoid_mor_unique_im
              (φ : partial_setoid_morphism)
              {Γ : ty H}
              {Δ : form Γ}
              {x : tm Γ X}
              {y₁ y₂ : tm Γ Y}
              (p₁ : Δ ⊢ φ [ ⟨ x , y₁ ⟩ ])
              (p₂ : Δ ⊢ φ [ ⟨ x , y₂ ⟩ ])
    : Δ ⊢ y₁ ~ y₂.
  Proof.
    pose (r := pr12 (pr222 φ)).
    unfold partial_setoid_mor_unique_im_law in r ; cbn in r.
    pose (x' := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X) ×h Y) ×h Y))))).
    pose (y₁' := π₂ (π₁ (tm_var (((𝟙 ×h X) ×h Y) ×h Y)))).
    pose (y₂' := π₂ (tm_var (((𝟙 ×h X) ×h Y) ×h Y))).
    fold x' y₁' y₂' in r.
    pose proof (hyperdoctrine_proof_subst (!! : tm Γ 𝟙) r) as r'.
    clear r.
    rename r' into r.
    rewrite truth_subst in r.
    rewrite !forall_subst in r.
    rewrite !impl_subst in r.
    rewrite partial_setoid_subst in r.
    rewrite !hyperdoctrine_comp_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_unit_tm_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    unfold x', y₁', y₂' in r ; clear x' y₁' y₂'.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    pose (x' := π₂ (π₁ (π₁ (tm_var (((Γ ×h X) ×h Y) ×h Y))))).
    pose (y₁' := π₂ (π₁ (tm_var (((Γ ×h X) ×h Y) ×h Y)))).
    pose (y₂' := π₂ (tm_var (((Γ ×h X) ×h Y) ×h Y))).
    fold x' y₁' y₂' in r.
    pose proof (forall_elim r x) as r'.
    clear r.
    rename r' into r.
    rewrite !forall_subst in r.
    rewrite !impl_subst in r.
    rewrite partial_setoid_subst in r.
    rewrite !hyperdoctrine_comp_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !tm_subst_comp in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    unfold x', y₁', y₂' in r ; clear x' y₁' y₂'.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    pose proof (forall_elim r y₁) as r'.
    clear r.
    rename r' into r.
    rewrite !forall_subst in r.
    rewrite !impl_subst in r.
    rewrite partial_setoid_subst in r.
    rewrite !hyperdoctrine_comp_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !tm_subst_comp in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    pose proof (forall_elim r y₂) as r'.
    clear r.
    rename r' into r.
    rewrite !impl_subst in r.
    rewrite partial_setoid_subst in r.
    rewrite !hyperdoctrine_comp_subst in r.
    rewrite !hyperdoctrine_pair_subst in r.
    rewrite !hyperdoctrine_pr2_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !tm_subst_comp in r.
    rewrite !hyperdoctrine_pr1_subst in r.
    rewrite !var_tm_subst in r.
    rewrite !hyperdoctrine_pair_pr1 in r.
    rewrite !hyperdoctrine_pair_pr2 in r.
    rewrite !tm_subst_var in r.
    pose proof (weaken_to_empty r : Δ ⊢ _) as r'.
    clear r.
    rename r' into r.
    pose proof (impl_elim p₁ r) as r'.
    clear r.
    rename r' into r.
    exact (impl_elim p₂ r).
  Qed.

  Proposition partial_setoid_mor_hom_exists
              (φ : partial_setoid_morphism)
              {Γ : ty H}
              {Δ : form Γ}
              {x : tm Γ X}
              (p : Δ ⊢ x ~ x)
    : Δ ⊢ (∃h (φ [ ⟨ x [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ])).
  Proof.
    pose (q := pr22 (pr222 φ)).
    unfold partial_setoid_mor_hom_exists_law in q ; cbn in q.
    pose (x' := π₂ (tm_var (𝟙 ×h X))).
    pose (y := π₂ (tm_var ((𝟙 ×h X) ×h Y))).
    fold x' y in q.
    pose proof (hyperdoctrine_proof_subst (!! : tm Γ 𝟙) q) as q'.
    clear q.
    rename q' into q.
    rewrite truth_subst in q.
    rewrite !forall_subst in q.
    rewrite impl_subst in q.
    rewrite partial_setoid_subst in q.
    rewrite exists_subst in q.
    rewrite !hyperdoctrine_comp_subst in q.
    rewrite !hyperdoctrine_pair_subst in q.
    rewrite !hyperdoctrine_unit_tm_subst in q.
    rewrite !tm_subst_comp in q.
    rewrite !hyperdoctrine_pr1_subst in q.
    rewrite !hyperdoctrine_pr2_subst in q.
    rewrite !var_tm_subst in q.
    rewrite !hyperdoctrine_pair_pr1 in q.
    unfold x', y in q ; clear x' y.
    rewrite !hyperdoctrine_pr2_subst in q.
    rewrite !var_tm_subst in q.
    rewrite !hyperdoctrine_pair_pr2 in q.
    pose proof (forall_elim q x) as q'.
    clear q.
    rename q' into q.
    rewrite impl_subst in q.
    rewrite partial_setoid_subst in q.
    rewrite exists_subst in q.
    rewrite !hyperdoctrine_comp_subst in q.
    rewrite !hyperdoctrine_pair_subst in q.
    rewrite !hyperdoctrine_pr2_subst in q.
    rewrite !hyperdoctrine_pr1_subst in q.
    rewrite !var_tm_subst in q.
    rewrite !hyperdoctrine_pair_pr2 in q.
    rewrite !hyperdoctrine_pair_pr1 in q.
    rewrite !hyperdoctrine_pair_pr2 in q.
    pose proof (weaken_to_empty q : Δ ⊢ _) as q'.
    clear q.
    rename q' into q.
    exact (impl_elim p q).
  Qed.
End PartialEquivalenceRelationMorphisms.

Arguments partial_setoid_morphism {H} X Y.


(***************************)


Section PartialEquivalenceRelationEqualizer.
  Context {H : first_order_hyperdoctrine}
          {X Y : partial_setoid H}
          (φ ψ : partial_setoid_morphism X Y).

  Definition equalizer_per_form
    : form (X ×h X)
    := let x := π₁ (tm_var (X ×h X)) in
       let x' := π₂ (tm_var (X ×h X)) in
       let y := π₂ (tm_var ((X ×h X) ×h Y)) in
       x ~ x'
       ∧
       (∃h (φ [ ⟨ x [ π₁ (tm_var _) ]tm , y ⟩ ] ∧ ψ [ ⟨ x [ π₁ (tm_var _) ]tm , y ⟩ ])).

  Proposition equalizer_per_axioms
    : per_axioms equalizer_per_form.
  Proof.
    unfold equalizer_per_form.
    repeat split.
    - pose (x := π₁ (tm_var (X ×h X))).
      pose (x' := π₂ (tm_var (X ×h X))).
      pose (y := π₂ (tm_var ((X ×h X) ×h Y))).
      fold x x' y.
      unfold per_symm_axiom.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      simplify_form.
      rewrite !partial_setoid_subst.
      unfold x, x', y ; clear x x' y.
      simplify.
      use conj_intro.
      + pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h X)))).
        pose (x' := π₂ (tm_var ((𝟙 ×h X) ×h X))).
        fold x x'.
        use weaken_left.
        use partial_setoid_sym.
        apply hyperdoctrine_hyp.
      + use (exists_elim (weaken_right (hyperdoctrine_hyp _) _)).
        use hyp_sym.
        simplify_form.
        rewrite partial_setoid_subst.
        use hyp_rtrans.
        use weaken_left.
        use exists_intro.
        * exact (π₂ (tm_var _)).
        * simplify.
          pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h Y))))).
          pose (x' := π₂ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h Y)))).
          pose (y := π₂ (tm_var (((𝟙 ×h X) ×h X) ×h Y))).
          fold x x' y.
          use conj_intro.
          ** use (partial_setoid_mor_eq_defined φ).
             *** exact x.
             *** exact y.
             *** use weaken_right.
                 apply hyperdoctrine_hyp.
             *** do 2 use weaken_left.
                 exact (partial_setoid_mor_cod_defined φ _ _ (hyperdoctrine_hyp _)).
             *** do 2 use weaken_left.
                 apply hyperdoctrine_hyp.
          ** use (partial_setoid_mor_eq_defined ψ).
             *** exact x.
             *** exact y.
             *** use weaken_right.
                 apply hyperdoctrine_hyp.
             *** do 2 use weaken_left.
                 exact (partial_setoid_mor_cod_defined φ _ _ (hyperdoctrine_hyp _)).
             *** use weaken_left.
                 use weaken_right.
                 apply hyperdoctrine_hyp.
    - unfold per_trans_axiom.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      pose (x₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h X))))).
      pose (x₂ := π₂ (π₁ (tm_var (((𝟙 ×h X) ×h X) ×h X)))).
      pose (x₃ := π₂ (tm_var (((𝟙 ×h X) ×h X) ×h X))).
      fold x₁ x₂ x₃.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      simplify_form.
      use hyp_ltrans.
      use weaken_right.
      use impl_intro.
      use hyp_rtrans.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      simplify_form.
      use hyp_ltrans.
      use weaken_right.
      use conj_intro.
      + unfold x₁, x₂, x₃ ; clear x₁ x₂ x₃.
        rewrite !partial_setoid_subst.
        simplify.
        pose (x₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y))))))).
        pose (x₂ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y)))))).
        pose (x₃ := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y))))).
        pose (y₁ := π₂ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y)))).
        pose (y₂ := π₂ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y))).
        fold x₁ x₂ x₃ y₁ y₂.
        use partial_setoid_trans.
        * exact x₂.
        * do 3 use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
      + use exists_intro.
        * exact (π₂ (tm_var _)).
        * unfold x₁, x₂, x₃ ; clear x₁ x₂ x₃.
          simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          pose (x₁ := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y))))))).
          pose (x₂ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y)))))).
          pose (x₃ := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y))))).
          pose (y₁ := π₂ (π₁ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y)))).
          pose (y₂ := π₂ (tm_var (((((𝟙 ×h X) ×h X) ×h X) ×h Y) ×h Y))).
          fold x₁ x₂ x₃ y₁ y₂.
          use conj_intro.
          ** use (partial_setoid_mor_eq_defined φ).
             *** exact x₂.
             *** exact y₂.
             *** use partial_setoid_sym.
                 do 3 use weaken_left.
                 apply hyperdoctrine_hyp.
             *** do 2 use weaken_right.
                 use (partial_setoid_mor_cod_defined ψ x₂).
                 apply hyperdoctrine_hyp.
             *** use weaken_right.
                 use weaken_left.
                 apply hyperdoctrine_hyp.
          ** use (partial_setoid_mor_eq_defined ψ).
             *** exact x₂.
             *** exact y₂.
             *** use partial_setoid_sym.
                 do 3 use weaken_left.
                 apply hyperdoctrine_hyp.
             *** do 2 use weaken_right.
                 use (partial_setoid_mor_cod_defined ψ x₂).
                 apply hyperdoctrine_hyp.
             *** do 2 use weaken_right.
                 apply hyperdoctrine_hyp.
  Qed.

  Definition equalizer_per
    : per X.
  Proof.
    use make_per.
    - exact equalizer_per_form.
    - exact equalizer_per_axioms.
  Defined.

  Definition equalizer_partial_setoid
    : partial_setoid H.
  Proof.
    use make_partial_setoid.
    - exact X.
    - exact equalizer_per.
  Defined.

  Definition equalizer_partial_setoid_to_type
             {Γ : ty H}
             (t : tm Γ equalizer_partial_setoid)
    : tm Γ X
    := t.

  Notation "'ι'" := equalizer_partial_setoid_to_type.

  Proposition eq_in_equalizer_partial_setoid
              {Γ : ty H}
              {Δ : form Γ}
              (t₁ t₂ : tm Γ equalizer_partial_setoid)
              (p : Δ ⊢ ι t₁ ~ ι t₂)
              (q : Δ ⊢ ∃h (φ [ ⟨ t₁ [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ]
                           ∧
                           ψ [ ⟨ t₁ [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ]))
    : Δ ⊢ t₁ ~ t₂.
  Proof.
    refine (weaken_cut p _).
    unfold partial_setoid_formula ; cbn.
    unfold equalizer_per_form.
    simplify_form.
    rewrite partial_setoid_subst.
    simplify.
    use conj_intro.
    - use weaken_right.
      apply hyperdoctrine_hyp.
    - use weaken_left.
      exact q.
  Qed.

  Proposition from_eq_in_equalizer_partial_setoid
              {Γ : ty H}
              {Δ : form Γ}
              (t₁ t₂ : tm Γ equalizer_partial_setoid)
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ ι t₁ ~ ι t₂.
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    unfold equalizer_per_form.
    rewrite conj_subst.
    use weaken_left.
    rewrite partial_setoid_subst.
    simplify.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition from_eq_in_equalizer_partial_setoid_ex
              {Γ : ty H}
              {Δ : form Γ}
              (t₁ t₂ : tm Γ equalizer_partial_setoid)
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ ∃h (φ [ ⟨ t₁ [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ]
              ∧
              ψ [ ⟨ t₁ [ π₁ (tm_var _) ]tm , π₂ (tm_var _) ⟩ ]).
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    unfold equalizer_per_form.
    rewrite conj_subst.
    use weaken_right.
    simplify.
    apply hyperdoctrine_hyp.
  Qed.

  Definition equalizer_partial_setoid_morphism_form
    : form (equalizer_partial_setoid ×h X)
    := let x₁ := π₁ (tm_var _) in
       let x₂ := π₂ (tm_var _) in
       x₁ ~ x₂.

  Proposition equalizer_partial_setoid_morphism_laws
    : partial_setoid_morphism_laws equalizer_partial_setoid_morphism_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      pose (T := equalizer_partial_setoid).
      pose (T' := X).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      unfold equalizer_partial_setoid_morphism_form.
      fold x y.
      cbn.
      rewrite partial_setoid_subst.
      simplify.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
    - unfold partial_setoid_mor_cod_defined_law.
      pose (T := equalizer_partial_setoid).
      pose (T' := X).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      unfold equalizer_partial_setoid_morphism_form.
      fold x y.
      cbn.
      rewrite partial_setoid_subst.
      simplify.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use partial_setoid_refl_r.
      + exact x.
      + use from_eq_in_equalizer_partial_setoid.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law.
      pose (T := equalizer_partial_setoid).
      pose (T' := X).
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
      pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
      pose (y₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      unfold equalizer_partial_setoid_morphism_form.
      fold x₁ x₂ y₁ y₂.
      cbn.
      rewrite !partial_setoid_subst.
      simplify.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      use partial_setoid_trans.
      + exact x₁.
      + use partial_setoid_sym.
        do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + use partial_setoid_trans.
        * exact y₁.
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use hyp_ltrans.
          use weaken_right.
          use eq_in_equalizer_partial_setoid.
          ** use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             use from_eq_in_equalizer_partial_setoid_ex.
             *** exact x₁.
             *** use partial_setoid_sym.
                 apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law.
      pose (T := equalizer_partial_setoid).
      pose (T' := X).
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
      pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
      pose (y₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      unfold equalizer_partial_setoid_morphism_form.
      fold x y₁ y₂.
      cbn.
      rewrite !partial_setoid_subst.
      simplify.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use hyperdoctrine_cut.
      + exact (ι x ~ ι y₁ ∧ ι x ~ ι y₂).
      + use conj_intro.
        * use weaken_left.
          use from_eq_in_equalizer_partial_setoid.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          use from_eq_in_equalizer_partial_setoid.
          apply hyperdoctrine_hyp.
      + use partial_setoid_trans.
        * exact (ι x).
        * use partial_setoid_sym.
          use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      pose (T := equalizer_partial_setoid).
      pose (T' := X).
      pose (x := π₂ (tm_var (𝟙 ×h T))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      unfold equalizer_partial_setoid_morphism_form.
      fold x y.
      cbn.
      rewrite !partial_setoid_subst.
      simplify.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use exists_intro.
      {
        exact (π₂ (tm_var _)).
      }
      unfold x, y ; clear x y.
      simplify_form.
      rewrite partial_setoid_subst.
      simplify.
      cbn.
      pose (x := π₂ (tm_var (𝟙 ×h X))).
      fold x.
      apply hyperdoctrine_hyp.
  Qed.

  Definition equalizer_partial_setoid_morphism
    : partial_setoid_morphism equalizer_partial_setoid X.
  Proof.
    use make_partial_setoid_morphism.
    - exact equalizer_partial_setoid_morphism_form.
    - exact equalizer_partial_setoid_morphism_laws.
  Defined.


End PartialEquivalenceRelationEqualizer.


Definition id_partial_setoid_morphism_form
           {H : first_order_hyperdoctrine}
           (X : partial_setoid H)
  : form (X ×h X)
  := π₁ (tm_var _) ~ π₂ (tm_var _).

Arguments id_partial_setoid_morphism_form {H} X /.

Proposition id_partial_setoid_morphism_laws
            {H : first_order_hyperdoctrine}
            (X : partial_setoid H)
  : partial_setoid_morphism_laws (id_partial_setoid_morphism_form X).
Proof.
  repeat split.
  - unfold partial_setoid_mor_dom_defined_law.
    pose (T := X).
    pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T)))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T))).
    unfold T in *.
    fold x y.
    cbn.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    rewrite partial_setoid_subst.
    simplify.
    exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
  - unfold partial_setoid_mor_cod_defined_law.
    pose (T := X).
    pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T)))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T))).
    unfold T in *.
    fold x y.
    cbn.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    rewrite partial_setoid_subst.
    simplify.
    exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
  - unfold partial_setoid_mor_eq_defined_law.
    pose (T := X).
    pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T) ×h T)))))).
    pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T) ×h T))))).
    pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T) ×h T)))).
    pose (y₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T) ×h T))).
    unfold T in *.
    fold x₁ x₂ y₁ y₂.
    cbn.
    use forall_intro.
    use forall_intro.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    use impl_intro.
    rewrite !partial_setoid_subst.
    simplify.
    use partial_setoid_trans.
    + exact x₁.
    + use partial_setoid_sym.
      do 2 use weaken_left.
      use hyperdoctrine_hyp.
    + use partial_setoid_trans.
      * exact y₁.
      * use weaken_right.
        use hyperdoctrine_hyp.
      * use weaken_left.
        use weaken_right.
        use hyperdoctrine_hyp.
  - unfold partial_setoid_mor_unique_im_law.
    pose (T := X).
    pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T) ×h T))))).
    pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T) ×h T)))).
    pose (y₂ := π₂ (tm_var (((𝟙 ×h T) ×h T) ×h T))).
    unfold T in *.
    fold x y₁ y₂.
    cbn.
    use forall_intro.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    rewrite !partial_setoid_subst.
    simplify.
    use partial_setoid_trans.
    + exact x.
    + use partial_setoid_sym.
      use weaken_left.
      use hyperdoctrine_hyp.
    + use weaken_right.
      use hyperdoctrine_hyp.
  - unfold partial_setoid_mor_hom_exists_law.
    pose (T := X).
    pose (x := π₂ (tm_var (𝟙 ×h T))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T))).
    unfold T in *.
    fold x y.
    cbn.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    rewrite partial_setoid_subst.
    simplify.
    use exists_intro.
    + exact x.
    + unfold y.
      rewrite partial_setoid_subst.
      simplify.
      use hyperdoctrine_hyp.
Qed.

Definition id_partial_setoid_morphism
           {H : first_order_hyperdoctrine}
           (X : partial_setoid H)
  : partial_setoid_morphism X X.
Proof.
  use make_partial_setoid_morphism.
  - exact (id_partial_setoid_morphism_form X).
  - exact (id_partial_setoid_morphism_laws X).
Defined.

Section CompPartialSetoidMorphism.
  Context {H : first_order_hyperdoctrine}
          {X Y Z : partial_setoid H}
          (φ₁ : partial_setoid_morphism X Y)
          (φ₂ : partial_setoid_morphism Y Z).

  Definition partial_setoid_comp_morphism_form
    : form (X ×h Z)
    := let x := π₁ (π₁ (tm_var _)) : tm ((X ×h Z) ×h Y) X in
       let y := π₂ (tm_var _) : tm ((X ×h Z) ×h Y) Y in
       let z := π₂ (π₁ (tm_var _)) : tm ((X ×h Z) ×h Y) Z in
       (∃h (φ₁ [ ⟨ x , y ⟩ ] ∧ φ₂ [ ⟨ y , z ⟩ ])).

  Arguments partial_setoid_comp_morphism_form /.

  Proposition partial_setoid_comp_morphism_laws
    : partial_setoid_morphism_laws
        partial_setoid_comp_morphism_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      pose (T := X).
      pose (T' := Z).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (z := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x z.
      unfold partial_setoid_comp_morphism_form.
      simplify.
      pose (y := π₂ (tm_var (((𝟙 ×h X) ×h Z) ×h Y))).
      fold y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      rewrite partial_setoid_subst.
      unfold x, y, z.
      simplify.
      use weaken_left.
      apply (partial_setoid_mor_dom_defined φ₁ _ _ (hyperdoctrine_hyp _)).
    - unfold partial_setoid_mor_cod_defined_law.
      pose (T := X).
      pose (T' := Z).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (z := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x z.
      unfold partial_setoid_comp_morphism_form.
      simplify.
      pose (y := π₂ (tm_var (((𝟙 ×h X) ×h Z) ×h Y))).
      fold y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      rewrite partial_setoid_subst.
      unfold x, y, z.
      simplify.
      use weaken_right.
      apply (partial_setoid_mor_cod_defined φ₂ _ _ (hyperdoctrine_hyp _)).
    - unfold partial_setoid_mor_eq_defined_law.
      pose (T := X).
      pose (T' := Z).
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
      pose (z₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
      pose (z₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x₁ x₂ z₁ z₂.
      unfold partial_setoid_comp_morphism_form.
      simplify.
      pose (y := π₂ (tm_var (((((𝟙 ×h X) ×h X) ×h Z) ×h Z) ×h Y))).
      fold y.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      use hyp_sym.
      refine (exists_elim _ _) ; [ use weaken_left ; apply hyperdoctrine_hyp | ].
      rewrite conj_subst.
      use hyp_ltrans.
      use weaken_right.
      simplify.
      rewrite !partial_setoid_subst.
      use exists_intro.
      + exact (π₂ (tm_var _)).
      + simplify.
        use conj_intro.
        * use hyp_rtrans.
          use weaken_left.
          use hyp_sym.
          use hyp_rtrans.
          use weaken_left.
          unfold x₁, x₂, y.
          simplify.
          use (partial_setoid_mor_eq_defined
                 φ₁
                 _
                 _
                 (weaken_left (hyperdoctrine_hyp _) _)).
          ** use weaken_right.
             use hyperdoctrine_hyp.
          ** use weaken_left.
             exact (partial_setoid_mor_cod_defined φ₁ _ _ (hyperdoctrine_hyp _)).
        * use hyp_ltrans.
          use weaken_right.
          use hyp_sym.
          use hyp_ltrans.
          use weaken_right.
          unfold z₁, z₂, y.
          simplify.
          use (partial_setoid_mor_eq_defined
                 φ₂
                 _
                 _
                 (weaken_left (hyperdoctrine_hyp _) _)).
          ** use weaken_left.
             exact (partial_setoid_mor_dom_defined φ₂ _ _ (hyperdoctrine_hyp _)).
          ** use weaken_right.
             use hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law.
      pose (T := X).
      pose (T' := Z).
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
      pose (z₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
      pose (z₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x z₁ z₂.
      unfold partial_setoid_comp_morphism_form.
      simplify.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      simplify.
      use impl_intro.
      use hyp_sym.
      use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
      rewrite conj_subst.
      use hyp_ltrans.
      use weaken_right.
      simplify.
      rewrite partial_setoid_subst.
      unfold x, z₁, z₂.
      clear x z₁ z₂.
      simplify.
      pose (x := π₂ (π₁ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h Z) ×h Z) ×h Y) ×h Y))))))).
      pose (y := π₂ (π₁ (tm_var (((((𝟙 ×h X) ×h Z) ×h Z) ×h Y) ×h Y)))).
      pose (y' := π₂ (tm_var (((((𝟙 ×h X) ×h Z) ×h Z) ×h Y) ×h Y))).
      pose (z₁ := π₂ (π₁ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h Z) ×h Z) ×h Y) ×h Y)))))).
      pose (z₂ := π₂ (π₁ (π₁ (tm_var (((((𝟙 ×h X) ×h Z) ×h Z) ×h Y) ×h Y))))).
      fold x y y' z₁ z₂.
      use (partial_setoid_mor_unique_im φ₂).
      + exact y.
      + use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
      + use (partial_setoid_mor_eq_defined φ₂).
        * exact y'.
        * exact z₂.
        * use hyp_rtrans.
          use weaken_left.
          use hyp_sym.
          use hyp_rtrans.
          use weaken_left.
          use (partial_setoid_mor_unique_im φ₁).
          ** exact x.
          ** use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
        * use (partial_setoid_mor_cod_defined φ₂).
          ** exact y'.
          ** do 2 use weaken_right.
             apply hyperdoctrine_hyp.
        * do 2 use weaken_right.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      pose (x := π₂ (tm_var (𝟙 ×h X))).
      pose (z := π₂ (tm_var ((𝟙 ×h X) ×h Z))).
      fold x z.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use (exists_elim (partial_setoid_mor_hom_exists φ₁ (hyperdoctrine_hyp _))).
      use weaken_right.
      pose (y := π₂ (tm_var ((𝟙 ×h X) ×h Y))).
      fold y.
      use weaken_cut.
      + exact (y ~ y).
      + exact (partial_setoid_mor_cod_defined φ₁ _ _ (hyperdoctrine_hyp _)).
      + use (exists_elim
               (partial_setoid_mor_hom_exists φ₂ (weaken_right (hyperdoctrine_hyp _) _))).
        simplify_form.
        use hyp_sym.
        use hyp_rtrans.
        use weaken_left.
        use hyp_sym.
        use exists_intro.
        * exact (π₂ (tm_var _)).
        * unfold partial_setoid_comp_morphism_form.
          simplify.
          use exists_intro.
          ** exact (π₂ (π₁ (tm_var _))).
          ** unfold x, y, z.
             simplify.
             apply hyperdoctrine_hyp.
  Qed.

  Definition partial_setoid_comp_morphism
    : partial_setoid_morphism X Z.
  Proof.
    use make_partial_setoid_morphism.
    - exact partial_setoid_comp_morphism_form.
    - exact partial_setoid_comp_morphism_laws.
  Defined.
End CompPartialSetoidMorphism.

Arguments partial_setoid_comp_morphism_form {H X Y Z} φ₁ φ₂ /.


Definition term_partial_setoid_morphism_form
           {H : first_order_hyperdoctrine}
           {X Y : ty H}
           (t : tm X Y)
  : form (eq_partial_setoid X ×h eq_partial_setoid Y)
  := t [ π₁ (tm_var _) ]tm ≡ π₂ (tm_var _).

Arguments term_partial_setoid_morphism_form {H X Y} t /.

Proposition term_partial_setoid_morphism_laws
            {H : first_order_hyperdoctrine}
            {X Y : ty H}
            (t : tm X Y)
  : partial_setoid_morphism_laws (term_partial_setoid_morphism_form t).
Proof.
  unfold term_partial_setoid_morphism_form.
  repeat split.
  - unfold partial_setoid_mor_dom_defined_law.
    cbn ; simplify.
    pose (T := X).
    pose (T' := Y).
    pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
    unfold T, T' in *.
    fold x y.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use eq_in_eq_partial_setoid.
    simplify.
    apply hyperdoctrine_refl.
  - unfold partial_setoid_mor_cod_defined_law.
    cbn ; simplify.
    pose (T := X).
    pose (T' := Y).
    pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
    unfold T, T' in *.
    fold x y.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use eq_in_eq_partial_setoid.
    simplify.
    apply hyperdoctrine_refl.
  - unfold partial_setoid_mor_eq_defined_law.
    cbn ; simplify.
    pose (T := X).
    pose (T' := Y).
    pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
    pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
    pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
    pose (y₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
    unfold T, T' in *.
    fold x₁ x₂ y₁ y₂.
    use forall_intro.
    use forall_intro.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use impl_intro.
    use impl_intro.
    simplify.
    use hyperdoctrine_eq_trans.
    + exact y₁.
    + use hyperdoctrine_eq_trans.
      * exact (t [ x₁ ]tm).
      * use hyperdoctrine_subst_eq.
        use hyperdoctrine_eq_sym.
        do 2 use weaken_left.
        use weaken_right.
        use from_eq_in_eq_partial_setoid.
        apply hyperdoctrine_hyp.
      * use weaken_right.
        apply hyperdoctrine_hyp.
    + use weaken_left.
      use weaken_right.
      use from_eq_in_eq_partial_setoid.
      apply hyperdoctrine_hyp.
  - unfold partial_setoid_mor_unique_im_law.
    cbn ; simplify.
    pose (T := X).
    pose (T' := Y).
    pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
    pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
    pose (y₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
    unfold T, T' in *.
    fold x y₁ y₂.
    use forall_intro.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use impl_intro.
    use eq_in_eq_partial_setoid.
    simplify.
    use hyperdoctrine_eq_trans.
    + exact (t [ x ]tm).
    + use weaken_left.
      use weaken_right.
      use hyperdoctrine_eq_sym.
      apply hyperdoctrine_hyp.
    + use weaken_right.
      apply hyperdoctrine_hyp.
  - unfold partial_setoid_mor_hom_exists_law.
    cbn ; simplify.
    pose (T := X).
    pose (T' := Y).
    pose (x := π₂ (tm_var (𝟙 ×h T))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
    unfold T, T' in *.
    fold x y.
    use forall_intro.
    use impl_intro.
    unfold x, y.
    simplify.
    use exists_intro.
    + exact (t [ π₂ (tm_var _) ]tm).
    + simplify.
      apply hyperdoctrine_refl.
Qed.

Definition term_partial_setoid_morphism
           {H : first_order_hyperdoctrine}
           {X Y : ty H}
           (t : tm X Y)
  : partial_setoid_morphism (eq_partial_setoid X) (eq_partial_setoid Y).
Proof.
  use make_partial_setoid_morphism.
  - exact (term_partial_setoid_morphism_form t).
  - exact (term_partial_setoid_morphism_laws t).
Defined.

Definition partial_setoid_morphism_to_terminal_form
           {H : first_order_hyperdoctrine}
           (X : partial_setoid H)
  : form (X ×h eq_partial_setoid 𝟙)
  := let x := π₁ (tm_var (X ×h 𝟙)) in
     x ~ x.

Arguments partial_setoid_morphism_to_terminal_form {H} X /.

Proposition partial_setoid_morphism_to_terminal_laws
            {H : first_order_hyperdoctrine}
            (X : partial_setoid H)
  : partial_setoid_morphism_laws (partial_setoid_morphism_to_terminal_form X).
Proof.
  unfold partial_setoid_morphism_to_terminal_form.
  repeat split.
  - unfold partial_setoid_mor_dom_defined_law.
    cbn ; simplify.
    rewrite partial_setoid_subst.
    simplify.
    pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h 𝟙)))).
    fold x.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    apply hyperdoctrine_hyp.
  - unfold partial_setoid_mor_cod_defined_law.
    cbn ; simplify.
    rewrite partial_setoid_subst.
    simplify.
    pose (x := π₂ (π₁ (tm_var ((𝟙 ×h X) ×h 𝟙)))).
    pose (y := π₂ (tm_var ((𝟙 ×h X) ×h 𝟙))).
    fold x y.
    use forall_intro.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    use eq_in_eq_partial_setoid.
    apply hyperdoctrine_refl.
  - unfold partial_setoid_mor_eq_defined_law.
    cbn ; simplify.
    rewrite !partial_setoid_subst.
    simplify.
    pose (T := X).
    pose (T' := 𝟙 : ty H).
    pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
    pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
    pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
    pose (y₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
    unfold T, T' in *.
    fold x₁ x₂ y₁ y₂.
    do 4 use forall_intro.
    use impl_intro.
    use weaken_right.
    do 2 use impl_intro.
    do 2 use weaken_left.
    use partial_setoid_refl_r.
    {
      exact x₁.
    }
    apply hyperdoctrine_hyp.
  - unfold partial_setoid_mor_unique_im_law.
    cbn ; simplify.
    rewrite !partial_setoid_subst.
    simplify.
    pose (T := X).
    pose (T' := 𝟙 : ty H).
    pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
    pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
    pose (y₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
    unfold T, T' in *.
    fold x y₁ y₂.
    do 3 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    use eq_in_eq_partial_setoid.
    use hyperdoctrine_unit_tm_eq.
  - unfold partial_setoid_mor_hom_exists_law.
    cbn ; simplify.
    rewrite !partial_setoid_subst.
    simplify.
    pose (T := X).
    pose (T' := 𝟙 : ty H).
    pose (x := π₂ (tm_var (𝟙 ×h T))).
    pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
    unfold T, T' in *.
    fold x y.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    use exists_intro.
    + exact !!.
    + rewrite partial_setoid_subst.
      simplify.
      apply hyperdoctrine_hyp.
Qed.

Definition partial_setoid_morphism_to_terminal
           {H : first_order_hyperdoctrine}
           (X : partial_setoid H)
  : partial_setoid_morphism X (eq_partial_setoid 𝟙).
Proof.
  use make_partial_setoid_morphism.
  - exact (partial_setoid_morphism_to_terminal_form X).
  - exact (partial_setoid_morphism_to_terminal_laws X).
Defined.

Definition partial_setoid_morphism_from_terminal_form
           {H : first_order_hyperdoctrine}
           {X : partial_setoid H}
           {A : ty H}
           (x : tm A X)
  : form (eq_partial_setoid A ×h X)
  := (x [ π₁ (tm_var _) ]tm ~ π₂ (tm_var _)).

Arguments partial_setoid_morphism_from_terminal_form {H X A} x /.

Proposition partial_setoid_morphism_from_terminal_laws
            {H : first_order_hyperdoctrine}
            {X : partial_setoid H}
            {A : ty H}
            (x : tm A X)
  : partial_setoid_morphism_laws
      (partial_setoid_morphism_from_terminal_form x).
Proof.
  repeat split.
  - unfold partial_setoid_mor_dom_defined_law ; cbn.
    simplify_form.
    rewrite partial_setoid_subst.
    simplify.
    pose (x' := π₂ (tm_var ((𝟙 ×h A) ×h X))).
    fold x'.
    do 2 use forall_intro.
    use impl_intro.
    use eq_in_eq_partial_setoid.
    apply hyperdoctrine_refl.
  - unfold partial_setoid_mor_cod_defined_law ; cbn.
    simplify_form.
    rewrite partial_setoid_subst.
    simplify.
    pose (x' := π₂ (tm_var ((𝟙 ×h A) ×h X))).
    fold x'.
    do 2 use forall_intro.
    use impl_intro.
    use weaken_right.
    exact (partial_setoid_refl_r (hyperdoctrine_hyp _)).
  - unfold partial_setoid_mor_eq_defined_law ; cbn.
    rewrite !partial_setoid_subst.
    simplify.
    pose (x' := π₂ (π₁ (tm_var ((((𝟙 ×h A) ×h A) ×h X) ×h X)))).
    pose (x'' := π₂ (tm_var ((((𝟙 ×h A) ×h A) ×h X) ×h X))).
    fold x' x''.
    do 4 use forall_intro.
    use impl_intro.
    use weaken_right.
    do 2 use impl_intro.
    simplify.
    use partial_setoid_trans.
    + exact x'.
    + (*use (partial_setoid_trans _ _ (weaken_right (hyperdoctrine_hyp _) _)).
      do 2 use weaken_left.
      use (hyperdoctrine_cut (from_eq_in_eq_partial_setoid (hyperdoctrine_hyp _))).
      unfold partial_setoid_formula.
      simplify.
      assert (π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h A) ×h 𝟙) ×h X) ×h X)))))
              =
              π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h 𝟙) ×h 𝟙) ×h X) ×h X)))))
        as q.
      {
        use hyperdoctrine_unit_eq.
      }
      rewrite q.
      refine (hyperdoctrine_cut
                  (hyperdoctrine_cut
                     _
                     (hyperdoctrine_proof_subst
                        (π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h 𝟙) ×h 𝟙) ×h X) ×h X)))))
                        p))
                  _).
        ** simplify_form.
           apply truth_intro.
        ** rewrite partial_setoid_subst.
           apply hyperdoctrine_hyp.*)
      admit.
    + use weaken_left.
      use weaken_right.
      apply hyperdoctrine_hyp.
  - unfold partial_setoid_mor_unique_im_law ; cbn.
    rewrite !partial_setoid_subst.
    simplify.
    pose (x' := π₂ (π₁ (tm_var (((𝟙 ×h A) ×h X) ×h X)))).
    pose (x'' := π₂ (tm_var (((𝟙 ×h A) ×h X) ×h X))).
    fold x' x''.
    do 3 use forall_intro.
    use impl_intro.
    use weaken_right.
    use impl_intro.
    use (partial_setoid_trans _ _ (weaken_right (hyperdoctrine_hyp _) _)).
    use partial_setoid_sym.
    use weaken_left.
    apply hyperdoctrine_hyp.
  - unfold partial_setoid_mor_hom_exists_law ; cbn.
    rewrite partial_setoid_subst.
    simplify.
    use forall_intro.
    use impl_intro.
    use weaken_right.
    use exists_intro.
    + exact (x [ π₂ (tm_var _) ]tm).
    + rewrite partial_setoid_subst.
      simplify.
      unfold partial_setoid_formula.
      cbn.
      simplify.
Admitted.

Definition partial_setoid_morphism_from_terminal
           {H : first_order_hyperdoctrine}
           (X : partial_setoid H)
           {A : ty H}
           (x : tm A X)
           (p : ⊤ ⊢ x ~ x)
  : partial_setoid_morphism (eq_partial_setoid A) X.
Proof.
  use make_partial_setoid_morphism.
  - exact (partial_setoid_morphism_from_terminal_form x).
  - exact (partial_setoid_morphism_from_terminal_laws x).
Defined.



Section Projections.
  Context {H : first_order_hyperdoctrine}
          (X Y : partial_setoid H).

  Definition partial_setoid_pr1_form
    : form ((prod_partial_setoid X Y) ×h X)
    := let x := π₁ (π₁ (tm_var _)) : tm ((X ×h Y) ×h X) X in
       let y := π₂ (π₁ (tm_var _)) : tm ((X ×h Y) ×h X) Y in
       let x' := π₂ (tm_var _) : tm ((X ×h Y) ×h X) X in
       x ~ x' ∧ y ~ y.

  Arguments partial_setoid_pr1_form /.

  Proposition partial_setoid_pr1_laws
    : partial_setoid_morphism_laws partial_setoid_pr1_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := X).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      simplify.
      rewrite !partial_setoid_subst.
      use eq_in_prod_partial_setoid.
      + use partial_setoid_refl_l.
        * exact y.
        * simplify.
          use weaken_left.
          use hyperdoctrine_hyp.
      + use weaken_right.
        unfold x.
        simplify.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := X).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      simplify_form.
      use weaken_left.
      rewrite !partial_setoid_subst.
      simplify.
      use partial_setoid_refl_r.
      + exact (π₁ x).
      + apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := X).
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
      pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
      pose (y₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x₁ x₂ y₁ y₂.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use impl_intro.
      cbn.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use conj_intro.
      + use (partial_setoid_trans y₁).
        * use (partial_setoid_trans (π₁ x₁)).
          ** do 2 use weaken_left.
             use partial_setoid_sym.
             use eq_in_prod_partial_setoid_l.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
        * use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
      + do 2 use weaken_left.
        use eq_in_prod_partial_setoid_r.
        use partial_setoid_refl_r ; [ | apply hyperdoctrine_hyp ].
    - unfold partial_setoid_mor_unique_im_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := X).
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
      pose (z₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
      pose (z₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x z₁ z₂.
      cbn.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use partial_setoid_trans.
      + exact (π₁ x).
      + use partial_setoid_sym.
        use weaken_left.
        use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := X).
      pose (x := π₂ (tm_var (𝟙 ×h T))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      cbn.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use exists_intro.
      + exact (π₁ (π₂ (tm_var _))).
      + simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        use conj_intro.
        * unfold y.
          simplify.
          use eq_in_prod_partial_setoid_l.
          apply hyperdoctrine_hyp.
        * use eq_in_prod_partial_setoid_r.
          apply hyperdoctrine_hyp.
  Qed.

  Definition partial_setoid_pr1
    : partial_setoid_morphism (prod_partial_setoid X Y) X.
  Proof.
    use make_partial_setoid_morphism.
    - exact partial_setoid_pr1_form.
    - exact partial_setoid_pr1_laws.
  Defined.

    Definition partial_setoid_pr2_form
    : form ((prod_partial_setoid X Y) ×h Y)
    := let x := π₁ (π₁ (tm_var _)) : tm ((X ×h Y) ×h Y) X in
       let y := π₂ (π₁ (tm_var _)) : tm ((X ×h Y) ×h Y) Y in
       let y' := π₂ (tm_var _) : tm ((X ×h Y) ×h Y) Y in
       x ~ x ∧ y ~ y'.

  Arguments partial_setoid_pr2_form /.

  Proposition partial_setoid_pr2_laws
    : partial_setoid_morphism_laws partial_setoid_pr2_form.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := Y).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      simplify.
      rewrite !partial_setoid_subst.
      use eq_in_prod_partial_setoid.
      + use weaken_left.
        unfold x.
        simplify.
        apply hyperdoctrine_hyp.
      + use partial_setoid_refl_l.
        * exact y.
        * simplify.
          use weaken_right.
          use hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := Y).
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h T) ×h T')))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      cbn.
      simplify_form.
      use weaken_right.
      rewrite !partial_setoid_subst.
      simplify.
      use partial_setoid_refl_r.
      + exact (π₂ x).
      + apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := Y).
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
      pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
      pose (y₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x₁ x₂ y₁ y₂.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use impl_intro.
      cbn.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use conj_intro.
      + do 2 use weaken_left.
        use eq_in_prod_partial_setoid_l.
        use partial_setoid_refl_r ; [ | apply hyperdoctrine_hyp ].
      + use (partial_setoid_trans y₁).
        * use (partial_setoid_trans (π₂ x₁)).
          ** do 2 use weaken_left.
             use partial_setoid_sym.
             use eq_in_prod_partial_setoid_r.
             apply hyperdoctrine_hyp.
          ** do 2 use weaken_right.
             apply hyperdoctrine_hyp.
        * use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := Y).
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
      pose (z₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
      pose (z₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x z₁ z₂.
      cbn.
      use forall_intro.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use partial_setoid_trans.
      + exact (π₂ x).
      + use partial_setoid_sym.
        use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
      + do 2 use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      pose (T := prod_partial_setoid X Y).
      pose (T' := Y).
      pose (x := π₂ (tm_var (𝟙 ×h T))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      cbn.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      use exists_intro.
      + exact (π₂ (π₂ (tm_var _))).
      + simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        use conj_intro.
        * use eq_in_prod_partial_setoid_l.
          apply hyperdoctrine_hyp.
        * unfold y.
          simplify.
          use eq_in_prod_partial_setoid_r.
          apply hyperdoctrine_hyp.
  Qed.

  Definition partial_setoid_pr2
    : partial_setoid_morphism (prod_partial_setoid X Y) Y.
  Proof.
    use make_partial_setoid_morphism.
    - exact partial_setoid_pr2_form.
    - exact partial_setoid_pr2_laws.
  Defined.
End Projections.


Section Pairing.
  Context {H : first_order_hyperdoctrine}
          {W X Y : partial_setoid H}
          (φ : partial_setoid_morphism W X)
          (ψ : partial_setoid_morphism W Y).

  Definition pair_partial_setoid_morphism_form
    : form (W ×h prod_partial_setoid X Y)
    := let w := π₁ (tm_var (W ×h X ×h Y)) in
       let x := π₁ (π₂ (tm_var (W ×h X ×h Y))) in
       let y := π₂ (π₂ (tm_var (W ×h X ×h Y))) in
       φ [ ⟨ w , x ⟩ ] ∧ ψ [ ⟨ w , y ⟩ ].

  Proposition pair_partial_setoid_morphism_laws
    : partial_setoid_morphism_laws pair_partial_setoid_morphism_form.
  Proof.
    unfold pair_partial_setoid_morphism_form.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      cbn ; simplify.
      pose (w := π₂ (π₁ (tm_var ((𝟙 ×h W) ×h X ×h Y)))).
      pose (x := π₁ (π₂ (tm_var ((𝟙 ×h W) ×h X ×h Y)))).
      pose (y := π₂ (π₂ (tm_var ((𝟙 ×h W) ×h X ×h Y)))).
      fold w x y.
      do 2 use forall_intro.
      use impl_intro.
      do 2 use weaken_right.
      use (partial_setoid_mor_dom_defined ψ w y).
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law.
      cbn ; simplify.
      pose (w := π₂ (π₁ (tm_var ((𝟙 ×h W) ×h X ×h Y)))).
      pose (x := π₁ (π₂ (tm_var ((𝟙 ×h W) ×h X ×h Y)))).
      pose (y := π₂ (π₂ (tm_var ((𝟙 ×h W) ×h X ×h Y)))).
      fold w x y.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use eq_in_prod_partial_setoid ; fold x y.
      + use weaken_left.
        use (partial_setoid_mor_cod_defined φ w x).
        apply hyperdoctrine_hyp.
      + use weaken_right.
        use (partial_setoid_mor_cod_defined ψ w y).
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law.
      pose (T := W).
      pose (T' := prod_partial_setoid X Y).
      pose (w₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))))).
      pose (w₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))))).
      pose (xy₁ := π₂ (π₁ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T')))).
      pose (xy₂ := π₂ (tm_var ((((𝟙 ×h T) ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold w₁ w₂ xy₁ xy₂.
      simplify.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      use conj_intro.
      + use hyp_rtrans.
        use weaken_left.
        use (partial_setoid_mor_eq_defined φ).
        * exact w₁.
        * exact (π₁ xy₁).
        * do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          use weaken_right.
          use eq_in_prod_partial_setoid_l.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
      + use hyp_sym.
        use hyp_ltrans.
        use weaken_right.
        use (partial_setoid_mor_eq_defined ψ).
        * exact w₁.
        * exact (π₂ xy₁).
        * use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
        * do 2 use weaken_right.
          use eq_in_prod_partial_setoid_r.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law.
      pose (T := W).
      pose (T' := prod_partial_setoid X Y).
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T'))))).
      pose (z₁ := π₂ (π₁ (tm_var (((𝟙 ×h T) ×h T') ×h T')))).
      pose (z₂ := π₂ (tm_var (((𝟙 ×h T) ×h T') ×h T'))).
      unfold T, T' in *.
      fold x z₁ z₂.
      simplify.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use eq_in_prod_partial_setoid.
      + use hyp_rtrans.
        use weaken_left.
        use hyp_sym.
        use hyp_rtrans.
        use weaken_left.
        use (partial_setoid_mor_unique_im φ).
        * exact x.
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
      + use hyp_ltrans.
        use weaken_right.
        use hyp_sym.
        use hyp_ltrans.
        use weaken_right.
        use (partial_setoid_mor_unique_im ψ).
        * exact x.
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      pose (T := W).
      pose (T' := prod_partial_setoid X Y).
      pose (x := π₂ (tm_var (𝟙 ×h T))).
      pose (y := π₂ (tm_var ((𝟙 ×h T) ×h T'))).
      unfold T, T' in *.
      fold x y.
      cbn.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      simplify.
      use (exists_elim
             (partial_setoid_mor_hom_exists φ (hyperdoctrine_hyp _))).
      rewrite partial_setoid_subst.
      use (exists_elim
             (partial_setoid_mor_hom_exists ψ (weaken_left (hyperdoctrine_hyp _) _))).
      unfold x, y.
      simplify_form.
      use hyp_ltrans.
      use weaken_right.
      use exists_intro.
      + exact (⟨ π₂ (π₁ (tm_var _)) , π₂ (tm_var _) ⟩).
      + unfold x, y.
        simplify.
        apply hyperdoctrine_hyp.
  Qed.

  Definition pair_partial_setoid_morphism
    : partial_setoid_morphism W (prod_partial_setoid X Y).
  Proof.
    use make_partial_setoid_morphism.
    - exact pair_partial_setoid_morphism_form.
    - exact pair_partial_setoid_morphism_laws.
  Defined.

  Arguments pair_partial_setoid_morphism_form /.

  Proposition pair_partial_setoid_morphism_pr1
    : partial_setoid_comp_morphism
        pair_partial_setoid_morphism
        (partial_setoid_pr1 _ _)
      =
      φ.
  Proof.
    use eq_partial_setoid_morphism ; cbn.
    - use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      unfold partial_setoid_pr1_form.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      pose (w := π₁ (π₁ (tm_var ((W ×h X) ×h X ×h Y)))).
      pose (x := π₁ (π₂ (tm_var ((W ×h X) ×h X ×h Y)))).
      pose (x' := π₂ (π₁ (tm_var ((W ×h X) ×h X ×h Y)))).
      pose (y := π₂ (π₂ (tm_var ((W ×h X) ×h X ×h Y)))).
      fold w x x' y.
      rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((W ×h X) ×h X ×h Y)))).
      fold w x'.
      use hyp_rtrans.
      use weaken_left.
      use hyp_sym.
      use hyp_rtrans.
      use weaken_left.
      use (partial_setoid_mor_eq_defined φ).
      + exact w.
      + exact x.
      + use weaken_right.
        exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - use (exists_elim (partial_setoid_mor_hom_exists ψ _)).
      + exact (π₁ (tm_var _)).
      + use (partial_setoid_mor_dom_defined φ _ (π₂ (tm_var _))).
        rewrite <- hyperdoctrine_pair_eta.
        rewrite hyperdoctrine_id_subst.
        apply hyperdoctrine_hyp.
      + unfold partial_setoid_pr1_form.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        use exists_intro.
        * exact (⟨ π₂ (π₁ (tm_var _)) , π₂ (tm_var _) ⟩).
        * simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          use conj_intro.
          ** use conj_intro.
             *** use weaken_left.
                 rewrite <- hyperdoctrine_pair_eta.
                 apply hyperdoctrine_hyp.
             *** use weaken_right.
                 apply hyperdoctrine_hyp.
          ** use conj_intro.
             *** use weaken_left.
                 use (partial_setoid_mor_cod_defined φ).
                 {
                   exact (π₁ (π₁ (tm_var _))).
                 }
                 rewrite <- hyperdoctrine_pair_eta.
                 apply hyperdoctrine_hyp.
             *** use weaken_right.
                 exact (partial_setoid_mor_cod_defined ψ _ _ (hyperdoctrine_hyp _)).
  Qed.

  Proposition pair_partial_setoid_morphism_pr2
    : partial_setoid_comp_morphism
        pair_partial_setoid_morphism
        (partial_setoid_pr2 _ _)
      =
      ψ.
  Proof.
    use eq_partial_setoid_morphism ; cbn.
    - use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      unfold partial_setoid_pr2_form.
      simplify_form.
      rewrite !partial_setoid_subst.
      simplify.
      pose (w := π₁ (π₁ (tm_var ((W ×h Y) ×h X ×h Y)))).
      pose (x := π₁ (π₂ (tm_var ((W ×h Y) ×h X ×h Y)))).
      pose (y' := π₂ (π₁ (tm_var ((W ×h Y) ×h X ×h Y)))).
      pose (y := π₂ (π₂ (tm_var ((W ×h Y) ×h X ×h Y)))).
      fold w x y y'.
      rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((W ×h Y) ×h X ×h Y)))).
      fold w y'.
      use hyp_ltrans.
      use weaken_right.
      use hyp_sym.
      use hyp_ltrans.
      use weaken_right.
      use (partial_setoid_mor_eq_defined ψ).
      + exact w.
      + exact y.
      + use weaken_right.
        exact (partial_setoid_mor_dom_defined ψ _ _ (hyperdoctrine_hyp _)).
      + use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - use (exists_elim (partial_setoid_mor_hom_exists φ _)).
      + exact (π₁ (tm_var _)).
      + use (partial_setoid_mor_dom_defined ψ _ (π₂ (tm_var _))).
        rewrite <- hyperdoctrine_pair_eta.
        rewrite hyperdoctrine_id_subst.
        apply hyperdoctrine_hyp.
      + unfold partial_setoid_pr2_form.
        simplify_form.
        rewrite !partial_setoid_subst.
        simplify.
        use exists_intro.
        * exact (⟨ π₂ (tm_var _) , π₂ (π₁ (tm_var _)) ⟩).
        * simplify_form.
          rewrite !partial_setoid_subst.
          simplify.
          use conj_intro.
          ** use conj_intro.
             *** use weaken_right.
                 apply hyperdoctrine_hyp.
             *** use weaken_left.
                 rewrite <- hyperdoctrine_pair_eta.
                 apply hyperdoctrine_hyp.
          ** use conj_intro.
             *** use weaken_right.
                 exact (partial_setoid_mor_cod_defined φ _ _ (hyperdoctrine_hyp _)).
             *** use weaken_left.
                 use (partial_setoid_mor_cod_defined ψ).
                 {
                   exact (π₁ (π₁ (tm_var _))).
                 }
                 rewrite <- hyperdoctrine_pair_eta.
                 apply hyperdoctrine_hyp.
  Qed.
End Pairing.


Section CategoryOfPartialSetoids.
  Context (H : first_order_hyperdoctrine).

  Definition precategory_ob_mor_of_partial_setoids
    : precategory_ob_mor.
  Proof.
    use make_precategory_ob_mor.
    - exact (partial_setoid H).
    - exact (λ (X Y : partial_setoid H), partial_setoid_morphism X Y).
  Defined.

  Definition precategory_data_of_partial_setoids
    : precategory_data.
  Proof.
    use make_precategory_data.
    - exact precategory_ob_mor_of_partial_setoids.
    - exact id_partial_setoid_morphism.
    - exact (λ _ _ _ f g, partial_setoid_comp_morphism f g).
  Defined.

  Proposition precategory_of_partial_setoids_laws
    : is_precategory precategory_data_of_partial_setoids.
  Proof.
    use make_is_precategory_one_assoc.
    - intros X Y φ.
      use eq_partial_setoid_morphism ; cbn in *.
      + use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        rewrite partial_setoid_subst.
        simplify.
        pose (x := π₁ (π₁ (tm_var ((X ×h Y) ×h X)))).
        pose (x' := π₂ (tm_var ((X ×h Y) ×h X))).
        pose (y := π₂ (π₁ (tm_var ((X ×h Y) ×h X)))).
        fold x x' y.
        rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((X ×h Y) ×h X)))).
        fold x y.
        use (partial_setoid_mor_eq_defined φ).
        * exact x'.
        * exact y.
        * use weaken_left.
          use partial_setoid_sym.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          exact (partial_setoid_mor_cod_defined φ _ _ (hyperdoctrine_hyp _)).
        * use weaken_right.
          apply hyperdoctrine_hyp.
      + rewrite partial_setoid_subst.
        simplify.
        pose (x := π₁ (π₁ (tm_var ((X ×h Y) ×h X)))).
        pose (x' := π₂ (tm_var ((X ×h Y) ×h X))).
        pose (y := π₂ (π₁ (tm_var ((X ×h Y) ×h X)))).
        fold x x' y.
        use exists_intro.
        * exact (π₁ (tm_var (X ×h Y))).
        * simplify_form.
          rewrite partial_setoid_subst.
          unfold x, x', y ; clear x x' y.
          simplify.
          use conj_intro.
          ** use (partial_setoid_mor_dom_defined φ _ (π₂ (tm_var _))).
             rewrite <- hyperdoctrine_pair_eta.
             rewrite hyperdoctrine_id_subst.
             apply hyperdoctrine_hyp.
          ** rewrite <- hyperdoctrine_pair_eta.
             rewrite hyperdoctrine_id_subst.
             apply hyperdoctrine_hyp.
    - intros X Y φ.
      use eq_partial_setoid_morphism ; cbn in *.
      + use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        rewrite partial_setoid_subst.
        simplify.
        pose (x := π₁ (π₁ (tm_var ((X ×h Y) ×h Y)))).
        pose (y := π₂ (π₁ (tm_var ((X ×h Y) ×h Y)))).
        pose (y' := π₂ (tm_var ((X ×h Y) ×h Y))).
        fold x y y'.
        rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((X ×h Y) ×h Y)))).
        fold x y.
        use (partial_setoid_mor_eq_defined φ).
        * exact x.
        * exact y'.
        * use weaken_left.
          exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use weaken_left.
          apply hyperdoctrine_hyp.
      + rewrite partial_setoid_subst.
        simplify.
        pose (x := π₁ (π₁ (tm_var ((X ×h Y) ×h Y)))).
        pose (y := π₂ (π₁ (tm_var ((X ×h Y) ×h Y)))).
        pose (y' := π₂ (tm_var ((X ×h Y) ×h Y))).
        fold x y y'.
        use exists_intro.
        * exact (π₂ (tm_var (X ×h Y))).
        * simplify_form.
          rewrite partial_setoid_subst.
          unfold x, y, y' ; clear x y y'.
          simplify.
          use conj_intro.
          ** rewrite <- hyperdoctrine_pair_eta.
             rewrite hyperdoctrine_id_subst.
             apply hyperdoctrine_hyp.
          ** use (partial_setoid_mor_cod_defined φ (π₁ (tm_var _))).
             rewrite <- hyperdoctrine_pair_eta.
             rewrite hyperdoctrine_id_subst.
             apply hyperdoctrine_hyp.
    - intros W X Y Z φ₁ φ₂ φ₃.
      use eq_partial_setoid_morphism ; cbn in *.
      + use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify_form.
        use hyp_sym.
        use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
        simplify_form.
        use hyp_ltrans.
        use weaken_right.
        simplify.
        pose (w := π₁ (π₁ (π₁ (tm_var (((W ×h Z) ×h X) ×h Y))))).
        pose (x := π₂ (π₁ (tm_var (((W ×h Z) ×h X) ×h Y)))).
        pose (y := π₂ (tm_var (((W ×h Z) ×h X) ×h Y))).
        pose (z := π₂ (π₁ (π₁ (tm_var (((W ×h Z) ×h X) ×h Y))))).
        fold w x y z.
        use exists_intro.
        * exact y.
        * simplify.
          fold z.
          use conj_intro.
          ** use exists_intro.
             *** exact x.
             *** simplify.
                 fold w.
                 use conj_intro.
                 **** use weaken_left.
                      apply hyperdoctrine_hyp.
                 **** use weaken_right.
                      use weaken_left.
                      apply hyperdoctrine_hyp.
          ** do 2 use weaken_right.
             apply hyperdoctrine_hyp.
      + use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify_form.
        use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
        simplify_form.
        use hyp_ltrans.
        use weaken_right.
        simplify.
        pose (w := π₁ (π₁ (π₁ (tm_var (((W ×h Z) ×h Y) ×h X))))).
        pose (x := π₂ (tm_var (((W ×h Z) ×h Y) ×h X))).
        pose (y := π₂ (π₁ (tm_var (((W ×h Z) ×h Y) ×h X)))).
        pose (z := π₂ (π₁ (π₁ (tm_var (((W ×h Z) ×h Y) ×h X))))).
        fold w x y z.
        use exists_intro.
        * exact x.
        * simplify.
          fold w.
          use conj_intro.
          ** use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
          ** use exists_intro.
             *** exact y.
             *** simplify.
                 fold z.
                 use conj_intro.
                 **** do 2  use weaken_right.
                      apply hyperdoctrine_hyp.
                 **** use weaken_left.
                      apply hyperdoctrine_hyp.
  Qed.

  Definition precategory_of_partial_setoids
    : precategory.
  Proof.
    use make_precategory.
    - exact precategory_data_of_partial_setoids.
    - exact precategory_of_partial_setoids_laws.
  Defined.

  Definition category_of_partial_setoids
    : category.
  Proof.
    use make_category.
    - exact precategory_of_partial_setoids.
    - abstract
        (intros X Y ;
         exact isaset_partial_setoid_morphism).
  Defined.


  Definition functor_to_partial_setoids_data
    : functor_data
        (hyperdoctrine_type_category H)
        category_of_partial_setoids.
  Proof.
    use make_functor_data.
    - exact (λ X, eq_partial_setoid X).
    - exact (λ _ _ t, term_partial_setoid_morphism t).
  Defined.

  Proposition functor_to_partial_setoids_laws
    : is_functor functor_to_partial_setoids_data.
  Proof.
    split.
    - refine (λ (X : ty H), _).
      use eq_partial_setoid_morphism ; cbn in *.
      + use eq_in_eq_partial_setoid.
        use (hyperdoctrine_eq_trans _ (hyperdoctrine_hyp _)).
        use hyperdoctrine_refl_eq.
        refine (!_).
        exact (var_tm_subst (π₁ (tm_var (X ×h X)))).
      + use (hyperdoctrine_cut (from_eq_in_eq_partial_setoid (hyperdoctrine_hyp _))).
        use (hyperdoctrine_eq_trans _ (hyperdoctrine_hyp _)).
        use hyperdoctrine_refl_eq.
        exact (var_tm_subst (π₁ (tm_var (X ×h X)))).
    - refine (λ (X Y Z : ty H) (t₁ : tm X Y) (t₂ : tm Y Z), _).
      use eq_partial_setoid_morphism ; cbn in *.
      + use exists_intro.
        * exact (t₁ [ π₁ (tm_var _) ]tm).
        * simplify.
          use conj_intro.
          ** apply hyperdoctrine_refl.
          ** use (hyperdoctrine_eq_trans _ (hyperdoctrine_hyp _)).
             use hyperdoctrine_refl_eq.
             exact (!(tm_subst_comp (π₁ (tm_var (X ×h Z))) t₁ t₂)).
      + use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify.
        use (hyperdoctrine_eq_trans _ (weaken_right (hyperdoctrine_hyp _) _)).
        use weaken_left.
        use hyperdoctrine_eq_trans.
        * exact (t₂ [ t₁ [π₁ (π₁ (tm_var ((X ×h Z) ×h Y))) ]tm ]tm).
        * use hyperdoctrine_refl_eq.
          exact (tm_subst_comp _ t₁ t₂).
        * use hyperdoctrine_subst_eq.
          apply hyperdoctrine_hyp.
  Qed.

  Definition functor_to_partial_setoids
    : hyperdoctrine_type_category H ⟶ category_of_partial_setoids.
  Proof.
    use make_functor.
    - exact functor_to_partial_setoids_data.
    - exact functor_to_partial_setoids_laws.
  Defined.

  Require Import UniMath.CategoryTheory.Limits.Terminal.

  Proposition parital_setoid_morphism_to_terminal_eq
              {X : partial_setoid H}
              (φ : partial_setoid_morphism X (eq_partial_setoid 𝟙))
    : φ = partial_setoid_morphism_to_terminal X.
  Proof.
    pose (x := π₁ (tm_var (X ×h 𝟙))).
    pose (y := π₂ (tm_var (X ×h 𝟙))).
    use eq_partial_setoid_morphism ; cbn ; fold x.
    - use (partial_setoid_mor_dom_defined φ x y).
      unfold x, y.
      rewrite <- hyperdoctrine_pair_eta.
      simplify.
      apply hyperdoctrine_hyp.
    - use (exists_elim (partial_setoid_mor_hom_exists φ (hyperdoctrine_hyp _))).
      cbn.
      use weaken_right.
      unfold x, y ; clear x y.
      simplify.
      pose (x := π₁ (tm_var ((X ×h 𝟙) ×h 𝟙))).
      pose (y := π₂ (tm_var ((X ×h 𝟙) ×h 𝟙))).
      fold x y.
      assert (y = π₂ x) as p.
      {
        use hyperdoctrine_unit_eq.
      }
      rewrite p.
      rewrite <- (hyperdoctrine_pair_eta x).
      apply hyperdoctrine_hyp.
  Qed.

  Definition terminal_partial_setoid
    : Terminal category_of_partial_setoids.
  Proof.
    use make_Terminal.
    - exact (eq_partial_setoid 𝟙).
    - intros X.
      use make_iscontr.
      + exact (partial_setoid_morphism_to_terminal X).
      + exact parital_setoid_morphism_to_terminal_eq.
  Defined.
End CategoryOfPartialSetoids.



Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.MonoCodomain.
Require Import UniMath.CategoryTheory.DisplayedCats.MonoCodomain.FiberMonoCod.

Section FormulaFunctor.
  Context (H : first_order_hyperdoctrine).

  Definition formula_to_per_form
             {A : ty H}
             (φ : form A)
    : form (A ×h A)
    := let x₁ := π₁ (tm_var (A ×h A)) in
       let x₂ := π₂ (tm_var (A ×h A)) in
       x₁ ≡ x₂ ∧ φ [ x₁ ].

  Proposition formula_to_per_axioms
              {A : ty H}
              (φ : form A)
    : per_axioms (formula_to_per_form φ).
  Proof.
    unfold formula_to_per_form.
    split.
    - unfold per_symm_axiom.
      simplify.
      pose (x₁ := π₂ (π₁ (tm_var ((𝟙 ×h A) ×h A)))).
      pose (x₂ := π₂ (tm_var ((𝟙 ×h A) ×h A))).
      fold x₁ x₂.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use conj_intro.
      + use weaken_left.
        use hyperdoctrine_eq_sym.
        apply hyperdoctrine_hyp.
      + use hyperdoctrine_eq_transportf.
        * exact x₁.
        * use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
    - unfold per_trans_axiom.
      simplify.
      pose (x₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h A) ×h A) ×h A))))).
      pose (x₂ := π₂ (π₁ (tm_var (((𝟙 ×h A) ×h A) ×h A)))).
      pose (x₃ := π₂ (tm_var (((𝟙 ×h A) ×h A) ×h A))).
      fold x₁ x₂ x₃.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use conj_intro.
      + use hyperdoctrine_eq_trans.
        * exact x₂.
        * do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          use weaken_left.
          apply hyperdoctrine_hyp.
      + use weaken_left.
        use weaken_right.
        apply hyperdoctrine_hyp.
  Qed.

  Definition formula_to_per
          {A : ty H}
          (φ : form A)
    : per A.
  Proof.
    use make_per.
    - exact (formula_to_per_form φ).
    - exact (formula_to_per_axioms φ).
  Defined.

  Definition formula_to_partial_setoid
             {A : ty H}
             (φ : form A)
    : partial_setoid H.
  Proof.
    use make_partial_setoid.
    - exact A.
    - exact (formula_to_per φ).
  Defined.

  Proposition eq_in_formula_to_partial_setoid
              {A : ty H}
              (φ : form A)
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ t₂ : tm Γ (formula_to_partial_setoid φ)}
              (p : Δ ⊢ t₁ ≡ t₂)
              (q : Δ ⊢ φ [ t₁ ])
    : Δ ⊢ t₁ ~ t₂.
  Proof.
    unfold partial_setoid_formula ; cbn.
    unfold formula_to_per_form.
    simplify.
    use conj_intro.
    - exact p.
    - exact q.
  Qed.

  Proposition eq_from_formula_to_partial_setoid
              {A : ty H}
              (φ : form A)
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ t₂ : tm Γ (formula_to_partial_setoid φ)}
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ t₁ ≡ t₂.
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    unfold formula_to_per_form.
    simplify.
    use weaken_left.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition prop_from_formula_to_partial_setoid
              {A : ty H}
              (φ : form A)
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ t₂ : tm Γ (formula_to_partial_setoid φ)}
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ φ [ t₁ ].
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    unfold formula_to_per_form.
    simplify.
    use weaken_right.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition prop_from_formula_to_partial_setoid'
              {A : ty H}
              (φ : form A)
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ t₂ : tm Γ (formula_to_partial_setoid φ)}
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ φ [ t₂ ].
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    unfold formula_to_per_form.
    simplify.
    use hyperdoctrine_eq_transportf.
    - exact t₁.
    - use weaken_left.
      apply hyperdoctrine_hyp.
    - use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Definition formula_to_partial_setoid_incl_form
             {A : ty H}
             (φ : form A)
    : form (formula_to_partial_setoid φ ×h eq_partial_setoid A)
    := let x₁ := π₁ (tm_var (A ×h A)) in
       let x₂ := π₂ (tm_var (A ×h A)) in
       x₁ ≡ x₂ ∧ φ [ x₁ ].

  Proposition formula_to_partial_setoid_incl_laws
              {A : ty H}
              (φ : form A)
    : partial_setoid_morphism_laws (formula_to_partial_setoid_incl_form φ).
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law, formula_to_partial_setoid_incl_form.
      cbn.
      simplify.
      pose (x₁ := π₂ (π₁ (tm_var ((𝟙 ×h A) ×h A)))).
      pose (x₂ := π₂ (tm_var ((𝟙 ×h A) ×h A))).
      fold x₁ x₂.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use eq_in_formula_to_partial_setoid.
      + use hyperdoctrine_refl.
      + use weaken_right.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law, formula_to_partial_setoid_incl_form.
      cbn.
      simplify.
      pose (x₁ := π₂ (π₁ (tm_var ((𝟙 ×h A) ×h A)))).
      pose (x₂ := π₂ (tm_var ((𝟙 ×h A) ×h A))).
      fold x₁ x₂.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use eq_in_eq_partial_setoid.
      use hyperdoctrine_refl.
    - unfold partial_setoid_mor_eq_defined_law, formula_to_partial_setoid_incl_form.
      cbn.
      simplify.
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h A) ×h A) ×h A) ×h A)))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h A) ×h A) ×h A) ×h A))))).
      pose (x₃ := π₂ (π₁ (tm_var ((((𝟙 ×h A) ×h A) ×h A) ×h A)))).
      pose (x₄ := π₂ (tm_var ((((𝟙 ×h A) ×h A) ×h A) ×h A))).
      fold x₁ x₂ x₃ x₄.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      use conj_intro.
      + use hyp_rtrans.
        use weaken_left.
        use hyperdoctrine_eq_trans.
        * exact x₁.
        * do 2 use weaken_left.
          use hyperdoctrine_eq_sym.
          use (eq_from_formula_to_partial_setoid φ).
          apply hyperdoctrine_hyp.
        * use hyperdoctrine_eq_trans.
          ** exact x₃.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
          ** use weaken_left.
             use weaken_right.
             use from_eq_in_eq_partial_setoid.
             apply hyperdoctrine_hyp.
      + use hyperdoctrine_eq_transportf.
        * exact x₁.
        * do 2 use weaken_left.
          exact (eq_from_formula_to_partial_setoid _ (hyperdoctrine_hyp _)).
        * do 2 use weaken_right.
          apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law, formula_to_partial_setoid_incl_form.
      cbn.
      simplify.
      pose (x₁ := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h A) ×h A) ×h A))))).
      pose (x₂ := π₂ (π₁ (tm_var (((𝟙 ×h A) ×h A) ×h A)))).
      pose (x₃ := π₂ (tm_var (((𝟙 ×h A) ×h A) ×h A))).
      fold x₁ x₂ x₃.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use eq_in_eq_partial_setoid.
      use hyperdoctrine_eq_trans.
      + exact x₁.
      + use hyperdoctrine_eq_sym.
        do 2 use weaken_left.
        apply hyperdoctrine_hyp.
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law, formula_to_partial_setoid_incl_form.
      cbn.
      simplify.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use exists_intro.
      + exact (π₂ (tm_var _)).
      + simplify.
        pose (x := π₂ (tm_var (𝟙 ×h A))).
        fold x.
        use conj_intro.
        * use (eq_from_formula_to_partial_setoid φ).
          apply hyperdoctrine_hyp.
        * exact (prop_from_formula_to_partial_setoid φ (hyperdoctrine_hyp _)).
  Qed.

  Definition formula_to_partial_setoid_incl
             {A : ty H}
             (φ : form A)
    : partial_setoid_morphism
        (formula_to_partial_setoid φ)
        (eq_partial_setoid A).
  Proof.
    use make_partial_setoid_morphism.
    - exact (formula_to_partial_setoid_incl_form φ).
    - exact (formula_to_partial_setoid_incl_laws φ).
  Defined.

  Proposition isMonic_formula_to_partial_setoid_incl_eq
              {A : ty H}
              (φ : form A)
              (X : partial_setoid H)
              {ψ₁ ψ₂ : partial_setoid_morphism X (formula_to_partial_setoid φ)}
              (p : partial_setoid_comp_morphism ψ₁ (formula_to_partial_setoid_incl φ)
                   =
                   partial_setoid_comp_morphism ψ₂ (formula_to_partial_setoid_incl φ))
    : ψ₁ ⊢ ψ₂.
  Proof.
    refine (hyperdoctrine_cut
              (@from_eq_partial_setoid_morphism_f
                 _ _ _ _ _
                 p
                 _
                 ψ₁
                 (π₁ (tm_var _)) (π₂ (tm_var _))
                 _)
              _).
    - cbn.
      unfold formula_to_partial_setoid_incl_form.
      simplify_form.
      use exists_intro.
      + exact (π₂ (tm_var _)).
      + simplify.
        use conj_intro.
        * rewrite <- hyperdoctrine_pair_eta.
          rewrite hyperdoctrine_id_subst.
          apply hyperdoctrine_hyp.
        * use conj_intro.
          ** apply hyperdoctrine_refl.
          ** use hyperdoctrine_cut.
             *** exact (ψ₁ [ ⟨ π₁ (tm_var _) , π₂ (tm_var _) ⟩ ]).
             *** rewrite <- (hyperdoctrine_pair_eta (tm_var _)).
                 rewrite hyperdoctrine_id_subst.
                 apply hyperdoctrine_hyp.
             *** refine (hyperdoctrine_cut
                           (partial_setoid_mor_cod_defined
                              ψ₁
                              (π₁ (tm_var _)) (π₂ (tm_var _))
                              (hyperdoctrine_hyp _))
                           _).
                 exact (prop_from_formula_to_partial_setoid φ (hyperdoctrine_hyp _)).
    - cbn.
      unfold formula_to_partial_setoid_incl_form.
      simplify_form.
      use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      simplify.
      use hyp_rtrans.
      use weaken_left.
      pose (x := π₁ (π₁ (tm_var ((X ×h A) ×h A)))).
      pose (a := π₂ (tm_var ((X ×h A) ×h A))).
      pose (a' := π₂ (π₁ (tm_var ((X ×h A) ×h A)))).
      fold x a a'.
      rewrite (hyperdoctrine_pair_eta (π₁ (tm_var ((X ×h A) ×h A)))).
      fold x a'.
      use hyperdoctrine_eq_transportf.
      + exact ⟨ x , a ⟩.
      + use weaken_right.
        use hyperdoctrine_eq_pair_eq.
        * apply hyperdoctrine_refl.
        * apply hyperdoctrine_hyp.
      + use weaken_left.
        apply hyperdoctrine_hyp.
  Qed.

  Proposition isMonic_formula_to_partial_setoid_incl
              {A : ty H}
              (φ : form A)
    : isMonic (C := category_of_partial_setoids H) (formula_to_partial_setoid_incl φ).
  Proof.
    intros X ψ₁ ψ₂ p.
    use eq_partial_setoid_morphism.
    - use isMonic_formula_to_partial_setoid_incl_eq.
      exact p.
    - use isMonic_formula_to_partial_setoid_incl_eq.
      exact (!p).
  Qed.

  Definition proof_to_partial_setoid_morphism_form
             {Γ₁ Γ₂ : ty H}
             {Δ : form Γ₁}
             {φ : form Γ₂}
             {s : tm Γ₁ Γ₂}
             (q : Δ ⊢ φ [ s ])
    : form (formula_to_partial_setoid Δ ×h formula_to_partial_setoid φ)
    := let x := π₁ (tm_var (Γ₁ ×h Γ₂)) in
       let y := π₂ (tm_var (Γ₁ ×h Γ₂)) in
       Δ [ x ] ∧ φ [ y ] ∧ y ≡ s [ x ]tm.

  Proposition proof_to_partial_setoid_morphism_laws
              {Γ₁ Γ₂ : ty H}
              {Δ : form Γ₁}
              {φ : form Γ₂}
              {s : tm Γ₁ Γ₂}
              (q : Δ ⊢ φ [ s ])
    : partial_setoid_morphism_laws (proof_to_partial_setoid_morphism_form q).
  Proof.
    unfold proof_to_partial_setoid_morphism_form.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      cbn.
      simplify.
      unfold partial_setoid_formula.
      cbn.
      unfold formula_to_per_form.
      simplify.
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h Γ₁) ×h Γ₂)))).
      pose (y := π₂ (tm_var ((𝟙 ×h Γ₁) ×h Γ₂))).
      fold x y.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use conj_intro.
      + apply hyperdoctrine_refl.
      + use weaken_left.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law.
      cbn.
      simplify.
      unfold partial_setoid_formula.
      cbn.
      unfold formula_to_per_form.
      simplify.
      pose (x := π₂ (π₁ (tm_var ((𝟙 ×h Γ₁) ×h Γ₂)))).
      pose (y := π₂ (tm_var ((𝟙 ×h Γ₁) ×h Γ₂))).
      fold x y.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use conj_intro.
      + apply hyperdoctrine_refl.
      + use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law.
      cbn.
      simplify.
      unfold partial_setoid_formula.
      cbn.
      unfold formula_to_per_form.
      simplify.
      pose (x₁ := π₂ (π₁ (π₁ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂)))))).
      pose (x₂ := π₂ (π₁ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂))))).
      pose (y₁ := π₂ (π₁ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂)))).
      pose (y₂ := π₂ (tm_var ((((𝟙 ×h Γ₁) ×h Γ₁) ×h Γ₂) ×h Γ₂))).
      fold x₁ x₂ y₁ y₂.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      use conj_intro.
      + do 2 use weaken_left.
        use hyperdoctrine_eq_transportf.
        * apply x₁.
        * use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
      + use conj_intro.
        * use weaken_left.
          use weaken_right.
          use hyperdoctrine_eq_transportf.
          ** apply y₁.
          ** use weaken_left.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             apply hyperdoctrine_hyp.
        * use hyperdoctrine_eq_trans.
          ** exact y₁.
          ** use hyperdoctrine_eq_sym.
             use weaken_left.
             use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
          ** use hyperdoctrine_eq_trans.
             *** exact (s [ x₁ ]tm).
             *** do 3 use weaken_right.
                 apply hyperdoctrine_hyp.
             *** use hyperdoctrine_subst_eq.
                 do 3 use weaken_left.
                 apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law.
      cbn.
      unfold partial_setoid_formula.
      cbn.
      unfold formula_to_per_form.
      simplify.
      pose (x := π₂ (π₁ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₂) ×h Γ₂))))).
      pose (y₁ := π₂ (π₁ (tm_var (((𝟙 ×h Γ₁) ×h Γ₂) ×h Γ₂)))).
      pose (y₂ := π₂ (tm_var (((𝟙 ×h Γ₁) ×h Γ₂) ×h Γ₂))).
      fold x y₁ y₂.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use conj_intro.
      + use hyperdoctrine_eq_trans.
        * exact (s [ x ]tm).
        * use weaken_left.
          do 2 use weaken_right.
          apply hyperdoctrine_hyp.
        * use hyperdoctrine_eq_sym.
          do 3 use weaken_right.
          apply hyperdoctrine_hyp.
      + use weaken_left.
        use weaken_right.
        use weaken_left.
        apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      cbn.
      unfold partial_setoid_formula.
      cbn.
      unfold formula_to_per_form.
      simplify.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      use exists_intro.
      + exact (s [ π₂ (tm_var (𝟙 ×h Γ₁)) ]tm).
      + simplify.
        pose (x := π₂ (tm_var (𝟙 ×h Γ₁))).
        fold x.
        use conj_intro.
        * use weaken_right.
          apply hyperdoctrine_hyp.
        * use conj_intro.
          ** use weaken_right.
             refine (hyperdoctrine_cut (hyperdoctrine_proof_subst x q) _).
             simplify.
             apply hyperdoctrine_hyp.
          ** apply hyperdoctrine_refl.
  Qed.

  Definition proof_to_partial_setoid_morphism
             {Γ₁ Γ₂ : ty H}
             {Δ : form Γ₁}
             {φ : form Γ₂}
             {s : tm Γ₁ Γ₂}
             (q : Δ ⊢ φ [ s ])
    : partial_setoid_morphism (formula_to_partial_setoid Δ) (formula_to_partial_setoid φ).
  Proof.
    use make_partial_setoid_morphism.
    - exact (proof_to_partial_setoid_morphism_form q).
    - exact (proof_to_partial_setoid_morphism_laws q).
  Defined.

  Proposition proof_to_partial_setoid_morphism_eq
              {Γ₁ Γ₂ : ty H}
              {Δ : form Γ₁}
              {φ : form Γ₂}
              {s : tm Γ₁ Γ₂}
              (q : Δ ⊢ φ [ s ])
    : partial_setoid_comp_morphism
        (proof_to_partial_setoid_morphism q)
        (formula_to_partial_setoid_incl φ)
      =
      partial_setoid_comp_morphism
        (formula_to_partial_setoid_incl Δ)
        (term_partial_setoid_morphism s).
  Proof.
    use eq_partial_setoid_morphism.
    - use (exists_elim (hyperdoctrine_hyp _)).
      cbn.
      unfold proof_to_partial_setoid_morphism_form.
      unfold formula_to_partial_setoid_incl_form.
      use weaken_right.
      simplify_form.
      use exists_intro.
      + exact (π₁ (π₁ (tm_var _))).
      + simplify.
        pose (x := π₁ (π₁ (tm_var ((Γ₁ ×h Γ₂) ×h Γ₂)))).
        pose (y₁ := π₂ (π₁ (tm_var ((Γ₁ ×h Γ₂) ×h Γ₂)))).
        pose (y₂ := π₂ (tm_var ((Γ₁ ×h Γ₂) ×h Γ₂))).
        fold x y₁ y₂.
        use conj_intro.
        * use conj_intro.
          ** apply hyperdoctrine_refl.
          ** do 2 use weaken_left.
             apply hyperdoctrine_hyp.
        * use hyperdoctrine_eq_trans.
          ** exact y₂.
          ** use hyperdoctrine_eq_sym.
             use weaken_left.
             do 2 use weaken_right.
             apply hyperdoctrine_hyp.
          ** use weaken_right.
             use weaken_left.
             apply hyperdoctrine_hyp.
    - use (exists_elim (hyperdoctrine_hyp _)).
      cbn.
      unfold proof_to_partial_setoid_morphism_form.
      unfold formula_to_partial_setoid_incl_form.
      use weaken_right.
      simplify_form.
      use exists_intro.
      + exact (π₂ (π₁ (tm_var _))).
      + simplify.
        pose (x₁ := π₁ (π₁ (tm_var ((Γ₁ ×h Γ₂) ×h Γ₁)))).
        pose (y := π₂ (π₁ (tm_var ((Γ₁ ×h Γ₂) ×h Γ₁)))).
        pose (x₂ := π₂ (tm_var ((Γ₁ ×h Γ₂) ×h Γ₁))).
        fold x₁ x₂ y.
        assert ((x₁ ≡ x₂ ∧ Δ [x₁]) ∧ s [x₂ ]tm ≡ y ⊢ φ [y]) as r.
        {
          refine (weaken_cut
                    (weaken_left (weaken_right (hyperdoctrine_proof_subst x₁ q) _) _)
                    _).
          simplify.
          use hyperdoctrine_eq_transportf.
          * exact (s [ x₁ ]tm).
          * use weaken_left.
            refine (hyperdoctrine_eq_trans _ (weaken_right (hyperdoctrine_hyp _) _)).
            do 2 use weaken_left.
            use hyperdoctrine_subst_eq.
            use hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
        }
        use conj_intro.
        * use conj_intro.
          ** use weaken_left.
             use weaken_right.
             apply hyperdoctrine_hyp.
          ** use conj_intro.
             *** exact r.
             *** use hyperdoctrine_eq_trans.
                 **** exact (s [ x₂ ]tm).
                 **** use hyperdoctrine_eq_sym.
                      use weaken_right.
                      apply hyperdoctrine_hyp.
                 **** use hyperdoctrine_subst_eq.
                      use hyperdoctrine_eq_sym.
                      do 2 use weaken_left.
                      apply hyperdoctrine_hyp.
        * use conj_intro.
          ** apply hyperdoctrine_refl.
          ** exact r.
  Qed.

  Definition partial_setoids_disp_functor_data
    : disp_functor_data
        (functor_to_partial_setoids H)
        (hyperdoctrine_formula_disp_cat H)
        (disp_mono_codomain _).
  Proof.
    simple refine (_ ,, _).
    - simple refine (λ (A : ty H) (φ : form A), make_mono_cod_fib_ob _).
      + exact (formula_to_partial_setoid φ).
      + use make_Monic.
        * exact (formula_to_partial_setoid_incl φ).
        * exact (isMonic_formula_to_partial_setoid_incl φ).
    - refine (λ (Γ₁ Γ₂ : ty H)
                (Δ : form Γ₁)
                (φ : form Γ₂)
                (s : tm Γ₁ Γ₂)
                p, _).
      simple refine ((_ ,, _) ,, tt).
      + exact (proof_to_partial_setoid_morphism (from_disp_mor_hyperdoctrine _ p)).
      + apply proof_to_partial_setoid_morphism_eq.
  Defined.

  Definition partial_setoids_disp_functor
    : disp_functor
        (functor_to_partial_setoids H)
        (hyperdoctrine_formula_disp_cat H)
        (disp_mono_codomain _).
  Proof.
    simple refine (_ ,, _).
    - exact partial_setoids_disp_functor_data.
    - abstract
        (split ; intro ; intros ; apply locally_propositional_mono_cod_disp_cat).
  Defined.

  Definition partial_setoids_disp_functor_ff
    : disp_functor_ff partial_setoids_disp_functor.
  Proof.
    refine (λ (X Y : ty H) (φ : form X) (ψ : form Y) (s : tm X Y), _).
    use isweqimplimpl.
    - intro p.
      use to_disp_mor_hyperdoctrine.
      cbn in p.
      induction p as [ [ χ p ] t ].
      induction t.
      simple refine (hyperdoctrine_cut (from_eq_partial_setoid_morphism_f (!p) _) _).
      + apply tm_var.
      + exact s.
      + cbn.
        simplify.
        use exists_intro.
        * exact (tm_var _).
        * unfold formula_to_partial_setoid_incl_form.
          simplify.
          simplify_form.
          repeat (use conj_intro).
          ** apply hyperdoctrine_refl.
          ** apply hyperdoctrine_hyp.
          ** apply hyperdoctrine_refl.
      + cbn.
        simplify.
        use (exists_elim (hyperdoctrine_hyp _)).
        do 2 use weaken_right.
        unfold formula_to_partial_setoid_incl_form.
        simplify.
        use hyperdoctrine_eq_transportf.
        * exact (π₂ (tm_var (X ×h Y))).
        * use weaken_left.
          apply hyperdoctrine_hyp.
        * use weaken_right.
          apply hyperdoctrine_hyp.
    - use invproofirrelevance.
      intros ? ?.
      apply disp_mor_eq_hyperdoctrine.
    - apply locally_propositional_mono_cod_disp_cat.
  Qed.

  Definition TODO { A : UU } : A.
  Admitted.

  Section EssentiallySurjective.
    Context {A : ty H}
            {X : partial_setoid H}
            (φ : partial_setoid_morphism X (eq_partial_setoid A))
            (Hφ : isMonic (C := category_of_partial_setoids H) φ).

    Definition partial_setoids_disp_functor_eso_form
      : form A
      := let a := π₁ (tm_var (A ×h X)) in
         let x := π₂ (tm_var (A ×h X)) in
         (∃h (φ [ ⟨ x , a ⟩ ])).

    Definition partial_setoids_disp_functor_eso_mor_form
      : form (formula_to_partial_setoid partial_setoids_disp_functor_eso_form ×h X)
      := let a := π₁ (tm_var (A ×h X)) in
         let x := π₂ (tm_var (A ×h X)) in
         φ [ ⟨ x , a ⟩ ].

    Proposition partial_setoids_disp_functor_eso_mor_laws
      : partial_setoid_morphism_laws partial_setoids_disp_functor_eso_mor_form.
    Proof.
      unfold partial_setoids_disp_functor_eso_mor_form.
      repeat split.
      - unfold partial_setoid_mor_dom_defined_law.
        cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        unfold partial_setoid_formula ; cbn.
        unfold formula_to_per_form, partial_setoids_disp_functor_eso_form.
        simplify.
        use conj_intro.
        + apply hyperdoctrine_refl.
        + use exists_intro.
          * exact (π₂ (tm_var _)).
          * simplify.
            apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_cod_defined_law.
        cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
      - unfold partial_setoid_mor_eq_defined_law.
        cbn.
        do 4 use forall_intro.
        use impl_intro.
        use weaken_right.
        do 2 use impl_intro.
        simplify.
        refine (partial_setoid_mor_eq_defined φ _ _ (weaken_right (hyperdoctrine_hyp _) _)).
        + use weaken_left.
          use weaken_right.
          apply hyperdoctrine_hyp.
        + do 2 use weaken_left.
          unfold partial_setoid_formula ; cbn.
          unfold formula_to_per_form, partial_setoids_disp_functor_eso_form.
          simplify_form.
          use weaken_left.
          apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_unique_im_law.
        cbn.
        do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify. (* here monic is needed *)
        assert (⊤ ⊢ π₂ (π₁ (tm_var (((𝟙 ×h A) ×h X) ×h X))) ~ π₂ (π₁ (tm_var (((𝟙 ×h A) ×h X) ×h X)))) as h₁.
        admit.
        assert (⊤ ⊢ π₂ (tm_var (((𝟙 ×h A) ×h X) ×h X)) ~ π₂ (tm_var (((𝟙 ×h A) ×h X) ×h X))) as h₂.
        admit.
        pose (partial_setoid_morphism_from_terminal
                X
                (π₂ (π₁ (tm_var (((𝟙 ×h A) ×h X) ×h X))))
                h₁)
          as f₁.
        pose (partial_setoid_morphism_from_terminal
                X
                (π₂ (tm_var (((𝟙 ×h A) ×h X) ×h X)))
                h₂)
          as f₂.
        (*
        assert (partial_setoid_comp_morphism f₁ φ = partial_setoid_comp_morphism f₂ φ).
        {
          use eq_partial_setoid_morphism ; cbn.
          - use (exists_elim (hyperdoctrine_hyp _)).
            use weaken_right.
            simplify_form.
            use exists_intro.
            * exact (π₂ (tm_var _)).
            * simplify_form.
              rewrite !partial_setoid_subst.
              simplify.
              admit.
          - use (exists_elim (hyperdoctrine_hyp _)).
            use weaken_right.
            simplify_form.
            use exists_intro.
            * exact (π₂ (tm_var _)).
            * simplify_form.
              rewrite !partial_setoid_subst.
              simplify.
              admit.

              rewrite partial_setoid_subst.
            use weak
        Check Hφ _ f₁ f₂.
         *)

        (*
          we should restrict `eq_partial_setoid` using a context delta
          this way we restrict the elements

          given `A : ty`
                `Δ : form A`
          look at
               `x₁ ≡ x₂ ∧ Δ [ x₁ ]

          then we can add the assumptions`
         *)

        partial_setoid_morphism_from_terminal
        apply TODO.
      - unfold partial_setoid_mor_hom_exists_law.
        cbn.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        unfold partial_setoid_formula.
        cbn.
        unfold formula_to_per_form.
        unfold partial_setoids_disp_functor_eso_form.
        simplify.
        use weaken_right.
        apply hyperdoctrine_hyp.
    Qed.

    Definition partial_setoids_disp_functor_eso_mor
      : partial_setoid_morphism
          (formula_to_partial_setoid partial_setoids_disp_functor_eso_form)
          X.
    Proof.
      use make_partial_setoid_morphism.
      - exact partial_setoids_disp_functor_eso_mor_form.
      - exact partial_setoids_disp_functor_eso_mor_laws.
    Defined.

    Proposition partial_setoids_disp_functor_eso_mor_comm
      : partial_setoid_comp_morphism
          partial_setoids_disp_functor_eso_mor
          φ
        =
        partial_setoid_comp_morphism
          (formula_to_partial_setoid_incl partial_setoids_disp_functor_eso_form)
          (id_partial_setoid_morphism (eq_partial_setoid A)).
    Proof.
      use eq_partial_setoid_morphism.
      - cbn.
        unfold formula_to_partial_setoid_incl_form, partial_setoids_disp_functor_eso_form.
        unfold partial_setoids_disp_functor_eso_mor_form.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify.
        use exists_intro.
        + exact (π₁ (π₁ (tm_var _))).
        + simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          repeat (use conj_intro).
          * apply hyperdoctrine_refl.
          * use exists_intro.
            ** exact (π₂ (tm_var _)).
            ** simplify.
               use weaken_left.
               apply hyperdoctrine_hyp.
          * use (partial_setoid_mor_unique_im φ).
            ** exact (π₂ (tm_var ((A ×h A) ×h X))).
            ** use weaken_left.
               apply hyperdoctrine_hyp.
            ** use weaken_right.
               apply hyperdoctrine_hyp.
      - cbn.
        unfold formula_to_partial_setoid_incl_form, partial_setoids_disp_functor_eso_form.
        unfold partial_setoids_disp_functor_eso_mor_form.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        use hyp_sym.
        use hyp_rtrans.
        use hyp_sym.
        use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
        simplify_form.
        use hyp_ltrans.
        use weaken_right.
        use exists_intro.
        + exact (π₂ (tm_var _)).
        + simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          use conj_intro.
          * use weaken_right.
            apply hyperdoctrine_hyp.
          * use (hyperdoctrine_eq_transportf _ _ (weaken_right (hyperdoctrine_hyp _) _)).
            use hyperdoctrine_eq_pair_eq.
            ** apply hyperdoctrine_refl.
            ** use weaken_left.
               refine (hyperdoctrine_eq_trans (weaken_right (hyperdoctrine_hyp _) _) _).
               use weaken_left.
               use from_eq_in_eq_partial_setoid.
               apply hyperdoctrine_hyp.
    Qed.

    Definition partial_setoids_disp_functor_eso_inv_form
      : form (X ×h formula_to_partial_setoid partial_setoids_disp_functor_eso_form)
      := let x := π₁ (tm_var (X ×h A)) in
         let a := π₂ (tm_var (X ×h A)) in
         φ [ ⟨ x , a ⟩ ].

    Proposition partial_setoids_disp_functor_eso_inv_laws
      : partial_setoid_morphism_laws partial_setoids_disp_functor_eso_inv_form.
    Proof.
      unfold partial_setoids_disp_functor_eso_inv_form.
      repeat split.
      - unfold partial_setoid_mor_dom_defined_law.
        cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        exact (partial_setoid_mor_dom_defined φ _ _ (hyperdoctrine_hyp _)).
      - unfold partial_setoid_mor_cod_defined_law.
        cbn.
        do 2 use forall_intro.
        use impl_intro.
        use weaken_right.
        simplify.
        unfold partial_setoid_formula.
        cbn.
        unfold formula_to_per_form, partial_setoids_disp_functor_eso_form.
        simplify.
        use conj_intro.
        + use from_eq_in_eq_partial_setoid.
          exact (partial_setoid_mor_cod_defined φ _ _ (hyperdoctrine_hyp _)).
        + use exists_intro.
          * exact (π₂ (π₁ (tm_var _))).
          * simplify.
            apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_eq_defined_law.
        cbn.
        do 4 use forall_intro.
        use impl_intro.
        use weaken_right.
        do 2 use impl_intro.
        simplify.
        use (partial_setoid_mor_eq_defined φ).
        + exact (π₂ (π₁ (π₁ (π₁ (tm_var _))))).
        + exact (π₂ (π₁ (tm_var _))).
        + do 2 use weaken_left.
          apply hyperdoctrine_hyp.
        + use weaken_left.
          use weaken_right.
          unfold partial_setoid_formula.
          cbn.
          unfold formula_to_per_form, partial_setoids_disp_functor_eso_form.
          rewrite conj_subst.
          use weaken_left.
          apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_unique_im_law.
        cbn.
        do 3 use forall_intro.
        use impl_intro.
        use weaken_right.
        use impl_intro.
        simplify.
        unfold partial_setoid_formula.
        cbn.
        unfold formula_to_per_form, partial_setoids_disp_functor_eso_form.
        simplify.
        use conj_intro.
        + use from_eq_in_eq_partial_setoid.
          use (partial_setoid_mor_unique_im φ).
          * exact (π₂ (π₁ (π₁ (tm_var _)))).
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            apply hyperdoctrine_hyp.
        + use exists_intro.
          * exact (π₂ (π₁ (π₁ (tm_var _)))).
          * simplify.
            use weaken_left.
            apply hyperdoctrine_hyp.
      - unfold partial_setoid_mor_hom_exists_law.
        cbn.
        use forall_intro.
        use impl_intro.
        use weaken_right.
        use (exists_elim (partial_setoid_mor_hom_exists φ (hyperdoctrine_hyp _))).
        simplify_form.
        use exists_intro.
        + exact (π₂ (tm_var _)).
        + cbn.
          simplify.
          use weaken_right.
          apply hyperdoctrine_hyp.
    Qed.

    Definition partial_setoids_disp_functor_eso_inv
      : partial_setoid_morphism
          X
          (formula_to_partial_setoid partial_setoids_disp_functor_eso_form).
    Proof.
      use make_partial_setoid_morphism.
      - exact partial_setoids_disp_functor_eso_inv_form.
      - exact partial_setoids_disp_functor_eso_inv_laws.
    Defined.

    Proposition partial_setoids_disp_functor_eso_inv_comm
      : partial_setoid_comp_morphism
          partial_setoids_disp_functor_eso_inv
          (formula_to_partial_setoid_incl partial_setoids_disp_functor_eso_form)
        =
        partial_setoid_comp_morphism φ (id_partial_setoid_morphism (eq_partial_setoid A)).
    Proof.
      use eq_partial_setoid_morphism.
      - cbn.
        unfold formula_to_partial_setoid_incl_form, partial_setoids_disp_functor_eso_form.
        unfold partial_setoids_disp_functor_eso_inv_form.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify_form.
        rewrite partial_setoid_subst.
        simplify.
        use hyp_rtrans.
        use hyp_sym.
        use (exists_elim (weaken_left (hyperdoctrine_hyp _) _)).
        simplify_form.
        use hyp_ltrans.
        use weaken_right.
        use exists_intro.
        + exact (π₂ (π₁ (tm_var _))).
        + simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          use conj_intro.
          * do 2 use weaken_left.
            apply hyperdoctrine_hyp.
          * use eq_in_eq_partial_setoid.
            use weaken_left.
            use weaken_right.
            apply hyperdoctrine_hyp.
      - cbn.
        unfold formula_to_partial_setoid_incl_form, partial_setoids_disp_functor_eso_form.
        unfold partial_setoids_disp_functor_eso_inv_form.
        use (exists_elim (hyperdoctrine_hyp _)).
        use weaken_right.
        simplify.
        use exists_intro.
        + exact (π₂ (tm_var _)).
        + simplify_form.
          rewrite partial_setoid_subst.
          simplify.
          repeat (use conj_intro).
          * use weaken_left.
            apply hyperdoctrine_hyp.
          * use weaken_right.
            use from_eq_in_eq_partial_setoid.
            apply hyperdoctrine_hyp.
          * use exists_intro.
            ** exact (π₁ (π₁ (tm_var _))).
            ** simplify.
               use weaken_left.
               apply hyperdoctrine_hyp.
    Qed.
  End EssentiallySurjective.

  Definition partial_setoids_disp_functor_ess_split_surj
    : disp_functor_disp_ess_split_surj partial_setoids_disp_functor.
  Proof.
    refine (λ (A : ty H) f, _).
    induction f as [ [ X φ ] Hφ ].
    simple refine (_ ,, _).
    - exact (partial_setoids_disp_functor_eso_form φ).
    - simple refine (_ ,, _ ,, _ ,, _).
      + simple refine ((_ ,, _) ,, tt) ; cbn.
        * apply partial_setoids_disp_functor_eso_mor.
        * apply partial_setoids_disp_functor_eso_mor_comm.
      + simple refine ((_ ,, _) ,, tt) ; cbn.
        * apply partial_setoids_disp_functor_eso_inv.
        * apply partial_setoids_disp_functor_eso_inv_comm.
      + apply locally_propositional_mono_cod_disp_cat.
      + apply locally_propositional_mono_cod_disp_cat.
  Defined.
End FormulaFunctor.


Section PartialEquivalenceRelationInitial.
  Context (H : first_order_hyperdoctrine).

  Proposition initial_partial_setoid_axioms
    : @per_axioms H 𝟙 ⊥.
  Proof.
    split.
    - unfold per_symm_axiom.
      simplify.
      use forall_intro.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      apply hyperdoctrine_hyp.
    - unfold per_trans_axiom.
      simplify.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use impl_intro.
      use weaken_right.
      apply hyperdoctrine_hyp.
  Qed.

  Definition initial_partial_setoid
    : partial_setoid H.
  Proof.
    use make_partial_setoid.
    - exact 𝟙.
    - use make_per.
      + exact ⊥.
      + exact initial_partial_setoid_axioms.
  Defined.

  Proposition eq_in_initial_partial_setoid
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ t₂ : tm Γ initial_partial_setoid}
              (p : Δ ⊢ ⊥)
    : Δ ⊢ t₁ ~ t₂.
  Proof.
    unfold partial_setoid_formula ; cbn.
    simplify.
    exact p.
  Qed.

  Proposition from_eq_in_initial_partial_setoid
              {Γ : ty H}
              {Δ : form Γ}
              {t₁ t₂ : tm Γ initial_partial_setoid}
              (p : Δ ⊢ t₁ ~ t₂)
    : Δ ⊢ ⊥.
  Proof.
    refine (hyperdoctrine_cut p _).
    unfold partial_setoid_formula ; cbn.
    simplify.
    apply hyperdoctrine_hyp.
  Qed.

  Proposition initial_partial_setoid_morphism_laws
              (X : partial_setoid H)
    : @partial_setoid_morphism_laws H initial_partial_setoid X ⊥.
  Proof.
    repeat split.
    - unfold partial_setoid_mor_dom_defined_law.
      cbn.
      simplify.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use false_elim.
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_cod_defined_law.
      cbn.
      simplify.
      do 2 use forall_intro.
      use impl_intro.
      use weaken_right.
      use false_elim.
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_eq_defined_law.
      cbn.
      simplify.
      do 4 use forall_intro.
      use impl_intro.
      use weaken_right.
      do 2 use impl_intro.
      use weaken_right.
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_unique_im_law.
      cbn.
      simplify.
      do 3 use forall_intro.
      use impl_intro.
      use weaken_right.
      use false_elim.
      apply hyperdoctrine_hyp.
    - unfold partial_setoid_mor_hom_exists_law.
      cbn.
      simplify.
      use forall_intro.
      use impl_intro.
      use weaken_right.
      unfold partial_setoid_formula ; cbn.
      simplify.
      use false_elim.
      apply hyperdoctrine_hyp.
  Qed.

  Definition initial_partial_setoid_morphism
             (X : partial_setoid H)
    : partial_setoid_morphism initial_partial_setoid X.
  Proof.
    use make_partial_setoid_morphism.
    - exact ⊥.
    - exact (initial_partial_setoid_morphism_laws X).
  Defined.

  Proposition initial_partial_setoid_morphism_eq
              {X : partial_setoid H}
              (f : partial_setoid_morphism initial_partial_setoid X)
    : f = initial_partial_setoid_morphism X.
  Proof.
    use eq_partial_setoid_morphism ; unfold initial_partial_setoid_morphism ; cbn.
    - refine (hyperdoctrine_cut
                (partial_setoid_mor_dom_defined f (π₁ (tm_var _)) (π₂ (tm_var _)) _)
                _).
      + cbn.
        rewrite <- hyperdoctrine_pair_eta.
        rewrite hyperdoctrine_id_subst.
        apply hyperdoctrine_hyp.
      + exact (from_eq_in_initial_partial_setoid (hyperdoctrine_hyp _)).
    - use false_elim.
      apply hyperdoctrine_hyp.
  Qed.

  Proposition initial_partial_setoid_morphism_eq_id
              {X : partial_setoid H}
              (φ : partial_setoid_morphism X initial_partial_setoid)
    : partial_setoid_comp_morphism φ (initial_partial_setoid_morphism X)
      =
      id_partial_setoid_morphism X.
  Proof.
    use eq_partial_setoid_morphism.
    - cbn.
      use (exists_elim (hyperdoctrine_hyp _)).
      use weaken_right.
      simplify_form.
      use false_elim.
      use weaken_right.
      apply hyperdoctrine_hyp.
    - cbn.
      use exists_intro.
      + exact !!.
      + simplify.
        use false_elim.
        pose (x₁ := π₁ (tm_var (X ×h X))).
        pose (x₂ := π₂ (tm_var (X ×h X))).
        fold x₁ x₂.
        use (exists_elim (partial_setoid_mor_hom_exists φ _)).
        * exact x₁.
        * exact (partial_setoid_refl_l (hyperdoctrine_hyp _)).
        * unfold x₁, x₂ ; clear x₁ x₂.
          rewrite partial_setoid_subst.
          simplify.
          cbn.
          pose (x₁ := π₁ (π₁ (tm_var ((X ×h X) ×h 𝟙)))).
          pose (x₂ := π₂ (π₁ (tm_var ((X ×h X) ×h 𝟙)))).
          pose (y := π₂ (tm_var ((X ×h X) ×h 𝟙))).
          fold x₁ x₂ y.
          use from_eq_in_initial_partial_setoid.
          ** exact y.
          ** exact y.
          ** use (partial_setoid_mor_cod_defined φ x₁ y).
             use weaken_right.
             apply hyperdoctrine_hyp.
  Qed.
End PartialEquivalenceRelationInitial.
