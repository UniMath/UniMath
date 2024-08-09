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
Require Import UniMath.CategoryTheory.Hyperdoctrines.Hyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.FirstOrderHyperdoctrine.
Require Import UniMath.CategoryTheory.Hyperdoctrines.PartialEqRels.PERs.

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
