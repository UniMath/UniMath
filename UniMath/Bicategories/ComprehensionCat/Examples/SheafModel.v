(**

 The sheaf model of type theory

 Given a site `C` we construct a comprehension category such that
 - Contexts are sheaves over `C`
 - Types in context `Γ` are sheaves over the category of elements of `Γ`
 Since terms in comprehension categories are defined to be sections of the projection, we
 can show that terms are the same as natural families of elements in a sheaf.

 We construct this comprehension category as a full subcomprehension category of the
 presheaf model. Specifically, the sheaf model is a restriction of the presheaf model where
 we only consider contexts and types that are sheaves. Most type formers of sheaves are
 inherited from presheaves. For instance, if we have a sheaf `Γ` and sheaves `A` and `B`
 over `Γ`, then their binary product (of presheaves) is again a sheaf, which gives us an
 interpretation of binary products in the sheaf model. We can do the same for other type
 formers, like extensional identity types, ∑-types, and ∏-types. However, there are two
 type formers that require a different treatment. Both the subobject classifier type and
 the type of natural numbers of sheaves differ from their counterparts in the presheaf
 model. Hence, both these types are constructed by hand in the sheaf model.

 Content
 1. The comprehension category of sheaves as a subcomprehension category of presheaves
 2. ∏-types and the subobject classifier
 3. The category of sheaves is an elementary topos

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.LocallyCartesianClosed.LocallyCartesianClosed.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.FullSubDispCat.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.PowerObject.
Require Import UniMath.CategoryTheory.ElementaryTopos.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.SigmaTypes.
Require Import UniMath.CategoryTheory.Presheaves.PiTypes.
Require Import UniMath.CategoryTheory.Presheaves.PiTypesStable.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.NaturalNumbers.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.Presheaves.ConstructionsSheaves.
Require Import UniMath.CategoryTheory.Presheaves.SigmaSheaf.
Require Import UniMath.CategoryTheory.Presheaves.PiSheaf.
Require Import UniMath.CategoryTheory.Presheaves.ClosedSieves.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifierSheaf.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.HPropMono.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.Democracy.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.EqualizerTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.ProductTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.UnitTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.SigmaTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.DFLCompCatWithProp.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.DFLCompCatToFinLim.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.PiTypesBiequiv.
Require Import UniMath.Bicategories.ComprehensionCat.Biequivalence.LocalProperty.
Require Import UniMath.Bicategories.ComprehensionCat.Examples.PresheafModel.
Require Import UniMath.Bicategories.ComprehensionCat.Examples.FullSubCompCat.

Local Open Scope cat.
Local Open Scope comp_cat.

Section SheafCompCat.
  Context (C : site).

  (** * 1. The comprehension category of sheaves as a subcomprehension category of presheaves *)
  Definition is_sheaf_comp_cat_pred_data
    : comp_cat_pred_data (psh_dfl_full_comp_cat C).
  Proof.
    use make_comp_cat_pred_data.
    - intro Γ.
      use make_hProp.
      + exact (is_sheaf Γ).
      + apply isaprop_is_sheaf.
    - intros Γ HΓ A.
      use make_hProp.
      + exact (is_dep_sheaf A).
      + apply isaprop_is_dep_sheaf.
  Defined.

  Definition is_sheaf_comp_cat_pred
    : comp_cat_pred (psh_dfl_full_comp_cat C).
  Proof.
    use make_comp_cat_pred.
    - exact is_sheaf_comp_cat_pred_data.
    - apply is_sheaf_terminal.
    - exact (λ Γ A HΓ HA, is_sheaf_total_psh HΓ HA).
    - exact (λ Γ₁ Γ₂ A s HΓ₁ HΓ₂ HA, is_dep_sheaf_dep_psh_subst s HA).
  Defined.

  Definition is_sheaf_dfl_full_comp_cat_pred
    : dfl_full_comp_cat_pred (psh_dfl_full_comp_cat C).
  Proof.
    use make_dfl_full_comp_cat_pred.
    - exact is_sheaf_comp_cat_pred.
    - exact (λ Γ HΓ, is_dep_sheaf_unit_dep_psh Γ).
    - exact (λ Γ HΓ A B HA HB, is_dep_sheaf_prod_dep_psh HA HB).
    - exact (λ Γ HΓ A B τ₁ τ₂ HA HB, is_dep_sheaf_equalizer_dep_psh τ₁ τ₂ HA HB).
    - exact (λ Γ HΓ, is_dep_sheaf_psh_to_dep_psh HΓ).
    - exact (λ Γ HΓ A HA B HB, is_dep_sheaf_sigma_dep_psh HA HB).
  Defined.

  Definition sheaf_dfl_full_comp_cat
    : dfl_full_comp_cat
    := full_sub_dfl_full_comp_cat is_sheaf_dfl_full_comp_cat_pred.

  Definition sheaf_dfl_full_comp_cat_incl
    : dfl_full_comp_cat_functor
        sheaf_dfl_full_comp_cat
        (psh_dfl_full_comp_cat C)
    := full_sub_dfl_full_comp_cat_incl is_sheaf_dfl_full_comp_cat_pred.

  (** * 2. ∏-types and the subobject classifier *)
  Definition is_sheaf_dfl_full_pi_comp_cat_pred
    : dfl_full_pi_comp_cat_pred
        (psh_dfl_full_comp_cat C)
        (dependent_prod_psh_comp_cat C).
  Proof.
    use make_dfl_full_pi_comp_cat_pred.
    - exact is_sheaf_dfl_full_comp_cat_pred.
    - exact (λ Γ HΓ A HA B HB, is_dep_sheaf_pi_dep_psh A HB).
  Defined.

  Definition dependent_prod_sheaf_comp_cat
    : comp_cat_dependent_prod sheaf_dfl_full_comp_cat
    := comp_cat_dependent_prod_full_sub_dfl_full_comp_cat
         is_sheaf_dfl_full_pi_comp_cat_pred.

  Definition subobject_classifier_sheaf_comp_cat
    : fiberwise_cat_property
        subobject_classifier_local_property
        sheaf_dfl_full_comp_cat.
  Proof.
    use make_fiberwise_cat_property.
    - exact dep_sheaf_subobject_classifier.
    - intros Γ₁ Γ₂ s.
      exact (dep_sheaf_subobject_classifier_preservation s).
  Defined.

  (** * 3. The category of sheaves is an elementary topos *)
  Definition sheaf_univ_cat_with_finlim
    : univ_cat_with_finlim
    := dfl_full_comp_cat_to_finlim sheaf_dfl_full_comp_cat.

  Definition is_locally_cartesian_closed_sheaf_univ_cat_with_finlim
    : is_locally_cartesian_closed
        (pullbacks_univ_cat_with_finlim sheaf_univ_cat_with_finlim)
    := dfl_comp_cat_to_finlim_disp_psfunctor_pi_types_ob
         sheaf_dfl_full_comp_cat
         dependent_prod_sheaf_comp_cat.

  Definition sheaf_univ_cat_subobject_classifier
    : subobject_classifier
        (terminal_univ_cat_with_finlim
           (dfl_full_comp_cat_to_finlim
              sheaf_dfl_full_comp_cat))
    := local_property_in_dfl_comp_cat
         subobject_classifier_local_property
         sheaf_dfl_full_comp_cat
         subobject_classifier_sheaf_comp_cat.

  Definition sheaf_topos
    : Topos.
  Proof.
    use make_Topos.
    - exact sheaf_univ_cat_with_finlim.
    - use make_Topos_Structure.
      + exact (pullbacks_univ_cat_with_finlim sheaf_univ_cat_with_finlim).
      + exact (terminal_univ_cat_with_finlim sheaf_univ_cat_with_finlim).
      + exact sheaf_univ_cat_subobject_classifier.
      + use PowerObject_from_exponentials.
        use is_locally_cartesian_closed_exponentials.
        exact is_locally_cartesian_closed_sheaf_univ_cat_with_finlim.
  Defined.

  (** * 4. Terms in the presheaf model *)
  Definition sheaf_comp_cat_tm_to_sec
             {Γ : sheaf_dfl_full_comp_cat}
             {A : ty Γ}
             (t : tm Γ A)
    : sheaf_term A.
  Proof.
    use make_psh_term.
    - exact (λ x γ,
             transportf
               ((A : dep_sheaf _) x)
               (from_sheaf_nat_trans_eq (comp_cat_tm_eq t) γ)
               (pr2 ((pr11 t : _ ⟹ _) x γ))).
    - abstract
        (intros x y f γ ;
         etrans ;
         [ apply maponpaths ;
           exact (!(fiber_paths (!(eqtohomot (nat_trans_ax (pr11 t) _ _ f) γ))))
         | ] ;
         rewrite !transport_dep_psh_mor ;
         rewrite !dep_psh_mor_comp' ;
         refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _) ;
         use dep_psh_mor_path_eq ;
         rewrite !id_left, id_right ;
         apply idpath).
  Defined.

  Definition sheaf_comp_cat_sec_to_tm_nat_trans
             {Γ : sheaf_dfl_full_comp_cat}
             {A : ty Γ}
             (t : sheaf_term A)
    : Γ --> Γ & A.
  Proof.
    use make_sheaf_nat_trans.
    use make_nat_trans.
    - exact (λ x γ, γ ,, t x γ).
    - abstract
        (intros x y f ;
         use funextsec ; intro γ ;
         cbn ;
         apply maponpaths ;
         exact (psh_term_naturality t f γ)).
  Defined.

  Definition sheaf_comp_cat_sec_to_tm
             {Γ : sheaf_dfl_full_comp_cat}
             {A : ty Γ}
             (t : sheaf_term A)
    : tm Γ A.
  Proof.
    use make_comp_cat_tm.
    - exact (sheaf_comp_cat_sec_to_tm_nat_trans t).
    - abstract
        (use sheaf_nat_trans_eq ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         cbn ;
         intro x ;
         apply idpath).
  Defined.

  Proposition sheaf_comp_cat_tm_to_sec_to_tm
              {Γ : sheaf_dfl_full_comp_cat}
              {A : ty Γ}
              (t : tm Γ A)
    : sheaf_comp_cat_sec_to_tm (sheaf_comp_cat_tm_to_sec t) = t.
  Proof.
    use eq_comp_cat_tm.
    use sheaf_nat_trans_eq.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use funextsec.
    intro γ ; cbn.
    refine (!_).
    use total2_paths_f.
    - exact (from_sheaf_nat_trans_eq (comp_cat_tm_eq t) γ).
    - cbn.
      apply idpath.
  Qed.

  Proposition sheaf_comp_cat_sec_to_tm_to_sec
              {Γ : sheaf_dfl_full_comp_cat}
              {A : ty Γ}
              (t : sheaf_term A)
    : sheaf_comp_cat_tm_to_sec (sheaf_comp_cat_sec_to_tm t) = t.
  Proof.
    use psh_term_eq.
    intros x γ.
    cbn.
    apply (transportf_set ((A : dep_sheaf _) x)).
    apply setproperty.
  Qed.

  Definition sheaf_comp_cat_tm_weq_sec
             {Γ : sheaf_dfl_full_comp_cat}
             (A : ty Γ)
    : tm Γ A ≃ sheaf_term A.
  Proof.
    use weq_iso.
    - exact sheaf_comp_cat_tm_to_sec.
    - exact sheaf_comp_cat_sec_to_tm.
    - exact sheaf_comp_cat_tm_to_sec_to_tm.
    - exact sheaf_comp_cat_sec_to_tm_to_sec.
  Defined.

  Proposition sheaf_comp_cat_tm_subst
              {Γ Δ : sheaf_dfl_full_comp_cat}
              {A : ty Γ}
              (t : tm Γ A)
              (s : Δ --> Γ)
    : t [[ s ]]tm
      =
      sheaf_comp_cat_sec_to_tm (sheaf_term_subst s (sheaf_comp_cat_tm_to_sec t)).
  Proof.
    use eq_comp_cat_tm.
    refine (!_).
    use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback A s))).
    - use sheaf_nat_trans_eq.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use funextsec ; intro γ.
      refine (!_).
      use total2_paths_f.
      + exact (from_sheaf_nat_trans_eq (comp_cat_tm_eq t) _).
      + apply idpath.
    - use sheaf_nat_trans_eq.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      use funextsec ; intro γ.
      apply idpath.
  Qed.

  Proposition sheaf_comp_cat_tm_coerce
              {Γ : sheaf_dfl_full_comp_cat}
              {A B : ty Γ}
              (f : A <: B)
              (t : tm Γ A)
    : t ↑ f
      =
      sheaf_comp_cat_sec_to_tm (sheaf_term_coerce f (sheaf_comp_cat_tm_to_sec t)).
  Proof.
    use eq_comp_cat_tm.
    use sheaf_nat_trans_eq.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use funextsec ; intro γ.
    use total2_paths_f ; cbn.
    - exact (from_sheaf_nat_trans_eq (comp_cat_tm_eq t) _).
    - rewrite transport_map.
      apply maponpaths.
      apply maponpaths_2.
      apply setproperty.
  Qed.

  Proposition sheaf_comp_cat_id_subst_ty
              {Γ : sheaf C}
              (A : dep_sheaf Γ)
              {x : C}
              {γ : (Γ x : hSet)}
              (a : A x γ)
    : (id_subst_ty (C := sheaf_dfl_full_comp_cat) A : dep_psh_nat_trans _ _ _) x γ a
      =
      a.
  Proof.
    refine (_ @ psh_comp_cat_id_subst_ty C A a).
    refine (maponpaths (λ (z : dep_psh_nat_trans _ _ _), z x γ a) _).
    exact (full_sub_comp_cat_id_subst_ty is_sheaf_comp_cat_pred A).
  Qed.

  Proposition sheaf_comp_cat_id_subst_ty_inv
              {Γ : sheaf C}
              (A : dep_sheaf Γ)
              {x : C}
              {γ : (Γ x : hSet)}
              (a : A x γ)
    : (id_subst_ty_inv (C := sheaf_dfl_full_comp_cat) A : dep_psh_nat_trans _ _ _) x γ a
      =
      a.
  Proof.
    refine (_ @ psh_comp_cat_id_subst_ty_inv C A a).
    refine (maponpaths
              (λ (z : dep_psh_nat_trans _ _ _), z x γ _)
              _).
    exact (full_sub_comp_cat_id_subst_ty_inv is_sheaf_comp_cat_pred A).
  Qed.

  Proposition sheaf_comp_cat_comp_subst_ty
              {Γ₁ Γ₂ Γ₃ : sheaf C}
              (s₁ : sheaf_nat_trans Γ₁ Γ₂)
              (s₂ : sheaf_nat_trans Γ₂ Γ₃)
              (A : dep_sheaf Γ₃)
              {x : C}
              {γ : (Γ₁ x : hSet)}
              (a : A x (s₂ x (s₁ x γ)))
    : (comp_subst_ty (C := sheaf_dfl_full_comp_cat) s₁ s₂ A : dep_psh_nat_trans _ _ _) x γ a
      =
      a.
  Proof.
    refine (_ @ psh_comp_cat_comp_subst_ty C s₁ s₂ A a).
    refine (maponpaths
              (λ (z : dep_psh_nat_trans _ _ _), z x γ _)
              _).
    exact (full_sub_comp_cat_comp_subst_ty is_sheaf_comp_cat_pred s₁ s₂ A).
  Qed.

  Proposition sheaf_comp_cat_comp_subst_ty_inv
              {Γ₁ Γ₂ Γ₃ : sheaf C}
              (s₁ : sheaf_nat_trans Γ₁ Γ₂)
              (s₂ : sheaf_nat_trans Γ₂ Γ₃)
              (A : dep_sheaf Γ₃)
              {x : C}
              {γ : (Γ₁ x : hSet)}
              (a : A x (s₂ x (s₁ x γ)))
    : (comp_subst_ty_inv (C := sheaf_dfl_full_comp_cat) s₁ s₂ A : dep_psh_nat_trans _ _ _) x γ a
      =
      a.
  Proof.
    refine (_ @ psh_comp_cat_comp_subst_ty_inv C s₁ s₂ A a).
    refine (maponpaths
              (λ (z : dep_psh_nat_trans _ _ _), z x γ _)
              _).
    exact (full_sub_comp_cat_comp_subst_ty_inv is_sheaf_comp_cat_pred s₁ s₂ A).
  Qed.

  Proposition sheaf_comp_cat_eq_subst_ty
              {Γ₁ Γ₂ : sheaf C}
              {s₁ s₂ : sheaf_nat_trans Γ₁ Γ₂}
              (A : dep_sheaf Γ₂)
              (p : s₁ = s₂)
              {x : C}
              {γ : (Γ₁ x : hSet)}
              (a : A x (s₁ x γ))
    : (eq_subst_ty (C := sheaf_dfl_full_comp_cat) A p : dep_psh_nat_trans _ _ _) x γ a
      =
      transportf (A x) (from_sheaf_nat_trans_eq p γ) a.
  Proof.
    refine (_ @ psh_comp_cat_eq_subst_ty C A (maponpaths pr1 p) a @ _).
    - refine (maponpaths
                (λ (z : dep_psh_nat_trans _ _ _), z x γ _)
                _).
      exact (full_sub_comp_cat_eq_subst_ty is_sheaf_comp_cat_pred A p).
    - apply maponpaths_2.
      apply setproperty.
  Qed.

  Proposition sheaf_comp_cat_eq_subst_ty_inv
              {Γ₁ Γ₂ : sheaf C}
              {s₁ s₂ : sheaf_nat_trans Γ₁ Γ₂}
              (A : dep_sheaf Γ₂)
              (p : s₁ = s₂)
              {x : C}
              {γ : (Γ₁ x : hSet)}
              (a : A x (s₂ x γ))
    : (eq_subst_ty_inv (C := sheaf_dfl_full_comp_cat) A p : dep_psh_nat_trans _ _ _) x γ a
      =
      transportb (A x) (from_sheaf_nat_trans_eq p γ) a.
  Proof.
    refine (_ @ psh_comp_cat_eq_subst_ty_inv C A (maponpaths pr1 p) a @ _).
    - refine (maponpaths
                (λ (z : dep_psh_nat_trans _ _ _), z x γ _)
                _).
      exact (full_sub_comp_cat_eq_subst_ty_inv is_sheaf_comp_cat_pred A p).
    - apply maponpaths_2.
      apply setproperty.
  Qed.

  Proposition sheaf_comp_cat_coerce_subst_ty
              {Γ₁ Γ₂ : sheaf C}
              (s : sheaf_nat_trans Γ₁ Γ₂)
              {A B : dep_sheaf Γ₂}
              (f : dep_psh_nat_trans A B (nat_trans_id _))
              {x : C}
              {γ : (Γ₁ x : hSet)}
              (a : A x (s x γ))
    : (coerce_subst_ty (C := sheaf_dfl_full_comp_cat) s f : dep_psh_nat_trans _ _ _) x γ a
      =
      f x (s x γ) a.
  Proof.
    refine (_ @ psh_comp_cat_coerce_subst_ty C s f a).
    refine (maponpaths
              (λ (z : dep_psh_nat_trans _ _ _), z x γ _)
              _).
    exact (full_sub_comp_cat_coerce_subst_ty is_sheaf_comp_cat_pred s f).
  Qed.

  Proposition sheaf_comp_cat_sub_to_extension
              {Γ Δ : sheaf C}
              {A : dep_sheaf Γ}
              (s : sheaf_nat_trans Δ Γ)
              (t : comp_cat_tm (C := sheaf_dfl_full_comp_cat) Δ (dep_sheaf_subst s A))
              {x : C}
              (δ : (Δ x : hSet))
    : (sub_to_extension (C := sheaf_dfl_full_comp_cat) s t : sheaf_nat_trans _ _) x δ
      =
      s x δ
      ,,
      sheaf_comp_cat_tm_to_sec t x δ.
  Proof.
    cbn.
    use total2_paths_f ; cbn.
    - apply maponpaths.
      exact (from_sheaf_nat_trans_eq (comp_cat_tm_eq t) δ).
    - rewrite (functtransportf (s x) (A x)).
      apply maponpaths_2.
      apply setproperty.
  Qed.

  Proposition sheaf_comp_cat_var
              (Γ : sheaf_dfl_full_comp_cat)
              (A : ty Γ)
    : comp_cat_tm_var Γ A = sheaf_comp_cat_sec_to_tm (sheaf_term_var Γ A).
  Proof.
    use eq_comp_cat_tm.
    refine (!_).
    use (PullbackArrowUnique _ (isPullback_Pullback (comp_cat_pullback A _))).
    - use sheaf_nat_trans_eq.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn.
      apply idpath.
    - use sheaf_nat_trans_eq.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn.
      apply idpath.
  Qed.

  Proposition sheaf_comp_cat_hprop_ty
              {Γ : sheaf C}
              (A : dep_sheaf Γ)
              (HA : ∏ (x : C) (xx : (Γ x : hSet)), isaprop (A x xx))
    : is_hprop_ty (C := sheaf_dfl_full_comp_cat) A.
  Proof.
    use mono_ty_to_hprop_ty.
    use injective_sheaf_isMonic.
    cbn ; intros x [ xx a₁ ] [ xx' a₂ ] p.
    cbn in p.
    induction p.
    apply maponpaths.
    specialize (HA x xx).
    apply (proofirrelevance _ HA).
  Qed.

  Proposition sheaf_comp_cat_hprop_ty_inv
              {Γ : sheaf C}
              (A : dep_sheaf Γ)
              (HA : is_hprop_ty (C := sheaf_dfl_full_comp_cat) A)
              (x : C)
              (xx : (Γ x : hSet))
    : isaprop (A x xx).
  Proof.
    apply hprop_ty_to_mono_ty in HA.
    use invproofirrelevance.
    intros a₁ a₂.
    pose proof (isMonic_sheaf_injective
                  HA
                  (x := x)
                  (xx₁ := (xx ,, a₁)) (xx₂ := (xx ,, a₂))
                  (idpath _))
      as p.
    refine (!_ @ fiber_paths p).
    apply (transportf_set (A x)).
    apply setproperty.
  Qed.

  Proposition sheaf_comp_cat_hprop_ty_weq
              {Γ : sheaf C}
              (A : dep_sheaf Γ)
    : is_hprop_ty (C := sheaf_dfl_full_comp_cat) A
      ≃
      (∏ (x : C) (xx : (Γ x : hSet)), isaprop (A x xx)).
  Proof.
    use weqimplimpl.
    - exact (sheaf_comp_cat_hprop_ty_inv A).
    - exact (sheaf_comp_cat_hprop_ty A).
    - apply isaprop_is_hprop_ty.
    - abstract
        (do 2 (use impred ; intro) ;
         apply isapropisaprop).
  Defined.
End SheafCompCat.
