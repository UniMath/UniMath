From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac2 Backtrace.
Set Ltac Batch Debug.
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.DaggerCategories.Univalence.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.
Require Import UniMath.CategoryTheory.DaggerCategories.Transformations.

Local Open Scope cat.

Local Lemma equality_on_objects_from_functor_equality
      {C D : category}
      (F G : functor_data C D)
      (p : ∏ c: C, F c = G c)
      (q : transportf (λ F : C → D, ∏ a b : C, C ⟦ a, b ⟧ → D ⟦ F a, F b ⟧)
   (funextsec (λ _ : C, D) (pr1 F) (pr1 G) (λ x : C, p x)) (pr2 F) = pr2 G)
  : ∏ c : C,
      toforallpaths (λ _ : C, D) F G
    (base_paths F G
       (total2_paths_f ((funextsec (λ _ : C, D) (pr1 F) (pr1 G) (λ x : C, p x)))
                       q)) c = p c.
Proof.
  intro c.
  rewrite base_total2_paths.
  now rewrite toforallpaths_funextsec.
Qed.

Local Definition functor_eq_eq_from_functor_ob_eq'
             (C C': category)
             (F G : functor C C') (p q : pr1 F = pr1 G)
             (H : (base_paths _ _  p) =
                    (base_paths _ _ q)) :
    p = q.
Proof.
  apply (invmaponpathsweq (total2_paths_equiv _ _ _ )); simpl.
  use total2_paths_f.
  + exact H.
  + apply uip.
    do 2 (apply impred_isaset ; intro).
    apply funspace_isaset.
    apply C'.
Defined.

Section DaggerFunctorCategories.

  Context {C D : category}
          (dagC : dagger C) (dagD : dagger D).

  Definition dagger_functor_disp_cat
    : disp_cat (functor_category C D)
    := disp_full_sub [C,D] (λ F, is_dagger_functor dagC dagD F).

  Definition dagger_functor_cat
    : category
    := total_category dagger_functor_disp_cat.

  Definition make_dagger_functor
             {F : functor C D}
             (dagF : is_dagger_functor dagC dagD F)
    : dagger_functor_cat
    := F ,, dagF.

  Definition make_dagger_transformation
             (F G : dagger_functor_cat)
             (α : nat_trans (pr1 F : functor _ _) (pr1 G : functor _ _))
    : dagger_functor_cat⟦F,G⟧
    := α ,, tt.

  Definition dagger_functor_cat_structure
    : dagger_structure dagger_functor_cat
    := λ F G α, make_dagger_transformation _ _ (dagger_adjoint (pr2 F) (pr2 G) (pr1 α)).

  Lemma dagger_transformation_equality
        {F G : functor C D}
        {dagF : is_dagger_functor dagC dagD F}
        {dagG : is_dagger_functor dagC dagD G}
        (α β : dagger_functor_cat⟦make_dagger_functor dagF , make_dagger_functor dagG⟧)
    : (∏ x : C, pr11 α x = pr11 β x) -> α = β.
  Proof.
    intro p.
    use subtypePath.
    { intro ; apply isapropunit. }
    apply (nat_trans_eq D).
    exact p.
  Qed.

  Lemma dagger_functor_cat_laws
    : dagger_laws dagger_functor_cat_structure.
  Proof.
    (*use make_dagger_laws*) repeat split ;
      (intro ; intros ; apply dagger_transformation_equality ; intro).
    - apply dagger_to_law_id.
    - apply dagger_to_law_comp.
    - apply dagger_to_law_idemp.
  Qed.

  Definition dagger_on_functor_cat : dagger dagger_functor_cat
    := _ ,, dagger_functor_cat_laws.

End DaggerFunctorCategories.

Section Univalence.

  Context {C D : category}
          {dagC : dagger C} {dagD : dagger D}
          {F G : functor C D}
          (dagF : is_dagger_functor dagC dagD F)
          (dagG : is_dagger_functor dagC dagD G).

  Local Definition unitary_functors_eq
    : UU
    := ∑ p : (∏ x : pr11 C, unitary dagD (F x) (G x)),
        ∏ (x y : C) (f : C⟦x,y⟧),
        #G f = (dagD _ _ (pr1 (p x))) · #F f · (pr1 (p y)).

  Local Definition functors_eq_data
    : UU
    := ∑ p : (∏ x : C, (pr11 F x) = (pr11 G x)),
        ∏ (x y : pr11 C) (f : (pr11 C)⟦x,y⟧),
        #G f = idtodaggermor dagD (! p x) · #F f · idtodaggermor dagD (p y).

  Definition unitary_functors_equiv_unitary
    : unitary_functors dagF dagG ≃ unitary (dagger_functor_cat_structure dagC dagD) (F,,dagF) (G,,dagG).
  Proof.
    use weq_iso.
    - intro α.
      exists (make_dagger_transformation dagC dagD _ _ (pr1 α : nat_trans (pr1 (F,,dagF)) (pr1 (G,,dagG)))).
      abstract (split ; apply dagger_transformation_equality ; intro c ; apply (pr2 α c)).
    - intro α.
      exists (pr11 α).
      abstract (
          intro c ;
          split ;
          [ exact (eqtohomot (base_paths _ _ (base_paths _ _ (pr12 α))) c)
          | exact (eqtohomot (base_paths _ _ (base_paths _ _ (pr22 α))) c) ]).
    - abstract (
          intro α ;
          use total2_paths_f ;
          [ use (nat_trans_eq (pr2 D)) ; intro ; apply idpath
          | use proofirrelevance ;
            apply impred_isaprop ; intro ;
            apply Isos.isaprop_is_inverse_in_precat]).
    - abstract (
          intro α ;
          use total2_paths_f ;
          [ apply dagger_transformation_equality ;
            intro ; apply idpath
          | apply isaprop_is_unitary]).
  Defined.

  Lemma unitary_functor_eq_to_unitary_functors_naturality
        (p : unitary_functors_eq)
    : is_nat_trans F G (λ c : pr11 C, pr1 (pr1 p c)).
  Proof.
    intros c1 c2 f.
    refine (_ @ maponpaths (compose _) (! pr2 p _ _ _)).
    refine (_ @ assoc' _ _ _).
    apply maponpaths_2.
    refine (_ @ assoc' _ _ _).
    refine (! id_left _ @ _).
    apply maponpaths_2, pathsinv0, (pr1 p).
  Qed.

  Definition unitary_functors_eq_to_unitary_functors
    : unitary_functors_eq -> unitary_functors dagF dagG.
  Proof.
    intros [p q].
    use tpair.
    - apply (make_nat_trans _ _ (λ c, pr1 (p c))).
      exact (unitary_functor_eq_to_unitary_functors_naturality (p,,q)).
    - abstract (intro ; apply p).
  Defined.

  Lemma unitary_functors_eq_from_unitary_functors_naturality
        (α : unitary_functors dagF dagG)
    : ∏ (x y : C) (f : C ⟦ x, y ⟧), # G f = dagD (F x) (G x) ((pr1 α) x) · # F f · (pr1 α) y.
  Proof.
    intros c1 c2 f.
    apply pathsinv0.
    refine (assoc' _ _ _ @ _).
    refine (maponpaths (compose _) (pr21 α _ _ _) @ _).
    refine (assoc _ _ _ @ _).
    refine (_ @ id_left _).
    apply maponpaths_2, (pr2 α).
  Qed.

  Definition unitary_functors_eq_from_unitary_functors
    : unitary_functors dagF dagG -> unitary_functors_eq.
  Proof.
    intros [α p].
    use tpair.
    + intro c.
      exists (α c).
      apply p.
    + exact (unitary_functors_eq_from_unitary_functors_naturality (α,,p)).
  Defined.

  Lemma unitary_functors_eq_equiv_unitary_functors_inv_law1
    :  ∏ x : unitary_functors_eq,
        unitary_functors_eq_from_unitary_functors (unitary_functors_eq_to_unitary_functors x) = x.
  Proof.
    intro.
    use total2_paths_f.
    - apply funextsec ; intro.
      apply unitary_eq, idpath.
    - repeat (apply funextsec ; intro).
      apply homset_property.
  Qed.

  Lemma unitary_functors_eq_equiv_unitary_functors_inv_law2
    :  ∏ y : unitary_functors dagF dagG,
        unitary_functors_eq_to_unitary_functors (unitary_functors_eq_from_unitary_functors y) = y.
  Proof.
    intro.
    use total2_paths_f.
    - use (nat_trans_eq (pr2 D)).
      intro ; apply idpath.
    - apply funextsec ; intro.
      apply Isos.isaprop_is_inverse_in_precat.
  Qed.

  Definition unitary_functors_eq_equiv_unitary_functors
    : unitary_functors_eq ≃ unitary_functors dagF dagG.
  Proof.
    use weq_iso.
    - exact unitary_functors_eq_to_unitary_functors.
    - exact unitary_functors_eq_from_unitary_functors.
    - exact unitary_functors_eq_equiv_unitary_functors_inv_law1.
    - exact unitary_functors_eq_equiv_unitary_functors_inv_law2.
  Defined.

  Definition functors_eq_data_to_unitary_functors_eq
             (u : is_univalent_dagger dagD)
    : functors_eq_data -> unitary_functors_eq.
  Proof.
    intro p.
    exists (λ c, idtodaggeriso dagD _ _ (pr1 p c)).
    intros x y f.
    refine (pr2 p x y f @ _).
    do 2 apply maponpaths_2.
    etrans.
    { apply (idtodaggeriso_is_dagger_of_idtodaggeriso dagD). }
    do 3 apply maponpaths.
    apply pathsinv0inv0.
  Defined.

  Definition functors_eq_data_from_unitary_functors_eq
             (u : is_univalent_dagger dagD)
    : unitary_functors_eq -> functors_eq_data.
  Proof.
    intros p.
    use tpair.
    - intro c ; apply u ; exact (pr1 p c).
    - intros x y f.
      refine (pr2 p x y f @ _).
      apply maponpaths_compose.
      + apply maponpaths_2.
        refine (_ @ ! idtodaggeriso_is_dagger_of_idtodaggeriso dagD _).
        do 2 apply maponpaths.
        etrans.
        * apply pathsinv0, (idtodaggeriso_daggerisotoid u).
        * apply maponpaths, pathsinv0, pathsinv0inv0.
      + apply pathsinv0, idtodaggermor_daggerisotoid.
  Defined.

  Lemma functors_eq_data_equiv_unitary_functors_eq_inv_law1
        (u : is_univalent_dagger dagD)
    :   ∏ x : functors_eq_data,
        functors_eq_data_from_unitary_functors_eq u (functors_eq_data_to_unitary_functors_eq u x) = x.
  Proof.
    intro p.
    use total2_paths_f.
    - apply funextsec ; intro.
      apply daggerisotoid_idtodaggeriso.
    - repeat (apply funextsec ; intro).
      apply homset_property.
  Qed.

  Lemma functors_eq_data_equiv_unitary_functors_eq_inv_law2
        (u : is_univalent_dagger dagD)
    :   ∏ y : unitary_functors_eq,
        functors_eq_data_to_unitary_functors_eq u (functors_eq_data_from_unitary_functors_eq u y) = y.
  Proof.
    intro p.
    use total2_paths_f.
    - apply funextsec ; intro.
      use total2_paths_f.
      + apply maponpaths, idtodaggeriso_daggerisotoid.
      + apply isaprop_is_unitary.
    - repeat (apply funextsec ; intro).
      apply homset_property.
  Qed.

  Definition functors_eq_data_equiv_unitary_functors_eq
             (u : is_univalent_dagger dagD)
    : functors_eq_data ≃ unitary_functors_eq.
  Proof.
    use weq_iso.
    - exact (functors_eq_data_to_unitary_functors_eq u).
    - exact (functors_eq_data_from_unitary_functors_eq u).
    - exact (functors_eq_data_equiv_unitary_functors_eq_inv_law1 u).
    - exact (functors_eq_data_equiv_unitary_functors_eq_inv_law2 u).
  Defined.

  Lemma transport_of_dagger_functor_map_is_pointwise
        (F0 G0 : pr11 C -> pr11 D)
        (F1 : ∏ a b : pr11 C, a --> b -> F0 a --> F0 b)
        (gamma : F0  = G0 )
        (a b : pr11 C) (f : a --> b) :
    transportf (fun x : pr11 C -> pr11 D =>
                  ∏ a0 b0 : pr11 C, a0 --> b0 -> x a0 --> x b0)
               gamma F1 a b f =
      Univalence.double_transport (toforallpaths (λ _ : pr11 C, pr11 D) F0 G0 gamma a)
                       (toforallpaths (λ _ : pr11 C, pr11 D) F0 G0 gamma b)
                       (F1 a b f).
  Proof.
    induction gamma.
    apply idpath.
  Qed.

  Lemma double_transport_idtodaggeriso (a a' b b' : pr111 D)
        (p : a = a') (q : b = b')  (f : a --> b) :
    Univalence.double_transport p q f = pr1 (idtodaggeriso dagD _ _ (! p)) · f · pr1 (idtodaggeriso dagD _ _ q).
  Proof.
    destruct p.
    destruct q.
    intermediate_path (identity _ · f).
    - apply pathsinv0; apply id_left.
    - apply pathsinv0; apply id_right.
  Qed.

  Definition equality_to_functors_eq_data
    : pr1 F = pr1 G -> functors_eq_data.
  Proof.
    intro p.
    exists (λ c, eqtohomot (base_paths _ _ p) c).
    abstract (
        intros x y f ;
        refine (! eqtohomot (eqtohomot (eqtohomot (fiber_paths p) x) y) f @ _) ;
        etrans ; [
          apply transport_of_dagger_functor_map_is_pointwise
        | apply double_transport_idtodaggeriso]
      ).
  Defined.

  Definition equality_from_functors_eq_data
    : functors_eq_data → pr1 F = pr1 G.
  Proof.
    intros [p q].
    use total2_paths_f.
    - apply funextsec ; intro ; apply p.
    - abstract(
          repeat (apply funextsec ; intro) ;
          rewrite transport_of_dagger_functor_map_is_pointwise ;
          rewrite double_transport_idtodaggeriso ;
          rewrite toforallpaths_funextsec ;
          exact (! q _ _ _)
        ).
  Defined.

  Lemma equality_equiv_functors_eq_data_inv_law1
    : ∏ x : pr1 F = pr1 G, equality_from_functors_eq_data (equality_to_functors_eq_data x) = x.
  Proof.
    intro.
    apply functor_eq_eq_from_functor_ob_eq'.
    refine (base_total2_paths _ @ _).
    apply (invmaponpathsweq (weqtoforallpaths _ _ _)).
    simpl.
    rewrite toforallpaths_funextsec.
    apply funextsec; intro ; apply idpath.
  Qed.

  Lemma equality_equiv_functors_eq_data_inv_law2
    : ∏ y : functors_eq_data, equality_to_functors_eq_data (equality_from_functors_eq_data y) = y.
  Proof.
    intros [p q].
    use total2_paths_f.
    - apply funextsec ; intro.
      apply equality_on_objects_from_functor_equality.
    - apply proofirrelevance.
      do 3 (apply impred_isaprop ; intro).
      apply homset_property.
  Qed.

  Definition equality_equiv_functors_eq_data
    : pr1 F = pr1 G ≃ functors_eq_data.
  Proof.
    use weq_iso.
    - exact equality_to_functors_eq_data.
    - exact equality_from_functors_eq_data.
    - exact equality_equiv_functors_eq_data_inv_law1.
    - exact equality_equiv_functors_eq_data_inv_law2.
  Defined.

  Local Definition id_pr1_to_pr11_id
    : F = G ≃ pr1 F = pr1 G.
  Proof.
    use subtypeInjectivity.
    intro.
    apply isaprop_is_functor.
    apply (pr2 D).
  Defined.

  Local Definition id_to_pr1_id
    : (F,,dagF) = (G,,dagG) ≃ F = G.
  Proof.
    use subtypeInjectivity.
    intro.
    apply isaprop_is_dagger_functor.
  Defined.

  Local Definition univalence_iso
             (u : is_univalent_dagger dagD)
    : (F,,dagF) = (G,,dagG) ≃  unitary (dagger_functor_cat_structure dagC dagD) (F,, dagF) (G,, dagG).
  Proof.
    refine (_ ∘ id_to_pr1_id)%weq.
    refine (_ ∘ id_pr1_to_pr11_id)%weq.
    refine (_ ∘ equality_equiv_functors_eq_data)%weq.
    refine (_ ∘ functors_eq_data_equiv_unitary_functors_eq u)%weq.
    refine (_ ∘ unitary_functors_eq_equiv_unitary_functors)%weq.
    exact unitary_functors_equiv_unitary.
  Defined.

End Univalence.

Lemma dagger_functor_cat_is_dagger_univalent
      {C D : category}
      (dagC : dagger C) (dagD : dagger D)
      (u : is_univalent_dagger dagD)
  : is_univalent_dagger (dagger_on_functor_cat dagC dagD).
Proof.
  intros F G.
  use weqhomot.
  - exact (univalence_iso (pr2 F) (pr2 G) u).
  - intro p.
    induction p.
    use subtypePath.
    { intro ; apply isaprop_is_unitary. }
    use subtypePath.
    { intro ; apply isapropunit. }
    apply (nat_trans_eq (pr2 D)).
    intro ; apply idpath.
Qed.
