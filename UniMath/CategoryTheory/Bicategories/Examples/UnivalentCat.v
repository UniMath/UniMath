Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.OpCellBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.Bicategories.equiv_to_adjequiv.

Open Scope cat.

Definition data_cat_eq_1
           (C D : precategory_data)
           (Fo : (ob C) = ob D)
  : UU
  := transportf (λ z, z → z → UU) Fo (@precategory_morphisms C)
     =
     @precategory_morphisms D.

Definition data_cat_eq_2
           (C D : precategory_data)
           (Fo : (ob C) = ob D)
  : UU
  := ∏ (a b : ob C), C⟦a,b⟧ = D⟦eqweqmap Fo a,eqweqmap Fo b⟧.

Definition data_cat_eq_1_to_2
           (C D : precategory_data)
           (Fo : (ob C) = ob D)
  : data_cat_eq_1 C D Fo ≃ data_cat_eq_2 C D Fo.
Proof.
  induction C as [C HC].
  induction C as [CO CM].
  induction D as [D HD].
  induction D as [DO DM].
  cbn in *.
  induction Fo.
  unfold data_cat_eq_1, data_cat_eq_2.
  cbn.
  refine (_ ∘ weqtoforallpaths _ _ _)%weq.
  use weqonsecfibers.
  intros x.
  exact (weqtoforallpaths _ _ _)%weq.
Defined.

Definition cat_eq_1
           (C D : precategory_data)
  : UU
  := ∑ (F : ∑ (Fo : ob C = ob D), data_cat_eq_1 C D Fo),
       (pr1 (transportf (λ x, precategory_id_comp x)
                        (total2_paths_f (pr1 F) (pr2 F))
                        (pr2 C))
        = pr1 (pr2 D))
     ×
       pr2 (transportf (λ x, precategory_id_comp x)
                       (total2_paths_f (pr1 F) (pr2 F))
                       (pr2 C))
       =
       pr2(pr2 D).

Definition cat_eq_2
           (C D : precategory_data)
  : UU
  := ∑ (F : ∑ (Fo : ob C = ob D), data_cat_eq_2 C D Fo),
       (∏ (a : C), eqweqmap (pr2 F a a) (identity a) = identity (eqweqmap (pr1 F) a))
     ×
       (∏ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧),
         eqweqmap (pr2 F a c) (f · g)
         =
         eqweqmap (pr2 F a b) f · eqweqmap (pr2 F b c) g).

Definition cat_equiv
           (C D : precategory_data)
  : UU
  := ∑ (F : ∑ (Fo : ob C ≃ D), ∏ (a b : ob C), C⟦a,b⟧ ≃ D⟦Fo a,Fo b⟧),
       (∏ (a : C), (pr2 F) a a (identity a) = identity (pr1 F a))
     ×
       (∏ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧), pr2 F a c (f · g) = pr2 F a b f · pr2 F b c g).

Definition cat_path_to_cat_eq_1
           (C D : precategory_data)
  : C = D ≃ cat_eq_1 C D.
Proof.
  refine (_ ∘ total2_paths_equiv _ _ _)%weq.
  use weqbandf.
  - apply total2_paths_equiv.
  - intro p ; cbn.
    induction C as [C HC].
    induction D as [D HD].
    cbn in *.
    induction p ; cbn ; unfold idfun.
    refine (_ ∘ total2_paths_equiv _ _ _)%weq.
    use weqfibtototal.
    intros p.
    cbn.
    rewrite transportf_const.
    exact (idweq _).
Defined.

Definition cat_eq_1_to_cat_eq_2
           (C D : precategory_data)
           (DS : ∏ (x y : D), isaset (precategory_morphisms x y))
  : cat_eq_1 C D ≃ cat_eq_2 C D.
Proof.
  use weqbandf.
  - use weqfibtototal.
    intro p.
    exact (data_cat_eq_1_to_2 C D p).
  - intros p.
    induction C as [C HC].
    induction C as [CO CM].
    induction HC as [CI CC].
    induction D as [D HD].
    induction D as [DO DM].
    induction HD as [DI DC].
    induction p as [p1 p2] ; cbn in *.
    unfold data_cat_eq_1 in p2.
    induction p1 ; cbn in *.
    induction p2 ; cbn ; unfold idfun.
    use weqdirprodf.
    + use weqimplimpl.
      * intros f a.
        induction f.
        reflexivity.
      * intros f.
        apply funextsec.
        intro z.
        apply f.
      * intro.
        apply impred_isaset.
        intro.
        apply DS.
      * apply impred.
        intro.
        apply DS.
    + use weqimplimpl.
      * intros p.
        induction p.
        reflexivity.
      * intros p.
        apply funextsec ; intro a.
        apply funextsec ; intro b.
        apply funextsec ; intro c.
        apply funextsec ; intro f.
        apply funextsec ; intro g.
        specialize (p a b c f g).
        induction p.
        reflexivity.
      * repeat (apply impred_isaset ; intro).
        apply DS.
      * repeat (apply impred ; intro).
        apply DS.
Defined.

Definition weq_cat_eq_cat_equiv
           (C D : precategory_data)
  : cat_eq_2 C D ≃ cat_equiv C D.
Proof.
  use weqbandf.
  - use weqbandf.
    + apply univalence.
    + intros p.
      unfold data_cat_eq_2.
      use weqonsecfibers.
      intros x.
      use weqonsecfibers.
      intros y.
      apply univalence.
  - intros q.
    apply idweq.
Defined.

Definition cat_equiv_to_catiso
           (C D : precategory_data)
  : cat_equiv C D → catiso C D.
Proof.
  intros F.
  use tpair.
  - use tpair.
    + use tpair.
      * exact (pr1(pr1 F)).
      * exact (pr2(pr1 F)).
    + split.
      * exact (pr1(pr2 F)).
      * exact (pr2(pr2 F)).
  - split.
    + intros a b.
      apply (pr2(pr1 F)).
    + apply (pr1(pr1 F)).
Defined.

Definition catiso_to_cat_equiv
           (C D : precategory_data)
  : catiso C D → cat_equiv C D.
Proof.
  intros F.
  use tpair.
  - use tpair.
    + use weqpair.
      * exact (functor_on_objects F).
      * apply F.
    + intros a b.
      use weqpair.
      * exact (functor_on_morphisms F).
      * apply F.
  - split.
    + exact (functor_id F).
    + exact (@functor_comp _ _ F).
Defined.

Definition cat_equiv_to_catiso_weq
           (C D : category)
  : cat_equiv C D ≃ catiso C D.
Proof.
  refine (cat_equiv_to_catiso C D ,, _).
  use isweq_iso.
  - exact (catiso_to_cat_equiv C D).
  - reflexivity.
  - reflexivity.
Defined.

Definition path_sigma_hprop
           {A : UU}
           (B : A → UU)
           (x y : ∑ (z : A), B z)
           (HB : isaprop (B (pr1 y)))
  : x = y ≃ pr1 x = pr1 y.
Proof.
  refine (weqpr1 _ _ ∘ total2_paths_equiv _ _ _)%weq.
  intros.
  apply HB.
Defined.

Definition path_precat
           (C D : category)
  : C = D ≃ precategory_data_from_precategory C = D.
Proof.
  refine (path_sigma_hprop _ _ _ _ ∘ path_sigma_hprop _ _ _ _)%weq.
  - intros.
    apply isaprop_has_homsets.
  - intros.
    apply isaprop_is_precategory.
    apply D.
Defined.

Definition univalent_cat : bicat
  := fullsubprebicat bicat_of_cats (λ C, is_univalent (pr1 C)).

Definition path_univalent_cat
           (C D : univalent_cat)
  : C = D ≃ pr1 C = pr1 D.
Proof.
  apply path_sigma_hprop.
  simpl.
  apply isaprop_is_univalent.
Defined.

Definition univalent_cat_idtoiso_2_1
           {C D : univalent_cat}
           (f g : univalent_cat⟦C,D⟧)
  : f = g ≃ invertible_2cell f g.
Proof.
  refine (_ ∘ weqpair (@idtoiso (functor_category (pr1(pr1 C)) (pr1 D)) (pr1 f) (pr1 g)) _
            ∘ path_sigma_hprop _ _ _ _)%weq.
  - exact isapropunit.
  - destruct C as [C HC].
    destruct D as [D HD].
    destruct D as [D HD2].
    destruct HD as [DU DS].
    exact (pr1 (is_univalent_functor_category (pr1 C) D (DU,,HD2)) (pr1 f) (pr1 g)).
  - use weqbandf.
    + use tpair.
      * exact (λ F, F ,, tt).
      * use isweq_iso.
        ** exact pr1.
        ** reflexivity.
        ** intros F.
           use subtypeEquality.
           *** intro ; apply isapropunit.
           *** reflexivity.
    + intros F.
      use weqimplimpl.
      * intros η.
        use tpair.
        ** exact (inv_from_iso (_ ,, η) ,, tt).
        ** split.
           *** use subtypeEquality.
               **** intro ; apply isapropunit.
               **** exact (iso_inv_after_iso (_ ,, η)).
           *** use subtypeEquality.
               **** intro ; apply isapropunit.
               **** exact (iso_after_iso_inv (_ ,, η)).
      * intros η.
        use is_iso_qinv.
        ** apply (η^-1).
        ** split.
           *** exact (maponpaths pr1 (pr1(pr2 η))).
           *** exact (maponpaths pr1 (pr2(pr2 η))).
      * apply isaprop_is_iso.
      * apply isaprop_is_invertible_2cell.
Defined.

Definition univalent_cat_is_univalent_2_1
  : is_univalent_2_1 univalent_cat.
Proof.
  intros C D f g.
  use isweqhomot.
  - exact (univalent_cat_idtoiso_2_1 f g).
  - intros p.
    induction p.
    use subtypeEquality.
    + intro.
      apply isaprop_is_invertible_2cell.
    + reflexivity.
  - exact (pr2 (univalent_cat_idtoiso_2_1 f g)).
Defined.

Definition test
           {C D : univalent_cat}
           (F : pr1(pr1 C) ⟶ pr1(pr1 D))
  : adj_equivalence_of_precats F → @left_adjoint_equivalence univalent_cat _ _ (F ,, tt).
Proof.
  intros A.
  use tpair.
  - use tpair.
    + exact (right_adjoint A ,, tt).
    + split.
      * exact (unit_from_left_adjoint A ,, tt).
      * exact (counit_from_left_adjoint A ,, tt).
  - split ; split.
    * use subtypeEquality.
      ** intro.
         apply isapropunit.
      ** apply nat_trans_eq.
         *** apply D.
         *** intros x ; cbn.
             rewrite !id_left, !id_right.
             exact (pr1(pr2(pr2(pr1 A))) x).
    * use subtypeEquality.
      ** intro.
         apply isapropunit.
      ** apply nat_trans_eq.
         *** apply C.
         *** intros x ; cbn.
             rewrite !id_left, !id_right.
             exact (pr2(pr2(pr2(pr1 A))) x).
    * use tpair.
      ** refine (_ ,, tt).
         cbn.
         apply (pr2 (pr2 A)).
         Check (adjcounit (pr1 A)).

Definition cat_iso_to_adjequiv
           {C D : univalent_cat}
           (F :  ⟶ D)
  : is_catiso F.
  : catiso (pr1(pr1 C)) (pr1(pr1 D)) → adjoint_equivalence C D.
Proof.
  intros F.
  Check (rad_equivalence_of_precats (pr1(pr1 C)) (pr1(pr1 D)) (pr2 C) (pr1 F)).
  use equiv_to_adjequiv.
  - use tpair.
    + exact (pr1 F).
    + exact tt.
  - use tpair.
    + use tpair.
      * use tpair.
        ** exact (inv_catiso F).
        ** exact tt.
      * split.
        ** use tpair.
           *** use tpair.
               **** intros X ; cbn.
           *** exact tt.
        ** use tpair.
           *** admit.
           *** exact tt.
    + split.
      ** cbn.

Definition univalent_cat_is_univalent_2_0
  : is_univalent_2_0 univalent_cat.
Proof.
  intros C D.