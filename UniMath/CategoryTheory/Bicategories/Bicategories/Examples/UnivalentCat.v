Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.catiso.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.AdjointUnique.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.EquivToAdjequiv.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.FullSub.

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
  := fullsubbicat bicat_of_cats (λ C, is_univalent (pr1 C)).

Definition functor_univalent_cat
           (C D : univalent_cat)
  : pr1 (pr1 C) ⟶ pr1 (pr1 D) ≃ univalent_cat ⟦C,D⟧.
Proof.
  use tpair.
  - exact (λ F, F ,, tt).
  - use isweq_iso.
    + exact pr1.
    + reflexivity.
    + intros F.
      use subtypeEquality.
      * intro ; apply isapropunit.
      * reflexivity.
Defined.

Definition nat_trans_univalent_cat
           {C D : univalent_cat}
           (F G : univalent_cat ⟦C,D⟧)
  : nat_trans (pr1(pr1 F)) (pr1(pr1 G)) ≃ F ==> G.
Proof.
  use tpair.
  - exact (λ F, F ,, tt).
  - use isweq_iso.
    + exact pr1.
    + reflexivity.
    + intros η.
      use subtypeEquality.
      * intro ; apply isapropunit.
      * reflexivity.
Defined.

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
    + exact (nat_trans_univalent_cat f g).
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

Definition inv_catiso
           {C D : category}
           (F : catiso C D)
  : D ⟶ C.
Proof.
  use mk_functor.
  - use tpair.
    + exact (invweq (catiso_ob_weq F)).
    + intros X Y f ; cbn.
      refine (invmap
                (catiso_fully_faithful_weq F
                                           (invmap (catiso_ob_weq F) X)
                                           (invmap (catiso_ob_weq F) Y))
                _).
      exact ((idtoiso (homotweqinvweq (catiso_ob_weq F) X))
               · f
               · idtoiso (!(homotweqinvweq (catiso_ob_weq F) Y))).
  - split.
    + intro X ; cbn.
      rewrite id_right.
      etrans.
      {
        apply maponpaths.
        exact (!(maponpaths pr1
                            (idtoiso_concat D _ _ _
                                            (homotweqinvweq (catiso_ob_weq F) X)
                                            (! homotweqinvweq (catiso_ob_weq F) X)))).
      }
      rewrite pathsinv0r ; cbn.
      apply invmap_eq ; cbn.
      rewrite functor_id.
      reflexivity.
    + intros X Y Z f g ; cbn.
      apply invmap_eq ; cbn.
      rewrite functor_comp.
      pose (homotweqinvweq
              (catiso_fully_faithful_weq F
                                         (invmap (catiso_ob_weq F) X)
                                         (invmap (catiso_ob_weq F) Y))) as p.
      cbn in p.
      rewrite p ; clear p.
      pose (homotweqinvweq
              (catiso_fully_faithful_weq F
                                         (invmap (catiso_ob_weq F) Y)
                                         (invmap (catiso_ob_weq F) Z))) as p.
      cbn in p.
      rewrite p ; clear p.
      rewrite <- !assoc.
      repeat (apply (maponpaths (λ z, _ · (f · z)))).
      refine (!(id_left _) @ _).
      rewrite !assoc.
      repeat (apply (maponpaths (λ z, z · _))).
      rewrite idtoiso_inv.
      cbn.
      rewrite iso_after_iso_inv.
      reflexivity.
Defined.

Section CatIso_To_LeftAdjEquiv.
  Context {C D : univalent_cat}.
  Variable (F : pr1(pr1 C) ⟶ pr1(pr1 D))
           (HF : is_catiso F).

  Local Definition cat_iso_unit
    : nat_iso
        (functor_identity (pr1 (pr1 C)))
        (functor_composite F (inv_catiso (F ,, HF))).
  Proof.
    use tpair.
    - use mk_nat_trans.
      + intros X ; cbn.
        exact (pr1 (idtoiso (! homotinvweqweq (catiso_ob_weq (F ,, HF)) X))).
      + intros X Y f ; cbn.
        use (invmaponpathsweq (#F ,, _)).
        { apply HF. }
        cbn.
        refine (functor_comp _ _ _ @ !_).
        refine (functor_comp _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          match goal with [ |- _ (invmap ?FFF ?fff) = _ ] => apply (homotweqinvweq FFF fff) end.
        }
        rewrite !assoc.
        etrans.
        {
          refine (maponpaths (λ z, ((z · _) · _) · _) _).
          apply (!(base_paths _ _ (maponpaths_idtoiso _ _ F _ _ _))).
        }
        etrans.
        {
          refine (maponpaths (λ z, (z · _) · _) (!_)).
          apply (base_paths _ _ (idtoiso_concat _ _ _ _ _ _)).
        }
        rewrite maponpathsinv0.
        etrans.
        {
          refine (maponpaths (λ z, (pr1 (idtoiso (! z @ _)) · _) · _) _).
          match goal with [ |- _ (homotinvweqweq ?w _) = _] => apply (homotweqinvweqweq w) end.
        }
        rewrite pathsinv0l ; cbn.
        rewrite id_left.
        apply maponpaths.
        etrans.
        {
          repeat apply maponpaths.
          match goal with [ |- (homotweqinvweq ?w _) = _] => apply (! homotweqinvweqweq w Y) end.
        }
        rewrite <- maponpathsinv0.
        apply (base_paths _ _ (maponpaths_idtoiso _ _ F _ _ _)).
    - intros X.
      apply (idtoiso (! homotinvweqweq (catiso_ob_weq (F ,, HF)) X)).
  Defined.

  Local Definition cat_iso_counit
    : nat_iso
        (functor_composite (inv_catiso (F ,, HF)) F)
        (functor_identity (pr1 (pr1 D))).
  Proof.
    use tpair.
    - use mk_nat_trans.
      + intros X ; cbn.
        exact (pr1 (idtoiso (homotweqinvweq (catiso_ob_weq (F ,, HF)) X))).
      + intros X Y f ; cbn.
        etrans.
        {
          apply maponpaths_2.
          match goal with [ |- _ (invmap ?FFF ?fff) = _ ] => apply (homotweqinvweq FFF fff) end.
        }
        rewrite <- !assoc.
        etrans.
        {
          refine (maponpaths (λ z, _ · (_ · z)) _).
          apply (base_paths _ _ (!(idtoiso_concat _ _ _ _ _ _))).
        }
        rewrite pathsinv0l ; cbn.
        rewrite id_right.
        reflexivity.
    - intros X.
      apply (idtoiso (homotweqinvweq (catiso_ob_weq (F ,, HF)) X)).
  Defined.

  Definition is_catiso_to_left_adjoint_equivalence
    : @left_adjoint_equivalence univalent_cat _ _ (F ,, tt).
  Proof.
    use equiv_to_adjequiv.
    use tpair.
    - use tpair.
      + exact (inv_catiso (F ,, HF) ,, tt).
      + split.
        * refine (_ ,, tt).
          apply cat_iso_unit.
        * refine (_ ,, tt).
          apply cat_iso_counit.
    - split.
      + use tpair ; try split.
        * refine (_ ,, tt).
          apply (nat_iso_inv cat_iso_unit).
        * apply subtypeEquality.
          { intro ; apply isapropunit. }
          apply nat_trans_eq.
          { apply C. }
          intro X ; cbn.
          rewrite idtoiso_inv ; cbn ; unfold precomp_with.
          rewrite id_right.
          apply iso_after_iso_inv.
        * apply subtypeEquality.
          { intro ; apply isapropunit. }
          apply nat_trans_eq.
          { apply C. }
          intro X ; cbn.
          rewrite idtoiso_inv ; cbn ; unfold precomp_with.
          rewrite id_right.
          apply iso_inv_after_iso.
      + use tpair ; try split.
        * refine (_ ,, tt).
          apply (nat_iso_inv cat_iso_counit).
        * apply subtypeEquality.
          { intro ; apply isapropunit. }
          apply nat_trans_eq.
          { apply D. }
          intro X ; cbn.
          apply iso_inv_after_iso.
        * apply subtypeEquality.
          { intro ; apply isapropunit. }
          apply nat_trans_eq.
          { apply D. }
          intro X ; cbn.
          apply iso_after_iso_inv.
  Qed.
End CatIso_To_LeftAdjEquiv.

Definition left_adjoint_equivalence_to_is_catiso
           {C D : univalent_cat}
           (L : pr1(pr1 C) ⟶ pr1(pr1 D))
  : @left_adjoint_equivalence univalent_cat _ _ (L ,, tt) → is_catiso L.
Proof.
  intros HF.
  pose (R := pr1 (left_adjoint_right_adjoint HF)).
  pose (η := pr1 (left_adjoint_unit HF)).
  pose (ηinv := pr1 ((left_equivalence_unit_iso HF)^-1)).
  pose (ε := pr1 (left_adjoint_counit HF)).
  pose (εinv := pr1 ((left_equivalence_counit_iso HF)^-1)).
  assert (ηηinv := nat_trans_eq_pointwise
                     (base_paths _ _
                                 (pr1(pr2(pr2 (left_equivalence_unit_iso HF)))))).
  assert (ηinvη := nat_trans_eq_pointwise
                     (base_paths _ _
                                 (pr2(pr2(pr2 (left_equivalence_unit_iso HF)))))).
  assert (εεinv := nat_trans_eq_pointwise
                     (base_paths _ _
                                 (pr1(pr2(pr2 (left_equivalence_counit_iso HF)))))).
  assert (εinvε := nat_trans_eq_pointwise
                     (base_paths _ _
                                 (pr2(pr2(pr2 (left_equivalence_counit_iso HF)))))).
  assert (LηεL := nat_trans_eq_pointwise (base_paths _ _ (internal_triangle1 HF))).
  assert (ηRRε := nat_trans_eq_pointwise (base_paths _ _ (internal_triangle2 HF))).
  cbn in *.
  use tpair.
  - intros X Y.
    use isweq_iso.
    + intros f.
      exact (η X · #R f · ηinv Y).
    + intros f ; cbn.
      etrans.
      {
        apply maponpaths_2.
        exact (!(pr2 η X Y f)).
      }
      rewrite <- assoc.
      refine (maponpaths (λ z, _ · z) (ηηinv Y) @ _).
      apply id_right.
    + intros f ; cbn.
      rewrite !functor_comp.
      assert (#L (ηinv Y) = ε (L Y)) as X0.
      {
        specialize (LηεL Y).
        rewrite !id_left, !id_right in LηεL.
        refine (!(id_right _) @ _).
        refine (maponpaths (λ z, _ · z) (!LηεL) @ _).
        rewrite assoc.
        rewrite <- functor_comp.
        refine (maponpaths (λ z, # L z · _) (ηinvη Y) @ _).
        rewrite functor_id, id_left.
        reflexivity.
      }
      etrans.
      {
        apply maponpaths.
        exact X0.
      }
      rewrite <- assoc.
      refine (maponpaths _ (nat_trans_ax ε (L X) (L Y) f) @ _).
      rewrite assoc.
      specialize (LηεL X).
      rewrite !id_left, !id_right in LηεL.
      etrans.
      {
        apply maponpaths_2.
        exact LηεL.
      }
      apply id_left.
  - cbn.
    use isweq_iso.
    + apply R.
    + intros X ; cbn.
      apply isotoid.
      * apply C.
      * use tpair.
        ** exact (ηinv X).
        ** use is_iso_qinv ; try split.
           *** exact (η X).
           *** exact (ηinvη X).
           *** exact (ηηinv X).
    + intros Y ; cbn.
      apply isotoid.
      * apply D.
      * use tpair.
        ** exact (ε Y).
        ** use is_iso_qinv ; try split.
           *** exact (εinv Y).
           *** exact (εεinv Y).
           *** exact (εinvε Y).
Qed.

Definition is_catiso_left_adjoint_equivalence
           {C D : univalent_cat}
           (F : pr1(pr1 C) ⟶ pr1(pr1 D))
  : is_catiso F ≃ @left_adjoint_equivalence univalent_cat _ _ (F ,, tt).
Proof.
  use weqimplimpl.
  - exact (is_catiso_to_left_adjoint_equivalence F).
  - exact (left_adjoint_equivalence_to_is_catiso F).
  - apply isaprop_is_catiso.
  - apply invproofirrelevance.
    intros A₁ A₂.
    apply unique_internal_adjoint_equivalence.
    apply univalent_cat_is_univalent_2_1.
Defined.

Definition cat_iso_to_adjequiv
           (C D : univalent_cat)
  : catiso (pr1(pr1 C)) (pr1(pr1 D)) ≃ adjoint_equivalence C D.
Proof.
  use weqbandf.
  - exact (functor_univalent_cat C D).
  - intros.
    apply is_catiso_left_adjoint_equivalence.
Defined.

Definition idtoiso_2_0_univalent_cat
           (C D : univalent_cat)
  : C = D ≃ adjoint_equivalence C D
  := ((cat_iso_to_adjequiv C D)
        ∘ cat_equiv_to_catiso_weq _ _
        ∘ weq_cat_eq_cat_equiv _ _
        ∘ cat_eq_1_to_cat_eq_2 _ _ (pr2 (pr2 D))
        ∘ cat_path_to_cat_eq_1 _ _
        ∘ path_precat _ _
        ∘ path_univalent_cat _ _)%weq.

Definition univalent_cat_is_univalent_2_0
  : is_univalent_2_0 univalent_cat.
Proof.
  intros C D.
  use isweqhomot.
  - exact (idtoiso_2_0_univalent_cat C D).
  - intro p.
    induction p.
    apply path_internal_adjoint_equivalence.
    + apply univalent_cat_is_univalent_2_1.
    + reflexivity.
  - apply (idtoiso_2_0_univalent_cat C D).
Defined.
