Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.

Require Import UniMath.CategoryTheory.Monoidal.RezkCompletion.CategoriesLemmas.

Local Open Scope cat.

Local Notation "C ⊠ D" := (category_binproduct C D) (at level 38).

Local Notation "( c , d )" := (make_catbinprod c d).
Local Notation "( f #, g )" := (catbinprodmor f g).

Section TensorFunctorCategory.

  Context {C D : category}
          (TC : functor (C ⊠ C) C)
          (TD : functor (D ⊠ D) D).

  Notation "X ⊗_C Y" := (TC (X , Y)) (at level 31).
  Notation "f #⊗_C g" := (# TC (f #, g)) (at level 31).
  Notation "X ⊗_D Y" := (TD (X , Y)) (at level 31).
  Notation "f #⊗_D g" := (# TD (f #, g)) (at level 31).

  Definition functor_tensor_map_dom (F : functor C D)
    : functor (C ⊠ C) D
    := functor_composite (pair_functor F F) TD.

  Definition functor_tensor_map_codom (F : functor C D)
    : functor (C ⊠ C) D
    := functor_composite TC F.

  Definition functor_tensor (F : functor C D)
    : UU := nat_trans (functor_tensor_map_dom F) (functor_tensor_map_codom F).
  Identity Coercion functor_tensor_c : functor_tensor >-> nat_trans.

  Definition nat_trans_tensor {F G : functor C D}
             (FF : functor_tensor F) (GG : functor_tensor G)
             (α : nat_trans F G) : UU
    := ∏ x y : C, (α x #⊗_D α y) · GG (x, y)
                  = FF (x, y) · α (x ⊗_C y).

  Lemma isaprop_nat_trans_tensor {F G : functor C D}
             (FF : functor_tensor F) (GG : functor_tensor G)
             (α : nat_trans F G)
    : isaprop (nat_trans_tensor FF GG α).
  Proof.
    do 2 (apply impred_isaprop ; intro) ; apply homset_property.
  Qed.

  Definition nat_trans_tensor_id
             {F : functor C D} (FF : functor_tensor F)
    : nat_trans_tensor FF FF (nat_trans_id F).
  Proof.
    intros x y.
    simpl.
    rewrite (functor_id TD).
    exact (id_left _ @ ! id_right _).
  Qed.

  Definition nat_trans_tensor_comp
             {F G H : functor C D}
             (FF : functor_tensor F) (GG : functor_tensor G) (HH : functor_tensor H)
             {α : nat_trans F G} {β : nat_trans G H}
             (αα : nat_trans_tensor FF GG α)
             (ββ : nat_trans_tensor GG HH β)
    : nat_trans_tensor FF HH (nat_trans_comp _ _ _ α β).
  Proof.
    intros x y.
    simpl.
    etrans. {
      apply maponpaths_2.
      exact (functor_comp TD (α x #, α y) (β x #, β y)).
    }
    rewrite assoc'.
    etrans. {
      apply maponpaths.
      exact (ββ x y).
    }
    do 2 rewrite assoc.
    apply maponpaths_2.
    apply αα.
  Qed.

  Definition functor_tensor_disp_cat_ob_mor
    : disp_cat_ob_mor [C,D].
  Proof.
    exists (λ F, functor_tensor F).
    exact (λ F G FF GG α, nat_trans_tensor FF GG α).
  Defined.

  Definition functor_tensor_disp_cat_id_comp
    : disp_cat_id_comp _ functor_tensor_disp_cat_ob_mor.
  Proof.
    split ; intro ; intros ; [apply nat_trans_tensor_id | use nat_trans_tensor_comp ; assumption ].
  Qed.

  Definition functor_tensor_disp_cat_data
    : disp_cat_data [C,D]
    := _ ,, functor_tensor_disp_cat_id_comp.

  Definition functor_tensor_disp_cat_axioms
    : disp_cat_axioms _ functor_tensor_disp_cat_data.
  Proof.
    repeat split ; intro ; intros ; try (apply isaprop_nat_trans_tensor).
    use isasetaprop.
    apply isaprop_nat_trans_tensor.
  Qed.

  Definition functor_tensor_disp_cat : disp_cat [C,D]
    := _ ,, functor_tensor_disp_cat_axioms.

  Definition functor_tensor_cat : category
    := total_category functor_tensor_disp_cat.

End TensorFunctorCategory.

Section TensorFunctorCategoryUnivalence.

  Context {C D : category}
          (TC : functor (C ⊠ C) C)
          (TD : functor (D ⊠ D) D).

  Lemma isaset_functor_tensor_disp_cat (F : functor C D)
    :  isaset (functor_tensor_disp_cat TC TD F).
  Proof.
    apply isaset_nat_trans.
    { apply homset_property. }
  Qed.

  Lemma functor_tensor_disp_cat_is_univalent
    : is_univalent_disp (functor_tensor_disp_cat TC TD).
  Proof.
    apply is_univalent_disp_from_fibers.
    intros F pt1 pt2.
    use isweqimplimpl.
    - intro i.
      use total2_paths_f.
      + apply funextsec ; intro.
        set (ix := (pr1 i) (pr1 x) (pr2 x)).
        cbn in ix.
        rewrite binprod_id in ix.
        rewrite (functor_id TD) in ix.
        rewrite id_right in ix.
        rewrite id_left in ix.
        exact (! ix).
      + do 2 (apply funextsec ; intro).
        repeat (apply impred_isaprop ; intro).
        apply homset_property.
    - apply isaset_functor_tensor_disp_cat.
    - apply isaproptotal2.
      + intro ; apply Isos.isaprop_is_z_iso_disp.
      + do 4 intro ; apply isaprop_nat_trans_tensor.
  Qed.

End TensorFunctorCategoryUnivalence.

Section TensorFunctorProperties.

  Lemma functor_tensor_composition_is_nat_trans
        {C D E : category}
        {TC : functor (C ⊠ C) C}
        {TD : functor (D ⊠ D) D}
        {TE : functor (E ⊠ E) E}
        {F : functor C D} {G : functor D E}
        (FF : functor_tensor TC TD F) (GG : functor_tensor TD TE G)
    : is_nat_trans
        (functor_tensor_map_dom TE (F ∙ G))
        (functor_tensor_map_codom TC (F ∙ G))
        (λ cc : ∑ _ : C, C, GG (F (pr1 cc), F (pr2 cc)) · # G (FF cc)).
  Proof.
    intros cc1 cc2 f.
    etrans. {
      rewrite assoc.
      apply maponpaths_2.
      exact (pr2 GG ((pair_functor F F) cc1) (pair_functor F F cc2) (# (pair_functor F F) f)).
    }

    etrans.
    2: {
      rewrite assoc'.
      simpl.
      rewrite <- (functor_comp G).
      do 2 apply maponpaths.
      exact (pr2 FF cc1 cc2 f).
    }
    rewrite assoc'.
    apply maponpaths.
    apply (! functor_comp G _ _).
  Qed.

  Definition functor_tensor_composition
             {C D E : category}
             {TC : functor (C ⊠ C) C}
             {TD : functor (D ⊠ D) D}
             {TE : functor (E ⊠ E) E}
             {F : functor C D} {G : functor D E}
             (FF : functor_tensor TC TD F) (GG : functor_tensor TD TE G)
    : functor_tensor TC TE (functor_composite F G).
  Proof.
    exists (λ cc, GG (F (pr1 cc) , F (pr2 cc)) · #G (FF cc)).
    apply functor_tensor_composition_is_nat_trans.
  Defined.

  (* A characterization of the tensor property of monoidal natural transformations
     in terms of equality/isos of functors/natural transformations. *)
  Context {C D E : category}
          {TC : functor (C ⊠ C) C}
          {TD : functor (D ⊠ D) D}.

  Notation "X ⊗_C Y" := (TC (X , Y)) (at level 31).
  Notation "f #⊗_C g" := (# TC (f #, g)) (at level 31).
  Notation "X ⊗_D Y" := (TD (X , Y)) (at level 31).
  Notation "f #⊗_D g" := (# TD (f #, g)) (at level 31).

  Context {F G : functor C D}
          (FF : functor_tensor TC TD F) (GG : functor_tensor TC TD G)
          (α : nat_trans F G).

  Lemma nat_trans_tensor_ntrans1_is_nat_trans
    :  is_nat_trans
         (functor_tensor_map_dom TD F)
         (functor_tensor_map_codom TC G)
         (λ cc : _, # TD (α (pr1 cc) #, α (pr2 cc)) · GG cc).
  Proof.
    intros cc1 cc2 ff.
    simpl.
    rewrite assoc.
    rewrite <- (functor_comp TD).
    rewrite <- binprod_comp.
    do 2 rewrite (pr2 α).
    rewrite binprod_comp.
    rewrite (functor_comp TD).
    do 2 rewrite assoc'.
    apply maponpaths.
    apply (pr2 GG).
  Qed.

  Definition nat_trans_tensor_ntrans1
    : nat_trans (functor_tensor_map_dom TD F) (functor_tensor_map_codom TC G)
    := _ ,, nat_trans_tensor_ntrans1_is_nat_trans.

  Definition nat_trans_tensor_ntrans2_is_nat_trans
    : is_nat_trans
        (functor_tensor_map_dom TD F)
        (functor_tensor_map_codom TC G)
        (λ cc : C ⊠ C, FF cc · α (pr1 cc ⊗_C pr2 cc)).
  Proof.
    intros cc1 cc2 ff.
    simpl.
    set (t := pr2 FF cc1 cc2).
    simpl in t.
    rewrite assoc.
    rewrite t.
    do 2 rewrite assoc'.
    apply maponpaths.
    apply (pr2 α).
  Qed.

  Definition nat_trans_tensor_ntrans2
    : nat_trans (functor_tensor_map_dom TD F) (functor_tensor_map_codom TC G)
    := _ ,, nat_trans_tensor_ntrans2_is_nat_trans.

  Definition nat_trans_tensor' : UU
    := nat_trans_tensor_ntrans1 = nat_trans_tensor_ntrans2.

  Lemma nat_trans_tensor_to_characterization
        (p : nat_trans_tensor')
    : nat_trans_tensor TC TD FF GG α.
  Proof.
    intros x y.
    exact (toforallpaths _ _ _ (base_paths _ _ p) (x,y)).
  Qed.

  Lemma nat_trans_tensor_from_characterization
        (p : nat_trans_tensor TC TD FF GG α)
    : nat_trans_tensor'.
  Proof.
    use nat_trans_eq.
    { apply homset_property. }
    exact (λ cc, p (pr1 cc) (pr2 cc)).
  Qed.

End TensorFunctorProperties.

Section UnitFunctorCategory.

  Context {C D : category} (IC : C) (ID : D).

  Definition functor_unit (F : functor C D) : UU
    := D⟦ID, pr1 F IC⟧.

  Definition nat_trans_unit
             {F G : functor C D} (FF : functor_unit F) (GG : functor_unit G)
             (α : nat_trans F G) : UU
    := FF · α IC = GG.

  Definition functor_unit_disp_cat_ob_mor
    : disp_cat_ob_mor [C,D].
  Proof.
    exists (λ F, functor_unit F).
    exact (λ F G FF GG α, nat_trans_unit FF GG α).
  Defined.

  Definition nat_trans_unit_id
             {F : functor C D} (FF : functor_unit F)
    : nat_trans_unit FF FF (nat_trans_id F).
  Proof.
    apply id_right.
  Qed.

  Definition nat_trans_unit_comp
             {F G H : functor C D}
             (FF : functor_unit F) (GG : functor_unit G) (HH : functor_unit H)
             {α : nat_trans F G} {β : nat_trans G H}
             (αα : nat_trans_unit FF GG α)
             (ββ : nat_trans_unit GG HH β)
    : nat_trans_unit FF HH (nat_trans_comp _ _ _ α β).
  Proof.
    etrans. { apply assoc. }
    etrans. { apply maponpaths_2 ; exact αα. }
    exact ββ.
  Qed.

  Definition functor_unit_disp_cat_id_comp
    : disp_cat_id_comp _ functor_unit_disp_cat_ob_mor.
  Proof.
    split ; intro ; intros ; [apply nat_trans_unit_id | use nat_trans_unit_comp ; assumption ].
  Qed.

  Definition functor_unit_disp_cat_data
    : disp_cat_data [C,D]
    := _ ,, functor_unit_disp_cat_id_comp.

  Definition functor_unit_disp_cat_axioms
    : disp_cat_axioms _ functor_unit_disp_cat_data.
  Proof.
    repeat split ; intro ; intros ; try (apply homset_property).
    use isasetaprop.
    apply homset_property.
  Qed.

  Definition functor_unit_disp_cat : disp_cat [C,D]
    := _ ,, functor_unit_disp_cat_axioms.

  Definition functor_unit_cat : category
    := total_category functor_unit_disp_cat.

End UnitFunctorCategory.

Section UnitFunctorCategoryUnivalence.

  Context {C D : category} (IC : C) (ID : D).

  Lemma functor_unit_disp_cat_is_univalent
    : is_univalent_disp (functor_unit_disp_cat IC ID).
  Proof.
    apply is_univalent_disp_from_fibers.
    intros F pt1 pt2.
    use isweqimplimpl.
    - intro i.
      refine (_ @ pr1 i).
      apply (! id_right _).
    - apply homset_property.
    - apply isaproptotal2.
      + intro ; apply Isos.isaprop_is_z_iso_disp.
      + do 4 intro ; apply homset_property.
  Qed.

End UnitFunctorCategoryUnivalence.

Section UnitFunctorProperties.

  Definition functor_unit_composition
             {C D E : category}
             {IC : C} {ID : D} {IE : E}
             {F : functor C D} {G : functor D E}
             (FF : functor_unit IC ID F) (GG : functor_unit ID IE G)
    : functor_unit IC IE (functor_composite F G)
    := GG · #G FF.

End UnitFunctorProperties.


Section FunctorTensorUnit.

  Context {C D : category}
          (TC : functor (C ⊠ C) C) (TD : functor (D ⊠ D) D)
          (IC : C) (ID : D).

  Definition functor_tensorunit_disp_cat
    : disp_cat [C,D]
    := dirprod_disp_cat (functor_tensor_disp_cat TC TD) (functor_unit_disp_cat IC ID).

  Lemma functor_tensorunit_disp_cat_is_univalent
    : is_univalent_disp functor_tensorunit_disp_cat.
  Proof.
    apply dirprod_disp_cat_is_univalent.
    - apply functor_tensor_disp_cat_is_univalent.
    - apply functor_unit_disp_cat_is_univalent.
  Qed.

  Definition functor_tensorunit_cat
    : category := total_category functor_tensorunit_disp_cat.

End FunctorTensorUnit.

Section TensorUnitFunctorProperties.

  Context {C D E : category}
          {TC : functor (C ⊠ C) C} {TD : functor (D ⊠ D) D}
          {TE : functor (E ⊠ E) E}
          {IC : C} {ID : D} {IE : E}.

  Definition functor_tensorunit_composition
             {F : functor C D} {G : functor D E}
             (FF : functor_tensorunit_disp_cat TC TD IC ID F)
             (GG : functor_tensorunit_disp_cat TD TE ID IE G)
    : functor_tensorunit_disp_cat TC TE IC IE (functor_composite F G).
  Proof.
    exists (functor_tensor_composition (pr1 FF) (pr1 GG)).
    exact (functor_unit_composition (pr2 FF) (pr2 GG)).
  Defined.

End TensorUnitFunctorProperties.

Section MonoidalFunctorCategory.

  Context {C D : category}
          {TC : functor (C ⊠ C) C} {TD : functor (D ⊠ D) D}
          {IC : C} {ID : D}
          (luC : left_unitor TC IC) (luD : left_unitor TD ID)
          (ruC : right_unitor TC IC) (ruD : right_unitor TD ID)
          (αC : associator TC) (αD : associator TD).

  Notation "X ⊗_C Y" := (TC (X , Y)) (at level 31).
  Notation "f #⊗_C g" := (# TC (f #, g)) (at level 31).
  Notation "X ⊗_D Y" := (TD (X , Y)) (at level 31).
  Notation "f #⊗_D g" := (# TD (f #, g)) (at level 31).

  Definition functor_lu_disp_cat : disp_cat (functor_tensorunit_cat TC TD IC ID).
  Proof.
    use disp_full_sub.
    intros [F [FT FU]].
    exact (∏ x : C, luD (pr1 F x) = FU #⊗_D (id (pr1 F x)) · (pr1 FT) (IC, x) · #(pr1 F) (luC x)).
  Defined.

  Definition functor_ru_disp_cat : disp_cat (functor_tensorunit_cat TC TD IC ID).
  Proof.
    use disp_full_sub.
    intros [F [FT FU]].
    exact (∏ x : C, ruD (pr1 F x) =  (id (pr1 F x)) #⊗_D FU · (pr1 FT) (x, IC) · #(pr1 F) (ruC x)).
  Defined.

  Definition functor_ass_disp_cat : disp_cat (functor_tensorunit_cat TC TD IC ID).
  Proof.
    use disp_full_sub.
    intros [F [FT FU]].

    exact (∏ (x y z : C),
            pr1 FT (x, y) #⊗_D id (pr1 F(z)) · pr1 FT (x ⊗_C y, z) · #(pr1 F) (αC ((x, y), z))
            =
              αD ((pr1 F x, pr1 F y), pr1 F z) · id (pr1 F x) #⊗_D pr1 FT (y, z) · pr1 FT (x, y ⊗_C z)).
  Defined.

  Lemma functor_lu_disp_cat_is_univalent
    : is_univalent_disp functor_lu_disp_cat.
  Proof.
    apply disp_full_sub_univalent.
    intro.
    apply impred_isaprop ; intro ; apply homset_property.
  Qed.

  Lemma functor_ru_disp_cat_is_univalent
    : is_univalent_disp functor_ru_disp_cat.
  Proof.
    apply disp_full_sub_univalent.
    intro.
    apply impred_isaprop ; intro ; apply homset_property.
  Qed.

  Lemma functor_ass_disp_cat_is_univalent
    : is_univalent_disp functor_ass_disp_cat.
  Proof.
    apply disp_full_sub_univalent.
    intro.
    do 3 (apply impred_isaprop ; intro) ; apply homset_property.
  Qed.

  Definition functor_monoidal_disp_cat
    : disp_cat (functor_tensorunit_cat TC TD IC ID)
    := dirprod_disp_cat
         (dirprod_disp_cat functor_lu_disp_cat functor_ru_disp_cat)
         functor_ass_disp_cat.

  Definition functor_monoidal_cat
    : category
    := total_category functor_monoidal_disp_cat.

End MonoidalFunctorCategory.

Section FunctorMonoidalProperties.

  Context {C D E : category}
          {TC : functor (C ⊠ C) C} {TD : functor (D ⊠ D) D}
          {TE : functor (E ⊠ E) E}
          {IC : C} {ID : D} {IE : E}.

  Notation "X ⊗_C Y" := (TC (X , Y)) (at level 31).
  Notation "f #⊗_C g" := (# TC (f #, g)) (at level 31).
  Notation "X ⊗_D Y" := (TD (X , Y)) (at level 31).
  Notation "f #⊗_D g" := (# TD (f #, g)) (at level 31).
  Notation "X ⊗_E Y" := (TE (X , Y)) (at level 31).
  Notation "f #⊗_E g" := (# TE (f #, g)) (at level 31).

  Definition functor_lu_composition
             {luC : left_unitor TC IC} {luD : left_unitor TD ID} {luE : left_unitor TE IE}
             {F : functor C D} {G : functor D E}
             {FF : functor_tensorunit_disp_cat TC TD IC ID F}
             {GG : functor_tensorunit_disp_cat TD TE ID IE G}
             (FFF : functor_lu_disp_cat luC luD (_,,FF))
             (GGG : functor_lu_disp_cat luD luE (_,,GG))
    : functor_lu_disp_cat luC luE (_,, functor_tensorunit_composition FF GG).
  Proof.
    intro x.
    refine (GGG (F x) @ _).
  Admitted.

  Definition functor_ru_composition
             {ruC : right_unitor TC IC} {ruD : right_unitor TD ID} {ruE : right_unitor TE IE}
             {F : functor C D} {G : functor D E}
             {FF : functor_tensorunit_disp_cat TC TD IC ID F}
             {GG : functor_tensorunit_disp_cat TD TE ID IE G}
             (FFF : functor_ru_disp_cat ruC ruD (_,,FF))
             (GGG : functor_ru_disp_cat ruD ruE (_,,GG))
    : functor_ru_disp_cat ruC ruE (_,, functor_tensorunit_composition FF GG).
  Proof.
    intro x.
    refine (GGG (F x) @ _).
    unfold functor_tensorunit_composition.
    unfold functor_unit_composition.
    unfold functor_tensor_composition.
    simpl.


  Admitted.

  Definition functor_ass_composition
             {αC : associator TC} {αD : associator TD} {αE : associator TE}
             {F : functor C D} {G : functor D E}
             {FF : functor_tensorunit_disp_cat TC TD IC ID F}
             {GG : functor_tensorunit_disp_cat TD TE ID IE G}
             (FFF : functor_ass_disp_cat αC αD (_,,FF))
             (GGG : functor_ass_disp_cat αD αE (_,,GG))
    : functor_ass_disp_cat αC αE (_,, functor_tensorunit_composition FF GG).
  Proof.
    intros x y z.
    simpl.

  Admitted.

End FunctorMonoidalProperties.

Section AssociatorMonoidalProperty.

  Definition pair_nat_trans
             {C1 C2 D1 D2 : category}
             {F1 G1 : functor C1 D1}
             {F2 G2 : functor C2 D2}
             (α : nat_trans F1 G1)
             (β : nat_trans F2 G2)
    : nat_trans (pair_functor F1 F2) (pair_functor G1 G2).
  Proof.
    use make_nat_trans.
    - intro x.
      use catbinprodmor.
      + exact (α (pr1 x)).
      + exact (β (pr2 x)).
    - abstract (intro ; intros ; use total2_paths_f ;
                   [ apply (pr2 α) | rewrite transportf_const ; apply (pr2 β) ]
               ).
  Defined.

  Definition pair_nat_z_iso
             {C1 C2 D1 D2 : category}
             {F1 G1 : functor C1 D1}
             {F2 G2 : functor C2 D2}
             (α : nat_z_iso F1 G1)
             (β : nat_z_iso F2 G2)
    : nat_z_iso (pair_functor F1 F2) (pair_functor G1 G2).
  Proof.
    use make_nat_z_iso.
    { exact (pair_nat_trans α β). }
    intro x.
    use tpair.
    - use catbinprodmor.
      + exact (pr1 (pr2 α (pr1 x))).
      + exact (pr1 (pr2 β (pr2 x))).
    - abstract (
          split ; (use total2_paths_f ;
                   [ apply (pr2 α) | rewrite transportf_const ; apply (pr2 β) ]
                  )
        ).
  Defined.

  Require Import UniMath.CategoryTheory.whiskering.

  Lemma unassoc_commutes
        {C D : category} (F : functor C D)
    : nat_z_iso ((pair_functor (pair_functor F F) F) ∙ (precategory_binproduct_unassoc D D D))
                ((precategory_binproduct_unassoc C C C) ∙ (pair_functor F (pair_functor F F))).
  Proof.
    use make_nat_z_iso.
    - use make_nat_trans.
      + intro ; use catbinprodmor ; apply identity.
      + intro ; intros.
        use total2_paths_f.
        * exact (id_right _ @ ! id_left _).
        * abstract (rewrite transportf_const ; exact (id_right _ @ ! id_left _)).
    - intro.
      use tpair.
      * use catbinprodmor ; apply identity.
      * abstract (split ; (use total2_paths_f ; [ apply id_right | rewrite transportf_const ; apply id_right ])).
  Defined.

  Lemma assoc_right_commutes_with_triple_pairing
        {C D : category}
        (F : functor C D)
        {TC : functor (C ⊠ C) C}
        {TD : functor (D ⊠ D) D}
        {FF : functor_tensor TC TD F}
        (FF_iso : is_nat_z_iso FF)
    : nat_z_iso
        (pair_functor (pair_functor F F) F ∙ assoc_right TD) (assoc_right TC ∙ F).
  Proof.
    (* This commuting diagram can be split in 3 commuting diagrams stacked together *)
    (* Step 1: The top commuting diagram is unassoc_commutes *)
    use nat_z_iso_comp.
    2: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    2: {
      use CategoriesLemmas.post_whisker_nat_z_iso.
      2: apply unassoc_commutes.
    }
    use nat_z_iso_comp.
    2: apply (nat_z_iso_inv (CategoriesLemmas.nat_z_iso_functor_comp_assoc _ _ _)).
    use nat_z_iso_comp.
    3: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    apply CategoriesLemmas.pre_whisker_nat_z_iso.

    (* Step 2: The lowest commuting diagram is the tensor preserving commuting one *)
    use nat_z_iso_comp.
    3: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    3: {
      apply CategoriesLemmas.pre_whisker_nat_z_iso.
      apply (FF ,, FF_iso).
    }

    use nat_z_iso_comp.
    3: apply (nat_z_iso_inv (CategoriesLemmas.nat_z_iso_functor_comp_assoc _ _ _)).
    use nat_z_iso_comp.
    2: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    apply CategoriesLemmas.post_whisker_nat_z_iso.

    (* Step 3: The middle commuting square is the tensor preserving commuting one
               but tensored with the identity functor on the left *)

    use CategoriesLemmas.product_of_commuting_squares.
    { apply (make_nat_z_iso _ _ _ (is_nat_z_iso_nat_trans_id F)). }
    apply (FF ,, FF_iso).
  Defined.

  Lemma pair_functor_composite
        {C1 C2 C3 D1 D2 D3 : category}
        (F1 : functor C1 C2)
        (G1 : functor D1 D2)
        (F2 : functor C2 C3)
        (G2 : functor D2 D3)
    : nat_z_iso
        (functor_composite (pair_functor F1 G1) (pair_functor F2 G2))
        (pair_functor (functor_composite F1 F2) (functor_composite G1 G2)).
  Proof.
    use make_nat_z_iso.
    { apply nat_trans_id. }
    intro.
    use tpair.
    - use catbinprodmor ; apply identity.
    - split ; apply id_right.
  Defined.

  Lemma assoc_left_commutes_with_triple_pairing
        {C D : category}
        (F : functor C D)
        {TC : functor (C ⊠ C) C}
        {TD : functor (D ⊠ D) D}
        {FF : functor_tensor TC TD F}
        (FF_iso : is_nat_z_iso FF)
    :  nat_z_iso ((pair_functor (pair_functor F F) F) ∙ assoc_left TD) (assoc_left TC ∙ F).
  Proof.
    unfold assoc_left.
    use nat_z_iso_comp.
    2: apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
    use nat_z_iso_comp.
    2: {
      use CategoriesLemmas.post_whisker_nat_z_iso.
      2: apply pair_functor_composite.
    }
    use nat_z_iso_comp.
    2: {
      use CategoriesLemmas.post_whisker_nat_z_iso.
      2: {
        use pair_nat_z_iso.
        3: {
          exists FF.
          apply FF_iso.
        }
        2: {
          exists (nat_trans_id _).
          apply is_nat_z_iso_nat_trans_id.
        }
      }
    }
    unfold functor_tensor_map_codom.
    use nat_z_iso_comp.
    2: {
      use CategoriesLemmas.post_whisker_nat_z_iso.
      2: {
        use pair_nat_z_iso.
        3: {
          exists (nat_trans_id _).
          apply is_nat_z_iso_nat_trans_id.
        }
        2: apply CategoriesLemmas.functor_commutes_with_id.
      }
    }

    use nat_z_iso_comp.
    2: {
      use CategoriesLemmas.post_whisker_nat_z_iso.
      2: apply (nat_z_iso_inv (pair_functor_composite _ _ _ _)).
    }
    use nat_z_iso_comp.
    2: apply (nat_z_iso_inv (CategoriesLemmas.nat_z_iso_functor_comp_assoc _ _ _)).
    use nat_z_iso_comp.
    2: {
      use CategoriesLemmas.pre_whisker_nat_z_iso.
      2: {
        exists FF.
        apply FF_iso.
      }
    }
    apply CategoriesLemmas.nat_z_iso_functor_comp_assoc.
  Defined.

  Context {C D : category}
          {TC : functor (C ⊠ C) C} {TD : functor (D ⊠ D) D}
          {IC : C} {ID : D}.

  Notation "X ⊗_C Y" := (TC (X , Y)) (at level 31).
  Notation "f #⊗_C g" := (# TC (f #, g)) (at level 31).
  Notation "X ⊗_D Y" := (TD (X , Y)) (at level 31).
  Notation "f #⊗_D g" := (# TD (f #, g)) (at level 31).


  Definition functor_ass_ntrans1
             (αC : associator TC) (αD : associator TD)
             {F : functor C D}
             {FF : functor_tensorunit_disp_cat TC TD IC ID F}
             (FF_iso : is_nat_z_iso (pr11 FF))
    : nat_trans
        (functor_composite
           (pair_functor (pair_functor F F) F)
           (functor_composite (pair_functor TD (functor_identity _)) TD)
        )
        (functor_composite (assoc_right TC) F).
  Proof.

    set (pF := pair_functor F F).
    set (pFF := pair_functor pF F).

    use nat_trans_comp.
    2: { exact (pre_whisker pFF αD). }
    use assoc_right_commutes_with_triple_pairing.
    - exact (pr1 FF).
    - exact FF_iso.
  Defined.

  Definition functor_ass_ntrans2
             (αC : associator TC) (αD : associator TD)
             {F : functor C D}
             {FF : functor_tensorunit_disp_cat TC TD IC ID F}
             (FF_iso : is_nat_z_iso (pr11 FF))
    : nat_trans
        (functor_composite
           (pair_functor (pair_functor F F) F)
           (functor_composite (pair_functor TD (functor_identity _)) TD)
        )
        (functor_composite (assoc_right TC) F).
  Proof.

    use nat_trans_comp.
    3: exact (post_whisker αC F).
    use assoc_left_commutes_with_triple_pairing.
    - exact (pr1 FF).
    - exact FF_iso.
  Defined.

  Definition functor_nat_trans_preserves
             (αC : associator TC) (αD : associator TD)
             {F : functor C D}
             {FF : functor_tensorunit_disp_cat TC TD IC ID F}
             (FF_iso : is_nat_z_iso (pr11 FF))
    : UU := functor_ass_ntrans2 αC αD FF_iso = functor_ass_ntrans1 αC αD FF_iso.

  Definition functor_ass_to_nat_trans_ass
             {αC : associator TC} {αD : associator TD}
             {F : functor C D}
             {FF : functor_tensorunit_disp_cat TC TD IC ID F}
             (FF_iso : is_nat_z_iso (pr11 FF))
             (FFF : functor_ass_disp_cat αC αD (_,,FF))
    : functor_nat_trans_preserves αC αD FF_iso.
  Proof.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    set (p := FFF (pr11 x) (pr21 x) (pr2 x)).
    simpl.
    rewrite assoc.
    rewrite ! (functor_id TD).
    rewrite ! id_left.
    rewrite ! id_right.
    refine (p @ _).
    apply assoc'.
  Qed.

  Definition functor_ass_from_nat_trans_ass
             {αC : associator TC} {αD : associator TD}
             {F : functor C D}
             {FF : functor_tensorunit_disp_cat TC TD IC ID F}
             {FF_iso : is_nat_z_iso (pr11 FF)}
             (FFF : functor_nat_trans_preserves αC αD FF_iso)
    : functor_ass_disp_cat αC αD (_,,FF).
  Proof.
    intros x y z.
    simpl.
    set (t := toforallpaths _ _ _ (base_paths _ _ FFF) ((x,y),z)).
    simpl in t.
    rewrite ! (functor_id TD) in t.
    rewrite ! id_left in t.
    rewrite ! id_right in t.
    refine (t @ _).
    apply assoc.
  Qed.

End AssociatorMonoidalProperty.
