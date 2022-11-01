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
