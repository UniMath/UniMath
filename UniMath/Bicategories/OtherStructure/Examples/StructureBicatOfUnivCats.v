(**
 Duality involutions of bicategories

 Contents:
 1. Duality involution on categories
 2. Classifying discrete opfibration
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Elements.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetOpFibration.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatSlice.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.Examples.MorphismsInBicatOfUnivCats.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Op2OfPseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.OpFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.OtherStructure.ClassifyingDiscreteOpfib.
Require Import UniMath.Bicategories.OtherStructure.DualityInvolution.

Local Open Scope cat.

(**
 1. Duality involution on categories
 *)
Definition op_unit_nat_trans
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : functor_identity C₁ ∙ functor_opp (functor_opp F)
    ⟹
    F ∙ functor_identity C₂.
Proof.
  use make_nat_trans.
  - exact (λ x, identity (F x)).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_unit_nat_iso
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : nat_iso
      (functor_identity C₁ ∙ functor_opp (functor_opp F))
      (F ∙ functor_identity C₂).
Proof.
  use make_nat_iso.
  - exact (op_unit_nat_trans F).
  - intro.
    apply identity_is_iso.
Defined.

Definition op_unit_data
  : pstrans_data
      (id_psfunctor _)
      (comp_psfunctor op_psfunctor (op2_psfunctor op_psfunctor)).
Proof.
  use make_pstrans_data.
  - exact (λ C, functor_identity _).
  - intros C₁ C₂ F.
    use nat_iso_to_invertible_2cell.
    exact (op_unit_nat_iso F).
Defined.

Definition op_unit_is_pstrans
  : is_pstrans op_unit_data.
Proof.
  repeat split ; intro ; intros ;
    (use nat_trans_eq ; [ apply homset_property | ]) ; intro ; cbn ;
    rewrite ?id_left, ?id_right.
  - apply idpath.
  - apply idpath.
  - exact (!(functor_id _ _)).
Qed.

Definition op_unit
  : pstrans
      (id_psfunctor _)
      (comp_psfunctor op_psfunctor (op2_psfunctor op_psfunctor)).
Proof.
  use make_pstrans.
  - exact op_unit_data.
  - exact op_unit_is_pstrans.
Defined.

Definition op_unit_inv_nat_trans
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : functor_identity _ ∙ F
    ⟹
    functor_opp (functor_opp F) ∙ functor_identity _.
Proof.
  use make_nat_trans.
  - exact (λ x, identity (F x)).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_unit_inv_nat_iso
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : nat_iso
      (functor_identity _ ∙ F)
      (functor_opp (functor_opp F) ∙ functor_identity _).
Proof.
  use make_nat_iso.
  - exact (op_unit_inv_nat_trans F).
  - intro.
    apply identity_is_iso.
Defined.

Definition op_unit_inv_data
  : pstrans_data
      (comp_psfunctor op_psfunctor (op2_psfunctor op_psfunctor))
      (id_psfunctor _).
Proof.
  use make_pstrans_data.
  - exact (λ C, functor_identity _).
  - intros C₁ C₂ F.
    use nat_iso_to_invertible_2cell.
    exact (op_unit_inv_nat_iso F).
Defined.

Definition op_unit_inv_is_pstrans
  : is_pstrans op_unit_inv_data.
Proof.
  repeat split ; intro ; intros ;
    (use nat_trans_eq ; [ apply homset_property | ]) ; intro ; cbn ;
    rewrite ?id_left, ?id_right.
  - apply idpath.
  - apply idpath.
  - exact (!(functor_id _ _)).
Qed.

Definition op_unit_inv
  : pstrans
      (comp_psfunctor op_psfunctor (op2_psfunctor op_psfunctor))
      (id_psfunctor _).
Proof.
  use make_pstrans.
  - exact op_unit_inv_data.
  - exact op_unit_inv_is_pstrans.
Defined.

Definition op_triangle_nat_trans
           (C : category)
  : functor_identity _ ⟹ functor_opp (functor_identity C).
Proof.
  use make_nat_trans.
  - exact (λ x, identity x).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_triangle_nat_iso
           (C : category)
  : nat_iso
      (functor_identity _)
      (functor_opp (functor_identity C)).
Proof.
  use make_nat_iso.
  - exact (op_triangle_nat_trans C).
  - intro.
    apply identity_is_iso.
Defined.

Definition op_triangle
           (C : op2_bicat bicat_of_univ_cats)
  : invertible_2cell
      (op_unit (op_psfunctor C))
      (# op_psfunctor (op_unit C)).
Proof.
  use nat_iso_to_invertible_2cell.
  exact (op_triangle_nat_iso _).
Defined.

Definition op_unit_unit_inv_nat_trans
           (C : category)
  : nat_trans
      (functor_identity C)
      (functor_identity C ∙ functor_identity ((C^op)^op)).
Proof.
  use make_nat_trans.
  - exact (λ x, identity x).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_unit_unit_inv_nat_iso
           (C : category)
  : nat_iso
      (functor_identity C)
      (functor_identity C ∙ functor_identity ((C^op)^op)).
Proof.
  use make_nat_iso.
  - exact (op_unit_unit_inv_nat_trans C).
  - intro.
    apply identity_is_iso.
Defined.

Definition op_unit_unit_inv_data
  : invertible_modification_data
      (id₁ _)
      (op_unit · op_unit_inv).
Proof.
  intro C.
  use nat_iso_to_invertible_2cell.
  exact (op_unit_unit_inv_nat_iso _).
Defined.

Definition op_unit_unit_inv_is_modif
  : is_modification op_unit_unit_inv_data.
Proof.
  intros C₁ C₂ F.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro x ; cbn.
  rewrite !id_left, !id_right.
  exact (!(functor_id _ _)).
Qed.

Definition op_unit_unit_inv
  : invertible_modification
      (id₁ _)
      (op_unit · op_unit_inv).
Proof.
  use make_invertible_modification.
  - exact op_unit_unit_inv_data.
  - exact op_unit_unit_inv_is_modif.
Defined.

Definition op_unit_inv_unit_nat_trans
           (C : category)
  : nat_trans
      (functor_identity ((C^op)^op) ∙ functor_identity C)
      (functor_identity ((C^op)^op)).
Proof.
  use make_nat_trans.
  - exact (λ x, identity x).
  - abstract
      (intros x y f ; cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition op_unit_inv_unit_nat_iso
           (C : category)
  : nat_iso
      (functor_identity ((C^op)^op) ∙ functor_identity C)
      (functor_identity ((C^op)^op)).
Proof.
  use make_nat_iso.
  - exact (op_unit_inv_unit_nat_trans C).
  - intro.
    apply identity_is_iso.
Defined.

Definition op_unit_inv_unit_data
  : invertible_modification_data
      (op_unit_inv · op_unit)
      (id₁ _).
Proof.
  intro C.
  use nat_iso_to_invertible_2cell.
  exact (op_unit_inv_unit_nat_iso _).
Defined.

Definition op_unit_inv_unit_is_modif
  : is_modification op_unit_inv_unit_data.
Proof.
  intros C₁ C₂ F.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro x ; cbn.
  rewrite !id_left, !id_right.
  exact (!(functor_id _ _)).
Qed.

Definition op_unit_inv_unit
  : invertible_modification
      (op_unit_inv · op_unit)
      (id₁ _).
Proof.
  use make_invertible_modification.
  - exact op_unit_inv_unit_data.
  - exact op_unit_inv_unit_is_modif.
Defined.

Definition bicat_of_univ_cat_duality_involution_data
  : duality_involution_data op_psfunctor.
Proof.
  use make_duality_involution_data.
  - exact op_unit.
  - exact op_unit_inv.
  - exact op_unit_unit_inv.
  - exact op_unit_inv_unit.
  - exact op_triangle.
Defined.

Definition bicat_of_univ_cat_duality_laws
  : duality_involution_laws bicat_of_univ_cat_duality_involution_data.
Proof.
  split.
  - intro C.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x ; cbn.
    apply id_left.
  - intros C₁ C₂ F.
    use nat_trans_eq ; [ apply homset_property | ].
    intro  ; cbn.
    rewrite !id_left.
    exact (!(functor_id _ _)).
Qed.

Definition bicat_of_univ_cat_duality
  : duality_involution op_psfunctor
  := bicat_of_univ_cat_duality_involution_data ,, bicat_of_univ_cat_duality_laws.

(** 2. Classifying discrete opfibration *)
Definition disc_sopfib_cat_of_elems_forgetful
           {C : univalent_category}
           (P : C ⟶ HSET)
  : @disc_sopfib
      bicat_of_univ_cats
      (univalent_cat_of_elems P) C
      (cat_of_elems_forgetful P).
Proof.
  split.
  - apply street_opfib_is_internal_sopfib.
    apply opfibration_is_street_opfib.
    apply disp_cat_of_elems_opcleaving.
  - split.
    + apply cat_faithful_is_faithful_1cell.
      apply pr1_category_faithful.
      intro ; intros.
      apply disp_mor_elems_isaprop.
    + apply cat_conservative_is_conservative_1cell.
      apply groupoidal_disp_cat_to_conservative.
      intro ; intros.
      apply is_iso_disp_cat_of_elems.
Defined.

Section CategoryOfElementsHasPbUMP.
  Context {C : bicat_of_univ_cats}
          (P : C --> HSET_univalent_category).

  Let F₁ : bicat_of_univ_cats ⟦ univalent_cat_of_elems P , pointed_sets_univalent ⟧
    := cat_of_elems_to_pointed P.
  Let F₂ : bicat_of_univ_cats ⟦ univalent_cat_of_elems P, C ⟧
    := cat_of_elems_forgetful P.

  Definition cat_of_elems_inv2cell
    : invertible_2cell
        (F₁ · set_of_pointed_set)
        (F₂ · P).
  Proof.
    use invertible_2cell_is_nat_iso.
    exact (cat_of_elems_commute_iso P).
  Defined.

  Let cone
    : @pb_cone bicat_of_univ_cats _ _ _ set_of_pointed_set P
    := make_pb_cone
         _ _ _
         cat_of_elems_inv2cell.

  Definition cat_of_elems_pb_ump_1
    : pb_ump_1 cone.
  Proof.
    intro q.
    use make_pb_1cell.
    - cbn.
      apply (functor_to_cat_of_elems
               _
               (pb_cone_pr1 q)
               (pb_cone_pr2 q)).
      apply invertible_2cell_to_nat_iso.
      apply (pb_cone_cell q).
    - apply nat_iso_to_invertible_2cell.
      apply functor_to_cat_of_elems_pointed.
    - apply nat_iso_to_invertible_2cell.
      apply functor_to_cat_of_elems_forgetful.
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         use funextsec ;
         intro z ; cbn ;
         cbn in * ;
         refine (_ @ !(eqtohomot (functor_id P (pr1 (pb_cone_pr2 q) x)) _)) ;
         exact (!(eqtohomot
                    (nat_trans_eq_pointwise (vcomp_linv (pb_cone_cell q)) x) z))).
  Defined.

  Definition cat_of_elems_pb_ump_2
    : pb_ump_2 cone.
  Proof.
    intros C' G₁ G₂ τ₁ τ₂ p.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ;
         use subtypePath ; [ intro ; apply disp_mor_elems_isaprop | ] ;
         exact (nat_trans_eq_pointwise (pr22 φ₁) x @ !(nat_trans_eq_pointwise (pr22 φ₂) x))).
    - simple refine (_ ,, _ ,, _).
      + refine (nat_trans_to_cat_of_elems P τ₁ τ₂ _).
        abstract
          (intro x ;
           pose (q := eqtohomot (nat_trans_eq_pointwise p x)) ;
           cbn in q ;
           apply q).
      + abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           cbn ;
           intro ;
           use subtypePath ; [ intro ; apply (pr1 P _) | ] ;
           exact (nat_trans_eq_pointwise p x)).
      + abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           cbn ;
           intro ;
           apply idpath).
  Defined.

  Definition cat_of_elems_has_pb_ump
    : has_pb_ump cone.
  Proof.
    split.
    - exact cat_of_elems_pb_ump_1.
    - exact cat_of_elems_pb_ump_2.
  Defined.
End CategoryOfElementsHasPbUMP.

Definition pb_via_cat_of_elems
  : @map_to_disp_sopfib bicat_of_univ_cats _ _ set_of_pointed_set.
Proof.
  intros C P.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, (_ ,, _))).
  - exact (univalent_cat_of_elems P).
  - exact (cat_of_elems_forgetful P).
  - exact (disc_sopfib_cat_of_elems_forgetful P).
  - exact (cat_of_elems_to_pointed P).
  - exact (cat_of_elems_inv2cell P).
  - exact (cat_of_elems_has_pb_ump P).
Defined.

Definition disc_sopfib_set_of_pointed_set
  : @disc_sopfib
      bicat_of_univ_cats
      _ _
      set_of_pointed_set.
Proof.
  split.
  - apply street_opfib_is_internal_sopfib.
    apply opfibration_is_street_opfib.
    apply opcleaving_elements_universal.
  - split.
    + apply cat_faithful_is_faithful_1cell.
      apply pr1_category_faithful.
      intros X Y f x y.
      apply Y.
    + apply cat_conservative_is_conservative_1cell.
      apply groupoidal_disp_cat_to_conservative.
      intros X Y f Hf x y ff.
      apply is_iso_disp_elements_universal.
Defined.

Section IsClassifyingFull.
  Context {C : univalent_category}
          {F G : C ⟶ HSET_univalent_category}
          (n : disc_sopfib_slice
                 univalent_cat_is_univalent_2_1
                 C
               ⟦ pr1 (pb_via_cat_of_elems C F)
               , pr1 (pb_via_cat_of_elems C G) ⟧).

  Definition is_classifying_nat_trans_data
    : nat_trans_data F G.
  Proof.
    intros x z.
    exact (cat_of_elems_iso_lift
             G
             (pr2 C)
             (pr1 (pr122 n) (x ,, z))
             (iso_is_iso
                (nat_iso_pointwise_iso
                   (make_nat_iso
                      _ _ _
                      (is_invertible_2cell_to_is_nat_iso _ (pr222 n)))
                   (x ,, z)))
             (pr2 (pr1 (pr1 n) (x ,, z)))).
  Defined.

  Definition is_classifying_nat_trans_is_nat_trans
    : is_nat_trans _ _ is_classifying_nat_trans_data.
  Proof.
    intros x y f ; cbn.
    use funextsec.
    intro z.
    unfold is_classifying_nat_trans_data ; cbn.
    unfold cat_of_elems_iso_lift ; cbn.
    pose (p := pr212 (pr2 n) (x ,, z) (y,, # F f z) (f ,, idpath _)).
    refine (cat_of_elems_iso_natural _ _ _ _ _ _ _ _ _ _ p (!_)) ; cbn.
    exact (pr2 (@functor_on_morphisms
                  _ _
                  (pr11 n)
                  (x ,, z) (y,, # F f z)
                  (f ,, idpath _))).
  Qed.

  Definition is_classifying_nat_trans
    : F ⟹ G.
  Proof.
    use make_nat_trans.
    - exact is_classifying_nat_trans_data.
    - exact is_classifying_nat_trans_is_nat_trans.
  Defined.

  Definition is_classifying_bicat_of_univ_cats_eq_nat_trans_data
    : nat_trans_data
        (mor_of_pb_disc_sopfib_mor
           _
           disc_sopfib_set_of_pointed_set
           pb_via_cat_of_elems
           (is_classifying_nat_trans) : _ ⟶ _)
        (pr1 n : _ ⟶ _).
  Proof.
    intro x.
    simple refine (pr1 (pr122 n) x ,, _).
    apply cat_of_elems_iso_path.
  Defined.

  Definition is_classifying_bicat_of_univ_cats_eq_is_nat_trans
    : is_nat_trans _ _ is_classifying_bicat_of_univ_cats_eq_nat_trans_data.
  Proof.
    intros x y f.
    use subtypePath.
    {
      intro.
      apply disp_mor_elems_isaprop.
    }
    cbn.
    exact (nat_trans_ax (pr122 n) _ _ f).
  Qed.

  Definition is_classifying_bicat_of_univ_cats_nat_trans
    : mor_of_pb_disc_sopfib_mor
        _
        disc_sopfib_set_of_pointed_set
        pb_via_cat_of_elems
        (is_classifying_nat_trans)
      ==>
      pr1 n.
  Proof.
    use make_nat_trans.
    - exact is_classifying_bicat_of_univ_cats_eq_nat_trans_data.
    - exact is_classifying_bicat_of_univ_cats_eq_is_nat_trans.
  Defined.

  Definition invertible_is_classifying_bicat_of_univ_cats_nat_trans
    : is_invertible_2cell is_classifying_bicat_of_univ_cats_nat_trans.
  Proof.
    use is_nat_iso_to_is_invertible_2cell.
    intros x.
    use is_iso_cat_of_elems.
    cbn.
    exact (iso_is_iso
             (nat_iso_pointwise_iso
                (make_nat_iso
                   _ _ _
                   (is_invertible_2cell_to_is_nat_iso _ (pr222 n)))
                x)).
  Defined.

  Definition is_classifying_bicat_of_univ_cats_nat_trans_coh
    : is_classifying_bicat_of_univ_cats_nat_trans ▹ _
      =
      pb_ump_mor_pr2
        (cat_of_elems_has_pb_ump G)
        (mor_of_pb_disc_sopfib_mor_cone
           _
           disc_sopfib_set_of_pointed_set
           pb_via_cat_of_elems (is_classifying_nat_trans))
      • pr122 n.
  Proof.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    cbn.
    rewrite id_left.
    apply idpath.
  Qed.
End IsClassifyingFull.

Definition is_classifying_full_help_in_bicat_of_univ_cats
  : is_classifying_full_help
      univalent_cat_is_univalent_2_1
      set_of_pointed_set
      disc_sopfib_set_of_pointed_set
      pb_via_cat_of_elems.
Proof.
  intros C F G n.
  simple refine (_ ,, _ ,, (_ ,, _)).
  - exact (is_classifying_nat_trans n).
  - exact (is_classifying_bicat_of_univ_cats_nat_trans n).
  - exact (invertible_is_classifying_bicat_of_univ_cats_nat_trans n).
  - exact (is_classifying_bicat_of_univ_cats_nat_trans_coh n).
Defined.

Definition is_classifying_faithful_help_in_bicat_of_univ_cats
  : is_classifying_faithful_help
      _
      disc_sopfib_set_of_pointed_set
      pb_via_cat_of_elems.
Proof.
  intros C F G n₁ n₂ γ p.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro x.
  use funextsec.
  intro z.
  pose (pr11 γ (x ,, z)) as q.
  cbn in q.
  refine (_ @ pr2 q).
  unfold q ; clear q.
  pose (nat_trans_eq_pointwise p (x ,, z)) as q.
  cbn in q.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    refine (!(id_right _) @ _).
    exact q.
  }
  apply (eqtohomot (functor_id G x)).
Qed.

Definition is_classifying_in_bicat_of_univ_cats
  : is_classifying
      univalent_cat_is_univalent_2_1
      set_of_pointed_set
      disc_sopfib_set_of_pointed_set
      pb_via_cat_of_elems.
Proof.
  use make_is_classifying.
  - exact is_classifying_full_help_in_bicat_of_univ_cats.
  - exact is_classifying_faithful_help_in_bicat_of_univ_cats.
Defined.
