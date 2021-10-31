(** **********************************************************

Ralph Matthes

2021
*)

(** **********************************************************

Contents :

- build monoidal category for the pointed endofunctors

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.UnitorsAndAssociatorsForEndofunctors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.Monoidal.EndofunctorsMonoidal.

Local Open Scope cat.

Section PointedFunctors_as_monoidal_category.

  Context (C : category).

  Local Notation "'Ptd'" := (category_Ptd C).

  Definition tensor_pointedfunctor_data: functor_data (Ptd ⊠ Ptd) Ptd.
  Proof.
    use make_functor_data.
    - intros PF1PF2.
      exact (ptd_compose C (pr1 PF1PF2) (pr2 PF1PF2)).
    - intros PF1PF2 PF1PF2' α1α2.
      induction α1α2 as [α1 α2].
      induction PF1PF2 as [PF1 PF2]. induction PF1PF2' as [PF1' PF2'].
      cbn in α1, α2 |- *.
      set (α1' := pr1 α1).
      set (α2' := pr1 α2).
      exists (# (functorial_composition _ _ _) (α1',,α2':
                 [C, C] ⊠ [C, C]⟦(pr1 PF1,,pr1 PF2),(pr1 PF1',,pr1 PF2')⟧)).
      abstract ( intro c;
                 assert (α1commutes := ptd_mor_commutes _ α1);
                 assert (α2commutes := ptd_mor_commutes _ α2);
                 cbn;
                 etrans;
                 [ apply maponpaths; apply nat_trans_ax |
                   rewrite <- α1commutes;
                   repeat rewrite <- assoc;
                   apply maponpaths;
                   rewrite assoc;
                   unfold α2';
                   etrans;
                   [apply cancel_postcomposition;
                    apply α2commutes |
                     etrans;
                     [assert (η2'nat := nat_trans_ax (pr2 PF2'));
                      apply pathsinv0, η2'nat |
                       apply idpath]]] ).
  Defined.

  Definition tensor_pointedfunctor_is_functor: is_functor tensor_pointedfunctor_data.
  Proof.
    split.
    - intro PF1PF2.
      (* UniMath.MoreFoundations.Tactics.show_id_type. *)
      apply eq_ptd_mor.
      unfold tensor_pointedfunctor_data.
      simpl. unfold post_whisker_in_funcat, pre_whisker_in_funcat.
      rewrite pre_whisker_identity.
      rewrite post_whisker_identity.
      apply nat_trans_eq; try apply homset_property. intro c.
      cbn.
      apply id_right.
    - intros PF1PF2 PF1'PF2' PF1''PF2'' α1α2 α1'α2'.
      apply eq_ptd_mor.
      unfold tensor_pointedfunctor_data.
      simpl. unfold post_whisker_in_funcat, pre_whisker_in_funcat.
      rewrite (post_whisker_composition _ _ _).
      rewrite (pre_whisker_composition _ _ _).
      cbn.
      apply nat_trans_eq; try apply homset_property. intro c.
      cbn.
      repeat rewrite <- assoc.
      apply maponpaths.
      do 2 rewrite assoc.
      apply cancel_postcomposition.
      apply nat_trans_ax.
  Qed.

  Definition tensor_pointedfunctors:
    category_Ptd C ⊠ category_Ptd C ⟶ category_Ptd C.
  Proof.
    use make_functor.
    - exact tensor_pointedfunctor_data.
    - exact tensor_pointedfunctor_is_functor.
  Defined.

  (** a preparation for the lemma afterwards *)
  Lemma ptd_mor_z_iso_from_underlying_mor {F G : Ptd} (α : ptd_mor C F G):
    is_nat_z_iso (pr1 α) -> is_z_isomorphism(C:=Ptd) α.
  Proof.
    intro Hyp.
    use tpair.
    - use tpair.
      apply nat_z_iso_to_trans_inv.
      + exact (pr1 α ,, Hyp).
      + abstract
          (cbn; red; intro c;
           cbn;
           apply pathsinv0;
           apply (z_iso_inv_on_left _ _ _ _ (make_z_iso _ _ (Hyp c)));
           cbn;
           apply pathsinv0;
           apply ptd_mor_commutes).
    - abstract
        (red; split; apply eq_ptd_mor; apply (nat_trans_eq (homset_property C)); intro c; cbn ;
         [ apply (z_iso_inv_after_z_iso (make_z_iso _ _ (Hyp c)))
          | apply (z_iso_after_z_iso_inv (make_z_iso _ _ (Hyp c))) ]).
  Defined.

  Definition left_unitor_of_pointedfunctors:
    left_unitor tensor_pointedfunctors (id_Ptd C).
  Proof.
    use make_nat_z_iso.
    + use make_nat_trans.
      * intro PF.
        exists (λ_functors (pr1 PF)).
        abstract ( intro c; cbn; rewrite id_right; apply id_left ).
      * abstract ( intros PF PF' α;
                   apply eq_ptd_mor;
                   apply (nat_trans_eq (homset_property C)); intro c; cbn;
                   rewrite id_left;
                   rewrite id_right;
                   etrans; [apply cancel_postcomposition, functor_id | apply id_left] ).
    + intro PF. cbn.
      apply ptd_mor_z_iso_from_underlying_mor.
      intro c.
      cbn.
      apply identity_is_z_iso.
  Defined.

  Definition right_unitor_of_pointedfunctors:
    right_unitor tensor_pointedfunctors (id_Ptd C).
  Proof.
    use make_nat_z_iso.
    + use make_nat_trans.
      * intro PF.
        exists (ρ_functors (pr1 PF)).
        abstract ( intro c;
                   cbn;
                   rewrite id_right;
                   apply id_right ).
      * abstract ( intros PF PF' α;
                   apply eq_ptd_mor;
                   apply (nat_trans_eq (homset_property C));
                   intro c; cbn;
                   rewrite id_left;
                   rewrite id_right;
                   apply id_right ).
    + intro PF. cbn.
      apply ptd_mor_z_iso_from_underlying_mor.
      intro c.
      cbn.
      apply identity_is_z_iso.
  Defined.

  Definition associator_of_pointedfunctors : associator tensor_pointedfunctors.
  Proof.
    use make_nat_z_iso.
    + use make_nat_trans.
      * intro PFtriple.
        induction PFtriple as [[PF1 PF2] PF3].
        exists (α_functors (pr1 PF1) (pr1 PF2) (pr1 PF3)).
        abstract ( intro c;
                   cbn;
                   rewrite id_right;
                   apply pathsinv0, assoc ).
      * abstract ( intros PFtriple PFtriple' αtriple;
                   apply eq_ptd_mor;
                   apply (nat_trans_eq (homset_property C));
                   intro c; cbn;
                   rewrite id_right;
                   rewrite id_left;
                   rewrite assoc;
                   apply cancel_postcomposition;
                   apply functor_comp ).
    + intro PFtriple. cbn.
      apply ptd_mor_z_iso_from_underlying_mor.
      intro c.
      cbn.
      apply identity_is_z_iso.
  Defined.

  Lemma triangle_eq_of_pointedfunctors :
    triangle_eq tensor_pointedfunctors (id_Ptd C)
                left_unitor_of_pointedfunctors
                right_unitor_of_pointedfunctors
                associator_of_pointedfunctors.
  Proof.
    intros PF1 PF2.
    apply eq_ptd_mor.
    (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    apply (nat_trans_eq (homset_property C)).
    intro c.
    cbn.
    do 2 rewrite id_right.
    apply pathsinv0, id_left.
  Qed.

  Lemma pentagon_eq_of_pointedfunctors :
    pentagon_eq tensor_pointedfunctors associator_of_pointedfunctors.
  Proof.
    intros PF1 PF2 PF3 PF4.
    apply eq_ptd_mor.
    apply nat_trans_eq_alt.
    intro c.
    cbn.
    do 3 rewrite functor_id.
    do 5 rewrite id_right.
    apply pathsinv0, functor_id.
  Qed.

  Definition monoidal_cat_of_pointedfunctors : monoidal_cat.
  Proof.
    use mk_monoidal_cat.
    - exact Ptd.
    - apply tensor_pointedfunctors.
    - apply id_Ptd.
    - exact left_unitor_of_pointedfunctors.
    - exact right_unitor_of_pointedfunctors.
    - exact associator_of_pointedfunctors.
    - exact triangle_eq_of_pointedfunctors.
    - exact pentagon_eq_of_pointedfunctors.
  Defined.

  Definition forgetful_functor_from_ptd_as_strong_monoidal_functor
    : strong_monoidal_functor
        monoidal_cat_of_pointedfunctors
        (monoidal_cat_of_endofunctors C).
  Proof.
    use tpair.
    - apply (mk_lax_monoidal_functor
               monoidal_cat_of_pointedfunctors
               (monoidal_cat_of_endofunctors C)
               (functor_ptd_forget C)
               (nat_trans_id _)
               (nat_trans_id _)).
      + abstract ( intros PF1 PF2 PF3;
                   apply nat_trans_eq_alt;
                   intro c;
                   cbn;
                   do 2 rewrite functor_id;
                   repeat rewrite id_right;
                   apply functor_id ).
      + abstract ( intro PF;
                   split; apply nat_trans_eq_alt; intro c; cbn; do 3 rewrite id_right;
                   [ apply pathsinv0, functor_id | apply idpath ] ).
    - split;
        [ apply (nat_trafo_z_iso_if_pointwise_z_iso C);
          apply is_nat_z_iso_nat_trans_id
        | apply (is_nat_z_iso_nat_trans_id
                   ((functor_composite
                       (PrecategoryBinProduct.pair_functor
                          (functor_ptd_forget C)
                          (functor_ptd_forget C))
                       (functorial_composition _ _ _))))].
  Defined.

End PointedFunctors_as_monoidal_category.
