(** exploring the isomorphism between [A × B --> C] and [[B, [A,C]]] for categories A, B, C

Authors: Ralph Matthes 2021
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.UnitorsAndAssociatorsForEndofunctors.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCatsWithoutUnivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.

Import Bicat.Notations.

Local Open Scope cat.

Section Upstream.

  Context (A B : category).

  Definition category_binproduct : category :=
    precategory_binproduct A B ,, has_homsets_precategory_binproduct A B (homset_property A) (homset_property B).


End Upstream.

Local Definition CAT : bicat := bicat_of_cats_nouniv.

Section SomePseudoFunctors.

Section ProductWithFixedSecondArgument.

  Context (B0 : ob CAT).

Definition binproductleft_map_data: psfunctor_data CAT CAT.
Proof.
  use make_psfunctor_data.
  - exact (fun A =>  category_binproduct A B0).
  - intros A A' F.
    exact (pair_functor F (functor_identity (pr1 B0))).
  - intros A A' F G α. cbn.
    use make_nat_trans.
    + intro ab. induction ab as [a b].
      cbn.
      exact (pr1 α a ,, identity b).
    + intros ab ab' fg. induction ab as [a b]. induction ab' as [a' b'].
      induction fg as [f g].
      cbn.
      apply pathsdirprod.
      * apply nat_trans_ax.
      * rewrite id_left.
        apply id_right.
  - intro A. cbn.
    use make_nat_trans.
    + intro ab. exact (identity ab).
    + intros ab ab' fg.
      cbn.
      apply pathsdirprod; rewrite id_left; apply id_right.
  - intros A1 A2 A3 F G. cbn.
    use make_nat_trans.
    + intro a1b. apply identity.
    + intros a1b a1b' fg.
      cbn.
      apply pathsdirprod; rewrite id_left; apply id_right.
Defined.

Definition binproductleft_map_laws: psfunctor_laws binproductleft_map_data.
Proof.
  repeat split; red; cbn.
  - intros A A' F.
    apply nat_trans_eq; try exact (homset_property (category_binproduct _ _)).
    intro ab. cbn. apply idpath.
  - intros A A' F1 F2 F3 α β.
    apply nat_trans_eq; try exact (homset_property (category_binproduct _ _)).
    intro ab. cbn.
    apply pathsdirprod.
    * apply idpath.
    * apply pathsinv0, id_left.
  - intros A B F.
    apply nat_trans_eq; try exact (homset_property (category_binproduct _ _)).
    intro ab. cbn.
    apply pathsdirprod.
    * do 2 rewrite id_right. apply pathsinv0, functor_id.
    * do 2 rewrite id_right. apply idpath.
  - intros A B F.
    apply nat_trans_eq; try exact (homset_property (category_binproduct _ _)).
    intro ab. cbn.
    apply pathsdirprod; do 2 rewrite id_right; apply idpath.
  - intros A1 A2 A3 A4 F G H.
    apply nat_trans_eq; try exact (homset_property (category_binproduct _ _)).
    intro a1b. cbn.
    apply pathsdirprod.
    * do 3 rewrite id_left. rewrite id_right.
      apply pathsinv0, functor_id.
    * apply idpath.
  - intros A1 A2 A3 F G1 G2 β.
    apply nat_trans_eq; try exact (homset_property (category_binproduct _ _)).
    intro a1b. cbn.
    apply pathsdirprod.
    * rewrite id_left, id_right.
      apply idpath.
    * apply idpath.
  - intros A1 A2 A3 F1 F2 G α.
    apply nat_trans_eq; try exact (homset_property (category_binproduct _ _)).
    intro a1b. cbn.
    apply pathsdirprod.
    * rewrite id_left, id_right.
      apply idpath.
    * apply idpath.
Defined.

Definition binproductleft_psfunctor: psfunctor CAT CAT.
Proof.
  use make_psfunctor.
  - exact binproductleft_map_data.
  - exact binproductleft_map_laws.
  - split; red; cbn.
    + intro A.
      use tpair.
      * use make_nat_trans.
        -- intro ab. apply identity.
        -- intros ab ab' fg.
           cbn.
           apply pathsdirprod; rewrite id_left; apply id_right.
      * split; apply nat_trans_eq; try exact (homset_property (category_binproduct _ _));
          intro ab; cbn; apply pathsdirprod; apply id_left.
    + intros A1 A2 A3 F G.
      use tpair.
      * use make_nat_trans.
        -- intro a1b. apply identity.
        -- intros a1b a1b' fg.
           cbn.
           apply pathsdirprod; rewrite id_left; apply id_right.
      * split; apply nat_trans_eq; try exact (homset_property (category_binproduct _ _));
          intro a1b; cbn; apply pathsdirprod; apply id_left.
Defined.

End ProductWithFixedSecondArgument.

Section FunctorCategoryWithFixedSource.

  Context (A0 : ob CAT).

Definition functorcategoryright_map_data: psfunctor_data CAT CAT.
Proof.
  use make_psfunctor_data.
  - exact (fun B => functor_category (pr1 A0) B).
  - intros B B' F.
    cbn.
    exact (post_composition_functor (pr1 A0) (pr1 B) (pr1 B') (homset_property B) (homset_property B') F).
  - intros B1 B2 F F' β.
    use make_nat_trans.
    + intro G. cbn.
      exact (pre_whisker (pr1 G) β).
    + intros G G' α. cbn.
      etrans.
      2: { apply horcomp_pre_post. }
      apply pathsinv0.
      apply horcomp_post_pre.
  - intro B.
    use make_nat_trans.
    + intro G. cbn. apply ρ_functors_inv.
    + intros G G' α.
      apply nat_trans_eq; try apply (homset_property B).
      intro a.
      cbn.
      rewrite id_left; apply id_right.
  - intros B1 B2 B3 H F. cbn.
    use make_nat_trans.
    + intro G.
      cbn.
      apply α_functors.
    + intros G G' α. cbn.
      apply nat_trans_eq; try apply (homset_property B3).
      intro a.
      cbn.
      rewrite id_left; apply id_right.
Defined.

Definition functorcategoryright_map_laws: psfunctor_laws functorcategoryright_map_data.
Proof.
  repeat split; red; cbn.
  - intros B B' F.
    apply nat_trans_eq; try exact (homset_property (functor_category _ _)).
    intro G.
    apply nat_trans_eq; try exact (homset_property B').
    intro a. apply idpath.
  - intros B B' F1 F2 F3 β1 β2.
    apply nat_trans_eq; try exact (homset_property (functor_category _ _)).
    intro G.
    apply nat_trans_eq; try exact (homset_property B').
    intro a. apply idpath.
  - intros B B' F.
    apply nat_trans_eq; try exact (homset_property (functor_category _ _)).
    intro G.
    apply nat_trans_eq; try exact (homset_property B').
    intro a.
    cbn.
    do 2 rewrite id_right; apply pathsinv0, functor_id.
  - intros B B' F.
    apply nat_trans_eq; try exact (homset_property (functor_category _ _)).
    intro G.
    apply nat_trans_eq; try exact (homset_property B').
    intro a.
    cbn.
    do 2 rewrite id_right; apply idpath.
  - intros B1 B2 B3 B4 F1 F2 F3.
    apply nat_trans_eq; try exact (homset_property (functor_category _ _)).
    intro G.
    apply nat_trans_eq; try exact (homset_property B4).
    intro a.
    cbn. do 3 rewrite id_left. rewrite id_right. apply pathsinv0, functor_id.
  - intros B C D F H1 H2 γ.
    apply nat_trans_eq; try exact (homset_property (functor_category _ _)).
    intro G.
    apply nat_trans_eq; try exact (homset_property D).
    intro a.
    cbn. rewrite id_right; apply id_left.
  - intros B C D F1 F2 H β.
    apply nat_trans_eq; try exact (homset_property (functor_category _ _)).
    intro G.
    apply nat_trans_eq; try exact (homset_property D).
    intro a.
    cbn. rewrite id_right; apply id_left.
Defined.

Definition functorcategoryright_psfunctor: psfunctor CAT CAT.
Proof.
  use make_psfunctor.
  - exact functorcategoryright_map_data.
  - exact functorcategoryright_map_laws.
  - split; red; cbn.
    + intro B.
      use tpair.
      * use make_nat_trans.
        -- intro G.
           cbn. apply ρ_functors.
        -- intros G G' α.
           apply nat_trans_eq; try exact (homset_property B).
           intro a.
           cbn. rewrite id_left; apply id_right.
      * split; apply nat_trans_eq; try exact (homset_property (functor_category _ _));
          intro G; cbn; apply nat_trans_eq; try exact (homset_property B); intro a; apply id_left.
    + intros B1 B2 B3 F H.
      use tpair.
      * use make_nat_trans.
        -- intro G.
           cbn. apply α_functors_inv.
        -- intros G G' α.
           apply nat_trans_eq; try exact (homset_property B3).
           intro a.
           cbn. rewrite id_left; apply id_right.
      * split; apply nat_trans_eq; try exact (homset_property (functor_category _ _));
          intro G; cbn; apply nat_trans_eq; try exact (homset_property B3); intro a; apply id_left.
Defined.

End FunctorCategoryWithFixedSource.

End SomePseudoFunctors.
