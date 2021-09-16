(** exploring the isomorphism between [A × B --> C] and [[B, [A,C]]] for categories A, B, C

Authors: Ralph Matthes 2021
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.UnitorsAndAssociatorsForEndofunctors.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCatsWithoutUnivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Modifications.Modification.

Import Bicat.Notations.

Local Open Scope cat.

Local Definition CAT : bicat := bicat_of_cats_nouniv.

Section ThePseudoFunctors.

Section ProductWithFixedSecondArgument.

  Context (B0 : ob CAT).

  Local Definition productwithfixedelement (A: ob CAT) : ob CAT := category_binproduct (pr1 A) (pr1 B0) (homset_property A) (homset_property B0).


Definition binproductleft_map_data: psfunctor_data CAT CAT.
Proof.
  use make_psfunctor_data.
  - exact productwithfixedelement.
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
    apply nat_trans_eq; try exact (homset_property (productwithfixedelement _)).
    intro ab. cbn. apply idpath.
  - intros A A' F1 F2 F3 α β.
    apply nat_trans_eq; try exact (homset_property (productwithfixedelement _)).
    intro ab. cbn.
    apply pathsdirprod.
    * apply idpath.
    * apply pathsinv0, id_left.
  - intros A B F.
    apply nat_trans_eq; try exact (homset_property (productwithfixedelement _)).
    intro ab. cbn.
    apply pathsdirprod.
    * do 2 rewrite id_right. apply pathsinv0, functor_id.
    * do 2 rewrite id_right. apply idpath.
  - intros A B F.
    apply nat_trans_eq; try exact (homset_property (productwithfixedelement _)).
    intro ab. cbn.
    apply pathsdirprod; do 2 rewrite id_right; apply idpath.
  - intros A1 A2 A3 A4 F G H.
    apply nat_trans_eq; try exact (homset_property (productwithfixedelement _)).
    intro a1b. cbn.
    apply pathsdirprod.
    * do 3 rewrite id_left. rewrite id_right.
      apply pathsinv0, functor_id.
    * apply idpath.
  - intros A1 A2 A3 F G1 G2 β.
    apply nat_trans_eq; try exact (homset_property (productwithfixedelement _)).
    intro a1b. cbn.
    apply pathsdirprod.
    * rewrite id_left, id_right.
      apply idpath.
    * apply idpath.
  - intros A1 A2 A3 F1 F2 G α.
    apply nat_trans_eq; try exact (homset_property (productwithfixedelement _)).
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
      * split; apply nat_trans_eq; try exact (homset_property (productwithfixedelement _));
          intro ab; cbn; apply pathsdirprod; apply id_left.
    + intros A1 A2 A3 F G.
      use tpair.
      * use make_nat_trans.
        -- intro a1b. apply identity.
        -- intros a1b a1b' fg.
           cbn.
           apply pathsdirprod; rewrite id_left; apply id_right.
      * split; apply nat_trans_eq; try exact (homset_property (productwithfixedelement _));
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

End ThePseudoFunctors.

Section Currying.

  Context (B0 : ob CAT).

  Let L := binproductleft_psfunctor B0.
  Let R := functorcategoryright_psfunctor B0.

(* to observe the type of the goal: match goal with | |- ?f => set (goal := f) end. *)


  Definition coevaluation_pstrans_data: pstrans_data (id_psfunctor CAT) (comp_psfunctor R L).
  Proof.
    use make_pstrans_data.
      + intro A. apply coevaluation_functor.
      + intros A A' F.
        apply nat_iso_to_invertible_2cell.
        use make_nat_iso.
        * use make_nat_trans.
          -- intro a.
             cbn in a. cbn.
             ++ use make_nat_trans.
                ** intro b. apply identity.
                ** intros b b' f. cbn.
                   apply pathsdirprod.
                   --- do 2 rewrite id_right. apply functor_id.
                   --- rewrite id_left. apply id_right.
          --  intros a a' g. cbn.
              apply nat_trans_eq; try exact (homset_property (productwithfixedelement _ _)).
              cbn. intro b.
              apply pathsdirprod.
              ++ rewrite id_left. apply id_right.
              ++ apply idpath.
        * intro a.
          apply is_iso_from_is_z_iso.
          apply nat_trafo_z_iso_if_pointwise_z_iso.
          intro b. cbn.
          cbn in F, a.
          set (aux := identity(C:=pr1(productwithfixedelement _ _)) (make_dirprod (F a) b)).
          change (is_z_isomorphism aux).
          apply identity_is_z_iso.
  Defined.

  Lemma coevaluation_is_pstrans: is_pstrans coevaluation_pstrans_data.
  Proof.
    repeat split.
    - intros A A' F F' α.
      apply nat_trans_eq; try exact (homset_property (functor_category _ _)).
      intro a.
      apply nat_trans_eq; try exact (homset_property (productwithfixedelement _ _)).
      intro b. cbn.
      apply pathsdirprod.
      + rewrite id_left. apply id_right.
      + apply idpath.
    - intro A.
      apply nat_trans_eq; try exact (homset_property (functor_category _ _)).
      intro a.
      apply nat_trans_eq; try exact (homset_property (productwithfixedelement _ _)).
      intro b. cbn. apply idpath.
    - intros A1 A2 A3 F G.
      apply nat_trans_eq; try exact (homset_property (functor_category _ _)).
      intro a.
      apply nat_trans_eq; try exact (homset_property (productwithfixedelement _ _)).
      intro b. cbn.
      apply pathsdirprod.
      + do 6 rewrite id_right. rewrite id_left. apply pathsinv0, functor_id.
      + etrans.
        2: { do 3 rewrite id_right. apply idpath. }
        apply idpath.
  Qed.

  Definition coevaluation_pstrans: pstrans (id_psfunctor CAT) (comp_psfunctor R L).
  Proof.
    use make_pstrans.
    - exact coevaluation_pstrans_data.
    - exact coevaluation_is_pstrans.
  Defined.


  Definition evaluation_pstrans_data: pstrans_data (comp_psfunctor L R) (id_psfunctor CAT).
  Proof.
    use make_pstrans_data.
    - intro A. apply evaluation_functor.
    - intros A A' F.
      apply nat_iso_to_invertible_2cell.
      use make_nat_iso.
      + use make_nat_trans.
        * intro Gb. apply identity.
        * intros Gb Gb' βg. induction Gb as [G b]. induction Gb' as [G' b']. induction βg as [β g].
          simpl in *.
          rewrite id_left, id_right.
          apply functor_comp.
      + intro a.
        apply is_iso_from_is_z_iso.
        cbn.
        apply identity_is_z_iso.
  Defined.

  Lemma evaluation_is_pstrans: is_pstrans evaluation_pstrans_data.
  Proof.
    repeat split.
    - intros A A' F F' α.
      apply nat_trans_eq; try exact (homset_property A').
      intro Gb. induction Gb as [G b]. cbn.
      do 2 rewrite functor_id. do 2 rewrite id_left. apply id_right.
    - intro A.
      apply nat_trans_eq; try exact (homset_property A).
      intro Gb. induction Gb as [G b]. cbn.
      do 5 rewrite id_left. rewrite id_right. apply pathsinv0, functor_id.
    - intros A1 A2 A3 F H.
      apply nat_trans_eq; try exact (homset_property A3).
      intro Gb. induction Gb as [G b]. cbn.
      do 7 rewrite id_right.
      do 3 rewrite functor_id.
      rewrite id_left, id_right. apply pathsinv0, functor_id.
  Qed.

  Definition evaluation_pstrans: pstrans (comp_psfunctor L R) (id_psfunctor CAT).
  Proof.
    use make_pstrans.
    - exact evaluation_pstrans_data.
    - exact evaluation_is_pstrans.
  Defined.

  Definition currying_biajd_unit_counit: left_biadj_unit_counit L.
  Proof.
    use (make_biadj_unit_counit R).
    - exact coevaluation_pstrans.
    - exact evaluation_pstrans.
  Defined.

  Definition currying_biajd_triangle_l_law: biadj_triangle_l_law currying_biajd_unit_counit.
  Proof.
    red.
    use make_invertible_modification.
    - intro A.
      apply nat_iso_to_invertible_2cell.
      use make_nat_iso.
      + use make_nat_trans.
        * intro ab. apply identity.
        * intros ab ab' fg.
          cbn.
          apply pathsdirprod.
          -- rewrite id_right. apply idpath.
          -- rewrite id_left. rewrite id_right. apply id_right.
      + intro ab.
        apply is_iso_from_is_z_iso.
        cbn.
        set (aux := identity(C:=pr1(productwithfixedelement _ _)) ab).
        change (is_z_isomorphism aux).
        apply identity_is_z_iso.
    - intros A A' F.
      apply nat_trans_eq; try exact (homset_property (productwithfixedelement _ _)).
      intro ab. cbn.
      apply pathsdirprod.
      + do 2 rewrite functor_id. repeat rewrite id_left. apply idpath.
      + repeat rewrite id_left. apply idpath.
  Defined.

  Definition currying_biajd_triangle_r_law: biadj_triangle_r_law currying_biajd_unit_counit.
  Proof.
    red.
    use make_invertible_modification.
    - intro A.
      apply nat_iso_to_invertible_2cell.
      use make_nat_iso.
      + use make_nat_trans.
        * intro G. cbn in G.
          use make_nat_trans.
          -- intro b. apply identity.
          -- intros b b' g.
             cbn. rewrite id_left, id_right. apply id_right.
        * intros G G' β.
          apply nat_trans_eq; try exact (homset_property A).
          intro b.
          cbn. rewrite id_right. apply cancel_postcomposition. apply functor_id.
      + intro G.
        apply is_iso_from_is_z_iso.
        apply nat_trafo_z_iso_if_pointwise_z_iso.
        intro b. cbn.
        apply identity_is_z_iso.
    - intros A A' F.
      apply nat_trans_eq; try exact (homset_property (functor_category _ _)).
      intro G. cbn.
      apply nat_trans_eq; try exact (homset_property A').
      intro b.
      cbn.
      repeat rewrite id_left.
      repeat rewrite functor_id.
      repeat rewrite id_left.
      rewrite id_right. apply pathsinv0, functor_id.
  Defined.

  Definition currying_biajd: left_biadj_data L.
  Proof.
    use make_biadj_data.
    - exact currying_biajd_unit_counit.
    - exact currying_biajd_triangle_l_law.
    - exact currying_biajd_triangle_r_law.
  Defined.

End Currying.
