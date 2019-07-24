(*
The univalent bicategory of pointed groupoid.
*)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.TransportMorphisms.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OneTypes.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Groupoids.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.BicatOfCats.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.PathGroupoid.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.PointedOneTypes.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.

Local Open Scope cat.
Local Open Scope bicategory_scope.


Definition pgrpds_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells grpds.
Proof.
  use tpair.
  - use tpair.
    + (** Objects and 1-cells *)
      use tpair.
      * (** Objects over a groupoid are points of X *)
        intro G. apply G.
      * cbn. intros G1 G2 x y F.
        (** 1-cells over F are properties: F preserves points *)
        exact (iso (pr1 F x) y).
    + (** Identity and composition of 1-cells: composition of properties *)
      use tpair.
      * cbn. intros G x. exact (identity_iso x).
      * cbn. intros G1 G2 G3 F1 F2 x y z.
        intros i1 i2.
        exact (iso_comp (functor_on_iso (pr1 F2) i1) i2).
  - cbn. hnf. intros G1 G2 F1 F2 α. cbn in *.
    (** Two cells over α : F1 ==> F2 *)
    intros x y i1 i2.
    unfold total_prebicat_cell_struct in α.
    cbn in *.
    (* α on the point of G1 is iso to identity *)
    exact (pr1 α x · i2 = i1).
Defined.

Definition pgrpds_disp_prebicat_ops : disp_prebicat_ops pgrpds_disp_prebicat_1_id_comp_cells.
Proof.
  repeat split; cbn.
  - intros G1 G2 F x y i.
    apply id_left.
  - intros G1 G2 F x y i.
    rewrite functor_id.
    apply idpath.
  - intros G1 G2 F x y i.
    rewrite id_left.
    rewrite id_right.
    apply idpath.
  - intros G1 G2 F x y i.
    rewrite functor_id.
    rewrite !id_left.
    apply idpath.
  - intros G1 G2 F x y i.
    rewrite id_left.
    rewrite id_right.
    apply idpath.
  - intros G1 G2 G3 G4 F1 F2 F3 x y z w i1 i2 i3.
    rewrite id_left.
    rewrite functor_comp.
    rewrite assoc.
    apply idpath.
  - intros G1 G2 G3 G4 F1 F2 F3 x y z w i1 i2 i3.
    rewrite id_left.
    rewrite functor_comp.
    rewrite assoc.
    apply idpath.
  - intros G1 G2 F1 F2 F3 α β x y i1 i2 i3 p1 p2.
    rewrite assoc'.
    rewrite p2.
    apply p1.
  - intros G1 G2 G3 F1 F2 F3 α x y z i1 i2 i3 p.
    rewrite assoc.
    rewrite <- (nat_trans_ax (pr1 α)).
    rewrite assoc'.
    apply maponpaths.
    apply p.
  - intros G1 G2 G3 F1 F2 F3 α x y z i1 i2 i3 p.
    rewrite assoc.
    apply (maponpaths (λ z, z · i3)).
    rewrite <- functor_comp.
    apply maponpaths.
    apply p.
Qed.

Definition pgrpds_prebicat : disp_prebicat grpds.
Proof.
  use tpair.
  - exists pgrpds_disp_prebicat_1_id_comp_cells.
    apply pgrpds_disp_prebicat_ops.
  - repeat split; intro; intros.
    + apply (pr1 b).
    + apply (pr1 b).
    + apply (pr1 b).
    + apply (pr1 c).
    + apply (pr1 c).
    + apply (pr1 c).
    + apply (pr1 c).
    + apply (pr1 b).
    + apply (pr1 b).
    + apply (pr1 d).
    + apply (pr1 d).
    + apply (pr1 d).
    + apply (pr1 c).
    + apply (pr1 b).
    + apply (pr1 b).
    + apply (pr1 b).
    + apply (pr1 b).
    + apply (pr1 d).
    + apply (pr1 d).
    + apply (pr1 c).
    + apply (pr1 e).
Defined.

Definition pgrpds_disp : disp_bicat grpds.
Proof.
  use tpair.
  - apply pgrpds_prebicat.
  - repeat intro. apply hlevelntosn.
    apply (pr1 b).
Defined.

Definition pgrpds : bicat := total_bicat pgrpds_disp.

(*
The bicategory of pointed groupoids is biequivalent to the bicategory of pointed 1types.
*)


Lemma grpd_all_homot
      {X : UU}
      (HX : isofhlevel 3 X)
      {x y : X}
      {p q : x = y}
      (s1 s2 : p = q)
  : s1 = s2.
Proof.
  apply (HX x y p q s1 s2).
Qed.

Definition disp_objects_of_pgrpd_data : disp_psfunctor_data pgrpds_disp p1types_disp objects_of_grpd.
Proof.
  use make_disp_psfunctor_data.
  - exact (λ G x, x).
  - intros G1 G2 F x y i.
    exact (isotoid _ (pr21 G2) i).
  - intros G1 G2 F1 F2 α x y i1 i2 p.
    cbn in *.
    rewrite transportf_id2.
    apply path_inv_rotate_ll.
    rewrite <- isotoid_comp.
    apply maponpaths.
    apply eq_iso.
    cbn.
    refine (! p).
  - intros G x.
    repeat use tpair.
    + cbn.
      rewrite isotoid_identity_iso.
      apply idpath.
    + cbn.
      rewrite isotoid_identity_iso.
      apply idpath.
    + apply grpd_all_homot.
      exact (univalent_category_has_groupoid_ob (pr1 G)).
    + apply grpd_all_homot.
      exact (univalent_category_has_groupoid_ob (pr1 G)).
  - intros G1 G2 G3 F1 F2 x y z i1 i2.
    repeat use tpair.
    + cbn.
      rewrite (maponpaths_isotoid _ _ _ (pr21 G2) (pr21 G3)).
      rewrite <- isotoid_comp.
      apply idpath.
    + cbn.
      rewrite (maponpaths_isotoid _ _ _ (pr21 G2) (pr21 G3)).
      rewrite <- isotoid_comp.
      apply idpath.
    + apply grpd_all_homot.
      exact (univalent_category_has_groupoid_ob (pr1 G3)).
    + apply grpd_all_homot.
      exact (univalent_category_has_groupoid_ob (pr1 G3)).
Defined.

Definition disp_objects_of_pgrpd_laws
  : is_disp_psfunctor pgrpds_disp p1types_disp objects_of_grpd disp_objects_of_pgrpd_data.
Proof.
  repeat use tpair; intro; intros.
  - apply grpd_all_homot.
    exact (univalent_category_has_groupoid_ob (pr1 b)).
  - apply grpd_all_homot.
    exact (univalent_category_has_groupoid_ob (pr1 b)).
  - apply grpd_all_homot.
    exact (univalent_category_has_groupoid_ob (pr1 b)).
  - apply grpd_all_homot.
    exact (univalent_category_has_groupoid_ob (pr1 b)).
  - apply grpd_all_homot.
    exact (univalent_category_has_groupoid_ob (pr1 d)).
  - apply grpd_all_homot.
    exact (univalent_category_has_groupoid_ob (pr1 c)).
  - apply grpd_all_homot.
    exact (univalent_category_has_groupoid_ob (pr1 c)).
Qed.

Definition disp_objects_of_pgrpd : disp_psfunctor pgrpds_disp p1types_disp objects_of_grpd
  := disp_objects_of_pgrpd_data ,, disp_objects_of_pgrpd_laws.

Definition disp_path_pgroupoid_data : disp_psfunctor_data p1types_disp pgrpds_disp path_groupoid.
Proof.
  use make_disp_psfunctor_data.
  - exact (λ X x, x).
  - intros X Y f x y p.
    exact (@idtoiso (pr11 (path_univalent_groupoid (pr2 Y))) _ _ p).
  - intros X Y f g α x y p q αα.
    cbn in *.
    induction (α x).
    cbn in *.
    apply maponpaths.
    apply maponpaths.
    exact (! αα).
  - intros X x.
    repeat use tpair.
    + apply idpath.
    + apply idpath.
    + apply grpd_all_homot.
      exact (one_type_isofhlevel X).
    + apply grpd_all_homot.
      exact (one_type_isofhlevel X).
  - intros X Y Z f g x y z p q.
    repeat use tpair.
    + induction p. induction q.
      apply idpath.
    + induction p. induction q.
      apply idpath.
    + apply grpd_all_homot.
      exact (one_type_isofhlevel Z).
    + apply grpd_all_homot.
      exact (one_type_isofhlevel Z).
Defined.

Definition disp_path_pgroupoid_laws
  : is_disp_psfunctor p1types_disp pgrpds_disp path_groupoid disp_path_pgroupoid_data.
Proof.
  repeat use tpair; intro; intros.
  - apply grpd_all_homot.
    exact (one_type_isofhlevel b).
  - apply grpd_all_homot.
    exact (one_type_isofhlevel b).
  - apply grpd_all_homot.
    exact (one_type_isofhlevel b).
  - apply grpd_all_homot.
    exact (one_type_isofhlevel b).
  - apply grpd_all_homot.
    exact (one_type_isofhlevel d).
  - apply grpd_all_homot.
    exact (one_type_isofhlevel c).
  - apply grpd_all_homot.
    exact (one_type_isofhlevel c).
Qed.

Definition disp_path_pgroupoid
  : disp_psfunctor p1types_disp pgrpds_disp path_groupoid
  := disp_path_pgroupoid_data ,, disp_path_pgroupoid_laws.
