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
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.PathGroupoid.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.PointedOneTypes.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBiequivalence.

Local Open Scope cat.
Local Open Scope bicategory_scope.


Definition pgrpds_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells grpds.
Proof.
  use tpair.
  - use tpair.
    + (** Objects and 1-cells *)
      use tpair.
      * (** Objects over a groupoid are points of X *)
        exact (λ G, pr11 G).
      * cbn. intros G1 G2 x y F.
        (** 1-cells over F are properties: F preserves points *)
        exact (iso (pr1 F x) y).
    + (** Identity and composition of 1-cells: composition of properties *)
      use tpair.
      * exact (λ G x, identity_iso x).
      * intros G1 G2 G3 F1 F2 x y z i1 i2.
        exact (iso_comp (functor_on_iso (pr1 F2) i1) i2).
  - intros G1 G2 F1 F2 α x y i1 i2. cbn in *.
    (** Two cells over α : F1 ==> F2 *)
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

Definition pgrpds_prebicat_laws
  : disp_prebicat_laws (pgrpds_disp_prebicat_1_id_comp_cells,, pgrpds_disp_prebicat_ops).
Proof.
  cbn. repeat split; intro; intros.
  - apply (pr1 b).
  - apply (pr1 b).
  - apply (pr1 b).
  - apply (pr1 c).
  - apply (pr1 c).
  - apply (pr1 c).
  - apply (pr1 c).
  - apply (pr1 b).
  - apply (pr1 b).
  - apply (pr1 d).
  - apply (pr1 d).
  - apply (pr1 d).
  - apply (pr1 c).
  - apply (pr1 b).
  - apply (pr1 b).
  - apply (pr1 b).
  - apply (pr1 b).
  - apply (pr1 d).
  - apply (pr1 d).
  - apply (pr1 c).
  - apply (pr1 e).
Qed.

Definition pgrpds_prebicat : disp_prebicat grpds.
Proof.
  use tpair.
  - exists pgrpds_disp_prebicat_1_id_comp_cells.
    apply pgrpds_disp_prebicat_ops.
  - exact pgrpds_prebicat_laws.
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

(* THIS LEMMA SHOULD BE MOVED SOMEWHERE ELSE *)
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

(* Note: this definition is opaque, because the 2-cells form a proposition *)
Lemma disp_invertible_2cell_pgrpd
      {G1 G2 : grpds} {F1 F2 : G1 --> G2} {n : invertible_2cell F1 F2}
      {pG1 : pgrpds_disp G1} {pG2 : pgrpds_disp G2}
      {pF1 : pG1 -->[ F1 ] pG2} {pF2 : pG1 -->[ F2 ] pG2}
      (pn : pF1 ==>[ n ] pF2)
  : disp_invertible_2cell n pF1 pF2.
Proof.
  repeat use tpair.
  - exact pn.
  - cbn in *.
    rewrite <- pn.
    rewrite assoc.
    etrans.
    {
      apply maponpaths_2.
      apply (nat_trans_eq_pointwise (maponpaths pr1 (vcomp_lid (pr2 n)))).
    }
    apply id_left.
  - apply (pr1 G2).
  - apply (pr1 G2).
Qed.

Lemma disp_invertible_2cell_p1types
      {X Y : one_types} {f1 f2 : X --> Y} {p : invertible_2cell f1 f2}
      {pX : p1types_disp X} {pY : p1types_disp Y}
      {pf1 : pX -->[ f1 ] pY} {pf2 : pX -->[ f2 ] pY}
      (pp : pf1 ==>[ p ] pf2)
  : disp_invertible_2cell p pf1 pf2.
Proof.
  cbn in *.
  repeat use tpair.
  - exact pp.
  - cbn in *.
    rewrite <- pp.
    rewrite transport_f_f.
    refine (transportb (λ z, transportf _ z _ = _) _ _).
    { exact (maponpaths (λ z, z pX) (vcomp_rinv p)). }
    apply idpath.
  - apply grpd_all_homot.
    apply one_type_isofhlevel.
  - apply grpd_all_homot.
    apply one_type_isofhlevel.
Admitted.

Definition disp_objects_of_pgrpd_data : disp_psfunctor_data pgrpds_disp p1types_disp objects_of_grpd.
Proof.
  use make_disp_psfunctor_data.
  - exact (λ G x, x).
  - intros G1 G2 F x y i.
    exact (isotoid _ (pr21 G2) i).
  - abstract
      (intros G1 G2 F1 F2 α x y i1 i2 p ;
       cbn in * ;
       rewrite transportf_id2 ;
       apply path_inv_rotate_ll ;
       rewrite <- isotoid_comp ;
       apply maponpaths ;
       apply eq_iso ;
       cbn ;
       refine (! p)).
  - abstract
      (intros G x ;
       apply disp_invertible_2cell_p1types ;
       cbn ;
       rewrite isotoid_identity_iso ;
       apply idpath).
  - abstract
      (intros G1 G2 G3 F1 F2 x y z i1 i2 ;
       apply disp_invertible_2cell_p1types ;
       cbn ;
       rewrite (maponpaths_isotoid _ _ _ (pr21 G2) (pr21 G3)) ;
       rewrite <- isotoid_comp ;
       apply idpath).
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
    exact (p ,, pr2 (path_groupoid Y) _ _ p).
  - abstract
      (intros X Y f g α x y p q αα ;
       cbn in * ;
       induction (α x) ;
       exact (! αα)).
  - abstract
      (intros X x ;
       apply disp_invertible_2cell_pgrpd ;
       apply idpath).
  - abstract
      (intros X Y Z f g x y z p q ;
       apply disp_invertible_2cell_pgrpd ;
       apply idpath).
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

Definition iso_comp_rid {C : precategory} {x y : C} (f : iso x y)
  : iso_comp f (identity_iso y) = f.
Proof.
  use eq_iso.
  cbn.
  rewrite id_right.
  apply idpath.
Defined.

Definition iso_comp_lid {C : precategory} {x y : C} (f : iso x y)
  : iso_comp (identity_iso x) f = f.
Proof.
  use eq_iso.
  cbn.
  rewrite id_left.
  apply idpath.
Defined.

Definition functor_on_iso_on_identity {C D : precategory} (F : functor C D) {x : C}
  : functor_on_iso F (identity_iso x) = identity_iso (F x).
Proof.
  use eq_iso.
  cbn.
  rewrite functor_id.
  apply idpath.
Defined.

Definition disp_path_pgroupoid_counit_data
  : disp_pstrans_data (disp_pseudo_comp _ _ _ _ _ disp_objects_of_pgrpd disp_path_pgroupoid)
                      (disp_pseudo_id _)
                      path_groupoid_counit.
Proof.
  use make_disp_pstrans_data.
  - exact (λ G x, identity_iso x).
  - abstract
      (intros G1 G2 F x y i ;
       cbn in * ;
       rewrite functor_on_iso_on_identity ;
       rewrite iso_comp_lid ;
       rewrite iso_comp_rid ;
       apply disp_invertible_2cell_pgrpd ;
       cbn ;
       rewrite id_left ;
       rewrite idtoiso_isotoid ;
       apply idpath).
Defined.

Definition disp_path_pgroupoid_counit_laws
  : is_disp_pstrans (disp_pseudo_comp _ _ _ _ _ disp_objects_of_pgrpd disp_path_pgroupoid)
                    (disp_pseudo_id _)
                    path_groupoid_counit
                    disp_path_pgroupoid_counit_data.
Proof.
  repeat split; intro; intros.
  - apply (pr1 y).
  - apply (pr1 x).
  - apply (pr1 z).
Qed.

Definition disp_path_pgroupoid_counit
  : disp_pstrans (disp_pseudo_comp _ _ _ _ _ disp_objects_of_pgrpd disp_path_pgroupoid)
                 (disp_pseudo_id _)
                 path_groupoid_counit
  := disp_path_pgroupoid_counit_data ,, disp_path_pgroupoid_counit_laws.

Definition disp_path_pgroupoid_unit_data
  : disp_pstrans_data (disp_pseudo_id _)
                      (disp_pseudo_comp _ _ _ _ _ disp_path_pgroupoid disp_objects_of_pgrpd)
                      path_groupoid_unit.
Proof.
  use make_disp_pstrans_data.
  - exact (λ X x, idpath x).
  - intros X Y f x y p.
    cbn in *.
    rewrite pathscomp0rid.
    rewrite maponpathsidfun.
    apply disp_invertible_2cell_p1types.
    cbn.
    unfold idfun.
    refine (!((!_)@(!_))).
    apply (isotoid_idtoiso _ (is_univalent_path_groupoid (pr1 Y) (pr2 Y))).
    apply maponpaths.
    apply eq_iso.
    cbn.
    induction p.
    apply idpath.
Defined.

Definition disp_path_pgroupoid_unit_laws
  : is_disp_pstrans (disp_pseudo_id _)
                    (disp_pseudo_comp _ _ _ _ _ disp_path_pgroupoid disp_objects_of_pgrpd)
                    path_groupoid_unit
                    disp_path_pgroupoid_unit_data.
Proof.
  repeat split; intro; intros.
  - apply y.
  - apply x.
  - apply z.
Qed.

Definition disp_path_pgroupoid_unit
  : disp_pstrans (disp_pseudo_id _)
                 (disp_pseudo_comp _ _ _ _ _ disp_path_pgroupoid disp_objects_of_pgrpd)
                 path_groupoid_unit
                 := disp_path_pgroupoid_unit_data ,, disp_path_pgroupoid_unit_laws.

(*
Definition disp_invertible_2cell_of_1types
           {X Y : one_type} {f g : X → Y} {h : f ~ g}
           {x : X} {y : Y} {p : f x = y} {q : g x = y}
           (hh : @disp_2cells _ p1types_disp X Y f g h x y p q)
  : UU.
Proof.
  Check @disp_invertible_2cell _ p1types_disp X Y f g x y (invhomot h).
  Locate "~".
  Search homot.
  Check .
  cbn.
  Check.
  refine ( _ _ _ _ _ _).
           (α : disp_2cells α ff gg)
  : disp_invertible_2cell α ff gg.
 *)

Definition disp_path_pgroupoid_counit_inv_data
  : disp_pstrans_data (disp_pseudo_id _)
                      (disp_pseudo_comp _ _ _ _ _ disp_objects_of_pgrpd disp_path_pgroupoid)
                      path_groupoid_counit_inv.
Proof.
  use make_disp_pstrans_data.
  - intros G x.
    exact (@identity_iso (pr11 (path_groupoid (objects_of_grpd G))) x).
  - intros G1 G2 F x y i.
    cbn.
    rewrite iso_comp_rid.
    rewrite functor_on_iso_on_identity.
    rewrite iso_comp_lid.
    repeat use tpair.
    + cbn.
      apply maponpaths.
      use eq_iso.
      apply idpath.
    + cbn.
      apply maponpaths.
      use eq_iso.
      apply idpath.
    + apply (pr1 (path_groupoid (objects_of_grpd G2))).
    + apply (pr1 (path_groupoid (objects_of_grpd G2))).
Defined.

Definition disp_path_pgroupoid_counit_inv_laws
  : is_disp_pstrans (disp_pseudo_id _)
                     (disp_pseudo_comp _ _ _ _ _ disp_objects_of_pgrpd disp_path_pgroupoid)
                     path_groupoid_counit_inv
                     disp_path_pgroupoid_counit_inv_data.
Proof.
  repeat use tpair; intro; intros.
  - apply (pr1 (path_groupoid (objects_of_grpd y))).
  - apply (pr1 (path_groupoid (objects_of_grpd x))).
  - apply (pr1 (path_groupoid (objects_of_grpd z))).
Qed.

Definition disp_path_pgroupoid_counit_inv
  : disp_pstrans (disp_pseudo_id _)
                 (disp_pseudo_comp _ _ _ _ _ disp_objects_of_pgrpd disp_path_pgroupoid)
                 path_groupoid_counit_inv
  := disp_path_pgroupoid_counit_inv_data ,, disp_path_pgroupoid_counit_inv_laws.

Definition disp_path_pgroupoid_unit_inv_data
  : disp_pstrans_data (disp_pseudo_comp _ _ _ _ _ disp_path_pgroupoid disp_objects_of_pgrpd)
                      (disp_pseudo_id _)
                      path_groupoid_unit_inv.
Proof.
  use make_disp_pstrans_data.
  - exact (λ X x, idpath x).
  - intros X Y f x y p.
    cbn in *.
    rewrite pathscomp0rid.
    rewrite maponpathsidfun.
    repeat use tpair.
    + refine (!_@_).
      apply (isotoid_idtoiso _ (is_univalent_path_groupoid (pr1 Y) (pr2 Y))).
      apply maponpaths.
      induction p.
      use eq_iso.
      apply idpath.
    + cbn.
      refine (!(!_@_)).
      apply (isotoid_idtoiso _ (is_univalent_path_groupoid (pr1 Y) (pr2 Y))).
      unfold idfun.
      apply maponpaths.
      induction p.
      use eq_iso.
      apply idpath.
    + apply Y.
    + apply Y.
Defined.

Definition disp_path_pgroupoid_unit_inv_laws
  : is_disp_pstrans (disp_pseudo_comp _ _ _ _ _ disp_path_pgroupoid disp_objects_of_pgrpd)
                    (disp_pseudo_id _)
                    path_groupoid_unit_inv
                    disp_path_pgroupoid_unit_inv_data.
Proof.
  repeat use tpair; intro; intros.
  - apply y.
  - apply x.
  - apply z.
Qed.

Definition disp_path_pgroupoid_unit_inv
  : disp_pstrans (disp_pseudo_comp _ _ _ _ _ disp_path_pgroupoid disp_objects_of_pgrpd)
                 (disp_pseudo_id _)
                 path_groupoid_unit_inv
  := disp_path_pgroupoid_unit_inv_data ,, disp_path_pgroupoid_unit_inv_laws.


Definition is_disp_biequiv_unit_counit_path_pgroupoid :
  is_disp_biequivalence_unit_counit _ _
                                    (unit_counit_from_is_biequivalence is_biequiv_path_groupoid)
                                    disp_path_pgroupoid disp_objects_of_pgrpd.
Proof.
  use tpair.
  - exact disp_path_pgroupoid_unit_inv.
  - exact disp_path_pgroupoid_counit.
Defined.

Definition TODO {A : UU} : A.
Admitted.

Definition disp_path_pgroupoid_unit_unit_inv_data :
  disp_invmodification_data _ _ _ _
    (disp_ps_comp _ _ _ _ _ _ _ _ _ _ disp_path_pgroupoid_unit disp_path_pgroupoid_unit_inv)
    (disp_id_trans _)
    (unitcounit_of_is_biequivalence is_biequiv_path_groupoid).
Proof.
  intros X x.
  repeat use tpair.
  - apply idpath.
  - apply idpath.
  - apply X.
  - apply X.
Defined.

Opaque disp_ps_comp ps_comp.
Definition disp_path_pgroupoid_unit_unit_inv_laws :
  is_disp_invmodification _ _ _ _
    (disp_ps_comp _ _ _ _ _ _ _ _ _ _ disp_path_pgroupoid_unit disp_path_pgroupoid_unit_inv)
    (disp_id_trans _)
    (unitcounit_of_is_biequivalence is_biequiv_path_groupoid)
    disp_path_pgroupoid_unit_unit_inv_data.
Proof.
  intros X Y f x y p.
  apply TODO.
Qed.

Definition disp_path_pgroupoid_unit_unit_inv :
  disp_invmodification _ _ _ _
    (disp_ps_comp _ _ _ _ _ _ _ _ _ _ disp_path_pgroupoid_unit disp_path_pgroupoid_unit_inv)
    (disp_id_trans _)
    (unitcounit_of_is_biequivalence is_biequiv_path_groupoid)
  := disp_path_pgroupoid_unit_unit_inv_data ,, disp_path_pgroupoid_unit_unit_inv_laws.


Definition disp_path_pgroupoid_unit_inv_unit :
  disp_invmodification _ _ _ _
    (disp_ps_comp _ _ _ _ _ _ _ _ _ _ disp_path_pgroupoid_unit_inv disp_path_pgroupoid_unit)
    (disp_id_trans _)
    (unitunit_of_is_biequivalence is_biequiv_path_groupoid).
Admitted.

Definition disp_path_pgroupoid_counit_inv_counit :
  disp_invmodification _ _ _ _
    (disp_ps_comp _ _ _ _ _ _ _ _ _ _ disp_path_pgroupoid_counit_inv disp_path_pgroupoid_counit)
    (disp_id_trans _)
    (counitcounit_of_is_biequivalence is_biequiv_path_groupoid).
Admitted.

Definition disp_path_pgroupoid_counit_counit_inv :
  disp_invmodification _ _ _ _
    (disp_ps_comp _ _ _ _ _ _ _ _ _ _ disp_path_pgroupoid_counit disp_path_pgroupoid_counit_inv)
    (disp_id_trans _)
    (counitunit_of_is_biequivalence is_biequiv_path_groupoid).
Admitted.

Definition disp_biequiv_data_unit_counit_path_pgroupoid :
  disp_is_biequivalence_data _ _
                             (adjoints_from_is_biequivalence is_biequiv_path_groupoid)
                             is_disp_biequiv_unit_counit_path_pgroupoid.
Proof.
  use tpair.
  - exact disp_path_pgroupoid_unit.
  - use tpair.
    + exact disp_path_pgroupoid_counit_inv.
    + use tpair.
      * simpl.
        exact disp_path_pgroupoid_unit_unit_inv.
      * use tpair.
        -- exact disp_path_pgroupoid_unit_inv_unit.
        -- use tpair.
           ++ exact disp_path_pgroupoid_counit_inv_counit.
           ++ exact disp_path_pgroupoid_counit_counit_inv.
Defined.
