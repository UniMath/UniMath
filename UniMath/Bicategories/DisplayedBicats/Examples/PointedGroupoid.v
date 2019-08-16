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
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Examples.Groupoids.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Biequivalence.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.PathGroupoid.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.PointedOneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiequivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.

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

Definition pgrpds_disp_2cells_isaprop : disp_2cells_isaprop pgrpds_disp.
Proof.
  intros G₁ G₂; intros.
  apply (pr1 G₂).
Qed.

Definition pgrpds_disp_locally_groupoid : disp_locally_groupoid pgrpds_disp.
Proof.
  use make_disp_locally_groupoid.
  - intros G₁ G₂ F₁ F₂ n pG₁ pG₂ pF₁ pF₂ pn.
    cbn in *.
    rewrite <- pn.
    rewrite assoc.
    etrans.
    {
      apply maponpaths_2.
      apply (nat_trans_eq_pointwise (maponpaths pr1 (vcomp_lid (pr2 n)))).
    }
    apply id_left.
  - exact pgrpds_disp_2cells_isaprop.
Qed.

Definition p1types_disp_2cells_isaprop : disp_2cells_isaprop p1types_disp.
Proof.
  intros A B; intros.
  exact (pr2 B _ _ _ _).
Qed.

Definition p1types_disp_locally_groupoid : disp_locally_groupoid p1types_disp.
Proof.
  use make_disp_locally_groupoid.
  - intros G₁ G₂ F₁ F₂ n pG₁ pG₂ pF₁ pF₂ pn.
    cbn in *.
    rewrite <- pn.
    rewrite transport_f_f.
    refine (transportb (λ z, transportf _ z _ = _) _ _).
    { exact (maponpaths (λ z, z pG₁) (vcomp_rinv n)). }
    apply idpath.
  - exact p1types_disp_2cells_isaprop.
Qed.

Definition disp_objects_of_pgrpd : disp_psfunctor pgrpds_disp p1types_disp objects_of_grpd.
Proof.
  use make_disp_psfunctor.
  - exact p1types_disp_2cells_isaprop.
  - exact p1types_disp_locally_groupoid.
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
       cbn ;
       rewrite isotoid_identity_iso ;
       apply idpath).
  - abstract
      (intros G1 G2 G3 F1 F2 x y z i1 i2 ;
       cbn ;
       rewrite (maponpaths_isotoid _ _ _ (pr21 G2) (pr21 G3)) ;
       rewrite <- isotoid_comp ;
       apply idpath).
Defined.

Definition disp_path_pgroupoid : disp_psfunctor p1types_disp pgrpds_disp path_groupoid.
Proof.
  use make_disp_psfunctor.
  - exact pgrpds_disp_2cells_isaprop.
  - exact pgrpds_disp_locally_groupoid.
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
       apply idpath).
  - abstract
      (intros X Y Z f g x y z p q ;
       apply idpath).
Defined.

Definition disp_path_pgroupoid_counit
  : disp_pstrans (disp_pseudo_comp _ _ _ _ _ disp_objects_of_pgrpd disp_path_pgroupoid)
                 (disp_pseudo_id _)
                 path_groupoid_counit.
Proof.
  use make_disp_pstrans.
  - exact pgrpds_disp_2cells_isaprop.
  - exact pgrpds_disp_locally_groupoid.
  - exact (λ G x, identity_iso x).
  - abstract
      (intros G1 G2 F x y i ;
       cbn in * ;
       rewrite idtoiso_isotoid ;
       rewrite functor_id ;
       rewrite !id_left ;
       apply id_right).
Defined.

Definition disp_path_pgroupoid_unit
  : disp_pstrans (disp_pseudo_id _)
                 (disp_pseudo_comp _ _ _ _ _ disp_path_pgroupoid disp_objects_of_pgrpd)
                 path_groupoid_unit.
Proof.
  use make_disp_pstrans.
  - exact p1types_disp_2cells_isaprop.
  - exact p1types_disp_locally_groupoid.
  - exact (λ X x, idpath x).
  - abstract
      (intros X Y f x y p;
       cbn in *;
       rewrite pathscomp0rid;
       rewrite maponpathsidfun;
       cbn;
       refine (_ @ isotoid_idtoiso _ (is_univalent_path_groupoid (pr1 Y) (pr2 Y)) _ _ _);
       apply maponpaths;
       apply eq_iso;
       cbn;
       induction p;
       apply idpath).
Defined.

Definition disp_path_pgroupoid_counit_inv
  : disp_pstrans (disp_pseudo_id _)
                 (disp_pseudo_comp _ _ _ _ _ disp_objects_of_pgrpd disp_path_pgroupoid)
                 path_groupoid_counit_inv.
Proof.
  use make_disp_pstrans.
  - exact pgrpds_disp_2cells_isaprop.
  - exact pgrpds_disp_locally_groupoid.
  - intros G x.
    exact (@identity_iso (pr11 (path_groupoid (objects_of_grpd G))) x).
  - abstract
      (intros G1 G2 F x y i;
       cbn;
       rewrite pathscomp0rid;
       apply maponpaths;
       use eq_iso;
       apply idpath).
Defined.

Definition disp_path_pgroupoid_unit_inv
  : disp_pstrans (disp_pseudo_comp _ _ _ _ _ disp_path_pgroupoid disp_objects_of_pgrpd)
                 (disp_pseudo_id _)
                 path_groupoid_unit_inv.
Proof.
  use make_disp_pstrans.
  - exact p1types_disp_2cells_isaprop.
  - exact p1types_disp_locally_groupoid.
  - exact (λ X x, idpath x).
  - abstract
      (intros X Y f x y p;
       cbn in *;
       rewrite pathscomp0rid;
       rewrite maponpathsidfun;
       refine (!(isotoid_idtoiso _ (is_univalent_path_groupoid (pr1 Y) (pr2 Y)) _ _ _) @_);
       apply maponpaths;
       induction p;
       use eq_iso;
       apply idpath).
Defined.


Definition is_disp_biequiv_unit_counit_path_pgroupoid :
  is_disp_biequivalence_unit_counit _ _
                                    (unit_counit_from_is_biequivalence is_biequiv_path_groupoid)
                                    disp_path_pgroupoid disp_objects_of_pgrpd.
Proof.
  use tpair.
  - exact disp_path_pgroupoid_unit_inv.
  - exact disp_path_pgroupoid_counit.
Defined.

Definition disp_path_pgroupoid_unit_unit_inv :
  disp_invmodification _ _ _ _
    (disp_ps_comp _ _ _ _ _ _ _ _ _ _ disp_path_pgroupoid_unit disp_path_pgroupoid_unit_inv)
    (disp_id_trans _)
    (unitcounit_of_is_biequivalence is_biequiv_path_groupoid).
Proof.
  use make_disp_invmodification.
  - exact p1types_disp_2cells_isaprop.
  - exact p1types_disp_locally_groupoid.
  - abstract
      (intros X x;
       apply idpath).
Defined.

Definition disp_path_pgroupoid_unit_inv_unit :
  disp_invmodification _ _ _ _
    (disp_ps_comp _ _ _ _ _ _ _ _ _ _ disp_path_pgroupoid_unit_inv disp_path_pgroupoid_unit)
    (disp_id_trans _)
    (unitunit_of_is_biequivalence is_biequiv_path_groupoid).
Proof.
  use make_disp_invmodification.
  - exact p1types_disp_2cells_isaprop.
  - exact p1types_disp_locally_groupoid.
  - abstract
      (intros X x;
       apply idpath).
Defined.

Definition disp_path_pgroupoid_counit_inv_counit :
  disp_invmodification _ _ _ _
    (disp_ps_comp _ _ _ _ _ _ _ _ _ _ disp_path_pgroupoid_counit_inv disp_path_pgroupoid_counit)
    (disp_id_trans _)
    (counitcounit_of_is_biequivalence is_biequiv_path_groupoid).
Proof.
  use make_disp_invmodification.
  - exact pgrpds_disp_2cells_isaprop.
  - exact pgrpds_disp_locally_groupoid.
  - abstract
      (intros G x;
       cbn;
       rewrite !id_right;
       apply (iso_inv_after_iso (id₁ x ,, _))).
Defined.

Definition disp_path_pgroupoid_counit_counit_inv :
  disp_invmodification _ _ _ _
    (disp_ps_comp _ _ _ _ _ _ _ _ _ _ disp_path_pgroupoid_counit disp_path_pgroupoid_counit_inv)
    (disp_id_trans _)
    (counitunit_of_is_biequivalence is_biequiv_path_groupoid).
Proof.
  use make_disp_invmodification.
  - exact pgrpds_disp_2cells_isaprop.
  - exact pgrpds_disp_locally_groupoid.
  - abstract
      (intros G x;
       cbn;
       rewrite pathscomp0rid;
       refine (! (isotoid_idtoiso _ (pr21 G) _ _ (idpath _)) @ _);
       apply maponpaths;
       apply eq_iso;
       apply idpath).
Defined.

Definition disp_biequiv_data_unit_counit_path_pgroupoid :
  disp_is_biequivalence_data _ _
                             is_biequiv_path_groupoid
                             is_disp_biequiv_unit_counit_path_pgroupoid.
Proof.
  use tpair.
  - exact disp_path_pgroupoid_unit.
  - use tpair.
    + exact disp_path_pgroupoid_counit_inv.
    + use tpair.
      * simpl.
        use tpair.
        -- exact disp_path_pgroupoid_unit_unit_inv.
        -- exact disp_path_pgroupoid_unit_inv_unit.
      * use tpair.
        -- exact disp_path_pgroupoid_counit_inv_counit.
        -- exact disp_path_pgroupoid_counit_counit_inv.
Defined.
