(******************************************************************

 Opposites of displayed categories

 If we have a displayed category `D` on a category `C`, then we can
 define a displayed category on `C^op`

 ******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.
Local Open Scope mor_disp.

Section OpDispCat.
  Context {C : category}
          (D : disp_cat C).

  Definition op_disp_cat_ob_mor
    : disp_cat_ob_mor C^op.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, D x).
    - exact (λ x y xx yy f, yy -->[ f ] xx).
  Defined.

  Definition op_disp_cat_id_comp
    : disp_cat_id_comp C^op op_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, id_disp _).
    - refine (λ x y z f g xx yy zz ff gg, _) ; cbn in *.
      exact (gg ;; ff).
  Defined.

  Definition op_disp_cat_data
    : disp_cat_data C^op.
  Proof.
    simple refine (_ ,, _).
    - exact op_disp_cat_ob_mor.
    - exact op_disp_cat_id_comp.
  Defined.

  Definition op_disp_cat_axioms
    : disp_cat_axioms C^op op_disp_cat_data.
  Proof.
    repeat split ; cbn ; intros.
    - apply id_right_disp.
    - apply id_left_disp.
    - rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      refine (!_).
      apply transportf_set.
      apply C.
    - apply D.
  Qed.

  Definition op_disp_cat
    : disp_cat C^op.
  Proof.
    simple refine (_ ,, _).
    - exact op_disp_cat_data.
    - exact op_disp_cat_axioms.
  Defined.
End OpDispCat.

Definition to_z_iso_disp_op_disp_cat
           {C : category}
           {D : disp_cat C}
           {x y : C}
           {f : z_iso y x}
           {xx : D x}
           {yy : D y}
           (ff : yy -->[ f ] xx)
           (Hff : is_z_iso_disp f ff)
  : @is_z_iso_disp
      _
      (op_disp_cat D)
      x y
      (opp_z_iso f)
      _ _
      ff.
Proof.
  simple refine (_ ,, _ ,, _).
  - simple refine (transportb
                     (λ z, _ -->[ z ] _)
                     _
                     (inv_mor_disp_from_z_iso Hff)).
    apply idpath.
  - cbn.
    apply inv_mor_after_z_iso_disp.
  - cbn.
    apply z_iso_disp_after_inv_mor.
Defined.

Definition z_iso_disp_to_op_disp_cat
           {C : category}
           {D : disp_cat C}
           {x : C}
           {xx yy : D x}
           (f : z_iso_disp (identity_z_iso x) xx yy)
  : @z_iso_disp _ (op_disp_cat D) _ _ (@identity_z_iso (op_cat C) x) xx yy.
Proof.
  use make_z_iso_disp.
  - exact (inv_mor_disp_from_z_iso f).
  - simple refine (_ ,, _ ,, _).
    + exact (pr1 f).
    + abstract
        (cbn ;
         refine (z_iso_disp_after_inv_mor f @ _) ;
         apply maponpaths_2 ;
         apply homset_property).
    + abstract
        (cbn ;
         refine (inv_mor_after_z_iso_disp f @ _) ;
         apply maponpaths_2 ;
         apply homset_property).
Defined.

Definition z_iso_disp_from_op_disp_cat
           {C : category}
           {D : disp_cat C}
           {x : C}
           {xx yy : D x}
           (f :  @z_iso_disp _ (op_disp_cat D) _ _ (@identity_z_iso C^op x) xx yy)
  : z_iso_disp (identity_z_iso x) xx yy.
Proof.
  use make_z_iso_disp.
  - exact (inv_mor_disp_from_z_iso f).
  - simple refine (_ ,, _ ,, _).
    + exact (pr1 f).
    + abstract
        (cbn ;
         refine (z_iso_disp_after_inv_mor f @ _) ;
         apply maponpaths_2 ;
         apply homset_property).
    + abstract
        (cbn ;
         refine (inv_mor_after_z_iso_disp f @ _) ;
         apply maponpaths_2 ;
         apply homset_property).
Defined.

Definition z_iso_disp_weq_op_disp_cat
           {C : category}
           {D : disp_cat C}
           {x : C}
           (xx yy : D x)
  : @z_iso_disp _ (op_disp_cat D) _ _ (@identity_z_iso C^op x) xx yy
    ≃
    z_iso_disp (identity_z_iso x) xx yy.
Proof.
  use make_weq.
  - exact z_iso_disp_from_op_disp_cat.
  - use gradth.
    + exact z_iso_disp_to_op_disp_cat.
    + abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         apply idpath).
    + abstract
        (intro f ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         apply idpath).
Defined.

Definition is_univalent_op_disp_cat
           {C : category}
           {D : disp_cat C}
           (HD : is_univalent_disp D)
  : is_univalent_disp (op_disp_cat D).
Proof.
  intros x y p xx yy.
  induction p.
  use weqhomot.
  - exact (z_iso_disp_weq_op_disp_cat xx yy
           ∘ make_weq _ (HD x x (idpath _) xx yy))%weq.
  - abstract
      (intro p ;
       use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
       induction p ; cbn ;
       apply idpath).
Defined.
