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

Local Open Scope cat.
Local Open Scope mor_disp.

Section OpDispCat.
  Context {C : category}
          (D : disp_cat C).

  Definition op_disp_cat_ob_mor
    : disp_cat_ob_mor (op_cat C).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, D x).
    - exact (λ x y xx yy f, yy -->[ f ] xx).
  Defined.

  Definition op_disp_cat_id_comp
    : disp_cat_id_comp (op_cat C) op_disp_cat_ob_mor.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x xx, id_disp _).
    - refine (λ x y z f g xx yy zz ff gg, _) ; cbn in *.
      exact (gg ;; ff).
  Defined.

  Definition op_disp_cat_data
    : disp_cat_data (op_cat C).
  Proof.
    simple refine (_ ,, _).
    - exact op_disp_cat_ob_mor.
    - exact op_disp_cat_id_comp.
  Defined.

  Definition op_disp_cat_axioms
    : disp_cat_axioms (op_cat C) op_disp_cat_data.
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
    : disp_cat (op_cat C).
  Proof.
    simple refine (_ ,, _).
    - exact op_disp_cat_data.
    - exact op_disp_cat_axioms.
  Defined.
End OpDispCat.

Definition to_iso_disp_op_disp_cat
           {C : category}
           {D : disp_cat C}
           {x y : C}
           {f : iso y x}
           {xx : D x}
           {yy : D y}
           (ff : yy -->[ f ] xx)
           (Hff : is_iso_disp f ff)
  : @is_iso_disp
      _
      (op_disp_cat D)
      x y
      (opp_iso f)
      _ _
      ff.
Proof.
  simple refine (_ ,, _ ,, _).
  - exact (transportb
             (λ z, _ -->[ z ] _)
             (id_left _)
             (inv_mor_disp_from_iso Hff)).
  - abstract
      (cbn ;
       unfold transportb ;
       rewrite mor_disp_transportf_prewhisker ;
       etrans ;
       [ apply maponpaths ;
         apply inv_mor_after_iso_disp
       | ] ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply homset_property).
  - abstract
      (cbn ;
       unfold transportb ;
       rewrite mor_disp_transportf_postwhisker ;
       etrans ;
       [ apply maponpaths ;
         apply iso_disp_after_inv_mor
       | ] ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply homset_property).
Defined.
