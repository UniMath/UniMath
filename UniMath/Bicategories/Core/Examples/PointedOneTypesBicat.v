Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.

Local Open Scope cat.

(** The bicategory *)
Definition pointed_one_type_bicat_data
  : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact (∑ (X : one_type), X).
  - exact (λ X Y, ∑ (f : pr1 X → pr1 Y), f (pr2 X) = pr2 Y).
  - exact (λ X Y f g, ∑ (h : pr1 f = pr1 g),
           transportf (λ φ, φ (pr2 X) = pr2 Y) h (pr2 f) = pr2 g).
  - exact (λ X, (λ x, x) ,, idpath _).
  - exact (λ X Y Z f g, (λ x,pr1 g(pr1 f x)) ,, maponpaths (pr1 g) (pr2 f) @ pr2 g).
  - exact (λ X Y f, idpath _ ,, idpath _).
  - refine (λ X Y f g h p q, (pr1 p @ pr1 q) ,, _) ; cbn in *.
    exact (!(transport_f_f _ _ _ _) @ maponpaths _ (pr2 p) @ pr2 q).
  - refine (λ X Y Z f g h p, (maponpaths (λ φ x, φ (pr1 f x)) (pr1 p)) ,, _) ; cbn in *.
    induction g as [g1 g2], h as [h1 h2], p as [p1 p2] ; cbn in *.
    induction p1, p2 ; cbn.
    reflexivity.
  - refine (λ X Y Z f g h p, (maponpaths (λ φ x, pr1 h (φ x)) (pr1 p)) ,, _) ; cbn in *.
    induction g as [g1 g2], h as [h1 h2], p as [p1 p2] ; cbn in *.
    induction p1, p2 ; cbn.
    reflexivity.
  - exact (λ X Y f, idpath _ ,, idpath _).
  - exact (λ X Y f, idpath _ ,, idpath _).
  - refine (λ X Y f, idpath _ ,, _) ; cbn in *.
    exact (pathscomp0rid _ @ maponpathsidfun _).
  - refine (λ X Y f, idpath _ ,, _) ; cbn in *.
    exact (!(pathscomp0rid _ @ maponpathsidfun _)).
  - refine (λ W X Y Z f g h, idpath _ ,, _) ; cbn in *.
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    refine (_ @ !(maponpathscomp0 _ _ _)).
    apply maponpaths_2.
    exact (!(maponpathscomp _ _ _)).
  - refine (λ W X Y Z f g h, idpath _ ,, ! _) ; cbn in *.
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    refine (_ @ !(maponpathscomp0 _ _ _)).
    apply maponpaths_2.
    exact (!(maponpathscomp _ _ _)).
Defined.

Definition pointed_one_type_bicat_laws
  : prebicat_laws pointed_one_type_bicat_data.
Proof.
  repeat (use tpair).
  - intros X Y f g p ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], p as [p1 p2] ; cbn in *.
    induction p1 ; cbn.
    reflexivity.
  - intros X Y f g p ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], p as [p1 p2] ; cbn in *.
    induction p1, p2 ; cbn.
    reflexivity.
  - intros X Y f g h k p q r ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], h as [h1 h2], k as [k1 k2].
    induction p as [p1 p2], q as [q1 q2], r as [r1 r2] ; cbn in *.
    induction p1, p2, q1, q2, r1, r2.
    reflexivity.
  - reflexivity.
  - reflexivity.
  - intros X Y Z f g h i p q ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], h as [h1 h2], i as [i1 i2].
    induction p as [p1 p2], q as [q1 q2] ; cbn in *.
    induction p1, p2, q1, q2 ; cbn.
    reflexivity.
  - intros X Y Z f g h i p q ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], h as [h1 h2], i as [i1 i2].
    induction p as [p1 p2], q as [q1 q2] ; cbn in *.
    induction p1, p2, q1, q2 ; cbn.
    reflexivity.
  - intros X Y f g p ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], p as [p1 p2] ; cbn in *.
    induction p1, p2 ; cbn.
    reflexivity.
  - intros X Y f g p ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], p as [p1 p2] ; cbn in *.
    induction p1, p2, f2 ; cbn.
    reflexivity.
  - intros W X Y Z f g h i p ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], h as [h1 h2], i as [i1 i2].
    induction p as [p1 p2] ; cbn in *.
    induction p1, p2, f2, g2, h2 ; cbn.
    reflexivity.
  - intros W X Y Z f g h i p ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], h as [h1 h2], i as [i1 i2].
    induction p as [p1 p2] ; cbn in *.
    induction p1, p2, f2, g2 ; cbn.
    reflexivity.
  - intros W X Y Z f g h i p ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], h as [h1 h2], i as [i1 i2].
    induction p as [p1 p2] ; cbn in *.
    induction p1, p2, f2, h2 ; cbn.
    reflexivity.
  - intros X Y Z f g h i p q ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], h as [h1 h2], i as [i1 i2].
    induction p as [p1 p2], q as [q1 q2] ; cbn in *.
    induction p1, p2, q1, q2, f2, h2 ; cbn.
    reflexivity.
  - reflexivity.
  - reflexivity.
  - intros X Y p ; cbn in *.
    induction p as [p1 p2].
    induction p2 ; cbn.
    reflexivity.
  - intros X Y p ; cbn in *.
    induction p as [p1 p2].
    induction p2 ; cbn.
    reflexivity.
  - intros W X Y Z f g h ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], h as [h1 h2] ; cbn in *.
    induction f2, g2, h2 ; cbn.
    reflexivity.
  - intros W X Y Z f g h ; cbn in *.
    induction f as [f1 f2], g as [g1 g2], h as [h1 h2] ; cbn in *.
    induction f2, g2, h2 ; cbn.
    reflexivity.
  - intros X Y Z f g ; cbn in *.
    induction f as [f1 f2], g as [g1 g2] ; cbn in *.
    induction f2, g2 ; cbn.
    reflexivity.
  - intros V W X Y Z f g h i.
    induction f as [f1 f2], g as [g1 g2], h as [h1 h2], i as [i1 i2] ; cbn in *.
    induction f2, g2, h2, i2 ; cbn.
    reflexivity.
Qed.

Definition pointed_one_types
  : bicat.
Proof.
  use build_bicategory.
  - exact pointed_one_type_bicat_data.
  - exact pointed_one_type_bicat_laws.
  - intros X Y f g ; cbn in *.
    use isaset_total2.
    + exact (impredfun 3 (pr1 X) (pr1 Y) (pr21 Y) (pr1 f) (pr1 g)).
    + intro ; cbn.
      repeat intro.
      apply hlevelntosn.
      apply (pr21 Y).
Defined.