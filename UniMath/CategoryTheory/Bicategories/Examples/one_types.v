(* 1-types as a bicategory *)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Bicategories.Bicat.

Definition one_type
  := ∑ (A : Type), isofhlevel 3 A.

Definition one_type_to_type : one_type -> UU := pr1.
Coercion one_type_to_type : one_type >-> UU.

Definition one_type_bicat_data
  : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact one_type.
  - exact (fun X Y => X -> Y).
  - exact (fun _ _ f g => f = g).
  - exact (fun _ x => x).
  - exact (fun _ _ _ f g x => g(f x)).
  - reflexivity.
  - cbn ; intros X Y f g h p q.
    exact (p @ q).
  - cbn ; intros X Y Z f g h p.
    exact (maponpaths (λ φ x, φ (f x)) p).
  - cbn ; intros X Y Z f g h p.
    exact (maponpaths (λ φ x, h(φ x)) p).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Definition one_type_bicat_laws
  : prebicat_laws one_type_bicat_data.
Proof.
  build_prebicat_laws.
  - intros X Y f g p ; cbn in *.
    reflexivity.
  - intros X Y f g p ; cbn in *.
    apply pathscomp0rid.
  - intros X Y f g h k p q r.
    apply path_assoc.
  - reflexivity.
  - reflexivity.
  - intros X Y Z f g h i p q ; cbn in *.
    induction p, q ; cbn.
    reflexivity.
  - intros X Y Z f g h i p q ; cbn in *.
    induction p, q ; cbn.
    reflexivity.
  - intros X Y f g p ; cbn in *.
    induction p ; cbn.
    reflexivity.
  - intros X Y f g p ; cbn in *.
    induction p ; cbn.
    reflexivity.
  - intros W X Y Z f g h i p ; cbn in *.
      induction p ; cbn.
      reflexivity.
  - intros W X Y Z f g h i p ; cbn in *.
    induction p ; cbn.
    reflexivity.
  - intros W X Y Z f g h i p ; cbn in *.
    induction p ; cbn.
    reflexivity.
  - intros X Y Z f g h i p q ; cbn in *.
    induction p, q ; cbn.
    reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros V W X Y Z f g h i ; cbn in *.
    reflexivity.
Qed.

Definition one_type_bicat
  : bicat.
Proof.
  use build_bicategory.
  - exact one_type_bicat_data.
  - exact one_type_bicat_laws.
  - intros X Y f g ; cbn in *.
    exact (impredfun 3 X Y (pr2 Y) f g).
Defined.