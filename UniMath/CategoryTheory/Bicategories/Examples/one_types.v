Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Bicategories.Bicat.

Definition one_type
  := ∑ (A : Type), isofhlevel 3 A.

Definition one_type_to_type : one_type -> UU := pr1.
Coercion one_type_to_type : one_type >-> UU.

Definition one_type_bicat
  : bicat.
Proof.
  simple refine (build_bicategory
                   _ _ _ _ _ _ _
                   _ _ _ _ _ _ _
                   _ _ _ _ _ _ _
                   _ _ _ _ _ _ _
                   _ _ _ _ _ _ _
                   _ _
                ).
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
  - abstract (reflexivity).
  - abstract (intros X Y f g p ;
              apply pathscomp0rid).
  - abstract (intros X Y f g h k p q r ;
              apply path_assoc).
  - abstract reflexivity.
  - abstract reflexivity.
  - abstract (intros X Y Z f g h i p q ;
              induction p, q ; cbn ;
              reflexivity).
  - abstract (intros X Y Z f g h i p q ;
              induction p, q ; cbn ;
              reflexivity).
  - abstract (intros X Y f g p ;
              induction p ; cbn ;
              reflexivity).
  - abstract (intros X Y f g p ;
              induction p ; cbn ;
              reflexivity).
  - abstract (intros W X Y Z f g h i p ;
              induction p ; cbn ;
              reflexivity).
  - abstract (intros W X Y Z f g h i p ;
              induction p ; cbn ;
              reflexivity).
  - abstract (intros W X Y Z f g h i p ;
              induction p ; cbn ;
              reflexivity).
  - abstract (cbn ; intros X Y Z f g h i p q ;
              induction p, q ; cbn ;
              reflexivity).
  - abstract reflexivity.
  - abstract reflexivity.
  - abstract reflexivity.
  - abstract reflexivity.
  - abstract reflexivity.
  - abstract reflexivity.
  - abstract reflexivity.
  - abstract reflexivity.
  - abstract (cbn ; intros X Y f g ;
              exact (impredfun 3 X Y (pr2 Y) f g)).
Defined.