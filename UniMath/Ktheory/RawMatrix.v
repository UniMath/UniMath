(** ** raw matrices

       Raw matrices of a map are formed from a product decomposition of
       the target or from a sum decomposition of the source.  We call
       them "raw" to distinguish them from matrices formed from direct
       sum decompositions. *)

Require Import
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Representation
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Precategories.
Require UniMath.Ktheory.Sum UniMath.Ktheory.Product.
Local Open Scope cat.
Import UniMath.Ktheory.Sum.Coercions UniMath.Ktheory.Product.Coercions.

Definition to_row {C:Precategory} {I} {b:I -> ob C}
           (B:Sum.type C b) {d:ob C} :
  weq (Hom C B d) (∀ j, Hom C (b j) d).
Proof. intros. exact (universalProperty B d). Defined.

Definition from_row {C:Precategory}  {I} {b:I -> ob C}
           (B:Sum.type C b) {d:ob C} :
  weq (∀ j, Hom C (b j) d) (Hom C B d).
Proof. intros. apply invweq. apply to_row. Defined.

Lemma from_row_entry {C:Precategory} {I} {b:I -> ob C}
           (B:Sum.type C b) {d:ob C} (f : ∀ j, Hom C (b j) d) :
  ∀ j, from_row B f ∘ Sum.In B j = f j.
Proof. intros. exact (apevalat j (homotweqinvweq (to_row B) f)). Qed.

Definition to_col {C:Precategory} {I} {d:I -> ob C} (D:Product.type C d) {b:ob C} :
  weq (Hom C b D) (∀ i, Hom C b (d i)).
Proof. intros. exact (universalProperty D b). Defined.

Definition from_col {C:Precategory} {I} {d:I -> ob C}
           (D:Product.type C d) {b:ob C} :
  weq (∀ i, Hom C b (d i)) (Hom C b D).
Proof. intros. apply invweq. apply to_col. Defined.

Lemma from_col_entry {C:Precategory} {I} {b:I -> ob C}
           (D:Product.type C b) {d:ob C} (f : ∀ i, Hom C d (b i)) :
  ∀ i, Product.Proj D i ∘ from_col D f = f i.

Proof. intros.
  apply (apevalat i (homotweqinvweq (to_row D) f )). Qed.

Definition to_matrix {C:Precategory}
           {I} {d:I -> ob C} (D:Product.type C d)
           {J} {b:J -> ob C} (B:Sum.type C b) :
           weq (Hom C B D) (∀ i j, Hom C (b j) (d i)).
Proof. intros. apply @weqcomp with (Y := ∀ i, Hom C B (d i)).
       { apply to_col. } { apply weqonsecfibers; intro i. apply to_row. } Defined.

Definition from_matrix {C:Precategory}
           {I} {d:I -> ob C} (D:Product.type C d)
           {J} {b:J -> ob C} (B:Sum.type C b) :
           weq (∀ i j, Hom C (b j) (d i)) (Hom C B D).
Proof. intros. apply invweq. apply to_matrix. Defined.

Lemma from_matrix_entry {C:Precategory}
           {I} {d:I -> ob C} (D:Product.type C d)
           {J} {b:J -> ob C} (B:Sum.type C b)
           (f : ∀ i j, Hom C (b j) (d i)) :
  ∀ i j, (Product.Proj D i ∘ from_matrix D B f) ∘ Sum.In B j = f i j.
Proof. intros. exact (apevalat j (apevalat i (homotweqinvweq (to_matrix D B) f))). Qed.

Lemma from_matrix_entry_assoc {C:Precategory}
           {I} {d:I -> ob C} (D:Product.type C d)
           {J} {b:J -> ob C} (B:Sum.type C b)
           (f : ∀ i j, Hom C (b j) (d i)) :
  ∀ i j, Product.Proj D i ∘ (from_matrix D B f ∘ Sum.In B j) = f i j.
Proof. intros. refine ( !_ @ from_matrix_entry D B f i j ). apply assoc. Qed.
