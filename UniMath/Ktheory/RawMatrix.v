(** ** raw matrices

       Raw matrices of a map are formed from a product decomposition of
       the target or from a sum decomposition of the source.  We call
       them "raw" to distinguish them from matrices formed from direct
       sum decompositions. *)

Require Import
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Precategories.
Require UniMath.Ktheory.Sum UniMath.Ktheory.Product.
Import UniMath.Ktheory.Sum.Coercions UniMath.Ktheory.Product.Coercions.
Definition to_row {C:precategory} (hs: has_homsets C) {I} {b:I -> ob C}
           (B:Sum.type C hs b) {d:ob C} :
  weq (Hom B d) (∀ j, Hom (b j) d).
Proof. intros. exact (Representation.Iso B d). Defined.
Definition from_row {C:precategory} (hs: has_homsets C)  {I} {b:I -> ob C}
           (B:Sum.type C hs b) {d:ob C} :
  weq (∀ j, Hom (b j) d) (Hom B d).
Proof. intros. apply invweq. apply to_row. Defined.
Lemma from_row_entry {C:precategory} (hs: has_homsets C) {I} {b:I -> ob C}
           (B:Sum.type C hs b) {d:ob C} (f : ∀ j, Hom (b j) d) :
  ∀ j, from_row hs B f ∘ Sum.In hs B j = f j.
Proof. intros. exact (apevalat j (homotweqinvweq (to_row hs B) f)). Qed.
Definition to_col {C:precategory} (hs: has_homsets C) {I} {d:I -> ob C} (D:Product.type C hs d) {b:ob C} :
  weq (Hom b D) (∀ i, Hom b (d i)).
Proof. intros. exact (Representation.Iso D b). Defined.
Definition from_col {C:precategory} (hs: has_homsets C) {I} {d:I -> ob C}
           (D:Product.type C hs d) {b:ob C} :
  weq (∀ i, Hom b (d i)) (Hom b D).
Proof. intros. apply invweq. apply to_col. Defined.
Lemma from_col_entry {C:precategory} (hs: has_homsets C) {I} {b:I -> ob C}
           (D:Product.type C hs b) {d:ob C} (f : ∀ i, Hom d (b i)) :
  ∀ i, Product.Proj hs D i ∘ from_col hs D f = f i.
Proof. intros.
  apply (apevalat i (homotweqinvweq (to_row _ D) f )). Qed.
Definition to_matrix {C:precategory} (hs: has_homsets C)
           {I} {d:I -> ob C} (D:Product.type C hs d)
           {J} {b:J -> ob C} (B:Sum.type C hs b) :
           weq (Hom B D) (∀ i j, Hom (b j) (d i)).
Proof. intros. apply @weqcomp with (Y := ∀ i, Hom B (d i)).
       { apply to_col. } { apply weqonsecfibers; intro i. apply to_row. } Defined.
Definition from_matrix {C:precategory} (hs: has_homsets C)
           {I} {d:I -> ob C} (D:Product.type C hs d)
           {J} {b:J -> ob C} (B:Sum.type C hs b) :
           weq (∀ i j, Hom (b j) (d i)) (Hom B D).
Proof. intros. apply invweq. apply to_matrix. Defined.
Lemma from_matrix_entry {C:precategory} (hs: has_homsets C)
           {I} {d:I -> ob C} (D:Product.type C hs d)
           {J} {b:J -> ob C} (B:Sum.type C hs b)
           (f : ∀ i j, Hom (b j) (d i)) :
  ∀ i j, (Product.Proj hs D i ∘ from_matrix hs D B f) ∘ Sum.In hs B j = f i j.
Proof. intros. exact (apevalat j (apevalat i (homotweqinvweq (to_matrix _ D B) f))). Qed.
Lemma from_matrix_entry_assoc {C:precategory} (hs: has_homsets C)
           {I} {d:I -> ob C} (D:Product.type C _ d)
           {J} {b:J -> ob C} (B:Sum.type C hs b)
           (f : ∀ i j, Hom (b j) (d i)) :
  ∀ i j, Product.Proj _ D i ∘ (from_matrix _ D B f ∘ Sum.In _ B j) = f i j.
Proof. intros. refine ( !_ @ from_matrix_entry _ D B f i j ). apply assoc. Qed.
