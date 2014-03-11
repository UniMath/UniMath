(** ** raw matrices

       Raw matrices of a map are formed from a product decomposition of
       the target or from a sum decomposition of the source.  We call
       them "raw" to distinguish them from matrices formed from direct
       sum decompositions. *)

Unset Automatic Introduction.
Require Import 
        Foundations.hlevel2.hSet
        RezkCompletion.precategories
        RezkCompletion.functors_transformations
        Ktheory.Utilities.
Require Ktheory.Precategories Ktheory.Sum Ktheory.Product.
Import RezkCompletion.pathnotations.PathNotations Utilities.Notation Precategories.Notation.
Import Sum.Coercions Product.Coercions.
Definition to_row {C:precategory} {I} {b:I -> ob C} 
           (B:Sum.type C b) {d:ob C} :
  weq (Hom B d) (forall j, Hom (b j) d).
Proof. intros. exact (Representation.Iso B d). Defined.
Definition from_row {C:precategory} {I} {b:I -> ob C} 
           (B:Sum.type C b) {d:ob C} :
  weq (forall j, Hom (b j) d) (Hom B d).
Proof. intros. apply invweq. apply to_row. Defined.
Lemma from_row_entry {C:precategory} {I} {b:I -> ob C} 
           (B:Sum.type C b) {d:ob C} (f : forall j, Hom (b j) d) :
  forall j, from_row B f ∘ Sum.In B j == f j.
Proof. intros. exact (apevalsecat j (homotweqinvweq (to_row B) f)). Qed.
Definition to_col {C:precategory} {I} {d:I -> ob C} (D:Product.type C d) {b:ob C} :
  weq (Hom b D) (forall i, Hom b (d i)).
Proof. intros. exact (Representation.Iso D b). Defined.
Definition from_col {C:precategory} {I} {d:I -> ob C} 
           (D:Product.type C d) {b:ob C} :
  weq (forall i, Hom b (d i)) (Hom b D).
Proof. intros. apply invweq. apply to_col. Defined.
Lemma from_col_entry {C:precategory} {I} {b:I -> ob C} 
           (D:Product.type C b) {d:ob C} (f : forall i, Hom d (b i)) :
  forall i, Product.Proj D i ∘ from_col D f == f i.
Proof. intros. exact (apevalsecat i (homotweqinvweq (to_row D) f)). Qed.
Definition to_matrix {C:precategory} 
           {I} {d:I -> ob C} (D:Product.type C d)
           {J} {b:J -> ob C} (B:Sum.type C b) :
           weq (Hom B D) (forall i j, Hom (b j) (d i)).
Proof. intros. apply @weqcomp with (Y := forall i, Hom B (d i)).
       { apply to_col. } { apply weqonseqfibers; intro i. apply to_row. } Defined.
Definition from_matrix {C:precategory} 
           {I} {d:I -> ob C} (D:Product.type C d)
           {J} {b:J -> ob C} (B:Sum.type C b) :
           weq (forall i j, Hom (b j) (d i)) (Hom B D).
Proof. intros. apply invweq. apply to_matrix. Defined.
Lemma from_matrix_entry {C:precategory} 
           {I} {d:I -> ob C} (D:Product.type C d)
           {J} {b:J -> ob C} (B:Sum.type C b)
           (f : forall i j, Hom (b j) (d i)) :
  forall i j, (Product.Proj D i ∘ from_matrix D B f) ∘ Sum.In B j == f i j.
Proof. intros. exact (apevalsecat j (apevalsecat i (homotweqinvweq (to_matrix D B) f))). Qed.
Lemma from_matrix_entry_assoc {C:precategory} 
           {I} {d:I -> ob C} (D:Product.type C d)
           {J} {b:J -> ob C} (B:Sum.type C b)
           (f : forall i j, Hom (b j) (d i)) :
  forall i j, Product.Proj D i ∘ (from_matrix D B f ∘ Sum.In B j) == f i j.
Proof. intros. refine ( !_ @ from_matrix_entry D B f i j ). apply assoc. Qed.
