(** ** raw matrices

       Raw matrices of a map are formed from a product decomposition of
       the target or from a sum decomposition of the source.  We call
       them "raw" to distinguish them from matrices formed from direct
       sum decompositions. *)

Require Import
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.Categories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Representation
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Precategories.
Unset Automatic Introduction.
Local Open Scope cat.

Definition to_row {C:category} {I} {b:I -> ob C}
           (B:Sum b) {d:ob C} :
  (Hom C (universalObject B) d) ≃ (∏ j, Hom C (b j) d).
Proof. intros. exact (universalProperty B d). Defined.

Definition from_row {C:category}  {I} {b:I -> ob C}
           (B:Sum b) {d:ob C} :
  (∏ j, Hom C (b j) d) ≃ (Hom C (universalObject B) d).
Proof. intros. apply invweq. apply to_row. Defined.

Lemma from_row_entry {C:category} {I} {b:I -> ob C}
           (B:Sum b) {d:ob C} (f : ∏ j, Hom C (b j) d) :
  ∏ j, from_row B f ∘ opp_mor (universalElement B j) = f j.
Proof. intros. exact (eqtohomot (homotweqinvweq (to_row B) f) j). Qed.

Definition to_col {C:category} {I} {d:I -> ob C} (D:Product d) {b:ob C} :
  (Hom C b (universalObject D)) ≃ (∏ i, Hom C b (d i)).
Proof. intros. exact (universalProperty D b). Defined.

Definition from_col {C:category} {I} {d:I -> ob C}
           (D:Product d) {b:ob C} :
 (∏ i, Hom C b (d i)) ≃ (Hom C b (universalObject D)).
Proof. intros. apply invweq. apply to_col. Defined.

Lemma from_col_entry {C:category} {I} {b:I -> ob C}
           (D:Product b) {d:ob C} (f : ∏ i, Hom C d (b i)) :
  ∏ i, universalElement D i ∘ from_col D f = f i.
Proof. intros.
  apply (eqtohomot (homotweqinvweq (to_col D) f ) i). Qed.

Definition to_matrix {C:category}
           {I} {d:I -> ob C} (D:Product d)
           {J} {b:J -> ob C} (B:Sum b) :
  (Hom C (universalObject B) (universalObject D))
    ≃
    (∏ i j, Hom C (b j) (d i)).
Proof.
  intros. apply @weqcomp with (Y := ∏ i, Hom C (universalObject B) (d i)).
  { apply to_col. }
  { apply weqonsecfibers; intro i. apply to_row. }
Defined.

Definition from_matrix {C:category}
           {I} {d:I -> ob C} (D:Product d)
           {J} {b:J -> ob C} (B:Sum b) :
           weq (∏ i j, Hom C (b j) (d i)) (Hom C (universalObject B) (universalObject D)).
Proof. intros. apply invweq. apply to_matrix. Defined.

Lemma from_matrix_entry {C:category}
           {I} {d:I -> ob C} (D:Product d)
           {J} {b:J -> ob C} (B:Sum b)
           (f : ∏ i j, Hom C (b j) (d i)) :
  ∏ i j, (universalElement D i ∘ from_matrix D B f) ∘ opp_mor (universalElement B j) = f i j.
Proof. intros. exact (eqtohomot (eqtohomot (homotweqinvweq (to_matrix D B) f) i) j). Qed.

Lemma from_matrix_entry_assoc {C:category}
           {I} {d:I -> ob C} (D:Product d)
           {J} {b:J -> ob C} (B:Sum b)
           (f : ∏ i j, Hom C (b j) (d i)) :
  ∏ i j, universalElement D i ∘ (from_matrix D B f ∘ opp_mor(universalElement B j)) = f i j.
Proof. intros. rewrite <- assoc. exact (from_matrix_entry D B f i j). Qed.
