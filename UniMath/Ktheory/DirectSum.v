(** *** direct sums

    Recall that X is a family of objects in a category, and the map from the
    sum to the product is an isomorphism, then the sum is called a direct sum. *)

Require Import
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Representation
        UniMath.Ktheory.Precategories
        UniMath.Ktheory.ZeroObject.
Require UniMath.Ktheory.RawMatrix
        UniMath.Ktheory.Sum UniMath.Ktheory.Product UniMath.Ktheory.FiniteSet.
Local Open Scope cat.
Import FiniteSet.Coercions Sum.Coercions Product.Coercions.

Definition identity_matrix {C:Precategory} (h:hasZeroObject C)
           {I} (d:I -> ob C) (dec : isdeceq I) : ∀ i j, Hom C (d j) (d i).
Proof. intros. destruct (dec i j) as [ [] | _ ].
       { apply identity. } { apply zeroMap. apply h. } Defined.

Definition identity_map {C:Precategory} (h:hasZeroObject C)
           {I} {d:I -> ob C} (dec : isdeceq I)
           (B:Sum.type C d) (D:Product.type C d)
      : Hom C B D.
Proof. intros. apply RawMatrix.from_matrix. apply identity_matrix.
       assumption. assumption. Defined.

Record DirectSum {C:Precategory} (h:hasZeroObject C) I (dec : isdeceq I) (c : I -> ob C) :=
  make_DirectSum {
      ds : C;
      ds_pr : ∀ i, Hom C ds (c i);
      ds_in : ∀ i, Hom C (c i) ds;
      ds_id : ∀ i j, ds_pr i ∘ ds_in j = identity_matrix h c dec i j;
      ds_isprod : ∀ c, isweq (fun f : Hom C c ds => fun i => ds_pr i ∘ f);
      ds_issum  : ∀ c, isweq (fun f : Hom C ds c => fun i => f ∘ ds_in i) }.
Definition toDirectSum {C:Precategory} (h:hasZeroObject C) {I} (dec : isdeceq I) (d:I -> ob C)
           (B:Sum.type C d) (D:Product.type C d)
           (is: is_isomorphism (identity_map h dec B D)) : DirectSum h I dec d.
Proof. intros. set (id := identity_map h dec B D).
  refine (make_DirectSum C h I dec d D
                         (fun i => Product.Proj D i)
                         (fun i => id ∘ Sum.In B i) _ _ _).
  { intros. exact (RawMatrix.from_matrix_entry_assoc D B (identity_matrix h d dec) i j). }
  { intros. exact (pr2 (universalProperty D c)). }
  { intros.
    assert (b : (fun (f : Hom C D c) (i : I) => (f ∘ id) ∘ Sum.In B i)
             = (fun (f : Hom C D c) (i : I) => f ∘ (id ∘ Sum.In B i))).
    { apply funextsec; intros f. apply funextsec; intros i. apply assoc. }
    destruct b.
    exact (twooutof3c (fun f => f ∘ id)
                      (fun g i => g ∘ Sum.In B i)
                      (iso_comp_right_isweq (id,,is) c)
                      (pr2 (universalProperty B c))). }
Defined.
Definition FiniteDirectSums (C:Precategory) :=
             Σ h : hasZeroObject C,
             ∀ I : FiniteSet.Data,
             ∀ d : I -> ob C,
               DirectSum h I (FiniteSet.Isdeceq I) d.
