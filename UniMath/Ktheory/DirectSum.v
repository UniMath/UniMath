(** *** direct sums

    Recall that X is a family of objects in a category, and the map from the
    sum to the product is an isomorphism, then the sum is called a direct sum. *)

Require Import
        UniMath.Foundations.Sets
        UniMath.CategoryTheory.precategories
        UniMath.CategoryTheory.functor_categories
        UniMath.Ktheory.Utilities
        UniMath.Ktheory.Precategories
        UniMath.Ktheory.ZeroObject.
Require UniMath.Ktheory.RawMatrix
        UniMath.Ktheory.Sum UniMath.Ktheory.Product UniMath.Ktheory.FiniteSet.
Import FiniteSet.Coercions Sum.Coercions Product.Coercions.
Definition identity_matrix {C:precategory} (hs: has_homsets C) (h:hasZeroObject C)
           {I} (d:I -> ob C) (dec : isdeceq I) : ∀ i j, Hom (d j) (d i).
Proof. intros. destruct (dec i j) as [ [] | _ ].
       { apply identity. } { apply zeroMap. apply hs. apply h. } Defined.
Definition identity_map {C:precategory} (hs: has_homsets C) (h:hasZeroObject C)
           {I} {d:I -> ob C} (dec : isdeceq I)
           (B:Sum.type C hs d) (D:Product.type C hs d)
      : Hom B D.
Proof. intros. apply RawMatrix.from_matrix. apply identity_matrix.
       assumption. assumption. assumption. Defined.
Record DirectSum {C:precategory} (hs: has_homsets C) (h:hasZeroObject C) I (dec : isdeceq I) (c : I -> ob C) :=
  make_DirectSum {
      ds : C;
      ds_pr : ∀ i, Hom ds (c i);
      ds_in : ∀ i, Hom (c i) ds;
      ds_id : ∀ i j, ds_pr i ∘ ds_in j = identity_matrix hs h c dec i j;
      ds_isprod : ∀ c, isweq (fun f : Hom c ds => fun i => ds_pr i ∘ f);
      ds_issum  : ∀ c, isweq (fun f : Hom ds c => fun i => f ∘ ds_in i) }.
Definition toDirectSum {C:precategory} (hs: has_homsets C) (h:hasZeroObject C) {I} (dec : isdeceq I) (d:I -> ob C)
           (B:Sum.type C hs d) (D:Product.type C hs d)
           (is: is_isomorphism (identity_map hs h dec B D)) : DirectSum hs h I dec d.
Proof. intros. set (id := identity_map hs h dec B D).
  refine (make_DirectSum C hs h I dec d D
                         (fun i => Product.Proj hs D i)
                         (fun i => id ∘ Sum.In hs B i) _ _ _).
  { intros. exact (RawMatrix.from_matrix_entry_assoc _ D B (identity_matrix _ h d dec) i j). }
  { intros. exact (pr2 (Representation.Iso D c)). }
  { intros.
    assert (b : (fun (f : Hom D c) (i : I) => (f ∘ id) ∘ Sum.In _ B i)
             = (fun (f : Hom D c) (i : I) => f ∘ (id ∘ Sum.In _ B i))).
    { apply funextsec; intros f. apply funextsec; intros i. apply assoc. }
    destruct b.
    exact (twooutof3c (fun f => f ∘ id)
                      (fun g i => g ∘ Sum.In _ B i)
                      (iso_comp_right_isweq (id,,is) c)
                      (pr2 (Representation.Iso B c))). }
Defined.
Definition FiniteDirectSums (C:precategory) (hs: has_homsets C) :=
             Σ h : hasZeroObject C,
             ∀ I : FiniteSet.Data,
             ∀ d : I -> ob C,
               DirectSum hs  h I (FiniteSet.Isdeceq I) d.
