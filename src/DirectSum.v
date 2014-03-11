(** *** direct sums

    Recall that X is a family of objects in a category, and the map from the 
    sum to the product is an isomorphism, then the sum is called a direct sum. *)

Unset Automatic Introduction.
Require Import 
        Foundations.hlevel2.hSet
        RezkCompletion.precategories
        RezkCompletion.functors_transformations
        Ktheory.ZeroObject.
Require Ktheory.Utilities Ktheory.Precategories Ktheory.RawMatrix
        Ktheory.Sum Ktheory.Product Ktheory.FiniteSet.
Import RezkCompletion.pathnotations.PathNotations 
       Ktheory.Utilities.Notation
       Precategories.Notation
       FiniteSet.Coercions 
       Sum.Coercions Product.Coercions.
Definition identity_matrix {C:precategory} (h:hasZeroObject C)
           {I} (d:I -> ob C) (dec : isdeceq I) : forall i j, Hom (d j) (d i).
Proof. intros. destruct (dec i j) as [ [] | _ ].
       { apply identity. } { apply zeroMap. apply h. } Defined.
Definition identity_map {C:precategory} (h:hasZeroObject C)
           {I} {d:I -> ob C} (dec : isdeceq I) 
           (B:Sum.type C d) (D:Product.type C d)
      : Hom B D.
Proof. intros. apply RawMatrix.from_matrix. apply identity_matrix.  
       assumption. assumption. Defined.
Record DirectSum {C:precategory} (h:hasZeroObject C) I (dec : isdeceq I) (c : I -> ob C) := 
  make_DirectSum {
      ds : C;
      ds_pr : forall i, Hom ds (c i);
      ds_in : forall i, Hom (c i) ds;
      ds_id : forall i j, ds_pr i ∘ ds_in j == identity_matrix h c dec i j;
      ds_isprod : forall c, isweq (fun f : Hom c ds => fun i => ds_pr i ∘ f);
      ds_issum  : forall c, isweq (fun f : Hom ds c => fun i => f ∘ ds_in i) }.
Definition toDirectSum {C:precategory} (h:hasZeroObject C) {I} (dec : isdeceq I) (d:I -> ob C) 
           (B:Sum.type C d) (D:Product.type C d)
           (is: is_isomorphism (identity_map h dec B D)) : DirectSum h I dec d.
Proof. intros. set (id := identity_map h dec B D).
  refine (make_DirectSum C h I dec d D
                         (fun i => Product.Proj D i)
                         (fun i => id ∘ Sum.In B i) _ _ _).
  { intros. exact (RawMatrix.from_matrix_entry_assoc D B (identity_matrix h d dec) i j). }
  { intros. exact (pr2 (Representation.Iso D c)). }
  { intros. 
    assert (b : (fun (f : Hom D c) (i : I) => (f ∘ id) ∘ Sum.In B i)
             == (fun (f : Hom D c) (i : I) => f ∘ (id ∘ Sum.In B i))).
    { apply funextsec; intros f. apply funextsec; intros i. apply assoc. }
    destruct b.
    exact (twooutof3c (fun f => f ∘ id) 
                      (fun g i => g ∘ Sum.In B i)
                      (iso_comp_right_isweq (id,,is) c)
                      (pr2 (Representation.Iso B c))). }
Defined.
Definition FiniteDirectSums (C:precategory) := total2 (fun 
             h:hasZeroObject C => 
             forall (I:FiniteSet.Data) (d:I -> ob C), 
               DirectSum h I (FiniteSet.Isdeceq I) d).
