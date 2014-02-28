(** *** the category of elements of a functor *)
Unset Automatic Introduction.
Require Import RezkCompletion.precategories
               RezkCompletion.functors_transformations 
               Foundations.hlevel2.hSet 
               Ktheory.Utilities.
Require Ktheory.Precategories.
Import Utilities.Notation
       Precategories.Notation
       pathnotations.PathNotations.
Definition cat_data {C} (X:C==>SET) : precategory_data.
  intros. refine (Precategories.makePrecategory_data _ _ _ _ _).
  { exact (total2 (fun c : ob C => set_to_type (X c))). }
  { exact (fun a b => total2 (fun f : pr1 a → pr1 b => #X f (pr2 a) == (pr2 b))). }
  { abstract (
        intros; apply (isofhleveltotal2 2);
        [ apply setproperty |
          intros f;  apply (isofhlevelsnprop 1); apply setproperty])
    using cat_data_isaset. }
  { intro a. 
    exact (identity (pr1 a),, (apevalat (pr2 a) ((functor_id X) (pr1 a)))). }
  { intros ? ? ? f g.
    exact (pr1 g ∘ pr1 f,,
           (  (apevalat (pr2 i) ((functor_comp X) _ _ _ (pr1 f) (pr1 g)))
            @ (ap (#X (pr1 g)) (pr2 f) @ (pr2 g)))). } Defined.
Definition get_mor {C} {X:C==>SET} {x y:ob (cat_data X)} (f:x → y) := pr1 f.
Lemma mor_equality {C} (X:C==>SET) (x y:ob (cat_data X)) (f g:x → y) :
      get_mor f == get_mor g -> f == g.
Proof. intros ? ? ? ? [f i] [g j] p. simpl in p. destruct p.
       assert (k : i==j). { apply equality_proof_irrelevance. }
       destruct k. reflexivity. Qed.
Lemma isPrecategory {C} (X:C==>SET) : is_precategory (cat_data X).
Proof. intros. split. split.
       - intros. apply mor_equality. apply id_left.
       - intros. apply mor_equality. apply id_right.
       - intros. apply mor_equality. apply assoc. Qed.
Definition cat {C} (X:C==>SET) : precategory.
  intros. exact (cat_data X ,, isPrecategory X). Defined.
Definition get_ob {C} {X:C==>SET} (x:ob (cat X)) := pr1 x.
Definition get_el {C} {X:C==>SET} (x:ob (cat X)) := pr2 x.
Definition make_ob {C} (X:C==>SET) 
           (c:ob C) (x:set_to_type (X c)) : ob (cat X).
  intros. exact (c,,x). Defined.
Definition make_mor {C} (X:C==>SET) (r s : ob (cat X)) 
           (f : Hom (pr1 r) (pr1 s))
           (i : #X f (pr2 r) == pr2 s) : Hom r s.
  intros. exact (f,,i). Defined.
Module pr1.
  Definition fun_data {C} (X:C==>SET) : 
      functor_data (Precategories.Precategory.obmor (cat X)) (Precategories.Precategory.obmor C).
    intros. exists pr1. intros x x'. exact pr1. Defined.
  Definition func {C} (X:C==>SET) : cat X ==> C.
    intros. exists (fun_data _).
    split. { reflexivity. } { reflexivity. } Defined.
  Lemma func_reflects_isos {C} (X:C==>SET) : Precategories.reflects_isos (func X).
  Proof. intros ? ? [c x] [d y] [f i] [f' j].
    assert (i' : #X f' y == x).
    { intermediate (#X f' (#X f x)).
      { exact (ap (#X f') (!i)). }
      { intermediate (#X (f' ∘ f) x).
        { exact (apevalat x (!functor_comp X _ _ _ f f')). }
        { intermediate (#X (identity c) x).
          { exact (apevalat x (ap #X (pr1 j))). }
          { exact (apevalat x (functor_id X c)). }}}}
    { exists (f' ,, i'). split.
      { apply mor_equality.  exact (pr1 j). }
      { apply mor_equality.  exact (pr2 j). } } Qed.
End pr1.
