(** *** the category of elements of a functor *)

Unset Automatic Introduction.
Require Export RezkCompletion.precategories
               RezkCompletion.functors_transformations 
               Foundations.hlevel2.hSet 
               Ktheory.Utilities.
Require Export Ktheory.Precategories.
Export Utilities.Notation
       Precategories.Notation
       pathnotations.PathNotations.
Definition cat_ob_mor {C} (X:C==>SET) : precategory_ob_mor.
  intros. exists (total2 (fun c : ob C => set_to_type (X c))).
  intros a b. exists (total2 (fun f : pr1 a → pr1 b => #X f (pr2 a) == (pr2 b))).
  abstract (
        intros; apply (isofhleveltotal2 2);
        [ apply setproperty |
          intros f;  apply (isofhlevelsnprop 1); apply setproperty])
    using cat_data_isaset. Defined.
Definition cat_data {C} (X:C==>SET) : precategory_data.
  intros. exists (cat_ob_mor X). split.
  { intro a. 
    exact (identity (pr1 a),, (apevalat (pr2 a) ((functor_id X) (pr1 a)))). }
  { intros a b c f g.
    exact (pr1 g ∘ pr1 f,,
           (  (apevalat (pr2 a) ((functor_comp X) _ _ _ (pr1 f) (pr1 g)))
            @ (ap (#X (pr1 g)) (pr2 f) @ (pr2 g)))). } Defined.
Definition get_mor {C} {X:C==>SET} {x y:ob (cat_data X)} (f:x → y) := pr1 f.
Lemma mor_equality {C} (X:C==>SET) (x y:ob (cat_data X)) (f g:x → y) :
      get_mor f == get_mor g -> f == g.
Proof. intros ? ? ? ? [f i] [g j] p. simpl in p. destruct p.
       assert (k : i==j). { apply equality_proof_irrelevance. }
       destruct k. reflexivity. Qed.
Lemma isPrecategory {C} (X:C==>SET) : is_precategory (cat_data X).
Proof. intros. split.
       { split. 
         { intros. apply mor_equality. apply id_left. }
         { intros. apply mor_equality. apply id_right. } }
       { intros. apply mor_equality. apply assoc. } Qed.
Definition cat {C} (X:C==>SET) : precategory.
  intros. exact (cat_data X ,, isPrecategory X). Defined.
Definition get_ob {C} {X:C==>SET} (x:ob (cat X)) := pr1 x.
Definition get_el {C} {X:C==>SET} (x:ob (cat X)) := pr2 x.
Definition get_eqn {C} {X:C==>SET} {x y:ob (cat_data X)} (f:x → y) := pr2 f.
Definition make_ob {C} (X:C==>SET) (c:ob C) (x:set_to_type (X c)) : ob (cat X)
  := (c,,x).
Definition make_mor {C} (X:C==>SET) (r s : ob (cat X)) 
           (f : Hom (pr1 r) (pr1 s))
           (i : #X f (pr2 r) == pr2 s) : Hom r s
  := (f,,i).

(** *** functoriality of the construction of the category of elements *)

Definition cat_on_nat_trans_data {C} {X Y:C==>SET} (p:nat_trans X Y) :
  functor_data (cat X) (cat Y).
Proof. intros. 
  exists (fun a => pr1 a,, p (pr1 a) (pr2 a)).
  exact (fun b c f => pr1 f,,
          ! (apevalat (pr2 b) (pr2 p (pr1 b) (pr1 c) (pr1 f)))
          @ ap ((pr1 p) (pr1 c)) (pr2 f)). Defined.

Lemma cat_on_nat_trans_is_nat_trans {C} {X Y:C==>SET} (p:nat_trans X Y) :
  is_functor (cat_on_nat_trans_data p).
Proof. intros. split.
  { intros. apply mor_equality. reflexivity. }
  { intros. apply mor_equality. reflexivity. } Qed.

Definition cat_on_nat_trans {C} {X Y:C==>SET} (p:nat_trans X Y) :
  cat X ==> cat Y.
Proof. 
  intros. 
  exact (cat_on_nat_trans_data p,, cat_on_nat_trans_is_nat_trans p). Defined.

(** *** properties of projection to the original category *)

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
    { intermediate_path (#X f' (#X f x)).
      { exact (ap (#X f') (!i)). }
      { intermediate_path (#X (f' ∘ f) x).
        { exact (apevalat x (!functor_comp X _ _ _ f f')). }
        { intermediate_path (#X (identity c) x).
          { exact (apevalat x (ap #X (pr1 j))). }
          { exact (apevalat x (functor_id X c)). }}}}
    { exists (f' ,, i'). split.
      { apply mor_equality.  exact (pr1 j). }
      { apply mor_equality.  exact (pr2 j). } } Qed.
End pr1.
