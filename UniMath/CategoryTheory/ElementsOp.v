(* Modification of UniMath.Ktheory.Elements to use
   over presheaves instead of covariant functors *)

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.Foundations.Sets.
(* Require Export UniMath.Ktheory.Precategories. *)

Local Open Scope cat.

Definition cat_ob_mor {C} (X:C^op⟶SET) : precategory_ob_mor.
  intros. exists (∑ c:ob C, X c : hSet).
  intros a b.
  exact (∑ f : pr1 a --> pr1 b, (pr2 a) = #X f (pr2 b)).
Defined.

Local Open Scope cat_deprecated.

Definition cat_data {C} (X:C^op⟶SET) : precategory_data.
  intros. exists (cat_ob_mor X). split.
  { intro a.
    exact (identity (pr1 a),,
                    (eqtohomot (!((functor_id X) (pr1 a))) (pr2 a))). }
  { intros a b c f g.
    exact (pr1 g ∘ pr1 f,,
               ((pr2 f) @ ap (#X (pr1 f)) (pr2 g))
               @ ((eqtohomot (!((functor_comp X) (pr1 g) (pr1 f))) (pr2 c)))). } Defined.

Lemma has_homsets_cat_ob_mor {C:Precategory} (X:C^op⟶SET) :
   has_homsets (cat_data X).
Proof.
  intros C X a b. simpl. apply (isofhleveltotal2 2).
  - apply homset_property.
  - intro f. apply isasetaprop, setproperty.
Qed.

Definition get_mor {C} {X:C^op⟶SET} {x y:ob (cat_data X)} (f:x --> y) := pr1 f.

Lemma mor_equality {C} (X:C^op⟶SET) (x y:ob (cat_data X)) (f g:x --> y) :
      get_mor f = get_mor g -> f = g.
Proof. intros ? ? ? ? ? ? p. apply subtypeEquality.
       - intro r. apply setproperty.
       - exact p.
Qed.

Lemma isPrecategory {C:Precategory} (X:C^op⟶SET) : is_precategory (cat_data X).
Proof. intros. split.
       { split.
         { intros.  apply mor_equality. apply id_left. }
         { intros. apply mor_equality. apply id_right. } }
       { intros. apply mor_equality. apply assoc. } Qed.

Definition cat {C:Precategory} (X:C^op⟶SET) : Precategory
  := ((cat_data X,,isPrecategory X),,has_homsets_cat_ob_mor X).

Definition get_ob {C:Precategory} {X:C^op⟶SET} (x:ob (cat X)) := pr1 x.

Definition get_el {C:Precategory} {X:C^op⟶SET} (x:ob (cat X)) := pr2 x.

Definition get_eqn {C} {X:C^op⟶SET} {x y:ob (cat_data X)} (f:x --> y) := pr2 f.

Definition make_ob {C:Precategory} (X:C^op⟶SET) (c:ob C) (x:X c:hSet) : ob (cat X)
  := (c,,x).

Definition make_mor {C:Precategory} (X:C^op⟶SET) (r s : ob (cat X))
           (f : Hom C (pr1 r) (pr1 s))
           (i : pr2 r = #X f (pr2 s)) : Hom _ r s
  := (f,,i).


(** *** functoriality of the construction of the category of elements *)

Definition cat_on_nat_trans_data {C:Precategory} {X Y:C^op⟶SET} (p:X ⟹ Y) :
  functor_data (cat X) (cat Y).
Proof. intros.
       exists (fun a => pr1 a,, p (pr1 a) (pr2 a)).
       exact (fun b c f => (pr1 f,,
                                (ap ((pr1 p) (pr1 b)) (pr2 f))
                                @ (eqtohomot (pr2 p (pr1 c) (pr1 b) (pr1 f)) (pr2 c)))).
Defined.

Lemma cat_on_nat_trans_is_nat_trans {C:Precategory} {X Y:C^op⟶SET} (p:X ⟹ Y) :
  is_functor (cat_on_nat_trans_data p).
Proof. intros. split.
  { intros a . apply mor_equality. reflexivity. }
  { intros a b c f g . apply mor_equality. reflexivity. } Qed.

Definition cat_on_nat_trans {C:Precategory} {X Y:C^op⟶SET} (p:X ⟹ Y) :
  cat X ⟶ cat Y.
Proof.
  intros.
  exact (cat_on_nat_trans_data p,, cat_on_nat_trans_is_nat_trans p). Defined.

(* maybe make a functor [C,SET] ⟶ [category of Precategories] *)


(** *** properties of projection to the original category *)

Module pr1.

  Definition fun_data {C:Precategory} (X:C^op⟶SET) :
      functor_data (Precategories.Precategory_obmor (cat X)) (Precategories.Precategory_obmor C).
    intros. exists pr1. intros x x'. exact pr1. Defined.

  Definition func {C:Precategory} (X:C^op⟶SET) : cat X ⟶ C.
    intros. exists (fun_data _).
    split. { intros a . reflexivity. } { intros a b c f g . reflexivity. } Defined.


  Lemma func_reflects_isos {C:Precategory} (X:C^op⟶SET) : Precategories.reflects_isos (func X).
  Proof. intros C X [c x] [d y] f Hf.
    apply is_iso_from_is_z_iso.
    set (H := is_z_iso_from_is_iso _ Hf). clearbody H. clear Hf.
    destruct f as [f i]. destruct H as [f' j].
    assert (i' : y = #X f' x).
         + intermediate_path (#X (identity d) y).
         - exact (eqtohomot (!functor_id X d) y).
         - intermediate_path (#X (f ∘ f') y).
           -- exact (eqtohomot (!ap #X (pr2 j)) y).
           -- intermediate_path (#X f' (#X f y)).
              --- exact (eqtohomot ((functor_comp X) f f') y).
              --- exact (ap (#X f') (!i)).
         + exists (f',, i'). split.
         - apply mor_equality. exact (pr1 j).
         - apply mor_equality. exact (pr2 j).
  Qed.

End pr1.
