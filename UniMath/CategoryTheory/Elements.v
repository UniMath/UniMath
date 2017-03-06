(** *** the category of elements of a functor *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.category_hset.

Local Open Scope cat.

Section cov_cat_elems_def.

Context {C : precategory} (X : C ⟶ HSET).

Definition cat_of_elems_ob_mor  : precategory_ob_mor.
Proof.
exists (∑ (c : C), X c : hSet).
intros a b.
apply (∑ (f : C⟦pr1 a,pr1 b⟧), # X f (pr2 a) = pr2 b).
Defined.

Definition cat_of_elems_data : precategory_data.
Proof.
exists cat_of_elems_ob_mor.
split.
+ intros a.
  exists (identity (pr1 a)).
  abstract (exact (eqtohomot ((functor_id X) (pr1 a)) (pr2 a))).
+ intros a b c f g.
  exists (pr1 f · pr1 g).
  abstract (exact ((eqtohomot ((functor_comp X) (pr1 f) (pr1 g)) (pr2 a))
                      @ (maponpaths (# X (pr1 g)) (pr2 f) @ (pr2 g)))).
Defined.

Definition get_mor {x y : cat_of_elems_data} (f : _⟦x,y⟧) := pr1 f.

Lemma cat_of_elems_mor_eq (x y : cat_of_elems_data) (f g : _⟦x,y⟧) :
  get_mor f = get_mor g → f = g.
Proof.
intros p.
apply subtypeEquality.
- intro r; apply setproperty.
- exact p.
Qed.

Lemma is_precategory_cat_of_elems_data : is_precategory cat_of_elems_data.
Proof.
split; [split|]; intros; apply cat_of_elems_mor_eq.
+ apply id_left.
+ apply id_right.
+ apply assoc.
Qed.

Definition cat_of_elems : precategory :=
  (cat_of_elems_data,,is_precategory_cat_of_elems_data).

Lemma has_homsets_cat_of_elems (hsC : has_homsets C) : has_homsets cat_of_elems.
Proof.
intros a b.
apply isaset_total2.
- apply hsC.
- intro f. apply isasetaprop, setproperty.
Qed.

End cov_cat_elems_def.

Notation "∫ X" := (cat_of_elems X) (at level 3) : cat.

Section cov_cat_elems_theory.

Context {C : precategory} {X Y : C ⟶ HSET}.

Definition get_ob (x : ∫ X) := pr1 x.
Definition get_el (x : ∫ X) := pr2 x.
Definition get_eqn {x y : ∫ X} (f : (∫ X)⟦x,y⟧) := pr2 f.

Definition make_ob (c : C) (x : pr1 X c : hSet) : ∫ X := (c,,x).

Definition make_mor (r s : ∫ X) (f : C⟦pr1 r,pr1 s⟧) (i : # X f (pr2 r) = pr2 s) : (∫ X)⟦r,s⟧
  := (f,,i).


(** *** Functoriality of the construction of the category of elements *)
Definition cat_of_elems_on_nat_trans_data (α : X ⟹ Y) : functor_data (∫ X) (∫ Y).
Proof.
exists (λ a, (pr1 a,, α (pr1 a) (pr2 a))).
intros b c f.
exists (pr1 f).
abstract (exact (! (eqtohomot (pr2 α (pr1 b) (pr1 c) (pr1 f)) (pr2 b))
                   @ maponpaths ((pr1 α) (pr1 c)) (pr2 f))).
Defined.

Lemma cat_of_elems_on_nat_trans_is_functor (α : X ⟹ Y) :
  is_functor (cat_of_elems_on_nat_trans_data α).
Proof.
split.
- now intros a; apply cat_of_elems_mor_eq.
- now intros a b c f g; apply cat_of_elems_mor_eq.
Qed.

Definition cat_of_elems_on_nat_trans (α : X ⟹ Y) : ∫ X ⟶ ∫ Y :=
  (cat_of_elems_on_nat_trans_data α,, cat_of_elems_on_nat_trans_is_functor α).

(* maybe make a functor [C,SET] ⟶ [category of Precategories] *)

End cov_cat_elems_theory.

(** *** properties of projection to the original category *)

(* TODO: port *)
(* Module pr1. *)

(*   Definition fun_data {C:Precategory} (X:C⟶SET) : *)
(*       functor_data (Precategories.Precategory_obmor (cat X)) (Precategories.Precategory_obmor C). *)
(*     intros. exists pr1. intros x x'. exact pr1. Defined. *)

(*   Definition func {C:Precategory} (X:C⟶SET) : cat X ⟶ C. *)
(*     intros. exists (fun_data _). *)
(*     split. { intros a . reflexivity. } { intros a b c f g . reflexivity. } Defined. *)


(*   Lemma func_reflects_isos {C:Precategory} (X:C⟶SET) : Precategories.reflects_isos (func X). *)
(*   Proof. intros C X [c x] [d y] f Hf. *)
(*     apply is_iso_from_is_z_iso. *)
(*     set (H := is_z_iso_from_is_iso _ Hf). clearbody H. clear Hf. *)
(*     destruct f as [f i]. destruct H as [f' j]. *)
(*         assert (i' : #X f' y = x). *)
(*     { intermediate_path (#X f' (#X f x)). *)
(*       { exact (ap (#X f') (!i)). } *)
(*       { intermediate_path (#X (f' ∘ f) x). *)
(*         { exact (eqtohomot (!functor_comp X f f') x). } *)
(*         { intermediate_path (#X (identity c) x). *)
(*           { exact (eqtohomot (ap #X (pr1 j)) x). } *)
(*           { exact (eqtohomot (functor_id X c) x). }}}} *)
(*     { exists (f' ,, i'). split. *)
(*       { apply mor_equality.  exact (pr1 j). } *)
(*       { apply mor_equality.  exact (pr2 j). } } Qed. *)

(* End pr1. *)
