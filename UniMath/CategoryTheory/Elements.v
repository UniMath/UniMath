(** ****************************************************************************

The category of elements of a functor "F : C ⟶ HSET"

Contents:

- Category of elements ([cat_of_elems])
- Functoriality of the constructon of the category of elements
  ([cat_of_elems_on_nat_trans])
- The forgetful functor from the category of elements to C
  ([cat_of_elems_forgetful])

Originally written by: Dan Grayson
Ported to CT by: Anders Mörtberg

*******************************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.

Local Open Scope cat.

Section cat_of_elems_def.

Context {C : precategory} (X : C ⟶ HSET).

Definition cat_of_elems_ob_mor : precategory_ob_mor.
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

End cat_of_elems_def.

Arguments get_mor {_ _ _ _} _.

(** Type as \int in Agda mode *)
Notation "∫ X" := (cat_of_elems X) (at level 3) : cat.

Section cat_of_elems_theory.

Context {C : precategory} {X Y : C ⟶ HSET}.

Definition get_ob (x : ∫ X) : C := pr1 x.
Definition get_el (x : ∫ X) : X (get_ob x) : hSet := pr2 x.
Definition get_eqn {x y : ∫ X} (f : (∫ X)⟦x,y⟧) :
  # X (get_mor f) (get_el x) = get_el y := pr2 f.

Definition make_ob (c : C) (x : X c : hSet) : ∫ X := (c,,x).
Definition make_mor (r s : ∫ X) (f : C⟦get_ob r,get_ob s⟧)
  (i : # X f (get_el r) = get_el s) : (∫ X)⟦r,s⟧ := (f,,i).


(** Functoriality of the construction of the category of elements *)
Definition cat_of_elems_on_nat_trans_data (α : X ⟹ Y) :
  functor_data (∫ X) (∫ Y).
Proof.
exists (λ a, (get_ob a,,α (get_ob a) (get_el a))).
intros b c f.
exists (get_mor f).
abstract (exact (!eqtohomot (pr2 α (get_ob b) (get_ob c) (get_mor f)) (get_el b)
                @ maponpaths (α (get_ob c)) (get_eqn f))).
Defined.

Lemma cat_of_elems_on_nat_trans_is_functor (α : X ⟹ Y) :
  is_functor (cat_of_elems_on_nat_trans_data α).
Proof.
split.
- now intros a; apply cat_of_elems_mor_eq.
- now intros a b c f g; apply cat_of_elems_mor_eq.
Qed.

Definition cat_of_elems_on_nat_trans (α : X ⟹ Y) : ∫ X ⟶ ∫ Y :=
  (cat_of_elems_on_nat_trans_data α,,cat_of_elems_on_nat_trans_is_functor α).

(* maybe make a functor [C,SET] ⟶ [category of Precategories] *)

(** The forgetful functor from the category of elements to C *)
Definition cat_of_elems_forgetful : ∫ X ⟶ C.
Proof.
use mk_functor.
- exists pr1.
  intros a b; apply pr1.
- now split.
Defined.

Lemma reflects_isos_cat_of_elems_forgetful : reflects_isos cat_of_elems_forgetful.
Proof.
intros [c x] [d y] f Hf.
apply is_iso_from_is_z_iso.
assert (H := is_z_iso_from_is_iso _ Hf); clear Hf.
destruct f as [f i]; destruct H as [f' j].
assert (i' : #X f' y = x).
{ intermediate_path (#X f' (#X f x)).
  - exact (maponpaths (#X f') (!i)).
  - intermediate_path (#X (f' ∘ f) x).
    + exact (eqtohomot (!functor_comp X f f') x).
    + intermediate_path (#X (identity c) x).
      * exact (eqtohomot (maponpaths #X (pr1 j)) x).
      * exact (eqtohomot (functor_id X c) x).
}
exists (f' ,, i').
split; apply cat_of_elems_mor_eq; [ exact (pr1 j) | exact (pr2 j) ].
Qed.

End cat_of_elems_theory.
