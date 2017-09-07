(** ****************************************************************************

The category of elements of a presheaf "F : C^op ⟶ HSET"

Contents:

- Category of elements ([cat_of_elems])
- Functoriality of the constructon of the category of elements
  ([cat_of_elems_on_nat_trans])
- The forgetful functor from the category of elements to C
  ([cat_of_elems_forgetful])

Originally written by: Matthew Weaver (based on Elements.v by Dan Grayson)
Ported to CT by: Anders Mörtberg

*******************************************************************************)

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.

Local Open Scope cat.

Section cat_of_elems_def.

Context {C : precategory} (X : C^op ⟶ HSET).

Definition cat_of_elems_ob_mor : precategory_ob_mor.
Proof.
exists (∑ (c : C), X c : hSet).
intros a b.
apply (∑ (f : C⟦pr1 a,pr1 b⟧), (pr2 a) = # X f (pr2 b)).
Defined.

Definition cat_of_elems_data : precategory_data.
Proof.
exists cat_of_elems_ob_mor.
split.
+ intros a.
  exists (identity (pr1 a)).
  abstract (exact (eqtohomot (!(functor_id X) (pr1 a)) (pr2 a))).
+ intros a b c f g.
  exists (pr1 f · pr1 g).
  abstract (exact ((pr2 f) @ maponpaths (#X (pr1 f)) (pr2 g)
                    @ (eqtohomot (!(functor_comp X) (pr1 g) (pr1 f)) (pr2 c)))).
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

Context {C : precategory} {X Y : C^op ⟶ HSET}.

Definition get_ob (x : ∫ X) : C := pr1 x.
Definition get_el (x : ∫ X) : X (get_ob x) : hSet := pr2 x.
Definition get_eqn {x y : ∫ X} (f : (∫ X)⟦x,y⟧) :
  get_el x = # X (get_mor f) (get_el y)  := pr2 f.

Definition make_ob (c : C) (x : X c : hSet) : ∫ X := (c,,x).
Definition make_mor (r s : ∫ X) (f : C⟦get_ob r,get_ob s⟧)
  (i : get_el r = # X f (get_el s)) : (∫ X)⟦r,s⟧ := (f,,i).

(* Any f : J → I and ρ : X I defines a morphism from (J,,# X ρ) to (I,,ρ) in ∫ X *)
Definition mor_to_el_mor {I J : C} (f : J --> I) (ρ : pr1 X I : hSet) :
  ∫ X ⟦ make_ob J (# (pr1 X) f ρ), make_ob I ρ ⟧ :=
  make_mor (J,,# (pr1 X) f ρ) (I,,ρ) f (idpath (# (pr1 X) f ρ)).

Lemma base_paths_maponpaths_make_ob {I : C} x y (e : x = y) :
  base_paths _ _ (maponpaths (make_ob I) e) = idpath I.
Proof.
now induction e.
Qed.

Lemma transportf_make_ob_eq {I J} (f : C⟦J,I⟧) {a b} (e : make_ob J a = make_ob J b) :
  transportf (λ x : ∫ X, C⟦pr1 x,I⟧) e f = transportf (λ x, C⟦x,I⟧) (base_paths _ _ e) f.
Proof.
now induction e.
Qed.

Lemma transportf_make_ob {A : PreShv (∫ X)} {I : C} {x y} (e : x = y)
  (u : pr1 (pr1 A (make_ob I x))) :
    transportf (λ x, pr1 (pr1 A (make_ob I x))) e u =
    transportf (λ x, pr1 (pr1 A x)) (maponpaths (make_ob I) e) u.
Proof.
now induction e.
Qed.

Lemma make_ob_identity_eq {I : C} (ρ : pr1 (pr1 X I)) :
  make_ob I (# (pr1 X) (identity I) ρ) = make_ob I ρ.
Proof.
exact (maponpaths (make_ob I) (eqtohomot (functor_id X I) ρ)).
Defined.

Lemma mor_to_el_mor_id {I : C} (ρ : pr1 (pr1 X I)) :
  mor_to_el_mor (identity I) ρ =
  transportb (λ Z, ∫ X⟦Z, make_ob I ρ⟧) (make_ob_identity_eq ρ) (identity _).
Proof.
apply (@transportf_transpose _ (λ Z : ∫ X, ∫ X ⟦Z,_⟧)), cat_of_elems_mor_eq; simpl.
unfold transportb; rewrite pathsinv0inv0.
rewrite transportf_total2; simpl; rewrite transportf_make_ob_eq.
now unfold make_ob_identity_eq; rewrite base_paths_maponpaths_make_ob, idpath_transportf.
Qed.

Lemma make_ob_comp_eq {I J K} (ρ : pr1 (pr1 X I)) (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
  make_ob _ (# (pr1 X) (f · g) ρ) = make_ob _ (# (pr1 X) g (# (pr1 X) f ρ)).
Proof.
exact (maponpaths (make_ob K) (eqtohomot (functor_comp X f g) ρ)).
Defined.

Lemma mor_to_el_mor_comp {I J K} (ρ : pr1 (pr1 X I)) (f : C^op⟦I,J⟧) (g : C^op⟦J,K⟧) :
  mor_to_el_mor (f · g) ρ =
  transportb (λ Z, ∫ X⟦Z,_⟧) (make_ob_comp_eq ρ f g)
             (mor_to_el_mor g (# (pr1 X) f ρ) · mor_to_el_mor f ρ).
Proof.
apply (@transportf_transpose _ (λ Z : ∫ X, ∫ X ⟦Z,_⟧)), cat_of_elems_mor_eq; simpl.
unfold transportb; rewrite pathsinv0inv0.
rewrite transportf_total2; simpl; rewrite transportf_make_ob_eq.
now unfold make_ob_comp_eq; rewrite base_paths_maponpaths_make_ob, idpath_transportf.
Qed.

(** Functoriality of the construction of the category of elements *)
Definition cat_of_elems_on_nat_trans_data (α : X ⟹ Y) :
  functor_data (∫ X) (∫ Y).
Proof.
exists (λ a, (get_ob a,, α (get_ob a) (get_el a))).
intros b c f.
exists (get_mor f).
abstract (exact (maponpaths (α (get_ob b)) (get_eqn f)
                @ eqtohomot (pr2 α (get_ob c) (get_ob b) (get_mor f)) (get_el c))).
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
assert (i' : y = #X f' x).
{ intermediate_path (#X (identity d) y).
  - exact (eqtohomot (!functor_id X d) y).
  - intermediate_path (#X (f ∘ f') y).
    + exact (eqtohomot (!maponpaths #X (pr2 j)) y).
    + intermediate_path (#X f' (#X f y)).
      * exact (eqtohomot ((functor_comp X) f f') y).
      * exact (maponpaths (#X f') (!i)).
}
exists (f',,i').
split; apply cat_of_elems_mor_eq; [ exact (pr1 j) | exact (pr2 j) ].
Qed.

End cat_of_elems_theory.
