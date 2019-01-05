(** * Setcategories: Precategories whose objects and morphisms are sets *)

(** ** Contents

  - Setcategories: objects and morphisms are sets [setcategory]
 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.

Local Open Scope cat.

Definition object_hlevel (n : nat) (C : precategory) : hProp :=
  hProppair _ (isapropisofhlevel n (ob C)).

(* TODO: someday, [has_homsets] should be rephrased in terms of this *)
Definition homtype_hlevel (n : nat) (C : precategory) : hProp :=
  hProppair (∏ a b : C, isofhlevel n (C ⟦ a, b ⟧))
            (impred _ _ (λ _, impred _ _ (λ _, isapropisofhlevel n _))).

Definition object_homtype_hlevel (n m : nat) (C : precategory) : hProp :=
  object_hlevel n C ∧ homtype_hlevel m C.

Definition is_setcategory : precategory → UU := object_homtype_hlevel 2 2.
Definition setcategory := total2 is_setcategory.
Definition category_from_setcategory (C : setcategory) : category :=
  (pr1 C,, (dirprod_pr2 (pr2 C))).
Coercion category_from_setcategory : setcategory >-> category.

Lemma isaprop_is_setcategory (C : precategory) : isaprop (is_setcategory C).
Proof.
  apply isapropdirprod.
  - apply isapropisaset.
  - apply isaprop_has_homsets.
Defined.

Definition setcategory_objects_set (C : setcategory) : hSet :=
    hSetpair (ob C) (pr1 (pr2 C)).

Definition isaset_ob (C : setcategory) : isaset C := (dirprod_pr1 (pr2 C)).
Definition isaset_mor (C : setcategory) : has_homsets C := homset_property C.

Lemma setcategory_eq_morphism_pi (C : setcategory) (a b : ob C)
      (e e': a = b) : idtomor _ _ e = idtomor _ _ e'.
Proof.
  assert (h : e = e').
  apply uip. apply (pr2 C).
  apply (maponpaths (idtomor _ _ ) h).
Qed.