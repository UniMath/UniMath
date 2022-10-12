(** * Setcategories: Precategories whose objects and morphisms are sets *)

(** ** Contents

  - Setcategories: objects and morphisms are sets [setcategory]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.

Local Open Scope cat.

Definition object_hlevel (n : nat) (C : precategory) : hProp :=
  make_hProp _ (isapropisofhlevel n (ob C)).

(* TODO: someday, [has_homsets] should be rephrased in terms of this *)
Definition homtype_hlevel (n : nat) (C : precategory) : hProp :=
  make_hProp (∏ a b : C, isofhlevel n (C ⟦ a, b ⟧))
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
    make_hSet (ob C) (pr1 (pr2 C)).

Definition isaset_ob (C : setcategory) : isaset C := (dirprod_pr1 (pr2 C)).
Definition isaset_mor (C : setcategory) : has_homsets C := homset_property C.

Lemma setcategory_eq_morphism_pi (C : setcategory) (a b : ob C)
      (e e': a = b) : idtomor _ _ e = idtomor _ _ e'.
Proof.
  assert (h : e = e').
  apply uip. apply (pr2 C).
  apply (maponpaths (idtomor _ _ ) h).
Qed.

Definition setcategory_eq_idtoiso
          {C : setcategory}
          {x y : C}
          (p q : x = y)
  : pr1 (idtoiso p) = pr1 (idtoiso q).
Proof.
  do 2 apply maponpaths.
  apply C.
Qed.

Definition setcategory_refl_idtoiso
          {C : setcategory}
          {x : C}
          (p : x = x)
  : pr1 (idtoiso p) = identity _.
Proof.
  apply (setcategory_eq_idtoiso p (idpath x)).
Qed.

Definition setcategory_eq_idtoiso_comp
           {C : setcategory}
           {x x' y y' : C}
           (p p' : x = x')
           (f : x' --> y)
           (q q' : y = y')
  : idtoiso p · f · idtoiso q
    =
    idtoiso p' · f · idtoiso q'.
Proof.
  etrans.
  {
    apply maponpaths.
    exact (setcategory_eq_idtoiso q q').
  }
  do 2 apply maponpaths_2.
  apply setcategory_eq_idtoiso.
Qed.

Definition from_eq_cat_of_setcategory
           {C₁ C₂ : setcategory}
           {F₁ F₂ : C₁ ⟶ C₂}
           (p : F₁ = F₂)
           {x₁ x₂ : pr1 C₁}
          (f : x₁ --> x₂)
  : # (pr1 F₁) f
    =
    idtoiso (maponpaths (λ z, pr11 z x₁) p)
    · # (pr1 F₂) f
    · idtoiso (maponpaths (λ z, pr11 z x₂) (!p)).
Proof.
  induction p ; cbn.
  rewrite id_left, id_right.
  apply idpath.
Qed.
