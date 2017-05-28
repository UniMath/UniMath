(** **********************************************************

Benedikt Ahrens
March 2016


************************************************************)


(** **********************************************************

Contents :

        - special comma categories (c ↓ K),
          called [cComma] (constant Comma)
        - forgetful functor [cComma_pr1]
        - morphism [f : C ⟦c, c'⟧] induces
          [functor_cComma_mor : functor (c' ↓ K) (c ↓ K)]

************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.

Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).


Section const_comma_category_definition.

Context {M C : precategory}.
Variable hsC : has_homsets C.
Variable hsM : has_homsets M.
Variable K : functor M C.
Variable c : C.

Definition ccomma_object : UU := ∑ m, C⟦c, K m⟧.
Definition ccomma_morphism (a b : ccomma_object) : UU
  := ∑ f : _ ⟦pr1 a, pr1 b⟧, pr2 a · #K f = pr2 b.

Definition isaset_ccomma_morphism a b : isaset (ccomma_morphism a b).
Proof.
  apply (isofhleveltotal2 2).
  - apply hsM.
  - intro.
    apply hlevelntosn.
    apply hsC.
Qed.

Definition cComma_mor_eq a b (f f' : ccomma_morphism a b)
  : pr1 f = pr1 f' -> f = f'.
Proof.
  intro H.
  apply subtypeEquality.
  intro. apply hsC.
  exact H.
Qed.

Definition ccomma_id a : ccomma_morphism a a.
Proof.
  exists (identity _ ).
  abstract (
  pathvia (pr2 a · identity _ );
   [ apply maponpaths; apply functor_id |];
  apply id_right
  ).
Defined.

Definition ccomma_comp a b d :
  ccomma_morphism a b -> ccomma_morphism b d -> ccomma_morphism a d.
Proof.
  intros f g.
  exists (pr1 f · pr1 g).
  abstract (
  rewrite functor_comp;
  rewrite assoc;
  rewrite (pr2 f);
  apply (pr2 g)
   ).
Defined.

Definition ccomma_precategory_ob_mor : precategory_ob_mor.
Proof.
  exists ccomma_object.
  exact ccomma_morphism.
Defined.

Definition ccomma_precategory_data : precategory_data.
Proof.
  exists ccomma_precategory_ob_mor.
  split.
  - exact ccomma_id.
  - exact ccomma_comp.
Defined.

Definition is_precategory_ccomma_precategory_data
  : is_precategory ccomma_precategory_data.
Proof.
  repeat split.
  - intros. apply cComma_mor_eq.
    simpl. apply id_left.
  - intros. apply cComma_mor_eq.
    simpl. apply id_right.
  - intros. apply cComma_mor_eq.
    simpl. apply assoc.
Qed.

Definition cComma : precategory.
Proof.
  exists ccomma_precategory_data.
  exact is_precategory_ccomma_precategory_data.
Defined.


Definition ccomma_pr1_functor_data : functor_data cComma M.
Proof.
  exists pr1.
  intros a b f. exact (pr1 f).
Defined.

Lemma is_functor_ccomma_pr1 : is_functor ccomma_pr1_functor_data.
Proof.
  split.
  - intro a. apply idpath.
  - intros ? ? ? ? ?. apply idpath.
Qed.

Definition cComma_pr1 : functor _ _ := tpair _ _ is_functor_ccomma_pr1.


End const_comma_category_definition.

Section lemmas_on_const_comma_cats.


Context {M C : precategory}.
Variable hsC : has_homsets C.
Variable hsM : has_homsets M.

Local Notation "c ↓ K" := (cComma hsC K c) (at level 3).

Variable K : functor M C.
Context {c c' : C}.
Variable h : _ ⟦c, c'⟧.


Definition cComma_mor_ob : c' ↓ K → c ↓ K.
Proof.
  intro af.
  exists (pr1 af).
  exact (h · pr2 af).
Defined.

Definition cComma_mor_mor (af af' : c' ↓ K) (g : _ ⟦af, af'⟧)
  : _ ⟦cComma_mor_ob af, cComma_mor_ob af'⟧.
Proof.
  exists (pr1 g).
  abstract (
    simpl;
    rewrite <- assoc;
    rewrite (pr2 g);
    apply idpath
    ).
Defined.

Definition cComma_mor_functor_data : functor_data (c' ↓ K) (c ↓ K).
Proof.
  exists cComma_mor_ob.
  exact cComma_mor_mor.
Defined.

Lemma is_functor_cComma_mor_functor_data : is_functor cComma_mor_functor_data.
Proof.
  split.
  - intro. apply cComma_mor_eq. { apply hsC. }
    apply idpath.
  - intros ? ? ? ? ?. apply cComma_mor_eq. { apply hsC. }
    apply idpath.
Qed.

Definition functor_cComma_mor : functor _ _ := tpair _ _ is_functor_cComma_mor_functor_data.

End lemmas_on_const_comma_cats.
