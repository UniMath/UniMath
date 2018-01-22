(** **********************************************************

Benedikt Ahrens March 2016, Anthony Bordg May 2017


************************************************************)


(** **********************************************************

Contents :

        - special comma categories (c ↓ K),
          called [cComma] (constant Comma)
        - forgetful functor [cComma_pr1]
        - morphism [f : C ⟦c, c'⟧] induces
          [functor_cComma_mor : functor (c' ↓ K) (c ↓ K)]
        - general comma precategories [comma_precategory]

************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.

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
  intermediate_path (pr2 a · identity _ );
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


(** * The general comma precategories *)

Section general_comma_precategories.

Local Open Scope cat.

(* We require that the target category C below has homsets *)

Context {C : category}.
Context {D E : precategory}.
Variable S : D ⟶ C.
Variable T : E ⟶ C.

Local Open Scope type_scope.
Local Open Scope cat.

Definition comma_cat_ob : UU := ∑ ed : ob E × ob D, C⟦T (pr1 ed), S (pr2 ed)⟧.

Definition comma_cat_mor : comma_cat_ob -> comma_cat_ob -> UU :=
  λ abf : comma_cat_ob,
    (λ cdg : comma_cat_ob,
             ∑ kh : E⟦pr1 (pr1 abf), pr1 (pr1 cdg)⟧ × D⟦pr2 (pr1 abf), pr2 (pr1 cdg)⟧, pr2 (abf) · #S(pr2 kh) = #T(pr1 kh) · pr2 (cdg)).

Definition comma_cat_ob_mor : precategory_ob_mor := precategory_ob_mor_pair comma_cat_ob comma_cat_mor.

Definition comma_cat_id : ∏ edf : comma_cat_ob_mor, comma_cat_ob_mor ⟦ edf, edf ⟧.
Proof.
  intro edf. cbn.
  exists (dirprodpair (identity (pr1 (pr1 edf))) (identity (pr2 (pr1 edf)))). cbn.
  abstract (
    rewrite 2 functor_id;
    rewrite id_right;
    rewrite id_left;
    apply idpath
    ).
Defined.

Definition comma_cat_comp : ∏ uvf xyg zwh : comma_cat_ob, comma_cat_mor uvf xyg → comma_cat_mor xyg zwh → comma_cat_mor uvf zwh.
Proof.
  intros uvf xyg zwh ijp klq.
  exists (dirprodpair (pr1 (pr1 ijp) · pr1 (pr1 klq)) (pr2 (pr1 ijp) · pr2 (pr1 klq))). cbn.
  abstract (
    rewrite 2 functor_comp;
    rewrite assoc;
    rewrite (pr2 ijp);
    rewrite <- assoc;
    rewrite (pr2 klq);
    rewrite assoc;
    apply idpath
    ).
Defined.

Definition comma_cat_id_comp : precategory_id_comp comma_cat_ob_mor := dirprodpair comma_cat_id comma_cat_comp.

Definition comma_cat_data : precategory_data := tpair _ comma_cat_ob_mor comma_cat_id_comp.

Definition comma_cat_data_id_left :  ∏ (abf cdg : comma_cat_data) (hkp : abf --> cdg), identity abf · hkp = hkp .
Proof.
  intros abf cdg hkp.
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply id_left.
    + cbn. apply id_left.
  - cbn. apply (homset_property C).
Qed.

Definition comma_cat_data_id_right :  ∏ (abf cdg : comma_cat_data) (hkp : abf --> cdg), hkp · identity cdg = hkp .
Proof.
  intros abf cdg hkp.
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply id_right.
    + cbn. apply id_right.
  - cbn. apply (homset_property C).
Qed.

Definition comma_cat_data_assoc :
  ∏ (stf uvg xyh zwi : comma_cat_data) (jkp : stf --> uvg) (lmq : uvg --> xyh) (nor : xyh --> zwi), jkp · (lmq · nor) = (jkp · lmq) · nor .
Proof.
  intros stf uvg xyh zwi jkp lmq nor.
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply assoc.
    + cbn. apply assoc.
  - apply (homset_property C).
Qed.

Definition is_precategory_comma_cat_data : is_precategory comma_cat_data :=
  mk_is_precategory comma_cat_data_id_left comma_cat_data_id_right comma_cat_data_assoc.

Definition comma_precategory : precategory := mk_precategory comma_cat_data is_precategory_comma_cat_data.


End general_comma_precategories.
