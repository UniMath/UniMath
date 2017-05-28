(** Anthony Bordg, May 2017 *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

(** * The general comma categories *)

Section comma_categories.

Local Open Scope cat.

(* We require that the target category C below has homsets *)

Variable C : category.
Variables D E : precategory.
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

Definition comma_cat_id_comp : precategory_id_comp comma_cat_ob_mor.
Proof.
  use dirprodpair.
  - intro edf. cbn. destruct edf as [ed f]. destruct ed as [e d].
    exists (dirprodpair (identity e) (identity d)). cbn.
    rewrite 2 functor_id.
    rewrite id_right.
    rewrite id_left.
    apply idpath.
  - cbn. intros uvf xyg zwh ijp klq. destruct ijp as [ij p]. destruct klq as [kl q]. destruct ij as [i j]. destruct kl as [k l].
    exists (dirprodpair (i · k) (j · l)). cbn.
    rewrite 2 functor_comp. destruct uvf as [uv f]. cbn.
    rewrite assoc. cbn in p.
    rewrite p. destruct xyg as [xy g]. cbn. cbn in q.
    rewrite <- assoc.
    rewrite q.
    rewrite assoc.
    apply idpath.
Defined.

Definition comma_cat_data : precategory_data := tpair _ comma_cat_ob_mor comma_cat_id_comp.

Definition comma_cat_data_H1 :  ∏ (abf cdg : comma_cat_data) (hkp : abf --> cdg), identity abf · hkp = hkp .
Proof.
  intros abf cdg hkp. destruct hkp as [hk p]. destruct hk as [h k]. destruct abf as [ab f]. destruct ab as [a b].
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply id_left.
    + cbn. apply id_left.
  - cbn. apply (pr2 C).
Defined.

Definition comma_cat_data_H2 :  ∏ (abf cdg : comma_cat_data) (hkp : abf --> cdg), hkp · identity cdg = hkp .
Proof.
  intros abf cdg hkp. destruct hkp as [hk p]. destruct hk as [h k]. destruct abf as [ab f]. destruct ab as [a b].
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply id_right.
    + cbn. apply id_right.
  - cbn. apply (pr2 C).
Defined.

Definition comma_cat_data_H3 :
  ∏ (stf uvg xyh zwi : comma_cat_data) (jkp : stf --> uvg) (lmq : uvg --> xyh) (nor : xyh --> zwi), jkp · (lmq · nor) = (jkp · lmq) · nor .
Proof.
  intros stf uvg xyh zwi jkp lmq nor.
  destruct stf as [st f]. destruct st as [s t].
  destruct uvg as [uv g]. destruct uv as [u v].
  destruct xyh as [xy h]. destruct xy as [x y].
  destruct zwi as [zw i]. destruct zw as [z w].
  destruct jkp as [jk p]. destruct jk as [j k].
  destruct lmq as [lm q]. destruct lm as [l m].
  destruct nor as [no r]. destruct no as [n o].
  use total2_paths2_f.
  - use total2_paths2.
    + cbn. apply assoc.
    + cbn. apply assoc.
  - apply (pr2 C).
Defined.

Definition is_precategory_comma_cat_data : is_precategory comma_cat_data :=
  mk_is_precategory comma_cat_data_H1 comma_cat_data_H2 comma_cat_data_H3.

Definition comma_category : precategory := mk_precategory comma_cat_data is_precategory_comma_cat_data.

Local Close Scope cat.

End comma_categories.
