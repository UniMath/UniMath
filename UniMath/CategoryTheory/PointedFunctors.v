
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-    Definition of precategory of pointed endofunctors
-    Forgetful functor to precategory of endofunctors


************************************************************)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.

Section def_ptd.

Variable C : precategory.
Hypothesis hs : has_homsets C.

Definition ptd_obj : UU := ∑ F : functor C C, functor_identity C ⟹ F.

Coercion functor_from_ptd_obj (F : ptd_obj) : functor C C := pr1 F.

Definition ptd_pt (F : ptd_obj) : functor_identity C ⟹ F := pr2 F.

Definition is_ptd_mor {F G : ptd_obj}(α: F ⟹ G) : UU := ∏ c : C, ptd_pt F c · α c = ptd_pt G c.

Definition ptd_mor (F G : ptd_obj) : UU :=
  ∑ α : F ⟹ G, is_ptd_mor α.

Coercion nat_trans_from_ptd_mor {F G : ptd_obj} (a : ptd_mor F G) : nat_trans F G := pr1 a.

Lemma eq_ptd_mor {F G : ptd_obj} (a b : ptd_mor F G)
  : a = b ≃ (a : F ⟹ G) = b.
Proof.
  apply subtypeInjectivity.
  intro x.
  apply impred; intros ?.
  apply hs.
Defined.

Definition ptd_mor_commutes {F G : ptd_obj} (α : ptd_mor F G)
  : ∏ c : C, ptd_pt F c · α c = ptd_pt G c.
Proof.
  exact (pr2 α).
Qed.

Definition ptd_id (F : ptd_obj) : ptd_mor F F.
Proof.
  exists (nat_trans_id _ ).
  abstract (
      intro c;
      apply id_right) .
Defined.

Definition ptd_comp {F F' F'' : ptd_obj} (α : ptd_mor F F') (α' : ptd_mor F' F'')
  : ptd_mor F F''.
Proof.
  exists (nat_trans_comp _ _ _ α α').
  abstract (
      intro c; simpl;
      rewrite assoc ;
      set (H:=ptd_mor_commutes α c); simpl in H; rewrite H; clear H ;
      set (H:=ptd_mor_commutes α' c); simpl in H; rewrite H; clear H ;
      apply idpath ).
Defined.

Definition ptd_ob_mor : precategory_ob_mor.
Proof.
  exists ptd_obj.
  exact ptd_mor.
Defined.

Definition ptd_precategory_data : precategory_data.
Proof.
  exists ptd_ob_mor.
  exists ptd_id.
  exact @ptd_comp.
Defined.

Lemma is_precategory_ptd : is_precategory ptd_precategory_data.
Proof.
  repeat split; simpl; intros.
  - apply (invmap (eq_ptd_mor _ _ )).
    apply (@id_left (functor_precategory C C hs)).
  - apply (invmap (eq_ptd_mor _ _ )).
    apply (@id_right (functor_precategory _ _ hs )).
  - apply (invmap (eq_ptd_mor _ _ )).
    apply (@assoc (functor_precategory _ _ hs)).
Qed.

Definition precategory_Ptd : precategory := tpair _ _ is_precategory_ptd.

Definition id_Ptd : precategory_Ptd.
Proof.
  exists (functor_identity _).
  exact (nat_trans_id _ ).
Defined.

Lemma eq_ptd_mor_precat {F G : precategory_Ptd} (a b : F --> G)
  : a = b ≃ (a : ptd_mor F G) = b.
Proof.
  use tpair.
  intro H.
  exact H.
  apply idisweq.
Qed.

(** Forgetful functor to functor category *)

Definition ptd_forget_data : functor_data precategory_Ptd [C, C, hs].
Proof.
  exists (λ a, pr1 a).
  exact (λ a b f, pr1 f).
Defined.

Lemma is_functor_ptd_forget : is_functor ptd_forget_data.
Proof.
  split; simpl; intros.
  - unfold functor_idax; intros; apply idpath.
  - unfold functor_compax; intros; apply idpath.
Qed.

Definition functor_ptd_forget : functor _ _ := tpair _ _ is_functor_ptd_forget.

End def_ptd.
