
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-    Definition of category of pointed endofunctors
-    Forgetful functor to category of endofunctors


************************************************************)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Local Open Scope cat.

Section def_ptd.

Context (C : category).

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
  apply homset_property.
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
    apply (@id_left (functor_category C C)).
  - apply (invmap (eq_ptd_mor _ _ )).
    apply (@id_right (functor_category _ _)).
  - apply (invmap (eq_ptd_mor _ _ )).
    apply (@assoc (functor_category _ _)).
  - apply (invmap (eq_ptd_mor _ _ )).
    apply (@assoc' (functor_category _ _)).
Qed.

Definition precategory_Ptd : precategory := tpair _ _ is_precategory_ptd.

Lemma has_homsets_precategory_Ptd: has_homsets precategory_Ptd.
Proof.
  red.
  intros F G.
  red.
  intros a b.
  apply (isofhlevelweqb 1 (eq_ptd_mor a b)).
  apply (homset_property (functor_category C C)).
Qed.

Definition category_Ptd : category := precategory_Ptd ,, has_homsets_precategory_Ptd.

Definition id_Ptd : category_Ptd.
Proof.
  exists (functor_identity _).
  exact (nat_trans_id _ ).
Defined.

Lemma eq_ptd_mor_cat {F G : category_Ptd} (a b : F --> G)
  : a = b ≃ (a : ptd_mor F G) = b.
Proof.
  use tpair.
  intro H.
  exact H.
  apply idisweq.
Defined.

(** Forgetful functor to functor category *)

Definition ptd_forget_data : functor_data category_Ptd [C, C].
Proof.
  exists (λ a, pr1 a).
  exact (λ a b f, pr1 f).
Defined.

Lemma is_functor_ptd_forget : is_functor ptd_forget_data.
Proof.
  split; intros; red; intros; apply idpath.
Qed.

Definition functor_ptd_forget : functor category_Ptd [C, C] := tpair _ _ is_functor_ptd_forget.

End def_ptd.

Arguments eq_ptd_mor { _ } _ { _ _ } .
