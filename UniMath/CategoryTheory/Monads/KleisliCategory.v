(** **********************************************************
Contents:
        - Definition of the Kleisli category of a monad.
        - The canonical adjunction between a category C and the Kleisli
          category of a monad on C.
TODO:
        - Show that this definition is equivalent to the Kleisli category of a
          relative monad with respect to the identity functor.


Written by: Brandon Doherty (July 2018)
************************************************************)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

Section Monad_Lemmas.

(*A couple of lemmas involving bind*)

Lemma bind_comp_η {C : precategory} {T : Monad C} {a b : C} (f : C ⟦a , b⟧) :
  bind (f · (η T) b) = # T f.
Proof.
  unfold bind; rewrite functor_comp.
  rewrite <- assoc.
  rewrite <- id_right.
  apply cancel_precomposition.
  apply bind_η.
Qed.

Lemma bind_identity {C : precategory} {T : Monad C} (a : C) :
  bind (identity (T a)) = (μ T) a.
Proof.
  unfold bind.
  rewrite functor_id.
  apply id_left.
Qed.

End Monad_Lemmas.

Section Kleisli_Categories.

Definition Kleisli_precat_ob_mor_monad {C : precategory_data} (T : Monad_data C) :
  precategory_ob_mor.
Proof.
  use tpair.
  - exact (ob C).
  - intros X Y.
    exact (X --> T Y).
Defined.

Definition Kleisli_precat_data_monad {C : precategory_data} (T : Monad_data C) :
  precategory_data.
Proof.
  use precategory_data_pair.
  - exact (Kleisli_precat_ob_mor_monad T).
  - intro c.
    exact (η T c).
  - intros a b c f g.
    exact (f · (bind g)).
Defined.

Lemma Kleisli_precat_monad_is_precat {C : precategory} (T : Monad C) :
  is_precategory (Kleisli_precat_data_monad T).
Proof.
  split.
  - split.
    + intros a b f.
      unfold identity; unfold compose; simpl.
      apply η_bind.
    + intros a b f.
      unfold identity; unfold compose; simpl.
      rewrite <- id_right.
      apply cancel_precomposition.
      apply bind_η.
  - intros a b c d f g h.
    unfold compose; simpl.
    rewrite <- bind_bind.
    apply assoc.
Defined.

Definition Kleisli_precat_monad {C : precategory} (T : Monad C) : precategory := (Kleisli_precat_data_monad T,,Kleisli_precat_monad_is_precat T).

Lemma Kleisli_precat_monad_has_homsets {C : precategory} (T : Monad C)
      (hs : has_homsets C) : has_homsets (Kleisli_precat_data_monad T).
Proof.
  intros a b.
  apply hs.
Defined.

Definition Kleisli_cat_monad {C : category} (T : Monad C): category
  := (Kleisli_precat_monad T,, Kleisli_precat_monad_has_homsets T
  (homset_property C)).

(*TODO: show that this is equivalent to the definition of the Kleisli category of a relative monad with respect to the identity*)

(*The canonical adjunction between C and the Kleisli category of a monad on C*)

Definition Left_Kleisli_functor_data {C : precategory} (T: Monad C) :
  functor_data C (Kleisli_precat_monad T).
Proof.
  use mk_functor_data.
  - apply idfun.
  - intros a b f; unfold idfun.
    exact (f · (η T) b).
Defined.

Lemma Left_Kleisli_is_functor {C : precategory} (T: Monad C) :
  is_functor (Left_Kleisli_functor_data T).
Proof.
  split.
  - intro a.
    unfold Left_Kleisli_functor_data; simpl.
    apply id_left.
  - intros a b c f g.
    unfold Left_Kleisli_functor_data; simpl.
    unfold compose at 3; simpl.
    do 2 (rewrite <- assoc).
    apply cancel_precomposition.
    apply pathsinv0.
    apply η_bind.
Defined.

Definition Left_Kleisli_functor {C : precategory} (T : Monad C) :
  functor C (Kleisli_precat_monad T)
  := (Left_Kleisli_functor_data T,,Left_Kleisli_is_functor T).

Definition Right_Kleisli_functor_data {C : precategory} (T : Monad C) :
  functor_data (Kleisli_precat_monad T) C.
Proof.
  use mk_functor_data.
  - exact T.
  - intros a b.
    apply bind.
Defined.

Lemma Right_Kleisli_is_functor {C : precategory} (T : Monad C) :
  is_functor (Right_Kleisli_functor_data T).
Proof.
  use tpair.
  - intro a.
    unfold Right_Kleisli_functor_data; unfold identity;
    unfold functor_on_morphisms; simpl.
    apply bind_η.
  - intros a b c f g; simpl.
    apply pathsinv0.
    apply bind_bind.
Defined.

Definition Right_Kleisli_functor {C : precategory} (T : Monad C) :
  functor (Kleisli_precat_monad T) C
  := (Right_Kleisli_functor_data T,,Right_Kleisli_is_functor T).

(*Composition of the left and right Kleisli functors is equal to T as a functor*)

Definition Kleisli_functor_left_right_compose {C : precategory}
  (hs : has_homsets C) (T : Monad C) :
  (Left_Kleisli_functor T) ∙ (Right_Kleisli_functor T) = T.
Proof.
  use functor_eq.
  - exact hs.
  - use functor_data_eq_from_nat_trans.
    + intro a; apply idpath.
    + intros a b f; simpl.
      rewrite id_right.
      rewrite id_left.
      apply bind_comp_η.
Defined.

(*Showing that these functors are adjoints*)

Definition Kleisli_homset_iso {C : precategory} (T : Monad C) : natural_hom_weq (Left_Kleisli_functor T) (Right_Kleisli_functor T).
Proof.
  use tpair.
  - intros a b.
    use tpair.
    + simpl.
      apply idfun.
    + simpl.
      apply idisweq.
  - unfold idfun; split.
    + intros a b f c h.
      simpl.
      unfold compose at 1; simpl.
      rewrite <- assoc.
      apply cancel_precomposition.
      apply η_bind.
    + intros a b f c k; simpl.
      reflexivity.
Defined.

Definition Kleisli_functors_are_adjoints {C : precategory} (T : Monad C) : are_adjoints (Left_Kleisli_functor T) (Right_Kleisli_functor T) := adj_from_nathomweq (Kleisli_homset_iso T).

End Kleisli_Categories.
