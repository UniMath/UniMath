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
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
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
  use make_precategory_data.
  - exact (Kleisli_precat_ob_mor_monad T).
  - intro c.
    exact (η T c).
  - intros a b c f g.
    exact (f · (bind g)).
Defined.

Lemma Kleisli_precat_monad_is_precat {C : precategory} (T : Monad C) :
  is_precategory (Kleisli_precat_data_monad T).
Proof.
  apply is_precategory_one_assoc_to_two.
  split.
  - split.
    + intros a b f.
      unfold identity; unfold compose; cbn.
      apply η_bind.
    + intros a b f.
      unfold identity; unfold compose; cbn.
      rewrite <- id_right.
      apply cancel_precomposition.
      apply bind_η.
  - intros a b c d f g h.
    unfold compose; cbn.
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
  use make_functor_data.
  - apply idfun.
  - intros a b f; unfold idfun.
    exact (f · (η T) b).
Defined.

Lemma Left_Kleisli_is_functor {C : precategory} (T: Monad C) :
  is_functor (Left_Kleisli_functor_data T).
Proof.
  split.
  - intro a.
    unfold Left_Kleisli_functor_data; cbn.
    apply id_left.
  - intros a b c f g.
    unfold Left_Kleisli_functor_data; cbn.
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
  use make_functor_data.
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
    unfold functor_on_morphisms; cbn.
    apply bind_η.
  - intros a b c f g; cbn.
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
    + intros a b f; cbn.
      rewrite id_right.
      rewrite id_left.
      apply bind_comp_η.
Defined.

(*Showing that these functors are adjoints*)

Definition Kleisli_homset_iso {C : precategory} (T : Monad C) : natural_hom_weq (Left_Kleisli_functor T) (Right_Kleisli_functor T).
Proof.
  use tpair.
  - intros a b; cbn.
    apply idweq.
  - cbn; unfold idfun; split.
    + intros.
      rewrite <- assoc.
      apply cancel_precomposition.
      apply η_bind.
    + reflexivity.
Defined.

Definition Kleisli_functors_are_adjoints {C : precategory} (T : Monad C) : are_adjoints (Left_Kleisli_functor T) (Right_Kleisli_functor T) := adj_from_nathomweq (Kleisli_homset_iso T).

Definition Left_Kleisli_is_left_adjoint {C : precategory} (T : Monad C)
  : is_left_adjoint (Left_Kleisli_functor T)
    := are_adjoints_to_is_left_adjoint (Left_Kleisli_functor T)
    (Right_Kleisli_functor T) (Kleisli_functors_are_adjoints T).

Definition Right_Kleisli_is_right_adjoint {C : precategory} (T : Monad C)
  : is_right_adjoint (Right_Kleisli_functor T)
    := are_adjoints_to_is_right_adjoint (Left_Kleisli_functor T)
    (Right_Kleisli_functor T) (Kleisli_functors_are_adjoints T).

Theorem Kleisli_adjunction_monad_eq {C : precategory} (hs : has_homsets C) (T : Monad C)  : Monad_from_adjunction (Kleisli_functors_are_adjoints T) = T.
Proof.
  use Monad_eq_raw_data.
  - exact hs.
  - apply total2_paths_equiv; use tpair.
    + cbn.
      reflexivity.
    + cbn.
      apply total2_paths_equiv; use tpair.
      * cbn.
        apply total2_paths_equiv; use tpair.
        -- cbn.
           do 2 (apply funextsec; intro).
           apply funextfun; intro f.
           cbn.
           apply bind_comp_η.
        -- cbn.
           rewrite transportf_const.
           unfold idfun.
           apply funextsec; intro c.
           apply bind_identity.
      * cbn.
        rewrite transportf_const.
        reflexivity.
Defined.

End Kleisli_Categories.
