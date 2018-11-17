(** **********************************************************
Contents:
        - "Kleisli" definition of monad [Kleisli]
        - equivalence of this definition and the "monoidal" definition [weq_Kleisli_Monad]

Written by: Joseph Helfer, Matthew Weaver, 2017

************************************************************)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.RelativeMonads.

Local Open Scope cat.

(** * Definition of "Kleisli style" monad *)
Section Kleisli_def.

  Definition Kleisli (C : precategory_data) : UU := RelMonad (functor_identity C).

  Definition RelMonad_from_Kleisli {C : precategory_data} (T : Kleisli C) := (T : RelMonad (functor_identity C)).
  Coercion RelMonad_from_Kleisli : Kleisli >-> RelMonad.

End Kleisli_def.

(** * Equivalence of the types of Kleisli monads and "monoidal" monads *)
Section monad_types_equiv.
  Definition Monad_to_Kleisli {C : precategory} : Monad C → Kleisli C :=
    λ T, (functor_on_objects T ,, (pr1 (η T) ,, @bind C T))
               ,, @Monad_law2 C T ,, (@η_bind C T ,, @bind_bind C T).

  Definition Kleisli_to_functor {C : precategory} (T: Kleisli C) : C ⟶ C.
  Proof.
    use mk_functor.
    - use mk_functor_data.
      + exact T.
      + apply r_lift.
    - apply is_functor_r_lift.
  Defined.

  Definition Kleisli_to_μ {C : precategory} (T: Kleisli C) :
    Kleisli_to_functor T ∙ Kleisli_to_functor T ⟹ Kleisli_to_functor T.
  Proof.
    use tpair.
    - exact (λ (x : C), r_bind T (identity (T x))).
    - intros x x' f; simpl.
      unfold r_lift.
      now rewrite (r_bind_r_bind T), <- assoc, (r_eta_r_bind T (T x')), id_right, (r_bind_r_bind T), id_left.
  Defined.

  Definition Kleisli_to_η {C : precategory} (T: Kleisli C) :
    functor_identity C ⟹ Kleisli_to_functor T.
  Proof.
    use tpair.
    - exact (r_eta T).
    - intros x x' f; simpl.
      unfold r_lift.
      now rewrite (r_eta_r_bind T x).
  Defined.

  Definition Kleisli_to_Monad {C : precategory} (T : Kleisli C) : Monad C.
  Proof.
    use (((Kleisli_to_functor T,, Kleisli_to_μ T) ,, Kleisli_to_η T) ,, _).
    do 2 try apply tpair; intros; simpl.
    - apply (r_eta_r_bind T).
    - unfold r_lift. now rewrite (r_bind_r_bind T), <- assoc, (r_eta_r_bind T (T c)), id_right, (r_bind_r_eta T).
    - unfold r_lift. now rewrite !(r_bind_r_bind T), id_left, <- assoc, (r_eta_r_bind T (T c)), id_right.
  Defined.

  Proposition Kleisli_to_Monad_to_Kleisli {C : precategory} (hs : has_homsets C) (T : Kleisli C) :
    Monad_to_Kleisli (Kleisli_to_Monad T) = T.
  Proof.
    apply subtypeEquality'.
    - apply (maponpaths (λ p, tpair _ _ p )); simpl.
      apply dirprod_paths.
      * apply idpath.
      * repeat (apply funextsec; unfold homot; intro).
        simpl; unfold Monads.bind; simpl; unfold r_lift.
        now rewrite (r_bind_r_bind T), <- assoc, (r_eta_r_bind T (T x0)), id_right.
    - do 2 try apply isapropdirprod;
        do 5 try (apply impred; intro);
        apply hs.
  Defined.

  Lemma Monad_to_Kleisli_to_Monad_raw_data {C : precategory} (T : Monad C) :
    Monad_to_raw_data (Kleisli_to_Monad (Monad_to_Kleisli T)) = Monad_to_raw_data T.
  Proof.
    apply (maponpaths (λ p, tpair _ _ p )); simpl.
    apply dirprod_paths.
    + apply dirprod_paths;
        repeat (apply funextsec; unfold homot; intro);
        simpl.
      * unfold r_lift, r_bind, r_eta; simpl. unfold Monads.bind.
        rewrite (functor_comp T), <- assoc.
        change (# T x1 · (# T (η T x0) · μ T x0) = #T x1).
        now rewrite (@Monad_law2 C T x0), id_right.
      * unfold Monads.bind, r_bind; simpl.
        now rewrite (functor_id T), id_left.
    + apply idpath.
  Defined.

  Definition Monad_to_Kleisli_to_Monad {C : precategory} (hs : has_homsets C) (T : Monad C) :
    Kleisli_to_Monad (Monad_to_Kleisli T) = T.
  Proof.
    apply (Monad_eq_raw_data hs).
    apply Monad_to_Kleisli_to_Monad_raw_data.
  Defined.

  Definition isweq_Monad_to_Kleisli {C : precategory} (hs: has_homsets C) :
    isweq Monad_to_Kleisli :=
    isweq_iso _ _ (Monad_to_Kleisli_to_Monad hs) (Kleisli_to_Monad_to_Kleisli hs).

  Definition weq_Kleisli_Monad {C : precategory} (hs : has_homsets C) :
    (Monad C) ≃ (Kleisli C) := _,, (isweq_Monad_to_Kleisli hs).

End monad_types_equiv.
