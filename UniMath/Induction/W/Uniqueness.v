(** ** Uniqueness of W-types

    W-types are unique up to propositional equality.

    Author: Langston Barrett (@siddharthist)
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.W.Core.

Section Uniqueness.

  Local Open Scope functions.
  Local Open Scope cat.

  Context (A : UU).
  Context (B : A → UU).

  (** Following the paper, we have [X ⇒ Y] = Hom(X, Y) *)
  Local Notation F := (polynomial_functor A B). (* can be coerced to a function *)
  Local Notation "F*" := (polynomial_functor_arr A B).
  Local Notation "X ⇒ Y" := (algebra_mor F X Y).

  (** Since we can't use the standard categorical proof, we must re-prove that
      initial algebras are unique up to isomorphism.
   *)

  (** We prove that their carriers (first projections) are isomorphic, and hence
      equal (by univalence).

      This is standard categorical reasoning: each has exactly one arrow to the
      other, which, composing, gives an endormorphism. However, each has exactly
      one endomorphism, the identity map. Therefore, they are isomorphic. *)

  Lemma W_carriers_iso : ∏ X Y : W B, (alg_carrier F X) ≃
                                      (alg_carrier F Y).
  Proof.
    intros X Y.

    (** Get the algebra morphisms X → Y and Y → X via initiality *)
    pose (X_mor_Y := iscontrpr1 (pr2 X Y)).
    pose (Y_mor_X := iscontrpr1 (pr2 Y X)).

    apply (weq_iso
             (mor_from_algebra_mor _ _ _ X_mor_Y)
             (mor_from_algebra_mor _ _ _ Y_mor_X)).
    - intro x.
      apply (toforallpaths _ (Y_mor_X ∘ X_mor_Y) (idfun _)).
      refine (base_paths (algebra_mor_comp _ _ _ _ X_mor_Y Y_mor_X)
                         (algebra_mor_id F X) _).
      apply (proofirrelevancecontr (pr2 X X)).
    - intro y.
      apply (toforallpaths _ (X_mor_Y ∘ Y_mor_X) (idfun _)).
      refine (base_paths (algebra_mor_comp _ _ _ _ Y_mor_X X_mor_Y)
                         (algebra_mor_id F Y) _).
      apply (proofirrelevancecontr (pr2 Y Y)).
  Defined.

  (** Note the crucial use of univalence *)
  Lemma W_carriers_eq : ∏ X Y : W B, (alg_carrier _ X) = (alg_carrier _ Y).
  Proof.
    exact (fun X Y => weqtopaths (W_carriers_iso X Y)).
  Defined.

  (** Now we must prove that the algebra morphisms, when transported along
      the path W_carriers_eq, will be equal. *)
  Lemma W_alg_eq : ∏ X Y : W B, W_algebra B X = W_algebra B Y.
  Proof.
    intros X Y.
    pose (f := pr1 ((pr2 X) (W_algebra B Y))).
    pose (pr1eq := (W_carriers_eq X Y)).
    apply (total2_paths_f pr1eq).

    (** Some shorthands for items we'll use *)
    pose (is_final_X := pr2 X).
    pose (is_final_Y := pr2 Y).
    pose (θ := pr2 (pr1 X)).
    pose (ψ := pr2 (pr1 Y)).

    (** substⁱ-lemma in HoTT/W-types *)
    assert (trans_fun : forall {X Y : UU} {F : UU → UU} {f : F X → X} {g : F Y → Y}
                          (p : X = Y),
               (forall (x : F X),
                   g (transportf F p x) = (transportf (idfun UU) p (f x))) →
               (* (forall (x : X), *)
               (*     transportf F p (f x) = g (transportf (idfun UU) p x)) → *)
               transportf (λ X, F X → X) p f = g).
    {
      intros ? ? ? ? ? p H.
      induction p.
      apply funextfun.
      intro x.
      exact (!H x).
    }

    apply trans_fun.
    intro x.

    assert (arr_transport :
              forall {X Y : UU} (p : X = Y), F* (transportf (idfun _) p) = transportf F p).
    {
      intros ? ? p.
      induction p.
      reflexivity.
    }

    assert (lemma1 : forall x : pr1 (pr1 X),
               (pr1 f) x = transportf (idfun UU) pr1eq x ).
    {
      intro.
      refine (toforallpaths _ _ _ _ x0).
      refine (_ @ !(weqpath_transport (W_carriers_iso X Y))).
      reflexivity.
    }

    assert (lemma2 : transportf F pr1eq = F* (pr1 f)).
    {
      refine (!(arr_transport _ _ pr1eq) @ _).
      apply maponpaths.
      unfold pr1eq, W_carriers_eq.
      refine ((weqpath_transport (W_carriers_iso X Y)) @ _).
      reflexivity.
    }

    refine (_ @ lemma1 (θ x)).
    refine (maponpaths ψ (toforallpaths _ _ _ lemma2 x) @ _).

    (** Now our goal is simply the condition that f is a algebra morphism *)
    apply (toforallpaths _ (λ x, ψ (F* (pr1 f) x)) (pr1 f ∘ θ)).
    exact (!pr2 f).
  Defined.

  Lemma isaprop_W : isaprop (W B).
    apply invproofirrelevance.
    intros X Y.
    apply subtypeEquality.
    - exact isaprop_is_initial.
    - exact (W_alg_eq X Y).
  Defined.
End Uniqueness.
