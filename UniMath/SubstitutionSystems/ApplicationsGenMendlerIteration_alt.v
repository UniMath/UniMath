(** proves Theorem 4.7 in Fiore & Saville, List Objects with Algebraic Structures, FSCD'17

    also instantiates it to present a variant of Lemma 4.8 in that paper

author: Ralph Matthes
formulation of Theorem 4.7 inspired by code provided by Ambroise Lafont available at https://github.com/amblafont/Skew-Monoidalcategories

2022
 *)

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Adamek.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.SubstitutionSystems.GenMendlerIteration_alt.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.


Import BifunctorNotations.

Local Open Scope cat.

Local Notation carrier := (alg_carrier _ ).

Section A.

  Context {D C B A : category}
    (OC : Initial C)
    (chC : Colims_of_shape nat_graph C)
    (* (chA : Colims_of_shape nat_graph A) - superfluous assumption in the paper *)
    {J : C ⟶ A} (OJ : isInitial _ (J (InitialObject OC)))
    (omegaJ : is_omega_cocont J)
    {F : bifunctor D C C}
    (omegaF : ∏ d , is_omega_cocont (leftwhiskering_functor F d))
    (G : bifunctor B A A)
    (* (omegaG : ∏ b , is_omega_cocont (leftwhiskering_functor G b)) - superfluous assumption in the paper *)
    {K : D ⟶ B}
    (h : binat_trans (compose_bifunctor_with_functor F J)
           (compose_functor_with_bifunctor K J G)).

  Let OA : Initial A := make_Initial _ OJ.

  Context {a : A} {d : D} (α : A ⟦ (K d) ⊗_{G} a , a ⟧).

  Let iniChd := (initChain OC (leftwhiskering_functor F d)).

  Let μFd := (InitialObject (colimAlgInitial OC (omegaF d) (chC iniChd))).

  Definition statement_Thm47 : UU :=
        ∃! (β : A ⟦ J (carrier μFd) , a ⟧),
                h d (carrier μFd) · K d ⊗^{G}_{l} β · α  =
                # J (alg_map (leftwhiskering_functor F d) μFd) · β.


  Definition Thm47 : statement_Thm47.
  Proof.
    red.
    set (Mendler := GenMendlerIteration OC chC (leftwhiskering_functor F d) (omegaF d) a J OJ omegaJ).
    transparent assert (ψ : (ψ_source a J ⟹ ψ_target (leftwhiskering_functor F d) a J)).
    { use make_nat_trans.
      - intros y f.
        cbn; red.
        exact (h d y · (K d) ⊗^{G}_{l} f · α).
      - intros y y' f. cbn in f. apply funextsec. intro g. cbn in g. red in g. cbn.
        repeat rewrite assoc. apply cancel_postcomposition.
        rewrite bifunctor_leftcomp.
        rewrite assoc. apply cancel_postcomposition.
        apply pathsinv0, (pr12 h).
    }
    set (Mendlerinst := Mendler ψ).
    use tpair.
    - exists (pr11 Mendlerinst).
      apply pathsinv0. exact (pr21 Mendlerinst).
    - intro t.
      induction t as [β βeq].
      assert (Mendlerinst2 := pr2 Mendlerinst (β,,!βeq)).
      use subtypePath.
      { intro g. apply A. }
      apply (maponpaths pr1) in Mendlerinst2.
      etrans.
      { exact Mendlerinst2. }
      apply idpath.
  Defined.

End A.

Section B.

  Context {C : category } (Mon_V : monoidal C)
    (OC : Initial C) (chC : Colims_of_shape nat_graph C)
    {F : bifunctor C C C} (omegaF : ∏ c , is_omega_cocont (leftwhiskering_functor F c))
    (** Lemma 4.8 in the paper asks for global omega-cocontinuity of [F] *)
    (p : C).
    (** we formulate the statement for each [p] individually *)

  Let J : C ⟶ C := rightwhiskering_functor Mon_V p.
  Let G : bifunctor C C C := compose_functor_with_bifunctor J (functor_identity C) F.

  (** the next two lemmas are no longer needed without the continuity requirement on [G] of the theorem *)
  Local Lemma lwG_is_lwF (c : C) : leftwhiskering_functor G c = leftwhiskering_functor F (c ⊗_{Mon_V} p).
  Proof.
    apply functor_eq.
    { apply C. }
    apply idpath.
  Qed.

  Local Lemma omegaG (c : C) : is_omega_cocont (leftwhiskering_functor G c).
  Proof.
    rewrite lwG_is_lwF. apply omegaF.
  Qed.

  Context (OJ : isInitial _ (J (InitialObject OC))) (omegaJ : is_omega_cocont J)
    (h: binat_trans (compose_bifunctor_with_functor F J)
          (compose_functor_with_bifunctor (functor_identity C) J G))
    (** the target functor of [h] is "morally" [compose_functor_with_bifunctor J J F],
        hence [h] qualifies as strength data for [F], in the sense of p.3 of the paper, however
        with only naturality in the arguments to [F] and w/o the coherence conditions  *)
    (z c : C) (γ : C ⟦ (z ⊗_{ Mon_V} p) ⊗_{ F} c, c ⟧).

  Definition statement_Lemma_48 : UU
    := statement_Thm47 (D:=C)(B:=C)(A:=C) OC chC omegaF (* omegaG *) (K:=functor_identity C) G h (a:=c)(d:=z) γ.

  Let cc := chC (initChain OC (leftwhiskering_functor F z)).

  Local Lemma statement_Lemma_48_ok : statement_Lemma_48 =
         ∃! β : C ⟦ colim cc ⊗_{ Mon_V} p, c ⟧,
                h z (colim cc) · (z ⊗_{ Mon_V} p) ⊗^{ F}_{l} β · γ =
                colim_algebra_mor OC (omegaF z) cc ⊗^{ Mon_V}_{r} p · β.
  Proof.
    apply idpath.
  Qed.

  Definition Lemma48 : statement_Lemma_48.
  Proof.
    red. apply Thm47.
    - exact OJ.
    - exact omegaJ.
  Defined.

End B.
