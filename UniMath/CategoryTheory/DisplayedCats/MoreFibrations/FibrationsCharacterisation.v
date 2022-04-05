(** Definitions of various kinds of Lemmas about _fibrations_, leading up to a theorem characterizing their composites. *)

Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence. (* only coercions *)
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Presheaf.
Local Open Scope cat.

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.DisplayedCats.MoreFibrations.Prefibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.MoreFibrations.CartesiannessOfComposites.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

Definition precleaving_comp_is_precart
    {C : category} {D : disp_cat C} (lift : precleaving D)
  := forall (c c' c'' : C) (f' : c'' --> c') (f : c' --> c) (d : D c),
    is_precartesian ((lift _ _ f' (object_of_precartesian_lift (lift _ _ f d))) ;; (lift _ _ f d)).

Definition precleaving_is_cleaving
    {C : category} {D : disp_cat C} (lift : precleaving D)
:= forall (c c' : C) (f: c' --> c) (d : D c), is_cartesian (lift _ _ f d).

Lemma transportf_cancel
      {X : UU} (P : X → UU) {x x' : X} (e : x = x') (y0 y1 : P x):
      transportf P e y0 = transportf P e y1 -> y0 = y1.
Proof.
  induction e.
  apply idfun.
Defined.

Definition assoc_eq {C} {D : disp_precat C}
    {x y z w} {f} {g} {h} {xx : D x} {yy : D y} {zz : D z} {ww : D w}
    (ff ff' : xx -->[f] yy) (gg gg' : yy -->[g] zz) (hh hh' : zz -->[h] ww)
  : ff ;; (gg ;; hh) = ff' ;; (gg' ;; hh') -> (ff ;; gg) ;; hh = (ff' ;; gg') ;; hh'.
Proof.
  intro H.
  eapply pathscomp0.
  - apply assoc_disp_var.
  - eapply pathscomp0.
    + apply maponpaths.
      exact H.
    + apply pathsinv0.
      apply assoc_disp_var.
Qed.

Definition assoc_eq_var {C} {D : disp_precat C}
    {x y z w} {f} {g} {h} {xx : D x} {yy : D y} {zz : D z} {ww : D w}
    (ff ff' : xx -->[f] yy) (gg gg' : yy -->[g] zz) (hh hh' : zz -->[h] ww)
  : (ff ;; gg) ;; hh = (ff' ;; gg') ;; hh' -> ff ;; (gg ;; hh) = ff' ;; (gg' ;; hh').
Proof.
  intro H.
  eapply pathscomp0.
  - apply assoc_disp.
  - eapply pathscomp0.
    + apply maponpaths.
      exact H.
    + apply pathsinv0.
      apply assoc_disp.
Qed.


Definition prefibration_w_precart_closed_implies_fibration
    {C : category} {D : disp_cat C} (lift : precleaving D)
  : precleaving_comp_is_precart lift -> precleaving_is_cleaving lift.
Proof.
  unfold precleaving_comp_is_precart, precleaving_is_cleaving.
  intros liftclosed c c' f d.
  unfold is_cartesian.
  intros c'' g d'' hh.
  apply iscontraprop1.
  - apply invproofirrelevance.
    unfold isProofIrrelevant.
    intros [gg0 comm0] [gg1 comm1].
    apply subtypePairEquality.
    + intro gg.
      apply homsets_disp.
    + eapply transportf_cancel.
      eapply pathscomp0.
      * apply pathsinv0.
        use precartesian_factorisation_commutes.
        3: { use precartesian_lift_is_precartesian. apply lift. }
      * eapply pathscomp0.
        2: { use precartesian_factorisation_commutes.
          3: { use precartesian_lift_is_precartesian. apply lift. } }
        -- apply maponpaths_2.
           eapply precartesian_factorisation_unique.
           ++ apply liftclosed.
           ++ apply assoc_eq_var.
              eapply pathscomp0.
              ** apply maponpaths_2.
                 apply precartesian_factorisation_commutes.
              ** eapply pathscomp0.
                 --- eapply pathscomp0.
                     +++ apply mor_disp_transportf_postwhisker.
                     +++ eapply pathscomp0.
                         *** apply maponpaths.
                             exact (comm0 @ ! comm1).
                         *** apply pathsinv0.
                             apply mor_disp_transportf_postwhisker.
                 --- apply pathsinv0.
                     apply maponpaths_2.
                     apply precartesian_factorisation_commutes.
  - use tpair.
    + apply (transportf _ (id_left _)).
      eapply comp_disp.
      2: { apply lift. }
      eapply precartesian_factorisation.
      * apply liftclosed.
      * exact hh.
    + simpl.
      eapply pathscomp0.
      * eapply pathscomp0.
        -- apply mor_disp_transportf_postwhisker.
        -- eapply pathscomp0.
          ++ apply maponpaths.
             apply assoc_disp_var.
          ++ eapply pathscomp0.
             ** apply transport_f_f.
             ** apply maponpaths_2.
                apply homset_property.
      * apply transportf_transpose_left.
        apply precartesian_factorisation_commutes.
Defined.
