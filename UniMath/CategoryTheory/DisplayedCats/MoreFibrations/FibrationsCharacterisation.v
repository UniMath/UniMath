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

Require Import UniMath.CategoryTheory.DisplayedCats.MoreFibrations.GeneralPreliminaries.
Require Import UniMath.CategoryTheory.DisplayedCats.MoreFibrations.FibrationsPreliminaries.
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

Search (transportf _ _ ?p = transportf _ _ ?p' -> ?p = ?p').

Lemma transportf_cancel
      {X : UU} (P : X → UU) {x x' : X} (e : x = x') (y0 y1 : P x):
      transportf P e y0 = transportf P e y1 -> y0 = y1.
Proof.
  induction e.
  apply idfun.
Defined.

Lemma transportb_cancel
      {X : UU} (P : X → UU) {x x' : X} (e : x = x') (y'0 y'1 : P x'):
      transportb P e y'0 = transportb P e y'1 -> y'0 = y'1.
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
  eapply pathscomp_ternary.
  - apply assoc_disp_var.
  - apply maponpaths.
    exact H.
  - apply pathsinv0.
    apply assoc_disp_var.
Qed.

Definition assoc_eq_var {C} {D : disp_precat C}
    {x y z w} {f} {g} {h} {xx : D x} {yy : D y} {zz : D z} {ww : D w}
    (ff ff' : xx -->[f] yy) (gg gg' : yy -->[g] zz) (hh hh' : zz -->[h] ww)
  : (ff ;; gg) ;; hh = (ff' ;; gg') ;; hh' -> ff ;; (gg ;; hh) = ff' ;; (gg' ;; hh').
Proof.
  intro H.
  eapply pathscomp_ternary.
  - apply assoc_disp.
  - apply maponpaths.
    exact H.
  - apply pathsinv0.
    apply assoc_disp.
Qed.

Definition eq_postwhisker {C} {D : disp_precat C}
    {x y z} {f} {g} {xx : D x} {yy : D y} {zz : D z}
    (ff ff' : xx -->[f] yy) (gg : yy -->[g] zz)
  : ff = ff' -> ff ;; gg = ff' ;; gg.
Proof.
  intro H.
  apply (maponpaths (λ ff, ff ;; gg)).
  assumption.
Qed.

Definition eq_prewhisker {C} {D : disp_precat C}
    {x y z} {f} {g} {xx : D x} {yy : D y} {zz : D z}
    (ff : xx -->[f] yy) (gg gg' : yy -->[g] zz)
  : gg = gg' -> ff ;; gg = ff ;; gg'.
Proof.
  intro H.
  apply (maponpaths (λ gg, ff ;; gg)).
  assumption.
Qed.

Definition prefibration_w_precart_closed_implies_fibration
    {C : category} {D : disp_cat C} (lift : precleaving D)
  : precleaving_comp_is_precart lift -> precleaving_is_cleaving lift.
Proof.
  unfold precleaving_comp_is_precart, precleaving_is_cleaving.
  intros liftclosed c c' f d.
  set (ff := lift _ _ f d).
  set (d' := object_of_precartesian_lift ff).
  unfold is_cartesian.
  intros c'' g d'' hh.
  set (gg'all := lift _ _ g d' : precartesian_lift d' g).
  set (d''' := object_of_precartesian_lift gg'all).
  set (gg' := mor_disp_of_precartesian_lift gg'all).
  set (Hgg' := precartesian_lift_is_precartesian gg'all).
  set (precartgg'ff := liftclosed _ _ _ g f d).
  set (temp := @unique_exists' (d'' -->[ g] d') (λ gg, gg ;; ff = hh)). simpl in temp.
  (*eapply temp.*)
  use temp.
  - set (gg'' := precartesian_factorisation precartgg'ff hh).
    set (gg_id := gg'' ;; gg').
    set (gg := transportf _ (id_left g) gg_id).
    exact gg.
  - simpl.
    set (commgg'' := precartesian_factorisation_commutes precartgg'ff hh).
    set (commgg''_var := transportf_transpose_left commgg'').
    etrans.
    2: { apply commgg''_var. }
    etrans.
    apply mor_disp_transportf_postwhisker.
    etrans.
    apply maponpaths.
    apply assoc_disp_var.
    etrans.
    apply transport_f_f.
    apply maponpaths_2.
    apply homset_property.
  - intro gg. simpl.
    apply homsets_disp.
  - simpl. intros gg0 gg1 H0 H1.
    set (H :=  H0 @ ! H1).
    apply (transportb_cancel _ (id_left _) gg0 gg1).
    etrans.
    apply (! precartesian_factorisation_commutes Hgg' gg0).
    etrans.
    2: { apply (precartesian_factorisation_commutes Hgg' gg1). }
    apply (maponpaths (λ gg'', gg'' ;; gg')).
    apply (precartesian_factorisation_unique precartgg'ff).
    apply assoc_eq_var.
    set (comm0 := precartesian_factorisation_commutes Hgg' gg0).
    set (comm1 := precartesian_factorisation_commutes Hgg' gg1).
    etrans.
    apply (eq_postwhisker _ _ ff comm0).
    etrans.
    2: { apply (! eq_postwhisker _ _ ff comm1). }
    etrans.
    apply mor_disp_transportf_postwhisker.
    etrans.
    2: { apply (! mor_disp_transportf_postwhisker _ _ ff). }
    apply maponpaths.
    assumption.
Defined.

Definition prefibration_w_precart_closed_implies_fibration_new
    {C : category} {D : disp_cat C} (lift : precleaving D)
  : precleaving_comp_is_precart lift -> precleaving_is_cleaving lift.
Proof.
  unfold precleaving_comp_is_precart, precleaving_is_cleaving.
  intros liftclosed c c' f d.
  set (ff := lift _ _ f d).
  set (d' := object_of_precartesian_lift ff).
  unfold is_cartesian.
  intros c'' g d'' hh.
  set (gg'all := lift _ _ g d' : precartesian_lift d' g).
  set (d''' := object_of_precartesian_lift gg'all).
  set (gg' := mor_disp_of_precartesian_lift gg'all).
  set (Hgg' := precartesian_lift_is_precartesian gg'all).
  set (precartgg'ff := liftclosed _ _ _ g f d).
  use unique_exists'.
  - apply (transportf _ (id_left _)).
    apply (λ gg'', gg'' ;; gg').
    eapply (precartesian_factorisation).
    + apply liftclosed.
    + exact hh.
  - simpl.
    eapply pathscomp0.
    + eapply pathscomp0.
      * apply mor_disp_transportf_postwhisker.
      * eapply pathscomp0.
        -- apply maponpaths.
           apply assoc_disp_var.
        -- eapply pathscomp0.
           ++ apply transport_f_f.
           ++ apply maponpaths_2.
              apply homset_property.
    + apply transportf_transpose_left.
       apply precartesian_factorisation_commutes.
  - intro gg. simpl.
    apply homsets_disp.
  - simpl. intros gg0 gg1 H0 H1.
    apply (transportb_cancel _ (id_left _) gg0 gg1).
    eapply pathscomp0.
    + apply pathsinv0.
        apply (precartesian_factorisation_commutes Hgg').
    + eapply pathscomp0.
      2: { apply (precartesian_factorisation_commutes Hgg'). }
      * apply (maponpaths (λ gg'', gg'' ;; gg'all)).
        apply (precartesian_factorisation_unique precartgg'ff).
        apply assoc_eq_var.
        eapply pathscomp0.
        -- apply eq_postwhisker.
           apply precartesian_factorisation_commutes.
        -- eapply pathscomp0.
           ++ eapply pathscomp0.
              ** apply mor_disp_transportf_postwhisker.
              ** eapply pathscomp0.
                 --- apply maponpaths.
                     exact (H0 @ ! H1).
                 --- apply pathsinv0.
                     apply mor_disp_transportf_postwhisker.
           ++ apply pathsinv0.
              apply eq_postwhisker.
              apply precartesian_factorisation_commutes.
Defined.


Definition prefibration_w_precart_closed_implies_fibration_new2
    {C : category} {D : disp_cat C} (lift : precleaving D)
  : precleaving_comp_is_precart lift -> precleaving_is_cleaving lift.
Proof.
  unfold precleaving_comp_is_precart, precleaving_is_cleaving.
  intros liftclosed c c' f d.
  set (ff := lift _ _ f d).
  set (d' := object_of_precartesian_lift ff).
  unfold is_cartesian.
  intros c'' g d'' hh.
  set (gg'all := lift _ _ g d' : precartesian_lift d' g).
  set (d''' := object_of_precartesian_lift gg'all).
  set (gg' := mor_disp_of_precartesian_lift gg'all).
  set (Hgg' := precartesian_lift_is_precartesian gg'all).
  set (precartgg'ff := liftclosed _ _ _ g f d).
  apply iscontraprop1.
  - apply invproofirrelevance.
    unfold isProofIrrelevant.
    intros [gg0 comm0] [gg1 comm1].
    apply subtypePairEquality.
    + intro gg.
      apply homsets_disp.
    + apply (transportb_cancel _ (id_left _) gg0 gg1).
      eapply pathscomp0.
      * apply pathsinv0.
        apply (precartesian_factorisation_commutes Hgg').
      * eapply pathscomp0.
        2: { apply (precartesian_factorisation_commutes Hgg'). }
        -- apply (maponpaths (λ gg'', gg'' ;; gg'all)).
           apply (precartesian_factorisation_unique precartgg'ff).
           apply assoc_eq_var.
           eapply pathscomp0.
           ++ apply eq_postwhisker.
              apply precartesian_factorisation_commutes.
           ++ eapply pathscomp0.
              ** eapply pathscomp0.
                 --- apply mor_disp_transportf_postwhisker.
                 --- eapply pathscomp0.
                     +++ apply maponpaths.
                         exact (comm0 @ ! comm1).
                     +++ apply pathsinv0.
                         apply mor_disp_transportf_postwhisker.
              ** apply pathsinv0.
                 apply eq_postwhisker.
                 apply precartesian_factorisation_commutes.
  - use tpair.
    + apply (transportf _ (id_left _)).
      apply (λ gg'', gg'' ;; gg').
      eapply (precartesian_factorisation).
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



Definition prefibration_w_precart_closed_implies_fibration_new3
    {C : category} {D : disp_cat C} (lift : precleaving D)
  : precleaving_comp_is_precart lift -> precleaving_is_cleaving lift.
Proof.
  unfold precleaving_comp_is_precart, precleaving_is_cleaving.
  intros liftclosed c c' f d.
  set (ff := lift _ _ f d).
  set (d' := object_of_precartesian_lift ff).
  unfold is_cartesian.
  intros c'' g d'' hh.
  set (gg'all := lift _ _ g d' : precartesian_lift d' g).
  set (d''' := object_of_precartesian_lift gg'all).
  set (gg' := mor_disp_of_precartesian_lift gg'all).
  apply iscontraprop1.
  - apply invproofirrelevance.
    unfold isProofIrrelevant.
    intros [gg0 comm0] [gg1 comm1].
    apply subtypePairEquality.
    + intro gg.
      apply homsets_disp.
    + apply (transportb_cancel _ (id_left _) gg0 gg1).
      eapply pathscomp0.
      * apply pathsinv0.
        (*eapply precartesian_factorisation_commutes. Unshelve.*)
        use precartesian_factorisation_commutes.
        3: { use precartesian_lift_is_precartesian. apply lift. }
      * eapply pathscomp0.
        2: { use precartesian_factorisation_commutes.
          3: { use precartesian_lift_is_precartesian. apply lift. } }
        -- apply (maponpaths (λ gg'', gg'' ;; gg'all)).
           eapply precartesian_factorisation_unique.
           ++ apply liftclosed.
           ++ apply assoc_eq_var.
              eapply pathscomp0.
              ** apply eq_postwhisker.
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
                     apply eq_postwhisker.
                     apply precartesian_factorisation_commutes.
  - use tpair.
    + apply (transportf _ (id_left _)).
      apply (λ gg'', gg'' ;; gg').
      eapply (precartesian_factorisation).
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
