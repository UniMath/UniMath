(** Definitions of various kinds of Lemmas about _fibrations_, leading up to a theorem characterizing their composites. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

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

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.CategoryTheory.DisplayedCats.MoreFibrations.Prefibrations.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

(* First some technical lemmas about factorisation through a composite, where the latter morphism is cartesian. *)
Definition postcomp_pres_comm
    {C : category} {D : disp_cat C}
    {c c' c'' c''' : C} {f : c' --> c} {f' : c'' --> c'} {g' : c''' --> c''}
    {d : D c} {d' : D c'} {d'' : D c''} {d''' : D c'''}
    (ff : d' -->[f] d) (ff' : d'' -->[f'] d') (gg' : d''' -->[g'] d'')
    (gg : d''' -->[g' · f'] d') (hh : d''' -->[g' · (f' · f)] d)
    (comm_right : gg ;; ff = transportf (mor_disp d''' d) (assoc g' f' f) hh)
  : (gg' ;; ff' = gg) -> (gg' ;; (ff' ;; ff) = hh).
Proof.
  intro comm_left.
  eapply pathscomp0.
  - apply assoc_disp.
  - eapply pathscomp0.
    2: { apply transportbfinv. }
    + apply maponpaths.
      eapply pathscomp0.
      2: { exact comm_right. }
      * apply maponpaths_2.
        exact comm_left.
Qed.

Definition postcomp_refl_comm
    {C : category} {D : disp_cat C}
    {c c' c'' c''' : C} {f : c' --> c} {f' : c'' --> c'} {g' : c''' --> c''}
    {d : D c} {d' : D c'} {d'' : D c''} {d''' : D c'''}
    (ff : d' -->[f] d) (ff' : d'' -->[f'] d') (gg' : d''' -->[g'] d'')
    (gg : d''' -->[g' · f'] d') (hh : d''' -->[g' · (f' · f)] d)
    (H : is_cartesian ff)
    (comm_right : gg ;; ff = transportf (mor_disp d''' d) (assoc g' f' f) hh)
  : (gg' ;; (ff' ;; ff) = hh) -> (gg' ;; ff' = gg).
Proof.
  intro comm_all.
  apply (cartesian_factorisation_unique H).
  eapply pathscomp0.
  - apply assoc_disp_var.
  - eapply pathscomp0.
    2: { apply pathsinv0.
         exact comm_right. }
    + apply maponpaths.
      exact comm_all.
Qed.


(* In the following we show that postcomposition with cartesian morphisms preserves and reflects (pre)cartesianness. *)
Definition postcomp_w_cart_pres_cart
    {C : category} {D : disp_cat C}
    {c c' c'' : C} {f : c' --> c} {f' : c'' --> c'}
    {d : D c} {d' : D c'} {d'' : D c''} (ff : d' -->[f] d) (ff' : d'' -->[f'] d')
  : is_cartesian ff -> (is_cartesian ff' -> is_cartesian (ff' ;; ff)).
Proof.
  intros cartff cartff'.
  unfold is_cartesian.
  intros c''' g' d''' hh.
  apply iscontraprop1.
  - apply invproofirrelevance.
    unfold isProofIrrelevant.
    intros (gg0, commbig0) (gg1, commgg1).
    apply subtypePairEquality.
    + intro gg.
      apply homsets_disp.
    + apply (cartesian_factorisation_unique cartff').
      apply (cartesian_factorisation_unique cartff).
      eapply pathscomp0.
      * apply assoc_disp_var.
      * eapply pathscomp0.
        -- apply maponpaths.
           apply (pathscomp0 commbig0).
           apply pathsinv0.
           exact commgg1.
        -- apply pathsinv0.
           apply assoc_disp_var.
  - use tpair.
    + apply (cartesian_factorisation cartff').
      apply (cartesian_factorisation cartff).
      apply (transportb _ (! assoc _ _ _)).
      exact hh.
    + eapply pathscomp0.
      * apply assoc_disp.
      * eapply pathscomp0.
        --apply maponpaths.
          eapply pathscomp0.
          ++ eapply maponpaths_2.
             apply cartesian_factorisation_commutes.
          ++ apply cartesian_factorisation_commutes'.
        -- apply transportfbinv.
Defined.


Definition postcomp_w_cart_pres_pre'cart
    {C : category} {D : disp_cat C}
    {c c' c'' : C} {f : c' --> c} {f' : c'' --> c'}
    {d : D c} {d' : D c'} {d'' : D c''} (ff : d' -->[f] d) (ff' : d'' -->[f'] d')
  : is_cartesian ff -> (is_pre'cartesian ff' -> is_pre'cartesian (ff' ;; ff)).
Proof.
  intros cartff pre'cartff'.
  unfold is_pre'cartesian.
  intros d''' hh.
  apply iscontraprop1.
  - apply invproofirrelevance.
    unfold isProofIrrelevant.
    intros [gg0 commbig0] [gg1 commbig1].
    eapply subtypePairEquality.
    + intro gg.
      apply homsets_disp.
    + apply (pre'cartesian_factorisation_unique pre'cartff').
      apply (cartesian_factorisation_unique cartff).
      eapply pathscomp0.
      2: { apply pathsinv0.
        apply assoc_disp_var. }
      * eapply pathscomp0.
        -- apply assoc_disp_var.
        -- apply maponpaths.
           apply (pathscomp0 commbig0).
           apply pathsinv0.
           exact commbig1.
  - use tpair.
    + apply (pre'cartesian_factorisation pre'cartff').
      apply (cartesian_factorisation cartff).
      apply (transportb _ (! assoc _ _ _)).
      exact hh.
    + eapply pathscomp0.
      2: { apply (transportfbinv _ (! assoc _ _ _)). }
      * eapply pathscomp0.
        -- apply assoc_disp.
        -- apply maponpaths.
           eapply pathscomp0.
           ++ eapply maponpaths_2.
              apply pre'cartesian_factorisation_commutes.
           ++ apply cartesian_factorisation_commutes'.
Defined.


Definition postcomp_w_cart_refl_cart
    {C : category} {D : disp_cat C}
    {c c' c'' : C} {f : c' --> c} {f' : c'' --> c'}
    {d : D c} {d' : D c'} {d'' : D c''} (ff : d' -->[f] d) (ff' : d'' -->[f'] d')
  : is_cartesian ff -> (is_cartesian (ff' ;; ff) -> is_cartesian ff').
Proof.
  intros cartff cartff'ff.
  unfold is_cartesian.
  intros c''' g' d''' gg.
  apply iscontraprop1.
  - apply invproofirrelevance.
    unfold isProofIrrelevant.
    intros (gg0, commbig0) (gg1, commbig1).
    apply subtypePairEquality.
    + intro ggtemp.
      apply homsets_disp.
    + apply (cartesian_factorisation_unique cartff'ff).
      eapply pathscomp0.
      2: { apply pathsinv0.
        apply assoc_disp. }
      * eapply pathscomp0.
        -- apply assoc_disp.
        -- apply maponpaths.
           eapply maponpaths_2.
           exact (commbig0 @ ! commbig1).
  - use tpair.
    + apply (cartesian_factorisation cartff'ff).
      apply (transportb _ (assoc _ _ _)).
      exact (gg ;; ff).
    + apply (cartesian_factorisation_unique cartff).
      eapply pathscomp0.
      2: { apply transportfbinv. }
      * eapply pathscomp0.
        -- apply assoc_disp_var.
        -- apply maponpaths.
           apply cartesian_factorisation_commutes.
Defined.


Definition postcomp_w_cart_refl_pre'cart
    {C : category} {D : disp_cat C}
    {c c' c'' : C} {f : c' --> c} {f' : c'' --> c'}
    {d : D c} {d' : D c'} {d'' : D c''} (ff : d' -->[f] d) (ff' : d'' -->[f'] d')
  : is_cartesian ff -> (is_pre'cartesian (ff' ;; ff) -> is_pre'cartesian ff').
Proof.
  intros cartff pre'cartff'ff.
  unfold is_pre'cartesian.
  intros d''' gg.
  apply iscontraprop1.
  - apply invproofirrelevance.
    unfold isProofIrrelevant.
    intros (gg0, commbig0) (gg1, commbig1).
    apply subtypePairEquality.
    + intro ggtemp.
      apply homsets_disp.
    + apply (pre'cartesian_factorisation_unique pre'cartff'ff).
      eapply pathscomp0.
      2: { apply pathsinv0.
        apply assoc_disp. }
      * eapply pathscomp0.
        -- apply assoc_disp.
        -- apply maponpaths.
           eapply maponpaths_2.
           exact (commbig0 @ ! commbig1).
  - use tpair.
    + apply (pre'cartesian_factorisation pre'cartff'ff).
      apply (transportb _ (assoc _ _ _)).
      exact (gg ;; ff).
    + apply (cartesian_factorisation_unique cartff).
      eapply pathscomp0.
      2: { apply transportfbinv. }
      * eapply pathscomp0.
        -- apply assoc_disp_var.
        -- apply maponpaths.
           apply pre'cartesian_factorisation_commutes.
Defined.


Definition postcomp_w_cart_pres_precart
    {C : category} {D : disp_cat C}
    {c c' c'' : C} {f : c' --> c} {f' : c'' --> c'}
    {d : D c} {d' : D c'} {d'' : D c''} (ff : d' -->[f] d) (ff' : d'' -->[f'] d')
  : is_cartesian ff -> (is_precartesian ff' -> is_precartesian (ff' ;; ff)).
Proof.
  intros cartff precartff'.
  apply pre'_implies_pre.
  eapply postcomp_w_cart_pres_pre'cart.
  - exact cartff.
  - apply pre_implies_pre'.
    exact precartff'.
Defined.

Definition postcomp_w_cart_refl_precart
    {C : category} {D : disp_cat C}
    {c c' c'' : C} {f : c' --> c} {f' : c'' --> c'}
    {d : D c} {d' : D c'} {d'' : D c''} (ff : d' -->[f] d) (ff' : d'' -->[f'] d')
  : is_cartesian ff -> (is_precartesian (ff' ;; ff) -> is_precartesian ff').
Proof.
  intros cartff precartff'ff.
  apply pre'_implies_pre.
  eapply postcomp_w_cart_refl_pre'cart.
  - exact cartff.
  - apply pre_implies_pre'.
    exact precartff'ff.
Defined.
