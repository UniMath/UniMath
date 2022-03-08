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

Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Require Import UniMath.Foundations.All.

Require Import UniMath.CategoryTheory.DisplayedCats.MoreFibrations.GeneralPreliminaries.
Require Import UniMath.CategoryTheory.DisplayedCats.MoreFibrations.FibrationsPreliminaries.
Require Import UniMath.CategoryTheory.DisplayedCats.MoreFibrations.Prefibrations.

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.

Search (isaprop _ -> _ -> iscontr _).

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
    2: { apply transport_cancel_b_f. }
    + apply maponpaths.
      eapply pathscomp0.
      2: { exact comm_right. }
      * apply (maponpaths (fun gg: d''' -->[ g' · f'] d' => (gg ;; ff))).
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
      eapply pathscomp_ternary.
      3:{ apply pathsinv0. apply assoc_disp_var. }
      * apply assoc_disp_var.
      * apply maponpaths.
        apply (pathscomp0 commbig0).
        apply pathsinv0.
        exact commgg1.
  - use tpair.
    + apply (cartesian_factorisation cartff').
      apply (cartesian_factorisation cartff).
      apply (transportb _ (! assoc _ _ _)).
      exact hh.
    + eapply pathscomp_ternary.
      3:{ apply transport_cancel_f_b. }
      * apply assoc_disp.
      * apply maponpaths.
        eapply pathscomp0.
        -- eapply (maponpaths (fun gg: d''' -->[ g' · f'] d' => (gg ;; ff))).
           apply cartesian_factorisation_commutes.
        -- apply cartesian_factorisation_commutes'.
Defined.

(* Why does this not work? I can't choose a subgoal!
Definition postcomp_w_cart_pres_cart_new
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
    eapply subtypePairEquality.
    + intro gg.
      apply homsets_disp.
    + apply (cartesian_factorisation_unique cartff').
      apply (cartesian_factorisation_unique cartff).
      eapply pathscomp_ternary.
      * apply assoc_disp_var.
      2: { apply pathsinv0.
           apply assoc_disp_var. }
      * apply maponpaths.
        apply (pathscomp0 commbig0).
        apply pathsinv0.
        exact commgg1.
  - use tpair.
    + apply (cartesian_factorisation cartff').
      apply (cartesian_factorisation cartff).
      apply (transportb _ (! assoc _ _ _)).
      exact hh.
    + eapply pathscomp_ternary.
      * apply assoc_disp.
      3: { apply transport_cancel_f_b. }
      * apply maponpaths.
        eapply pathscomp0.
        -- eapply (maponpaths (fun gg: d''' -->[ g' · f'] d' => (gg ;; ff))).
           apply cartesian_factorisation_commutes.
        -- apply cartesian_factorisation_commutes'. }
Defined.
*)

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
  2: { use tpair.
    + apply (cartesian_factorisation cartff'ff).
      apply (transportb _ (assoc _ _ _)).
      exact (gg ;; ff).
    + apply (cartesian_factorisation_unique cartff).
      eapply pathscomp_ternary.
      3: { apply transport_cancel_f_b. }
      * apply assoc_disp_var.
      * apply maponpaths.
        apply cartesian_factorisation_commutes. }
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
           eapply (maponpaths ((fun gg: d''' -->[ g' · f'] d' => (gg ;; ff)))).
           apply (pathscomp0 commbig0).
           apply pathsinv0.
           exact commbig1.
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
    intros (gg0, commbig0) (gg1, commbig1).
    eapply subtypePairEquality.
    + intro gg.
      apply homsets_disp.
    + apply (pre'cartesian_factorisation_unique pre'cartff').
      apply (cartesian_factorisation_unique cartff).
      eapply pathscomp_ternary.
      3: { apply pathsinv0. apply assoc_disp_var. }
      * apply assoc_disp_var.
      * apply maponpaths.
        apply (pathscomp0 commbig0).
        apply pathsinv0.
        exact commbig1.
  - use tpair.
    + apply (pre'cartesian_factorisation pre'cartff').
      apply (cartesian_factorisation cartff).
      apply (transportb _ (! assoc _ _ _)).
      exact hh.
    + eapply pathscomp_ternary.
        3: { apply (transport_cancel_f_b _ (! assoc _ _ _) _). }
        * apply assoc_disp.
        * apply maponpaths.
           eapply pathscomp0.
           -- eapply (maponpaths (fun gg: d''' -->[(identity c'') · f'] d' => (gg ;; ff))).
              apply pre'cartesian_factorisation_commutes.
           -- apply cartesian_factorisation_commutes'.
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
  set (hh_assoc := gg ;; ff).
  set (hh := transportb _ (assoc (identity c'') f' f) hh_assoc).
  set (gg' := pre'cartesian_factorisation pre'cartff'ff hh).
  set (comm_all := pre'cartesian_factorisation_commutes pre'cartff'ff hh).
  set (temp := assoc_disp_var gg' ff' ff).
  set (temp' := transport_cancel_b_f _ (assoc (identity c'') f' f) hh).
  set (temp'' := transport_cancel_f_b _ (assoc (identity c'') f' f) hh_assoc).
  set (comm_all' := maponpaths (transportf (mor_disp d''' d) (assoc (identity c'') f' f)) comm_all).
  set (comm_left' := assoc_disp_var gg' ff' ff @ comm_all' @ temp'').
  set (comm_left := cartesian_factorisation_unique cartff (gg' ;; ff') gg comm_left').
  exists (gg',, comm_left).
  intros (gg'', commgg''_left).
  apply subtypePairEquality.
  intro gg0.
  set (settemp := homsets_disp ((identity c'') · f') d''' d').
  set (proptemp := settemp (gg0 ;; ff') gg).
  exact proptemp.
  set (commgg''_all_pre := maponpaths (fun gg: d''' -->[(identity c'') · f'] d' => (gg ;; ff)) commgg''_left).
  set (commgg''_all := (assoc_disp gg'' ff' ff) @ maponpaths (transportb _ (assoc (identity c'') f' f)) commgg''_all_pre).
  set (commgg''gg' := commgg''_all @ ! comm_all).
  set (eq := pre'cartesian_factorisation_unique pre'cartff'ff gg'' gg' commgg''gg').
  exact eq.
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
