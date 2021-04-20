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
  set (comm_left' := maponpaths (fun gg: d''' -->[ g' · f'] d' => (gg ;; ff)) comm_left).
  set (comm_all_pre := comm_left' @ comm_right).
  set (comm_all_pre' := maponpaths (transportb _ (assoc g' f' f)) comm_all_pre).
  set (comm_all := assoc_disp gg' ff' ff @ comm_all_pre' @ transport_cancel_b_f _ (assoc g' f' f) hh).
  exact comm_all.
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
  set (temp := assoc_disp_var gg' ff' ff).
  set (temp' := transport_cancel_b_f _ (assoc g' f' f) hh).
  intro comm_all.
  set (comm_all' := maponpaths (transportf (mor_disp d''' d) (assoc g' f' f)) comm_all).
  set (comm_left' := assoc_disp_var gg' ff' ff @ comm_all' @ ! comm_right).
  set (comm_left := cartesian_factorisation_unique H (gg' ;; ff') gg comm_left').
  exact comm_left.
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
  set (gg := cartesian_factorisation' cartff (g' · f') hh (! assoc g' f' f)).
  set (comm_right := cartesian_factorisation_commutes'  cartff (g' · f') hh (! assoc g' f' f)).
  set (gg' := cartesian_factorisation cartff' g' gg).
  set (comm_left := cartesian_factorisation_commutes cartff' g' gg).
  (*set (comm_all := postcomp_pres_eq ff ff' gg' gg hh comm_right).*)
  set (comm_left' := maponpaths (fun gg: d''' -->[ g' · f'] d' => (gg ;; ff)) comm_left).
  set (comm_all_pre := comm_left' @ comm_right).
  set (comm_all_pre' := maponpaths (transportb _ (assoc g' f' f)) comm_all_pre).
  set (comm_all := (assoc_disp gg' ff' ff) @ comm_all_pre' @ transport_cancel_f_b _ (! assoc g' f' f) hh).
  exists (gg',, comm_all).
  intros (gg'', commgg''big).
  apply subtypePairEquality.
  intro gg0.
  set (settemp := homsets_disp (g' · (f' · f)) d''' d).
  set (proptemp := settemp (gg0 ;; (ff' ;; ff)) hh).
  exact proptemp.
  set (H := commgg''big @ ! comm_all).
  set (H_assoc_temp := maponpaths (transportf _ (assoc g' f' f)) H).
  set (temp_assoc_var := assoc_disp_var gg' ff' ff).
  set (temp_assoc_var' := assoc_disp_var gg'' ff' ff).
  set (H_assoc := temp_assoc_var' @ H_assoc_temp @ ! temp_assoc_var).
  set (H_small := cartesian_factorisation_unique cartff (gg'' ;; ff') (gg' ;; ff') H_assoc).
  set (yay := cartesian_factorisation_unique cartff' gg'' gg' H_small).
  exact yay.
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
  set (hh_assoc := gg ;; ff).
  set (hh := transportb _ (assoc g' f' f) hh_assoc).
  set (gg' := cartesian_factorisation cartff'ff g' hh).
  set (comm_all := cartesian_factorisation_commutes cartff'ff g' hh).
  set (temp := assoc_disp_var gg' ff' ff).
  set (temp' := transport_cancel_b_f _ (assoc g' f' f) hh).
  set (temp'' := transport_cancel_f_b _ (assoc g' f' f) hh_assoc).
  set (comm_all' := maponpaths (transportf (mor_disp d''' d) (assoc g' f' f)) comm_all).
  set (comm_left' := assoc_disp_var gg' ff' ff @ comm_all' @ temp'').
  set (comm_left := cartesian_factorisation_unique cartff (gg' ;; ff') gg comm_left').
  exists (gg',, comm_left).
  intros (gg'', commgg''_left).
  apply subtypePairEquality.
  intro gg0.
  set (settemp := homsets_disp (g' · f') d''' d').
  set (proptemp := settemp (gg0 ;; ff') gg).
  exact proptemp.
  set (commgg''_all_pre := maponpaths (fun gg: d''' -->[ g' · f'] d' => (gg ;; ff)) commgg''_left).
  set (commgg''_all := (assoc_disp gg'' ff' ff) @ maponpaths (transportb _ (assoc g' f' f)) commgg''_all_pre).
  set (commgg''gg' := commgg''_all @ ! comm_all).
  set (eq := cartesian_factorisation_unique cartff'ff gg'' gg' commgg''gg').
  exact eq.
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
  set (gg := cartesian_factorisation' cartff ((identity c'') · f') hh (! assoc (identity c'') f' f)).
  set (comm_right := cartesian_factorisation_commutes'  cartff ((identity c'') · f') hh (! assoc (identity c'') f' f)).
  set (gg' := pre'cartesian_factorisation pre'cartff' gg).
  set (comm_left := pre'cartesian_factorisation_commutes pre'cartff' gg).
  set (comm_left' := maponpaths (fun gg: d''' -->[(identity c'') · f'] d' => (gg ;; ff)) comm_left).
  set (comm_all_pre := comm_left' @ comm_right).
  set (comm_all_pre' := maponpaths (transportb _ (assoc (identity c'') f' f)) comm_all_pre).
  set (comm_all := (assoc_disp gg' ff' ff) @ comm_all_pre' @ transport_cancel_f_b _ (! assoc (identity c'') f' f) hh).
  exists (gg',, comm_all).
  intros (gg'', commgg''big).
  apply subtypePairEquality.
  intro gg0.
  set (settemp := homsets_disp ((identity c'') · (f' · f)) d''' d).
  set (proptemp := settemp (gg0 ;; (ff' ;; ff)) hh).
  exact proptemp.
  set (H := commgg''big @ ! comm_all).
  set (H_assoc_temp := maponpaths (transportf _ (assoc (identity c'') f' f)) H).
  set (temp_assoc_var := assoc_disp_var gg' ff' ff).
  set (temp_assoc_var' := assoc_disp_var gg'' ff' ff).
  set (H_assoc := temp_assoc_var' @ H_assoc_temp @ ! temp_assoc_var).
  set (H_small := cartesian_factorisation_unique cartff (gg'' ;; ff') (gg' ;; ff') H_assoc).
  set (yay := pre'cartesian_factorisation_unique pre'cartff' gg'' gg' H_small).
  exact yay.
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
  set (pre'cartff' := pre_implies_pre' ff' precartff').
  set (pre'cartff'ff := postcomp_w_cart_pres_pre'cart ff ff' cartff pre'cartff').
  set (precartff'ff := pre'_implies_pre (ff' ;; ff) pre'cartff'ff).
  exact (precartff'ff).
Defined.

Definition postcomp_w_cart_refl_precart
    {C : category} {D : disp_cat C}
    {c c' c'' : C} {f : c' --> c} {f' : c'' --> c'}
    {d : D c} {d' : D c'} {d'' : D c''} (ff : d' -->[f] d) (ff' : d'' -->[f'] d')
  : is_cartesian ff -> (is_precartesian (ff' ;; ff) -> is_precartesian ff').
Proof.
  intros cartff precartff'ff.
  set (pre'cartff'ff := pre_implies_pre' (ff' ;; ff) precartff'ff).
  set (pre'cartff' := postcomp_w_cart_refl_pre'cart ff ff' cartff pre'cartff'ff).
  set (precartff' := pre'_implies_pre ff' pre'cartff').
  exact (precartff').
Defined.
