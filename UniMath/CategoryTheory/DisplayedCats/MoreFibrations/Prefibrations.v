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

Local Open Scope type_scope.
Local Open Scope mor_disp_scope.


(** * Prefibrations *)
Section Precartesian_morphisms.
(** The following two equivalent definitions are convenient in different situations. *)
Definition is_precartesian {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : UU
:= forall (d'' : D c') (hh : d'' -->[f] d),
    ∃! (gg : d'' -->[identity c'] d'), gg ;; ff = transportb _ (id_left _) hh.

Definition is_pre'cartesian {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : UU
:= forall (d'' : D c') (hh : d'' -->[identity c' · f] d),
    ∃! (gg : d'' -->[identity c'] d'), gg ;; ff = hh.

(** Show that the're equivalent. TODO: Separate existence (data) and uniqueness (property). *)
Definition pre'_implies_pre
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : is_pre'cartesian ff -> is_precartesian ff.
Proof.
  unfold is_pre'cartesian, is_precartesian.
  intros H d'' hh.
  exact (H _ (transportb _ (id_left _) hh)).
Defined.

Definition pre_implies_pre'
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : is_precartesian ff -> is_pre'cartesian ff.
Proof.
  unfold is_precartesian, is_pre'cartesian.
  intros H d'' hh.
  set (temp := H _ (transportf _ (id_left _) hh)).
  set (temp' := transport_cancel_b_f _ (id_left _) hh).
  rewrite temp' in temp.
  exact temp.
Defined.

(** See also [precartesian_factorisation'] below, for when the map one wishes to factor is not judgementally over [f], but over some equal map. TODO! *)

Definition precartesian_factorisation {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_precartesian ff)
    {d'': D c'} (hh : d'' -->[f] d)
  : d'' -->[identity c'] d'
:= pr1 (pr1 (H _ hh)).

Definition pre'cartesian_factorisation {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_pre'cartesian ff)
    {d'': D c'} (hh : d'' -->[identity c' · f] d)
  : d'' -->[identity c'] d'
:= pr1 (pr1 (H _ hh)).

Definition precartesian_factorisation_commutes
    {C : category} {D : disp_cat C} {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_precartesian ff)
    {d'': D c'} (hh : d'' -->[f] d)
  : precartesian_factorisation H hh ;; ff = transportb _ (id_left _) hh
:= pr2 (pr1 (H _ hh)).

Definition pre'cartesian_factorisation_commutes
    {C : category} {D : disp_cat C} {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_pre'cartesian ff)
    {d'': D c'} (hh : d'' -->[identity c' · f] d)
  : pre'cartesian_factorisation H hh ;; ff = hh
:= pr2 (pr1 (H _ hh)).

Definition pre'cartesian_factorisation_of_composite
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_pre'cartesian ff)
    {d'' : D c'} (gg : d'' -->[identity c'] d')
  : gg = pre'cartesian_factorisation H (gg ;; ff).
Proof.
  set (temp1 := pr2 (H _ (gg ;; ff))).
  set (temp2 := temp1 (gg,, idpath (gg ;; ff))). (* Why is it impossible to define the argument separately? *)
  (* set (temp' := (gg,, idpath (gg ;; ff))). *)
  set (yay := (maponpaths pr1 temp2)).
  exact yay.
Defined.

Definition precartesian_factorisation_of_composite
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_precartesian ff)
    {d'' : D c'} (gg : d'' -->[identity c'] d')
  : gg = precartesian_factorisation H (transportf _ (id_left _) (gg ;; ff)).
Proof.
  set (contr := pr2 (H _ (transportf _ (id_left _) (gg ;; ff)))).
  set (transp := (transport_cancel_b_f _ (id_left f) (gg ;; ff))).
  set (temp := contr (gg,, ! transp)).
  set (goal := (maponpaths pr1 temp)).
  exact goal.
Defined.

Definition pre'cartesian_factorisation_unique
    {C : category} {D : disp_cat C} {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_pre'cartesian ff)
    {d'': D c'} (gg gg' : d'' -->[identity c'] d')
  : (gg ;; ff = gg' ;; ff) -> gg = gg'.
Proof.
  set (temp := pre'cartesian_factorisation_of_composite H gg).
  set (temp' := pre'cartesian_factorisation_of_composite H gg').
  intros Hggff.
  set (temp'' := maponpaths (pre'cartesian_factorisation H) Hggff).
  set (yay := (temp @ temp'' @ ! temp')).
  exact yay.
Defined.

Definition precartesian_factorisation_unique
    {C : category} {D : disp_cat C} {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_precartesian ff)
    {d'': D c'} (gg gg' : d'' -->[identity c'] d')
  : (gg ;; ff = gg' ;; ff) -> gg = gg'.
Proof.
  set (H' := pre_implies_pre' ff H).
  exact (pre'cartesian_factorisation_unique H' gg gg').
Defined.

Definition isaprop_is_precartesian
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : isaprop (is_precartesian ff).
Proof.
  repeat (apply impred_isaprop; intro).
  apply isapropiscontr.
Defined.

Definition isaprop_is_pre'cartesian
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : isaprop (is_pre'cartesian ff).
Proof.
  repeat (apply impred_isaprop; intro).
  apply isapropiscontr.
Defined.

End Precartesian_morphisms.


Section Precartesian_lifts.
Definition precartesian_lift
    {C : category} {D : disp_cat C}
    {c c' : C} (d : D c) (f : c' --> c)
  : UU
:= ∑ (d' : D c') (ff : d' -->[f] d), is_precartesian ff.

Definition pre'cartesian_lift
    {C : category} {D : disp_cat C}
    {c c' : C} (d : D c) (f : c' --> c)
  : UU
:= ∑ (d' : D c') (ff : d' -->[f] d), is_pre'cartesian ff.

Definition object_of_precartesian_lift
    {C : category} {D : disp_cat C}
    {c c' : C} {d : D c} {f : c' --> c}
    (fd : precartesian_lift d f)
  : D c'
:= pr1 fd.
Coercion object_of_precartesian_lift : precartesian_lift >-> ob_disp.

Definition object_of_pre'cartesian_lift
    {C : category} {D : disp_cat C}
    {c c' : C} {d : D c} {f : c' --> c}
    (fd : pre'cartesian_lift d f)
  : D c'
:= pr1 fd.
Coercion object_of_pre'cartesian_lift : pre'cartesian_lift >-> ob_disp.

Definition mor_disp_of_precartesian_lift
    {C : category} {D : disp_cat C}
    {c c' : C} {d : D c} {f : c' --> c}
    (fd : precartesian_lift d f)
  : (fd : D c') -->[f] d
  := pr1 (pr2 fd).
Coercion mor_disp_of_precartesian_lift : precartesian_lift >-> mor_disp.

Definition mor_disp_of_pre'cartesian_lift
    {C : category} {D : disp_cat C}
    {c c' : C} {d : D c} {f : c' --> c}
    (fd : pre'cartesian_lift d f)
  : (fd : D c') -->[f] d
  := pr1 (pr2 fd).
Coercion mor_disp_of_pre'cartesian_lift : pre'cartesian_lift >-> mor_disp.

Definition precartesian_lift_is_precartesian
    {C : category} {D : disp_cat C}
    {c c' : C} {d : D c} {f : c' --> c}
    (fd : precartesian_lift d f)
  : is_precartesian fd
:= pr2 (pr2 fd).
Coercion precartesian_lift_is_precartesian : precartesian_lift >-> is_precartesian.

Definition pre'cartesian_lift_is_pre'cartesian
    {C : category} {D : disp_cat C}
    {c c' : C} {d : D c} {f : c' --> c}
    (fd : pre'cartesian_lift d f)
  : is_pre'cartesian fd
:= pr2 (pr2 fd).
Coercion pre'cartesian_lift_is_pre'cartesian : pre'cartesian_lift >-> is_pre'cartesian.

End Precartesian_lifts.


Section Precleavages.

Definition precleaving
    {C : category} (D : disp_cat C) : UU
  := forall (c c' : C) (f :  c' --> c) (d : D c), precartesian_lift d f.

Definition pre'cleaving
    {C : category} (D : disp_cat C) : UU
  := forall (c c' : C) (f :  c' --> c) (d : D c), pre'cartesian_lift d f.

Definition pre_implies_pre'_cleaving
    {C : category} (D : disp_cat C)
  : precleaving D -> pre'cleaving D.
Proof.
  unfold precleaving, pre'cleaving.
  intros X c c' f d.
  set (X' := X c c' f d).
  exists (object_of_precartesian_lift X').
  exists X'.
  exact (pre_implies_pre' X' (precartesian_lift_is_precartesian X')).
Defined.

Definition pre'_implies_pre_cleaving
    {C : category} (D : disp_cat C)
  : pre'cleaving D -> precleaving D.
Proof.
  unfold precleaving, pre'cleaving.
  intros X c c' f d.
  set (X' := X c c' f d).
  exists (object_of_pre'cartesian_lift X').
  exists X'.
  exact (pre'_implies_pre X' (pre'cartesian_lift_is_pre'cartesian X')).
Defined.

(* TODO: Show that the above functions yield an equivalence *)

End Precleavages.


Section Prefibrations.
Definition prefibration
    (C : category) : UU
:= ∑ (D : disp_cat C), precleaving D.

Definition pre'fibration
    (C : category) : UU
:= ∑ (D : disp_cat C), pre'cleaving D.

Definition pre_implies_pre'_fibration
    (C : category)
  : prefibration C -> pre'fibration C.
Proof.
  unfold prefibration, pre'fibration.
  intros (D, H).
  exists D.
  exact (pre_implies_pre'_cleaving D H).
Defined.

Definition pre'_implies_pre_fibration
    (C : category)
  : pre'fibration C -> prefibration C.
Proof.
  unfold prefibration, pre'fibration.
  intros (D, H').
  exists D.
  exact (pre'_implies_pre_cleaving D H').
Defined.

End Prefibrations.
