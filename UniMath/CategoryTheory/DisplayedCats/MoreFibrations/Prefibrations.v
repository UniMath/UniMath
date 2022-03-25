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

Definition pre'_implies_pre
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : is_pre'cartesian ff -> is_precartesian ff.
Proof.
  intros H d'' hh.
  apply H.
Defined.
Coercion pre'_implies_pre : is_pre'cartesian >-> is_precartesian.

Definition pre_implies_pre'
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : is_precartesian ff -> is_pre'cartesian ff.
Proof.
  intros H d'' hh.
  induction (transportbfinv _ (id_left _) hh).
  apply H.
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

Definition precartesian_factorisation_of_composite
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_precartesian ff)
    {d'' : D c'} (gg : d'' -->[identity c'] d')
  : gg = precartesian_factorisation H (transportf _ (id_left _) (gg ;; ff)).
Proof.
  exact (maponpaths pr1 ((pr2 (H _ _)) (_,, ! ((transportbfinv _ _ _))))).
Defined.

Definition pre'cartesian_factorisation_of_composite
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_pre'cartesian ff)
    {d'' : D c'} (gg : d'' -->[identity c'] d')
  : gg = pre'cartesian_factorisation H (gg ;; ff).
Proof.
  exact (maponpaths pr1 ((pr2 (H _ _)) (_,, idpath _))).
Defined.

Definition pre'cartesian_factorisation_unique
    {C : category} {D : disp_cat C} {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_pre'cartesian ff)
    {d'': D c'} (gg gg' : d'' -->[identity c'] d')
  : (gg ;; ff = gg' ;; ff) -> gg = gg'.
Proof.
  intro Hggff.
  eapply pathscomp0.
  - apply (pre'cartesian_factorisation_of_composite H).
  - eapply pathscomp0.
    + apply maponpaths.
      exact Hggff.
    + apply pathsinv0.
      apply pre'cartesian_factorisation_of_composite.
Defined.

Definition precartesian_factorisation_unique
    {C : category} {D : disp_cat C} {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} {ff : d' -->[f] d} (H : is_precartesian ff)
    {d'': D c'} (gg gg' : d'' -->[identity c'] d')
  : (gg ;; ff = gg' ;; ff) -> gg = gg'.
Proof.
  intro Hggff.
  eapply pathscomp0.
  - apply (precartesian_factorisation_of_composite H).
  - eapply pathscomp0.
    + apply maponpaths.
      apply maponpaths.
      exact Hggff.
    + apply pathsinv0.
      apply precartesian_factorisation_of_composite.
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

(*
Definition pre_implies_pre'_new
    {C : category} {D : disp_cat C}
    {c c' : C} {f : c' --> c}
    {d : D c} {d' : D c'} (ff : d' -->[f] d)
  : is_precartesian ff -> is_pre'cartesian ff.
Proof.
  unfold is_precartesian.
  intros precartff d'' hh.
  apply iscontraprop1.
  - apply invproofirrelevance.
    unfold isProofIrrelevant.
    intros [gg0 comm0] [gg1 comm1].
    apply subtypePairEquality.
    + intro gg.
      apply homsets_disp.
    + apply (precartesian_factorisation_unique precartff).
      exact (comm0 @ ! comm1).
  - use tpair.
    + apply precartff.
      eapply (transportf (mor_disp d'' d) (id_left f)).
      exact hh.
    + simpl.
      eapply pathscomp0.
      * apply precartesian_factorisation_commutes.
      * apply transportbfinv.
Defined.
*)

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

Definition pre'_implies_precartesian_lift
    {C : category} {D : disp_cat C}
    {c c' : C} {d : D c} {f : c' --> c}
    (fd : pre'cartesian_lift d f)
  : precartesian_lift d f.
Proof.
  exists (pr1 fd). exists (pr1 (pr2 fd)).
  apply pre'_implies_pre.
  exact (pr2 (pr2 fd)).
Defined.
Coercion pre'_implies_precartesian_lift : pre'cartesian_lift >-> precartesian_lift.

Definition pre_implies_pre'cartesian_lift
    {C : category} {D : disp_cat C}
    {c c' : C} {d : D c} {f : c' --> c}
    (fd : precartesian_lift d f)
  : pre'cartesian_lift d f.
Proof.
  exists (pr1 fd). exists (pr1 (pr2 fd)).
  apply pre_implies_pre'.
  exact (pr2 (pr2 fd)).
Defined.

End Precartesian_lifts.


Section Precleavages.

Definition precleaving
    {C : category} (D : disp_cat C) : UU
  := forall (c c' : C) (f :  c' --> c) (d : D c), precartesian_lift d f.

Definition pre'cleaving
    {C : category} (D : disp_cat C) : UU
  := forall (c c' : C) (f :  c' --> c) (d : D c), pre'cartesian_lift d f.

Definition pre_implies_pre'cleaving
    {C : category} (D : disp_cat C)
  : precleaving D -> pre'cleaving D.
Proof.
  unfold pre'cleaving.
  intros H c c' f d.
  apply pre_implies_pre'cartesian_lift.
  apply H.
Defined.
Coercion pre_implies_pre'cleaving : precleaving >-> pre'cleaving.

Definition pre'_implies_precleaving
    {C : category} (D : disp_cat C)
  : pre'cleaving D -> precleaving D.
Proof.
  unfold precleaving.
  intros H c c' f d.
  apply pre'_implies_precartesian_lift.
  apply H.
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

Definition pre'_implies_prefibration
    (C : category)
  : pre'fibration C -> prefibration C.
Proof.
  intro F.
  exists (pr1 F).
  apply pre'_implies_precleaving.
  exact (pr2 F).
Defined.
Coercion pre'_implies_prefibration : pre'fibration >-> prefibration.

Definition pre_implies_pre'fibration
    (C : category)
  : prefibration C -> pre'fibration C.
Proof.
  intro F.
  exists (pr1 F).
  apply pre_implies_pre'cleaving.
  exact (pr2 F).
Defined.

End Prefibrations.
