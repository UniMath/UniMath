(** *************************************************

Contents:

- Definition of limits
- Proof that limits form a property in a (saturated/univalent) category ([isaprop_Lims])
- Pointwise construction of limits in functor precategories [LimsFunctorCategory]
- Alternative definition of limits via colimits

Written by: Benedikt Ahrens and Anders Mörtberg, 2015-2016

*****************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.Adjunctions.

Local Open Scope cat.

(** * Definition of limits *)
Section lim_def.

Context {C : precategory} (hsC : has_homsets C).

Definition cone {g : graph} (d : diagram g C) (c : C) : UU :=
  ∑ (f : ∏ (v : vertex g), C⟦c,dob d v⟧),
    ∏ (u v : vertex g) (e : edge u v), f u · dmor d e = f v.

Definition mk_cone {g : graph} {d : diagram g C} {c : C}
  (f : ∏ v, C⟦c, dob d v⟧) (Hf : ∏ u v (e : edge u v), f u · dmor d e = f v) :
  cone d c
  := tpair _ f Hf.

(** The injections to c in the cocone *)
Definition coneOut {g : graph} {d : diagram g C} {c : C} (cc : cone d c) :
  ∏ v, C⟦c, dob d v⟧ := pr1 cc.

Lemma coneOutCommutes {g : graph} {d : diagram g C} {c : C} (cc : cone d c) :
  ∏ u v (e : edge u v), coneOut cc u · dmor d e = coneOut cc v.
Proof.
apply (pr2 cc).
Qed.

Definition isLimCone {g : graph} (d : diagram g C) (c0 : C)
  (cc0 : cone d c0) : UU := ∏ (c : C) (cc : cone d c),
    iscontr (∑ x : C⟦c,c0⟧, ∏ v, x · coneOut cc0 v = coneOut cc v).

Definition LimCone {g : graph} (d : diagram g C) : UU :=
   ∑ (A : (∑ l, cone d l)), isLimCone d (pr1 A) (pr2 A).

Definition mk_LimCone {g : graph} (d : diagram g C)
  (c : C) (cc : cone d c) (isCC : isLimCone d c cc) : LimCone d
  := tpair _ (tpair _ c cc) isCC.

(** [lim] is the tip of the [LimCone] *)
Definition lim {g : graph} {d : diagram g C} (CC : LimCone d) : C
  := pr1 (pr1 CC).

Definition limCone {g : graph} {d : diagram g C} (CC : LimCone d) :
  cone d (lim CC) := pr2 (pr1 CC).

Definition limOut {g : graph} {d : diagram g C} (CC : LimCone d) :
  ∏ (v : vertex g), C⟦lim CC, dob d v⟧ := coneOut (limCone CC).

Lemma limOutCommutes {g : graph} {d : diagram g C}
  (CC : LimCone d) : ∏ (u v : vertex g) (e : edge u v),
   limOut CC u · dmor d e = limOut CC v.
Proof.
exact (coneOutCommutes (limCone CC)).
Qed.

Lemma limUnivProp {g : graph} {d : diagram g C}
  (CC : LimCone d) : ∏ (c : C) (cc : cone d c),
  iscontr (∑ x : C⟦c, lim CC⟧, ∏ (v : vertex g), x · limOut CC v = coneOut cc v).
Proof.
apply (pr2 CC).
Qed.

Lemma isaprop_isLimCone {g : graph} {d : diagram g C} (c0 : C)
  (cc0 : cone d c0) : isaprop (isLimCone d c0 cc0).
Proof.
repeat (apply impred; intro).
apply isapropiscontr.
Qed.

Definition isLimCone_LimCone {g : graph} {d : diagram g C}
    (CC : LimCone d)
  : isLimCone d (lim CC) (tpair _ (limOut CC) (limOutCommutes CC))
  := pr2 CC.

Definition limArrow {g : graph} {d : diagram g C} (CC : LimCone d)
  (c : C) (cc : cone d c) : C⟦c, lim CC⟧ :=
  pr1 (pr1 (isLimCone_LimCone CC c cc)).

Lemma limArrowCommutes {g : graph} {d : diagram g C} (CC : LimCone d)
  (c : C) (cc : cone d c) (u : vertex g) :
   limArrow CC c cc · limOut CC u = coneOut cc u.
Proof.
exact ((pr2 (pr1 (isLimCone_LimCone CC _ cc))) u).
Qed.

Lemma limArrowUnique {g : graph} {d : diagram g C} (CC : LimCone d)
  (c : C) (cc : cone d c) (k : C⟦c, lim CC⟧)
  (Hk : ∏ (u : vertex g), k · limOut CC u = coneOut cc u) :
  k = limArrow CC c cc.
Proof.
now apply path_to_ctr, Hk.
Qed.

Lemma Cone_precompose {g : graph} {d : diagram g C}
  {c : C} (cc : cone d c) (x : C) (f : C⟦x,c⟧) :
    ∏ u v (e : edge u v), (f · coneOut cc u) · dmor d e = f · coneOut cc v.
Proof.
now intros u v e; rewrite <- assoc, coneOutCommutes.
Qed.

Lemma limArrowEta {g : graph} {d : diagram g C} (CC : LimCone d)
  (c : C) (f : C⟦c, lim CC⟧) :
  f = limArrow CC c (tpair _ (λ u, f · limOut CC u)
                 (Cone_precompose (limCone CC) c f)).
Proof.
now apply limArrowUnique.
Qed.

Definition limOfArrows {g : graph} {d1 d2 : diagram g C}
  (CC1 : LimCone d1) (CC2 : LimCone d2)
  (f : ∏ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∏ u v (e : edge u v), f u · dmor d2 e = dmor d1 e · f v) :
  C⟦lim CC1 , lim CC2⟧.
Proof.
apply limArrow; use mk_cone.
- now intro u; apply (limOut CC1 u · f u).
- abstract (intros u v e; simpl;
            now rewrite <- assoc, fNat, assoc, limOutCommutes).
Defined.

Lemma limOfArrowsOut {g : graph} (d1 d2 : diagram g C)
  (CC1 : LimCone d1) (CC2 : LimCone d2)
  (f : ∏ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∏ u v (e : edge u v), f u · dmor d2 e = dmor d1 e · f v) :
    ∏ u, limOfArrows CC1 CC2 f fNat · limOut CC2 u =
          limOut CC1 u · f u.
Proof.
now unfold limOfArrows; intro u; rewrite limArrowCommutes.
Qed.

Lemma postCompWithLimOfArrows_subproof {g : graph} {d1 d2 : diagram g C}
  (CC1 : LimCone d1) (CC2 : LimCone d2)
  (f : ∏ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∏ u v (e : edge u v), f u · dmor d2 e = dmor d1 e · f v)
  (x : C) (cc : cone d1 x) u v (e : edge u v) :
    (coneOut cc u · f u) · dmor d2 e = coneOut cc v · f v.
Proof.
now rewrite <- (coneOutCommutes cc u v e), <- assoc, fNat, assoc.
Defined.

Lemma postCompWithLimOfArrows {g : graph} (d1 d2 : diagram g C)
  (CC1 : LimCone d1) (CC2 : LimCone d2)
  (f : ∏ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∏ u v (e : edge u v), f u · dmor d2 e = dmor d1 e · f v)
  (x : C) (cc : cone d1 x) :
     limArrow CC1 x cc · limOfArrows CC1 CC2 f fNat =
       limArrow CC2 x (mk_cone (λ u, coneOut cc u · f u)
         (postCompWithLimOfArrows_subproof CC1 CC2 f fNat x cc)).
Proof.
apply limArrowUnique; intro u.
now rewrite <- assoc, limOfArrowsOut, assoc, limArrowCommutes.
Qed.

Lemma postCompWithLimArrow {g : graph} (D : diagram g C)
 (CC : LimCone D) (c : C) (cc : cone D c) (d : C) (k : C⟦d,c⟧) :
   k · limArrow CC c cc  =
   limArrow CC d (mk_cone (λ u, k · coneOut cc u)
              (Cone_precompose cc d k)).
Proof.
  apply limArrowUnique.
  now intro u; rewrite <- assoc, limArrowCommutes.
Qed.

Lemma lim_endo_is_identity {g : graph} (D : diagram g C)
  (CC : LimCone D) (k : lim CC --> lim CC)
  (H : ∏ u, k · limOut CC u = limOut CC u) :
  identity _ = k.
Proof.
use (uniqueExists _ _ (limUnivProp CC _ _)).
- now apply (limCone CC).
- intros v; simpl.
  unfold compose. simpl.
  now apply id_left.
- simpl; now apply H.
Qed.


Lemma isLim_is_iso {g : graph} (D : diagram g C) (CC : LimCone D) (d : C) (cd : cone D d) :
  isLimCone D d cd -> is_iso (limArrow CC d cd).
Proof.
intro H.
apply is_iso_from_is_z_iso.
set (CD := mk_LimCone D d cd H).
apply (tpair _ (limArrow (mk_LimCone D d cd H) (lim CC) (limCone CC))).
split.
    apply pathsinv0.
    change d with (lim CD).
    apply lim_endo_is_identity. simpl; intro u;
      rewrite <- assoc.
      eapply pathscomp0; [eapply maponpaths; apply limArrowCommutes|].
      apply (limArrowCommutes CC).
      apply pathsinv0, (lim_endo_is_identity _ CC); simpl; intro u;
      rewrite <- assoc.
      eapply pathscomp0; [eapply maponpaths; apply (limArrowCommutes CC)|].
      apply (limArrowCommutes CD).
Defined.


Lemma inv_isLim_is_iso {g : graph} (D : diagram g C) (CC : LimCone D) (d : C)
  (cd : cone D d) (H : isLimCone D d cd) :
  inv_from_iso (isopair _ (isLim_is_iso D CC d cd H)) =
  limArrow (mk_LimCone D d cd H) _ (limCone CC).
Proof.
cbn. unfold precomp_with.
apply id_right.
Qed.

Lemma is_iso_isLim {g : graph} (D : diagram g C) (CC : LimCone D) (d : C) (cd : cone D d) :
  is_iso (limArrow CC d cd) -> isLimCone D d cd.
Proof.
intro H.
set (iinv := z_iso_inv_from_is_z_iso _ (is_z_iso_from_is_iso _ H)).
intros x cx.
use tpair.
- use tpair.
  + exact (limArrow CC x cx·iinv).
  + simpl; intro u.
    assert (XR:=limArrowCommutes CC x cx u).
    eapply pathscomp0; [| apply XR].
    eapply pathscomp0; [ apply (!assoc _ _ _ ) |].
    apply maponpaths.
    apply z_iso_inv_on_right.
    apply pathsinv0, limArrowCommutes.
- intros p; destruct p as [f Hf].
  apply subtypeEquality.
  + intro a; apply impred; intro u; apply hsC.
  + simpl; apply  z_iso_inv_on_left; simpl.
    apply pathsinv0, limArrowUnique; intro u.
    cbn in *.
    eapply pathscomp0; [| apply Hf].
    eapply pathscomp0. apply (!assoc _ _ _ ).
    apply maponpaths.
    apply limArrowCommutes.
Defined.


(*
Definition Cocone_by_postcompose {g : graph} (D : diagram g C)
 (c : C) (cc : cocone D c) (d : C) (k : C⟦c,d⟧) : cocone D d.
Proof.
now exists (λ u, coconeIn cc u · k); apply Cocone_postcompose.
Defined.

Lemma isColim_weq_subproof1 {g : graph} (D : diagram g C)
  (c : C) (cc : cocone D c) (d : C) (k : C⟦c,d⟧) :
  ∏ u, coconeIn cc u · k = pr1 (Cocone_by_postcompose D c cc d k) u.
Proof.
now intro u.
Qed.

Lemma isColim_weq_subproof2 (g : graph) (D : diagram g C)
  (c : C) (cc : cocone D c) (H : ∏ d, isweq (Cocone_by_postcompose D c cc d))
  (d : C) (cd : cocone D d) (u : vertex g) :
    coconeIn cc u · invmap (weqpair _ (H d)) cd = coconeIn cd u.
Proof.
rewrite (isColim_weq_subproof1 D c cc d (invmap (weqpair _ (H d)) _) u).
set (p := homotweqinvweq (weqpair _ (H d)) cd); simpl in p.
now rewrite p.
Qed.

Lemma isColim_weq {g : graph} (D : diagram g C) (c : C) (cc : cocone D c) :
  isColimCocone D c cc <-> ∏ d, isweq (Cocone_by_postcompose D c cc d).
Proof.
split.
- intros H d.
  refine (gradth _ _ _ _).
  + intros k.
    exact (colimArrow (mk_ColimCocone D c cc H) _ k).
  + abstract (intro k; simpl;
              now apply pathsinv0, (colimArrowEta (mk_ColimCocone D c cc H))).
  + abstract (simpl; intro k;
              apply total2_paths_second_isaprop;
                [ now repeat (apply impred; intro); apply hsC
                | destruct k as [k Hk]; simpl; apply funextsec; intro u;
                  now apply (colimArrowCommutes (mk_ColimCocone D c cc H))]).
- intros H d cd.
  refine (tpair _ _ _).
  + exists (invmap (weqpair _ (H d)) cd).
    abstract (intro u; now apply isColim_weq_subproof2).
  + abstract (intro t; apply total2_paths_second_isaprop;
                [ now apply impred; intro; apply hsC
                | destruct t as [t Ht]; simpl;
                  apply (invmaponpathsweq (weqpair _ (H d))); simpl;
                  apply total2_paths_second_isaprop;
                    [ now repeat (apply impred; intro); apply hsC
                    | simpl; apply pathsinv0, funextsec; intro u; rewrite Ht;
                      now apply isColim_weq_subproof2]]).
Defined.
*)

Definition iso_from_lim_to_lim {g : graph} {d : diagram g C}
  (CC CC' : LimCone d) : iso (lim CC) (lim CC').
Proof.
use isopair.
- apply limArrow, limCone.
- use is_iso_qinv.
  + apply limArrow, limCone.
  + abstract (now split; apply pathsinv0, lim_endo_is_identity; intro u;
              rewrite <- assoc, limArrowCommutes; eapply pathscomp0; try apply limArrowCommutes).
Defined.

End lim_def.

Section Lims.

Definition Lims (C : precategory) : UU := ∏ (g : graph) (d : diagram g C), LimCone d.
Definition hasLims (C : precategory) : UU  :=
  ∏ (g : graph) (d : diagram g C), ishinh (LimCone d).

(** Limits of a specific shape *)
Definition Lims_of_shape (g : graph) (C : precategory) : UU :=
  ∏ (d : diagram g C), LimCone d.

Section Universal_Unique.

Variable (C : univalent_category).

Let H : is_univalent C := pr2 C.

Lemma isaprop_Lims : isaprop (Lims C).
Proof.
apply impred; intro g; apply impred; intro cc.
apply invproofirrelevance; intros Hccx Hccy.
apply subtypeEquality.
- intro; apply isaprop_isLimCone.
- apply (total2_paths_f (isotoid _ H (iso_from_lim_to_lim Hccx Hccy))).
  set (B c := ∏ v, C⟦c,dob cc v⟧).
  set (C' (c : C) f := ∏ u v (e : edge u v), @compose _ c _ _ (f u) (dmor cc e) = f v).
  rewrite (@transportf_total2 _ B C').
  apply subtypeEquality.
  + intro; repeat (apply impred; intro); apply univalent_category_has_homsets.
  + abstract (now simpl; eapply pathscomp0; [apply transportf_isotoid_dep'|];
              apply funextsec; intro v; rewrite inv_isotoid, idtoiso_isotoid;
              cbn; unfold precomp_with; rewrite id_right; apply limArrowCommutes).
Qed.

End Universal_Unique.
End Lims.

(** * Limits in functor categories *)
Section LimFunctor.

Context {A C : precategory} (hsC : has_homsets C) {g : graph} (D : diagram g [A, C, hsC]).

Variable (HCg : ∏ (a : A), LimCone (diagram_pointwise hsC D a)).

Definition LimFunctor_ob (a : A) : C := lim (HCg a).

Definition LimFunctor_mor (a a' : A) (f : A⟦a, a'⟧) :
  C⟦LimFunctor_ob a,LimFunctor_ob a'⟧.
Proof.
use limOfArrows.
- now intro u; apply (# (pr1 (dob D u)) f).
- abstract (now intros u v e; simpl; apply (nat_trans_ax (# D e))).
Defined.

Definition LimFunctor_data : functor_data A C := tpair _ _ LimFunctor_mor.

Lemma is_functor_LimFunctor_data : is_functor LimFunctor_data.
Proof.
split.
- intro a; simpl.
  apply pathsinv0, lim_endo_is_identity; intro u.
  unfold LimFunctor_mor; rewrite limOfArrowsOut.
  assert (H : # (pr1 (dob D u)) (identity a) = identity (pr1 (dob D u) a)).
    apply (functor_id (dob D u) a).
  now rewrite H, id_right.
- intros a b c fab fbc; simpl; unfold LimFunctor_mor.
  apply pathsinv0.
  eapply pathscomp0; [now apply postCompWithLimOfArrows|].
  apply pathsinv0, limArrowUnique; intro u.
  rewrite limOfArrowsOut, (functor_comp (dob D u)); simpl.
  now rewrite <- assoc.
Qed.

Definition LimFunctor : functor A C := tpair _ _ is_functor_LimFunctor_data.

Definition lim_nat_trans_in_data v : [A, C, hsC] ⟦ LimFunctor, dob D v ⟧.
Proof.
use tpair.
- intro a; exact (limOut (HCg a) v).
- abstract (intros a a' f; apply (limOfArrowsOut _ _ (HCg a) (HCg a'))).
Defined.

Definition cone_pointwise (F : [A,C,hsC]) (cc : cone D F) a :
  cone (diagram_pointwise _ D a) (pr1 F a).
Proof.
use mk_cone.
- now intro v; apply (pr1 (coneOut cc v) a).
- abstract (intros u v e;
    now apply (nat_trans_eq_pointwise (coneOutCommutes cc u v e))).
Defined.

Lemma LimFunctor_unique (F : [A, C, hsC]) (cc : cone D F) :
  iscontr (∑ x : [A, C, hsC] ⟦ F, LimFunctor ⟧,
            ∏ v, x · lim_nat_trans_in_data v = coneOut cc v).
Proof.
use tpair.
- use tpair.
  + apply (tpair _ (λ a, limArrow (HCg a) _ (cone_pointwise F cc a))).
    abstract (intros a a' f; simpl; apply pathsinv0; eapply pathscomp0;
    [ apply (postCompWithLimOfArrows _ _ (HCg a))
    | apply pathsinv0; eapply pathscomp0;
      [ apply postCompWithLimArrow
      | apply limArrowUnique; intro u; eapply pathscomp0;
      [ now apply limArrowCommutes | now use nat_trans_ax]]]).
  + abstract (intro u; apply (nat_trans_eq hsC); simpl; intro a;
              now apply (limArrowCommutes (HCg a))).
- abstract (intro t; destruct t as [t1 t2];
            apply subtypeEquality; simpl;
              [ intro; apply impred; intro u; apply functor_category_has_homsets
              | apply (nat_trans_eq hsC); simpl; intro a;
                apply limArrowUnique; intro u;
                now apply (nat_trans_eq_pointwise (t2 u))]).
Defined.

Lemma LimFunctorCone : LimCone D.
Proof.
use mk_LimCone.
- exact LimFunctor.
- use mk_cone.
  + now apply lim_nat_trans_in_data.
  + abstract (now intros u v e; apply (nat_trans_eq hsC);
                  intro a; apply (limOutCommutes (HCg a))).
- now intros F cc; simpl; apply (LimFunctor_unique _ cc).
Defined.


Definition isLimFunctor_is_pointwise_Lim
  (X : [A,C,hsC]) (R : cone D X) (H : isLimCone D X R)
  : ∏ a, isLimCone (diagram_pointwise hsC D a) _ (cone_pointwise X R a).
Proof.
  intro a.
  apply (is_iso_isLim hsC _ (HCg a)).
  set (XR := isLim_is_iso D LimFunctorCone X R H).
  apply  (is_functor_iso_pointwise_if_iso _ _ _ _ _ _ XR).
Defined.


End LimFunctor.

Lemma LimsFunctorCategory (A C : precategory) (hsC : has_homsets C)
  (HC : Lims C) : Lims [A,C,hsC].
Proof.
now intros g d; apply LimFunctorCone.
Defined.

Lemma LimsFunctorCategory_of_shape (g : graph) (A C : precategory) (hsC : has_homsets C)
  (HC : Lims_of_shape g C) : Lims_of_shape g [A,C,hsC].
Proof.
now intros d; apply LimFunctorCone.
Defined.

Section map.

Context {C D : precategory} (F : functor C D).

Definition mapcone {g : graph} (d : diagram g C) {x : C}
  (dx : cone d x) : cone (mapdiagram F d) (F x).
Proof.
use mk_cone.
- simpl; intro n.
  exact (#F (coneOut dx n)).
- abstract (intros u v e; simpl; rewrite <- functor_comp;
            apply maponpaths, (coneOutCommutes dx _ _ e)).
Defined.

Definition preserves_limit {g : graph} (d : diagram g C) (L : C)
  (cc : cone d L) : UU :=
  isLimCone d L cc -> isLimCone (mapdiagram F d) (F L) (mapcone d cc).

(** ** Right adjoints preserve limits *)
Lemma right_adjoint_preserves_limit (HF : is_right_adjoint F) (hsC : has_homsets C) (hsD : has_homsets D)
      {g : graph} (d : diagram g C) (L : C) (ccL : cone d L) : preserves_limit d L ccL.
Proof.
intros HccL M ccM.
set (G := left_adjoint HF).
set (H := pr2 HF : are_adjoints G F).
apply (@iscontrweqb _ (∑ y : C ⟦ G M, L ⟧,
    ∏ i, y · coneOut ccL i = φ_adj_inv H (coneOut ccM i))).
- eapply (weqcomp (Y := ∑ y : C ⟦ G M, L ⟧,
    ∏ i, φ_adj H y · # F (coneOut ccL i) = coneOut ccM i)).
  + apply invweq, (weqbandf (adjunction_hom_weq H M L)); simpl; intro f.
    abstract (now apply weqiff; try (apply impred; intro; apply hsD)).
  + eapply (weqcomp (Y := ∑ y : C ⟦ G M, L ⟧,
      ∏ i, φ_adj H (y · coneOut ccL i) = coneOut ccM i)).
    * apply weqfibtototal; simpl; intro f.
      abstract (apply weqiff; try (apply impred; intro; apply hsD); split; intros HH i;
               [ now rewrite φ_adj_natural_postcomp; apply HH
               | now rewrite <- φ_adj_natural_postcomp; apply HH ]).
    * apply weqfibtototal; simpl; intro f.
      abstract (apply weqiff; [ | apply impred; intro; apply hsD | apply impred; intro; apply hsC ];
      split; intros HH i;
        [ now rewrite <- (HH i), φ_adj_inv_after_φ_adj
        | now rewrite (HH i),  φ_adj_after_φ_adj_inv ]).
- transparent assert (X : (cone d (G M))).
  { use mk_cone.
    + intro v; apply (φ_adj_inv H (coneOut ccM v)).
    + intros m n e; simpl.
      rewrite <- (coneOutCommutes ccM m n e); simpl.
      now rewrite φ_adj_inv_natural_postcomp.
  }
  apply (HccL (G M) X).
Defined.

End map.


(** * Definition of limits via colimits *)

(** Put in a module for namespace reasons *)

Require UniMath.CategoryTheory.opp_precat.

Module co.

Import UniMath.CategoryTheory.opp_precat.

Section lim_def.

Context {C : precategory} (hsC : has_homsets C).

(* A cone with tip c over a diagram d *)
(*
Definition cocone {g : graph} (d : diagram g C) (c : C) : UU :=
  ∑ (f : ∏ (v : vertex g), C⟦dob d v,c⟧),
    ∏ (u v : vertex g) (e : edge u v), dmor d e · f v = f u.
*)

Definition opp_diagram g C := diagram g C^op.

Definition cone {g : graph} (d : diagram g C^op) (c : C) : UU :=
  @cocone C^op g d c.

(*
Definition mk_cocone {g : graph} {d : diagram g C} {c : C}
  (f : ∏ v, C⟦dob d v,c⟧) (Hf : ∏ u v e, dmor d e · f v = f u) :
  cocone d c := tpair _ f Hf.
*)

Definition mk_cone {g : graph} {d : diagram g C^op} {c : C}
  (f : ∏ v, C⟦c, dob d v⟧) (Hf : ∏ u v (e : edge u v) , f v · dmor d e  = f u) :
  cone d c
  := tpair _ f Hf.

(* The injections to c in the cocone *)
Definition coneOut {g : graph} {d : diagram g C^op} {c : C} (cc : cone d c) :
  ∏ v, C⟦c, dob d v⟧ := coconeIn cc.

Lemma coneOutCommutes {g : graph} {d : diagram g C^op} {c : C} (cc : cone d c) :
  ∏ u v (e : edge u v), coneOut cc v · dmor d e = coneOut cc u.
Proof.
  apply (coconeInCommutes cc).
Qed.

(* cc0 is a colimit cocone if for any other cocone cc over the same
   diagram there is a unique morphism from the tip of cc0 to the tip
   of cc *)
Definition isLimCone {g : graph} (d : diagram g C^op) (c0 : C)
  (cc0 : cone d c0) : UU :=
   isColimCocone _ _ cc0.
(*
∏ (c : C) (cc : cone d c),
      isColimCocone
    iscontr (∑ x : C⟦c0,c⟧, ∏ v, coconeIn cc0 v · x = coconeIn cc v).
*)

Definition LimCone {g : graph} (d : diagram g C^op) : UU :=
  ColimCocone d.

Definition mk_LimCone {g : graph} (d : diagram g C^op)
  (c : C) (cc : cone d c) (isCC : isLimCone d c cc) : LimCone d.
Proof.
use mk_ColimCocone.
- apply c.
- apply cc.
- apply isCC.
Defined.

Definition Lims : UU := ∏ (g : graph) (d : diagram g C^op), LimCone d.
Definition hasLims : UU  :=
  ∏ (g : graph) (d : diagram g C^op), ishinh (LimCone d).

(* lim is the tip of the lim cone *)
Definition lim {g : graph} {d : diagram g C^op} (CC : LimCone d) : C
  := colim CC.

Definition limCone {g : graph} {d : diagram g C^op} (CC : LimCone d) :
  cone d (lim CC) := colimCocone CC.

Definition limOut {g : graph} {d : diagram g C^op} (CC : LimCone d) :
  ∏ (v : vertex g), C⟦lim CC, dob d v⟧ := coneOut (limCone CC).

Lemma limOutCommutes {g : graph} {d : diagram g C^op}
  (CC : LimCone d) : ∏ (u v : vertex g) (e : edge u v),
   limOut CC v · dmor d e = limOut CC u.
Proof.
exact (coneOutCommutes (limCone CC)).
Qed.

Lemma limUnivProp {g : graph} {d : diagram g C^op}
  (CC : LimCone d) : ∏ (c : C) (cc : cone d c),
  iscontr (∑ x : C⟦c, lim CC⟧, ∏ (v : vertex g), x · limOut CC v = coneOut cc v).
Proof.
apply (colimUnivProp CC).
Qed.

Definition isLimCone_LimCone {g : graph} {d : diagram g C^op}
    (CC : LimCone d)
  : isLimCone d (lim CC) (tpair _ (limOut CC) (limOutCommutes CC))
  := isColimCocone_ColimCocone CC.

Definition limArrow {g : graph} {d : diagram g C^op} (CC : LimCone d)
  (c : C) (cc : cone d c) : C⟦c, lim CC⟧.
Proof.
 exact (colimArrow CC _ cc).
Defined.

Lemma limArrowCommutes {g : graph} {d : diagram g C^op} (CC : LimCone d)
  (c : C) (cc : cone d c) (u : vertex g) :
   limArrow CC c cc · limOut CC u = coneOut cc u.
Proof.
  exact (colimArrowCommutes CC _ cc _ ).
Qed.

Lemma limArrowUnique {g : graph} {d : diagram g C^op} (CC : LimCone d)
  (c : C) (cc : cone d c) (k : C⟦c, lim CC⟧)
  (Hk : ∏ (u : vertex g), k · limOut CC u = coneOut cc u) :
  k = limArrow CC c cc.
Proof.
  apply (colimArrowUnique CC c cc k Hk).
Qed.

Lemma Cone_precompose {g : graph} {d : diagram g C^op}
  {c : C} (cc : cone d c) (x : C) (f : C⟦x,c⟧) :
    ∏ u v (e : edge u v), (f · coneOut cc v) · dmor d e = f · coneOut cc u.
Proof.
  apply (Cocone_postcompose cc x f).
Qed.

Lemma limArrowEta {g : graph} {d : diagram g C^op} (CC : LimCone d)
  (c : C) (f : C⟦c, lim CC⟧) :
  f = limArrow CC c (tpair _ (λ u, f · limOut CC u)
                 (Cone_precompose (limCone CC) c f)).
Proof.
now apply limArrowUnique.
Qed.

Definition limOfArrows {g : graph} {d1 d2 : diagram g C^op}
  (CC1 : LimCone d1) (CC2 : LimCone d2)
  (f : ∏ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∏ u v (e : edge u v), f v · (dmor d2 e : C⟦dob d2 v, dob d2 u⟧)
                              =
                                (dmor d1 e : C⟦dob d1 v, dob d1 u⟧)· f u) :
  C⟦lim CC1 , lim CC2⟧.
Proof.
  use (colimOfArrows CC2 CC1).
  - apply f.
  - apply fNat.
Defined.

Lemma limOfArrowsOut {g : graph} (d1 d2 : diagram g C^op)
  (CC1 : LimCone d1) (CC2 : LimCone d2)
  (f : ∏ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∏ u v (e : edge u v), f v · dmor d2 e = (dmor d1 e : C ⟦ _ , _ ⟧)  · f u) :
    ∏ u, limOfArrows CC1 CC2 f fNat · limOut CC2 u =
          limOut CC1 u · f u.
Proof.
  apply (colimOfArrowsIn _ _ CC2 CC1 f fNat).
Qed.

Lemma postCompWithLimOfArrows_subproof {g : graph} {d1 d2 : diagram g C^op}
  (CC1 : LimCone d1) (CC2 : LimCone d2)
  (f : ∏ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∏ u v (e : edge u v), f v · dmor d2 e = (dmor d1 e : C ⟦ _ , _ ⟧)  · f u)
  (x : C) (cc : cone d1 x) u v (e : edge u v) :
    (coneOut cc v · f v) · dmor d2 e = coneOut cc u · f u.
Proof.
  apply (preCompWithColimOfArrows_subproof CC2 CC1 f fNat x cc _ _ e).
Defined.

Lemma postcompWithColimOfArrows {g : graph} (d1 d2 : diagram g C^op)
  (CC1 : LimCone d1) (CC2 : LimCone d2)
  (f : ∏ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∏ u v (e : edge u v), f v · dmor d2 e = (dmor d1 e : C ⟦ _ , _ ⟧)  · f u)
  (x : C) (cc : cone d1 x) :
     limArrow CC1 x cc · limOfArrows CC1 CC2 f fNat =
       limArrow CC2 x (mk_cone (λ u, coneOut cc u · f u)
         (postCompWithLimOfArrows_subproof CC1 CC2 f fNat x cc)).
Proof.
  apply limArrowUnique.
  intro.
  rewrite <- assoc.
  rewrite limOfArrowsOut.
  rewrite assoc.
  rewrite limArrowCommutes.
  apply idpath.
Qed.

Lemma precompWithLimArrow {g : graph} (D : diagram g C^op)
 (CC : LimCone D) (c : C) (cc : cone D c) (d : C) (k : C⟦d,c⟧) :
   k · limArrow CC c cc  =
   limArrow CC d (mk_cone (λ u, k · coneOut cc u)
              (Cone_precompose cc d k)).
Proof.
  apply limArrowUnique.
  now intro u; rewrite <- assoc, limArrowCommutes.
Qed.

Lemma lim_endo_is_identity {g : graph} (D : diagram g C^op)
  (CC : LimCone D) (k : lim CC --> lim CC)
  (H : ∏ u, k · limOut CC u = limOut CC u) :
  identity _ = k.
Proof.
use (uniqueExists _ _ (limUnivProp CC _ _)).
- now apply (limCone CC).
- intros v; simpl.
  unfold compose. simpl.
  now apply id_left.
- simpl; now apply H.
Qed.

(*
Definition Cocone_by_postcompose {g : graph} (D : diagram g C)
 (c : C) (cc : cocone D c) (d : C) (k : C⟦c,d⟧) : cocone D d.
Proof.
now exists (λ u, coconeIn cc u · k); apply Cocone_postcompose.
Defined.

Lemma isColim_weq_subproof1 {g : graph} (D : diagram g C)
  (c : C) (cc : cocone D c) (d : C) (k : C⟦c,d⟧) :
  ∏ u, coconeIn cc u · k = pr1 (Cocone_by_postcompose D c cc d k) u.
Proof.
now intro u.
Qed.

Lemma isColim_weq_subproof2 (g : graph) (D : diagram g C)
  (c : C) (cc : cocone D c) (H : ∏ d, isweq (Cocone_by_postcompose D c cc d))
  (d : C) (cd : cocone D d) (u : vertex g) :
    coconeIn cc u · invmap (weqpair _ (H d)) cd = coconeIn cd u.
Proof.
rewrite (isColim_weq_subproof1 D c cc d (invmap (weqpair _ (H d)) _) u).
set (p := homotweqinvweq (weqpair _ (H d)) cd); simpl in p.
now rewrite p.
Qed.

Lemma isColim_weq {g : graph} (D : diagram g C) (c : C) (cc : cocone D c) :
  isColimCocone D c cc <-> ∏ d, isweq (Cocone_by_postcompose D c cc d).
Proof.
split.
- intros H d.
  refine (gradth _ _ _ _).
  + intros k.
    exact (colimArrow (mk_ColimCocone D c cc H) _ k).
  + abstract (intro k; simpl;
              now apply pathsinv0, (colimArrowEta (mk_ColimCocone D c cc H))).
  + abstract (simpl; intro k;
              apply total2_paths_second_isaprop;
                [ now repeat (apply impred; intro); apply hsC
                | destruct k as [k Hk]; simpl; apply funextsec; intro u;
                  now apply (colimArrowCommutes (mk_ColimCocone D c cc H))]).
- intros H d cd.
  refine (tpair _ _ _).
  + exists (invmap (weqpair _ (H d)) cd).
    abstract (intro u; now apply isColim_weq_subproof2).
  + abstract (intro t; apply total2_paths_second_isaprop;
                [ now apply impred; intro; apply hsC
                | destruct t as [t Ht]; simpl;
                  apply (invmaponpathsweq (weqpair _ (H d))); simpl;
                  apply total2_paths_second_isaprop;
                    [ now repeat (apply impred; intro); apply hsC
                    | simpl; apply pathsinv0, funextsec; intro u; rewrite Ht;
                      now apply isColim_weq_subproof2]]).
Defined.
*)

Lemma isLim_is_iso {g : graph} (D : diagram g C^op) (CC : LimCone D) (d : C) (cd : cone D d) :
  isLimCone D d cd -> is_iso (limArrow CC d cd).
Proof.
intro H.
apply is_iso_from_is_z_iso.
set (CD := mk_LimCone D d cd H).
apply (tpair _ (limArrow (mk_LimCone D d cd H) (lim CC) (limCone CC))).
split.
    apply pathsinv0.
    change d with (lim CD).
    apply lim_endo_is_identity. simpl; intro u;
      rewrite <- assoc.
      eapply pathscomp0; [eapply maponpaths; apply limArrowCommutes|].
      apply (limArrowCommutes CC).
      apply pathsinv0, (lim_endo_is_identity _ CC); simpl; intro u;
      rewrite <- assoc.
      eapply pathscomp0; [eapply maponpaths; apply (limArrowCommutes CC)|].
      apply (limArrowCommutes CD).
Defined.


Lemma inv_isLim_is_iso {g : graph} (D : diagram g C^op) (CC : LimCone D) (d : C)
  (cd : cone D d) (H : isLimCone D d cd) :
  inv_from_iso (isopair _ (isLim_is_iso D CC d cd H)) =
  limArrow (mk_LimCone D d cd H) _ (limCone CC).
Proof.
cbn. unfold precomp_with.
apply id_right.
Qed.

Lemma is_iso_isLim {g : graph} (D : diagram g C^op) (CC : LimCone D) (d : C) (cd : cone D d) :
  is_iso (limArrow CC d cd) -> isLimCone D d cd.
Proof.
intro H.
set (iinv := z_iso_inv_from_is_z_iso _ (is_z_iso_from_is_iso _ H)).
intros x cx.
use tpair.
- use tpair.
  + exact (limArrow CC x cx·iinv).
  + simpl; intro u.
    assert (XR:=limArrowCommutes CC x cx u).
    eapply pathscomp0; [| apply XR].
    eapply pathscomp0; [ apply (!assoc _ _ _ ) |].
    apply maponpaths.
    apply z_iso_inv_on_right.
    apply pathsinv0, limArrowCommutes.
- intros p; destruct p as [f Hf].
  apply subtypeEquality.
  + intro a; apply impred; intro u; apply hsC.
  + simpl; apply  z_iso_inv_on_left; simpl.
    apply pathsinv0, limArrowUnique; intro u.
    cbn in *.
    eapply pathscomp0; [| apply Hf].
    eapply pathscomp0. apply (!assoc _ _ _ ).
    apply maponpaths.
    apply limArrowCommutes.
Defined.


End lim_def.

Arguments Lims : clear implicits.

Section LimFunctor.

Definition get_diagram (A C : precategory) (hsC : has_homsets C)
  (g : graph) (D : diagram g [A, C, hsC]^op) :
    diagram g [A^op, C^op, has_homsets_opp hsC].
Proof.
apply (tpair _ (λ u, from_opp_to_opp_opp _ _ _ (pr1 D u))).
intros u v e; simpl.
use tpair; simpl.
  + apply (pr2 D _ _ e).
  + abstract (intros a b f; apply pathsinv0, (pr2 (pr2 D u v e) b a f)).
Defined.

Definition get_cocone  (A C : precategory) (hsC : has_homsets C)
  (g : graph) (D : diagram g [A, C, hsC]^op) (F : functor A C) (ccF : cocone D F) :
  cocone (get_diagram A C hsC g D) (functor_opp F).
Proof.
destruct ccF as [t p]. (* If I remove this destruct the Qed for LimsFunctorCategory
                 takes twice as long *)
use mk_cocone.
- intro u; apply (tpair _ (pr1 (t u))).
  abstract (intros a b f; apply pathsinv0, (pr2 (t u) b a f)).
- abstract (intros u v e; apply (nat_trans_eq (has_homsets_opp hsC));
            now intro a; simpl; rewrite <- (p u v e)).
Defined.

Lemma LimFunctorCone (A C : precategory) (hsC : has_homsets C)
  (g : graph)
  (D : diagram g [A, C, hsC]^op)
  (HC : ∏ a : A^op,
            LimCone
              (diagram_pointwise (has_homsets_opp hsC) (get_diagram A C hsC g D) a))
  : LimCone D.
Proof.
set (HColim := ColimFunctorCocone (has_homsets_opp hsC) (get_diagram _ _ _ _ D) HC).
destruct HColim as [pr1x pr2x].
destruct pr1x as [pr1pr1x pr2pr1x].
destruct pr2pr1x as [pr1pr2pr1x pr2pr2pr1x].
simpl in *.
use (mk_ColimCocone _ (from_opp_opp_to_opp _ _ _ pr1pr1x)).
- use mk_cocone.
  + simpl; intros.
    use tpair.
    * intro a; apply (pr1pr2pr1x v a).
    * abstract (intros a b f; apply pathsinv0, (nat_trans_ax (pr1pr2pr1x v) (*b a f*))).
  + abstract (intros u v e; apply (nat_trans_eq hsC); simpl; intro a;
              now rewrite <- (pr2pr2pr1x u v e)).
- intros F ccF.
  set (H := pr2x (from_opp_to_opp_opp _ _ _ F) (get_cocone _ _ _ _ _ _ ccF)).
  destruct H as [H1 H2].
  destruct H1 as [α Hα].
  simpl in *.
  use tpair.
  + use tpair.
    * exists α.
      abstract (intros a b f; simpl; now apply pathsinv0, (nat_trans_ax α b a f)).
    * abstract (intro u; apply (nat_trans_eq hsC); intro a;
        destruct ccF as [t p]; apply (toforallpaths _ _ _ (maponpaths pr1 (Hα u)) a)).
  + intro H; destruct H as [f Hf]; apply subtypeEquality.
    * abstract (intro β; repeat (apply impred; intro);
        now apply (has_homsets_opp (functor_category_has_homsets A C hsC))).
    * match goal with |[ H2 : ∏ _ : ?TT ,  _ = _ ,,_   |- _ ] =>
                       transparent assert (T : TT) end.
      (*
      refine (let T : ∑ x : nat_trans pr1pr1x (functor_opp F),
                         ∏ v, nat_trans_comp (functor_opp (pr1 D v)) _ _
                                (pr1pr2pr1x v) x =
                               coconeIn (get_cocone A C hsC g D F ccF) v :=
                  _ in _).
      *)
      { use (tpair _ (tpair _ (pr1 f) _)); simpl.
        - abstract (intros x y fxy; apply pathsinv0, (pr2 f y x fxy)).
        - abstract (intro u; apply (nat_trans_eq (has_homsets_opp hsC)); intro x;
            destruct ccF as [t p]; apply (toforallpaths _ _ _ (maponpaths pr1 (Hf u)) x)).
      }
      set (T' := maponpaths pr1 (H2 T)); simpl in T'.
      apply (nat_trans_eq hsC); intro a; simpl.
      now rewrite <- T'.
Defined.

End LimFunctor.

(*

(* Defines colimits in functor categories when the target has colimits *)
Section ColimFunctor.

Variable A C : precategory.
Variable HC : Colims C.
Variable hsC : has_homsets C.
Variable g : graph.
Variable D : diagram g [A, C, hsC].

Definition diagram_pointwise (a : A) : diagram g C.
Proof.
exists (λ v, pr1 (dob D v) a); intros u v e.
now apply (pr1 (dmor D e) a).
Defined.

Let HCg a := HC g (diagram_pointwise a).

Definition ColimFunctor_ob (a : A) : C := colim (HCg a).

Definition ColimFunctor_mor (a a' : A) (f : A⟦a, a'⟧) :
  C⟦ColimFunctor_ob a,ColimFunctor_ob a'⟧.
Proof.
refine (colimOfArrows _ _ _ _).
- now intro u; apply (# (pr1 (dob D u)) f).
- abstract (now intros u v e; simpl; apply pathsinv0, (nat_trans_ax (dmor D e))).
Defined.

Definition ColimFunctor_data : functor_data A C := tpair _ _ ColimFunctor_mor.

Lemma is_functor_ColimFunctor_data : is_functor ColimFunctor_data.
Proof.
split.
- intro a; simpl.
  apply pathsinv0, colim_endo_is_identity; intro u.
  unfold ColimFunctor_mor.
  now rewrite colimOfArrowsIn, (functor_id (dob D u)), id_left.
- intros a b c fab fbc; simpl; unfold ColimFunctor_mor.
  apply pathsinv0.
  eapply pathscomp0; [now apply precompWithColimOfArrows|].
  apply pathsinv0, colimArrowUnique; intro u.
  rewrite colimOfArrowsIn.
  rewrite (functor_comp (dob D u)).
  now apply pathsinv0, assoc.
Qed.

Definition ColimFunctor : functor A C := tpair _ _ is_functor_ColimFunctor_data.

Definition colim_nat_trans_in_data v : [A, C, hsC] ⟦ dob D v, ColimFunctor ⟧.
Proof.
refine (tpair _ _ _).
- intro a; exact (colimIn (HCg a) v).
- abstract (intros a a' f;
            now apply pathsinv0, (colimOfArrowsIn _ _ (HCg a) (HCg a'))).
Defined.

Definition cocone_pointwise (F : [A,C,hsC]) (cc : cocone D F) a :
  cocone (diagram_pointwise a) (pr1 F a).
Proof.
refine (mk_cocone _ _).
- now intro v; apply (pr1 (coconeIn cc v) a).
- abstract (intros u v e;
    now apply (nat_trans_eq_pointwise  (coconeInCommutes cc u v e))).
Defined.

Lemma ColimFunctor_unique (F : [A, C, hsC]) (cc : cocone D F) :
  iscontr (∑ x : [A, C, hsC] ⟦ ColimFunctor, F ⟧,
            ∏ v : vertex g, colim_nat_trans_in_data v · x = coconeIn cc v).
Proof.
refine (tpair _ _ _).
- refine (tpair _ _ _).
  + apply (tpair _ (λ a, colimArrow (HCg a) _ (cocone_pointwise F cc a))).
    abstract (intros a a' f; simpl;
              eapply pathscomp0;
                [ now apply precompWithColimOfArrows
                | apply pathsinv0; eapply pathscomp0;
                  [ now apply postcompWithColimArrow
                  | apply colimArrowUnique; intro u;
                    eapply pathscomp0;
                      [ now apply colimArrowCommutes
                      | now apply pathsinv0, nat_trans_ax ]]]).
  + abstract (intro u; apply (nat_trans_eq hsC); simpl; intro a;
              now apply (colimArrowCommutes (HCg a))).
- abstract (intro t; destruct t as [t1 t2];
            apply (total2_paths_second_isaprop); simpl;
              [ apply impred; intro u; apply functor_category_has_homsets
              | apply (nat_trans_eq hsC); simpl; intro a;
                apply colimArrowUnique; intro u;
                now apply (nat_trans_eq_pointwise (t2 u))]).
Defined.

Lemma ColimFunctorCocone : ColimCocone D.
Proof.
refine (mk_ColimCocone _ _ _ _).
- exact ColimFunctor.
- refine (mk_cocone _ _).
  + now apply colim_nat_trans_in_data.
  + abstract (now intros u v e; apply (nat_trans_eq hsC);
                  intro a; apply (colimInCommutes (HCg a))).
- now intros F cc; simpl; apply (ColimFunctor_unique _ cc).
Defined.

End ColimFunctor.

Lemma ColimsFunctorCategory (A C : precategory) (hsC : has_homsets C)
  (HC : Colims C) : Colims [A,C,hsC].
Proof.
now intros g d; apply ColimFunctorCocone.
Defined.
*)

End co.