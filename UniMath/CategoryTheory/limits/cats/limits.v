(****************************************************
  Benedikt Ahrens and Anders Mörtberg, March 2016
*****************************************************)

(** *************************************************

Contents :

	    Definition of limits

*****************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Open Scope cat.

Section move_upstream.

Lemma path_to_ctr (A : UU) (B : A -> UU) (isc : iscontr (total2 (λ a, B a)))
           (a : A) (p : B a) : a = pr1 (pr1 isc).
Proof.
exact (maponpaths pr1 (pr2 isc (tpair _ a p))).
Defined.

Lemma uniqueExists (A : UU) (P : A -> UU)
  (Hexists : iscontr (total2 (λ a, P a)))
  (a b : A) (Ha : P a) (Hb : P b) : a = b.
Proof.
assert (H : tpair _ _ Ha = tpair _ _ Hb).
  now apply proofirrelevance, isapropifcontr.
exact (base_paths _ _ H).
Defined.

End move_upstream.

Section lim_def.

Definition cone {J C : precategory} (F : functor J C) (c : C) : UU :=
  ∑ (f : ∏ (v : J), C⟦c,F v⟧),
    ∏ (u v : J) (e : J⟦u,v⟧), f u · # F e = f v.

Definition mk_cone {J C : precategory} {F : functor J C} {c : C}
  (f : ∏ v, C⟦c, F v⟧) (Hf : ∏ u v (e : J⟦u,v⟧) , f u · # F e  = f v) :
  cone F c := tpair _ f Hf.

Definition coneOut {J C : precategory} {F : functor J C} {c : C} (cc : cone F c) :
  ∏ v, C⟦c, F v⟧ := pr1 cc.

Lemma coneOutCommutes {J C : precategory} {F : functor J C} {c : C}
  (cc : cone F c) : ∏ u v (e : J⟦u,v⟧), coneOut cc u · # F e = coneOut cc v.
Proof.
apply (pr2 cc).
Qed.

Definition isLimCone {J C : precategory} (F : functor J C)
  (l : C) (cc0 : cone F l) : UU := ∏ (c : C) (cc : cone F c),
    iscontr (∑ x : C⟦c,l⟧, ∏ v, x · coneOut cc0 v = coneOut cc v).

Definition LimCone {J C : precategory} (F : functor J C) : UU :=
  ∑ (A : (∑ l, cone F l)), isLimCone F (pr1 A) (pr2 A).

Definition mk_LimCone {J C : precategory} (F : functor J C)
  (c : C) (cc : cone F c) (isCC : isLimCone F c cc) : LimCone F :=
  tpair _ (tpair _ c cc) isCC.

(* lim is the tip of the lim cone *)
Definition lim {J C : precategory} {F : functor J C} (CC : LimCone F) : C
  := pr1 (pr1 CC).

Definition limCone {J C : precategory} {F : functor J C} (CC : LimCone F) :
  cone F (lim CC) := pr2 (pr1 CC).

Definition limOut {J C : precategory} {F : functor J C} (CC : LimCone F) :
  ∏ v, C⟦lim CC,F v⟧ := coneOut (limCone CC).

Lemma limOutCommutes {J C : precategory} {F : functor J C}
  (CC : LimCone F) : ∏ u v (e : J⟦u,v⟧),
   limOut CC u · # F e = limOut CC v.
Proof.
exact (coneOutCommutes (limCone CC)).
Qed.

Lemma limUnivProp {J C : precategory} {F : functor J C}
  (CC : LimCone F) : ∏ (c : C) (cc : cone F c),
  iscontr (∑ x : C⟦c, lim CC⟧, ∏ v, x · limOut CC v = coneOut cc v).
Proof.
exact (pr2 CC).
Qed.

Lemma isaprop_isLimCone {J C : precategory} (F : functor J C) (c0 : C)
  (cc0 : cone F c0) : isaprop (isLimCone F c0 cc0).
Proof.
repeat (apply impred; intro).
apply isapropiscontr.
Qed.

Definition isLimCone_LimCone {J C : precategory} {F : functor J C}
  (CC : LimCone F)
  : isLimCone F (lim CC) (tpair _ (limOut CC) (limOutCommutes CC))
  := pr2 CC.

Definition limArrow {J C : precategory} {F : functor J C} (CC : LimCone F)
  (c : C) (cc : cone F c) : C⟦c, lim CC⟧ := pr1 (pr1 (isLimCone_LimCone CC c cc)).

Lemma limArrowCommutes {J C : precategory} {F : functor J C} (CC : LimCone F)
  (c : C) (cc : cone F c) u :
   limArrow CC c cc · limOut CC u = coneOut cc u.
Proof.
exact ((pr2 (pr1 (isLimCone_LimCone CC _ cc))) u).
Qed.

Lemma limArrowUnique {J C : precategory} {F : functor J C} (CC : LimCone F)
  (c : C) (cc : cone F c) (k : C⟦c, lim CC⟧)
  (Hk : ∏ u, k · limOut CC u = coneOut cc u) :
  k = limArrow CC c cc.
Proof.
now apply path_to_ctr, Hk.
Qed.

Lemma Cone_precompose {J C : precategory} {F : functor J C}
  {c : C} (cc : cone F c) (x : C) (f : C⟦x,c⟧) :
    ∏ u v (e : J⟦u,v⟧), (f · coneOut cc u) · # F e = f · coneOut cc v.
Proof.
now intros u v e; rewrite <- assoc, coneOutCommutes.
Qed.

Lemma limArrowEta {J C : precategory} {F : functor J C} (CC : LimCone F)
  (c : C) (f : C⟦c, lim CC⟧) :
  f = limArrow CC c (tpair _ (λ u, f · limOut CC u)
                 (Cone_precompose (limCone CC) c f)).
Proof.
now apply limArrowUnique.
Qed.

Definition limOfArrows {J C : precategory} {F1 F2 : functor J C}
  (CC1 : LimCone F1) (CC2 : LimCone F2)
  (f : ∏ u, C⟦F1 u,F2 u⟧)
  (fNat : ∏ u v (e : J⟦u,v⟧), f u · # F2 e = # F1 e · f v) :
  C⟦lim CC1 , lim CC2⟧.
Proof.
apply limArrow; simple refine (mk_cone _ _).
- now intro u; apply (limOut CC1 u · f u).
- abstract (intros u v e; simpl;
            now rewrite <- assoc, fNat, assoc, limOutCommutes).
Defined.

Lemma limOfArrowsOut {J C : precategory} {F1 F2 : functor J C}
  (CC1 : LimCone F1) (CC2 : LimCone F2)
  (f : ∏ u, C⟦F1 u,F2 u⟧)
  (fNat : ∏ u v (e : J⟦u,v⟧), f u · # F2 e = # F1 e · f v) :
    ∏ u, limOfArrows CC1 CC2 f fNat · limOut CC2 u =
          limOut CC1 u · f u.
Proof.
now unfold limOfArrows; intro u; rewrite limArrowCommutes.
Qed.

Lemma postCompWithLimOfArrows_subproof
  {J C : precategory} {F1 F2 : functor J C}
  (CC1 : LimCone F1) (CC2 : LimCone F2)
  (f : ∏ u, C⟦F1 u,F2 u⟧)
  (fNat : ∏ u v (e : J⟦u,v⟧), f u · # F2 e = # F1 e · f v)
  (x : C) (cc : cone F1 x) u v (e : J⟦u,v⟧) :
    (coneOut cc u · f u) · # F2 e = coneOut cc v · f v.
Proof.
now rewrite <- (coneOutCommutes cc u v e), <- assoc, fNat, assoc.
Defined.

Lemma postcompWithLimOfArrows
  {J C : precategory} {F1 F2 : functor J C}
  (CC1 : LimCone F1) (CC2 : LimCone F2)
  (f : ∏ u, C⟦F1 u,F2 u⟧)
  (fNat : ∏ u v (e : J⟦u,v⟧), f u · # F2 e = # F1 e · f v)
  (x : C) (cc : cone F1 x) :
     limArrow CC1 x cc · limOfArrows CC1 CC2 f fNat =
       limArrow CC2 x (mk_cone (λ u, coneOut cc u · f u)
         (postCompWithLimOfArrows_subproof CC1 CC2 f fNat x cc)).
Proof.
apply limArrowUnique; intro u.
now rewrite <- assoc, limOfArrowsOut, assoc, limArrowCommutes.
Qed.

Lemma postcompWithLimArrow {J C : precategory} {F : functor J C}
 (CC : LimCone F) (c : C) (cc : cone F c) (d : C) (k : C⟦d,c⟧) :
   k · limArrow CC c cc  =
   limArrow CC d (mk_cone (λ u, k · coneOut cc u)
              (Cone_precompose cc d k)).
Proof.
apply limArrowUnique.
now intro u; rewrite <- assoc, limArrowCommutes.
Qed.

Lemma lim_endo_is_identity {J C : precategory} {F : functor J C}
  (CC : LimCone F) (k : lim CC --> lim CC)
  (H : ∏ u, k · limOut CC u = limOut CC u) :
  identity _ = k.
Proof.
unshelve refine (uniqueExists _ _ (limUnivProp CC _ _) _ _ _ _).
- now apply (limCone CC).
- now intros v; apply id_left.
- now apply H.
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

Definition iso_from_lim_to_lim {J C : precategory} {F : functor J C}
  (CC CC' : LimCone F) : iso (lim CC) (lim CC').
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

Definition Lims (C : precategory) : UU := ∏ (J : precategory) (F : functor J C), LimCone F.
Definition hasLims : UU  :=
  ∏ (J C : precategory) (F : functor J C), ishinh (LimCone F).
Definition Lims_of_shape (J C : precategory) : UU := ∏ (F : functor J C), LimCone F.

Section Universal_Unique.

Context (C : univalent_category).

Let H : is_univalent C := pr2 C.

Lemma isaprop_Lims: isaprop (Lims C).
Proof.
apply impred; intro J; apply impred; intro F.
apply invproofirrelevance; intros Hccx Hccy.
apply subtypeEquality.
- intro; apply isaprop_isLimCone.
- apply (total2_paths_f (isotoid _ H (iso_from_lim_to_lim Hccx Hccy))).
  set (B c := ∏ v, C⟦c,F v⟧).
  set (C' (c : C) f := ∏ u v (e : J⟦u,v⟧), @compose _ c _ _ (f u) (# F e) = f v).
  rewrite (@transportf_total2 _ B C').
  apply subtypeEquality.
  + intro; repeat (apply impred; intro); apply (pr2 H).
  + abstract (now simpl; eapply pathscomp0; [apply transportf_isotoid_dep'|];
              apply funextsec; intro v; rewrite inv_isotoid, idtoiso_isotoid;
              cbn; unfold precomp_with; rewrite id_right; apply limArrowCommutes).
Qed.

End Universal_Unique.
End Lims.

Section LimFunctor.

Variable A C : precategory.
Variable hsC : has_homsets C.
Variable (J : precategory).
Variable (D : functor J [A, C, hsC]).

Definition functor_pointwise (a : A) : functor J C.
Proof.
mkpair.
- apply (tpair _ (λ v, pr1 (D v) a)).
  intros u v e; simpl; apply (pr1 (# D e) a).
- abstract (mkpair;
    [ intro x; simpl;
      apply (toforallpaths _ _ _ (maponpaths pr1 (functor_id D x)) a)
    | intros x y z f g; simpl;
      apply (toforallpaths _ _ _ (maponpaths pr1 (functor_comp D f g)) a)]).
Defined.

Variable (HCg : ∏ (a : A), LimCone (functor_pointwise a)).

Definition LimFunctor_ob (a : A) : C := lim (HCg a).

Definition LimFunctor_mor (a a' : A) (f : A⟦a, a'⟧) :
  C⟦LimFunctor_ob a,LimFunctor_ob a'⟧.
Proof.
simple refine (limOfArrows _ _ _ _).
- now intro u; apply (# (pr1 (D u)) f).
- abstract (now intros u v e; simpl; apply (nat_trans_ax (# D e))).
Defined.

Definition LimFunctor_data : functor_data A C := tpair _ _ LimFunctor_mor.

Lemma is_functor_LimFunctor_data : is_functor LimFunctor_data.
Proof.
split.
- intro a; simpl.
  apply pathsinv0, lim_endo_is_identity; intro u.
  unfold LimFunctor_mor; rewrite limOfArrowsOut.
  assert (H : # (pr1 (D u)) (identity a) = identity (pr1 (D u) a)).
    apply (functor_id (D u) a).
  now rewrite H, id_right.
- intros a b c fab fbc; simpl; unfold LimFunctor_mor.
  apply pathsinv0.
  eapply pathscomp0; [now apply postcompWithLimOfArrows|].
  apply pathsinv0, limArrowUnique; intro u.
  rewrite limOfArrowsOut, (functor_comp (D u)); simpl.
  now rewrite <- assoc.
Qed.

Definition LimFunctor : functor A C := tpair _ _ is_functor_LimFunctor_data.

Definition lim_nat_trans_in_data v : [A, C, hsC] ⟦ LimFunctor, D v ⟧.
Proof.
mkpair.
- intro a; exact (limOut (HCg a) v).
- abstract (intros a a' f; apply (limOfArrowsOut (HCg a) (HCg a'))).
Defined.

Definition cone_pointwise (F : [A,C,hsC]) (cc : cone D F) a :
  cone (functor_pointwise a) (pr1 F a).
Proof.
simple refine (mk_cone _ _).
- now intro v; apply (pr1 (coneOut cc v) a).
- abstract (intros u v e;
    now apply (nat_trans_eq_pointwise (coneOutCommutes cc u v e))).
Defined.

Lemma LimFunctor_unique (F : [A, C, hsC]) (cc : cone D F) :
  iscontr (∑ x : [A, C, hsC] ⟦ F, LimFunctor ⟧,
            ∏ v, x · lim_nat_trans_in_data v = coneOut cc v).
Proof.
mkpair.
- mkpair.
  + apply (tpair _ (λ a, limArrow (HCg a) _ (cone_pointwise F cc a))).
    abstract (intros a a' f; simpl; apply pathsinv0; eapply pathscomp0;
    [ apply (postcompWithLimOfArrows (HCg a))
    | apply pathsinv0; eapply pathscomp0;
      [ apply postcompWithLimArrow
      | apply limArrowUnique; intro u; eapply pathscomp0;
      [ now apply limArrowCommutes | now refine (nat_trans_ax _ _ _ _)]]]).
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
simple refine (mk_LimCone _ _ _ _).
- exact LimFunctor.
- simple refine (mk_cone _ _).
  + now apply lim_nat_trans_in_data.
  + abstract (now intros u v e; apply (nat_trans_eq hsC);
                  intro a; apply (limOutCommutes (HCg a))).
- now intros F cc; simpl; apply (LimFunctor_unique _ cc).
Defined.

End LimFunctor.

Lemma LimsFunctorCategory (A C : precategory) (hsC : has_homsets C)
  (HC : Lims C) : Lims [A,C,hsC].
Proof.
now intros g d; apply LimFunctorCone.
Defined.

Lemma LimsFunctorCategory_of_shape (J A C : precategory) (hsC : has_homsets C)
  (HC : Lims_of_shape J C) : Lims_of_shape J [A,C,hsC].
Proof.
now intros d; apply LimFunctorCone.
Defined.
