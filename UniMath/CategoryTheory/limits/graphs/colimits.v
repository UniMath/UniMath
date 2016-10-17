
(** *************************************************

Contents:

- Definitions of graphs and diagrams
- Formalization of colimits on this basis
- Rules for pre- and post-composition
- Proof that colimits form a property in a (saturated/univalent) category ([isaprop_Colims])
- Pointwise construction of colimits in functor precategories ([ColimsFunctorCategory])

Written by Benedikt Ahrens and Anders Mörtberg, 2015-2016

*****************************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.AdjunctionHomTypesWeq.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).

Section move_upstream.

Lemma uniqueExists (A : UU) (P : A -> UU)
  (Hexists : iscontr (total2 (fun a => P a)))
  (a b : A) (Ha : P a) (Hb : P b) : a = b.
Proof.
assert (H : tpair _ _ Ha = tpair _ _ Hb).
  now apply proofirrelevance, isapropifcontr.
exact (base_paths _ _ H).
Defined.

End move_upstream.

(** Definition of graphs and diagrams *)
Section diagram_def.

Definition graph := Σ (D : UU), D -> D -> UU.

Definition vertex : graph -> UU := pr1.
Definition edge {g : graph} : vertex g -> vertex g -> UU := pr2 g.

Definition diagram (g : graph) (C : precategory) : UU :=
  Σ (f : vertex g -> C), Π (a b : vertex g), edge a b -> C⟦f a, f b⟧.

Definition dob {g : graph} {C : precategory} (d : diagram g C) : vertex g -> C :=
  pr1 d.

Definition dmor {g : graph} {C : precategory} (d : diagram g C) :
  Π {a b}, edge a b -> C⟦dob d a,dob d b⟧ := pr2 d.

Section diagram_from_functor.

Variables (J C : precategory).
Variable (F : functor J C).

Definition graph_from_precategory : graph := pr1 (pr1 J).

Definition diagram_from_functor : diagram graph_from_precategory C :=
  tpair _ _ (pr2 (pr1 F)).

End diagram_from_functor.

End diagram_def.

Coercion graph_from_precategory : precategory >-> graph.


(** * Definition of colimits *)
Section colim_def.

Context {C : precategory} (hsC : has_homsets C).

(** A cocone with tip c over a diagram d *)
Definition cocone {g : graph} (d : diagram g C) (c : C) : UU :=
  Σ (f : Π (v : vertex g), C⟦dob d v,c⟧),
    Π (u v : vertex g) (e : edge u v), dmor d e ;; f v = f u.

Definition mk_cocone {g : graph} {d : diagram g C} {c : C}
  (f : Π v, C⟦dob d v,c⟧) (Hf : Π u v e, dmor d e ;; f v = f u) :
  cocone d c := tpair _ f Hf.

(** The injections to c in the cocone *)
Definition coconeIn {g : graph} {d : diagram g C} {c : C} (cc : cocone d c) :
  Π v, C⟦dob d v,c⟧ := pr1 cc.

Lemma coconeInCommutes {g : graph} {d : diagram g C} {c : C} (cc : cocone d c) :
  Π u v (e : edge u v), dmor d e ;; coconeIn cc v = coconeIn cc u.
Proof.
exact (pr2 cc).
Qed.

(** cc0 is a colimit cocone if for any other cocone cc over the same
   diagram there is a unique morphism from the tip of cc0 to the tip
   of cc *)
Definition isColimCocone {g : graph} (d : diagram g C) (c0 : C)
  (cc0 : cocone d c0) : UU := Π (c : C) (cc : cocone d c),
    iscontr (Σ x : C⟦c0,c⟧, Π v, coconeIn cc0 v ;; x = coconeIn cc v).

(* Definition isColim {g : graph} (d : diagram g C) (L : C) := *)
(*   Σ c : cocone d L, isColimCocone d L c. *)

Definition ColimCocone {g : graph} (d : diagram g C) : UU :=
  Σ (A : (Σ c0 : C, cocone d c0)), isColimCocone d (pr1 A) (pr2 A).

Definition mk_ColimCocone {g : graph} (d : diagram g C)
  (c : C) (cc : cocone d c) (isCC : isColimCocone d c cc) : ColimCocone d :=
    tpair _ (tpair _ c cc) isCC.

(** colim is the tip of the colim cocone *)
Definition colim {g : graph} {d : diagram g C} (CC : ColimCocone d) : C :=
  pr1 (pr1 CC).

Definition colimCocone {g : graph} {d : diagram g C} (CC : ColimCocone d) :
  cocone d (colim CC) := pr2 (pr1 CC).

Definition isColimCocone_from_ColimCocone {g : graph} {d : diagram g C} (CC : ColimCocone d) :
  isColimCocone d (colim CC) _ := pr2 CC.

Definition colimIn {g : graph} {d : diagram g C} (CC : ColimCocone d) :
  Π (v : vertex g), C⟦dob d v,colim CC⟧ := coconeIn (colimCocone CC).

Lemma colimInCommutes {g : graph} {d : diagram g C}
  (CC : ColimCocone d) : Π (u v : vertex g) (e : edge u v),
   dmor d e ;; colimIn CC v = colimIn CC u.
Proof.
exact (coconeInCommutes (colimCocone CC)).
Qed.

Lemma colimUnivProp {g : graph} {d : diagram g C}
  (CC : ColimCocone d) : Π (c : C) (cc : cocone d c),
  iscontr (Σ x : C⟦colim CC,c⟧, Π (v : vertex g), colimIn CC v ;; x = coconeIn cc v).
Proof.
exact (pr2 CC).
Qed.

Lemma isaprop_isColimCocone {g : graph} (d : diagram g C) (c0 : C)
  (cc0 : cocone d c0) : isaprop (isColimCocone d c0 cc0).
Proof.
repeat (apply impred; intro).
apply isapropiscontr.
Qed.

Definition isColimCocone_ColimCocone {g : graph} {d : diagram g C}
  (CC : ColimCocone d) :
  isColimCocone d (colim CC) (tpair _ (colimIn CC) (colimInCommutes CC)) := pr2 CC.

Definition colimArrow {g : graph} {d : diagram g C} (CC : ColimCocone d)
  (c : C) (cc : cocone d c) : C⟦colim CC,c⟧ := pr1 (pr1 (isColimCocone_ColimCocone CC c cc)).

Lemma colimArrowCommutes {g : graph} {d : diagram g C} (CC : ColimCocone d)
  (c : C) (cc : cocone d c) (u : vertex g) :
  colimIn CC u ;; colimArrow CC c cc = coconeIn cc u.
Proof.
exact ((pr2 (pr1 (isColimCocone_ColimCocone CC _ cc))) u).
Qed.

Lemma colimArrowUnique {g : graph} {d : diagram g C} (CC : ColimCocone d)
  (c : C) (cc : cocone d c) (k : C⟦colim CC,c⟧)
  (Hk : Π (u : vertex g), colimIn CC u ;; k = coconeIn cc u) :
  k = colimArrow CC c cc.
Proof.
now apply path_to_ctr, Hk.
Qed.

Lemma Cocone_postcompose {g : graph} {d : diagram g C}
  {c : C} (cc : cocone d c) (x : C) (f : C⟦c,x⟧) :
    Π u v (e : edge u v), dmor d e ;; (coconeIn cc v ;; f) = coconeIn cc u ;; f.
Proof.
now intros u v e; rewrite assoc, coconeInCommutes.
Qed.

Lemma colimArrowEta {g : graph} {d : diagram g C} (CC : ColimCocone d)
  (c : C) (f : C⟦colim CC,c⟧) :
  f = colimArrow CC c (tpair _ (λ u, colimIn CC u ;; f)
                 (Cocone_postcompose (colimCocone CC) c f)).
Proof.
now apply colimArrowUnique.
Qed.


Definition colimOfArrows {g : graph} {d1 d2 : diagram g C}
  (CC1 : ColimCocone d1) (CC2 : ColimCocone d2)
  (f : Π (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : Π u v (e : edge u v), dmor d1 e ;; f v = f u ;; dmor d2 e) :
  C⟦colim CC1,colim CC2⟧.
Proof.
apply colimArrow; simple refine (mk_cocone _ _).
- now intro u; apply (f u ;; colimIn CC2 u).
- abstract (intros u v e; simpl;
            now rewrite assoc, fNat, <- assoc, colimInCommutes).
Defined.

Lemma colimOfArrowsIn {g : graph} (d1 d2 : diagram g C)
  (CC1 : ColimCocone d1) (CC2 : ColimCocone d2)
  (f : Π (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : Π u v (e : edge u v), dmor d1 e ;; f v = f u ;; dmor d2 e) :
    Π u, colimIn CC1 u ;; colimOfArrows CC1 CC2 f fNat =
         f u ;; colimIn CC2 u.
Proof.
now unfold colimOfArrows; intro u; rewrite colimArrowCommutes.
Qed.

Lemma preCompWithColimOfArrows_subproof {g : graph} {d1 d2 : diagram g C}
  (CC1 : ColimCocone d1) (CC2 : ColimCocone d2)
  (f : Π (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : Π u v (e : edge u v), dmor d1 e ;; f v = f u ;; dmor d2 e)
  (x : C) (cc : cocone d2 x) u v (e : edge u v) :
     dmor d1 e ;; (f v ;; coconeIn cc v) = f u ;; coconeIn cc u.
Proof.
  now rewrite <- (coconeInCommutes cc u v e), !assoc, fNat.
Qed.

Lemma precompWithColimOfArrows {g : graph} (d1 d2 : diagram g C)
  (CC1 : ColimCocone d1) (CC2 : ColimCocone d2)
  (f : Π (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : Π u v (e : edge u v), dmor d1 e ;; f v = f u ;; dmor d2 e)
  (x : C) (cc : cocone d2 x) :
  colimOfArrows CC1 CC2 f fNat ;; colimArrow CC2 x cc =
  colimArrow CC1 x (mk_cocone (λ u, f u ;; coconeIn cc u)
     (preCompWithColimOfArrows_subproof CC1 CC2 f fNat x cc)).
Proof.
apply colimArrowUnique.
now intro u; rewrite assoc, colimOfArrowsIn, <- assoc, colimArrowCommutes.
Qed.

Lemma postcompWithColimArrow {g : graph} (D : diagram g C)
 (CC : ColimCocone D) (c : C) (cc : cocone D c) (d : C) (k : C⟦c,d⟧) :
   colimArrow CC c cc ;; k =
   colimArrow CC d (mk_cocone (λ u, coconeIn cc u ;; k)
              (Cocone_postcompose cc d k)).
Proof.
apply colimArrowUnique.
now intro u; rewrite assoc, colimArrowCommutes.
Qed.

Lemma colim_endo_is_identity {g : graph} (D : diagram g C)
  (CC : ColimCocone D) (k : colim CC --> colim CC)
  (H : Π u, colimIn CC u ;; k = colimIn CC u) :
  identity _ = k.
Proof.
unshelve refine (uniqueExists _ _ (colimUnivProp CC _ _) _ _ _ _).
- now apply (colimCocone CC).
- intros v; simpl.
  now apply id_right.
- now apply H.
Qed.

Definition Cocone_by_postcompose {g : graph} (D : diagram g C)
 (c : C) (cc : cocone D c) (d : C) (k : C⟦c,d⟧) : cocone D d.
Proof.
now exists (λ u, coconeIn cc u ;; k); apply Cocone_postcompose.
Defined.

Lemma isColim_weq_subproof1 {g : graph} (D : diagram g C)
  (c : C) (cc : cocone D c) (d : C) (k : C⟦c,d⟧) :
  Π u, coconeIn cc u ;; k = pr1 (Cocone_by_postcompose D c cc d k) u.
Proof.
now intro u.
Qed.

Lemma isColim_weq_subproof2 (g : graph) (D : diagram g C)
  (c : C) (cc : cocone D c) (H : Π d, isweq (Cocone_by_postcompose D c cc d))
  (d : C) (cd : cocone D d) (u : vertex g) :
    coconeIn cc u ;; invmap (weqpair _ (H d)) cd = coconeIn cd u.
Proof.
rewrite (isColim_weq_subproof1 D c cc d (invmap (weqpair _ (H d)) _) u).
set (p := homotweqinvweq (weqpair _ (H d)) cd); simpl in p.
now rewrite p.
Qed.

Lemma isColim_weq {g : graph} (D : diagram g C) (c : C) (cc : cocone D c) :
  isColimCocone D c cc <-> Π d, isweq (Cocone_by_postcompose D c cc d).
Proof.
split.
- intros H d.
  simple refine (gradth _ _ _ _).
  + intros k.
    exact (colimArrow (mk_ColimCocone D c cc H) _ k).
  + abstract (intro k; simpl;
              now apply pathsinv0, (colimArrowEta (mk_ColimCocone D c cc H))).
  + abstract (simpl; intro k;
              apply subtypeEquality;
                [ intro; now repeat (apply impred; intro); apply hsC
                | destruct k as [k Hk]; simpl; apply funextsec; intro u;
                  now apply (colimArrowCommutes (mk_ColimCocone D c cc H))]).
- intros H d cd.
  simple refine (tpair _ _ _).
  + exists (invmap (weqpair _ (H d)) cd).
    abstract (intro u; now apply isColim_weq_subproof2).
  + abstract (intro t; apply subtypeEquality;
                [ intro; now apply impred; intro; apply hsC
                | destruct t as [t Ht]; simpl;
                  apply (invmaponpathsweq (weqpair _ (H d))); simpl;
                  apply subtypeEquality;
                    [ intro; now repeat (apply impred; intro); apply hsC
                    | simpl; apply pathsinv0, funextsec; intro u; rewrite Ht;
                      now apply isColim_weq_subproof2]]).
Defined.

Lemma isColim_is_iso {g : graph} (D : diagram g C) (CC : ColimCocone D) (d : C) (cd : cocone D d) :
  isColimCocone D d cd -> is_iso (colimArrow CC d cd).
Proof.
intro H.
apply is_iso_from_is_z_iso.
set (CD := mk_ColimCocone D d cd H).
apply (tpair _ (colimArrow (mk_ColimCocone D d cd H) (colim CC) (colimCocone CC))).
abstract (split;
    [ apply pathsinv0, colim_endo_is_identity; simpl; intro u;
      rewrite assoc;
      eapply pathscomp0; [eapply cancel_postcomposition; apply colimArrowCommutes|];
      apply (colimArrowCommutes CD) |
      apply pathsinv0, (colim_endo_is_identity _ CD); simpl; intro u;
      rewrite assoc;
      eapply pathscomp0; [eapply cancel_postcomposition; apply (colimArrowCommutes CD)|];
      apply colimArrowCommutes ]).
Defined.

Lemma inv_isColim_is_iso {g : graph} (D : diagram g C) (CC : ColimCocone D) (d : C)
  (cd : cocone D d) (H : isColimCocone D d cd) :
  inv_from_iso (isopair _ (isColim_is_iso D CC d cd H)) =
  colimArrow (mk_ColimCocone D d cd H) _ (colimCocone CC).
Proof.
cbn. (* why??? *)
unfold precomp_with.
apply id_right.
Qed.

Lemma is_iso_isColim {g : graph} (D : diagram g C) (CC : ColimCocone D) (d : C) (cd : cocone D d) :
  is_iso (colimArrow CC d cd) -> isColimCocone D d cd.
Proof.
intro H.
set (iinv := z_iso_inv_from_is_z_iso _ (is_z_iso_from_is_iso _ H)).
intros x cx.
simple refine (tpair _ _ _).
- simple refine (tpair _ _ _).
  + exact (iinv ;; colimArrow CC x cx).
  + simpl; intro u.
    rewrite <- (colimArrowCommutes CC x cx u), assoc.
    apply cancel_postcomposition, pathsinv0, z_iso_inv_on_left, pathsinv0, colimArrowCommutes.
- intros p; destruct p as [f Hf].
  apply subtypeEquality.
  + intro a; apply impred; intro u; apply hsC.
  + simpl; apply pathsinv0, z_iso_inv_on_right; simpl.
    apply pathsinv0, colimArrowUnique; intro u.
    now rewrite <- (Hf u), assoc, colimArrowCommutes.
Defined.

Definition iso_from_colim_to_colim {g : graph} {d : diagram g C}
  (CC CC' : ColimCocone d) : iso (colim CC) (colim CC').
Proof.
use isopair.
- apply colimArrow, colimCocone.
- use is_iso_qinv.
  + apply colimArrow, colimCocone.
  + abstract (now split; apply pathsinv0, colim_endo_is_identity; intro u;
              rewrite assoc, colimArrowCommutes; eapply pathscomp0; try apply colimArrowCommutes).
Defined.

End colim_def.

Section Colims.

Definition Colims (C : precategory) : UU := Π {g : graph} (d : diagram g C), ColimCocone d.
Definition hasColims (C : precategory) : UU  :=
  Π {g : graph} (d : diagram g C), ishinh (ColimCocone d).

(** Colimits of a specific shape *)
Definition Colims_of_shape (g : graph) (C : precategory) : UU :=
  Π (d : diagram g C), ColimCocone d.

(** If C is a category then Colims is a prop *)
Section Universal_Unique.

Variables (C : category).

Let H : is_category C := pr2 C.

Lemma isaprop_Colims: isaprop (Colims C).
Proof.
apply impred; intro g; apply impred; intro cc.
apply invproofirrelevance; intros Hccx Hccy.
apply subtypeEquality.
- intro; apply isaprop_isColimCocone.
- apply (total2_paths (isotoid _ H (iso_from_colim_to_colim Hccx Hccy))).
  set (B c := Π v, C⟦dob cc v,c⟧).
  set (C' (c : C) f := Π u v (e : edge u v), @compose _ _ _ c (dmor cc e) (f v) = f u).
  rewrite (@transportf_total2 _ B C').
  apply subtypeEquality.
  + intro; repeat (apply impred; intro); apply category_has_homsets.
  + simpl; eapply pathscomp0; [apply transportf_isotoid_dep''|].
    apply funextsec; intro v.
    now rewrite idtoiso_isotoid; apply colimArrowCommutes.
Qed.

End Universal_Unique.
End Colims.

(** * Defines colimits in functor categories when the target has colimits *)
Section ColimFunctor.

Context {A C : precategory} (hsC : has_homsets C) {g : graph} (D : diagram g [A, C, hsC]).
(* Variable HC : Colims C. *) (* Too strong! *)

Definition diagram_pointwise (a : A) : diagram g C.
Proof.
exists (fun v => pr1 (dob D v) a); intros u v e.
now apply (pr1 (dmor D e) a).
Defined.

Variable (HCg : Π (a : A), ColimCocone (diagram_pointwise a)).

Definition ColimFunctor_ob (a : A) : C := colim (HCg a).

Definition ColimFunctor_mor (a a' : A) (f : A⟦a, a'⟧) :
  C⟦ColimFunctor_ob a,ColimFunctor_ob a'⟧.
Proof.
simple refine (colimOfArrows _ _ _ _).
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
simple refine (tpair _ _ _).
- intro a; exact (colimIn (HCg a) v).
- abstract (intros a a' f;
            now apply pathsinv0, (colimOfArrowsIn _ _ (HCg a) (HCg a'))).
Defined.

Definition cocone_pointwise (F : [A,C,hsC]) (cc : cocone D F) a :
  cocone (diagram_pointwise a) (pr1 F a).
Proof.
simple refine (mk_cocone _ _).
- now intro v; apply (pr1 (coconeIn cc v) a).
- abstract (intros u v e;
    now apply (nat_trans_eq_pointwise  (coconeInCommutes cc u v e))).
Defined.

Lemma ColimFunctor_unique (F : [A, C, hsC]) (cc : cocone D F) :
  iscontr (Σ x : [A, C, hsC] ⟦ ColimFunctor, F ⟧,
            Π v : vertex g, colim_nat_trans_in_data v ;; x = coconeIn cc v).
Proof.
simple refine (tpair _ _ _).
- simple refine (tpair _ _ _).
  + apply (tpair _ (fun a => colimArrow (HCg a) _ (cocone_pointwise F cc a))).
    abstract (intros a a' f; simpl;
              eapply pathscomp0;
                [ now apply precompWithColimOfArrows
                | apply pathsinv0; eapply pathscomp0;
                  [ now apply postcompWithColimArrow
                  | apply colimArrowUnique; intro u;
                    eapply pathscomp0;
                      [ now apply colimArrowCommutes
                      | apply pathsinv0; now refine (nat_trans_ax _ _ _ _) ]]]).
  + abstract (intro u; apply (nat_trans_eq hsC); simpl; intro a;
              now apply (colimArrowCommutes (HCg a))).
- abstract (intro t; destruct t as [t1 t2];
            apply subtypeEquality; simpl;
              [ intro; apply impred; intro u; apply functor_category_has_homsets
              | apply (nat_trans_eq hsC); simpl; intro a;
                apply colimArrowUnique; intro u;
                now apply (nat_trans_eq_pointwise (t2 u))]).
Defined.

Lemma ColimFunctorCocone : ColimCocone D.
Proof.
simple refine (mk_ColimCocone _ _ _ _).
- exact ColimFunctor.
- simple refine (mk_cocone _ _).
  + now apply colim_nat_trans_in_data.
  + abstract (now intros u v e; apply (nat_trans_eq hsC);
                  intro a; apply (colimInCommutes (HCg a))).
- now intros F cc; simpl; apply (ColimFunctor_unique _ cc).
Defined.


Definition isColimFunctor_is_pointwise_Colim
  (X : [A,C,hsC]) (R : cocone D X) (H : isColimCocone D X R)
  : Π a, isColimCocone (diagram_pointwise a) _ (cocone_pointwise X R a).
Proof.
  intro a.
  apply (is_iso_isColim hsC _ (HCg a)).
  set (XR := isColim_is_iso D ColimFunctorCocone X R H).
  apply  (is_functor_iso_pointwise_if_iso _ _ _ _ _ _ XR).
Defined.

End ColimFunctor.

Lemma ColimsFunctorCategory (A C : precategory) (hsC : has_homsets C)
  (HC : Colims C) : Colims [A,C,hsC].
Proof.
now intros g d; apply ColimFunctorCocone.
Defined.

Lemma ColimsFunctorCategory_of_shape (g : graph) (A C : precategory) (hsC : has_homsets C)
  (HC : Colims_of_shape g C) : Colims_of_shape g [A,C,hsC].
Proof.
now intros d; apply ColimFunctorCocone.
Defined.

Lemma pointwise_Colim_is_isColimFunctor
  {A C : precategory} (hsC: has_homsets C) {g : graph}
  (d : diagram g [A,C,hsC]) (G : [A,C,hsC]) (ccG : cocone d G)
  (H : Π a, isColimCocone _ _ (cocone_pointwise hsC d G ccG a)) :
  isColimCocone d G ccG.
Proof.
set (CC a := mk_ColimCocone _ _ _ (H a)).
set (D' := ColimFunctorCocone _ _ CC).
use is_iso_isColim.
- apply functor_category_has_homsets.
- apply D'.
- use is_iso_qinv.
  + mkpair.
    * intros a; apply identity.
    * abstract (intros a b f; rewrite id_left, id_right; simpl;
                apply (colimArrowUnique (CC a)); intro u; cbn;
                now rewrite <- (nat_trans_ax (coconeIn ccG u))).
  + abstract (split;
    [ apply (nat_trans_eq hsC); intros x; simpl; rewrite id_right;
      apply pathsinv0, colimArrowUnique; intros v;
      now rewrite id_right
    | apply (nat_trans_eq hsC); intros x; simpl; rewrite id_left;
      apply pathsinv0, (colimArrowUnique (CC x)); intro u;
      now rewrite id_right]).
Defined.

Section map.

Context {C D : precategory} (F : functor C D).

Definition mapdiagram {g : graph} (d : diagram g C) : diagram g D.
Proof.
mkpair.
- intros n; apply (F (dob d n)).
- simpl; intros m n e.
  apply (# F (dmor d e)).
Defined.

Definition mapcocone {g : graph} (d : diagram g C) {x : C}
  (dx : cocone d x) : cocone (mapdiagram d) (F x).
Proof.
use mk_cocone.
- simpl; intro n.
  exact (#F (coconeIn dx n)).
- abstract (intros u v e; simpl; rewrite <- functor_comp;
            apply maponpaths, (coconeInCommutes dx _ _ e)).
Defined.

End map.
