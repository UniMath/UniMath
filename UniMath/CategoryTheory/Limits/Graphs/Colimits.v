
(** *************************************************

Contents:

- Definitions of graphs and diagrams
- Formalization of colimits on this basis
- Rules for pre- and post-composition
- Proof that colimits form a property in a (saturated/univalent) category ([isaprop_Colims])
- Pointwise construction of colimits in functor precategories ([ColimsFunctorCategory])

Written by Benedikt Ahrens and Anders Mörtberg, 2015-2016

*****************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Propositions.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.

(** Definition of graphs and diagrams *)
Section diagram_def.

Definition graph := ∑ (D : UU), D -> D -> UU.

Definition vertex : graph -> UU := pr1.
Definition edge {g : graph} : vertex g -> vertex g -> UU := pr2 g.

Definition make_graph (D : UU) (e : D → D → UU) : graph := tpair _ D e.

Definition diagram (g : graph) (C : precategory) : UU :=
  ∑ (f : vertex g -> C), ∏ (a b : vertex g), edge a b -> C⟦f a, f b⟧.

Definition make_diagram {g : graph} {C : precategory}
  (f : vertex g -> C)
  (P : (∏ (a b : vertex g),
         edge a b -> C⟦f a, f b⟧))
  : diagram g C
  := (f ,, P).

Definition dob {g : graph} {C : precategory} (d : diagram g C) : vertex g -> C :=
  pr1 d.

Definition dmor {g : graph} {C : precategory} (d : diagram g C) :
  ∏ {a b}, edge a b -> C⟦dob d a,dob d b⟧ := pr2 d.

Section diagram_from_functor.

Variables (J C : precategory).
Variable (F : functor J C).

Definition graph_from_precategory : graph :=  (pr1 (pr1 J)).

Definition diagram_from_functor : diagram graph_from_precategory C :=
  tpair _ _ (pr2 (pr1 F)).

End diagram_from_functor.

Definition constant_diagram
  {C : category}
  (J : graph)
  (c : C)
  : diagram J C
  := make_diagram (λ _, c) (λ _ _ _, identity c).

End diagram_def.

Coercion graph_from_precategory : precategory >-> graph.


(** * Definition of colimits *)
Section colim_def.

(** A cocone with tip c over a diagram d *)
Definition forms_cocone {C : precategory} {g : graph} (d : diagram g C) {c : C} (f : ∏ (v : vertex g), C⟦dob d v, c⟧) : UU
  := ∏ (u v : vertex g) (e : edge u v), dmor d e · f v = f u.

Definition cocone {C : precategory} {g : graph} (d : diagram g C) (c : C) : UU :=
  ∑ (f : ∏ (v : vertex g), C⟦dob d v,c⟧), forms_cocone d f.

Definition make_cocone {C : precategory} {g : graph} {d : diagram g C} {c : C}
  (f : ∏ v, C⟦dob d v,c⟧) (Hf : forms_cocone d f) :
  cocone d c := tpair _ f Hf.

(** The injections to c in the cocone *)
Definition coconeIn {C : precategory} {g : graph} {d : diagram g C} {c : C} (cc : cocone d c) :
  ∏ v, C⟦dob d v,c⟧ := pr1 cc.

(** not recommended! [Coercion coconeIn : cocone >-> Funclass.] *)

Lemma coconeInCommutes {C : precategory} {g : graph} {d : diagram g C} {c : C} (cc : cocone d c) :
  forms_cocone d (coconeIn cc).
Proof.
exact (pr2 cc).
Qed.

Definition cocone_paths {C : category} {g : graph} {d : diagram g C} {x : C}
           (cc1 cc2 : cocone d x)
           (eqin : ∏ g, coconeIn cc1 g = coconeIn cc2 g): cc1 = cc2.
Proof.
  use subtypePath'.
  - apply funextsec.
    exact eqin.
  - repeat (apply impred_isaprop; intro).
    apply C.
Defined.

Definition is_cocone_mor {C : precategory} {g : graph} {d : diagram g C} {c1 : C}
           (cc1 : cocone d c1) {c2 : C} (cc2 : cocone d c2) (x : c1 --> c2) : UU :=
  ∏ (v : vertex g), coconeIn cc1 v · x = coconeIn cc2 v.

Lemma isaprop_is_cocone_mor {C : category} {g : graph} {d : diagram g C}
  {c1 : C} (cc1 : cocone d c1) {c2 : C} (cc2 : cocone d c2) (f : c1 --> c2)
  : isaprop (is_cocone_mor cc1 cc2 f).
Proof.
  apply impred_isaprop ; intro.
  apply homset_property.
Qed.

(** cc0 is a colimit cocone if for any other cocone cc over the same
   diagram there is a unique morphism from the tip of cc0 to the tip
   of cc *)
Definition isColimCocone {C : precategory} {g : graph} (d : diagram g C) (c0 : C)
  (cc0 : cocone d c0) : UU := ∏ (c : C) (cc : cocone d c),
    iscontr (∑ x : C⟦c0,c⟧, is_cocone_mor cc0 cc x).

(* Definition isColim {g : graph} (d : diagram g C) (L : C) := *)
(*   ∑ c : cocone d L, isColimCocone d L c. *)

Definition ColimCocone {C : precategory} {g : graph} (d : diagram g C) : UU :=
  ∑ (A : (∑ c0 : C, cocone d c0)), isColimCocone d (pr1 A) (pr2 A).

Definition make_ColimCocone {C : precategory} {g : graph} (d : diagram g C)
  (c : C) (cc : cocone d c) (isCC : isColimCocone d c cc) : ColimCocone d :=
    tpair _ (tpair _ c cc) isCC.

(** colim is the tip of the colim cocone *)
Definition colim {C : precategory} {g : graph} {d : diagram g C} (CC : ColimCocone d) : C :=
  pr1 (pr1 CC).

Definition colimCocone {C : precategory} {g : graph} {d : diagram g C} (CC : ColimCocone d) :
  cocone d (colim CC) := pr2 (pr1 CC).

Definition isColimCocone_from_ColimCocone {C : precategory} {g : graph} {d : diagram g C} (CC : ColimCocone d) :
  isColimCocone d (colim CC) _ := pr2 CC.

Definition colimIn {C : precategory} {g : graph} {d : diagram g C} (CC : ColimCocone d) :
  ∏ (v : vertex g), C⟦dob d v,colim CC⟧ := coconeIn (colimCocone CC).

Lemma colimInCommutes {C : precategory} {g : graph} {d : diagram g C}
  (CC : ColimCocone d) : forms_cocone d (colimIn CC).
Proof.
exact (coconeInCommutes (colimCocone CC)).
Qed.

Lemma colimUnivProp {C : precategory} {g : graph} {d : diagram g C}
  (CC : ColimCocone d) : ∏ (c : C) (cc : cocone d c),
  iscontr (∑ x : C⟦colim CC,c⟧, ∏ (v : vertex g), colimIn CC v · x = coconeIn cc v).
Proof.
exact (pr2 CC).
Qed.

Lemma isaprop_isColimCocone {C : precategory} {g : graph} (d : diagram g C) (c0 : C)
  (cc0 : cocone d c0) : isaprop (isColimCocone d c0 cc0).
Proof.
repeat (apply impred; intro).
apply isapropiscontr.
Qed.

Definition colimArrow {C : precategory} {g : graph} {d : diagram g C} (CC : ColimCocone d)
  (c : C) (cc : cocone d c) : C⟦colim CC,c⟧ := pr1 (pr1 (isColimCocone_from_ColimCocone CC c cc)).

Lemma colimArrowCommutes {C : precategory} {g : graph} {d : diagram g C} (CC : ColimCocone d)
  (c : C) (cc : cocone d c) (u : vertex g) :
  colimIn CC u · colimArrow CC c cc = coconeIn cc u.
Proof.
exact ((pr2 (pr1 (isColimCocone_from_ColimCocone CC _ cc))) u).
Qed.

Lemma colimArrowUnique {C : precategory} {g : graph} {d : diagram g C} (CC : ColimCocone d)
  (c : C) (cc : cocone d c) (k : C⟦colim CC,c⟧)
  (Hk : ∏ (u : vertex g), colimIn CC u · k = coconeIn cc u) :
  k = colimArrow CC c cc.
Proof.
apply path_to_ctr. red. apply Hk.
Qed.

Lemma Cocone_postcompose {C : precategory} {g : graph} {d : diagram g C}
  {c : C} (cc : cocone d c) (x : C) (f : C⟦c,x⟧) :
    ∏ u v (e : edge u v), dmor d e · (coconeIn cc v · f) = coconeIn cc u · f.
Proof.
now intros u v e; rewrite assoc, coconeInCommutes.
Qed.

Lemma colimArrowEta {C : precategory} {g : graph} {d : diagram g C} (CC : ColimCocone d)
  (c : C) (f : C⟦colim CC,c⟧) :
  f = colimArrow CC c (tpair _ (λ u, colimIn CC u · f)
                 (Cocone_postcompose (colimCocone CC) c f)).
Proof.
now apply colimArrowUnique.
Qed.

Lemma colimArrowUnique' {C : precategory}
      {g : graph} {d : diagram g C} (CC : ColimCocone d)
      {c} (k k' : C ⟦ colim CC, c ⟧):
  (∏ u : vertex g, colimIn CC u · k = colimIn CC u · k') → k = k'.
Proof.
  intro eq.
  apply pathsinv0.
  etrans.
  { apply colimArrowEta. }
  apply pathsinv0.
  apply colimArrowUnique.
  cbn.
  exact eq.
Qed.

Definition colimOfArrows {C : precategory} {g : graph} {d1 d2 : diagram g C}
  (CC1 : ColimCocone d1) (CC2 : ColimCocone d2)
  (f : ∏ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∏ u v (e : edge u v), dmor d1 e · f v = f u · dmor d2 e) :
  C⟦colim CC1,colim CC2⟧.
Proof.
apply colimArrow; use make_cocone.
- now intro u; apply (f u · colimIn CC2 u).
- abstract (intros u v e; simpl;
            now rewrite assoc, fNat, <- assoc, colimInCommutes).
Defined.

Lemma colimOfArrowsIn {C : precategory} {g : graph} (d1 d2 : diagram g C)
  (CC1 : ColimCocone d1) (CC2 : ColimCocone d2)
  (f : ∏ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∏ u v (e : edge u v), dmor d1 e · f v = f u · dmor d2 e) :
    ∏ u, colimIn CC1 u · colimOfArrows CC1 CC2 f fNat =
         f u · colimIn CC2 u.
Proof.
now unfold colimOfArrows; intro u; rewrite colimArrowCommutes.
Qed.

Lemma preCompWithColimOfArrows_subproof {C : precategory} {g : graph} {d1 d2 : diagram g C}
  (CC1 : ColimCocone d1) (CC2 : ColimCocone d2)
  (f : ∏ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∏ u v (e : edge u v), dmor d1 e · f v = f u · dmor d2 e)
  (x : C) (cc : cocone d2 x) u v (e : edge u v) :
     dmor d1 e · (f v · coconeIn cc v) = f u · coconeIn cc u.
Proof.
  now rewrite <- (coconeInCommutes cc u v e), !assoc, fNat.
Qed.

Lemma precompWithColimOfArrows {C : precategory} {g : graph} (d1 d2 : diagram g C)
  (CC1 : ColimCocone d1) (CC2 : ColimCocone d2)
  (f : ∏ (u : vertex g), C⟦dob d1 u,dob d2 u⟧)
  (fNat : ∏ u v (e : edge u v), dmor d1 e · f v = f u · dmor d2 e)
  (x : C) (cc : cocone d2 x) :
  colimOfArrows CC1 CC2 f fNat · colimArrow CC2 x cc =
  colimArrow CC1 x (make_cocone (λ u, f u · coconeIn cc u)
     (preCompWithColimOfArrows_subproof CC1 CC2 f fNat x cc)).
Proof.
apply colimArrowUnique.
now intro u; rewrite assoc, colimOfArrowsIn, <- assoc, colimArrowCommutes.
Qed.

Lemma postcompWithColimArrow {C : precategory} {g : graph} (D : diagram g C)
 (CC : ColimCocone D) (c : C) (cc : cocone D c) (d : C) (k : C⟦c,d⟧) :
   colimArrow CC c cc · k =
   colimArrow CC d (make_cocone (λ u, coconeIn cc u · k)
              (Cocone_postcompose cc d k)).
Proof.
apply colimArrowUnique.
now intro u; rewrite assoc, colimArrowCommutes.
Qed.

Lemma colim_endo_is_identity {C : precategory} {g : graph} (D : diagram g C)
  (CC : ColimCocone D) (k : colim CC --> colim CC)
  (H : ∏ u, colimIn CC u · k = colimIn CC u) :
  identity _ = k.
Proof.
use (uniqueExists (colimUnivProp CC _ _)).
- now apply (colimCocone CC).
- intros v; simpl.
  now apply id_right.
- simpl; now apply H.
Qed.

Definition Cocone_by_postcompose {C : precategory} {g : graph} (D : diagram g C)
 (c : C) (cc : cocone D c) (d : C) (k : C⟦c,d⟧) : cocone D d.
Proof.
exists (λ u, coconeIn cc u · k). red; apply Cocone_postcompose.
Defined.

Lemma isColim_weq_subproof1 {C : precategory} {g : graph} (D : diagram g C)
      (c : C) (cc : cocone D c) (d : C) (k : C⟦c,d⟧) :
  ∏ u, coconeIn cc u · k = coconeIn (Cocone_by_postcompose D c cc d k) u.
Proof.
now intro u.
Qed.

Lemma isColim_weq_subproof2 {C : precategory} (g : graph) (D : diagram g C)
  (c : C) (cc : cocone D c) (H : ∏ d, isweq (Cocone_by_postcompose D c cc d))
  (d : C) (cd : cocone D d) : is_cocone_mor cc cd (invmap (make_weq _ (H d)) cd).
Proof.
intro u.
rewrite (isColim_weq_subproof1 D c cc d (invmap (make_weq _ (H d)) _) u).
set (p := homotweqinvweq (make_weq _ (H d)) cd); simpl in p.
now rewrite p.
Qed.

Lemma isColim_weq {C : category} {g : graph} (D : diagram g C) (c : C) (cc : cocone D c) :
  isColimCocone D c cc <-> ∏ d, isweq (Cocone_by_postcompose D c cc d).
Proof.
split.
- intros H d.
  use isweq_iso.
  + intros k.
    exact (colimArrow (make_ColimCocone D c cc H) _ k).
  + abstract (intro k; simpl;
              now apply pathsinv0, (colimArrowEta (make_ColimCocone D c cc H))).
  + abstract (simpl; intro k;
              apply subtypePath;
                [ intro; now repeat (apply impred; intro); apply C
                | destruct k as [k Hk]; simpl; apply funextsec; intro u;
                  now apply (colimArrowCommutes (make_ColimCocone D c cc H))]).
- intros H d cd.
  use tpair.
  + exists (invmap (make_weq _ (H d)) cd).
    abstract (intro u; now apply isColim_weq_subproof2).
  + abstract (intro t; apply subtypePath;
                [ intro; now apply impred; intro; apply C
                | destruct t as [t Ht]; simpl;
                  apply (invmaponpathsweq (make_weq _ (H d))); simpl;
                  apply subtypePath;
                    [ intro; now repeat (apply impred; intro); apply C
                    | simpl; apply pathsinv0, funextsec; intro u; rewrite Ht;
                      now apply isColim_weq_subproof2]]).
Defined.

Lemma isColim_is_z_iso {C : precategory} {g : graph} (D : diagram g C) (CC : ColimCocone D) (d : C) (cd : cocone D d) :
  isColimCocone D d cd -> is_z_isomorphism (colimArrow CC d cd).
Proof.
intro H.
set (CD := make_ColimCocone D d cd H).
apply (tpair _ (colimArrow (make_ColimCocone D d cd H) (colim CC) (colimCocone CC))).
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

Lemma inv_isColim_is_z_iso {C : precategory} {g : graph} (D : diagram g C) (CC : ColimCocone D) (d : C)
  (cd : cocone D d) (H : isColimCocone D d cd) :
  inv_from_z_iso (_,,isColim_is_z_iso D CC d cd H) =
  colimArrow (make_ColimCocone D d cd H) _ (colimCocone CC).
Proof.
  apply idpath.
Qed.

Lemma is_z_iso_isColim {C : category} {g : graph} (D : diagram g C) (CC : ColimCocone D) (d : C) (cd : cocone D d) :
  is_z_isomorphism (colimArrow CC d cd) -> isColimCocone D d cd.
Proof.
intro H.
set (iinv := z_iso_inv_from_is_z_iso _ H).
intros x cx.
use tpair.
- use tpair.
  + exact (iinv · colimArrow CC x cx).
  + simpl; intro u.
    rewrite <- (colimArrowCommutes CC x cx u), assoc.
    apply cancel_postcomposition, pathsinv0, z_iso_inv_on_left, pathsinv0, colimArrowCommutes.
- intros p; destruct p as [f Hf].
  apply subtypePath.
  + intro a; apply impred; intro u; apply C.
  + simpl; apply pathsinv0, z_iso_inv_on_right; simpl.
    apply pathsinv0, colimArrowUnique; intro u.
    now rewrite <- (Hf u), assoc, colimArrowCommutes.
Defined.

Definition z_iso_from_colim_to_colim {C : precategory} {g : graph} {d : diagram g C}
  (CC CC' : ColimCocone d) : z_iso (colim CC) (colim CC').
Proof.
use make_z_iso.
- apply colimArrow, colimCocone.
- apply colimArrow, colimCocone.
- abstract (now split; apply pathsinv0, colim_endo_is_identity; intro u;
              rewrite assoc, colimArrowCommutes; eapply pathscomp0; try apply colimArrowCommutes).
Defined.

End colim_def.

Section Colims.

Definition Colims (C : category) : UU := ∏ (g : graph) (d : diagram g C), ColimCocone d.
Definition hasColims (C : category) : UU  :=
  ∏ (g : graph) (d : diagram g C), ∥ ColimCocone d ∥.

(** Colimits of a specific shape *)
Definition Colims_of_shape (g : graph) (C : category) : UU :=
  ∏ (d : diagram g C), ColimCocone d.

(** If C is a univalent_category then Colims is a prop *)
Section Universal_Unique.

Variables (C : univalent_category).

Let H : is_univalent C := pr2 C.

Lemma isaprop_Colims: isaprop (Colims C).
Proof.
apply impred; intro g; apply impred; intro cc.
apply invproofirrelevance; intros Hccx Hccy.
apply subtypePath.
- intro; apply isaprop_isColimCocone.
- apply (total2_paths_f (isotoid _ H (z_iso_from_colim_to_colim Hccx Hccy))).
  set (B c := ∏ v, C⟦dob cc v,c⟧).
  set (C' (c : C) f := forms_cocone(c:=c) cc f).
  rewrite (@transportf_total2 _ B C').
  apply subtypePath.
  + intro; repeat (apply impred; intro); apply univalent_category_has_homsets.
  + simpl; eapply pathscomp0; [apply transportf_isotoid_dep''|].
    apply funextsec; intro v.
    now rewrite idtoiso_isotoid; apply colimArrowCommutes.
Qed.

End Universal_Unique.
End Colims.

(** * Defines colimits in functor categories when the target has colimits *)
Section ColimFunctor.

Context {A C : category} {g : graph} (D : diagram g [A, C]).
(* Variable HC : Colims C. *) (* Too strong! *)

Definition diagram_pointwise (a : A) : diagram g C.
Proof.
exists (λ v, pr1 (dob D v) a); intros u v e.
now apply (pr1 (dmor D e) a).
Defined.

Variable (HCg : ∏ (a : A), ColimCocone (diagram_pointwise a)).

Definition ColimFunctor_ob (a : A) : C := colim (HCg a).

Definition ColimFunctor_mor (a a' : A) (f : A⟦a, a'⟧) :
  C⟦ColimFunctor_ob a,ColimFunctor_ob a'⟧.
Proof.
use colimOfArrows.
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

Definition colim_nat_trans_in_data v : [A, C] ⟦ dob D v, ColimFunctor ⟧.
Proof.
use tpair.
- intro a; exact (colimIn (HCg a) v).
- abstract (intros a a' f;
            now apply pathsinv0, (colimOfArrowsIn _ _ (HCg a) (HCg a'))).
Defined.

Definition cocone_pointwise (F : [A,C]) (cc : cocone D F) a :
  cocone (diagram_pointwise a) (pr1 F a).
Proof.
use make_cocone.
- now intro v; apply (pr1 (coconeIn cc v) a).
- abstract (intros u v e;
    now apply (nat_trans_eq_pointwise (coconeInCommutes cc u v e))).
Defined.

Lemma ColimFunctor_unique (F : [A, C]) (cc : cocone D F) :
  iscontr (∑ x : [A, C] ⟦ ColimFunctor, F ⟧,
            ∏ v : vertex g, colim_nat_trans_in_data v · x = coconeIn cc v).
Proof.
use tpair.
- use tpair.
  + apply (tpair _ (λ a, colimArrow (HCg a) _ (cocone_pointwise F cc a))).
    abstract (intros a a' f; simpl;
              eapply pathscomp0;
                [ now apply precompWithColimOfArrows
                | apply pathsinv0; eapply pathscomp0;
                  [ now apply postcompWithColimArrow
                  | apply colimArrowUnique; intro u;
                    eapply pathscomp0;
                      [ now apply colimArrowCommutes
                      | apply pathsinv0; now use nat_trans_ax ]]]).
  + abstract (intro u; apply (nat_trans_eq C); simpl; intro a;
              now apply (colimArrowCommutes (HCg a))).
- abstract (intro t; destruct t as [t1 t2];
            apply subtypePath; simpl;
              [ intro; apply impred; intro u; apply functor_category_has_homsets
              | apply (nat_trans_eq C); simpl; intro a;
                apply colimArrowUnique; intro u;
                now apply (nat_trans_eq_pointwise (t2 u))]).
Defined.

Lemma ColimFunctorCocone : ColimCocone D.
Proof.
use make_ColimCocone.
- exact ColimFunctor.
- use make_cocone.
  + now apply colim_nat_trans_in_data.
  + abstract (now intros u v e; apply (nat_trans_eq C);
                  intro a; apply (colimInCommutes (HCg a))).
- now intros F cc; simpl; apply (ColimFunctor_unique _ cc).
Defined.


Definition isColimFunctor_is_pointwise_Colim
  (X : [A,C]) (R : cocone D X) (H : isColimCocone D X R)
  : ∏ a, isColimCocone (diagram_pointwise a) _ (cocone_pointwise X R a).
Proof.
  intro a.
  apply (is_z_iso_isColim  _ (HCg a)).
  set (XR := isColim_is_z_iso D ColimFunctorCocone X R H).
  apply  (is_functor_z_iso_pointwise_if_z_iso _ _ _ _ _ _ XR).
Defined.

End ColimFunctor.

Lemma ColimsFunctorCategory (A C : category)
  (HC : Colims C) : Colims [A,C].
Proof.
now intros g d; apply ColimFunctorCocone.
Defined.

Lemma ColimsFunctorCategory_of_shape (g : graph) (A C : category)
  (HC : Colims_of_shape g C) : Colims_of_shape g [A,C].
Proof.
now intros d; apply ColimFunctorCocone.
Defined.

Lemma pointwise_Colim_is_isColimFunctor
  {A C : category} {g : graph}
  (d : diagram g [A,C]) (G : [A,C]) (ccG : cocone d G)
  (H : ∏ a, isColimCocone _ _ (cocone_pointwise d G ccG a)) :
  isColimCocone d G ccG.
Proof.
 set (CC a := make_ColimCocone _ _ _ (H a)).
 set (D' := ColimFunctorCocone _ CC).
 use is_z_iso_isColim.
 - apply D'.
 - use tpair.
   + use make_nat_trans.
     * intros a; apply identity.
     * abstract (intros a b f; rewrite id_left, id_right; simpl;
                 apply (colimArrowUnique (CC a)); intro u; cbn;
                 now rewrite <- (nat_trans_ax (coconeIn ccG u))).
   + abstract (split;
               [ apply (nat_trans_eq C); intros x; simpl; rewrite id_right;
                 apply pathsinv0, colimArrowUnique; intros v;
                 now rewrite id_right
               | apply (nat_trans_eq C); intros x; simpl; rewrite id_left;
                 apply pathsinv0, (colimArrowUnique (CC x)); intro u;
                 now rewrite id_right]).
Defined.

Section map.

Context {C D : precategory} (F : functor C D).

Definition mapdiagram {g : graph} (d : diagram g C) : diagram g D.
Proof.
use tpair.
- intros n; apply (F (dob d n)).
- simpl; intros m n e.
  apply (# F (dmor d e)).
Defined.

Definition mapcocone {g : graph} (d : diagram g C) {x : C}
  (dx : cocone d x) : cocone (mapdiagram d) (F x).
Proof.
use make_cocone.
- simpl; intro n.
  exact (#F (coconeIn dx n)).
- abstract (intros u v e; simpl; rewrite <- functor_comp;
            apply maponpaths, (coconeInCommutes dx _ _ e)).
Defined.

Definition preserves_colimit {g : graph} (d : diagram g C) (L : C)
  (cc : cocone d L) : UU :=
  isColimCocone d L cc -> isColimCocone (mapdiagram d) (F L) (mapcocone d cc).

Definition preserves_colimits_of_shape (g : graph) : UU :=
  ∏ (d : diagram g C) (L : C)(cc : cocone d L), preserves_colimit d L cc.

End map.




(** ** Left adjoints preserve colimits *)
Lemma left_adjoint_preserves_colimit {C D : category} (F : functor C D) (HF : is_left_adjoint F)
      {g : graph} (d : diagram g C) (L : C) (ccL : cocone d L) : preserves_colimit F d L ccL.
Proof.
intros HccL M ccM.
set (G := right_adjoint HF).
set (H := pr2 HF : are_adjoints F G).
apply (@iscontrweqb _ (∑ y : C ⟦ L, G M ⟧,
    ∏ i, coconeIn ccL i · y = φ_adj H (coconeIn ccM i))).
- eapply (weqcomp (Y := ∑ y : C ⟦ L, G M ⟧,
    ∏ i, # F (coconeIn ccL i) · φ_adj_inv H y = coconeIn ccM i)).
  + apply (weqbandf (adjunction_hom_weq H L M)); simpl; intro f.
    abstract (apply weqiff; try (apply impred; intro; apply D);
    now rewrite φ_adj_inv_after_φ_adj).
  + eapply (weqcomp (Y := ∑ y : C ⟦ L, G M ⟧,
      ∏ i, φ_adj_inv H (coconeIn ccL i · y) = coconeIn ccM i)).
    * apply weqfibtototal; simpl; intro f.
    abstract (apply weqiff; try (apply impred; intro; apply D); split;
      [ intros HH i; rewrite φ_adj_inv_natural_precomp; apply HH
      | intros HH i; rewrite <- φ_adj_inv_natural_precomp; apply HH ]).
      (* apply weqonsecfibers; intro i. *)
      (* rewrite φ_adj_inv_natural_precomp; apply idweq. *)
    * apply weqfibtototal; simpl; intro f.
    abstract (apply weqiff; [ | apply impred; intro; apply D | apply impred; intro; apply C ];
      split; intros HH i;
        [ now rewrite <- (HH i), φ_adj_after_φ_adj_inv
        | now rewrite (HH i),  φ_adj_inv_after_φ_adj ]).
      (* apply weqonsecfibers; intro i. *)
      (* apply weqimplimpl; [ | | apply hsD | apply hsC]; intro h. *)
      (*   now rewrite <- h, (φ_adj_after_φ_adj_inv _ _ _ H). *)
      (* now rewrite h, (φ_adj_inv_after_φ_adj _ _ _ H). *)
- transparent assert (X : (cocone d (G M))).
  { use make_cocone.
    + intro v; apply (φ_adj H (coconeIn ccM v)).
    + abstract (intros m n e; simpl;
                rewrite <- (coconeInCommutes ccM m n e); simpl;
                now rewrite φ_adj_natural_precomp).
  }
  apply (HccL (G M) X).
Defined.



Section mapcocone_functor_composite.

Context {A B C : category}
        (F : functor A B) (G : functor B C).

Lemma mapcocone_functor_composite {g : graph} {D : diagram g A} {a : A} (cc : cocone D a) :
  mapcocone (functor_composite F G) _ cc = mapcocone G _ (mapcocone F _ cc).
Proof.
  apply subtypePath.
  - intros x. repeat (apply impred_isaprop; intro). apply C.
  - reflexivity.
Qed.

End mapcocone_functor_composite.

(**
 Some functions to construct morphisms using colimits
 *)
Definition colim_mor
           {C : category}
           {G : graph}
           {D : diagram G C}
           (c : ColimCocone D)
           (y : C)
           (g : ∏ (v : vertex G), dob D v --> y)
           (p : forms_cocone D g)
  : colim c --> y
  := pr11 (pr2 c y (make_cocone g p)).

Definition colim_mor_commute
           {C : category}
           {G : graph}
           {D : diagram G C}
           (c : ColimCocone D)
           (y : C)
           (g : ∏ (v : vertex G), dob D v --> y)
           (p : forms_cocone D g)
           (v : vertex G)
  : colimIn c v · colim_mor c y g p = g v
  := pr21 (pr2 c y (make_cocone g p)) v.

Definition colim_mor_eq
           {C : category}
           {G : graph}
           {D : diagram G C}
           (c : ColimCocone D)
           (y : C)
           {f₁ f₂ : colim c --> y}
           (H : ∏ (v : vertex G), colimIn c v · f₁ = colimIn c v · f₂)
  : f₁ = f₂.
Proof.
  assert (forms_cocone D (λ v : vertex G, colimIn c v · f₂)) as Hf₂.
  {
    unfold forms_cocone.
    cbn.
    unfold dmor.
    intros.
    rewrite !assoc.
    apply maponpaths_2.
    apply colimInCommutes.
  }
  pose (pr2 (pr2 c y (make_cocone (λ v, colimIn c v · f₂) Hf₂)) (f₁ ,, H)) as p.
  refine (maponpaths pr1 p @ _).
  pose (pr2 (pr2 c y (make_cocone (λ v, colimIn c v · f₂) Hf₂)) (f₂ ,, λ _, idpath _)) as q.
  exact (!(maponpaths pr1 q)).
Qed.

Section ConnectedGraphs.

Definition graph_zig_zag_of_length
           {g : graph}
           (n : nat)
  : ∏ (x y : vertex g), UU.
Proof.
  induction n as [ | n IHn ].
  - exact (λ x y, x = y).
  - exact (λ x y, ∑ (z : vertex g), ((edge x z) ⨿ (edge z x)) × IHn z y).
Defined.

Definition graph_zig_zag
          {g : graph}
          (x y : vertex g)
  : UU
  := ∑ (n : nat), graph_zig_zag_of_length n x y.

Definition length_of_graph_zig_zag
           {g : graph}
           {x y : vertex g}
           (gs : graph_zig_zag x y)
  : nat
  := pr1 gs.

Definition empty_graph_zig_zag
           {g : graph}
           (x : vertex g)
  : graph_zig_zag x x
  := 0 ,, idpath x.

Definition left_cons_graph_zig_zag
           {g : graph}
           {x z y : vertex g}
           (f : edge x z)
           (gs : graph_zig_zag z y)
  : graph_zig_zag x y
  := 1 + length_of_graph_zig_zag gs ,, (z ,, (inl f ,, pr2 gs)).

Definition right_cons_graph_zig_zag
           {g : graph}
           {x z y : vertex g}
           (f : edge z x)
           (gs : graph_zig_zag z y)
  : graph_zig_zag x y
  := 1 + length_of_graph_zig_zag gs ,, (z ,, (inr f ,, pr2 gs)).

Definition append_graph_zig_zag_of_length
           {g : graph}
           {n m : nat}
           {x y z : vertex g}
           (fs : graph_zig_zag_of_length n x y)
           (gs : graph_zig_zag_of_length m y z)
  : graph_zig_zag_of_length (n + m) x z.
Proof.
  revert x y z fs gs.
  induction n as [ | n IHn ].
  - intros x y z fs gs.
    rewrite fs.
    exact gs.
  - intros x y z fs gs.
    induction fs as [ w fs ].
    induction fs as [ f fs ].
    induction f as [ f | f ].
    + exact (w ,, inl f ,, IHn w y z fs gs).
    + exact (w ,, inr f ,, IHn w y z fs gs).
Defined.

Definition append_graph_zig_zag
           {g : graph}
           {x y z : vertex g}
           (fs : graph_zig_zag x y)
           (gs : graph_zig_zag y z)
  : graph_zig_zag x z
  := length_of_graph_zig_zag fs + length_of_graph_zig_zag gs
     ,,
     append_graph_zig_zag_of_length (pr2 fs) (pr2 gs).

(**
 5. Reversing zig-zags
 *)
Definition post_cons_left_graph_zig_zag_of_length
           {g : graph}
           {n : nat}
           {x y z : vertex g}
           (gs : graph_zig_zag_of_length n x y)
           (f : edge y z)
  : graph_zig_zag_of_length (S n) x z.
Proof.
  revert x y z gs f.
  induction n as [ | n IHn ].
  - intros x y z gs f.
    exists z.
    split.
    * rewrite <- gs in f.
      exact (inl f).
    * reflexivity.
  - intros x y z gs f.
    induction gs as [ w gs ].
    induction gs as [ g' gs ].
    induction g' as [ g' | g' ].
    + exact (w ,, inl g' ,, IHn _ _ _ gs f).
    + exact (w ,, inr g' ,, IHn _ _ _ gs f).
Defined.

Definition post_cons_right_graph_zig_zag_of_length
           {g : graph}
           {n : nat}
           {x y z : vertex g}
           (gs : graph_zig_zag_of_length n x y)
           (f : edge z y)
  : graph_zig_zag_of_length (S n) x z.
Proof.
  revert x y z gs f.
  induction n as [ | n IHn ].
  - intros x y z gs f.
    exists z.
    split.
    * rewrite <- gs in f.
      exact (inr f).
    * reflexivity.
  - intros x y z gs f.
    induction gs as [ w gs ].
    induction gs as [ g' gs ].
    induction g' as [ g' | g' ].
    + exact (w ,, inl g' ,, IHn _ _ _ gs f).
    + exact (w ,, inr g' ,, IHn _ _ _ gs f).
Defined.

Definition reverse_graph_zig_zag_of_length
           {g : graph}
           {n : nat}
           {x y : vertex g}
           (gs : graph_zig_zag_of_length n x y)
  : graph_zig_zag_of_length n y x.
Proof.
  revert x y gs.
  induction n as [ | n IHn ].
  - intros x y gs.
    exact (pathsinv0 gs).
  - intros x y gs.
    induction gs as [ z gs ].
    induction gs as [ g' gs ].
    induction g' as [ g' | g' ].
    + exact (post_cons_right_graph_zig_zag_of_length (IHn _ _ gs) g').
    + exact (post_cons_left_graph_zig_zag_of_length (IHn _ _ gs) g').
Defined.

Definition reverse_graph_zig_zag
           {g : graph}
           {x y : vertex g}
           (gs : graph_zig_zag x y)
  : graph_zig_zag y x
  := length_of_graph_zig_zag gs ,, reverse_graph_zig_zag_of_length (pr2 gs).

(* this assumes the induction hypothesis for all 
   edges, not just those in the path *)
Lemma graph_zig_zag_strong_induction_helper 
    {g : graph}
    {P : vertex g -> UU} :
  ∏ n, ∏ (x y : vertex g), 
      (P x) -> 
      (∏ (a b : vertex g), P a -> (edge a b ⨿ edge b a) -> P b) -> 
      graph_zig_zag_of_length n x y -> 
      P y.
Proof.
  intro n.
  induction n as [|n Hn].
  - intros x y Hx _ gs.
    now rewrite <- gs.
  - intros x y Hx eind gs.
    destruct gs as [z [xz gs]].
    use (Hn _ _ _ eind gs).
    exact (eind x z Hx xz).
Defined.

Lemma graph_zig_zag_strong_induction 
    {g : graph}
    {x y : vertex g}
    (gs : graph_zig_zag x y) :
  ∏ (P : vertex g -> UU),
    (P x) ->
    (∏ (a b : vertex g), P a -> (edge a b ⨿ edge b a) -> P b) ->
  P y.
Proof.
  intros P Hx Hind.
  destruct gs as [n gs].
  use graph_zig_zag_strong_induction_helper.
  - exact n.
  - exact x.
  - exact Hx.
  - exact Hind.
  - exact gs.
Defined.

Definition is_connected (g : graph) : UU :=
    ∏ (v1 v2 : vertex g), graph_zig_zag v1 v2.

Lemma connected_graph_zig_zag_strong_induction 
    {g : graph}
    (x : vertex g)
    {y : vertex g}
    (H : is_connected g) :
  ∏ (P : vertex g -> UU),
    (P x) ->
    (∏ (a b : vertex g), P a -> (edge a b ⨿ edge b a) -> P b) ->
  P y.
Proof.
  apply graph_zig_zag_strong_induction.
  apply H.
Defined.

Lemma connected_graph_zig_zag_strong_induction_symmetric
    {g : graph}
    (x : vertex g)
    {y : vertex g}
    (H : is_connected g)
    (P : vertex g -> UU)
    (Hsymm : ∏ [a b : vertex g], edge b a -> (edge a b -> P b) -> P b) :
  (P x) ->
    (∏ (a b : vertex g), P a -> edge a b -> P b) ->
  P y.
Proof.
  intros Px IHn.
  apply (connected_graph_zig_zag_strong_induction x H P Px).
  intros a b Pa e.
  destruct e.
  - apply (IHn a b Pa e).
  - apply (Hsymm a b e).
    intro e'.
    apply (IHn a b Pa e').
Defined.

Lemma is_connected_pointed (g : graph) (v0 : vertex g) :
    (∏ (v : vertex g), graph_zig_zag v0 v) ->
        is_connected g.
Proof.
  intro H.
  intros v1 v2.
  use (append_graph_zig_zag (y := v0)).
  - exact (reverse_graph_zig_zag (H v1)).
  - exact (H v2).
Defined.

End ConnectedGraphs.