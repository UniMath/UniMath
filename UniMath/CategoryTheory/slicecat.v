(** **********************************************************

Anders Mörtberg, Benedikt Ahrens, 2015-2016

*************************************************************)

(** **********************************************************

Contents:

- Definition of slice precategories, C/x (assumes that C has homsets)

- Proof that C/x is a category if C is

- Proof that any morphism C[x,y] induces a functor from C/x to C/y

- Colimits in slice categories ([slice_precat_colims])

************************************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.UnicodeNotations.

(** * Definition of slice categories *)
(** Given a category C and x : obj C. The slice category C/x is given by:

- obj C/x: pairs (a,f) where f : a -> x

- morphism (a,f) -> (b,g): morphism h : a -> b with
<<
           h
       a - - -> b
       |       /
       |     /
     f |   / g
       | /
       v
       x
>>
    where h ;; g = f

*)
Section slice_precat_def.

Variable C : precategory.
Variable x : C.

Definition slicecat_ob := total2 (fun (a : C) => a --> x).
Definition slicecat_mor (f g : slicecat_ob) :=
  total2 (fun h : pr1 f --> pr1 g => pr2 f = h ;; pr2 g).

Definition slice_precat_ob_mor : precategory_ob_mor :=
  tpair _ _ slicecat_mor.

Definition id_slice_precat (c : slice_precat_ob_mor) : c --> c :=
  tpair _ _ (!(id_left (pr2 c))).

Definition comp_slice_precat_subproof (a b c : slice_precat_ob_mor)
  (f : a --> b) (g : b --> c) : pr2 a = (pr1 f ;; pr1 g) ;; pr2 c.
Proof.
rewrite <- assoc, (!(pr2 g)).
exact (pr2 f).
Qed.

Definition comp_slice_precat (a b c : slice_precat_ob_mor)
                             (f : a --> b) (g : b --> c) : a --> c :=
  tpair _ (pr1 f ;; pr1 g) (comp_slice_precat_subproof _ _ _ _ _).

Definition slice_precat_data : precategory_data :=
  precategory_data_pair _ id_slice_precat comp_slice_precat.

Lemma is_precategory_slice_precat_data (hsC : has_homsets C) :
  is_precategory slice_precat_data.
Proof.
repeat split; simpl.
* intros a b f.
  case f; clear f; intros h hP.
  apply subtypePairEquality; [ intro; apply hsC | apply id_left ].
* intros a b f.
  case f; clear f; intros h hP.
  apply subtypePairEquality; [ intro; apply hsC | apply id_right ].
* intros a b c d f g h.
  apply subtypePairEquality; [ intro; apply hsC | apply assoc ].
Qed.

Definition slice_precat (hsC : has_homsets C) : precategory :=
  tpair _ _ (is_precategory_slice_precat_data hsC).


End slice_precat_def.

Section slice_precat_theory.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable x : C.

Local Notation "C / X" := (slice_precat C X hsC).

Lemma has_homsets_slice_precat : has_homsets (C / x).
Proof.
intros a b.
case a; clear a; intros a f; case b; clear b; intros b g; simpl.
apply (isofhleveltotal2 2); [ apply hsC | intro h].
apply isasetaprop; apply hsC.
Qed.

Lemma eq_mor_slicecat (af bg : C / x) (f g : af --> bg) : pr1 f = pr1 g -> f = g.
Proof. intro heq; apply (total2_paths heq); apply hsC. Qed.

Lemma eq_iso_slicecat (af bg : C / x) (f g : iso af bg) : pr1 f = pr1 g -> f = g.
Proof.
case g; case f; clear f g; simpl; intros f fP g gP eq.
refine (subtypePairEquality _ eq).
intro.
apply isaprop_is_iso.
Qed.

(** It suffices that the underlying morphism is an iso to get an iso in
    the slice category *)
Lemma iso_to_slice_precat_iso (af bg : C / x) (h : af --> bg)
  (isoh : is_iso (pr1 h)) : is_iso h.
Proof.
case (is_z_iso_from_is_iso _ isoh).
intros hinv hinvP; case hinvP; clear hinvP; intros h1 h2.
assert (pinv : hinv ;; pr2 af = pr2 bg).
  rewrite <- id_left, <- h2, <- assoc, (!(pr2 h)).
  apply idpath.
apply is_iso_from_is_z_iso.
exists (tpair _ hinv (!(pinv))).
split; ( apply subtypePairEquality ; [ intro; apply hsC | trivial ]).
Qed.

(** An iso in the slice category gives an iso in the base category *)
Lemma slice_precat_iso_to_iso  (af bg : C / x) (h : af --> bg)
  (p : is_iso h) : is_iso (pr1 h).
Proof.
case (is_z_iso_from_is_iso _ p); intros hinv hinvP.
case hinvP; clear hinvP; intros h1 h2.
apply is_iso_from_is_z_iso.
exists (pr1 hinv); split.
  apply (maponpaths pr1 h1).
apply (maponpaths pr1 h2).
Qed.

Lemma iso_weq (af bg : C / x) :
  weq (iso af bg) (total2 (fun h : iso (pr1 af) (pr1 bg) => pr2 af = h ;; pr2 bg)).
Proof.
apply (weqcomp (weqtotal2asstor _ _)).
apply invweq.
apply (weqcomp (weqtotal2asstor _ _)).
apply weqfibtototal; intro h; simpl.
apply (weqcomp (weqdirprodcomm _ _)).
apply weqfibtototal; intro p.
apply weqimplimpl; try apply isaprop_is_iso.
  intro hp; apply iso_to_slice_precat_iso; assumption.
intro hp; apply (slice_precat_iso_to_iso _ _ _ hp).
Defined.

(** The forgetful functor from C/x to C *)
Definition slicecat_to_cat : functor (C / x) C.
Proof.
mkpair.
+ mkpair.
  - apply pr1.
  - intros a b; apply pr1.
+ abstract (now split).
Defined.

End slice_precat_theory.

(** * Proof that C/x is a category if C is. *)
(** This is exercise 9.1 in the HoTT book *)
Section slicecat_theory.

Variable C : precategory.
Variable is_catC : is_category C.
Variable x : C.

Local Notation "C / x" := (slice_precat C x (pr2 is_catC)).

Lemma id_weq_iso_slicecat (af bg : C / x) : weq (af = bg) (iso af bg).
Proof.
set (a := pr1 af); set (f := pr2 af); set (b := pr1 bg); set (g := pr2 bg).

assert (weq1 : weq (af = bg)
                   (total2 (fun (p : a = b) => transportf _ p (pr2 af) = g))).
  apply (total2_paths_equiv _ af bg).

assert (weq2 : weq (total2 (fun (p : a = b) => transportf _ p (pr2 af) = g))
                   (total2 (fun (p : a = b) => idtoiso (! p) ;; f = g))).
  apply weqfibtototal; intro p.
  rewrite idtoiso_precompose.
  apply idweq.

assert (weq3 : weq (total2 (fun (p : a = b) => idtoiso (! p) ;; f = g))
                   (total2 (fun h : iso a b => f = h ;; g))).
  apply (weqbandf (weqpair _ ((pr1 is_catC) a b))); intro p.
  rewrite idtoiso_inv; simpl.
  apply weqimplimpl; simpl; try apply (pr2 is_catC); intro Hp.
    rewrite <- Hp, assoc, iso_inv_after_iso, id_left; apply idpath.
  rewrite Hp, assoc, iso_after_iso_inv, id_left; apply idpath.

assert (weq4 : weq (total2 (fun h : iso a b => f = h ;; g)) (iso af bg)).
  apply invweq; apply iso_weq.

apply (weqcomp weq1 (weqcomp weq2 (weqcomp weq3 weq4))).
Defined.

Lemma is_category_slicecat : is_category (C / x).
Proof.
split; [| apply has_homsets_slice_precat]; simpl; intros a b.
set (h := id_weq_iso_slicecat a b).
apply (isweqhomot h); [intro p|case h; trivial].
destruct p.
apply eq_iso.
apply eq_mor_slicecat; trivial.
Qed.

End slicecat_theory.

(** * A morphism x --> y in the base category induces a functor between C/x and C/y *)
Section slicecat_functor_def.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable x y : C.
Variable f : x --> y.

Local Notation "C / X" := (slice_precat C X hsC).

Definition slicecat_functor_ob (af : C / x) : C / y :=
  tpair _ (pr1 af) (pr2 af ;; f).

Lemma slicecat_functor_subproof (af bg : C / x) (h : af --> bg) :
  pr2 af ;; f = pr1 h ;; (pr2 bg ;; f).
Proof. rewrite assoc, (!(pr2 h)); apply idpath. Qed.

Definition slicecat_functor_data : functor_data (C / x) (C / y) :=
  tpair (fun F => Π a b, a --> b -> F a --> F b)
        slicecat_functor_ob
        (fun a b h => tpair _ (pr1 h) (slicecat_functor_subproof _ _ h)).

Lemma is_functor_slicecat_functor : is_functor slicecat_functor_data.
Proof.
split.
  intros a; apply eq_mor_slicecat; apply idpath.
intros a b c g h; apply eq_mor_slicecat; apply idpath.
Qed.

Definition slicecat_functor : functor (C / x) (C / y) :=
  tpair _ _ is_functor_slicecat_functor.

End slicecat_functor_def.

Section slicecat_functor_theory.

Variable C : precategory.
Variable hsC : has_homsets C.

Local Notation "C / X" := (slice_precat C X hsC).

Lemma slicecat_functor_identity_ob (x : C) :
  slicecat_functor_ob C hsC x x (identity x) = functor_identity (C / x).
Proof.
apply funextsec; intro af.
unfold slicecat_functor_ob.
now rewrite id_right, tppr.
Defined.

Lemma slicecat_functor_identity (x : C) :
  slicecat_functor _ _ _ _ (identity x) = functor_identity (C / x).
Proof.
apply (functor_eq _ _ (has_homsets_slice_precat _ _ _)); simpl.
apply (total2_paths2 (slicecat_functor_identity_ob _)).
apply funextsec; intros [a f].
apply funextsec; intros [b g].
apply funextsec; intros [h hh].
rewrite transport_of_functor_map_is_pointwise; simpl in *.
unfold slicecat_mor.
rewrite transportf_total2.
apply subtypePairEquality; [intro; apply hsC | ].
rewrite transportf_total2; simpl.
unfold slicecat_functor_identity_ob.
rewrite toforallpaths_funextsec; simpl.
case (id_right f).
now case (id_right g).
Qed.

Lemma slicecat_functor_comp_ob (x y z : C) (f : x --> y) (g : y --> z) :
  slicecat_functor_ob C hsC x z (f ;; g) =
       (fun a : slicecat_ob C x =>
        slicecat_functor_ob C hsC y z g (slicecat_functor_ob C hsC x y f a)).
Proof.
apply funextsec; intro af.
now unfold slicecat_functor_ob; rewrite assoc.
Defined.

(* This proof is not so nice... *)
Lemma slicecat_functor_comp (x y z : C) (f : x --> y) (g : y --> z) :
  slicecat_functor _ hsC _ _ (f ;; g) =
  functor_composite (slicecat_functor _ _ _ _ f) (slicecat_functor _ _ _ _ g).
Proof.
apply (functor_eq _ _ (has_homsets_slice_precat _ _ _)); simpl.
unfold slicecat_functor_data; simpl.
unfold functor_composite_data; simpl.
apply (total2_paths2 (slicecat_functor_comp_ob _ _ _ _ _)).
apply funextsec; intros [a fax].
apply funextsec; intros [b fbx].
apply funextsec; intros [h hh].
rewrite transport_of_functor_map_is_pointwise; simpl in *.
unfold slicecat_mor.
rewrite transportf_total2.
apply subtypePairEquality; [intro; apply hsC | ].
rewrite transportf_total2; simpl.
unfold slicecat_functor_comp_ob.
rewrite toforallpaths_funextsec; simpl.
assert (H1 : transportf (fun x : C / z => pr1 x --> b)
               (Basics.PartA.internal_paths_rew_r _ _ _
                 (fun p => tpair _ a p = tpair _ a _) (idpath (tpair _ a _))
                 (assoc fax f g)) h = h).
  case (assoc fax f g); apply idpath.
assert (H2 : Π h', h' = h ->
             transportf (fun x : C / z => a --> pr1 x)
                        (Basics.PartA.internal_paths_rew_r _ _ _
                           (fun p => tpair _ b p = tpair _ b _) (idpath _)
                           (assoc fbx f g)) h' = h).
  intros h' eq.
  case (assoc fbx f g); rewrite eq; apply idpath.
now apply H2.
Qed.

End slicecat_functor_theory.

(** * Colimits in slice categories *)
Section slicecat_colimits.

Context (g : graph) {C : precategory} (hsC : has_homsets C) (x : C).

Local Notation "C / X" := (slice_precat C X hsC).

(* I think that this lemma would be better stated by saying that the forgetful functor *)
(* `slicecat_to_cat' creates limits, that is, by saying that, given a diagram in C/X and a cocone CC *)
(* under that diagram, then CC is colimiting if the image of CC under the forgetful functor is. *)

Let U : functor (C / x) C := slicecat_to_cat C hsC x.

Lemma slice_precat_isColimCocone (d : diagram g (C / x)) (a : C / x)
  (cc : cocone d a)
  (H : isColimCocone (mapdiagram U d) (U a) (mapcocone U d cc)) :
  isColimCocone d a cc.
Proof.
set (CC := mk_ColimCocone _ _ _ H).
intros y ccy.
  use unique_exists.
  + mkpair; simpl.
    * apply (colimArrow CC), (mapcocone U _ ccy).
    *
apply pathsinv0.
eapply pathscomp0.
apply (postcompWithColimArrow _ CC (pr1 y) (mapcocone U d ccy)).
apply pathsinv0.
apply (colimArrowUnique CC).
intros u.
simpl.
unfold colimIn.
simpl.
eapply pathscomp0.
apply (!(pr2 (coconeIn cc u))).
apply (pr2 (coconeIn ccy u)).
+ intros u.
apply subtypeEquality.
intros xx.
apply hsC.
simpl.
apply (colimArrowCommutes CC).
+ intros f; simpl; apply impred; intro u; apply has_homsets_slice_precat.
+ intros f; simpl; intros Hf.
apply eq_mor_slicecat; simpl.
apply (colimArrowUnique CC); intro u.
cbn.
rewrite <- (Hf u).
apply idpath.
Defined.



Lemma slice_precat_ColimCocone (d : diagram g (C / x))
  (H : ColimCocone (mapdiagram U d)) :
  ColimCocone d.
Proof.
use mk_ColimCocone.
- mkpair.
  + apply (colim H).
  + apply colimArrow.
    use mk_cocone.
    * intro v; apply (pr2 (dob d v)).
    * abstract (intros u v e; apply (! pr2 (dmor d e))).
- use mk_cocone.
  + intro v; simpl.
    mkpair; simpl.
    * apply (colimIn H v).
    * abstract (apply pathsinv0, (colimArrowCommutes H)).
  + abstract (intros u v e; apply eq_mor_slicecat, (coconeInCommutes (colimCocone H))).
- intros y ccy.
  use unique_exists.
  + mkpair; simpl.
    * apply colimArrow, (mapcocone U _ ccy).
    * abstract (apply pathsinv0, colimArrowUnique; intros v; simpl; rewrite assoc;
                eapply pathscomp0;
                  [apply cancel_postcomposition,
                        (colimArrowCommutes H _ (mapcocone U _ ccy) v)|];
                destruct ccy as [f Hf]; simpl; apply (! pr2 (f v))).
  + abstract (intro v; apply eq_mor_slicecat; simpl;
              apply (colimArrowCommutes _ _ (mapcocone U d ccy))).
  + abstract (simpl; intros f; apply impred; intro v; apply has_homsets_slice_precat).
  + abstract (intros f Hf; apply eq_mor_slicecat; simpl in *; apply colimArrowUnique;
              intros v; apply (maponpaths pr1 (Hf v))).
Defined.

Lemma slice_precat_colims_of_shape (CC : Colims_of_shape g C) : Colims_of_shape g (C / x).
Proof.
now intros d; apply slice_precat_ColimCocone, CC.
Defined.

End slicecat_colimits.

Lemma slice_precat_colims {C : precategory} (hsC : has_homsets C) (x : C) (CC : Colims C) :
  Colims (slice_precat C x hsC).
Proof.
now intros g d; apply slice_precat_ColimCocone, CC.
Defined.
