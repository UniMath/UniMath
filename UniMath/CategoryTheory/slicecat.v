(** **********************************************************

Anders Mörtberg, Benedikt Ahrens

*************************************************************)

(** **********************************************************

Contents: Definition of slice precategories, C/x (assumes
            that C has homsets)

          Proof that C/x is a category if C is

          Proof that any morphism x --> y induces a functor
            from C/x to C/y

************************************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50, left associativity).
Local Notation "f ;; g"  := (compose f g) (at level 50, format "f  ;;  g").

(* Slice category:

Given a category C and x : obj C. The slice category C/x is given by:

- obj C/x: pairs (a,f) where f : a -> x

- morphism (a,f) -> (b,g): morphism h : a -> b with

           h
       a - - -> b
       |       /
       |     /
     f |   / g
       | /
       v
       x

    where h ;; g = f

*)
Section slice_precat_def.

Variable C : precategory.
Variable x : C.

Definition slicecat_ob := total2 (fun (a : C) => a --> x).
Definition slicecat_mor (f g : slicecat_ob) :=
  total2 (fun h : pr1 f --> pr1 g => h ;; pr2 g = pr2 f).

Definition slice_precat_ob_mor : precategory_ob_mor :=
  tpair _ _ slicecat_mor.

Definition id_slice_precat (c : slice_precat_ob_mor) : c --> c :=
  tpair _ _ (id_left (pr2 c)).

Definition comp_slice_precat_subproof (a b c : slice_precat_ob_mor)
  (f : a --> b) (g : b --> c) : (pr1 f ;; pr1 g) ;; pr2 c = pr2 a.
Proof.
rewrite <- assoc, (pr2 g).
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

(* It suffices that the underlying morphism is an iso to get an iso in
   the slice category *)
Lemma iso_to_slice_precat_iso (af bg : C / x) (h : af --> bg)
  (isoh : is_iso (pr1 h)) : is_iso h.
Proof.
case (is_z_iso_from_is_iso _ isoh).
intros hinv hinvP; case hinvP; clear hinvP; intros h1 h2.
assert (pinv : hinv ;; pr2 af = pr2 bg).
  rewrite <- id_left, <- h2, <- assoc, (pr2 h).
  apply idpath.
apply is_iso_from_is_z_iso.
exists (tpair _ hinv pinv).
split; ( apply subtypePairEquality ; [ intro; apply hsC | trivial ]).
Qed.

(* An iso in the slice category gives an iso in the base category *)
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
  weq (iso af bg) (total2 (fun h : iso (pr1 af) (pr1 bg) => h ;; pr2 bg = pr2 af)).
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

End slice_precat_theory.

(* Proof that C/x is a category if C is. This is exercise 9.1 in the
   HoTT book *)
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
                   (total2 (fun h : iso a b => h ;; g = f))).
  apply (weqbandf (weqpair _ ((pr1 is_catC) a b))); intro p.
  rewrite idtoiso_inv; simpl.
  apply weqimplimpl; simpl; try apply (pr2 is_catC); intro Hp.
    rewrite <- Hp, assoc, iso_inv_after_iso, id_left; apply idpath.
  rewrite <- Hp, assoc, iso_after_iso_inv, id_left; apply idpath.

assert (weq4 : weq (total2 (fun h : iso a b => h ;; g = f)) (iso af bg)).
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

(* Any morphism x --> y in the base category induces a functor between
   the slice categories C/x and C/y *)
Section slicecat_functor_def.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable x y : C.
Variable f : x --> y.

Local Notation "C / X" := (slice_precat C X hsC).

Definition slicecat_functor_ob (af : C / x) : C / y :=
  tpair _ (pr1 af) (pr2 af ;; f).

Lemma slicecat_functor_subproof (af bg : C / x) (h : af --> bg) :
  pr1 h ;; (pr2 bg ;; f) = pr2 af ;; f.
Proof. rewrite assoc, (pr2 h); apply idpath. Qed.

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
rewrite id_right, tppr.
apply idpath.
Defined.

Lemma slicecat_functor_identity (x : C) :
  slicecat_functor _ _ _ _ (identity x) = functor_identity (C / x).
Proof.
apply (functor_eq _ _ (has_homsets_slice_precat _ _ _)); simpl.
apply (total2_paths2 (slicecat_functor_identity_ob _)).
apply funextsec; intro a; case a; clear a; intros a f.
apply funextsec; intro b; case b; clear b; intros b g.
apply funextsec; intro h; case h; clear h; intros h hh.
rewrite transport_of_functor_map_is_pointwise; simpl in *.
unfold slicecat_mor.
rewrite transportf_total2.
apply subtypePairEquality; [intro; apply hsC | ].
rewrite transportf_total2; simpl.
unfold slicecat_functor_identity_ob.
rewrite toforallpaths_funextsec; simpl.
case (id_right f).
case (id_right g).
apply idpath.
Qed.

Lemma slicecat_functor_comp_ob (x y z : C) (f : x --> y) (g : y --> z) :
  slicecat_functor_ob C hsC x z (f ;; g) =
       (fun a : slicecat_ob C x =>
        slicecat_functor_ob C hsC y z g (slicecat_functor_ob C hsC x y f a)).
Proof.
apply funextsec; intro af.
unfold slicecat_functor_ob; simpl.
rewrite assoc; apply idpath.
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
apply funextsec; intro a; case a; clear a; intros a fax.
apply funextsec; intro b; case b; clear b; intros b fbx.
apply funextsec; intro h; case h; clear h; intros h hh.
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
apply H2.
assumption.
Qed.

End slicecat_functor_theory.
