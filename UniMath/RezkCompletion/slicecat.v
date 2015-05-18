(** Definition of slice categories C/X and proof that if C is a
    category then C/X is also a category *)
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.

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
Section slicecat_def.

Variable C : precategory.
Variable x : ob C.

Definition slicecat_ob := total2 (fun (a : C) => a --> x).
Definition slicecat_mor (f g : slicecat_ob) :=
  total2 (fun h : pr1 f --> pr1 g => h ;; pr2 g = pr2 f).

Definition slice_precat_ob_mor : precategory_ob_mor :=
  tpair _ _ slicecat_mor.

Definition id_slice_precat (c : slice_precat_ob_mor) : c --> c :=
  tpair _ _ (id_left _ _ _ (pr2 c)).

Definition comp_slice_precat (a b c : slice_precat_ob_mor)
                             (f : a --> b) (g : b --> c) : a --> c.
Proof.
apply (tpair _ (pr1 f ;; pr1 g)).
rewrite <- assoc, (pr2 g).
exact (pr2 f).
Defined.

Definition slice_precat_data : precategory_data :=
  precategory_data_pair _ id_slice_precat comp_slice_precat.

Lemma is_precategory_slice_precat_data (hsC : has_homsets C) :
  is_precategory slice_precat_data.
Proof.
repeat split; simpl.
* intros a b f.
  case f; clear f; intros h hP.
  apply total2_paths2_second_isaprop; [ apply id_left | apply hsC ].
* intros a b f.
  case f; clear f; intros h hP.
  apply total2_paths2_second_isaprop; [ apply id_right | apply hsC ].
* intros a b c d f g h.
  apply total2_paths2_second_isaprop; [ apply assoc | apply hsC ].
Qed.

Definition slice_precat (hsC : has_homsets C) : precategory :=
  tpair _ _ (is_precategory_slice_precat_data hsC).

Lemma has_homsets_slice_precat (hsC : has_homsets C) :
  has_homsets (slice_precat hsC).
Proof.
intros a b.
case a; clear a; intros a f; case b; clear b; intros b g; simpl.
unfold slicecat_mor; simpl.
change (isaset (total2 (fun h => h ;; g = f))) with
        (isofhlevel (S (S O)) (total2 (fun h => h ;; g = f))).
apply isofhleveltotal2; [ apply hsC | intro h].
apply isasetaprop; apply hsC.
Qed.

(* It suffices that the underlying morphism is an iso to get an iso in
   the slice category *)
Lemma iso_to_slicecat_iso (hsC : has_homsets C) (af bg : slice_precat hsC)
                          (h : af --> bg) (isoh : is_iso (pr1 h)) :
                          is_iso h.
Proof.
case (is_z_iso_from_is_iso _ isoh).
intros hinv hinvP; case hinvP; clear hinvP; intros h1 h2.
assert (pinv : hinv ;; pr2 af = pr2 bg).
  rewrite <- id_left, <- h2, <- assoc, (pr2 h).
  apply idpath.
apply is_iso_from_is_z_iso.
exists (tpair _ hinv pinv).
split; apply total2_paths2_second_isaprop; try assumption; apply hsC.
Qed.

(* An iso in the slice category gives an iso in the base category *)
Lemma slicecat_iso_to_iso (hsC : has_homsets C) (af bg : slice_precat hsC)
      (h : af --> bg) (p : is_iso h) : is_iso (pr1 h).
Proof.
case (is_z_iso_from_is_iso _ p); intros hinv hinvP.
case hinvP; clear hinvP; intros h1 h2.
apply is_iso_from_is_z_iso.
exists (pr1 hinv); split.
  apply (identity_congr pr1 h1).
apply (identity_congr pr1 h2).
Qed.

Lemma iso_weq (hsC : has_homsets C) (af bg : slice_precat hsC) :
  weq (iso af bg) (total2 (fun h : iso (pr1 af) (pr1 bg) => h ;; pr2 bg = pr2 af)).
Proof.
apply (weqcomp (weqtotal2asstor _ _)).
apply invweq.
apply (weqcomp (weqtotal2asstor _ _)).
apply weqfibtototal; intro h; simpl.
apply (weqcomp (weqdirprodcomm _ _)).
apply weqfibtototal; intro p.
apply weqimplimpl; try apply isaprop_is_iso.
  intro hp; apply (iso_to_slicecat_iso hsC); assumption.
intro hp; apply (slicecat_iso_to_iso hsC _ _ _ hp).
Defined.

Lemma id_weq_iso_slicecat (is_catC : is_category C)
  (af bg : slice_precat (pr2 is_catC)) : weq (af = bg) (iso af bg).
Proof.
set (a := pr1 af); set (f := pr2 af); set (b := pr1 bg); set (g := pr2 bg).
case is_catC; simpl; intros h_univ h_homsets; simpl in *.

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
  apply (weqbandf (weqpair _ (h_univ a b))); intro p.
  rewrite idtoiso_inv; simpl.
  apply weqimplimpl; simpl; try apply h_homsets; intro Hp.
    rewrite <- Hp, assoc, iso_inv_after_iso, id_left; apply idpath.
  rewrite <- Hp, assoc, iso_after_iso_inv, id_left; apply idpath.

assert (weq4 : weq (total2 (fun h : iso a b => h ;; g = f))
                   (@iso (slice_precat h_homsets) af bg)).
  apply invweq; apply iso_weq.

apply (weqcomp weq1 (weqcomp weq2 (weqcomp weq3 weq4))).
Defined.

Lemma is_category_slice_precategory (is_catC : is_category C) :
  is_category (slice_precat (pr2 is_catC)).
Proof.
split; [| apply has_homsets_slice_precat]; simpl; intros a b.
case is_catC; simpl; intros h_univ h_homsets.
set (h := id_weq_iso_slicecat is_catC a b).
apply (isweqhomot h).
  intro p; destruct p.
  apply eq_iso; simpl.
  assert (H : pr1 (pr1 (h (idpath a))) = pr1 (id_slice_precat a)).
    unfold h; unfold id_weq_iso_slicecat.
    case is_catC; trivial.
  apply (total2_paths H); apply h_homsets.
case h; trivial.
Qed.

End slicecat_def.