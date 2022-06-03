(**

Definition of the precategory of cones over a precategory C together with a proof that that
precategory is a univalent_category if C is ([is_univalent_CONE]).

Written by Benedikt Ahrens, following discussions with J. Gross, D. Grayson and V. Voevodsky
*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Local Open Scope cat.

Section Cone.

  Variables J : precategory.
  Variable C : category.

Variable F : functor J C.

Definition ConeData : UU := ∑ a : C, ∏ j : J, a --> F j.

Definition ConeTop (a : ConeData) : C := pr1 a.
Definition ConeMor (a : ConeData) (j : J) : ConeTop a --> F j := (pr2 a) j.

Lemma eq_ConeData_eq (a b : ConeData) (p q : a = b) :
   base_paths _ _ p = base_paths _ _ q -> p = q.
Proof.
  intro H.
  apply (eq_equalities_between_pairs _ _ _ _ _ _ H).
  apply uip.
  apply (impred 2); intro j.
  apply C.
Defined.

Definition ConeProp (a : ConeData) :=
  ∏ j j' (f : j --> j'), ConeMor a j · #F f = ConeMor a j'.

Lemma isaprop_ConeProp (a : ConeData) : isaprop (ConeProp a).
Proof.
  repeat (apply impred; intro).
  apply C.
Qed.

Definition Cone := total2 (λ a : ConeData, ConeProp a).


Definition ConeData_from_Cone : Cone -> ConeData := λ a, pr1 a.

Lemma eq_Cone_eq (a b : Cone) (p q : a = b) :
   base_paths _ _ (base_paths _ _ p) =
   base_paths _ _ (base_paths _ _ q) -> p = q.
Proof.
  intro H.
  assert (H2 : base_paths _ _ p = base_paths _ _ q).
  apply eq_ConeData_eq.
  apply H.
  apply (eq_equalities_between_pairs _ _ _ _ _ _ H2).
  apply uip.
  apply isasetaprop.
  apply isaprop_ConeProp.
Defined.


Coercion ConeData_from_Cone : Cone >-> ConeData.

Definition ConeProp_from_Cone (a : Cone) : ConeProp a := pr2 a.
Coercion ConeProp_from_Cone : Cone >-> ConeProp.


Lemma cone_prop (a : Cone) :
  ∏ j j' (f : j --> j'), ConeMor a j · #F f = ConeMor a j'.
Proof.
  exact (pr2 a).
Qed.

Definition Cone_eq (a b : Cone) : pr1 a = pr1 b -> a = b.
Proof.
  intro H.
  apply (total2_paths_f H).
  apply proofirrelevance.
  apply isaprop_ConeProp.
Defined.

Definition Cone_Mor (M N : Cone) :=
  total2 (fun f : ConeTop M --> ConeTop N =>
        ∏ j : J, f · ConeMor N j = ConeMor M j).


Lemma isaset_Cone_Mor (M N : Cone) : isaset (Cone_Mor M N).
Proof.
  apply (isofhleveltotal2 2).
  apply C.
  intros.
  apply hlevelntosn.
  apply impred.
  intros.
  apply C.
Qed.

Definition ConeConnect {M N : Cone} (f : Cone_Mor M N) :
    ConeTop M --> ConeTop N := pr1 f.

Lemma Cone_Mor_eq (M N : Cone) (f g : Cone_Mor M N) :
   ConeConnect f = ConeConnect g -> f = g.
Proof.
  intro H.
  apply (total2_paths_f H).
  apply proofirrelevance.
  apply impred; intro; apply C.
Qed.

Lemma cone_mor_prop M N (f : Cone_Mor M N) :
    ∏ j : J, ConeConnect f · ConeMor N j = ConeMor M j.
Proof.
  exact (pr2 f).
Qed.

Definition Cone_id (A : Cone) : Cone_Mor A A.
Proof.
  exists (identity _).
  intros; apply id_left.
Defined.


Definition Cone_comp (A B D : Cone) (f : Cone_Mor A B)
        (g : Cone_Mor B D) : Cone_Mor A D.
Proof.
  exists (ConeConnect f · ConeConnect g).
  intro j.
  (* make this proof opaque *)
  rewrite <- assoc.
  rewrite cone_mor_prop.
  rewrite cone_mor_prop.
  apply idpath.
Defined.


Definition Cone_precategory_ob_mor : precategory_ob_mor :=
   make_precategory_ob_mor Cone
   (λ a b, Cone_Mor a b).

Definition Cone_precategory_data : precategory_data.
Proof.
  exists Cone_precategory_ob_mor.
  exists Cone_id.
  exact Cone_comp.
Defined.

Lemma is_precategory_Cone : is_precategory Cone_precategory_data.
Proof.
  repeat split; simpl.

  intros;
  apply Cone_Mor_eq;
  simpl; apply id_left.

  intros;
  apply Cone_Mor_eq;
  simpl; apply id_right.

  intros;
  apply Cone_Mor_eq;
  simpl; apply assoc.

  intros;
  apply Cone_Mor_eq;
  simpl; apply assoc'.
Defined.

Definition CONEpre : precategory := tpair _ _ is_precategory_Cone.

Lemma has_homsets_CONEpre : has_homsets CONEpre.
Proof.
  intros x y.
  apply isaset_Cone_Mor.
Qed.

Definition CONE : category := CONEpre ,, has_homsets_CONEpre.



(* this should not need the pr1 before f *)

Definition iso_projects_from_CONE (a b : CONE) (f : z_iso a b) :
  is_z_isomorphism (ConeConnect (pr1 f)).
Proof.
  set (T:=z_iso_inv_after_z_iso f).
  set (T':=z_iso_after_z_iso_inv f).
  exists (ConeConnect (inv_from_z_iso f)).
  split; simpl.
  - apply (base_paths _ _ T).
  - apply (base_paths _ _ T').
Defined.

Definition ConeConnectIso {a b : CONE} (f : z_iso a b) :
   z_iso (ConeTop (pr1 a)) (ConeTop (pr1 b)) :=
 tpair _ _ (iso_projects_from_CONE a b f).

Lemma ConeConnectIso_identity_iso (a : CONE) :
   ConeConnectIso (identity_z_iso a) = identity_z_iso _ .
Proof.
  apply eq_z_iso. apply idpath.
Qed.

Lemma ConeConnectIso_inj (a b : CONE) (f g : z_iso a b) :
   ConeConnectIso f = ConeConnectIso g -> f = g.
Proof.
  intro H.
  apply eq_z_iso; simpl in *.
  apply Cone_Mor_eq.
  apply (base_paths _ _ H).
Qed.

Lemma inv_from_iso_ConeConnectIso (a b : CONE) (f : z_iso a b):
  pr1 (inv_from_z_iso f) = inv_from_z_iso (ConeConnectIso f).
Proof.
  apply idpath.
Defined.

End Cone.

Arguments CONE [J C].
Arguments ConeConnect [J C].

Section CONE_category.


Variable J : precategory.
Variable C : category.
Variable F : functor J C.
Hypothesis is_cat_C : is_univalent C.


Definition isotoid_CONE_pr1 (a b : CONE F) : z_iso a b -> pr1 a = pr1 b.
Proof.
  intro f.
  apply (total2_paths_f (isotoid _ is_cat_C (ConeConnectIso _ _ _ f))).
  intermediate_path ((λ c : J,
     idtoiso (!isotoid C is_cat_C (ConeConnectIso _ _ _ f))· pr2 (pr1 a) c)).
  apply transportf_isotoid_dep'.
  apply funextsec.
  intro t.
  intermediate_path (idtoiso (isotoid C is_cat_C (z_iso_inv_from_z_iso (ConeConnectIso _ _ _ f)))·
       pr2 (pr1 a) t).
  apply cancel_postcomposition.
  apply maponpaths. apply maponpaths.
  apply inv_isotoid.
  intermediate_path (z_iso_inv_from_z_iso (ConeConnectIso _ _ _ f)· pr2 (pr1 a) t).
  apply cancel_postcomposition.
  set (H := idtoiso_isotoid _ is_cat_C _ _ (z_iso_inv_from_z_iso (ConeConnectIso _ _ _ f))).
  simpl in *.
  apply (base_paths _ _ H).
  simpl.
  set (T':= inv_from_z_iso f).
  set (T:=pr2 (inv_from_z_iso f) t).
  simpl in *.
  rewrite <- inv_from_iso_ConeConnectIso.
  apply T.
Defined.

Definition isotoid_CONE {a b : CONE F} : z_iso a b -> a = b.
Proof.
  intro f.
  apply Cone_eq.
  apply (isotoid_CONE_pr1 _ _ f).
Defined.


Lemma eq_CONE_pr1 (M N : CONE F) (p q : M = N) : base_paths _ _ p = base_paths _ _ q -> p = q.
Proof.
  intro H.
  simpl in *.
  apply (eq_equalities_between_pairs _ _ _ _ _ _ H).
  apply proofirrelevancecontr.
  apply isaprop_ConeProp.
Defined.


Lemma base_paths_isotoid_CONE (M : CONE F):
base_paths (pr1 M) (pr1 M)
      (base_paths M M (isotoid_CONE (identity_z_iso M))) =
    base_paths (pr1 M) (pr1 M) (idpath (pr1 M)).
Proof.
  intermediate_path (base_paths (pr1 M) (pr1 M) (isotoid_CONE_pr1 M M (identity_z_iso M))).
  unfold Cone_eq.
  apply maponpaths.
  apply base_total2_paths.
  intermediate_path (isotoid C is_cat_C (ConeConnectIso _ _ _ (identity_z_iso M))).
  unfold isotoid_CONE_pr1.
  apply base_total2_paths.
  intermediate_path (isotoid C is_cat_C (identity_z_iso (ConeTop _ _ _ (pr1 M)))).
  apply maponpaths, ConeConnectIso_identity_iso.
  apply isotoid_identity_iso.
Defined.


Lemma isotoid_CONE_idtoiso (M N : CONE F) : ∏ p : M = N, isotoid_CONE (idtoiso p) = p.
Proof.
  intro p.
  induction p.
  apply eq_Cone_eq.
  apply base_paths_isotoid_CONE.
Qed.



Lemma ConeConnect_idtoiso (M N : CONE F) (p : M = N):
  ConeConnect _ _ _ (pr1 (idtoiso p)) = idtoiso ((base_paths _ _ (base_paths _ _  p))).
Proof.
  destruct p.
  apply idpath.
Qed.

Lemma idtoiso_isotoid_CONE (M N : CONE F) : ∏ f : z_iso M N, idtoiso (isotoid_CONE f) = f.
Proof.
  intro f.
  apply eq_z_iso.
    apply Cone_Mor_eq.
    rewrite ConeConnect_idtoiso.
    unfold isotoid_CONE.
    unfold Cone_eq.
    rewrite base_total2_paths.
    unfold isotoid_CONE_pr1.
    rewrite base_total2_paths.
    simpl.
    rewrite idtoiso_isotoid.
    apply idpath.
Qed.


Lemma is_univalent_CONE : is_univalent (CONE F).
Proof.
  intros a b.
  apply (isweq_iso _  (@isotoid_CONE a b)).
  apply isotoid_CONE_idtoiso.
  apply idtoiso_isotoid_CONE.
Defined.

End CONE_category.
