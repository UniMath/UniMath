(** **********************************************************

Written by: Anders Mörtberg, Benedikt Ahrens
Based on: limits/cones.v

**************************************************************)

(** **********************************************************

Contents :

            Precategory COCONES of co-cones

************************************************************)

Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.

Local Notation "a --> b" := (precategory_morphisms a b) (at level 50).
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").
Local Notation "# F" := (functor_on_morphisms F) (at level 3).

Section CoCone.

Variables J C : precategory.
Variable hs : has_homsets C.
Variable F : functor J C.

Definition CoconeData : UU := Σ a, ∀ (j : J), F j --> a.

Definition coconeBottom (c : CoconeData) : C := pr1 c.
Definition coconeIn (c : CoconeData) (j : J) : F j --> coconeBottom c := pr2 c j.

Lemma eq_CoconeData_eq (a b : CoconeData) (p q : a = b) :
   base_paths _ _ p = base_paths _ _ q -> p = q.
Proof.
  intro H.
  apply (eq_equalities_between_pairs _ _ _ _ _ _ H).
  apply uip.
  apply (impred 2); intro j.
  apply hs.
Defined.

Definition CoconeProp (a : CoconeData) : UU :=
  ∀ i j (f : i --> j), #F f ;; coconeIn a j = coconeIn a i.

Lemma isaprop_CoconeProp (a : CoconeData) : isaprop (CoconeProp a).
Proof.
  repeat (apply impred; intro).
  apply hs.
Qed.

Definition Cocone : UU := Σ c, CoconeProp c.

Definition CoconeData_from_Cocone : Cocone -> CoconeData := pr1.
Coercion CoconeData_from_Cocone : Cocone >-> CoconeData.

Lemma eq_Cocone_eq (a b : Cocone) (p q : a = b) :
   base_paths _ _ (base_paths _ _ p) =
   base_paths _ _ (base_paths _ _ q) -> p = q.
Proof.
  intro H.
  (* generalize (eq_CoconeData_eq p q). *)
  assert (H2 : base_paths _ _ p = base_paths _ _ q).
    now apply eq_CoconeData_eq.
  apply (eq_equalities_between_pairs _ _ _ _ _ _ H2).
  apply uip.
  apply isasetaprop.
  now apply isaprop_CoconeProp.
Defined.

Definition CoconeProp_from_Cocone : ∀ (a : Cocone), CoconeProp a := pr2.
Coercion CoconeProp_from_Cocone : Cocone >-> CoconeProp.

(* Lemma cone_prop (a : Cone) :  *)
(*   forall j j' (f : j --> j'), ConeMor a j ;; #F f = ConeMor a j'. *)
(* Proof. *)
(*   exact (pr2 a). *)
(* Qed. *)

Definition Cocone_eq (a b : Cocone) : pr1 a = pr1 b -> a = b.
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_CoconeProp.
Defined.

Definition CoconeMor (M N : Cocone) :=
  Σ (f : coconeBottom M --> coconeBottom N),
     ∀ i : J, coconeIn M i ;; f = coconeIn N i.

Lemma isaset_CoconeMor (M N : Cocone) : isaset (CoconeMor M N).
Proof.
  apply (isofhleveltotal2 2).
    now apply hs.
  intros f.
  apply hlevelntosn.
  apply impred.
  intros i.
  now apply hs.
Qed.

Definition coconeBottomMor {M N : Cocone} (f : CoconeMor M N) :
  coconeBottom M --> coconeBottom N := pr1 f.

Lemma CoconeMor_eq (M N : Cocone) (f g : CoconeMor M N) :
   coconeBottomMor f = coconeBottomMor g -> f = g.
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply impred; intro Hs; apply hs.
Qed.

Lemma CoconeMor_prop M N (f : CoconeMor M N) :
  ∀ i, coconeIn M i ;; coconeBottomMor f = coconeIn N i.
Proof.
exact (pr2 f).
Qed.

Definition Cocone_id (A : Cocone) : CoconeMor A A.
Proof.
  exists (identity _).
  intro i; apply id_right.
Defined.

Definition Cocone_comp (a b c : Cocone) (f : CoconeMor a b)
  (g : CoconeMor b c) : CoconeMor a c.
Proof.
exists (coconeBottomMor f ;; coconeBottomMor g).
abstract (now (intro i; rewrite assoc, CoconeMor_prop, CoconeMor_prop)).
Defined.

Definition Cocone_precategory_ob_mor : precategory_ob_mor :=
  precategory_ob_mor_pair Cocone CoconeMor.

Definition Cocone_precategory_data : precategory_data.
Proof.
  exists Cocone_precategory_ob_mor.
  exists Cocone_id.
  exact Cocone_comp.
Defined.

Lemma is_precategory_Cocone : is_precategory Cocone_precategory_data.
Proof.
  repeat split; simpl.

  intros a b f; apply CoconeMor_eq; simpl; apply id_left.
  intros a b f; apply CoconeMor_eq; simpl; apply id_right.
  intros a b c d f g h; apply CoconeMor_eq; simpl; apply assoc.
Qed.

Definition COCONE : precategory := tpair _ _ is_precategory_Cocone.

(*** TODO: Adapt this: *)

(* this should not need the pr1 before f *)

(* Definition iso_projects_from_COCONE (a b : COCONE) (f : iso a b) : *)
(*   is_isomorphism (coconeBottom (pr1 f)). *)
(* Proof. *)
(*   set (T:=iso_inv_after_iso f). *)
(*   set (T':=iso_after_iso_inv f). *)
(*   apply (is_iso_qinv _ (ConeConnect (inv_from_iso f))). *)
(*   split; simpl. *)
(*   - apply (base_paths _ _ T). *)
(*   - apply (base_paths _ _ T'). *)
(* Defined. *)

(* Definition ConeConnectIso {a b : CONE} (f : iso a b) : *)
(*    iso (ConeTop (pr1 a)) (ConeTop (pr1 b)) :=  *)
(*  tpair _ _ (iso_projects_from_CONE a b f). *)

(* Lemma ConeConnectIso_identity_iso (a : CONE) : *)
(*    ConeConnectIso (identity_iso a) = identity_iso _ . *)
(* Proof. *)
(*   apply eq_iso. apply idpath. *)
(* Qed. *)

(* Lemma ConeConnectIso_inj (a b : CONE) (f g : iso a b) : *)
(*    ConeConnectIso f = ConeConnectIso g -> f = g. *)
(* Proof. *)
(*   intro H. *)
(*   apply eq_iso; simpl in *. *)
(*   apply Cone_Mor_eq. *)
(*   apply (base_paths _ _ H). *)
(* Qed. *)

(* Lemma inv_from_iso_ConeConnectIso (a b : CONE) (f : iso a b): *)
(*   pr1 (inv_from_iso f) = inv_from_iso (ConeConnectIso f). *)
(* Proof. *)
(*   apply inv_iso_unique'. *)
(*   unfold precomp_with.  *)
(*   set (T:=iso_inv_after_iso f). *)
(*   set (T':=iso_after_iso_inv f). *)
(*   apply (base_paths _ _ T). *)
(* Defined. *)

(* Section CONE_category. *)

(* Hypothesis is_cat_C : is_category C. *)


(* Definition isotoid_CONE_pr1 (a b : CONE) : iso a b -> pr1 a = pr1 b. *)
(* Proof. *)
(*   intro f. *)
(*   apply (total2_paths (isotoid _ is_cat_C (ConeConnectIso f))). *)
(*   pathvia ((fun c : J => *)
(*      idtoiso (!isotoid C is_cat_C (ConeConnectIso f));; pr2 (pr1 a) c)). *)
(*   apply transportf_isotoid_dep'. *)
(*   apply funextsec. *)
(*   intro t. *)
(*   pathvia (idtoiso (isotoid C is_cat_C (iso_inv_from_iso (ConeConnectIso f)));; *)
(*        pr2 (pr1 a) t). *)
(*   apply cancel_postcomposition. *)
(*   apply maponpaths. apply maponpaths. *)
(*   apply inv_isotoid. *)
(*   pathvia (iso_inv_from_iso (ConeConnectIso f);; pr2 (pr1 a) t). *)
(*   apply cancel_postcomposition. *)
(*   set (H := idtoiso_isotoid _ is_cat_C _ _ (iso_inv_from_iso (ConeConnectIso f))). *)
(*   simpl in *. *)
(*   apply (base_paths _ _ H). *)
(*   simpl. *)
(*   set (T':= inv_from_iso f). *)
(*   set (T:=pr2 (inv_from_iso f) t). *)
(*   simpl in *.  *)
(*   rewrite <- inv_from_iso_ConeConnectIso. *)
(*   apply T. *)
(* Defined. *)

(* Definition isotoid_CONE {a b : CONE} : iso a b -> a = b. *)
(* Proof. *)
(*   intro f. *)
(*   apply Cone_eq. *)
(*   apply (isotoid_CONE_pr1 _ _ f). *)
(* Defined. *)


(* Lemma eq_CONE_pr1 (M N : CONE) (p q : M = N) : base_paths _ _ p = base_paths _ _ q -> p = q. *)
(* Proof. *)
(*   intro H. *)
(*   simpl in *. *)
(*   apply (eq_equalities_between_pairs _ _ _ _ _ _ H). *)
(*   apply proofirrelevance. *)
(*   apply isapropifcontr. *)
(*   apply isaprop_ConeProp. *)
(* Defined. *)


(* Lemma base_paths_isotoid_CONE (M : CONE): *)
(* base_paths (pr1 M) (pr1 M) *)
(*       (base_paths M M (isotoid_CONE (identity_iso M))) = *)
(*     base_paths (pr1 M) (pr1 M) (idpath (pr1 M)). *)
(* Proof. *)
(*   pathvia (base_paths (pr1 M) (pr1 M) (isotoid_CONE_pr1 M M (identity_iso M))). *)
(*   unfold Cone_eq. *)
(*   apply maponpaths.  *)
(*   apply base_total2_paths. *)
(*   pathvia (isotoid C is_cat_C (ConeConnectIso (identity_iso M))). *)
(*   unfold isotoid_CONE_pr1. *)
(*   apply base_total2_paths. *)
(*   pathvia (isotoid C is_cat_C (identity_iso (ConeTop (pr1 M)))). *)
(*   apply maponpaths, ConeConnectIso_identity_iso. *)
(*   apply isotoid_identity_iso. *)
(* Defined. *)


(* Lemma isotoid_CONE_idtoiso (M N : CONE) : forall p : M = N, isotoid_CONE (idtoiso p) = p. *)
(* Proof. *)
(*   intro p. *)
(*   induction p. *)
(*   apply eq_Cone_eq. *)
(*   apply base_paths_isotoid_CONE. *)
(* Qed. *)



(* Lemma ConeConnect_idtoiso (M N : CONE) (p : M = N): *)
(*   ConeConnect (pr1 (idtoiso p)) = idtoiso ((base_paths _ _ (base_paths _ _  p))). *)
(* Proof. *)
(*   destruct p. *)
(*   apply idpath. *)
(* Qed. *)

(* Lemma idtoiso_isotoid_CONE (M N : CONE) : forall f : iso M N, idtoiso (isotoid_CONE f) = f. *)
(* Proof. *)
(*   intro f. *)
(*   apply eq_iso. *)
(*     simpl. *)
(*     apply Cone_Mor_eq. *)
(*     rewrite ConeConnect_idtoiso. *)
(*     unfold isotoid_CONE. *)
(*     unfold Cone_eq. *)
(*     rewrite base_total2_paths. *)
(*     unfold isotoid_CONE_pr1. *)
(*     rewrite base_total2_paths. *)
(*     simpl. *)
(*     rewrite idtoiso_isotoid. *)
(*     apply idpath. *)
(* Qed. *)


(* Lemma is_category_CONE : is_category CONE. *)
(* Proof. *)
(*   split. *)
(*   - intros a b. *)
(*     apply (gradth _  (@isotoid_CONE a b)). *)
(*     apply isotoid_CONE_idtoiso. *)
(*     apply idtoiso_isotoid_CONE. *)
(*   - intros x y. apply isaset_Cone_Mor. *)
(* Defined. *)

(* End CONE_category. *)

End CoCone.

Implicit Arguments Cocone [J C].
Implicit Arguments COCONE [J C].
Implicit Arguments coconeBottom [J C F].

Section Colimit.

Require Import UniMath.CategoryTheory.limits.initial.

Variables J C : precategory.
Variable F : functor J C.
Variable hsC : has_homsets C.

Definition Colimit := Initial (COCONE hsC F).

Definition Colimit_ob (colim : Colimit) : C := coconeBottom (pr1 (InitialObject _ colim)).
Definition Colimit_inj (colim : Colimit) : ∀ i,  F i --> Colimit_ob colim :=
  coconeIn _ _ _ (pr1 (InitialObject _ colim)).

Definition Colimit_cocone : ∀ (colim : Colimit) (b : COCONE hsC F), Colimit_ob colim --> coconeBottom (pr1 b).
Proof.
  intros colim c.
  exact (coconeBottomMor _ _ _ (InitialArrow _ colim c)).
Defined.

Definition Colimit_cocone' : ∀ (colim : Colimit) (c : C) (Fi : ∀ i, F i --> c)
  (H : CoconeProp _ _ _ (tpair _ c Fi)), Colimit_ob colim --> c.
Proof.
intros colim c Fi H.
exact (Colimit_cocone colim (tpair _ _ H)).
Defined.

Definition hasColimit := hasInitial (COCONE hsC F).

End Colimit.

Arguments Colimit [J C] _ _.
Arguments Colimit_ob [J C F hsC] _.
Arguments Colimit_inj [J C F hsC] _ _.

Definition AllColimits (C : precategory) (hsC : has_homsets C) : UU :=
  ∀ (J : precategory) (F : functor J C), Colimit F hsC.


(*
 colim : [J,D] -> D
 this is a functor under the hypothesis allColimits D
*)

(* Section test. *)

(* Variables (J D : precategory). *)
(* Variable (hsD : has_homsets D). *)
(* (* Variable (F : [J,D,hsD]). *) *)

(* Variable (allColimitsD : AllColimits D hsD). *)

(* End test. *)

Section ColimitsFunctorCategories.

Variables (J C D : precategory).
Variable (hsD : has_homsets D).
Variable (F : functor J [C,D,hsD]).

Variable (allColimitsD : AllColimits D hsD).

(* j -> F_j c, for a given c *)
Definition colim_ob_data (c : C) : functor_data J D.
Proof.
  exists (fun j => pr1 (F j) c).
  intros i j f.
  exact (pr1 (# F f) c).
Defined.

Lemma is_functor_colim_ob_data (c : C) : is_functor (colim_ob_data c).
Proof.
split.
- intro i; simpl.
  now rewrite (functor_id F).
- intros i j k f g; simpl.
  now rewrite (functor_comp F).
Qed.

Definition F' (c : C) : functor J D :=
  tpair _ _ (is_functor_colim_ob_data c).

Definition Fi (a b : C) (f : a --> b) : ∀ i : J, (F' a) i --> Colimit_ob (allColimitsD J (F' b)).
Proof.
intros i.
set (T := (# (pr1 (F i)) f )).
unfold Colimit_ob.
simpl.
exact (T ;; coconeIn _ _ _ (pr1 (pr1 (allColimitsD J (F' b)))) _).
Defined.

Definition colim_data : functor_data C D.
Proof.
exists (fun c => Colimit_ob (allColimitsD J (F' c))).
intros a b f.
apply (Colimit_cocone' _ _ _ _ _ _ (Fi a b f)).
intros i j fij.
simpl.
unfold Fi.
(* set (inj := coconeIn _ _ _ _). *)
set (T := CoconeProp_from_Cocone _ _ _ (pr1 (allColimitsD J (F' b))) i j fij).
eapply pathscomp0; [ | eapply maponpaths; apply T ].
repeat rewrite assoc.
apply cancel_postcomposition.
unfold F'; simpl.
set (K:=@nat_trans_ax _ _ _ _ (# F fij) a b f).
apply pathsinv0.
exact K.
Defined.

Definition colim : functor C D.
Proof.
exists colim_data.
split.
- intro a.
   admit.
- intros a b c f g.
  admit.
Admitted.

(* TODO: Prove that this is a colimit *)

    Definition colimitFunctor : Colimit F (functor_category_has_homsets _ _ hsD).
Proof.

  
End ColimitsFunctorCategories.