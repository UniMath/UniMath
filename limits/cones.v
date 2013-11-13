Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.
Require Import RezkCompletion.limits.aux_lemmas_HoTT.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

Section Cone.

Variables J C : precategory.

Variable F : functor J C.

Definition ConeData := total2 (
  fun a : C => forall j : J, a --> F j).

Definition ConeTop (a : ConeData) : C := pr1 a.
Definition ConeMor (a : ConeData) (j : J) : ConeTop a --> F j := (pr2 a) j.

Lemma eq_ConeData_eq (a b : ConeData) (p q : a == b) :
   base_paths _ _ p == base_paths _ _ q -> p == q.
Proof.
  intro H.
  apply (eq_equalities_between_pairs _ _ _ _ _ _ H).
  apply uip.
  apply (impred 2); intro j.
  apply (pr2 (_ --> _ )).
Defined.

Definition ConeProp (a : ConeData) :=
  forall j j' (f : j --> j'), ConeMor a j ;; #F f == ConeMor a j'.

Lemma isaprop_ConeProp (a : ConeData) : isaprop (ConeProp a).
Proof.
  repeat (apply impred; intro).
  apply (pr2 (_ --> _)).
Qed.

Definition Cone := total2 (fun a : ConeData => ConeProp a).


Definition ConeData_from_Cone : Cone -> ConeData := fun a => pr1 a.

Lemma eq_Cone_eq (a b : Cone) (p q : a == b) :
   base_paths _ _ (base_paths _ _ p) == 
   base_paths _ _ (base_paths _ _ q) -> p == q.
Proof.
  intro H.
  assert (H2 : base_paths _ _ p == base_paths _ _ q).
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
  forall j j' (f : j --> j'), ConeMor a j ;; #F f == ConeMor a j'.
Proof.
  exact (pr2 a).
Qed.

Definition Cone_eq (a b : Cone) : pr1 a == pr1 b -> a == b.
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply isaprop_ConeProp.
Defined.

Definition Cone_Mor (M N : Cone) := 
  total2 (fun f : ConeTop M --> ConeTop N =>
        forall j : J, f ;; ConeMor N j == ConeMor M j).


Lemma isaset_Cone_Mor (M N : Cone) : isaset (Cone_Mor M N).
Proof.
  apply (isofhleveltotal2 2).
  apply (pr2 (_ --> _ )).
  intros.
  apply hlevelntosn.
  apply impred.
  intros.
  apply (pr2 (_ --> _ )).
Qed.

Definition ConeConnect {M N : Cone} (f : Cone_Mor M N) : 
    ConeTop M --> ConeTop N := pr1 f.

Lemma Cone_Mor_eq (M N : Cone) (f g : Cone_Mor M N) : 
   ConeConnect f == ConeConnect g -> f == g.
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply impred; intro; apply (pr2 (_ --> _)).
Qed.

Lemma cone_mor_prop M N (f : Cone_Mor M N) : 
    forall j : J, ConeConnect f ;; ConeMor N j == ConeMor M j.
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
  exists (ConeConnect f ;; ConeConnect g).
  intro j.
  (* make this proof opaque *)
  rewrite <- assoc.
  rewrite cone_mor_prop.
  rewrite cone_mor_prop.
  apply idpath.
Defined.
Check is_precategory.
Print precategory_data.


Definition Cone_precategory_ob_mor : precategory_ob_mor := 
   precategory_ob_mor_pair Cone 
   (fun a b => hSetpair (Cone_Mor a b) (isaset_Cone_Mor a b)).

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
Qed.
  
Definition CONE : precategory := tpair _ _ is_precategory_Cone.

(*
Definition Cone_Mor_from_iso (a b : CONE) (f : iso a b) : 
         a --> b := pr1 f.
Coercion Cone_Mor_from_iso : iso >-> hSet.
*)


(* this should not need the pr1 before f *)

Definition iso_projects_from_CONE (a b : CONE) (f : iso a b) :
  is_isomorphism (ConeConnect (pr1 f)).
Proof.
  exists (ConeConnect (inv_from_iso f)).
  split; simpl.
  apply (base_paths _ _ (pr1 (pr2 (pr2 f)))).
  apply (base_paths _ _ (pr2 (pr2 (pr2 f)))).
Defined.

Definition ConeConnectIso {a b : CONE} (f : iso a b) :
   iso (ConeTop (pr1 a)) (ConeTop (pr1 b)) := 
 tpair _ _ (iso_projects_from_CONE a b f).

Lemma ConeConnectIso_identity_iso (a : CONE) :
   ConeConnectIso (identity_iso a) == identity_iso _ .
Proof.
  apply eq_iso.
  apply idpath.
Qed.

Lemma ConeConnectIso_inj (a b : CONE) (f g : iso a b) :
   ConeConnectIso f == ConeConnectIso g -> f == g.
Proof.
  intro H.
  apply eq_iso; simpl in *.
  apply Cone_Mor_eq.
  apply (base_paths _ _ H).
Qed.


Section CONE_category.

Hypothesis is_cat_C : is_category C.


Definition isotoid_CONE_pr1 (a b : CONE) : iso a b -> pr1 a == pr1 b.
Proof.
  intro f.
  apply (total2_paths (isotoid _ is_cat_C (ConeConnectIso f))).
  pathvia ((fun c : J =>
     idtoiso (!isotoid C is_cat_C (ConeConnectIso f));; pr2 (pr1 a) c)).
  apply transportf_isotoid_dep'.
  apply funextsec.
  intro t.
  pathvia (idtoiso (isotoid C is_cat_C (iso_inv_from_iso (ConeConnectIso f)));;
       pr2 (pr1 a) t).
  apply cancel_postcomposition.
  apply maponpaths. apply maponpaths.
  apply inv_isotoid.
  pathvia (iso_inv_from_iso (ConeConnectIso f);; pr2 (pr1 a) t).
  apply cancel_postcomposition.
  set (H := idtoiso_isotoid _ is_cat_C _ _ (iso_inv_from_iso (ConeConnectIso f))).
  simpl in *.
  apply (base_paths _ _ H).
  simpl.
  apply (pr2 (inv_from_iso f)).
Defined.

Definition isotoid_CONE {a b : CONE} : iso a b -> a == b.
Proof.
  intro f.
  apply Cone_eq.
  apply (isotoid_CONE_pr1 _ _ f).
Defined.


Lemma eq_CONE_pr1 (M N : CONE) (p q : M == N) : base_paths _ _ p == base_paths _ _ q -> p == q.
Proof.
  intro H.
  simpl in *.
  apply (eq_equalities_between_pairs _ _ _ _ _ _ H).
  apply proofirrelevance.
  apply isapropifcontr.
  apply isaprop_ConeProp.
Defined.
  

Lemma lemma1 (M : CONE):
  base_paths (pr1 M) (pr1 M)
    (base_paths M M (Cone_eq M M (isotoid_CONE_pr1 M M (identity_iso M)))) ==
  idpath (pr1 (pr1 M)).
Proof.
  pathvia (base_paths (pr1 M) (pr1 M) (isotoid_CONE_pr1 M M (identity_iso M))).
  unfold Cone_eq.
  apply maponpaths. 
  apply base_total_path.
  pathvia (isotoid C is_cat_C (ConeConnectIso (identity_iso M))).
  unfold isotoid_CONE_pr1.
  apply base_total_path.
  pathvia (isotoid C is_cat_C (identity_iso (ConeTop (pr1 M)))).
  apply maponpaths, ConeConnectIso_identity_iso.
  apply isotoid_identity_iso.
Defined.
  
Lemma lemma2 (M : CONE):
base_paths (pr1 M) (pr1 M)
      (base_paths M M (isotoid_CONE (identity_iso M))) ==
    base_paths (pr1 M) (pr1 M) (idpath (pr1 M)).
Proof.
  pathvia (base_paths (pr1 M) (pr1 M) (isotoid_CONE_pr1 M M (identity_iso M))).
  unfold Cone_eq.
  apply maponpaths. 
  apply base_total_path.
  pathvia (isotoid C is_cat_C (ConeConnectIso (identity_iso M))).
  unfold isotoid_CONE_pr1.
  apply base_total_path.
  pathvia (isotoid C is_cat_C (identity_iso (ConeTop (pr1 M)))).
  apply maponpaths, ConeConnectIso_identity_iso.
  apply isotoid_identity_iso.
Defined.


Lemma bla (M N : CONE) : forall p : M == N, isotoid_CONE (idtoiso p) == p.
Proof.
  intro p.
  induction p.
  apply eq_Cone_eq.
  apply lemma2.
Qed.


(*
Lemma isotoid_CONE_inj (M N : CONE) (f g : iso M N) : 
    isotoid_CONE f == isotoid_CONE g -> f == g.
Proof.
  intro H.
  apply ConeConnectIso_inj.
  apply (isotoid_inj _ is_cat_C).
  Check isotoid_CONE f.
  Check isotoid C is_cat_C (ConeConnectIso f).
  unfold isotoid_CONE in H.
  Check isotoid C is_cat_C (ConeConnectIso f).
  Check Cone_eq M N (isotoid_CONE_pr1 M N f).
  unfold isotoid_CONE_pr1 in H.
  simpl in H.
  apply (base_paths _ _ H).
  unfold isotoid_CONE in H.
  unfold 
  simpl in H.
  simpl.
  Check pr1 f.
  apply (Cone_Mor_eq M N).
  unfold isotoid_CONE in H.
  simpl in H.
  
*)

Lemma helper (M N : CONE):
  ConeConnect (idtoiso p) == idtoiso (base_path p).

Lemma bla2 (M N : CONE) : forall f : iso M N, idtoiso (isotoid_CONE f) == f.
Proof.
  intro f.
  apply eq_iso.
  simpl.
  apply Cone_Mor_eq.
  simpl.
  unfold isotoid_CONE.
  simpl.
  unfold isotoid_CONE_pr1.
  simpl.

  unfold Cone_eq.
  simpl.

  


  apply eq_CONE_pr1.
  simpl.
(*
    assert (H : base_paths _ _ (base_paths M M (isotoid_CONE M M (identity_iso M))) == 
              base_paths _ _ (idpath (pr1 M))).
   admit.
  set (H':= lemma1 M).
*)
  unfold isotoid_CONE.
   simpl.

  apply (eq_equalities_between_pairs  _ _ _ _ _  _  (lemma2 M)).
  simpl.
  
  simpl.
  unfold lemma2.
  simpl.
  
  assert (H : base_paths _ _ (base_paths M M (isotoid_CONE M M (identity_iso M))) == 
              base_paths _ _ (idpath (pr1 M))).
   simpl. unfold isotoid_CONE. unfold Cone_eq. 
   rewrite base_total_path.
   unfold isotoid_CONE_pr1.
   simpl.
   rewrite base_total_path.
   rewrite ConeConnectIso_identity_iso.
   rewrite isotoid_identity_iso.
   apply idpath.
   apply (eq_equalities_between_pairs _  _ _ _ _ _ H).
   simpl.
   rewrite fiber_base_path.
   unfold ConeConnectIso. simpl. 
   
   unfold 
   simpl.
   simpl.
  set (H':= equal_transport_along_weq _ _ (total_paths_equiv _ M M )).
  apply H'; clear H'.
  simpl.
  assert (H2 : base_paths M M (isotoid_CONE M M (identity_iso M)) == idpath (pr1 M)).
  set (H'':= equal_transport_along_weq _ _ (total_paths_equiv _ (pr1 M) (pr1 M) )).
  apply H''; clear H''.
  simpl.
  Focus 2.
  apply (total2_paths2_UU _ H2).
  
  unfold isotoid_CONE.
  simpl.
  unfold Cone_eq.
  simpl.
  apply idpath.
  simpl.
            
  
  simpl.
  
  unfold isotoid_CONE.
  simpl.
  unfold Cone_eq.
  simpl.
  apply idpath.

End Cone.

  

End Cone.
Check CONE.

Implicit Arguments CONE [J C].
Implicit Arguments ConeConnect [J C].
About CONE.


(** isos in CONE yield isos in C *)

(*
Lemma ConeConnect_inv_from_iso (a b : CONE) (f : iso a b) :
    ConeConnect (inv_from_iso f) == 
*)     



(* this should not need the pr1 before f *)

Definition iso_projects_from_CONE (J C : precategory) (F : functor J C) 
   (a b : CONE F) (f : iso a b) :
  is_isomorphism (ConeConnect F (pr1 f)).
Proof.
  exists (ConeConnect (inv_from_iso f)).
  split; simpl.
  apply (base_paths _ _ (pr1 (pr2 (pr2 f)))).
  apply (base_paths _ _ (pr2 (pr2 (pr2 f)))).
Defined.

Definition ConeConectIso (a b : CONE) (f : iso a b) :
   iso (ConeTop a) (ConeTop b) := tpair _ _ (iso_projects_from_CONE a b f).

Section CONE_category.

Hypothesis H : is_category C.

Definition isotoid_CONE (a b : CONE) : iso a b -> a == b.
intro f.
  apply (total2_paths (isotoid _ H (pr1 f))).


End Cone.

(** a limit is a terminal object in (CONE A) *)



Definition LIMIT A := Terminal (CONE A).

(** easy access to interesting parts of a limit *)

Section Limit_defs.

Variable A : Functor J C.

Hypothesis H : LIMIT A.

Definition Limit : Cone A := Term (Terminal := H).

Definition LimitVertex : obC := ConeTop Limit.

Definition LimitMor (j : obJ) := cone_mor (ConeClass := Limit) j.

End Limit_defs.

End defs.