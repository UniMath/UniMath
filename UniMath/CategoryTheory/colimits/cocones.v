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
Local Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (at level 50).
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

Definition CoconeMorProp {M N : CoconeData} (f : coconeBottom M --> coconeBottom N) :=
  ∀ i : J, coconeIn M i ;; f = coconeIn N i.

Definition CoconeMor (M N : CoconeData) :=
  Σ (f : coconeBottom M --> coconeBottom N), CoconeMorProp f. 

Lemma isaset_CoconeMor (M N : CoconeData) : isaset (CoconeMor M N).
Proof.
  apply (isofhleveltotal2 2).
    now apply hs.
  intros f.
  apply hlevelntosn.
  apply impred.
  intros i.
  now apply hs.
Qed.

Definition coconeBottomMor {M N : CoconeData} (f : CoconeMor M N) :
  coconeBottom M --> coconeBottom N := pr1 f.

Lemma CoconeMor_eq (M N : CoconeData) (f g : CoconeMor M N) :
   coconeBottomMor f = coconeBottomMor g -> f = g.
Proof.
  intro H.
  apply (total2_paths H).
  apply proofirrelevance.
  apply impred; intro Hs; apply hs.
Qed.

Lemma CoconeMor_prop {M N : CoconeData} (f : CoconeMor M N) :
  ∀ i, coconeIn M i ;; coconeBottomMor f = coconeIn N i.
Proof.
exact (pr2 f).
Qed.

Definition Cocone_id (A : CoconeData) : CoconeMor A A.
Proof.
  exists (identity _).
  intro i; apply id_right.
Defined.

Definition Cocone_comp (a b c : CoconeData) (f : CoconeMor a b)
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
  exists (fun (a : Cocone) => Cocone_id a).
  exact (fun (a b c : Cocone) => Cocone_comp a b c).
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

Section CoconeFunctor.

Variables J D : precategory.
Variable hsD : has_homsets D.
Variables F G : [J, D, hsD].
Variable α : F --> G.

Definition CoconeData_functor_ob : CoconeData _ _ G -> CoconeData _ _ F.
Proof.
intros CG.
exists (coconeBottom CG).
intro i.
exact (pr1 α i ;; coconeIn _ _ _ CG i).
Defined.

Definition COCONE_functor_ob : COCONE hsD G -> COCONE hsD F.
Proof.
intros CG.
exists (CoconeData_functor_ob (pr1 CG)).
abstract (
  intros i j x; simpl;
  set (T:= CoconeProp_from_Cocone _ _ _ CG i j x);
  eapply pathscomp0; [|eapply maponpaths; apply T]; 
  repeat rewrite assoc; 
  now apply cancel_postcomposition, nat_trans_ax).
Defined.

Definition CoconeFunctor_data : functor_data (COCONE hsD G) (COCONE hsD F).
Proof.
exists COCONE_functor_ob.
intros a b f.
simpl in α.
exists (coconeBottomMor _ _ _ f).
intros i; simpl; rewrite <- assoc; apply maponpaths;
apply CoconeMor_prop. (* Why cannot this be in abstract? *)
Defined.

Lemma is_functor_CoconeFunctor : is_functor CoconeFunctor_data.
Proof.
split.
- intro a.
  now apply (CoconeMor_eq _ _ hsD), idpath.
- intros a b c f g.
  now apply (CoconeMor_eq _ _ hsD), idpath.
Qed.

Definition CoconeFunctor : functor (COCONE hsD G) (COCONE hsD F) :=
  tpair _ _ is_functor_CoconeFunctor.


End CoconeFunctor.


Section Colimit.

Require Import UniMath.CategoryTheory.limits.initial.

Variables J C : precategory.
Variable F : functor J C.
Variable hsC : has_homsets C.

Definition Colimit := Initial (COCONE hsC F).

Definition Colimit_ob (colim : Colimit) : C := coconeBottom (pr1 (InitialObject _ colim)).
Definition Colimit_inj (colim : Colimit) : ∀ i, F i --> Colimit_ob colim :=
  coconeIn _ _ _ (pr1 (InitialObject _ colim)).
Definition Colimiting_cocone (c : Colimit) : COCONE hsC F :=
  InitialObject _ c.

Definition Colimit_univ (colim : Colimit) (c : COCONE hsC F) :
  Colimit_ob colim --> coconeBottom (pr1 c).
Proof.
  exact (coconeBottomMor _ _ _ (InitialArrow _ colim c)).
Defined.

Definition Colimit_univ' (colim : Colimit) (c : C) (Fi : ∀ i, F i --> c)
  (H : CoconeProp _ _ _ (tpair _ c Fi)) : Colimit_ob colim --> c.
Proof.
exact (Colimit_univ colim (tpair _ _ H)).
Defined.

Definition hasColimit := hasInitial (COCONE hsC F).

Lemma coconeEndoId (c : Colimit) (f : Colimiting_cocone c --> Colimiting_cocone c) :
  coconeBottomMor _ _ _ f = identity (Colimit_ob c).
Proof.
  set (T := InitialEndo_is_identity _ c f).
  set (T' := maponpaths (coconeBottomMor _ _ _) T).
  now apply pathsinv0.
Qed.

Lemma coconeEndoId' (c : Colimit) (f : Colimit_ob c --> Colimit_ob c) (h : @CoconeMorProp _ _ _ (pr1 (Colimiting_cocone c)) (pr1 (Colimiting_cocone c)) f) :
  f = identity (Colimit_ob c).
Proof.
  exact (coconeEndoId _ (tpair _ f h)).
Qed.
  
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
Section ColimitFunctor.

Variables (J D : precategory).
Variable (hsD : has_homsets D).
(* Variable (F : [J,D,hsD]). *)

Variable (H : ∀ (F : functor J D), Colimit F hsD).

Let colim (F : [J,D,hsD]) := coconeBottom (pr1 (Colimiting_cocone _ _ _ hsD (H F))).

Definition colimG_CoconeData (F G : [J, D, hsD]) (alpha : F --> G) :
  CoconeData _ _ F.
Proof.
exists (colim G).
intro i.
set (gi := coconeIn _ _ _ (pr1 (Colimiting_cocone J D G hsD (H G))) i).
exact (pr1 alpha i ;; gi).
Defined.

Definition colimG_Cocone (F G : [J, D, hsD]) (alpha : F --> G) :
  COCONE hsD F.
Proof.
exists (colimG_CoconeData F G alpha).
abstract (
  intros i j x; simpl; 
  set (T:= CoconeProp_from_Cocone _ _ _ (Colimiting_cocone J D G hsD (H G)) i j x);
  eapply pathscomp0; [|eapply maponpaths; apply T]; 
  repeat rewrite assoc; 
  now apply cancel_postcomposition, nat_trans_ax).
Defined.

Definition colimFunctor_data : functor_data [J,D,hsD] D.
Proof.
exists (fun (F : functor J D) => colim F).
intros F G alpha.
exact (Colimit_univ _ _ _ _ _ (colimG_Cocone F G alpha)).
Defined.

Definition wtf (F : [J,D,hsD]) : pr1 (colimG_CoconeData F F (identity F)) = pr1 (pr1 (pr1 (H F))).
Proof.
apply idpath.
Defined.

Lemma is_functor_colimFunctor_data : is_functor colimFunctor_data.
Proof.
split.
- intro F.
unfold colimFunctor_data.
simpl.
unfold Colimit_univ.
simpl.
set (Apa := (InitialArrow (COCONE hsD F) (H F) (colimG_Cocone F F (identity F)))).
assert (test : colimG_Cocone F F (identity F) = pr1 (H F)).
  apply total2_paths_second_isaprop.
    apply isaprop_CoconeProp.
    now apply hsD.
  simpl.
(* assert (HH:pr1 (colimG_CoconeData F F (identity F)) = pr1 (pr1 (pr1 (H F)))). *)
(* simpl. *)
(* apply idpath. *)
  apply (total2_paths (wtf F)).
  simpl.
  unfold wtf.
  apply funextsec.
  intro i.
  now apply id_left.
assert (InitialArrow (COCONE hsD F) (H F) (colimG_Cocone F F (identity F)) ;;
        idtoiso test =
        identity (pr1 (H F))).
  admit.
(* simpl. *)
(* apply idpath. *)

(* (* eapply pathscomp0. *) *)
(* (* eapply maponpaths. *) *)
(* case test.  *)
(* eapply maponpaths. *)
(* rewrite test. *)

(* set (T := coconeEndoId J D F hsD (H F)). *)
(* eapply pathscomp0. *)
(* apply T. *)
(* intros i. *)
(* set (cocF := pr1 _). *)

(* assert (HH : Colimit_univ J D F hsD (H F) (colimG_Cocone F F (identity F)) = identity _). *)


(* eapply pathscomp0. *)
(* eapply maponpaths. *)
(* apply HH. *)
(* apply id_right. *)
(* Defined. *)
admit.
Admitted.

End ColimitFunctor.

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
abstract (intros i j fij; unfold Fi; simpl;
          set (T := CoconeProp_from_Cocone _ _ _ (pr1 (allColimitsD J (F' b))) i j fij);
          eapply pathscomp0; [ | eapply maponpaths; apply T ];
          repeat rewrite assoc;
          apply cancel_postcomposition;
          unfold F'; 
          set (K:=@nat_trans_ax _ _ _ _ (# F fij) a b f);
          apply pathsinv0;
          exact K).
Defined.



Definition colim : functor C D.
Proof.
exists colim_data.
split.
- intro a.
  simpl.
  apply (coconeEndoId' J D (F' a) hsD (allColimitsD J (F' a))).
  intro i;  simpl.

  unfold Colimit_cocone', Colimit_cocone.
set (f := InitialArrow _ _ _).
set (T:=CoconeMor_prop J D (F' a) (pr1 (allColimitsD J (F' a))) _ f i).
eapply pathscomp0.
apply T.
assert (H : (tpair (CoconeProp J D (F' a))
        (tpair (λ a0 : D, ∀ j : J, (F' a) j --> a0)
           (Colimit_ob (allColimitsD J (F' a))) (Fi a a (identity a)))
        (colim_data_subproof a a (identity a))) = pr1 (allColimitsD J (F' a))).
Check (pr1 (pr1 (allColimitsD J (F' a)))).
apply Cocone_eq.
assumption.

simpl.
eapply (total2_paths ). (idpath _)).
apply idpath.

admit.

  
f_equal.

apply idpath.
Set Printing Coercions.
simpl in *.

apply T.

  apply
  simpl.
  
   coconeBottomMor J D (F' a)
     (InitialArrow (COCONE hsD (F' a)) (allColimitsD J (F' a))
        (tpair (CoconeProp J D (F' a))
           (tpair (λ a0 : D, ∀ j : J, (pr1 (F j)) a --> a0)
              (Colimit_ob (allColimitsD J (F' a))) 
              (Fi a a (identity a)))
           (colim_data_subproof a a (identity a))))



     apply id_right.
 apply pathsinv0.
  apply (maponpaths (coconeBottomMor _ _ _) (T (InitialArrow (COCONE hsD (F' a)) (allColimitsD J (F' a))
       (tpair (CoconeProp J D (F' a))
          (tpair (λ a0 : D, ∀ j : J, (F' a) j --> a0)
             (Colimit_ob (allColimitsD J (F' a))) 
             (Fi a a (identity a))) (colim_data_subproof a a (identity a)))))).
    unfold coconeBottomMor.
         
      Search functor_data.
  Check (# colim_data (identity a)).
  set (T:= InitialEndo_is_identity (COCONE hsD (F' a))).
  admit.
- intros a b c f g.
  admit.
Admitted.

(* TODO: Prove that this is a colimit *)

(* Definition colimitFunctor : Colimit F (functor_category_has_homsets
_ _ hsD). *)
(* Proof. *)

  
End ColimitsFunctorCategories.



(*** Old code proving that the category of HSETs has colimits *)

(* Section colimits. *)

(* Variable (J : precategory). *)
(* Variable (F : functor J HSET). *)

(* TODO: Define notation for pr1hSet? Or can we trigger computation so that
   coercion "ob  HSET = hSet :> UU" can be applied? *)
(* Definition cobase : UU := Σ j, pr1hSet (F j). *)

(* (* hprop stuff is in UniMath.Foundations.Propositions *) *)
(* Definition rel0 : hrel cobase := λ (ia jb : cobase), *)
(*   hProppair (ishinh (Σ f : pr1 ia --> pr1 jb, # F f (pr2 ia) = pr2 jb)) *)
(*             (isapropishinh _). *)

(* Definition rel : hrel cobase := eqrel_from_hrel rel0. *)

(* Lemma iseqrel_rel : iseqrel rel. *)
(* Proof. *)
(* now apply iseqrel_eqrel_from_hrel. *)
(* Qed. *)

(* Definition eqr : eqrel cobase := eqrelpair _ iseqrel_rel. *)

(* (* Defined in UniMath.Foundations.Sets *) *)
(* Definition colimit : HSET := *)
(*   hSetpair (setquot eqr) (isasetsetquot _). *)

(* (* *)

(*   (X,~) ---------- *)
(*     |             \ *)
(*     |setquotpr     \ *)
(*     V               \ *)
(*    X/~ -----------> (Y,=) *)

(* *) *)

(* Definition to_cobase (j : J) : pr1hSet (F j) -> cobase. *)
(* Proof. *)
(*   intros Fj. *)
(*   exists j. *)
(*   exact Fj. *)
(*   Defined. *)

(* Definition injections (j : J) : F j --> colimit. *)
(* Proof. *)
(* intros Fj. *)
(* unfold colimit. *)
(* apply (setquotpr _). *)
(* exact (to_cobase j Fj). *)
(* Defined. *)

(* Require Import UniMath.CategoryTheory.colimits.cocones. *)

(* Section cpm. *)

(* Variables (c : Cocone F). *)

(* Definition from_cobase : cobase -> pr1hSet (coconeBottom c). *)
(* Proof. *)
(* intros iA. *)
(* (* destruct iA as [i Fi]. *) *)
(* (* exact (coconeIn _ _ _ c i Fi) *) *)
(* exact ((coconeIn _ _ _ c) (pr1 iA) (pr2 iA)). (* TODO: implicits *) *)
(* Defined. *)

(* Lemma to_cobase_from_cobase (i : J) (A : pr1hSet (F i)) : from_cobase (to_cobase i A) = coconeIn _ _ _ c i A. *)
(* Proof. *)
(* apply idpath. *)
(* Qed. *)
  
(* Definition from_cobase_rel : hrel cobase. *)
(* Proof. *)
(* intros x x'. *)
(* exists (from_cobase x = from_cobase x'). *)
(* apply setproperty. *)
(* Defined. *)

(* Definition from_cobase_eqrel : eqrel cobase. *)
(* Proof. *)
(* exists from_cobase_rel. *)
(* repeat split. *)
(* - intros x y z H1 H2. *)
(*   exact (pathscomp0 H1 H2). *)
(* - intros x y H. *)
(*   exact (pathsinv0 H). *)
(* Defined. *)

(* (* TODO: clean this! *) *)
(* Lemma rel0_impl a b : rel0 a b -> from_cobase_eqrel a b. *)
(* Proof. *)
(* intros H. *)
(* apply H. *)
(* intros H'. *)
(* simpl. *)
(* unfold from_cobase. *)
(* simpl. *)
(* case H'. *)
(* simpl. *)
(* case c. *)
(* simpl. *)
(* intros. *)
(* generalize p0. *)
(* destruct a. *)
(* destruct b. *)
(* simpl in *. *)
(* generalize (p t1 t2 t0). *)
(* intros APA BEPA. *)
(* unfold compose in APA. *)
(* simpl in *. *)
(* rewrite <- BEPA. *)
(* set (T:=toforallpaths _ _ _ APA). *)
(* now rewrite T. *)
(* Qed. *)

(* Lemma test a b : rel a b -> from_cobase_eqrel a b. *)
(* Proof. *)
(* intros H. *)
(* apply (@minimal_eqrel_from_hrel _ rel0). *)
(* apply rel0_impl. *)
(* assumption. *)
(* Qed. *)

(* Lemma iscomprel_from_base : iscomprelfun rel from_cobase. *)
(* Proof. *)
(* intros x x' H. *)
(* apply test. *)
(* assumption. *)
(* Qed. *)

(* Definition from_colimit : colimit --> coconeBottom c. *)
(* Proof. *)
(* unfold colimit; simpl. *)
(* apply (setquotuniv _ _ from_cobase). *)
(* exact iscomprel_from_base. *)
(* Defined. *)

(* End cpm. *)

(* Definition thing0 : CoconeData J HSET F := tpair _ colimit injections. *)

(* Definition thing : COCONE has_homsets_HSET F. *)
(* Proof. *)
(* apply (tpair _ thing0). *)
(* unfold CoconeProp. *)
(* unfold coconeIn. *)
(* simpl. *)
(* intros i j f. *)
(* apply funextfun; intros Fi; simpl. *)
(* unfold compose; simpl. *)
(* unfold injections; simpl. *)
(* apply (weqpathsinsetquot eqr). *)
(* apply (eqrelsymm eqr). *)
(* apply eqrel_impl. *)
(* apply hinhpr; simpl. *)
(* now exists f. *)
(* Defined. *)

(* Definition foo (C : COCONE has_homsets_HSET F) : thing --> C. *)
(* Proof. *)
(* exists (from_colimit C); intro i; simpl. *)
(* unfold injections, compose, from_colimit; simpl. *)
(* apply funextfun; intro Fi. *)
(* rewrite (setquotunivcomm eqr). *)
(* apply to_cobase_from_cobase. *)
(* Defined. *)

(* Definition ColimitF : Colimit F has_homsets_HSET. *)
(* Proof. *)
(* apply (tpair _ thing); intro C. *)
(* exists (foo C); simpl; intro f. *)
(* apply (CoconeMor_eq _ _ has_homsets_HSET). *)
(* simpl. *)
(* apply funextfun; intro x; simpl. *)
(* Search (issurjective _ -> _). *)
(* apply (surjectionisepitosets (setquotpr eqr)). *)
(* apply issurjsetquotpr. *)
(* apply pr2. *)
(* intro y. *)
(* destruct y as [i Fi]. *)
(* generalize (CoconeMor_prop _ _ _ _ _ f i). *)
(* simpl. *)
(* intro H. *)
(* assert (H':=toforallpaths _ _ _ H Fi). *)
(* unfold compose in H'. *)
(* simpl in *. *)
(* eapply pathscomp0. *)
(* apply H'. *)
(* apply idpath. *)
(* Defined. *)

(* End colimits. *)
