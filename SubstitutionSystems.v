Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.
Require Import SubstSystems.UnicodeNotations.
Require Import UniMath.RezkCompletion.whiskering.
Require Import UniMath.RezkCompletion.Monads.
Require Import SubstSystems.Auxiliary.
Require Import SubstSystems.PointedFunctors.
Require Import SubstSystems.ProductPrecategory.
Require Import SubstSystems.HorizontalComposition.
Require Import SubstSystems.PointedFunctorsComposition.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Arguments functor_composite {_ _ _} _ _ .
Arguments nat_trans_comp {_ _ _ _ _} _ _ .
Local Notation "G ∙ F" := (functor_composite F G : [ _ , _ , _ ]) (at level 35).
Local Notation "α ∙∙ β" := (hor_comp β α) (at level 20).
Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Local Notation "Z ∘ α" := (post_whisker _ _ _ _ α Z) (at level 35).

Section def_hss.

(** ** Some variables and assumptions *)

(** Assume having a precategory [C] whose hom-types are sets *)
Variable C : precategory.
Variable hs : has_homsets C.

(** [H] is a rank-2 endofunctor on endofunctors *)
Variable H : functor [C, C, hs] [C, C, hs].

(** The forgetful functor from pointed endofunctors to endofunctors *)
Local Notation "'U'" := (functor_ptd_forget C hs).
(** The precategory of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (precategory_Ptd C hs).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hs]) .
(** The product of two precategories *)
Local Notation "A 'XX' B" := (product_precategory A B) (at level 2).
(** Pre-whiskering defined as morphism part of the functor given by precomposition 
    with a fixed functor *)
Local Notation "α 'øø' Z" :=  (# (pre_composition_functor_data _ _ _ hs _  Z) α) (at level 25).

(** Objects and morphisms in the product precategory of two precategories *)
Definition prodcatpair (X : functor C C) (Z : Ptd) : ob EndC XX Ptd.
Proof.
  exists X.
  exact Z.
Defined.
Local Notation "A ⊗ B" := (prodcatpair A B) (at level 10).
Definition prodcatmor {X X' : EndC} {Z Z' : Ptd} (α : X ⇒ X') (β : Z ⇒ Z') 
  : X ⊗ Z ⇒ X' ⊗ Z'.
Proof.
  exists α.
  exact β.
Defined.

(** ** Source and target of the natural transformation [θ] *)


(** Source is given by [(X,Z) => H(X)∙U(Z)] *)
Definition θ_source_ob (FX : EndC XX Ptd) : [C, C, hs] := H (pr1 FX) ∙ U (pr2 FX).

Definition θ_source_mor {FX FX' : EndC XX Ptd} (αβ : FX ⇒ FX') 
  : θ_source_ob FX ⇒ θ_source_ob FX' := hor_comp (#U (pr2 αβ)) (#H (pr1 αβ)).


Definition θ_source_functor_data : functor_data (EndC XX Ptd) EndC.
Proof.
  exists θ_source_ob.
  exact (@θ_source_mor).
Defined.

Lemma is_functor_θ_source : is_functor θ_source_functor_data.
Proof.
  split; simpl.
  - intro FX.
    apply nat_trans_eq.
    + apply hs.
    + intro c. simpl.
      rewrite functor_id.
      rewrite id_right.
      set (HH:=functor_id H).
      rewrite HH. apply idpath.
  - intros FX FX' FX'' α β.
    apply nat_trans_eq.
    + apply hs.
    + destruct FX as [F X].
      destruct FX' as [F' X'].
      destruct FX'' as [F'' X''].
      intro c ; simpl in *.
      destruct α as [α a].
      destruct β as [β b]. simpl in *.
      rewrite functor_comp.
      set (HH:=functor_comp H).
      rewrite HH; simpl; clear HH.
      repeat rewrite <- assoc.
      apply maponpaths.
      rewrite <- nat_trans_ax.
      destruct a as [a aax].
      destruct b as [b bax]. simpl in *.
      destruct X as [X eta].
      destruct X' as [X' eta'].
      destruct X'' as [X'' eta'']; simpl in *.
      clear aax eta. clear bax eta'. clear eta''.
      set (HHH:=nat_trans_ax (#H β)).
      rewrite <- functor_comp.
      rewrite assoc.
      rewrite <- functor_comp.
      rewrite HHH.
      apply idpath.
Qed.

Definition θ_source : functor _ _ := tpair _ _ is_functor_θ_source.

(** Target is given by [(X,Z) => H(X∙U(Z))] *)

Definition θ_target_ob (FX : EndC XX Ptd) : EndC := H (pr1 FX ∙ U (pr2 FX)).

Definition θ_target_mor (FX FX' : EndC XX Ptd) (αβ : FX ⇒ FX') 
  : θ_target_ob FX ⇒ θ_target_ob FX'
  := #H (pr1 αβ ∙∙ #U(pr2 αβ)).

Definition θ_target_functor_data : functor_data (EndC XX Ptd) EndC.
Proof.
  exists θ_target_ob.
  exact θ_target_mor.
Defined.


Lemma is_functor_θ_target_functor_data : is_functor θ_target_functor_data.
Proof.
  split; simpl.
  - intro FX; simpl.
    unfold θ_target_mor. 
    set (T:= functor_id_id _ _ H).
    apply T; simpl.
    apply nat_trans_eq.
    + apply hs.
    + intro c; simpl.
      rewrite id_left.
      rewrite functor_id.
      apply idpath.
  - intros FX FX' FX''.
    intros α β.
    unfold θ_target_mor.
    set (T:=functor_comp H _ _ _ (pr1 α ∙∙ # U (pr2 α)) (pr1 β ∙∙ # U (pr2 β))).
    simpl in *.
    match goal with |[ H :  ?f = _ |- _ ] => transitivity f end.
(*    etransitivity. *)
    Focus 2.
      apply T. 
    apply maponpaths. clear T.
    simpl.
    destruct α as [α a].
    destruct β as [β b]; simpl in *.
    apply nat_trans_eq.
    + apply hs.
    + intro c.
      unfold hor_comp; simpl.
      destruct FX as [F X];
      destruct FX' as [F' X'];
      destruct FX'' as [F'' X'']; simpl in *.
      repeat rewrite <- assoc. apply maponpaths.
      rewrite <- (nat_trans_ax β ((pr1 X') c)).
      rewrite assoc.
      rewrite <- functor_comp.
      rewrite nat_trans_ax.
      apply idpath.
Qed.      

Definition θ_target : functor _ _ := tpair _ _ is_functor_θ_target_functor_data.

(** We assume a suitable (bi)natural transformation [θ] *)
Hypothesis θ : θ_source ⟶ θ_target.

(** [θ] is supposed to satisfy two strength laws *)

Definition θ_Strength1 : UU := ∀ X : EndC,  
  (θ (X ⊗ (id_Ptd C hs))) ;; # H (identity X : functor_composite (functor_identity C) X ⟶ pr1 X) 
          = nat_trans_id _ .

Hypothesis θ_strength1 : θ_Strength1.

Definition θ_Strength2 : UU := ∀ (X : EndC) (Z Z' : Ptd) (Y : EndC)
           (α : functor_compose hs hs (functor_composite (U Z) (U Z')) X ⇒ Y),
    θ (X ⊗ (ptd_composite _ Z Z')) ;; # H α =
    θ (X ⊗ Z') øø (U Z) ;; θ ((functor_compose hs hs (U Z') X) ⊗ Z) ;; 
       # H (α : functor_compose hs hs (U Z) (functor_composite (U Z') X) ⇒ Y).

Hypothesis θ_strength2 : θ_Strength2.


(** Not having a general theory of binatural transformations, we isolate 
    naturality in each component here *)

Lemma θ_nat_1 (X X' : EndC) (α : X ⇒ X') (Z : Ptd) 
  : compose(C:=EndC) (# H α ∙∙ nat_trans_id (pr1 (U Z))) (θ (X' ⊗ Z)) =
        θ (X ⊗ Z);; # H (α ∙∙ nat_trans_id (pr1 (U Z))).
Proof.
  set (t:=nat_trans_ax θ).
  set (t':=t (X ⊗ Z) (X' ⊗ Z)).
  set (t'':= t' (prodcatmor α (identity _ ))).
  simpl in t''.
  exact t''.
Qed.

(* the following makes sense but is wrong
Lemma θ_nat_1' (X X' : EndC) (α : X ⇒ X') (Z : Ptd) 
  : compose(C:=EndC) (# H α øø (U Z)) (θ (X' ⊗ Z)) =
        θ (X ⊗ Z);; # H (α øø (U Z)).
Proof.
  admit.
Qed.
*)

Lemma θ_nat_1_pointwise (X X' : EndC) (α : X ⇒ X') (Z : Ptd) (c : C)
  :  pr1 (# H α) ((pr1 Z) c);; pr1 (θ (X' ⊗ Z)) c =
       pr1 (θ (X ⊗ Z)) c;; pr1 (# H (α ∙∙ nat_trans_id (pr1 Z))) c.
Proof.
  set (t := θ_nat_1 _ _ α Z).
  set (t' := nat_trans_eq_weq _ _ hs _ _ _ _ t c);
  clearbody t';  simpl in t'.
  set (H':= functor_id (H X') (pr1 (pr1 Z) c));
  clearbody H'; simpl in H'.
  match goal with |[H1 : ?f ;; _ ;; ?g = _ , H2 : ?x = _ |- _ ] =>
                        transitivity (f ;; x ;; g) end.
  - repeat rewrite <- assoc. 
    apply maponpaths.
    rewrite H'.
    apply pathsinv0, id_left.
  - apply t'.
Qed.

Lemma θ_nat_2 (X : EndC) (Z Z' : Ptd) (f : Z ⇒ Z')
  : compose (C:=EndC) (identity (H X) ∙∙ pr1 f) (θ (X ⊗ Z')) =
       θ (X ⊗ Z);; # H (identity X ∙∙ pr1 f).
Proof.
  set (t := nat_trans_ax θ).
  set (t' := t (prodcatpair X Z) (prodcatpair X Z') (prodcatmor (identity _ ) f)).
  simpl in t'.
  unfold θ_source_mor in t'.
  unfold θ_target_mor in t'.
  simpl in t'.
  set (T := functor_id H X).
  simpl in *.
  rewrite T in t'. clear T.
  exact t'.
Qed.

Lemma θ_nat_2_pointwise (X : EndC) (Z Z' : Ptd) (f : Z ⇒ Z') (c : C)
  :  # (pr1 (H X)) ((pr1 f) c);; pr1 (θ (X ⊗ Z')) c =
       pr1 (θ (X ⊗ Z)) c;; pr1 (# H (identity X ∙∙ pr1 f)) c .
Proof.
  set (t:=θ_nat_2 X _ _ f).
  set (t':=nat_trans_eq_weq _ _ hs _ _ _ _ t c).
  clearbody t'; clear t.
  simpl in t'.
  rewrite id_left in t'.
  exact t'.
Qed.

(** ** Definition of algebra structure [τ] of a pointed functor *)

Definition AlgStruct (T : Ptd) : UU := pr1 (H(U T)) ⟶ pr1 (U T).

Definition Alg : UU := Σ T : Ptd, AlgStruct T.

Coercion PtdFromAlg (T : Alg) : Ptd := pr1 T.

Definition τ (T : Alg) : pr1 (H (U T)) ⟶ pr1 (U T) := pr2 T.



Definition bracket (T : Alg) : UU := 
  ∀ (Z : Ptd) (f : Z ⇒ T), iscontr 
   (Σ h : (U T) ∙ (U Z)  ⇒ U T,
     (#U f = (ptd_pt _ (pr1 T)) øø (U Z) ;; h) ×
     (θ (U T ⊗ Z) ;; #H h ;; τ _  = τ _ øø ((U Z)) ;;  h )).

Definition hss : UU := Σ T : Alg, bracket T.

Coercion AlgFromhss (T : hss) : Alg := pr1 T.

Definition fbracket (T : hss) {Z : Ptd} (f : Z ⇒ T) 
  : (U T) ∙ (U Z) ⇒ U T
  := pr1 (pr1 (pr2 T Z f)).

(** The bracket operation [fbracket] is unique *)

Definition fbracket_unique_pointwise (T : hss) {Z : Ptd} (f : Z ⇒ T) 
  : ∀ (α : functor_composite (U Z)(U T) ⟶ pr1 (U T)),
     (∀ c : C, pr1 (#U f) c = ptd_pt _ (pr1 (pr1 T)) (pr1 (U Z) c) ;; α c) →
     (∀ c : C, pr1 (θ (U T ⊗ Z))  c ;; pr1 (#H α) c ;; τ _ c = 
        τ _ (pr1 (U Z) c) ;; α c) → α = fbracket T f.
Proof.
  intros α H1 H2.
  apply path_to_ctr.
  split; apply nat_trans_eq; assumption.
Qed.

Definition fbracket_unique (T : hss) {Z : Ptd} (f : Z ⇒ T) 
  : ∀ α : functor_composite (U Z)(U T) ⟶ pr1 (U T),
     (#U f = ptd_pt _ (pr1 (pr1 T)) øø ((U Z)) ;; α) →
     (θ (U T ⊗ Z) ;; #H α ;; τ _ = τ _ øø (U Z) ;; α) 
   → α = fbracket T f.
Proof.
  intros α H1 H2.
  apply path_to_ctr.
  split;  assumption.
Qed.

Definition fbracket_unique_target_pointwise (T : hss) {Z : Ptd} (f : Z ⇒ T) 
  : ∀ α : functor_composite (U Z)(U T) ⟶ pr1 (U T),
     (#U f =  (ptd_pt _ ((pr1 (pr1 T)))) øø U Z ;; α) →
     (θ (U T ⊗ Z) ;; #H α ;; τ _ = τ _ øø U Z ;; α) 
   → ∀ c, α c = pr1 (fbracket T f) c.
Proof.
  intros α H1 H2.
  set (t:= fbracket_unique _ _ α H1 H2).
  apply (nat_trans_eq_weq _ _ hs _ _ _ _ t).
Qed.

(** Properties of [fbracket] by definition: commutative diagrams *)

Lemma fbracket_η (T : hss) : ∀ {Z : Ptd} (f : Z ⇒ T),
   #U f = (ptd_pt _  (pr1 (pr1 T))) øø U Z ;;  (fbracket T f).
Proof.
  intros Z f.
  exact (pr1 (pr2 (pr1 (pr2 T Z f)))).
Qed.

Lemma fbracket_τ (T : hss) : ∀ {Z : Ptd} (f : Z ⇒ T),
    θ (U T ⊗ Z) ;; #H (fbracket T f) ;; τ _  
    = 
    τ _ øø U Z ;; (fbracket T f).
Proof.
  intros Z f.
  exact (pr2 (pr2 (pr1 (pr2 T Z f)))).
Qed.

(** [fbracket] is also natural *)

Lemma fbracket_natural (T : hss) {Z Z' : Ptd} (f : Z ⇒ Z') (g : Z' ⇒ T) 
  : post_whisker _ _ _ _ (#U f)(U T) ;; fbracket T g = fbracket T (f ;; g).
Proof.
  apply fbracket_unique_pointwise.
  - simpl. intro c.
    set (H':=nat_trans_ax (ptd_pt _ (pr1 (pr1 T)) )).
    rewrite assoc.
    simpl in H'.
    rewrite <- H'.
    rewrite <- assoc.
    apply maponpaths.
    set (X:= nat_trans_eq_weq _ _ hs _ _ _ _  (fbracket_η T g)).
    simpl in X. exact (X _ ).
  - intro c; simpl.
    set (H':=nat_trans_ax (τ T)).
    simpl in H'.
    rewrite assoc.
    rewrite <- H'; clear H'.
    set (H':=fbracket_τ T g).
    simpl in H'.
    set (X:= nat_trans_eq_pointwise _ _  _ _ _ _ H' c).
    simpl in X.
    rewrite  <- assoc.
    rewrite  <- assoc.
    simpl in *.
    transitivity (  # (pr1 (H ((U T)))) (pr1 (pr1 f) c) ;;
                     (pr1 (θ (prodcatpair (U T) Z')) c);; pr1 (# H (fbracket T g)) c;; (τ T) c).
    Focus 2.
      rewrite <- assoc.
      rewrite <- assoc.
      apply maponpaths.
      repeat rewrite assoc.
      apply X.
    clear X.
    set (A:=θ_nat_2_pointwise).
    simpl in *.
    set (A':= A (U T) Z Z').
    simpl in A'.
    set (A2:= A' f).
    clearbody A2; clear A'; clear A.
    rewrite A2; clear A2.
    repeat rewrite <- assoc.
    apply maponpaths.
    simpl.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    set (A := functor_comp H).
    simpl in A.
    rewrite A.
    apply cancel_postcomposition.
    clear A. clear H'.
    set (A:=horcomp_id_postwhisker C _ _ hs hs).
    rewrite A.
    apply idpath.
Qed.

(** As a consequence of naturality, we can compute [fbracket f] from [fbracket identity] *)

Lemma compute_fbracket (T : hss) : ∀ {Z : Ptd} (f : Z ⇒ T),
  fbracket T f = post_whisker _ _ _ _ (#U f)(U T) ;; fbracket T (identity _ ). 
Proof.
  intros Z f.
  assert (A : f = f ;; identity _ ).
  { rewrite id_right; apply idpath. }
  rewrite A.
  rewrite <- fbracket_natural.
  rewrite id_right.
  apply idpath.
Qed.


(** ** Derivation of the monad laws from a heterogeneous substitution system *)

Section mu_from_fbracket.

(** We assume given a hss [T] *)

Variable T : hss.

Local Notation "'η'" := (ptd_pt _ (pr1 (pr1 T))).

Definition μ_0 : functor_identity C ⟶ pr1 (U T) := η. (*ptd_pt _ (pr1 (pr1 T)).*)

Definition μ_0_ptd : id_Ptd C hs ⇒ T.
Proof.
  exists μ_0.
  intro c. simpl. apply id_left.
Defined.

Definition μ_1 : functor_composite (U (id_Ptd C hs)) (U T) ⟶ pr1 (U T) 
  := fbracket _ μ_0_ptd.

(*

Lemma μ_1_alt_is_nat_trans:
 is_nat_trans (functor_composite (U id_Ptd) (U T)) 
     (pr1 (U T)) (λ c : C, identity ((functor_composite (U id_Ptd) (U T)) c)).
Proof.
  unfold is_nat_trans; simpl; intros.
  rewrite id_right.
  rewrite id_left.
  apply idpath.
Qed.

Definition μ_1_alt : functor_composite (U id_Ptd) (U T) ⟶ pr1 (U T).
Proof.
  exists (λ c, identity _ ).
  apply μ_1_alt_is_nat_trans.
Defined.

*)

(*
Lemma equal_to_identity (a b : C) (f : a ⇒ a) (g g' : a ⇒ b) : 
   f = identity _ → g = g' → f ;; g = g'.
Proof.
  intros.
  subst.
  apply id_left.
Qed.
*)

(*
Lemma μ_1_identity' : μ_1_alt = μ_1.
Proof.
  apply fbracket_unique_pointwise.
  - intros; simpl.
    rewrite id_right.
    apply idpath.
  - intros; simpl.
    rewrite id_right.
    
   (* assert (H2 :  pr1 (θ ((U T) ⊗ id_Ptd)) c = identity _ ).*)
    assert (H':pr1 (θ (prodcatpair (U (pr1 T)) id_Ptd)) c;; pr1 (# H μ_1_alt) c = identity _ ).
    
    { admit. } (* should be given by hypothesis on θ *) 
    apply equal_to_identity.
    + apply H'.
    + apply idpath.
Qed.
*)
Lemma μ_1_identity : μ_1 = identity (U T) .
Proof.
  apply pathsinv0.
  apply fbracket_unique.
  - apply nat_trans_eq; try assumption.
    intros; simpl.
    rewrite id_right.
    apply idpath.
  - apply nat_trans_eq; try assumption.
    intro c. simpl.
    rewrite id_right.
    assert (H':= θ_strength1). 
    red in H'. simpl in H'.
    assert (H2 := H' (U T)).
    assert (H3 := nat_trans_eq_pointwise _ _ _ _ _ _ H2 c).
    simpl in *.
    rewrite H3.
    apply id_left.
Qed.


Lemma μ_1_identity' : ∀ c : C, μ_1 c = identity _.
Proof.
  intros c.
  assert (HA:= nat_trans_eq_pointwise _ _ _ _ _ _ μ_1_identity).
  apply HA.
Qed.

(* The whole secret is that this typechecks
  Check (μ_1:U T⇒U T).
*)

(* therefore, it is not just the type itself that makes it necessary to introduce μ_1_alt,
   it is rather the question of the formulation of the first strength law of θ *)

(*
Lemma μ_1_identity_stronger : μ_1 = identity (U T).
Proof.
  set (t':=nat_trans_eq_weq C C hs _ _ μ_1 (identity (U T))).
  apply invweq in t'.
  set (t'' := t' μ_1_identity').
  exact t''.
Qed.
*)

(** This is the multiplication of the monad to be constructed *)

Definition μ_2 : functor_composite (U T) (U T) ⟶ pr1 (U T) 
  := fbracket T (identity _ ).


Definition functor_with_mu_from_hss : functor_with_μ C.
Proof.
  exists (U T).
  exact μ_2.
Defined.

Definition Monad_data_from_hss : Monad_data C.
Proof.
  exists functor_with_mu_from_hss.
  exact μ_0.
Defined.

(** *** Proof of the first monad law *)

Lemma Monad_law_1_from_hss :
  ∀ c : C, μ_0 (pr1 (U T) c);; μ_2 c = identity ((pr1 (U T)) c).
Proof.
  intro c. 
  unfold μ_2. simpl.
  unfold μ_0. simpl.
  set (H':=fbracket_η T (identity _) ).
  set (H2:= nat_trans_eq_weq _ _ hs _ _ _ _ H').
  simpl in H2.
  apply pathsinv0.
  apply H2.
Qed.

(** *** Proof of the second monad law *)

Lemma Monad_law_2_from_hss:
  ∀ c : C, # (pr1 (U T)) (μ_0 c);; μ_2 c = identity ((pr1 (U T)) c).
Proof.
 intro c.
      transitivity (μ_1 c).
      * unfold μ_1.
        set (H':= fbracket_unique_target_pointwise).
        set (H1:= H' _ _ μ_0_ptd).
        set (x:= post_whisker _ _ _ _ μ_0 (U T)).
        set (x':= x ;; μ_2).
        set (H2 := H1 x').
        apply H2; clear H2.
        unfold x'. clear x'.
        unfold x; clear x.
        clear H1. clear H'. clear c.
        simpl.
        apply nat_trans_eq; simpl.
         apply hs.
         intro c.
         set (H':=nat_trans_ax (ptd_pt _ (pr1 (pr1 T)))).
         simpl in H'.
         rewrite assoc.
         rewrite <- H'; clear H'.
         set (H':= fbracket_η T (identity _ )).
         unfold μ_2.
         set (H2 := nat_trans_eq_weq _ _ hs _ _ _ _ H').
         simpl in H2.
         rewrite <- assoc.
         rewrite <- H2.
         rewrite id_right.
         apply idpath. (* done *)

         unfold x'; clear x'.
         unfold x; clear x.
         clear H1. clear H'.
         set (H':=θ_nat_2).
         set (H2 := H' (U T) _ _ μ_0_ptd).
         simpl in H2.
         rewrite functor_comp.
         apply nat_trans_eq; try assumption.
         clear c.
         intro c; simpl.
         set (H3:= nat_trans_eq_weq _ _ hs _ _ _ _ H2 c).
         simpl in H3.
         rewrite id_left in H3.
         rewrite <- horcomp_id_postwhisker.
         repeat rewrite assoc.
         simpl in *.
         transitivity ( # (pr1 (H ( (U T)))) (μ_0 c);; pr1 (θ (prodcatpair (U T) T)) c ;; 
                           pr1 (# H μ_2) c ;; (τ T) c).
           apply cancel_postcomposition.
           apply cancel_postcomposition.
           apply (!H3). (* done *)
           
           clear H3 H2 H'.
           set (H':= fbracket_τ T (identity _ )).
           unfold μ_2.
           simpl.
           set (H2:= nat_trans_eq_weq _ _ hs _ _ _ _ H' c).
             clearbody H2.
           simpl in *.
           repeat rewrite <- assoc.
           transitivity (  # (pr1 (H (U T))) (μ_0 c);;
                             (pr1 (τ T) (pr1 (U T) c);; pr1 (fbracket T (identity T)) c)).
             apply maponpaths.
             rewrite assoc.
             apply H2; clear H2. (* rewrite done *)
            
           clear H2 H'.
           repeat rewrite assoc.
           apply cancel_postcomposition.  
           
           
           set (H':=nat_trans_ax (τ T) ).
           rewrite H'.
           apply idpath.
    * apply μ_1_identity'.
Qed.

(** [T_squared] is [T∙T, η∙η], that is, the selfcomposition of [T] as a pointed functor *)

Definition T_squared : Ptd.
Proof.
  exact (ptd_composite _ (pr1 (pr1 T)) (pr1 (pr1 T))).
Defined.

(** [μ_2] is not just a natural transformation from [T∙T] to [T], but also compatible with 
    the pointed structure given by [η] *)

Lemma μ_2_is_ptd_mor :
  ∀ c : C, (ptd_pt C T_squared) c;; μ_2 c = (ptd_pt C (pr1 (pr1 T))) c.
Proof.
  intro c.
  unfold μ_2.
  unfold T_squared. simpl.
  set (H':=Monad_law_2_from_hss c).
  simpl in H'.
  transitivity (η c ;; identity _ ).
  - repeat rewrite <- assoc.
    apply maponpaths.
    apply H'.
  - apply id_right.
Qed.

Definition μ_2_ptd : T_squared ⇒ T.
Proof.
  exists μ_2.
  apply μ_2_is_ptd_mor.
Defined.

Definition μ_3 : U T_squared ∙ U T ⇒ U T := fbracket T μ_2_ptd.

(*
Definition μ_3' := fbracket T μ_2_ptd.
Check μ_3'.
Check (μ_3' = μ_3).
*)

(** *** Proof of the third monad law via transitivity *)
(** We show that both sides are equal to [μ_3 = fbracket μ_2] *)

Lemma μ_3_T_μ_2_μ_2 : μ_3 = (U T) ∘ μ_2 ;; μ_2.
Proof.
  apply pathsinv0.
  set (H1 := @fbracket_unique T _ μ_2_ptd).
  apply H1; clear H1.
  - apply nat_trans_eq; try assumption.
    intro c; simpl.
    assert (H2 := nat_trans_ax η); simpl in H2.
    rewrite assoc.
    rewrite <- H2.
    assert (H3 := Monad_law_1_from_hss).
    rewrite <- assoc.
    transitivity (μ_2 c ;; identity _ ).
    + rewrite id_right; apply idpath.
    + apply maponpaths.
      apply pathsinv0. apply H3.
  - rewrite functor_comp.
    assert (H1 := θ_nat_2 (U T) _ _ μ_2_ptd).
    set (H3:=horcomp_id_postwhisker).
    assert (H4 := H3 _ _ _ hs hs _ _ μ_2 (U T)); clear H3.
    simpl in H1.
    repeat rewrite assoc.
    match goal with |[H1 : ?g = _ |- _ ;; _ ;; ?f ;; ?h = _ ] => 
         transitivity (g ;; f ;; h) end.
    + apply cancel_postcomposition.
      apply cancel_postcomposition.
      apply pathsinv0.
      rewrite H1.
      apply maponpaths.
      apply maponpaths.
      apply H4.
    + 
      assert (H2 := @fbracket_τ T _ (identity _ )).
      clear H1 H4.
      apply nat_trans_eq; try assumption.
      intro c; simpl.
      rewrite id_left.
      assert (H3:= nat_trans_eq_pointwise _ _ _ _ _ _ H2 c); clear H2.
      simpl in *.
      match goal with |[H3 : _ = ?f |- ?e ;; _ ;; _ ;; _  = _ ] =>
         transitivity (e ;; f) end.
      * repeat rewrite <- assoc.
        apply maponpaths.
        repeat rewrite <- assoc in H3.
        apply H3.
      * repeat rewrite assoc.
        apply cancel_postcomposition.
        set (H1 := nat_trans_ax (τ T )).
        apply H1.
Qed.

Local Notation "'T∙T²'" := (functor_compose hs hs (functor_composite (U T) (U T)) (U T) : [C, C, hs]).
(*
Definition TtimesTthenT': [C, C] hs := functor_compose hs hs (functor_composite (U T) (U T)) (U T).
*)


Local Notation "'T²∙T'" := (@functor_composite C C C 
                    (@functor_composite C C C ((functor_ptd_forget C hs) T)
                                              ((functor_ptd_forget C hs) T))
                    ((functor_ptd_forget C hs) T) : functor C C).
(*
Definition TtimesTthenT: functor C C := @functor_composite C C C 
                    (@functor_composite C C C ((functor_ptd_forget C hs) T)
                                              ((functor_ptd_forget C hs) T))
                    ((functor_ptd_forget C hs) T).
*)
Lemma μ_3_μ_2_T_μ_2 :  (
    @compose (functor_precategory C C hs)
                 (* TtimesTthenT *) T²∙T _ _
                 (* (@functor_composite C C C ((functor_ptd_forget C hs) T)
                    ((functor_ptd_forget C hs) T))
                 ((functor_ptd_forget C hs) T) *)
          ((μ_2 øø U T) (* :  TtimesTthenT' ⇒ _ *)
                  (*:@functor_compose C C C hs hs 
                    (@functor_composite C C C ((functor_ptd_forget C hs) T)
                                              ((functor_ptd_forget C hs) T))
                    ((functor_ptd_forget C hs) T) ⇒ _*) ) μ_2 : 
            (*TtimesTthenT'*) T∙T² ⇒ U T) = μ_3.
  unfold μ_3.
  set (H1 := @fbracket_unique (*_pointwise*) T _ μ_2_ptd).
  apply H1; clear H1.
  - simpl.
    apply nat_trans_eq; try assumption; intro c.
    simpl.
    set (H1 := Monad_law_1_from_hss (pr1 (U T) c)).
    simpl in H1.
    rewrite assoc.
    unfold μ_0 in H1.
    transitivity (identity _ ;; μ_2 c).
    + rewrite id_left; apply idpath.
    + apply cancel_postcomposition.
      apply (!H1).
  - 
    
    set (A:=θ (U T ⊗ T_squared)).
    set (B:= τ T).
    match goal with | [|- _ = ?q] => set (Q:=q) end.
    match goal with | [|- _ ;; # ?H (?f ;; _ ) ;; _ = _ ] => set (F:=f : (*TtimesTthenT'*) T∙T² ⇒ _ ) end.
    set (HX:=θ_nat_1 _ _ μ_2).  (* it may be tested with the primed version *)
    set (H3:= functor_comp H _ _ _ F μ_2).
    unfold functor_compose in H3.
    match goal with | [ H' : ?f = _ |- _ ] => transitivity (A ;; f ;; B) end.
    + apply idpath.
    + rewrite H3.
      clear H3.
      set (A':= θ ((U T) ⊗ T) øø U T ;; θ ((functor_compose hs hs (U T) (U T)) ⊗ T)). 
      simpl in *.
      
      apply nat_trans_eq; try assumption.
      intro c. simpl.
      unfold A.
      simpl.
      set (A'c := A' c).
      simpl in *.
      
      clear A Q.
      match goal with | [ |- ?a ;; _ ;; _ = _ ] => set (Ac:= a) end.
      
      simpl in Ac.
      unfold θ_target_ob in *.
      simpl in *.
      unfold functor_compose in *.
      set (HX1:= HX (pr1 (pr1 T))).
      simpl in HX1.
      assert (HXX:=nat_trans_eq_pointwise _ _ _ _ _ _ HX1 c).
      clear HX1. clear HX.
      simpl in HXX.
      rewrite (functor_id ( H (U T))) in HXX.
      rewrite id_right in HXX. (* last two lines needed because of def. of theta on product category *)
      match goal with |[HXX : ?f ;; ?h = _ ;; _ |- _ ;; (_ ;; ?x ) ;; ?y = _ ] =>
      transitivity (pr1 (θ ((U T) ⊗ T)) (pr1 (pr1 (pr1 T)) c);;
                       f  ;; h ;; x;; y) end.
      * repeat rewrite assoc.
        apply cancel_postcomposition.
        apply cancel_postcomposition.
        unfold Ac.
        simpl.
        
        
(*
        unfold F.
        match goal with |[ H : _ = ?b ;; ?c |- _ = ?a ;; _ ;; _  ] => 
             transitivity ( a ;; (b ;; c)) end.
          repeat rewrite <- assoc.
         
          match goal with |[|- _ ;;  ((# ?H) ?f) _ = _ ] => set (E:=f) end.
*)          
          assert (Strength_2 : ∀ α : functor_compose hs hs (functor_composite (U T) (U T))(U T) ⇒ functor_composite (U T) (U T),
                       
                    pr1 (θ (U T ⊗ T_squared)) c ;; pr1 (# H α) c =
                     pr1 (θ ((U T) ⊗ T)) ((pr1 (pr1 (pr1 T))) c);;
                     pr1 (θ ((functor_composite (U T) (U T)) ⊗ (pr1 (pr1 T)))) c;;
                     pr1 (# H (α : functor_compose hs hs (U T) (functor_composite (U T) (U T))⇒ _)) c       ).
             {  intro α. 
                assert (HA := θ_strength2). red in HA. simpl in HA.
                assert (HA':= HA (U T) (pr1 (pr1 T)) (pr1 (pr1 T)) _ α).
                assert (HA2 := nat_trans_eq_pointwise _ _ _ _ _ _  HA' c ).
                simpl in HA2.
                apply HA2.
              }  
               
         (*
         assert (Strength_2' : ∀ α : functor_compose hs hs (functor_composite (U T) (U T))(U T) ⇒ functor_composite (U T) (U T),
                               ∀ β : _ ,
                        α = β → 
                    pr1 (θ (U T ⊗ T_squared)) c ;; pr1 (# H α) c =
                     pr1 (θ ((U T) ⊗ T)) ((pr1 (pr1 (pr1 T))) c);;
                     pr1 (θ ((functor_composite (U T) (U T)) ⊗ (pr1 (pr1 T)))) c;;
                     pr1 (# H (β : functor_compose hs hs (U T) (functor_composite (U T) (U T))⇒ _ )) c       ).
             admit. *)
(*
         fold TtimesTthenT' in Strength_2. (*, Strength_2' .*)
*)
         rewrite <- assoc.
         match goal with |[ HXX : ?a ;; ?b = _ |- _ = ?e ;; _] => 
             transitivity (e ;; (a ;; b)) end.
           Focus 2.
             apply idpath.

           rewrite HXX.
           clear HXX.

           rewrite assoc.
           assert (HS :=  Strength_2 F). 
           match goal with |[ H : ?a ;; ?b = _ ;; _ ;; _ |- _ ] => 
             transitivity (a ;; b) end.
           apply idpath. 
           rewrite HS.
           clear HS.
          
           repeat rewrite <- assoc.
           apply maponpaths.
           apply maponpaths.
           
           match goal with |[ |- _ = ?pr1 (# ?G ?g) _ ] =>
              assert (X : F = g) end.
           { apply nat_trans_eq. assumption.
             intros. unfold F.
             simpl.
             rewrite functor_id.
             rewrite id_right.
             apply idpath.
           }
              rewrite X.
              apply idpath.
  
    * set (H4 := fbracket_τ).
      set (H4':= H4 T T (identity _ )).
      set (H5:= nat_trans_eq_pointwise _ _ _ _ _ _ H4' (c)). 
      simpl in H5.
      unfold μ_2.
      unfold B.
      clearbody H5; clear H4'; clear H4; clear HXX.
      
      match goal with |[ H5 : _ = ?e |- ?a ;; ?b ;; _ ;; _ ;; _ = _ ] => 
            transitivity (a ;; b ;; e) end.
       
        repeat rewrite <- assoc.
        apply maponpaths.
        apply maponpaths.
        repeat rewrite assoc; repeat rewrite assoc in H5; apply H5.
        
        repeat rewrite assoc.
        apply cancel_postcomposition.
        
        set (HT := fbracket_τ).
        set (HT':= HT T T (identity _ )).
        set (H6:= nat_trans_eq_pointwise _ _ _ _ _ _ HT'). 
        
        apply H6.
Qed.      
    
 


Check μ_3_μ_2_T_μ_2.


Unset Printing All.
Set Printing Notations.
Unset Printing Implicit.

(** Finally putting together all the preparatory results to obtain a monad *)

Lemma Monad_laws_from_hss : Monad_laws Monad_data_from_hss.
Proof.
  split.
  - unfold Monad_data_from_hss; simpl; split.
    + apply Monad_law_1_from_hss.
    + apply Monad_law_2_from_hss.

  - unfold Monad_data_from_hss; simpl.
    intro c.
    transitivity (pr1 μ_3 c).
    + set (H1 := μ_3_T_μ_2_μ_2).
      set (H2 := nat_trans_eq_weq _ _ hs _ _ _ _ H1).
      apply pathsinv0, H2.
    + set (H1 :=  μ_3_μ_2_T_μ_2).
      set (H2 := nat_trans_eq_weq _ _ hs _ _ _ _ H1).
      apply pathsinv0, H2.
Qed.

Definition Monad_from_hss : Monad C.
Proof.
  exists Monad_data_from_hss.
  exact Monad_laws_from_hss.
Defined.

End mu_from_fbracket.

(** ** Morphisms of heterogeneous substitution systems *)

Section hss_morphisms.

(** A morphism [f] of pointed functors is an algebra morphism when... *)

Definition isAlgMor {T T' : Alg} (f : T ⇒ T') : UU :=
   #H (# U f) ;; τ T' =  compose (C:=EndC) (τ T) (#U f).

Lemma isaprop_isAlgMor (T T' : Alg) (f : T ⇒ T') : isaprop (isAlgMor f).
Proof.
  apply isaset_nat_trans.
  apply hs.
Qed.

(** A morphism [β] of pointed functors is a bracket morphism when... *)

Definition isbracketMor {T T' : hss} (β : T ⇒ T') : UU :=
    ∀ (Z : Ptd) (f : Z ⇒ T), 
       fbracket _ f ;; #U β
       = 
       (#U β)øø (U Z) ;; fbracket _ (f ;; β ).


Lemma isaprop_isbracketMor (T T':hss) (β : T ⇒ T') : isaprop (isbracketMor β).
Proof.
  do 2 (apply impred; intro).
  apply isaset_nat_trans.
  apply hs.
Qed.

(** A morphism of hss is a pointed morphism that is compatible with both 
    [τ] and [fbracket] *)

Definition ishssMor {T T' : hss} (β : T ⇒ T') : UU 
  :=  isAlgMor β × isbracketMor β.
  
Definition hssMor (T T' : hss) : UU 
  := Σ β : T ⇒ T', ishssMor β.

Coercion ptd_mor_from_hssMor (T T' : hss) (β : hssMor T T') : T ⇒ T' := pr1 β.

Definition isAlgMor_hssMor {T T' : hss} (β : hssMor T T') 
  : isAlgMor β := pr1 (pr2 β).
Definition isbracketMor_hssMor {T T' : hss} (β : hssMor T T') 
  : isbracketMor β := pr2 (pr2 β).

(** **** Equality of morphisms of hss *)

Section hssMor_equality.

(** Show that equality of hssMor is equality of underlying nat. transformations *)

Variables T T' : hss.
Variables β β' : hssMor T T'.
Definition hssMor_eq1 : β = β' ≃ (pr1 β = pr1 β').
Proof.
  apply total2_paths_isaprop_equiv.
  intro γ.
  apply isapropdirprod.
  - apply isaprop_isAlgMor.
  - apply isaprop_isbracketMor.
Defined.


Definition hssMor_eq : β = β' ≃ #U β = #U β'.
Proof.
  eapply weqcomp.
  - apply hssMor_eq1.
  - apply eq_ptd_mor.
    apply hs.
Defined.

End hssMor_equality.

Lemma isaset_hssMor (T T' : hss) : isaset (hssMor T T').
Proof.
  intros β β'.
  apply (isofhlevelweqb _ (hssMor_eq _ _ β β')).
  apply isaset_nat_trans.
  apply hs.
Qed.

(** ** The precategory of hss *)

Section hss_precategory.

(** *** Identity morphism of hss *)

Lemma ishssMor_id (T : hss) : ishssMor (identity T).
Proof.
  split.
  - unfold isAlgMor.
    rewrite functor_id.
    rewrite functor_id.
    rewrite id_left.
    set (H2 := id_right ([C,C,hs])).
    symmetry. apply H2.
  - unfold isbracketMor.
    intros Z f.
    rewrite functor_id.
    rewrite id_right.
    rewrite id_right.
    set (H2:=pre_composition_functor _ _ C _ hs (U Z)).
    set (H2' := functor_id H2). simpl in H2'.
    simpl.
    rewrite H2'.
    rewrite (id_left EndC).
    apply idpath.
Qed.

Definition hssMor_id (T : hss) : hssMor _ _ := tpair _ _ (ishssMor_id T).
  
(** *** Composition of morphisms of hss *)

Lemma ishssMor_comp {T T' T'' : hss} (β : hssMor T T') (γ : hssMor T' T'') 
  : ishssMor (β ;; γ).
Proof.
  split.
  - unfold isAlgMor.
    rewrite functor_comp.
    rewrite functor_comp.
    rewrite <- assoc.
    rewrite isAlgMor_hssMor.
    rewrite assoc.
    rewrite isAlgMor_hssMor.
    apply pathsinv0, assoc.
  - unfold isbracketMor.
    intros Z f.
    rewrite functor_comp.
    rewrite assoc.
    rewrite isbracketMor_hssMor.
    rewrite <- assoc.
    set (H2:=functor_comp (pre_composition_functor _ _ C _ hs (U Z)) ).
    simpl in H2.
    simpl.
    rewrite H2; clear H2.
    rewrite <- (assoc EndC).
    apply maponpaths.
    rewrite (assoc Ptd).
    apply isbracketMor_hssMor.
Qed.

Definition hssMor_comp {T T' T'' : hss} (β : hssMor T T') (γ : hssMor T' T'') 
  : hssMor T T'' := tpair _ _ (ishssMor_comp β γ).

Definition hss_obmor : precategory_ob_mor.
Proof.
  exists hss.
  exact hssMor.
Defined.

Definition hss_precategory_data : precategory_data.
Proof.
  exists hss_obmor.
  split.
  - exact hssMor_id.
  - exact @hssMor_comp.
Defined.

Lemma is_precategory_hss : is_precategory hss_precategory_data.
Proof.
  repeat split; intros.
  - apply (invmap (hssMor_eq _ _ _ _ )).
    apply (id_left EndC).
  - apply (invmap (hssMor_eq _ _ _ _ )).
    apply (id_right EndC).
  - apply (invmap (hssMor_eq _ _ _ _ )).
    apply (assoc EndC).
Qed.

Definition hss_precategory : precategory := tpair _ _ is_precategory_hss.

(** ** A functor from hss to monads *)

(** Objects are considered above, now morphisms *)

Definition Monad_Mor_laws_from_hssMor (T T' : hss)(β : hssMor T T') 
  : Monad_Mor_laws (T:=Monad_from_hss T) (T':=Monad_from_hss T') (#U β).
Proof.
  repeat split; simpl.
  - intro c.
    unfold μ_2. simpl.
    set (H':=isbracketMor_hssMor β).
    unfold isbracketMor in H'.
    set (H2:= H' _ (identity _ )).
    set (H3:=(nat_trans_eq_weq _ _ hs _ _ _ _ H2)).
    rewrite id_left in H3.
    simpl in H3.
    rewrite H3; clear H3 H2 H'. 
    rewrite compute_fbracket.
    simpl.
    repeat rewrite assoc.
    apply idpath.
  - unfold μ_0.
    intro c.
    set (H':=ptd_mor_commutes _  (pr1 β)).
    apply H'.
Qed.
    
Definition Monad_Mor_from_hssMor {T T' : hss}(β : hssMor T T') 
  : Monad_Mor (Monad_from_hss T) (Monad_from_hss T')
  := tpair _ (#U β) (Monad_Mor_laws_from_hssMor T T' β).


Definition hss_to_monad_functor_data : functor_data hss_precategory (precategory_Monad C hs).
Proof.
  exists Monad_from_hss.
  exact @Monad_Mor_from_hssMor.
Defined.

Lemma is_functor_hss_to_monad : is_functor hss_to_monad_functor_data.
Proof.  
  split; simpl.
  - intro a.
    apply (invmap (Monad_Mor_equiv hs _ _ )).
    apply idpath.
  - intros a b c f g.
    apply (invmap (Monad_Mor_equiv hs _ _ )).
    apply idpath.
Qed.

Definition hss_to_monad_functor : functor _ _ := tpair _ _ is_functor_hss_to_monad.

Lemma isaset_Monad_Mor (T T' : Monad C) : isaset (Monad_Mor T T').
Proof.
  intros β β'.
  apply (isofhlevelweqb _ (Monad_Mor_equiv hs  _ _)).
  apply isaset_nat_trans.
  apply hs.
Qed.

Definition hssMor_Monad_Mor_eq {T T' : hss} (β β' : hssMor T T') 
  : β = β' ≃ Monad_Mor_from_hssMor β = Monad_Mor_from_hssMor β'.
Proof.
  eapply weqcomp.
  - apply hssMor_eq.
  - apply invweq.
    apply Monad_Mor_equiv.
    apply hs.
Defined.

(** *** The functor from hss to monads is faithful, i.e. forgets at most structure *)

Lemma faithful_hss_to_monad : faithful hss_to_monad_functor.
Proof.
  unfold faithful.
  intros T T'.
  apply isinclbetweensets.
  - apply isaset_hssMor.
  - apply isaset_Monad_Mor.
  - intros β β'.
    apply (invmap (hssMor_Monad_Mor_eq _ _ )).
Qed.
 
End hss_precategory.

End hss_morphisms.

End def_hss.




