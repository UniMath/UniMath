Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.
Require Import SubstSystems.UnicodeNotations.
Require Import UniMath.RezkCompletion.whiskering.
Require Import UniMath.RezkCompletion.Monads.
Require Import UniMath.RezkCompletion.FunctorAlgebras.
Require Import UniMath.RezkCompletion.limits.coproducts.
Require Import SubstSystems.Auxiliary.
Require Import SubstSystems.PointedFunctors.
Require Import SubstSystems.ProductPrecategory.
Require Import SubstSystems.HorizontalComposition.
Require Import SubstSystems.PointedFunctorsComposition.
Require Import SubstSystems.EndofunctorsMonoidal.
Require Import SubstSystems.Signatures.
Require Import SubstSystems.FunctorAlgebraViews.
Require Import SubstSystems.FunctorsPointwiseCoproduct.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Arguments functor_composite {_ _ _} _ _ .
Arguments nat_trans_comp {_ _ _ _ _} _ _ .
Local Notation "G ∙ F" := (functor_composite F G : [ _ , _ , _ ]) (at level 35).
Local Notation "α ∙∙ β" := (hor_comp β α) (at level 20).
Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Local Notation "Z ∘ α" := (post_whisker _ _ _ _ α Z) (at level 35).

Local Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (at level 50).


Section def_hss.

(** ** Some variables and assumptions *)

(** Assume having a precategory [C] whose hom-types are sets *)
Variable C : precategory.
Variable hs : has_homsets C.

Variable CP : Coproducts C.

Local Notation "'EndC'":= ([C, C, hs]) .
Let hsEndC : has_homsets EndC := functor_category_has_homsets C C hs.
Let CPEndC : Coproducts EndC := Coproducts_functor_precat _ _ CP hs.

Variable H : Signature C hs.

Let θ := theta H.

Let θ_strength1_int := Sig_strength_law1 _ _ H.
Let θ_strength2_int := Sig_strength_law2 _ _ H.

Let Id_H
: functor EndC EndC
  := coproduct_functor _ _ CPEndC 
                       (constant_functor _ _ (functor_identity _ : EndC))
                       H.

(*
(** [H] is a rank-2 endofunctor on endofunctors *)
Variable H : functor [C, C, hs] [C, C, hs].
*)
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

Local Notation "A ⊗ B" := (prodcatpair _ _ A B) (at level 10).
Local Notation "'τ'" := (tau).

(** ** Definition of algebra structure [τ] of a pointed functor *)
(*
Definition AlgStruct (T : Ptd) : UU := pr1 (H(U T)) ⟶ pr1 (U T).

Definition Alg : UU := Σ T : Ptd, AlgStruct T.

Coercion PtdFromAlg (T : Alg) : Ptd := pr1 T.

Definition τ (T : Alg) : pr1 (H (U T)) ⟶ pr1 (U T) := pr2 T.
*)


(* An Id_H algebra is a pointed functor *)

Definition eta_from_alg (T : algebra_ob _ Id_H) : EndC ⟦ functor_identity _,  T ⟧.
Proof.
  exact (CoproductIn1 _ _ ;; alg_map _ _ T).
Defined.
  
Definition ptd_from_alg (T : algebra_ob _ Id_H) : Ptd.
Proof.
  exists (pr1 T).
  exact (eta_from_alg T).
Defined.

Definition tau_from_alg (T : algebra_ob _ Id_H) : EndC ⟦H T, T⟧.
Proof.
  exact (CoproductIn2 _ _ ;; alg_map _ _ T).
Defined.

Local Notation "'p' T" := (ptd_from_alg T) (at level 3).

Coercion functor_from_algebra_ob (X : algebra_ob _ Id_H) : functor C C  := pr1 X.
Local Notation "` T" := (functor_from_algebra_ob T) (at level 3).

Local Notation "f ⊕ g" := (CoproductOfArrows _ (CPEndC _ _ ) (CPEndC _ _ ) f g) (at level 40).

(*
Definition bracket (T : algebra_ob _ Id_H) : UU := 
  ∀ (Z : Ptd) (f : Z ⇒ ptd_from_alg T), iscontr 
   (Σ h : `T ∙ (U Z)  ⇒ T,
          alg_map _ _ T øø (U Z) ;; h =
          CoproductOfArrows _ (CPEndC _ _ ) (CPEndC _ _ ) (identity (U Z)) (θ (`T ⊗ Z)) ;;
          CoproductOfArrows _ (CPEndC _ _ ) (CPEndC _ _ ) (identity (U Z)) (#H h) ;;
          CoproductArrow _ (CPEndC _ _ ) (#U f) (tau_from_alg T )).                
*)                    

Definition bracket_point (T : algebra_ob _ Id_H) (Z : Ptd) (f : Z ⇒ ptd_from_alg T): UU := 
  iscontr 
   (Σ h : `T ∙ (U Z)  ⇒ T,
          alg_map _ _ T øø (U Z) ;; h =
          identity (U Z) ⊕ θ (`T ⊗ Z) ;;
          identity (U Z) ⊕ #H h ;;
          CoproductArrow _ (CPEndC _ _ ) (#U f) (tau_from_alg T )).

Definition bracket (T : algebra_ob _ Id_H) : UU
  := ∀ (Z : Ptd) (f : Z ⇒ ptd_from_alg T), bracket_point T Z f.


Definition bracket_parts_point (T : algebra_ob _ Id_H) (Z : Ptd) (f : Z ⇒ ptd_from_alg T) : UU := 
   iscontr 
   (Σ h : `T ∙ (U Z)  ⇒ T,
     (#U f = eta_from_alg T øø (U Z) ;; h) ×
     (θ (`T ⊗ Z) ;; #H h ;; tau_from_alg T  = tau_from_alg T øø (U Z) ;;  h )).

Definition bracket_parts (T : algebra_ob _ Id_H) : UU
  := ∀ (Z : Ptd) (f : Z ⇒ ptd_from_alg T), 
   iscontr 
   (Σ h : `T ∙ (U Z)  ⇒ T,
     (#U f = eta_from_alg T øø (U Z) ;; h) ×
     (θ (`T ⊗ Z) ;; #H h ;; tau_from_alg T  = tau_from_alg T øø (U Z) ;;  h )).

(* show that for any h of suitable type, the following are equivalent *)

Lemma parts_from_whole (T : algebra_ob _ Id_H) (Z : Ptd) (f : Z ⇒ ptd_from_alg T)
      (h :  `T ∙ (U Z)  ⇒ T) :
    alg_map _ _ T øø (U Z) ;; h =
          identity (U Z) ⊕ θ (`T ⊗ Z) ;;
          identity (U Z) ⊕ #H h ;;
          CoproductArrow _ (CPEndC _ _ ) (#U f) (tau_from_alg T ) → 
   (#U f = eta_from_alg T øø (U Z) ;; h) ×
     (θ (`T ⊗ Z) ;; #H h ;; tau_from_alg T  = tau_from_alg T øø (U Z) ;;  h ).
Proof.
  admit.
Admitted.

Lemma whole_from_parts (T : algebra_ob _ Id_H) (Z : Ptd) (f : Z ⇒ ptd_from_alg T)
      (h :  `T ∙ (U Z)  ⇒ T) :
  (#U f = eta_from_alg T øø (U Z) ;; h) ×
  (θ (`T ⊗ Z) ;; #H h ;; tau_from_alg T  = tau_from_alg T øø (U Z) ;;  h )
   →                                       
    alg_map _ _ T øø (U Z) ;; h =
          identity (U Z) ⊕ θ (`T ⊗ Z) ;;
          identity (U Z) ⊕ #H h ;;
          CoproductArrow _ (CPEndC _ _ ) (#U f) (tau_from_alg T ).
Proof.
  admit.
Admitted.


(* show bracket_parts_point is logically equivalent to bracket_point, then 
   use it to show that bracket_parts is equivalent to bracket using [weqonsecfibers:
  ∀ (X : UU) (P Q : X → UU),
  (∀ x : X, P x ≃ Q x) → (∀ x : X, P x) ≃ (∀ x : X, Q x)] *)


Definition hss : UU := Σ T, bracket T.

Coercion alg_from_hss (T : hss) : algebra_ob _ Id_H := pr1 T.


Definition fbracket (T : hss) {Z : Ptd} (f : Z ⇒ ptd_from_alg T) 
  : `T ∙ (U Z) ⇒ T
  := pr1 (pr1 (pr2 T Z f)).

(** The bracket operation [fbracket] is unique *)

Definition fbracket_unique_pointwise (T : hss) {Z : Ptd} (f : Z ⇒ ptd_from_alg T) 
  : ∀ (α : functor_composite (U Z) `T ⟶ `T),
     (∀ c : C, pr1 (#U f) c = pr1 (eta_from_alg T) (pr1 (U Z) c) ;; α c) →
     (∀ c : C, pr1 (θ (`T ⊗ Z))  c ;; pr1 (#H α) c ;; pr1 (tau_from_alg T) c = 
        pr1 (tau_from_alg T) (pr1 (U Z) c) ;; α c) → α = fbracket T f.
Proof.
  intros α H1 H2.
  apply path_to_ctr.
  apply whole_from_parts.
  split.
  - apply nat_trans_eq; try assumption.
  - apply nat_trans_eq; assumption.
Qed.
    
Definition fbracket_unique (T : hss) {Z : Ptd} (f : Z ⇒ ptd_from_alg T) 
  : ∀ α : functor_composite (U Z)(`T) ⟶ `T,
     (#U f = eta_from_alg T øø ((U Z)) ;; α) →
     (θ (`T ⊗ Z) ;; #H α ;; tau_from_alg T = tau_from_alg T øø (U Z) ;; α) 
   → α = fbracket T f.
Proof.
  intros α H1 H2.
  apply path_to_ctr.
  apply whole_from_parts.
  split;  assumption.
Qed.

Definition fbracket_unique_target_pointwise (T : hss) {Z : Ptd} (f : Z ⇒ ptd_from_alg T) 
  : ∀ α : functor_composite (U Z)(`T) ⟶ `T,
     (#U f =  eta_from_alg T øø U Z ;; α) →
     (θ (`T ⊗ Z) ;; #H α ;; tau_from_alg T = tau_from_alg T øø U Z ;; α) 
   → ∀ c, α c = pr1 (fbracket T f) c.
Proof.
  intros α H1 H2.
  set (t:= fbracket_unique _ _ α H1 H2).
  apply (nat_trans_eq_weq _ _ hs _ _ _ _ t).
Qed.

(** Properties of [fbracket] by definition: commutative diagrams *)

Lemma fbracket_η (T : hss) : ∀ {Z : Ptd} (f : Z ⇒ ptd_from_alg T),
   #U f = eta_from_alg T øø U Z ;; fbracket T f.
Proof.
  intros Z f.
  (* assert (H' := parts_from_whole T Z f (fbracket _ f)) . *)
  exact (pr1 (parts_from_whole _ _ _ _  (pr2 (pr1 (pr2 T Z f))))). 
Qed.

Lemma fbracket_τ (T : hss) : ∀ {Z : Ptd} (f : Z ⇒ ptd_from_alg T),
    θ (`T ⊗ Z) ;; #H (fbracket T f) ;; tau_from_alg T  
    = 
    tau_from_alg T øø U Z ;; (fbracket T f).
Proof.
  intros Z f.
  exact (pr2 (parts_from_whole _ _ _ _ (pr2 (pr1 (pr2 T Z f))))).
Qed.

(** [fbracket] is also natural *)

Lemma fbracket_natural (T : hss) {Z Z' : Ptd} (f : Z ⇒ Z') (g : Z' ⇒ ptd_from_alg T) 
  : post_whisker _ _ _ _ (#U f)(`T) ;; fbracket T g = fbracket T (f ;; g).
Proof.
  apply fbracket_unique_pointwise.
  - simpl. intro c.
    rewrite assoc.
    set (H':=nat_trans_ax (eta_from_alg T)).
    simpl in H'.
    rewrite <- H'; clear H'.
    rewrite <- assoc.
    apply maponpaths.
    set (X:= nat_trans_eq_weq _ _ hs _ _ _ _  (fbracket_η T g)).
    simpl in X. exact (X _ ).
  - intro c; simpl.
    assert (H':=nat_trans_ax (tau_from_alg T)).
    simpl in H'.
    eapply pathscomp0. Focus 2. apply (!assoc _ _ _ _ _ _ _ _ ).
    eapply pathscomp0. Focus 2.  apply  cancel_postcomposition. apply H'.
    clear H'.
    set (H':=fbracket_τ T g).
    simpl in H'.
    assert (X:= nat_trans_eq_pointwise _ _  _ _ _ _ H' c).
    simpl in X.
    rewrite  <- assoc.
    rewrite  <- assoc.
    transitivity (  # (pr1 (H ((`T)))) (pr1 (pr1 f) c) ;;
                     (pr1 (θ ((`T) ⊗ Z')) c);; pr1 (# H (fbracket T g)) c;; pr1 (tau_from_alg T) c).
    Focus 2.
      rewrite <- assoc.
      rewrite <- assoc.
      apply maponpaths.
      repeat rewrite assoc.
      apply X.
    clear X.
    set (A:=θ_nat_2_pointwise).
    simpl in *.
    set (A':= A _ hs H θ (`T) Z Z').
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

Lemma compute_fbracket (T : hss) : ∀ {Z : Ptd} (f : Z ⇒ ptd_from_alg T),
  fbracket T f = post_whisker _ _ _ _ (#U f)(`T) ;; fbracket T (identity _ ). 
Proof.
  intros Z f.
  assert (A : f = f ;; identity _ ).
  { rewrite id_right; apply idpath. }
  rewrite A.
  rewrite <- fbracket_natural.
  rewrite id_right.
  apply idpath.
Qed.



(** ** Morphisms of heterogeneous substitution systems *)


(** A morphism [f] of pointed functors is an algebra morphism when... *)
(*
Definition isAlgMor {T T' : Alg} (f : T ⇒ T') : UU :=
  #H (# U f) ;; τ T' = compose (C:=EndC) (τ T) (#U f).

Lemma isaprop_isAlgMor (T T' : Alg) (f : T ⇒ T') : isaprop (isAlgMor f).
Proof.
  apply isaset_nat_trans.
  apply hs.
Qed.
*)
(** A morphism [β] of pointed functors is a bracket morphism when... *)

Lemma is_ptd_mor_alg_mor (T T' : algebra_ob ([C, C] hs) Id_H)
  (β : algebra_mor ([C, C] hs) Id_H T T') :
  @is_ptd_mor C (ptd_from_alg T) (ptd_from_alg T') (pr1 β).
Proof.
  simpl.
  unfold is_ptd_mor. simpl.
  intro c.
  rewrite <- assoc.
  assert (X:=pr2 β).
  assert (X':= nat_trans_eq_pointwise _ _ _ _ _ _ X c).
  simpl in *.
  eapply pathscomp0. apply maponpaths. apply X'.
  unfold coproduct_nat_trans_in1_data.
  repeat rewrite assoc.
  unfold coproduct_nat_trans_data.
  eapply pathscomp0.
  apply cancel_postcomposition.
  apply CoproductIn1Commutes.
  simpl.
  repeat rewrite <- assoc.
  apply id_left.
Qed.
  
Definition ptd_from_alg_mor {T T' : algebra_ob _ Id_H} (β : algebra_mor _ _ T T')
: ptd_from_alg T ⇒ ptd_from_alg T'.
Proof.
  exists (pr1 β).
  apply is_ptd_mor_alg_mor.
Defined.

(* show functor laws for [ptd_from_alg] and [ptd_from_alg_mor] *)

Definition isbracketMor {T T' : hss} (β : algebra_mor _ _ T T') : UU :=
    ∀ (Z : Ptd) (f : Z ⇒ ptd_from_alg T), 
       fbracket _ f ;;  β
       = 
       (β)øø (U Z) ;; fbracket _ (f ;; ptd_from_alg_mor β ).


Lemma isaprop_isbracketMor (T T':hss) (β : algebra_mor _ _ T T') : isaprop (isbracketMor β).
Proof.
  do 2 (apply impred; intro).
  apply isaset_nat_trans.
  apply hs.
Qed.

(** A morphism of hss is a pointed morphism that is compatible with both 
    [τ] and [fbracket] *)

Definition ishssMor {T T' : hss} (β : algebra_mor _ _ T T') : UU 
  :=   isbracketMor β.
  
Definition hssMor (T T' : hss) : UU 
  := Σ β : algebra_mor _ _ T T', ishssMor β.

Coercion ptd_mor_from_hssMor (T T' : hss) (β : hssMor T T') : algebra_mor _ _ T T' := pr1 β.

(*
Definition isAlgMor_hssMor {T T' : hss} (β : hssMor T T') 
  : isAlgMor β := pr1 (pr2 β).
*)
Definition isbracketMor_hssMor {T T' : hss} (β : hssMor T T') 
  : isbracketMor β := pr2 β.

(** **** Equality of morphisms of hss *)

Section hssMor_equality.

(** Show that equality of hssMor is equality of underlying nat. transformations *)

Variables T T' : hss.
Variables β β' : hssMor T T'.
Definition hssMor_eq1 : β = β' ≃ (pr1 β = pr1 β').
Proof.
  apply total2_paths_isaprop_equiv.
  intro γ.
  apply isaprop_isbracketMor.
Defined.


Definition hssMor_eq : β = β' ≃ (β : EndC ⟦ _ , _ ⟧) = β'.
Proof.
  eapply weqcomp.
  - apply hssMor_eq1.
  - apply total2_paths_isaprop_equiv.
    intro.
    apply isaset_nat_trans.
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

(** *** Identity morphism of hss *)

Lemma ishssMor_id (T : hss) : ishssMor (identity (C:=precategory_FunctorAlg _ _ hsEndC ) (pr1 T)).
Proof.
  unfold ishssMor.
  unfold isbracketMor.
  intros Z f.
  rewrite id_right.
  
  set (H2:=pre_composition_functor _ _ C _ hs (U Z)).
  set (H2' := functor_id H2). simpl in H2'.
  simpl.
  rewrite H2'.
  rewrite (id_left EndC).
  simpl.
  admit. (* use functor laws for [ptd_from_alg_mor (identity (pr1 T))] *)
Admitted.

Definition hssMor_id (T : hss) : hssMor _ _ := tpair _ _ (ishssMor_id T).
  
(** *** Composition of morphisms of hss *)

Lemma ishssMor_comp {T T' T'' : hss} (β : hssMor T T') (γ : hssMor T' T'') 
  : ishssMor (compose (C:=precategory_FunctorAlg _ _ hsEndC) (pr1 β)  (pr1 γ)).
Proof.
  unfold ishssMor.
  unfold isbracketMor.
  intros Z f.
  (*
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
   *)
  admit.
Admitted.

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

End def_hss.

Arguments hss {_ _} _  _ .
Arguments hssMor {_ _ _ _ } _ _ .
Arguments fbracket {_ _ _ _ } _ {_} _ .
Arguments tau {_ _ _} _ .
Arguments fbracket_η {_ _ _ _ } _ {_} _ .
Arguments fbracket_τ {_ _ _ _} _ {_} _ .
Arguments fbracket_unique_target_pointwise {_ _ _ _ } _ {_ _ _} _ _ _ .
Arguments fbracket_unique {_ _ _ _ } _ {_} _ _ _ _ .
(* Arguments Alg {_ _} _. *)
Arguments hss_precategory {_ _} _ _ .
