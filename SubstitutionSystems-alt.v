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

Definition bracket (T : algebra_ob _ Id_H) : UU := 
  ∀ (Z : Ptd) (f : Z ⇒ T), iscontr 
   (Σ h : (U T) ∙ (U Z)  ⇒ U T,
     (#U f = (ptd_pt _ (pr1 T)) øø (U Z) ;; h) ×
     (θ (U T ⊗ Z) ;; #H h ;; τ _  = τ _ øø ((U Z)) ;;  h )).


Definition bracket (T : ALG H) : UU := 
  ∀ (Z : Ptd) (f : Z ⇒ T), iscontr 
   (Σ h : (U T) ∙ (U Z)  ⇒ U T,
     (#U f = (ptd_pt _ (pr1 T)) øø (U Z) ;; h) ×
     (θ (U T ⊗ Z) ;; #H h ;; τ _  = τ _ øø ((U Z)) ;;  h )).

Definition hss : UU := Σ T : ALG H, bracket T.

Coercion ALG_from_hss (T : hss) : ALG H := pr1 T.

Coercion AlgFromhss (T : hss) : ALG H := pr1 T.

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
   #U f = (ptd_pt _  (pr1 (pr1 T))) øø U Z ;; fbracket T f.
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
    rewrite assoc.
    set (H':=nat_trans_ax (ptd_pt _ (pr1 (pr1 T)) )).
    simpl in H'.
    rewrite <- H'; clear H'.
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
    assert (X:= nat_trans_eq_pointwise _ _  _ _ _ _ H' c).
    simpl in X.
    rewrite  <- assoc.
    rewrite  <- assoc.
    transitivity (  # (pr1 (H ((U T)))) (pr1 (pr1 f) c) ;;
                     (pr1 (θ ((U T) ⊗ Z')) c);; pr1 (# H (fbracket T g)) c;; (τ T) c).
    Focus 2.
      rewrite <- assoc.
      rewrite <- assoc.
      apply maponpaths.
      repeat rewrite assoc.
      apply X.
    clear X.
    set (A:=θ_nat_2_pointwise).
    simpl in *.
    set (A':= A _ hs H θ (U T) Z Z').
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
  :=  isALGMor β × isbracketMor β.
  
Definition hssMor (T T' : hss) : UU 
  := Σ β : T ⇒ T', ishssMor β.

Coercion ptd_mor_from_hssMor (T T' : hss) (β : hssMor T T') : T ⇒ T' := pr1 β.

Definition isAlgMor_hssMor {T T' : hss} (β : hssMor T T') 
  : isALGMor β := pr1 (pr2 β).
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
  - apply isaprop_isALGMor.
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

(** *** Identity morphism of hss *)

Lemma ishssMor_id (T : hss) : ishssMor (identity T).
Proof.
  split.
  - unfold isALGMor.
    rewrite functor_id.
    rewrite functor_id.
    rewrite id_left.
    set (H2 := id_right ([C,C,hs])).
    apply pathsinv0, H2.
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
  - unfold isALGMor.
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

End def_hss.

Arguments hss {_ _} _ .
Arguments hssMor {_ _ _} _ _ .
Arguments fbracket {_ _ _} _ {_} _ .
Arguments tau {_ _ _} _ .
Arguments fbracket_η {_ _ _} _ {_} _ .
Arguments fbracket_τ {_ _ _} _ {_} _ .
Arguments fbracket_unique_target_pointwise {_ _ _} _ {_ _ _} _ _ _ .
Arguments fbracket_unique {_ _ _} _ {_} _ _ _ _ .
(* Arguments Alg {_ _} _. *)
Arguments hss_precategory {_ _} _ .