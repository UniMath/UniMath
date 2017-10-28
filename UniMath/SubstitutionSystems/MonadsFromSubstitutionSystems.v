(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

- Construction of a monad from a substitution system
- Proof that morphism of hss gives morphism of monads
- Bundling that into a functor
- Proof that the functor is faithful


************************************************************)

Unset Kernel Term Sharing.

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.

Local Open Scope cat.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.

Section monad_from_hss.

(** ** Some variables and assumptions *)

(** Assume having a precategory [C] whose hom-types are sets *)
Variable C : precategory.
Variable hs : has_homsets C.

Variable CP : BinCoproducts C.

Local Notation "'EndC'":= ([C, C, hs]) .
Let hsEndC : has_homsets EndC := functor_category_has_homsets C C hs.
Let CPEndC : BinCoproducts EndC := BinCoproducts_functor_precat _ _ CP hs.

Variable H : Signature C hs C hs.

Let θ := theta H.

Let θ_strength1_int := Sig_strength_law1 _ _ _ _ H.
Let θ_strength2_int := Sig_strength_law2 _ _ _ _ H.

Let Id_H
: functor EndC EndC
  := BinCoproduct_of_functors _ _ CPEndC
                       (constant_functor _ _ (functor_identity _ : EndC))
                       H.


(** The precategory of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (precategory_Ptd C hs).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hs]) .
(** The product of two precategories *)



(** ** Definition of algebra structure [τ] of a pointed functor *)


(** ** Derivation of the monad laws from a heterogeneous substitution system *)

Section mu_from_fbracket.

(** We assume given a hss [T] *)

Variable T : hss CP H.

Local Notation "'p' T" := (ptd_from_alg T) (at level 3).
Local Notation "f ⊕ g" := (BinCoproductOfArrows _ (CPEndC _ _ ) (CPEndC _ _ ) f g) (at level 40).


Definition μ_0 : functor_identity C ⟹ functor_data_from_functor _ _ `T := η T. (*ptd_pt _ (pr1 (pr1 T)).*)

Definition μ_0_ptd : id_Ptd C hs --> p T.
Proof.
  exists μ_0.
  intro c. simpl. apply id_left.
Defined.

Definition μ_1 : functor_composite (U (id_Ptd C hs)) (`T) ⟹ functor_data_from_functor _ _ `T
  := fbracket _ μ_0_ptd.


Lemma μ_1_identity : μ_1 = identity `T .
Proof.
  apply pathsinv0.
  apply fbracket_unique.
  split.
  - apply nat_trans_eq; try assumption.
    intros; simpl.
    rewrite id_right.
    apply idpath.
  - apply nat_trans_eq; try assumption.
    intro c. simpl.
    rewrite id_right.
    assert (H':= θ_Strength1_int_implies_θ_Strength1 _ _ _ _ _ _ θ_strength1_int).
    red in H'. simpl in H'.
    assert (H2 := H' (`T)).
    assert (H3 := nat_trans_eq_pointwise H2 c).
    simpl in *.
    pathvia (identity _ · pr1 (τ T) c).
    + apply cancel_postcomposition. apply H3.
    + apply id_left.
Qed.


Lemma μ_1_identity' : ∏ c : C, μ_1 c = identity _.
Proof.
  intros c.
  assert (HA:= nat_trans_eq_pointwise μ_1_identity).
  apply HA.
Qed.

(* The whole secret is that this typechecks
  Check (μ_1:U T-->U T).
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

Definition μ_2 : functor_composite (`T) (`T) ⟹ pr1 (`T)
  := fbracket T (identity _ ).


Definition functor_with_mu_from_hss : functor_with_μ C.
Proof.
  exists (`T).
  exact μ_2.
Defined.

Definition Monad_data_from_hss : Monad_data C.
Proof.
  exists functor_with_mu_from_hss.
  exact μ_0.
Defined.

(** *** Proof of the first monad law *)

Lemma Monad_law_1_from_hss :
  ∏ c : C, μ_0 (pr1 (`T) c)· μ_2 c = identity ((pr1 (`T)) c).
Proof.
  intro c.
  unfold μ_2. simpl.
  unfold μ_0. simpl.
  set (H':=fbracket_η T (identity _) ).
  set (H2:= nat_trans_eq_weq hs _ _ H').
  simpl in H2.
  apply pathsinv0.
  apply H2.
Qed.

(** *** Proof of the second monad law *)

Lemma Monad_law_2_from_hss:
  ∏ c : C, # (pr1 (`T)) (μ_0 c)· μ_2 c = identity ((pr1 (`T)) c).
Proof.
  intro c.
  pathvia (μ_1 c).
  - unfold μ_1.
    assert (H':= @fbracket_unique_target_pointwise _ _  _ _ T).
    assert (H1:= H'  _ μ_0_ptd).
    set (x:= post_whisker μ_0 (`T)
             : EndC ⟦ `T • functor_identity _  , `T • `T ⟧).
    set (x':= x · μ_2).
    assert (H2 := H1 x').
    apply H2; clear H2.
    unfold x'. clear x'.
    unfold x; clear x.
    clear H1. clear H'. clear c.
    split.
    + apply nat_trans_eq; try apply hs.
      intro c.
      assert (H':=nat_trans_ax (η T)).
      simpl in H'.
      rewrite assoc.
      cbn.
      rewrite <- H'; clear H'.
      assert (H':= fbracket_η T (identity _ )).
      unfold μ_2.
      assert (H2 := nat_trans_eq_weq hs _ _ H').
      simpl in H2.
      rewrite <- assoc.
      rewrite <- H2.
      apply pathsinv0. apply id_right. (* done *)
    + rewrite functor_comp.
      apply nat_trans_eq; try assumption.
      intro c.
      rewrite <- horcomp_id_postwhisker.
      do 2 rewrite assoc.
      simpl in *.
      pathvia ( # (pr1 (H ( (` T)))) (μ_0 c)· pr1 (θ ((`T) ⊗ (p T))) c ·
                  pr1 (# H μ_2) c · pr1 (τ T) c).
      * unfold tau_from_alg; cbn.
        do 2 rewrite assoc.
        apply cancel_postcomposition.
        apply cancel_postcomposition.
        apply cancel_postcomposition.
        assert (H':=θ_nat_2 _ _ _ _ H θ).
        assert (H2 := H' (`T) _ _ μ_0_ptd); clear H'.
        assert (H3:= nat_trans_eq_weq hs _ _ H2 c); clear H2.
        simpl in H3.
        rewrite id_left in H3.
        apply (!H3). (* done *)
      * assert (H':= fbracket_τ T (identity _ )).
        unfold μ_2.
        simpl.
        assert (H2:= nat_trans_eq_weq hs _ _ H' c); clear H'.
        simpl in *.
        do 2 rewrite <- assoc.
        {
          pathvia (  # (pr1 (H (` T))) (μ_0 c)·
                       (pr1 (τ T) (pr1 (`T) c)· pr1 (fbracket T (identity (p T))) c)).
          - apply maponpaths.
            rewrite assoc.
            apply H2; clear H2. (* rewrite done *)
          - clear H2.
            do 2 rewrite assoc.
            apply cancel_postcomposition.
            eapply pathscomp0.
            apply (nat_trans_ax (τ T) ).
            apply cancel_postcomposition.
            apply pathsinv0.
            apply id_right.
        }
  - apply μ_1_identity'.
Qed.

(** [T_squared] is [T∙T, η∙η], that is, the selfcomposition of [T] as a pointed functor *)

Definition T_squared : Ptd.
Proof.
  exact (ptd_composite _ _ (p T) (p T)).
Defined.

(** [μ_2] is not just a natural transformation from [T∙T] to [T], but also compatible with
    the pointed structure given by [η] *)

Lemma μ_2_is_ptd_mor :
  ∏ c : C, (ptd_pt C T_squared) c· μ_2 c = pr1 (η T) c.
Proof.
  intro c.
  unfold μ_2.
  unfold T_squared. simpl.
  assert (H':=Monad_law_2_from_hss c).
  simpl in H'.
  pathvia (pr1 (η T) c · identity _ ).
  - unfold eta_from_alg; simpl.
    repeat rewrite <- assoc.
    apply maponpaths.
    apply maponpaths.
    apply H'.
  - apply id_right.
Qed.

Definition μ_2_ptd : T_squared --> p T.
Proof.
  exists μ_2.
  unfold is_ptd_mor.
  apply μ_2_is_ptd_mor.
Defined.

Definition μ_3 : EndC ⟦ U T_squared • `T,  `T⟧ := fbracket T μ_2_ptd.

(* for Travis *)

Check μ_3.

(*
Definition μ_3' := fbracket T μ_2_ptd.
Check μ_3'.
Check (μ_3' = μ_3).
*)

(** *** Proof of the third monad law via transitivity *)
(** We show that both sides are equal to [μ_3 = fbracket μ_2] *)

Lemma μ_3_T_μ_2_μ_2 : μ_3 =
                      (`T ∘ μ_2 : EndC ⟦ `T • _  , `T • `T ⟧ ) · μ_2.
Proof.
  apply pathsinv0.
  apply (fbracket_unique T  μ_2_ptd).
  split.
  - apply nat_trans_eq; try assumption.
    intro c.
    assert (H2 := nat_trans_ax (η T)); simpl in H2.
    rewrite assoc.
    simpl; rewrite <- H2 ; clear H2.
    (* rewrite <- assoc. *)
    pathvia (μ_2 c · identity _ ).
    + apply pathsinv0, id_right.
    + eapply pathscomp0. Focus 2.  apply assoc.
      apply pathsinv0.
      apply maponpaths. apply Monad_law_1_from_hss.
  - rewrite functor_comp.
    assert (H1 := θ_nat_2 _ _ _ _ H θ (`T) _ _ μ_2_ptd).
    simpl in H1.
    repeat rewrite assoc.
    match goal with |[H1 : ?g = _ |- _ · _ · ?f · ?h = _ ] =>
         pathvia (g · f · h) end.
    + apply cancel_postcomposition.
      apply cancel_postcomposition.
      apply pathsinv0.
      eapply pathscomp0. apply H1; clear H1.
      apply maponpaths.
      apply maponpaths.
      assert (H3:=horcomp_id_postwhisker).
      assert (H4 := H3 _ _ _ hs hs _ _ μ_2 (`T)); clear H3.
      apply H4.
    + clear H1.
      apply nat_trans_eq; try assumption.
      intro c; simpl.
      rewrite id_left.
      assert (H2 := fbracket_τ T  (identity _ )).
      assert (H3:= nat_trans_eq_pointwise H2 c); clear H2.
      simpl in *.
      match goal with |[H3 : _ = ?f |- ?e · _ · _ · _  = _ ] =>
         pathvia (e · f) end.
      * eapply pathscomp0. apply (!assoc _ _ _).
        eapply pathscomp0. apply (!assoc _ _ _ ).
        apply maponpaths.
        eapply pathscomp0. Focus 2. apply H3.
        apply assoc.
      * clear H3.
        repeat rewrite assoc.
        apply cancel_postcomposition.
        assert (H1 := nat_trans_ax (τ T )).
        unfold tau_from_alg in H1.
        eapply pathscomp0; [ | apply H1]; clear H1.
        apply pathsinv0, assoc.
Qed.

(* for Travis *)
Check μ_3_T_μ_2_μ_2.

Local Notation "'T•T²'" := (functor_compose hs hs (functor_composite (`T) (`T)) (`T) : [C, C, hs]).
(*
Definition TtimesTthenT': [C, C] hs := functor_compose hs hs (functor_composite (`T) (`T)) (`T).
*)


Local Notation "'T²∙T'" := (@functor_composite C C C
                    (@functor_composite C C C (`T)
                                              (` T))
                    (` T) : functor C C).
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
          ((μ_2 •• `T) (* :  TtimesTthenT' --> _ *)
                  (*:@functor_compose C C C hs hs
                    (@functor_composite C C C ((functor_ptd_forget C hs) T)
                                              ((functor_ptd_forget C hs) T))
                    ((functor_ptd_forget C hs) T) --> _*) ) μ_2 :
            (*TtimesTthenT'*) T•T² --> `T) = μ_3.
Proof.
  apply (fbracket_unique (*_pointwise*) T μ_2_ptd).
  split.
  - apply nat_trans_eq; try assumption; intro c.
    simpl.
    transitivity (identity _ · μ_2 c).
    + apply pathsinv0, id_left.
    + eapply pathscomp0; [ | apply (!assoc _ _ _ ) ].
      apply cancel_postcomposition.
      assert (H1 := Monad_law_1_from_hss (pr1 (`T) c)).
      apply (!H1).
  - set (B:= τ T).
    match goal with | [|- _ · # ?H (?f · _ ) · _ = _ ] => set (F:=f : (*TtimesTthenT'*) T•T² --> _ ) end.
    assert (H3:= functor_comp H F μ_2).
    unfold functor_compose in H3.
    eapply pathscomp0. apply cancel_postcomposition. apply maponpaths. apply H3.
    clear H3.
    apply nat_trans_eq; try assumption.
    intro c.
    simpl.
    match goal with | [ |- ?a · _ · _ = _ ] => set (Ac:= a) end.
    simpl in Ac.
    unfold θ_target_ob in *.
    simpl in *.
    unfold functor_compose in *.
    assert (HX:=θ_nat_1 _ _ _ _ H θ _ _ μ_2).  (* it may be tested with the primed version *)
    assert (HX1:= HX (ptd_from_alg T)); clear HX.
    simpl in HX1.
    assert (HXX:=nat_trans_eq_pointwise HX1 c); clear HX1.
    simpl in HXX.
    rewrite (functor_id ( H (`T))) in HXX.
    rewrite id_right in HXX. (* last two lines needed because of def. of theta on product category *)
    match goal with |[HXX : ?f · ?h = _ · _ |- _ · (_ · ?x ) · ?y = _ ] =>
      pathvia (pr1 (θ ((`T) ⊗ (ptd_from_alg T))) (pr1 (pr1 (pr1 T)) c)·
                       f  · h · x· y) end.
    * repeat rewrite assoc.
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      unfold Ac. clear Ac.
      eapply pathscomp0. Focus 2. apply assoc.
      eapply pathscomp0. Focus 2. apply maponpaths. apply (!HXX).
      clear HXX.
      assert (Strength_2 : ∏ α : functor_compose hs hs (functor_composite (`T) (`T))(`T) --> functor_composite (` T) (`T),

                    pr1 (θ (`T ⊗ T_squared)) c · pr1 (# H α) c =
                     pr1 (θ ((`T) ⊗ (ptd_from_alg T))) ((pr1 (pr1 (pr1 T))) c)·
                     pr1 (θ (( ((`T) • (`T) : [_, _, hs])) ⊗ (ptd_from_alg T))) c·
                     pr1 (# H (α : functor_compose hs hs (`T) (functor_composite (`T) (` T))--> _)) c       ).
      { (intro α;
          assert (HA := θ_Strength2_int_implies_θ_Strength2 _ _ _ _ _ _ θ_strength2_int);
          assert (HA':= HA (`T) (ptd_from_alg T) (ptd_from_alg T) _ α); clear HA;
          assert (HA2 := nat_trans_eq_pointwise HA' c ); clear HA';
          simpl in HA2; apply HA2 ).
      }
      eapply pathscomp0. apply (Strength_2 F).
      clear Strength_2.
      eapply pathscomp0. apply (!assoc _ _ _).
      apply maponpaths.
      apply maponpaths.
      match goal with |[ |- _ = ?pr1 (# ?G ?g) _ ] =>
              assert (X : F = g) end.
      { apply nat_trans_eq. assumption.
        intros. unfold F.
        simpl.
        rewrite functor_id.
        apply pathsinv0, id_right.
      }
      apply (maponpaths (λ T,  pr1 (# H T) c)).
      apply X.
    * clear HXX. clear Ac. clear F. clear B.
      assert (H4 := fbracket_τ T  (identity _ )).
      assert (H5:= nat_trans_eq_pointwise H4 c); clear H4.
      simpl in H5.
      unfold μ_2.
      {
        match goal with |[ H5 : _ = ?e |- ?a · ?b · _ · _ · _ = _ ] =>
                         pathvia (a · b · e) end.
        - repeat rewrite <- assoc.
          apply maponpaths.
          apply maponpaths.
          repeat rewrite <- assoc in H5. apply H5.
        - clear H5.
          repeat rewrite assoc.
          apply cancel_postcomposition.
          assert (HT := fbracket_τ T (identity _ )).
          assert (H6:= nat_trans_eq_pointwise HT); clear HT.
          unfold coproduct_nat_trans_in2_data.
          unfold tau_from_alg in H6.
          rewrite assoc in H6.
          apply H6.
      }
Qed.

(* for Travis *)
Check  μ_3_μ_2_T_μ_2.


(** proving a variant of the third monad law with assoc iso explicitly inserted *)

Section third_monad_law_with_assoc.

Lemma third_monad_law_from_hss :
  (`T ∘ μ_2 : EndC ⟦ functor_composite (functor_composite `T `T) `T , `T • `T ⟧) · μ_2
  =
  (α_functor _ _ _ : functor_compose hs hs _ _  --> _) · (μ_2 •• `T) · μ_2.
Proof.
  pathvia μ_3; [apply pathsinv0, μ_3_T_μ_2_μ_2 | ].
  apply pathsinv0.
  apply (fbracket_unique (*_pointwise*) T  μ_2_ptd).
  split.
  - apply nat_trans_eq; try assumption; intro c.
    simpl.
    rewrite assoc.
    pathvia (identity _ · μ_2 c).
    + apply pathsinv0, id_left.
    + apply cancel_postcomposition.
      rewrite id_left.
      assert (H1 := Monad_law_1_from_hss (pr1 (`T) c)).
      simpl in H1.
      apply (!H1).
  - rewrite functor_comp.
    rewrite functor_comp.
    rewrite assoc.
    rewrite assoc.
    rewrite assoc.
    rewrite assoc.
    unfold T_squared.
    apply nat_trans_eq; try assumption.
    intro x; simpl.
    assert (HTT := θ_strength2_int).
    assert (HX := HTT (`T) (ptd_from_alg T) (ptd_from_alg T)); clear HTT.
    assert (HX':= nat_trans_eq_pointwise HX x); clear HX.
    simpl in HX'.
    match goal with | [ H : _  = ?f |- _ · _ · ?g · ?h · ?i = _ ] =>
                      pathvia (f · g · h · i) end.
    + apply cancel_postcomposition.
      apply cancel_postcomposition.
      apply cancel_postcomposition.
      apply HX'.
    + clear HX'.
      rewrite id_left.
      rewrite id_right.
      assert (HX:=θ_nat_1 _ _ _ _ H θ _ _ μ_2).
      assert (HX1:= HX (ptd_from_alg T)); clear HX.
      simpl in HX1.
      assert (HXX:=nat_trans_eq_pointwise HX1 x); clear HX1.
      simpl in HXX.
      match goal with | [ H : ?x = _ |- ?e · _ · _ · ?f · ?g = _ ] =>
                 pathvia (e · x · f · g) end.
      * apply cancel_postcomposition.
        apply cancel_postcomposition.
        repeat rewrite <- assoc.
        apply maponpaths.
        {
          match goal with | [ H : _ = ?x |- _ ] => pathvia x end.
          -  clear HXX.
             apply maponpaths.
             match goal with | [ |- _  ?a ?x = _  ?b ?y ] => assert (TTT : a = b) end.
             {
               match goal with | [ |- _ ?a = _ ?b ] => assert (TTTT : a = b) end.
               { apply nat_trans_eq; try assumption.
                 intros. simpl. rewrite functor_id. apply pathsinv0, id_right.
               }
               apply maponpaths. apply TTTT.
             }
             apply (nat_trans_eq_pointwise TTT).
          - repeat rewrite assoc.
            repeat rewrite assoc in HXX.
            apply (!HXX).
         }
      * clear HXX.
        assert (H4 := fbracket_τ T (identity _ )).
        assert (H5:= nat_trans_eq_pointwise H4 x); clear H4.
        unfold μ_2.
        repeat rewrite <- assoc.
        simpl in H5; repeat rewrite <- assoc in H5.
        eapply pathscomp0. apply maponpaths. apply maponpaths. apply maponpaths. apply H5.
        clear H5.
        rewrite functor_id.
        rewrite id_left.
        repeat rewrite assoc.
        apply cancel_postcomposition.
        assert (H4':= fbracket_τ T (identity _ )).
        assert (H6:= nat_trans_eq_pointwise H4' (pr1 `T x)); clear H4'.
        simpl in H6.
        unfold coproduct_nat_trans_in2_data in H6. simpl in H6.
        rewrite assoc in H6.
        apply H6.
Qed.

End third_monad_law_with_assoc.

(* for Travis *)
Check third_monad_law_from_hss.

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
    pathvia (pr1 μ_3 c).
    + set (H1 := μ_3_T_μ_2_μ_2).
      set (H2 := nat_trans_eq_weq hs _ _ H1).
      apply pathsinv0, H2.
    + set (H1 :=  μ_3_μ_2_T_μ_2).
      set (H2 := nat_trans_eq_weq hs _ _ H1).
      apply pathsinv0, H2.
Qed.

Definition Monad_from_hss : Monad C.
Proof.
  exists Monad_data_from_hss.
  exact Monad_laws_from_hss.
Defined.

End mu_from_fbracket.

(** ** A functor from hss to monads *)

(** Objects are considered above, now morphisms *)

Definition Monad_Mor_laws_from_hssMor (T T' : hss CP H)(β : hssMor T T')
  : Monad_Mor_laws (T:=Monad_from_hss T) (T':=Monad_from_hss T') (pr1 (pr1 β)).
Proof.
  repeat split; simpl.
  - intro c.
    unfold μ_2. simpl.
    set (H':=isbracketMor_hssMor _ _ _ _ β).
    unfold isbracketMor in H'.
    set (H2:= H' _ (identity _ )).
    set (H3:=(nat_trans_eq_weq hs _ _ H2)).
    rewrite id_left in H3.
    simpl in H3.
    rewrite H3; clear H3 H2 H'.
    rewrite compute_fbracket.
    rewrite <- assoc.
    apply maponpaths.
    apply cancel_postcomposition.
    apply idpath.
  - unfold μ_0.
    intro c.
    set (H':=ptd_mor_commutes _  (ptd_from_alg_mor _ _ _ _ β)).
    apply H'.
Qed.

Definition Monad_Mor_from_hssMor {T T' : hss CP H}(β : hssMor T T')
  : Monad_Mor (Monad_from_hss T) (Monad_from_hss T')
  := tpair _ _ (Monad_Mor_laws_from_hssMor T T' β).


Definition hss_to_monad_functor_data : functor_data (hss_precategory CP H) (precategory_Monad C hs).
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

Definition hssMor_Monad_Mor_eq {T T' : hss CP H} (β β' : hssMor T T')
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



End monad_from_hss.
