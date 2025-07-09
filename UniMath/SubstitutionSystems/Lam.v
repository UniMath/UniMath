(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

- Specification of an initial morphism of substitution systems from
  lambda calculus with explicit flattening to lambda calculus



************************************************************)

Set Kernel Term Sharing.

Require Import UniMath.Foundations.PartD.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.BinSumOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.LiftingInitial.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.

Local Open Scope cat.

Section Lambda.

Context (C : category).

(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C]) .

Context (terminal : Terminal C)
        (CC : BinCoproducts C)
        (CP : BinProducts C).

Local Notation "'Ptd'" := (category_Ptd C).

Let CPEndC : BinCoproducts EndC := BinCoproducts_functor_precat _ _ CC.
Let EndEndC := [EndC, EndC].
Let CPEndEndC:= BinCoproducts_functor_precat _ _ CPEndC: BinCoproducts EndEndC.




Let one : C :=  @TerminalObject C terminal.

Context (KanExt : ∏ Z : precategory_Ptd C,
   RightKanExtension.GlobalRightKanExtensionExists C C
     (U Z) C).


Let Lam_S : Signature _ _ _ := Lam_Sig C terminal CC CP.
Let LamE_S : Signature _ _ _ := LamE_Sig C terminal CC CP.

(* assume initial algebra for signature Lam *)

Context (Lam_Initial : Initial
     (@category_FunctorAlg [C, C] (Id_H C CC Lam_S))).

Let Lam := InitialObject Lam_Initial.




(** bracket for Lam from the initial hss obtained via theorem 15+ *)

Definition LamHSS_Initial : Initial (hss_category CC Lam_S).
Proof.
  apply InitialHSS.
  - apply KanExt.
  - apply Lam_Initial.
Defined.
Let LamHSS := InitialObject LamHSS_Initial.

(** extract constructors *)


Definition Lam_Var : EndC ⟦functor_identity C, `Lam ⟧.
Proof.
  exact (η (pr1 LamHSS)).
Defined.

(* we later prefer leaving App and Abs bundled in the definition of LamE_algebra_on_Lam *)

Definition Lam_App_Abs :  [C, C]
   ⟦ (H C C C CC (App_H C CP) (Abs_H C terminal CC)) `Lam , `Lam ⟧.
Proof.
  exact (τ (pr1 LamHSS)).
Defined.

Definition Lam_App : [C, C] ⟦ (App_H C CP) `Lam , `Lam ⟧.
Proof.
  exact (BinCoproductIn1 (BinCoproducts_functor_precat _ _ _ _ _) · Lam_App_Abs).
Defined.

Definition Lam_Abs : [C, C] ⟦ (Abs_H C terminal CC) `Lam, `Lam ⟧.
Proof.
  exact (BinCoproductIn2 (BinCoproducts_functor_precat _ _ _ _ _) · Lam_App_Abs).
Defined.




(** * Definition of a "model" of the flattening arity in pure lambda calculus *)

(** we need a flattening in order to get a model for LamE *)

Definition Lam_Flatten :
  [C, C] ⟦ (Flat_H C) `Lam , `Lam ⟧.
Proof.
  exact (prejoin_from_hetsubst (hetsubst_from_hss _ _ _ LamHSS)).
Defined.


(** now get a LamE-algebra *)

Definition LamE_algebra_on_Lam : FunctorAlg (Id_H _ CC LamE_S).
Proof.
  exists ((*ob_from_algebra_ob _ _*) `Lam).
  use (BinCoproductArrow (CPEndC _ _ )).
  + exact Lam_Var.
  + use (BinCoproductArrow (CPEndC _ _ )).
    * apply Lam_App_Abs. (* do NOT destruct and reassemble more, use App_Abs directly *)
    * apply Lam_Flatten.
Defined.

Lemma τ_LamE_algebra_on_Lam : τ LamE_algebra_on_Lam =
                              BinCoproductArrow (CPEndC _ _ ) Lam_App_Abs Lam_Flatten.
Proof.
  apply BinCoproductIn2Commutes.
Defined.


(** now define bracket operation for a given [Z] and [f] *)

(** preparations for typedness *)
Local Definition helper_to: (ptd_from_alg_functor CC LamE_S LamE_algebra_on_Lam) --> (ptd_from_alg_functor CC Lam_S Lam).
Proof.
  use tpair.
    + apply (nat_trans_id _ ).
    + abstract
        (intro c; rewrite id_right
         ; apply BinCoproductIn1Commutes_left_dir;
         apply idpath).
Defined.

Local Definition helper_from: (ptd_from_alg_functor CC Lam_S Lam) --> (ptd_from_alg_functor CC LamE_S LamE_algebra_on_Lam).
Proof.
  use tpair.
    + apply (nat_trans_id _ ).
    + abstract
        (intro c; rewrite id_right ;
         apply BinCoproductIn1Commutes_right_dir;
         apply idpath) .
Defined.

(** this iso does nothing, but is needed to make the argument to [fbracket] below well-typed *)
(* maybe a better definition somewhere above could make this iso superfluous *)
(* maybe don't need iso, but only morphism *)
Local Definition bracket_property_for_LamE_algebra_on_Lam_helper : iso (ptd_from_alg_functor CC LamE_S LamE_algebra_on_Lam) (ptd_from_alg_functor CC Lam_S Lam).
Proof.
  unfold iso.
  exists helper_to.
  apply is_iso_from_is_z_iso.
  exists helper_from.
  abstract (
   split; [
    apply (invmap (eq_ptd_mor _ _));
    apply nat_trans_eq; [apply homset_property |] ;
    intro c ;
    apply id_left
                   |
    apply eq_ptd_mor_cat; (* idem *)
    apply (invmap (eq_ptd_mor _ _)) ;
    apply nat_trans_eq; [apply homset_property |];
    intro c ;
    apply id_left ]
           ).
Defined.


Definition fbracket_for_LamE_algebra_on_Lam (Z : Ptd)
   (f : Ptd ⟦ Z, ptd_from_alg_functor CC LamE_S LamE_algebra_on_Lam ⟧ ) :
   [C, C]⟦ functor_composite (U Z) `LamE_algebra_on_Lam, `LamE_algebra_on_Lam ⟧ .
Proof.
  exact (fbracket LamHSS (f · bracket_property_for_LamE_algebra_on_Lam_helper)).
Defined.

(** Main lemma: our "model" for the flatten arity in pure lambda calculus is compatible with substitution *)

Lemma bracket_property_for_LamE_algebra_on_Lam (Z : Ptd)
  (f : Ptd ⟦ Z, ptd_from_alg LamE_algebra_on_Lam ⟧)
 :
   bracket_property (nat_trans_fix_snd_arg [C, C] Ptd [C, C] (θ_source LamE_S)
            (θ_target LamE_S) (theta LamE_S) Z) LamE_algebra_on_Lam f (fbracket_for_LamE_algebra_on_Lam Z f).
Proof.
  (* Could we have this in a more declarative style? *)
  assert (Hyp := pr2 (pr1 (pr2 LamHSS _ (f · bracket_property_for_LamE_algebra_on_Lam_helper)))).
  apply parts_from_whole in Hyp.
  apply whole_from_parts.
  split.
  - (* the "easy" eta part *)
    apply pr1 in Hyp.
    apply (maponpaths (λ x, x · #U (inv_from_iso bracket_property_for_LamE_algebra_on_Lam_helper))) in Hyp.
    rewrite <- functor_comp in Hyp.
    rewrite <- assoc in Hyp.
    rewrite iso_inv_after_iso in Hyp.
    rewrite id_right in Hyp.
    etrans; [ exact Hyp |].
    clear Hyp.
    fold (fbracket LamHSS (f · bracket_property_for_LamE_algebra_on_Lam_helper)).
    unfold fbracket_for_LamE_algebra_on_Lam.
    match goal with |[ |- _· _ · ?h = _  ] =>
         assert (idness : h = nat_trans_id _) end.
    { apply nat_trans_eq_alt.
      intro c.
      unfold functor_ptd_forget.
      apply id_left.
    }
    rewrite idness. clear idness.
    rewrite id_right.
    (* does not work:
       apply cancel_postcomposition.
       although the terms are of identical type:
    match goal with | [ |- _ · ?l = _ ] => let ty:= (type of l) in idtac ty end.
(*
([C, C] hs
 ⟦ functor_composite (U Z) (functor_from_algebra_ob C hs CC Lam_S LamHSS)
   :[C, C] hs, LamHSS ⟧)
*)
    match goal with | [ |- _ = _ · ?l ] => let ty:= (type of l) in idtac ty end.
(*
([C, C] hs
 ⟦ functor_composite (U Z) (functor_from_algebra_ob C hs CC Lam_S LamHSS)
   :[C, C] hs, LamHSS ⟧)
*)
*)
    apply nat_trans_eq_alt.
    intro c.
    apply cancel_postcomposition.
    apply BinCoproductIn1Commutes_right_dir.
    apply idpath.
    (* this proof did not work with pointedness but with brute force *)
  - (* now the difficult case of the domain-specific constructors *)
    destruct Hyp as [_ Hyp2].
    fold (fbracket LamHSS (f · bracket_property_for_LamE_algebra_on_Lam_helper)) in Hyp2.
    unfold fbracket_for_LamE_algebra_on_Lam.
    apply nat_trans_eq_alt.
    intro c.

    (* from here slightly interesting, because it is crucial to see that
       the τ considered here is a BinCoproduct arrow *)

    rewrite τ_LamE_algebra_on_Lam.
    etrans; [ apply cancel_postcomposition ; apply BinCoproductOfArrows_comp |].
    etrans; [ apply precompWithBinCoproductArrow |].
    apply pathsinv0.

    (* showing that a diagram of coproduct arrows splits into two is slightly cumbersome,
       but a general theorem seems difficult to formulate

       instead we apply [BinCoproductArrowUnique] and then use the coproduct beta laws in
       each branch; this gives precisely what we want *)

    apply BinCoproductArrowUnique.
    + etrans; [ apply assoc |].
      etrans. { apply cancel_postcomposition. apply BinCoproductIn1Commutes. }
      assert (T:= nat_trans_eq_pointwise Hyp2 c).
      clear Hyp2.
      apply pathsinv0.
      assumption.

    (* There should be a more general hypothesis than 'Hyp' defined above,
       one where one has a quantification over maps 'f', no? *)

    + clear Hyp2.
      etrans; [ apply assoc |].
      etrans. { apply cancel_postcomposition. apply BinCoproductIn2Commutes. }
      unfold Lam_Flatten.

    (* from here on 'simpl' is feasible
       after some opacification, at least *)
      Opaque fbracket.
      Opaque LamHSS.
      set (X := f · bracket_property_for_LamE_algebra_on_Lam_helper).

      assert (TT := compute_fbracket C CC Lam_S LamHSS(Z:=Z)).
      simpl in *.
      assert (T3 := TT  X); clear TT.
      unfold X; unfold X in T3; clear X.
      do 2 rewrite id_left.

      Local Notation "⦃ f ⦄" := (fbracket _ f)(at level 0).
      (* written '\{{' and '\}}', respectively *)

      set (Tη := ptd_from_alg _ ).

      destruct Z as [Z e]. simpl in *.
      set (T := Lam).

      (* now we want to rewrite with T3 in 3 places *)

      assert (T3' := nat_trans_eq_pointwise T3 c).
      simpl in *.
      match goal with |[ T3' : _ = ?f |- ?a · _ = _ ] => transitivity (a · f) end.
      { apply maponpaths. apply T3'. }

      repeat rewrite assoc.
(*
    apply cancel_postcomposition. (* that's a bad idea, because it fucks up use of third monad law and
                                      leads to something that is generally false *)
 *)
      etrans.
      2: { do 2 apply cancel_postcomposition. do 3 apply maponpaths. apply pathsinv0, T3'. }
      clear T3'.
      apply pathsinv0.

      assert (T3' := nat_trans_eq_pointwise T3 (pr1 T c)).
      simpl in T3'. rewrite id_right in T3'.
      etrans. { apply cancel_postcomposition. apply maponpaths. exact T3'. }
      clear T3'.

      apply pathsinv0.
      destruct f as [f fptdmor]. simpl in *.

      repeat rewrite assoc.

      rewrite <- (functor_comp (pr1 T)).
      repeat rewrite <- assoc.
      etrans.
      2: { apply cancel_postcomposition. apply maponpaths. apply (nat_trans_ax e). }
      repeat rewrite assoc.
      rewrite <- (functor_comp (pr1 T)).

      assert (X := fptdmor ((pr1 T) c)). clear T3 fptdmor.
      unfold functor_identity_data. simpl.

      apply pathsinv0.
      etrans. { do 2 apply cancel_postcomposition. apply maponpaths. repeat rewrite <- assoc.
      do 2 apply maponpaths. apply X. }
      clear X.

      assert (X := Monad_law_2_from_hss _ CC Lam_S LamHSS ((pr1 T) c)).
      unfold μ_0 in X. unfold μ_2 in X.

      (*
      change (pr1 ⦃ identity (ptd_from_alg (pr1 LamHSS)) ⦄ c) with (prejoin_from_hetsubst LamHSS c).
      (* does not do anything *)
*)

      etrans.
      { do 2 apply cancel_postcomposition. apply maponpaths. apply assoc. }
      rewrite (functor_comp (pr1 T)).
      repeat rewrite <- assoc.

      match goal with |[ X : ?e = _ |- _ · (?a · (?b · _))  = _ ] =>
                         assert (X' : e = a · b) end.
      { apply cancel_postcomposition. apply maponpaths.
        cbn. apply pathsinv0, BinCoproductIn1Commutes. }
      rewrite X' in X. clear X'.

      etrans. { apply maponpaths. rewrite assoc. apply cancel_postcomposition. apply X. }
      clear X.

      rewrite id_left.

      assert (μ_2_nat := nat_trans_ax (μ_2 C CC Lam_S LamHSS)).
      assert (X := μ_2_nat _ _ (f c · identity (pr1 Lam c))).
      unfold μ_2 in X.

      etrans. 2: { rewrite assoc. apply cancel_postcomposition. apply X. }
      clear X.



      rewrite functor_comp.
      repeat rewrite <- assoc.
      apply maponpaths.

      assert (X := third_monad_law_from_hss _ CC Lam_S LamHSS).
      assert (X' := nat_trans_eq_pointwise X). clear X.
      simpl in X'.

      etrans; [ apply X' |].
      clear X'. apply cancel_postcomposition. apply id_left.
Qed.

(** * Uniqueness of the bracket operation *)
(** That is a consequence of uniqueness of that operation for a larger signature, namely
    for that of lambda calculus with flattening.
    We thus only have to extract the relevant parts, which is still a bit cumbersome.
*)

Lemma bracket_for_LamE_algebra_on_Lam_unique (Z : Ptd)
  (f : Ptd ⟦ Z, ptd_from_alg LamE_algebra_on_Lam ⟧)
 :
   ∏
   t : ∑
       h,
       bracket_property (nat_trans_fix_snd_arg _ _ _ _ _ (theta LamE_S) Z) _ f h,
   t =
   tpair
     (λ h,
      bracket_property (nat_trans_fix_snd_arg _ _ _ _ _ (theta LamE_S) Z) _ f h)
     (fbracket_for_LamE_algebra_on_Lam Z f) (bracket_property_for_LamE_algebra_on_Lam Z f).
Proof.
  intro t.
  apply subtypePath.
  - intro; apply (isaset_nat_trans (homset_property C)).
  - destruct t as [t Ht]; cbn.
    unfold fbracket_for_LamE_algebra_on_Lam.
    apply (fbracket_unique LamHSS).
    split.
    + apply parts_from_whole in Ht. destruct Ht as [H1 _].
      apply nat_trans_eq_alt.
      intro c.
      assert (HT := nat_trans_eq_pointwise H1 c).
      cbn.
      rewrite id_right.
      etrans; [ apply HT |].
      cbn. repeat rewrite assoc. apply cancel_postcomposition.
      apply BinCoproductIn1Commutes.
    + apply parts_from_whole in Ht. destruct Ht as [_ H2].
      assert (H2better: nat_trans_fix_snd_arg [C, C] Ptd [C, C] (θ_source LamE_S) (θ_target LamE_S) (theta LamE_S) Z
                          `LamE_algebra_on_Lam · # LamE_S t ·
                          BinCoproductArrow (CPEndC _ _ ) Lam_App_Abs Lam_Flatten =
                          BinCoproductArrow (CPEndC _ _ ) Lam_App_Abs Lam_Flatten •• U Z · t).
      { rewrite <- τ_LamE_algebra_on_Lam.
        exact H2. }
      clear H2.
      apply nat_trans_eq_alt.
      intro c.
      assert (HT := nat_trans_eq_pointwise H2better c).
      match goal with |[_ : ?e = ?f |- _ ] =>
                         assert (X: BinCoproductIn1 _ · e = BinCoproductIn1 _ · f) end.
      { apply maponpaths . assumption. }
      clear HT. clear H2better.

      match goal with |[X : _ = ?f |- _ ] => transitivity f end.

      2: { etrans; [apply assoc |].
           apply cancel_postcomposition. apply BinCoproductIn1Commutes.
      }
      match goal with |[_ : ?e = _ |- _ ] => transitivity e end.
      2: apply X.
      clear X.

      apply pathsinv0.
      etrans; [ apply assoc |].
      etrans. { apply cancel_postcomposition. apply assoc. }
      etrans. { apply cancel_postcomposition. apply cancel_postcomposition.
                apply BinCoproductIn1Commutes. }

      repeat rewrite <- assoc.
      etrans. { apply maponpaths. apply assoc. }

      etrans. { apply maponpaths. apply cancel_postcomposition. apply BinCoproductIn1Commutes. }

      etrans. { apply maponpaths. apply assoc'. }
      simpl. do 2 apply maponpaths.
      apply BinCoproductIn1Commutes.
Qed.


Definition bracket_for_LamE_algebra_on_Lam_at (Z : Ptd)
  (f : Ptd ⟦ Z, ptd_from_alg LamE_algebra_on_Lam ⟧)
  :
    bracket_at C CC LamE_S (nat_trans_fix_snd_arg _ _ _ _ _ (theta LamE_S) Z) LamE_algebra_on_Lam f.
Proof.
  use tpair.
  - exists (fbracket_for_LamE_algebra_on_Lam Z f).
    apply (bracket_property_for_LamE_algebra_on_Lam Z f).
  - simpl; apply bracket_for_LamE_algebra_on_Lam_unique.
Defined.

Definition bracket_for_LamE_algebra_on_Lam : bracket (theta LamE_S) LamE_algebra_on_Lam.
Proof.
  intros Z f.
  simpl.
  apply bracket_for_LamE_algebra_on_Lam_at.
Defined.

Definition LamE_model_on_Lam : hss CC LamE_S.
Proof.
  exists LamE_algebra_on_Lam.
  exact bracket_for_LamE_algebra_on_Lam.
Defined.

(* assume initial algebra for signature LamE *)

Context (LamE_Initial : Initial
     (@category_FunctorAlg [C, C]
        (Id_H C CC LamE_S))).


Definition LamEHSS_Initial : Initial (hss_category CC LamE_S).
Proof.
  apply  InitialHSS.
  - apply KanExt.
  - apply LamE_Initial.
Defined.
Let LamEHSS := InitialObject LamEHSS_Initial.

(** * Specification of a morphism from lambda calculus with flattening to pure lambda calculus *)

Definition FLATTEN : (hss_category CC LamE_S) ⟦LamEHSS, LamE_model_on_Lam⟧
  := InitialArrow _ _ .

End Lambda.
