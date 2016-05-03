(**

From signatures to monads

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.Basics.PartD.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseCoproduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseProduct.
Require Import UniMath.CategoryTheory.EndofunctorsMonoidal.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.ProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LamSignature.
Require Import UniMath.SubstitutionSystems.Lam.
Require Import UniMath.SubstitutionSystems.LiftingInitial.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.Notation.

Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.chains.
Require Import UniMath.CategoryTheory.cocontfunctors.
Require Import UniMath.CategoryTheory.lists.
Require Import UniMath.CategoryTheory.HorizontalComposition.

Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "'HSET2'":= ([HSET, HSET, has_homsets_HSET]) .


Section θ_from_δ.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable G : functor C C.

(** The precategory of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (precategory_Ptd C hsC).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hsC]) .

Definition δ_source_ob (Ze : Ptd) : EndC := G • pr1 Ze.
Definition δ_source_mor {Ze Ze' : Ptd} (α : Ze --> Ze') :
  δ_source_ob Ze --> δ_source_ob Ze' := hor_comp (pr1 α) (nat_trans_id G).

Definition δ_source_functor_data : functor_data Ptd EndC.
Proof.
exists δ_source_ob.
exact (@δ_source_mor).
Defined.

Lemma is_functor_δ_source : is_functor δ_source_functor_data.
Proof.
split; simpl.
- intro Ze.
  apply (nat_trans_eq hsC).
  now intro c; simpl; rewrite functor_id, id_right.
- intros [Z e] [Z' e'] [Z'' e''] [α a] [β b].
  apply (nat_trans_eq hsC); intro c; simpl in *.
  now rewrite !id_left, functor_comp.
Qed.

Definition δ_source : functor Ptd EndC := tpair _ _ is_functor_δ_source.

Definition δ_target_ob (Ze : Ptd) : EndC := pr1 Ze • G.
Definition δ_target_mor {Ze Ze' : Ptd} (α : Ze --> Ze') :
  δ_target_ob Ze --> δ_target_ob Ze' := hor_comp (nat_trans_id G) (pr1 α).

Definition δ_target_functor_data : functor_data Ptd EndC.
Proof.
exists δ_target_ob.
exact (@δ_target_mor).
Defined.

Lemma is_functor_δ_target : is_functor δ_target_functor_data.
Proof.
split; simpl.
- intro Ze.
  apply (nat_trans_eq hsC).
  now intro c; simpl; rewrite functor_id, id_right.
- intros [Z e] [Z' e'] [Z'' e''] [α a] [β b].
  apply (nat_trans_eq hsC); intro c; simpl in *.
  now rewrite !functor_id, !id_right.
Qed.

Definition δ_target : functor Ptd EndC := tpair _ _ is_functor_δ_target.

Hypothesis δ : δ_source ⟶ δ_target.

Let precompG := (pre_composition_functor _ _ _ hsC hsC G).

Definition θ_from_δ : θ_source precompG ⟶ θ_target precompG.
Proof.
mkpair.
- intros XZe.
  set (X := pr1 XZe); set (Z := pr1 (pr2 XZe)).
  set (F1 := α_functor _ G Z X).
  set (F2 := post_whisker (δ (pr2 XZe)) X).
  set (F3 := α_functor_inv _ Z G X).
  simpl in *.
  apply (nat_trans_comp F3 (nat_trans_comp F2 F1)).
- intros [F1 X1] [F2 X2] [α X]; simpl in *.
  apply (nat_trans_eq hsC); intro c; simpl; rewrite !id_right, !id_left.
  generalize (nat_trans_eq_pointwise (nat_trans_ax δ X1 X2 X) c); simpl.
  rewrite id_left, functor_id, id_right.
  intros H.
  rewrite <- assoc.
  eapply pathscomp0.
    eapply maponpaths, pathsinv0, functor_comp.
  eapply pathscomp0.
    eapply maponpaths, maponpaths, H.
  rewrite assoc; apply pathsinv0.
  eapply pathscomp0.
    eapply cancel_postcomposition, nat_trans_ax.
  now rewrite <- assoc, <- functor_comp.
Defined.

(* Should be ρ_G^-1 ∘ λ_G ? *)
Definition δ_law1 : UU := δ (id_Ptd C hsC) = nat_trans_id G.
Hypothesis (H1 : δ_law1).

Lemma θ_Strength1_int_from_δ : θ_Strength1_int θ_from_δ.
Proof.
intro F.
apply (nat_trans_eq hsC); intro c; simpl.
rewrite id_left, !id_right.
eapply pathscomp0;
  [eapply maponpaths, (nat_trans_eq_pointwise H1 c)|].
apply functor_id.
Qed.

Require Import UniMath.CategoryTheory.PointedFunctorsComposition.

(* set (F1 := α_functor _ G Z Z'). *)
(* set (F2 := post_whisker (δ Ze) Z'). *)
(* set (F3 := α_functor_inv _ Z G Z'). *)
(* set (F4 := pre_whisker Z (δ Ze')). *)
(* set (F5 := α_functor _ Z Z' G). *)
(* set (D' := nat_trans_comp F5 (nat_trans_comp F4 (nat_trans_comp F3 (nat_trans_comp F2 F1)))). *)

Let D' Ze Ze' :=
  nat_trans_comp (α_functor _ (pr1 Ze) (pr1 Ze') G)
 (nat_trans_comp (pre_whisker (pr1 Ze) (δ Ze'))
 (nat_trans_comp (α_functor_inv _ (pr1 Ze) G (pr1 Ze'))
 (nat_trans_comp (post_whisker (δ Ze) (pr1 Ze'))
                 (α_functor _ G (pr1 Ze) (pr1 Ze'))))).

Definition δ_law2 : UU := forall Ze Ze', δ (Ze p• Ze') = D' Ze Ze'.
Hypothesis H2 : δ_law2.

Lemma θ_Strength2_int_from_δ : θ_Strength2_int θ_from_δ.
Proof.
intros F Ze Ze'; simpl.
set (Z := pr1 Ze); set (Z' := pr1 Ze').
apply (nat_trans_eq hsC); intro c; simpl.
generalize (nat_trans_eq_pointwise (H2 Ze Ze') c); simpl.
rewrite !id_left, !id_right; intro H.
eapply pathscomp0;
  [eapply maponpaths, H|].
apply functor_comp.
Qed.

Definition θ_from_δ_Signature : Signature C hsC.
Proof.
mkpair.
- apply precompG.
- mkpair.
  + apply θ_from_δ.
  + apply (θ_Strength1_int_from_δ,,θ_Strength2_int_from_δ).
Defined.

End θ_from_δ.

Section δ_mul.

Variable C : precategory.
Variable hsC : has_homsets C.
Variable G1 G2 : functor C C.

Variable δ1 : δ_source C hsC G1 ⟶ δ_target C hsC G1.
Variable δ2 : δ_source C hsC G2 ⟶ δ_target C hsC G2.
Hypothesis (δ1_law1 : δ_law1 C hsC G1 δ1) (δ1_law2 : δ_law2 C hsC G1 δ1).
Hypothesis (δ2_law1 : δ_law1 C hsC G2 δ2) (δ2_law2 : δ_law2 C hsC G2 δ2).

Definition δ_comp : δ_source C hsC (G2 • G1 : [C,C,hsC]) ⟶ δ_target C hsC (G2 • G1 : [C,C,hsC]).
Proof.
mkpair.
- intros Ze.
  set (Z := pr1 Ze).
  set (F1 := α_functor_inv _ Z G1 G2).
  set (F2 := post_whisker (δ1 Ze) G2).
  set (F3 := α_functor _ G1 Z G2).
  set (F4 := pre_whisker G1 (δ2 Ze)).
  set (F5 := α_functor_inv _ G1 G2 Z).
  simpl in *.
  exact (nat_trans_comp F1 (nat_trans_comp F2 (nat_trans_comp F3 (nat_trans_comp F4 F5)))).
- intros [Z e] [Z' e'] [α X]; simpl in *.
  apply (nat_trans_eq hsC); intro c; simpl; rewrite functor_id, !id_right, !id_left.
eapply pathscomp0.
rewrite assoc.
eapply cancel_postcomposition.
eapply pathsinv0.
apply functor_comp.
simpl in *.
eapply pathscomp0.
eapply cancel_postcomposition.
eapply maponpaths.
generalize (nat_trans_eq_pointwise (nat_trans_ax δ1 (Z,,e) (Z',, e') (α,,X)) c).
simpl; rewrite id_left, functor_id, id_right; intro H1.
apply H1.
rewrite functor_comp, <- assoc.
eapply pathscomp0.
eapply maponpaths.
generalize (nat_trans_eq_pointwise (nat_trans_ax δ2 (Z,,e) (Z',, e') (α,,X)) (G1 c)).
simpl; rewrite id_left, functor_id, id_right; intro H2.
apply H2.
now rewrite assoc.
Defined.

Lemma δ_comp_law1 : δ_law1 C hsC (G2 • G1 : [C,C,hsC]) δ_comp.
Proof.
apply (nat_trans_eq hsC); intro c; simpl.
rewrite !id_left, id_right.
unfold δ_law1 in *.
eapply pathscomp0.
eapply maponpaths.
apply (nat_trans_eq_pointwise δ2_law1 (G1 c)).
eapply pathscomp0.
eapply cancel_postcomposition.
eapply maponpaths.
apply (nat_trans_eq_pointwise δ1_law1 c).
now rewrite id_right; apply functor_id.
Qed.

Lemma δ_comp_law2 : δ_law2 C hsC (G2 • G1 : [C,C,hsC]) δ_comp.
Proof.
intros Ze Ze'.
apply (nat_trans_eq hsC); intro c; simpl.
rewrite !id_left, !id_right.
eapply pathscomp0.
eapply cancel_postcomposition.
eapply maponpaths.
apply (nat_trans_eq_pointwise (δ1_law2 Ze Ze') c).
eapply pathscomp0.
eapply maponpaths.
apply (nat_trans_eq_pointwise (δ2_law2 Ze Ze') (G1 c)).
simpl.
rewrite !id_left, !id_right.
eapply pathscomp0.
eapply cancel_postcomposition.
apply functor_comp.
rewrite <- !assoc.
apply maponpaths.
destruct Ze as [Z e]; simpl in *.
destruct Ze' as [Z' e']; simpl in *.
rewrite assoc.
eapply pathscomp0.
eapply cancel_postcomposition.
apply (nat_trans_ax (δ2 (Z',,e')) _ _ (pr1 (δ1 (Z,, e)) c)).
simpl.
rewrite <- !assoc.
apply maponpaths.
apply pathsinv0.
now apply functor_comp.
Qed.

End δ_mul.

Section option_sig.

Variables (C : precategory) (hsC : has_homsets C) (TC : Terminal C) (CC : Coproducts C).

Local Notation "'Ptd'" := (precategory_Ptd C hsC).

Let opt := option_functor C CC TC.

Definition δ_option_mor (Ze : Ptd) (c : C) :  C ⟦ CoproductObject C (CC TC (pr1 Ze c)),
                                                  pr1 Ze (CoproductObject C (CC TC c)) ⟧.
Proof.
apply (@CoproductArrow _ _ _ (CC TC (pr1 Ze c)) (pr1 Ze (CoproductObject C (CC TC c)))).
- apply (CoproductIn1 _ (CC TC c) ;; pr2 Ze (CoproductObject _ (CC TC c))).
- apply (# (pr1 Ze) (CoproductIn2 _ (CC TC c))).
Defined.

Lemma is_nat_trans_δ_option_mor (Ze : Ptd) :
  is_nat_trans (δ_source C hsC opt Ze : functor C C) (δ_target C hsC opt Ze : functor C C)
     (δ_option_mor Ze).
Proof.
intros a b f; simpl.
destruct Ze as [Z e].
unfold coproduct_functor_mor; simpl.
eapply pathscomp0.
apply precompWithCoproductArrow.
rewrite id_left.
apply pathsinv0.
apply CoproductArrowUnique.
- eapply pathscomp0.
  rewrite assoc.
  eapply cancel_postcomposition.
  apply CoproductIn1Commutes.
  rewrite <- assoc.
  eapply pathscomp0.
  eapply maponpaths, pathsinv0.
  apply (nat_trans_ax e _ _ (CoproductOfArrows C (CC TC a) (CC TC b) (identity TC) f)).
  simpl.
  rewrite assoc.
  apply cancel_postcomposition.
  eapply pathscomp0.
  apply CoproductOfArrowsIn1.
  now rewrite id_left.
- rewrite assoc.
  eapply pathscomp0.
  eapply cancel_postcomposition.
  apply CoproductIn2Commutes.
  rewrite <- !functor_comp.
  apply maponpaths.
  now apply CoproductOfArrowsIn2.
Qed.

Lemma is_nat_trans_δ_option_mor_nat_trans : is_nat_trans (δ_source_functor_data C hsC opt)
     (δ_target_functor_data C hsC opt)
     (λ Ze : Ptd, δ_option_mor Ze,, is_nat_trans_δ_option_mor Ze).
Proof.
intros [Z e] [Z' e'] [α X]; simpl in *.
apply (nat_trans_eq hsC); intro c; simpl.
rewrite id_left, functor_id, id_right.
unfold coproduct_functor_mor, coproduct_functor_ob; simpl.
unfold δ_option_mor.
simpl.
rewrite precompWithCoproductArrow.
apply pathsinv0.
apply CoproductArrowUnique.
-
rewrite id_left, assoc.
eapply pathscomp0.
eapply cancel_postcomposition.
apply CoproductIn1Commutes.
rewrite <- assoc.
apply maponpaths.
apply X.
-
rewrite assoc.
eapply pathscomp0.
eapply cancel_postcomposition.
apply CoproductIn2Commutes.
apply nat_trans_ax.
Qed.

Definition δ_option : δ_source C hsC opt ⟶ δ_target C hsC opt.
Proof.
mkpair.
- intro Ze.
  apply (tpair _ (δ_option_mor Ze) (is_nat_trans_δ_option_mor Ze)).
- apply is_nat_trans_δ_option_mor_nat_trans.
Defined.

Lemma δ_law1_option : δ_law1 C hsC opt δ_option.
Proof.
apply (nat_trans_eq hsC); intro c; simpl.
unfold δ_option_mor, coproduct_functor_ob; simpl.
rewrite id_right.
apply pathsinv0, Coproduct_endo_is_identity.
- apply CoproductIn1Commutes.
- apply CoproductIn2Commutes.
Qed.

Lemma δ_law2_option : δ_law2 C hsC opt δ_option.
Proof.
intros [Z e] [Z' e'].
apply (nat_trans_eq hsC); intro c; simpl.
unfold δ_option_mor, coproduct_functor_ob; simpl.
rewrite !id_left, id_right.
apply pathsinv0.
apply CoproductArrowUnique.
-
rewrite assoc.
eapply pathscomp0.
eapply cancel_postcomposition.
apply CoproductIn1Commutes.
rewrite <- assoc.
eapply pathscomp0.
eapply maponpaths.
eapply pathsinv0.
apply (nat_trans_ax e').
simpl.
rewrite assoc.
eapply pathscomp0.
eapply cancel_postcomposition.
apply CoproductIn1Commutes.
rewrite <- !assoc.
apply maponpaths.
apply (nat_trans_ax e').
-
rewrite assoc.
eapply pathscomp0.
eapply cancel_postcomposition.
apply CoproductIn2Commutes.
eapply pathscomp0.
eapply pathsinv0.
apply functor_comp.
apply maponpaths.
apply CoproductIn2Commutes.
Qed.

Definition precomp_option_Signature : Signature C hsC :=
  θ_from_δ_Signature _ hsC opt δ_option δ_law1_option δ_law2_option.

End option_sig.

(* S : SIG *)
(* |->  # some hacking needed *)
(* functor(S) : functor [Set,Set] [Set,Set] *)
(* |->  # exists because func(S) is omega-cocont *)
(* Initial (Id + functor(S)) *)
(* |->  # see LiftingInitial.v *)
(* I:= Initial (HSS(func(S), \theta) *)
(* |->  # see MonadsFromSubstitutionSystems.v *)
(* M := Monad_from_HSS(I)    # *)
Section SigToMonad.

Local Definition has_homsets_HSET2 : has_homsets HSET2.
Proof.
apply functor_category_has_homsets.
Defined.

Local Definition ProductsHSET2 : Products HSET2.
Proof.
apply (Products_functor_precat _ _ ProductsHSET).
Defined.

Local Definition CoproductsHSET2 : Coproducts HSET2.
Proof.
apply (Coproducts_functor_precat _ _ CoproductsHSET).
Defined.

Local Lemma has_exponentials_HSET2 : has_exponentials  ProductsHSET2.
Proof.
apply has_exponentials_functor_HSET, has_homsets_HSET.
Defined.

(* Specialized notations for HSET2 *)

(* Notation "' x" := (omega_cocont_constant_functor _ _ has_homsets_HSET2 x) *)
(*                     (at level 10) : cocont_functor_hset_scope. *)

Local Notation "'Id'" := (omega_cocont_functor_identity _ has_homsets_HSET2).

Local Notation "F * G" :=
  (omega_cocont_product_functor _ _ ProductsHSET2 _
     has_exponentials_HSET2 has_homsets_HSET2 has_homsets_HSET2 F G).

Local Notation "F + G" :=
  (omega_cocont_coproduct_functor _ _ ProductsHSET2 CoproductsHSET2
     has_homsets_HSET2 has_homsets_HSET2 F G).


Definition Sig : UU := list (list nat).

Let precomp_option := omega_cocont_pre_composition_functor _ _ _
                        (option_functor HSET CoproductsHSET TerminalHSET) has_homsets_HSET has_homsets_HSET cats_LimsHSET.

Let optionHSET := (option_functor HSET CoproductsHSET TerminalHSET).

(* This would have been nice, but it adds an extra Id in the end *)
(* Local Definition SigToFunctor_helper2 (n : nat) : omega_cocont_functor HSET2 HSET2 := *)
(*   omega_cocont_iter_functor has_homsets_HSET2 (precomp_option) n. *)

Fixpoint iter_functor1 {C : precategory} (F : functor C C) (n : nat) : functor C C := match n with
  | O => F
  | S n' => functor_composite (iter_functor F n') F
  end.

(* This constructs: _ o option^n *)
(* Local Definition precomp_option_iter (n : nat) : omega_cocont_functor HSET2 HSET2 := match n with *)
(*   | O => Id *)
(*   | S n => omega_cocont_pre_composition_functor _ _ _ *)
(*              (iter_functor1 optionHSET n) has_homsets_HSET has_homsets_HSET cats_LimsHSET *)
(*   end. *)

(* (* Old version: *) *)
(* (* Local Fixpoint precomp_option_iter (n : nat) : omega_cocont_functor HSET2 HSET2 := match n with *) *)
(* (*   | O => Id *) *)
(* (*   | S O => precomp_option *) *)
(* (*   | S n' => let G := omega_cocont_pre_composition_functor _ _ _ *) *)
(* (*                        (option_functor HSET CoproductsHSET TerminalHSET) has_homsets_HSET has_homsets_HSET cats_LimsHSET *) *)
(* (*                (* is this order correct???? *) *) *)
(* (*             in omega_cocont_functor_composite has_homsets_HSET2 G (iter_precomp_option n') *) *)
(* (*   end. *) *)

(* (* Definition SigToFunctor_helper2_Signature (n : nat) : Signature HSET has_homsets_HSET. *) *)
(* (* Proof. *) *)
(* (* mkpair. *) *)
(* (* - apply (precom n). *) *)
(* (* - mkpair; simpl. *) *)
(* (* + *) *)

(* Local Definition arity_to_functor : list nat -> omega_cocont_functor HSET2 HSET2. *)
(* Proof. *)
(* intro l. *)
(* generalize (map_list precomp_option_iter l). *)
(* apply foldr1_list. *)
(* - intros F G. *)
(*   apply (F * G). *)
(* - apply Id. *)
(* Defined. *)

(* Arguments arity_to_functor : simpl never. *)

(* Definition SigToFunctor : Sig -> omega_cocont_functor HSET2 HSET2. *)
(* Proof. *)
(* use foldr_list. *)
(* - intros l F. *)
(*   apply (arity_to_functor l + F). *)
(* - apply Id. *)
(* Defined. *)


(* New version *)

Definition precomp_option_iter (n : nat) : functor HSET2 HSET2 := match n with
  | O => functor_identity HSET2
  | S n => pre_composition_functor _ _ _ has_homsets_HSET _ (iter_functor1 optionHSET n)
  end.

Arguments iter_functor1 : simpl never.

Lemma is_omega_cocont_precomp_option_iter (n : nat) : is_omega_cocont (precomp_option_iter n).
Proof.
destruct n; simpl.
- apply (is_omega_cocont_functor_identity _ has_homsets_HSET2).
- apply (is_omega_cocont_pre_composition_functor _ _ _ (iter_functor1 optionHSET n) _ _ cats_LimsHSET).
Qed.

(* Unset Printing Notations. *)
(* About θ_source. *)
(* About θ_target. *)

Definition apa (n : nat) : Σ
   θ : θ_source_functor_data _ _ (precomp_option_iter n)
       ⟶ θ_target_functor_data _ _ (precomp_option_iter n),
       θ_Strength1_int θ × θ_Strength2_int θ.
Admitted.

Definition precomp_option_iter_Signature (n : nat) : Signature HSET has_homsets_HSET.
Proof.
mkpair.
- apply (precomp_option_iter n).
- destruct n.
Defined.

Definition precomp_option_Signature : Signature HSET has_homsets_HSET.
Proof.
use (θ_from_δ_Signature _ _ optionHSET).
- mkpair.
  + intros [Z e]; simpl in *.
admit.
+ admit.
- admit.
Admitted.

Lemma is_omega_cocont_precomp_iter_Signature (n : nat) : is_omega_cocont (precomp_option_iter_Signature n).
Proof.
apply is_omega_cocont_precomp_option_iter.
Qed.

(* Local Definition arity_to_functor : list nat -> omega_cocont_functor HSET2 HSET2. *)
(* Proof. *)
(* intro l. *)
(* generalize (map_list precomp_option_iter l). *)
(* apply foldr1_list. *)
(* - intros F G. *)
(*   apply (F * G). *)
(* - apply Id. *)
(* Defined. *)

(* Arguments arity_to_functor : simpl never. *)

Lemma is_omega_cocont_Product_of_Signatures (S1 S2 : Signature HSET has_homsets_HSET)
  (h1 : is_omega_cocont S1) (h2 : is_omega_cocont S2) :
  is_omega_cocont (Product_of_Signatures _ _ ProductsHSET S1 S2).
Proof.
destruct S1 as [F1 [F2 [F3 F4]]]; simpl in *.
destruct S2 as [G1 [G2 [G3 G4]]]; simpl in *.
unfold H.
apply is_omega_cocont_product_functor; try assumption.
- apply ProductsHSET2.
- apply has_exponentials_HSET2.
- apply has_homsets_HSET2.
- apply has_homsets_HSET2.
Qed.

(* Signature for the Id functor *)
Definition IdSignature : Signature HSET has_homsets_HSET.
Proof.
mkpair.
- apply Id.
- mkpair; simpl.
  + mkpair; simpl.
    * intro x.
      { mkpair.
        - intro y; simpl; apply idfun.
        - abstract (intros y y' f; apply idpath).
      }
    * abstract (intros y y' f; apply (nat_trans_eq has_homsets_HSET); intro z; apply idpath).
  + abstract (split;
               [ intros x; apply (nat_trans_eq has_homsets_HSET); intro z; apply idpath
               | intros x y z; apply (nat_trans_eq has_homsets_HSET); intro w; apply idpath]).
Defined.

Definition Arity_to_Signature : list nat -> Signature HSET has_homsets_HSET.
Proof.
intros xs.
generalize (map_list precomp_option_iter_Signature xs).
apply foldr1_list.
- apply (Product_of_Signatures _ _ ProductsHSET).
- apply IdSignature.
Defined.

Lemma is_omega_cocont_Arity_to_Signature (xs : list nat) : is_omega_cocont (Arity_to_Signature xs).
Proof.
destruct xs as [n xs].
destruct n.
- destruct xs; simpl; apply (is_omega_cocont_functor_identity _ has_homsets_HSET2).
- induction n.
+
destruct xs as [m xs].
destruct xs; simpl.
apply is_omega_cocont_precomp_option_iter.
+
unfold Arity_to_Signature.
simpl in *.
destruct xs as [m xs].
generalize (IHn xs).
destruct xs.
apply is_omega_cocont_Product_of_Signatures.
apply is_omega_cocont_precomp_option_iter.
Defined.

Definition SigToSignature : Sig -> Signature HSET has_homsets_HSET.
Proof.
use foldr_list.
- intros l F.
  apply (Sum_of_Signatures _ _ CoproductsHSET (Arity_to_Signature l) F).
- apply IdSignature.
Defined.

Lemma is_omega_cocont_Sum_of_Signatures (S1 S2 : Signature HSET has_homsets_HSET)
  (h1 : is_omega_cocont S1) (h2 : is_omega_cocont S2) :
  is_omega_cocont (Sum_of_Signatures _ _ CoproductsHSET S1 S2).
Proof.
destruct S1 as [F1 [F2 [F3 F4]]]; simpl in *.
destruct S2 as [G1 [G2 [G3 G4]]]; simpl in *.
unfold H.
apply is_omega_cocont_coproduct_functor; try assumption.
- apply ProductsHSET2.
- apply has_homsets_HSET2.
- apply has_homsets_HSET2.
Qed.

Lemma is_omega_cocont_SigToSignature (s : Sig) : is_omega_cocont (SigToSignature s).
Proof.
destruct s as [n xs].
induction n.
destruct xs.
simpl.
apply (is_omega_cocont_functor_identity _ has_homsets_HSET2).
simpl.
destruct xs.
apply is_omega_cocont_Sum_of_Signatures.
apply is_omega_cocont_Arity_to_Signature.
apply IHn.
Qed.

Definition SigInitial (sig : Sig) :
  Initial (FunctorAlg (Id_H HSET has_homsets_HSET CoproductsHSET (SigToSignature sig))
                            (functor_category_has_homsets HSET HSET has_homsets_HSET)).
Proof.
use colimAlgInitial.
- unfold Id_H, Const_plus_H.
  apply is_omega_cocont_coproduct_functor.
  + apply (Products_functor_precat _ _ ProductsHSET).
  + apply functor_category_has_homsets.
  + apply functor_category_has_homsets.
  + apply is_omega_cocont_constant_functor; apply functor_category_has_homsets.
  + apply is_omega_cocont_SigToSignature.
- apply (Initial_functor_precat _ _ InitialHSET).
- apply ColimsFunctorCategory; apply ColimsHSET.
Defined.

Definition SigInitialHSS (sig : Sig) : Initial (hss_precategory CoproductsHSET (SigToSignature sig)).
Proof.
apply InitialHSS.
- intro Z; apply RightKanExtension_from_limits, cats_LimsHSET.
- apply SigInitial.
Defined.

Definition SigToMonad (sig : Sig) : Monad HSET.
Proof.
use Monad_from_hss.
- apply has_homsets_HSET.
- apply CoproductsHSET.
- apply (SigToSignature sig).
- apply SigInitialHSS.
Defined.

End SigToMonad.


(* (* Test lambda calculus *) *)
(* Section test_lam. *)

(* Infix "::" := (cons_list nat). *)
(* Notation "[]" := (nil_list nat) (at level 0, format "[]"). *)

(* (* The signature of the lambda calculus: [[0,0],[1]] *) *)
(* Definition LamSig : Sig := cons_list (list nat) (0 :: 0 :: []) (cons_list (list nat) (1 :: []) (nil_list (list nat))). *)

(* Eval cbn in pr1 (SigToSignature LamSig). *)

(* Require Import UniMath.SubstitutionSystems.LamHSET. *)

(* Let Lam_S : Signature HSET has_homsets_HSET := *)
(*   Lam_Sig HSET has_homsets_HSET TerminalHSET CoproductsHSET ProductsHSET. *)

(* Check (pr1 Lam_S). *)
(* Goal (pr1 Lam_S = pr1 (SigToFunctor LamSig)). *)
(* simpl. *)
(* apply subtypeEquality. *)
(* intros x. *)
(* apply isaprop_is_functor. *)
(* apply (functor_category_has_homsets HSET HSET has_homsets_HSET). *)
(* simpl. *)
(* unfold App_H, square_functor. *)
(* unfold Abs_H. *)
(* apply maponpaths. *)
(* admit. *)
(* Abort. (* equal if we add Id *) *)

(* End test_lam. *)
