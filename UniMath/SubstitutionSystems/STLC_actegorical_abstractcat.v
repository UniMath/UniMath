(**

Syntax of the simply typed lambda calculus as a
multisorted signature.

Written by: Ralph Matthes, 2024 (adapted from STLC_actegorical.v)

 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Cochains.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_coind_actegorical.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.InstantiateHSET.
Require Import UniMath.SubstitutionSystems.MultiSortedEmbeddingIndCoindHSET.
Require UniMath.SubstitutionSystems.STLC_alt.


Local Open Scope cat.

Section A.

  Context (sort : hSet) (arr : sort → sort → sort).

  Local Lemma Hsort : isofhlevel 3 sort.
  Proof.
    exact (isofhlevelssnset 1 sort (setproperty sort)).
  Defined.

  Context (C : category) (BinProductsC : BinProducts C) (BinCoproductsC : BinCoproducts C)
                         (TerminalC : Terminal C) (CoproductsC : ∏ I : UU, isaset I → Coproducts I C).

  Let sortToC : category := [path_pregroupoid sort Hsort, C].

  Let BPsortToC : BinProducts sortToC := BinProducts_functor_precat _ _ BinProductsC.
  Let BCsortToC : BinCoproducts sortToC := BinCoproducts_functor_precat _ _ BinCoproductsC.
  Let terminal_sortToC : Terminal sortToC := Terminal_functor_precat _ _  TerminalC.

  Local Lemma BinProd : BinProducts [sortToC,C].
  Proof.
    apply BinProducts_functor_precat, BinProductsC.
  Defined.

(** Some notations *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.
Local Notation "s ⇒ t" := (arr s t).
Local Notation "'Id'" := (functor_identity _).
(*Local Notation "a ⊕ b" := (BinCoproductObject (BinCoprodSortToSet a b)). *)
(* Local Notation "'1'" := (TerminalObject TerminalSortToSet). *)
Local Notation "F ⊗ G" := (BinProduct_of_functors BinProd F G).

Let sortToC2 := [sortToC,sortToC].

Let terminal_sortToC2 : Terminal sortToC2 := Terminal_functor_precat sortToC sortToC terminal_sortToC.

Local Lemma BinProducts_sortToC2 : BinProducts sortToC2.
Proof.
  apply BinProducts_functor_precat, BPsortToC.
Defined.

Lemma postcomp_with_projSortToC_on_mor (F : sortToC2) (s: sort) (ξ ξ' : sortToC) (f : sortToC ⟦ ξ, ξ' ⟧)
(* (arg : global_element TerminalC (pr1 (functor_compose F (projSortToC sort Hsort C s)) ξ)) *)
  : # (pr1 (functor_compose F (projSortToC sort Hsort C s))) f  = pr1 (# (pr1 F) f) s.
Proof.
  apply idpath.
Qed.

(** The signature of the simply typed lambda calculus *)
Definition STLC_Sig : MultiSortedSig sort.
Proof.
use make_MultiSortedSig.
- apply ((sort × sort) + (sort × sort))%set.
- intros H; induction H as [st|st]; induction st as [s t].
  + exact ((([],,(s ⇒ t)) :: ([],,s) :: nil),,t).
  + exact (((cons s [],,t) :: []),,(s ⇒ t)).
Defined.

(** the canonical functor associated with STLC_Sig *)
Definition STLC_Functor_H : functor sortToC2 sortToC2 :=
  MultiSorted_actegorical.MultiSortedSigToFunctor' sort Hsort C
    TerminalC BinProductsC BinCoproductsC CoproductsC STLC_Sig.

(** the functor of which the fixed points are considered *)
Definition STLC_Functor_Id_H : functor sortToC2 sortToC2 :=
  SubstitutionSystems.Id_H sortToC BCsortToC STLC_Functor_H.

(** the canonical strength associated with STLC_Sig *)
Let θSTLC := MultiSortedMonadConstruction_actegorical.MultiSortedSigToStrength' sort Hsort C
               TerminalC BinProductsC BinCoproductsC CoproductsC STLC_Sig.

Definition ctx_ext (ξ : sortToC) (s : sort) : sortToC
  := pr1 (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC s) ξ.
(*  := pr1 (option_list sort Hsort C TerminalC BinCoproductsC CoproductsC (s :: [])) ξ. *)

(** the sigma-monoids for wellfounded and non-wellfounded syntax for STLC *)
Context (InitialC : Initial C) (ProductsC : ∏ I : UU, Products.Products I C)
  (expSortToC1 : exponentials.Exponentials BinProducts_sortToC2)
  (ColimsC_of_shape_nat_graph : Colimits.Colims_of_shape nat_graph C).

Let σind : SigmaMonoid θSTLC := pr1 (InitialSigmaMonoidOfMultiSortedSig_CAT sort Hsort C TerminalC InitialC BinProductsC BinCoproductsC ProductsC CoproductsC expSortToC1 ColimsC_of_shape_nat_graph STLC_Sig).

Context (LimsC_of_shape_conat_graph : Graphs.Limits.Lims_of_shape conat_graph C)
    (I_coproduct_distribute_over_omega_limits_C : ∏ I : SET,
          CommutingOfOmegaLimitsAndCoproducts.ω_limits_distribute_over_I_coproducts C I
            LimsC_of_shape_conat_graph (CoproductsC (pr1 I) (pr2 I)))
    (is_univalent_C : is_univalent C). (** univalence is there to shorten one argument in the construction of the following *)

Let σcoind : SigmaMonoid θSTLC := coindSigmaMonoidOfMultiSortedSig_CAT sort Hsort C TerminalC
         BinProductsC BinCoproductsC CoproductsC LimsC_of_shape_conat_graph
         I_coproduct_distribute_over_omega_limits_C STLC_Sig is_univalent_C.

Section IndAndCoind.

  Context (σ : SigmaMonoid θSTLC).

  (** the functor representing the syntax for STLC *)
  Definition STLC_gen : sortToC2 := SigmaMonoid_carrier θSTLC σ.

  (** the type of STLC terms in a context of a sort *)
  Definition STLC_gen_ctx_sort (ξ : sortToC) (s : sort) : C
    := pr1 (pr1 STLC_gen ξ) s.

  (** variable inclusion for syntax for STLC *)
  Definition STLC_eta_gen : sortToC2⟦Id,STLC_gen⟧ := SigmaMonoid_η θSTLC σ.

  Definition STLC_eta_gen_natural (ξ ξ' : sortToC) (f : sortToC ⟦ ξ, ξ' ⟧) :
    # Id f · pr1 STLC_eta_gen ξ' = pr1 STLC_eta_gen ξ · # (pr1 STLC_gen) f
    := nat_trans_ax (STLC_eta_gen) ξ ξ' f.

  Lemma STLC_eta_gen_natural' (ξ ξ' : sortToC) (f : sortToC ⟦ ξ, ξ' ⟧) :
    f · pr1 STLC_eta_gen ξ' = pr1 STLC_eta_gen ξ · # (pr1 STLC_gen) f.
  Proof.
    etrans.
    2: { apply STLC_eta_gen_natural. }
    apply idpath.
  Qed.

  Lemma STLC_eta_gen_natural'_pointwise (ξ ξ' : sortToC) (f : sortToC ⟦ ξ, ξ' ⟧) (u : sort) :
    pr1 f u · pr1 (pr1 STLC_eta_gen ξ') u = pr1 (pr1 STLC_eta_gen ξ) u · pr1 (# (pr1 STLC_gen) f) u.
  Proof.
    apply (nat_trans_eq_weq C _ _ (STLC_eta_gen_natural' ξ ξ' f)).
  Qed.


  (** the algebra maps (the "domain-specific constructors") for STLC *)
  Definition STLC_tau_gen : STLC_Functor_H STLC_gen --> STLC_gen  := SigmaMonoid_τ θSTLC σ.

  (** the individual sorted constructors for application and lambda-abstraction *)

  Definition app_source_gen_oldstyle_abstracted (s t : sort) : functor sortToC2 sortToC2 :=
    (post_comp_functor (projSortToC sort Hsort C (s ⇒ t)) ⊗ post_comp_functor (projSortToC sort Hsort C s))
      ∙ (post_comp_functor (hat_functor sort Hsort C CoproductsC t)).

  Definition app_source_gen_newstyle (s t : sort) : sortToC2 :=
    BinProduct_of_functors BPsortToC
      (functor_compose STLC_gen
         (projSortToC sort Hsort C (s ⇒ t) ∙ hat_functor sort Hsort C CoproductsC t))
      (functor_compose STLC_gen
         (projSortToC sort Hsort C s ∙ hat_functor sort Hsort C CoproductsC t)).

  Definition app_source_gen (s t : sort) : sortToC2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort C TerminalC
      BinProductsC BinCoproductsC CoproductsC (arity sort STLC_Sig (inl (s,, t))) STLC_gen.

  Lemma app_source_gen_ok (s t : sort) : app_source_gen s t  = app_source_gen_newstyle s t.
  Proof.
    apply idpath.
  Qed.

  Definition app_source_gen_mor_eq_statement (s t : sort) {ξ ξ' : sortToC} (f : sortToC ⟦ ξ, ξ' ⟧)
    (u : sort) : UU.
  Proof.
    refine (pr1 (# (pr1 (app_source_gen s t)) f) u =  BinProductOfArrows C (BinProductsC _ _) (BinProductsC _ _)  _ _).
    - exact (pr1 (# (pr1 (functor_compose STLC_gen
                            (projSortToC sort Hsort C (s ⇒ t) ∙ hat_functor sort Hsort C CoproductsC t))) f) u).
    - exact (pr1 (# (pr1 (functor_compose STLC_gen
                            (projSortToC sort Hsort C s ∙ hat_functor sort Hsort C CoproductsC t))) f) u).
  Defined.

  Lemma app_source_gen_mor_eq (s t : sort) {ξ ξ' : sortToC} (f : sortToC ⟦ ξ, ξ' ⟧) (u : sort)
    : app_source_gen_mor_eq_statement s t f u.
  Proof.
    apply idpath.
  Qed.

  (** The application constructor *)
  Definition app_map_gen (s t : sort) : sortToC2⟦app_source_gen s t,STLC_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (ii1 (s,,t)) · STLC_tau_gen.

  Definition app_map_gen_natural (s t : sort) (ξ ξ' : sortToC) (f : sortToC ⟦ ξ, ξ' ⟧)
    : # (pr1 (app_source_gen s t)) f · pr1 (app_map_gen s t) ξ' = pr1 (app_map_gen s t) ξ · # (pr1 STLC_gen) f
    := nat_trans_ax (app_map_gen s t) ξ ξ' f.

  Lemma app_map_gen_natural_pointwise (s t : sort) (ξ ξ' : sortToC) (f : sortToC ⟦ ξ, ξ' ⟧) (u : sort)
    : pr1 (# (pr1 (app_source_gen s t)) f) u · pr1 (pr1 (app_map_gen s t) ξ') u =
        pr1 (pr1 (app_map_gen s t) ξ) u · pr1 (# (pr1 STLC_gen) f) u.
  Proof.
    apply (nat_trans_eq_weq C _ _ (app_map_gen_natural s t ξ ξ' f)).
  Qed.


  Definition lam_source_gen_oldstyle_abstracted (s t : sort) : functor sortToC2 sortToC2 :=
    pre_comp_functor (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC s)
      ∙ post_comp_functor (projSortToC sort Hsort C t)
      ∙ post_comp_functor (hat_functor sort Hsort C CoproductsC (s ⇒ t)).

  Definition lam_source_gen_newstyle (s t : sort) : sortToC2 :=
    functor_compose
      (functor_compose
         (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC s)
         STLC_gen)
      (projSortToC sort Hsort C t ∙ hat_functor sort Hsort C CoproductsC (s ⇒ t)).

  Definition lam_source_gen (s t : sort) : sortToC2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort C TerminalC
      BinProductsC BinCoproductsC CoproductsC (arity sort STLC_Sig (inr (s,, t))) STLC_gen.

  Lemma lam_source_gen_ok (s t : sort) : lam_source_gen s t  = lam_source_gen_newstyle s t.
  Proof.
    apply idpath.
  Qed.

  Lemma lam_source_gen_mor_eq (s t : sort) {ξ ξ' : sortToC} (f : sortToC ⟦ ξ, ξ' ⟧) (u : sort)
    : pr1 (# (pr1 (lam_source_gen s t)) f) u =
        pr1 (# (pr1 (functor_compose
      (functor_compose
         (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC s)
         STLC_gen)
      (projSortToC sort Hsort C t ∙ hat_functor sort Hsort C CoproductsC (s ⇒ t)))) f) u.
  Proof.
    apply idpath.
  Qed.

  (** The lambda-abstraction constructor *)
  Definition lam_map_gen (s t : sort) : sortToC2⟦lam_source_gen s t,STLC_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (ii2 (s,,t)) · STLC_tau_gen.

  Definition lam_map_gen_natural (s t : sort) (ξ ξ' : sortToC) (f : sortToC ⟦ ξ, ξ' ⟧)
    : # (pr1 (lam_source_gen s t)) f · pr1 (lam_map_gen s t) ξ' = pr1 (lam_map_gen s t) ξ · # (pr1 STLC_gen) f
    := nat_trans_ax (lam_map_gen s t) ξ ξ' f.

  Lemma lam_map_gen_natural_pointwise (s t : sort) (ξ ξ' : sortToC) (f : sortToC ⟦ ξ, ξ' ⟧) (u : sort)
    : pr1 (# (pr1 (lam_source_gen s t)) f) u · pr1 (pr1 (lam_map_gen s t) ξ') u =
        pr1 (pr1 (lam_map_gen s t) ξ) u · pr1 (# (pr1 STLC_gen) f) u.
  Proof.
    apply (nat_trans_eq_weq C _ _ (lam_map_gen_natural s t ξ ξ' f)).
  Qed.

  Section Church.

    (** fix a sort, viewed as an atom *)
    Context (s : sort).

    Definition ChurchZero_gen (ξ : sortToC) : global_element TerminalC (STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s))).
    Proof.
      (** abstract a first variable - forced to be of type [s ⇒ s] *)
      refine (_ · pr1 (pr1 (lam_map_gen _ _) _) _).
      refine (_ · CoproductIn _ _ _ (idpath _)).
      change (global_element TerminalC (STLC_gen_ctx_sort (ctx_ext ξ (s ⇒ s)) (s ⇒ s))).
      (** abstract a second variable - forced to be of type [s] *)
      refine (_ · pr1 (pr1 (lam_map_gen _ _) _) _).
      refine (_ · CoproductIn _ _ _ (idpath _)).
      change (global_element TerminalC (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s)).
      (** take a variable *)
      simple refine (_ · pr1 (pr1 STLC_eta_gen _) _).
      (* unfold functor_identity, functor_identity_data, functor_data_constr, functor_data_from_functor, functor_on_objects, pr1. *)
      (** the available variables are seen, pick the last added variable of type [s] *)
      refine (_ · BinCoproductIn1 _).
      cbn.
      exact (CoproductIn _ _ _ (idpath _)).
    Defined.

    Definition ChurchOne_gen (ξ : sortToC) : global_element TerminalC (STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s))).
    Proof.
      refine (_ · pr1 (pr1 (lam_map_gen _ _) _) _).
      refine (_ · CoproductIn _ _ _ (idpath _)).
      refine (_ · pr1 (pr1 (lam_map_gen _ _) _) _).
      refine (_ · CoproductIn _ _ _ (idpath _)).
      refine (_ · pr1 (pr1 (app_map_gen s _) _) _).
      (** do an application with argument type [s] - not giving this argument would potentially slow down the further steps *)
      apply BinProductArrow; refine (_ · CoproductIn _ _ _ (idpath _)).
      - change (global_element TerminalC (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) (s ⇒ s))).
        simple refine (_ · pr1 (pr1 STLC_eta_gen _) _).
        (** the available variables are seen, pick the first added variable of type [s ⇒ s] *)
        refine (_ · BinCoproductIn2 _).
        refine (_ · BinCoproductIn1 _).
        cbn.
        exact (CoproductIn _ _ _ (idpath _)).
      - change (global_element TerminalC (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s)).
        simple refine (_ · pr1 (pr1 STLC_eta_gen _) _).
        (** pick the last added variable of type [s] *)
        refine (_ · BinCoproductIn1 _).
        cbn.
        exact (CoproductIn _ _ _ (idpath _)).
    Defined.


    Definition Church_gen_body (n : nat) (ξ : sortToC) : global_element TerminalC (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
    Proof.
      induction n.
      - simple refine (_ · pr1 (pr1 STLC_eta_gen _) _).
        refine (_ · BinCoproductIn1 _).
        cbn.
        exact (CoproductIn _ _ _ (idpath _)).
      - refine (_ · pr1 (pr1 (app_map_gen s _) _) _).
        apply BinProductArrow; refine (_ · CoproductIn _ _ _ (idpath _)).
        + change (global_element TerminalC (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) (s ⇒ s))).
          simple refine (_ · pr1 (pr1 STLC_eta_gen _) _).
          refine (_ · BinCoproductIn2 _).
          refine (_ · BinCoproductIn1 _).
          cbn.
          exact (CoproductIn _ _ _ (idpath _)).
        + exact IHn.
    Defined.


    Lemma Church_gen_body_zero (ξ : sortToC) :
      Church_gen_body 0 ξ =
        (CoproductIn _ _ _ (idpath _) · BinCoproductIn1 _)
          · pr1 (pr1 STLC_eta_gen (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) _.
    Proof.
      apply idpath.
    Qed.


    Arguments BinProductArrow {_ _ _} _ {_}.
    Arguments BinProductsC {_ _}.
    Arguments CoproductIn {_ _ _ _}.
    Arguments BinCoproductIn1 {_ _ _ _}.
    Arguments BinCoproductIn2 {_ _ _ _}.

    (** by careful inspection of the generated term, one can obtain the following recursive equation *)
    Lemma Church_gen_body_rec_eq (n : nat) (ξ : sortToC) :
      Church_gen_body (S n) ξ =
        BinProductArrow BinProductsC
          ((((CoproductIn (idpath _) · BinCoproductIn1) · BinCoproductIn2)
              · pr1 (pr1 STLC_eta_gen (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) _)
             · CoproductIn (idpath _))
          (Church_gen_body n ξ · CoproductIn (idpath _))
          · pr1 (pr1 (app_map_gen s _) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s.
    Proof.
      apply idpath.
    Qed.

    Definition Church_gen_header (ξ : sortToC) :
      STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s
        --> STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s)).
    Proof.
      refine (_ · pr1 (pr1 (lam_map_gen _ _) _) _).
      refine (_ · CoproductIn (idpath _)).
      refine (_ · pr1 (pr1 (lam_map_gen _ _) _) _).
      exact (CoproductIn (idpath _)).
    Defined.

    Definition Church_gen (n : nat) (ξ : sortToC)
      : global_element TerminalC (STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s)))
      := (Church_gen_body n ξ) · Church_gen_header ξ.

  End Church.

  Section Church_functor.

    Arguments BinProductArrow {_ _ _} _ {_}.
    Arguments BinProductsC {_ _}.
    Arguments CoproductIn {_ _ _ _}.
    Arguments BinCoproductIn1 {_ _ _ _}.
    Arguments BinCoproductIn2 {_ _ _ _}.

    Definition Church_gen_body_target_data: functor_data sortToC sortToC.
    Proof.
      use make_functor_data.
      - intro ξ.
        apply (functor_path_pregroupoid Hsort).
        intro s.
        exact (pr1 (pr1 STLC_gen (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s).
        (** this is the pointwise formula - with context and sort argument *)
      - intros ξ ξ' f.
        apply nat_trans_functor_path_pregroupoid.
        intro s.
        simpl.
        exact (pr1 (# (pr1 STLC_gen)
                      (# (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC s)
                         (# (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC (s ⇒ s)) f))) s).
    Defined.

    Lemma Church_gen_body_target_data_ok : is_functor Church_gen_body_target_data.
    Proof.
      split; red.
      - intro ξ.
        apply nat_trans_eq; try apply C.
        intro s.
        unfold Church_gen_body_target_data.
        Opaque STLC_gen sorted_option_functor.
        simpl.
        rewrite (functor_id (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC (s ⇒ s))).
        rewrite (functor_id (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC s)).
        rewrite (functor_id STLC_gen).
        apply idpath.
      - intros ξ1 ξ2 ξ3 f g.
        apply nat_trans_eq; try apply C.
        intro s.
        unfold Church_gen_body_target_data.
        Opaque STLC_gen sorted_option_functor.
        simpl.
        rewrite (functor_comp (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC (s ⇒ s))).
        rewrite (functor_comp (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC s)).
        rewrite (functor_comp STLC_gen).
        apply idpath.
    Qed.

    Transparent STLC_gen sorted_option_functor.

    Definition Church_gen_body_target : sortToC2 := _,, Church_gen_body_target_data_ok.

    Definition Church_gen_body_sortToC_data (n : nat) (ξ : sortToC) : global_element terminal_sortToC (pr1 Church_gen_body_target ξ).
    Proof.
      use nat_trans_functor_path_pregroupoid.
      intro s.
      exact (Church_gen_body s n ξ).
    Defined.

    Lemma Church_gen_body_sortToC_data_ok (n : nat) (ξ ξ' : sortToC) (f : sortToC ⟦ ξ, ξ' ⟧) :
      Church_gen_body_sortToC_data n ξ · # (pr1 Church_gen_body_target) f = Church_gen_body_sortToC_data n ξ'.
    Proof.
      induction n.
      - apply nat_trans_eq; try apply C.
        intros s.
        unfold Church_gen_body_sortToC_data.
        Opaque Church_gen_body Church_gen_body_target.
        simpl.
        etrans.
        2: { rewrite Church_gen_body_zero.
             rewrite assoc'.
             apply maponpaths.
             apply pathsinv0.
             assert (aux := STLC_eta_gen_natural'_pointwise _ _
                                 (# (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC s)
                                    (# (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC (s ⇒ s)) f))
                                 s).
             apply (maponpaths (fun x => BinCoproductIn1 · x)) in aux.
             rewrite assoc in aux.
             match goal with |[  H : ?auxleft = _ |- _ ] => set (theauxleft := auxleft) end.
             intermediate_path theauxleft.
             + unfold theauxleft.
               apply cancel_postcomposition.
               unfold sorted_option_functor.
               unfold constcoprod_functor1.
               etrans.
               2: { apply pathsinv0.
                    unfold compose.
                    unfold functor_on_morphisms, make_functor_data.
                    unfold nat_trans_functor_path_pregroupoid, make_nat_trans, nat_trans_data_from_nat_trans_funclass.
                    apply BinCoproductIn1Commutes. }
               apply pathsinv0, id_left.
             + exact aux.
        }
        repeat rewrite assoc.
        apply idpath.
      - apply nat_trans_eq; try apply C.
        intros s.
        change (Church_gen_body s (S n) ξ · pr1 (# (pr1 Church_gen_body_target) f) s = Church_gen_body s (S n) ξ').
        do 2 rewrite Church_gen_body_rec_eq.
        assert (IHnpointwise : Church_gen_body s n ξ · pr1 (# (pr1 Church_gen_body_target) f) s = Church_gen_body s n ξ')
        by apply (toforallpaths _ _ _ (maponpaths pr1 IHn) s).
        rewrite <- IHnpointwise.
        clear IHnpointwise.
        Transparent Church_gen_body_target.
        unfold Church_gen_body_target.
        unfold pr1.
        unfold Church_gen_body_target_data.
        unfold make_functor_data.
        unfold functor_on_morphisms at 7.
        unfold pr2.
        unfold nat_trans_functor_path_pregroupoid.
        unfold make_nat_trans.
        apply pathsinv0.
        unfold functor_on_morphisms at 13.
        unfold pr2.
        apply pathsinv0.
        etrans.
        { rewrite assoc'.
          apply maponpaths, pathsinv0, app_map_gen_natural_pointwise. }
        rewrite assoc.
        apply cancel_postcomposition.
        etrans.
        { etrans.
          { apply maponpaths. apply app_source_gen_mor_eq. }
          apply postcompWithBinProductArrow.
        }
        apply maponpaths_12.
        + assert (aux := STLC_eta_gen_natural'_pointwise _ _
                                 (# (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC s)
                                    (# (sorted_option_functor sort Hsort C TerminalC BinCoproductsC CoproductsC (s ⇒ s)) f))
                                 (s ⇒ s)).
          apply (maponpaths (fun x => BinCoproductIn1 · BinCoproductIn2 · x)) in aux.
          rewrite assoc in aux.
          etrans.
          2: { apply cancel_postcomposition.
               do 2 rewrite assoc'.
               apply maponpaths.
               rewrite assoc.
               apply pathsinv0.
               match goal with |[  H : ?auxleft = _ |- _ ] => set (theauxleft := auxleft) end.
               intermediate_path theauxleft.
               * unfold theauxleft.
                 apply cancel_postcomposition.
                 rewrite assoc'.
                 etrans.
                 2: { apply maponpaths.
                      unfold sorted_option_functor.
                      unfold constcoprod_functor1.
                      apply pathsinv0.
                      unfold compose.
                      unfold functor_on_morphisms, make_functor_data.
                      unfold nat_trans_functor_path_pregroupoid, make_nat_trans, nat_trans_data_from_nat_trans_funclass.
                      apply BinCoproductIn2Commutes. }
                 simpl.
                 apply pathsinv0.
                 rewrite assoc.
                 apply cancel_postcomposition.
                 etrans.
                 { apply BinCoproductIn1Commutes. }
                 rewrite (id_left(C:=sortToC)).
                 apply idpath.
               * exact aux.
          }
          repeat rewrite assoc'.
          do 4 apply maponpaths.
          simple refine (CoproductOfArrowsIn (s=s) _ _ _ _ _).
        + repeat rewrite assoc'.
          apply maponpaths.
          simple refine (CoproductOfArrowsIn (s=s) _ _ _ _ _).
    Qed.

    Transparent Church_gen_body Church_gen_body_target.

    Definition Church_gen_body_sortToC (n : nat) : global_element terminal_sortToC2 Church_gen_body_target.
    Proof.
      use make_global_element_functor_precat.
      - exact (Church_gen_body_sortToC_data n).
      - exact (Church_gen_body_sortToC_data_ok n).
    Defined.

    Definition Church_gen_header_sortToC_data : nat_trans_data (pr1 Church_gen_body_target)
            (pr1 (functor_compose STLC_gen (projSortToCvariable sort Hsort C (λ s : sort, (s ⇒ s) ⇒ s ⇒ s)))).
    Proof.
      intro ξ.
      use nat_trans_functor_path_pregroupoid.
      intros s.
      exact (Church_gen_header s ξ).
    Defined.

    Lemma Church_gen_header_sortToC_data_ok : is_nat_trans _ _ Church_gen_header_sortToC_data.
      intros ξ ξ' f.
      apply nat_trans_eq; try apply C.
      intros s.
      change (pr1 (# (pr1 Church_gen_body_target) f) s · Church_gen_header s ξ' =
                Church_gen_header s ξ  · pr1 (# (pr1 STLC_gen) f) ((s ⇒ s) ⇒ s ⇒ s)).
      unfold Church_gen_header.
      etrans.
      2: { repeat rewrite assoc'.
           do 3 apply maponpaths.
           apply lam_map_gen_natural_pointwise. }
      repeat rewrite assoc.
      apply cancel_postcomposition.
      etrans.
      2: { repeat rewrite assoc'.
           do 2 apply maponpaths.
           apply pathsinv0.
           rewrite lam_source_gen_mor_eq.
           simple refine (CoproductOfArrowsIn (((s ⇒ s) ⇒ s ⇒ s) = ((s ⇒ s) ⇒ s ⇒ s)) _ _ _ _ _). }
      etrans.
      2: { apply maponpaths.
           rewrite assoc.
           apply cancel_postcomposition.
           apply lam_map_gen_natural_pointwise. }
      repeat rewrite assoc.
      do 2 apply cancel_postcomposition.
      rewrite lam_source_gen_mor_eq.
      etrans.
      2: { apply pathsinv0.
           simple refine (CoproductOfArrowsIn ((s ⇒ s) = (s ⇒ s)) _ _ _ _ _). }
      apply idpath.
    Qed.

    Definition Church_gen_header_sortToC : sortToC2⟦Church_gen_body_target,
         functor_compose STLC_gen (projSortToCvariable sort Hsort C (fun s => (s ⇒ s) ⇒ (s ⇒ s)))⟧
      := _,, Church_gen_header_sortToC_data_ok.

     Definition Church_gen_sortToC (n : nat) : global_element terminal_sortToC2
           (functor_compose STLC_gen (projSortToCvariable sort Hsort C (fun s => (s ⇒ s) ⇒ (s ⇒ s))))
      := Church_gen_body_sortToC n · Church_gen_header_sortToC.


  End Church_functor.

End IndAndCoind.

Definition STLC_ctx_sort_ind (ξ : sortToC) (s : sort) : C
  := STLC_gen_ctx_sort σind ξ s.
Definition STLC_ctx_sort_coind (ξ : sortToC) (s : sort) : C
  := STLC_gen_ctx_sort σcoind ξ s.

Definition STLC_ind : sortToC2 := STLC_gen σind.
Definition STLC_coind : sortToC2 := STLC_gen σcoind.

Definition STLC_eta_ind : sortToC2⟦Id,STLC_ind⟧ := STLC_eta_gen σind.
Definition STLC_eta_coind : sortToC2⟦Id,STLC_coind⟧ := STLC_eta_gen σcoind.

Definition STLC_tau_ind : STLC_Functor_H STLC_ind --> STLC_ind  := SigmaMonoid_τ θSTLC σind.
Definition STLC_tau_coind : STLC_Functor_H STLC_coind --> STLC_coind  := SigmaMonoid_τ θSTLC σcoind.

Definition app_source_ind (s t : sort) : sortToC2 := app_source_gen σind s t.
Definition app_map_ind (s t : sort) : sortToC2⟦app_source_ind s t,STLC_ind⟧ := app_map_gen σind s t.
Definition lam_source_ind (s t : sort) : sortToC2 := lam_source_gen σind s t.
Definition lam_map_ind (s t : sort) : sortToC2⟦lam_source_ind s t,STLC_ind⟧ := lam_map_gen σind s t.

Definition app_source_coind (s t : sort) : sortToC2 := app_source_gen σcoind s t.
Definition app_map_coind (s t : sort) : sortToC2⟦app_source_coind s t,STLC_coind⟧ := app_map_gen σcoind s t.
Definition lam_source_coind (s t : sort) : sortToC2 := lam_source_gen σcoind s t.
Definition lam_map_coind (s t : sort) : sortToC2⟦lam_source_coind s t,STLC_coind⟧ := lam_map_gen σcoind s t.


(** get a handle on the recursion principles *)

(** the initial algebra *)
Definition STLC_ind_IA : Initial (FunctorAlg STLC_Functor_Id_H)
  := DatatypeOfMultisortedBindingSig_CAT sort Hsort C TerminalC InitialC BinProductsC
       BinCoproductsC ProductsC CoproductsC expSortToC1
       ColimsC_of_shape_nat_graph STLC_Sig.
(** notice that this is only the initial algebra and not the initial sigma monoid *)

(** the final coalgebra *)
Definition STLC_coind_FC : Terminal (CoAlg_category STLC_Functor_Id_H)
  := coindCodatatypeOfMultisortedBindingSig_CAT sort Hsort C TerminalC
         BinProductsC BinCoproductsC CoproductsC LimsC_of_shape_conat_graph
         I_coproduct_distribute_over_omega_limits_C STLC_Sig is_univalent_C.

Section Church.

  (** fix a sort, viewed as an atom *)
  Context (s : sort).

  Definition ChurchInfinity (ξ : sortToC) : global_element TerminalC (STLC_ctx_sort_coind ξ ((s ⇒ s) ⇒ (s ⇒ s))).
  Proof.
    refine (_ · pr1 (pr1 (lam_map_coind _ _) _) _).
    refine (_ · CoproductIn _ _ _ (idpath _)).
    refine (_ · pr1 (pr1 (lam_map_coind _ _) _) _).
    refine (_ · CoproductIn _ _ _ (idpath _)).
    change (global_element TerminalC (STLC_ctx_sort_coind (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s)).
    (* TODO: coinduction has to come into play *)
    Abort.

End Church.

End A.
