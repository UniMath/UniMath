(**

Syntax of the simply-typed lambda calculus as a multisorted signature based on the actegorical development.
Thanks to that development, the inductive and the coinductive calculus are exposed in parallel.
The Church numerals are developed independently from the choice for inductive or coinductive syntax.
The entire development is only done for the base category [HSET] and thus profits from having inhabitants of the objects
and having functions as morphisms.

There is a sketch of how the Church numeral for infinity in the coinductive calculus could be obtained.

A point-free development for an abstract base category in place of [HSET] is found in STLC_actegorical_abstractcat.v.
That file includes a completed construction of Church numeral infinity.

Written by: Ralph Matthes, 2024 (reusing beginnings from STLC_alt.v)

 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
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
Require UniMath.SubstitutionSystems.SortIndexing.
Require Import UniMath.SubstitutionSystems.MultiSortedBindingSig.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_actegorical.
Require UniMath.SubstitutionSystems.MultiSortedMonadConstruction_alt.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_coind_actegorical.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.InstantiateHSET.
Require Import UniMath.SubstitutionSystems.MultiSortedEmbeddingIndCoindHSET.
Require UniMath.SubstitutionSystems.STLC_alt.


Local Open Scope cat.

Section A.

Context (sort : hSet) (arr : sort → sort → sort).

Local Definition Hsort : isofhlevel 3 sort := MultiSortedBindingSig.STLC_Hsort sort.

Let sortToSet : category := SortIndexing.sortToSet sort Hsort.
Let sortToSetSet : category := SortIndexing.sortToSetSet sort Hsort.
Let sortToSet2 : category := SortIndexing.sortToSet2 sort Hsort.

Let projSortToSet : sort -> sortToSetSet := MultiSortedMonadConstruction_alt.projSortToSet sort Hsort.
Let projSortToSetvariable : (sort → sort) → sortToSet2 := projSortToCvariable sort Hsort HSET.
Let hat_functorSet : sort -> HSET ⟶ sortToSet := MultiSortedMonadConstruction_alt.hat_functorSet sort Hsort.
Let sorted_option_functorSet : sort → functor sortToSet sortToSet := MultiSortedMonadConstruction_alt.sorted_option_functorSet sort Hsort.

Local Definition BCsortToSet : BinCoproducts sortToSet := SortIndexing.BCsortToSet sort Hsort.
Local Definition BPsortToSet : BinProducts sortToSet := SortIndexing.BPsortToSet sort Hsort.

Local Definition TsortToSet : Terminal sortToSet := SortIndexing.TsortToSet sort Hsort.
Local Definition TsortToSet2 : Terminal sortToSet2 := SortIndexing.TsortToSet2 sort Hsort.

Local Definition BPsortToSetSet : BinProducts sortToSetSet := SortIndexing.BPsortToSetSet sort Hsort.


(** Some notations *)
(* Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set. *)
Local Notation "s ⇒ t" := (arr s t).
Local Notation "'Id'" := (functor_identity _).
(*Local Notation "a ⊕ b" := (BinCoproductObject (BinCoprodSortToSet a b)). *)
(* Local Notation "'1'" := (TerminalObject TerminalSortToSet). *)
Local Notation "F ⊗ G" := (BinProduct_of_functors BPsortToSetSet F G).

Local Lemma sortToSet2_comp_on_mor (F G : sortToSet2) {ξ ξ' : sortToSet} (f : sortToSet⟦ ξ, ξ' ⟧) (s : sort) (* (elem : pr1 (pr1 (pr1 (functor_compose F G) ξ) s)) *) :
  pr1 (# (pr1 (functor_compose F G)) f) s = pr1 (# (pr1 G) (# (pr1 F) f)) s.
Proof.
  apply idpath.
Qed.

Lemma postcomp_with_projSortToSet_on_mor (F : sortToSet2) (s: sort) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
  (arg : pr1 (pr1 (functor_compose F (projSortToSet s)) ξ))
  : # (pr1 (functor_compose F (projSortToSet s))) f arg = pr1 (# (pr1 F) f) s arg.
Proof.
  apply idpath.
Qed.

Local Definition STLC_Sig : MultiSortedSig sort := STLC_Sig sort arr.

(** the canonical functor associated with STLC_Sig *)
Definition STLC_Functor_H : functor sortToSet2 sortToSet2 :=
  MultiSorted_actegorical.MultiSortedSigToFunctor' sort Hsort SET
    TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET STLC_Sig.

(** the functor of which the fixed points are considered *)
Definition STLC_Functor_Id_H : functor sortToSet2 sortToSet2 :=
  SubstitutionSystems.Id_H sortToSet BCsortToSet STLC_Functor_H.

(** the canonical strength associated with STLC_Sig *)
Let θSTLC := MultiSortedMonadConstruction_actegorical.MultiSortedSigToStrength' sort Hsort SET
               TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET STLC_Sig.

Definition ctx_ext (ξ : sortToSet) (s : sort) : sortToSet
  := sorted_option_functorSet s ξ.
(*  := pr1 (option_list sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET (s :: [])) ξ. *)

(** the sigma-monoids for wellfounded and non-wellfounded syntax for STLC *)
Let σind : SigmaMonoid θSTLC := MultiSortedEmbeddingIndCoindHSET.σind sort Hsort STLC_Sig.
Let σcoind : SigmaMonoid θSTLC := MultiSortedEmbeddingIndCoindHSET.σcoind sort Hsort STLC_Sig.

Section IndAndCoind.

  Context (σ : SigmaMonoid θSTLC).

  (** the functor representing the syntax for STLC *)
  Definition STLC_gen : sortToSet2 := SigmaMonoid_carrier θSTLC σ.

  (** the type of STLC terms in a context of a sort *)
  Definition STLC_gen_ctx_sort (ξ : sortToSet) (s : sort) : UU
    := pr1 (pr1 (pr1 STLC_gen ξ) s).

  (** variable inclusion for syntax for STLC *)
  Definition STLC_eta_gen : sortToSet2⟦Id,STLC_gen⟧ := SigmaMonoid_η θSTLC σ.

  Definition STLC_eta_gen_natural (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) :
    # Id f · pr1 STLC_eta_gen ξ' = pr1 STLC_eta_gen ξ · # (pr1 STLC_gen) f
    := nat_trans_ax (STLC_eta_gen) ξ ξ' f.

  Lemma STLC_eta_gen_natural' (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) :
    f · pr1 STLC_eta_gen ξ' = pr1 STLC_eta_gen ξ · # (pr1 STLC_gen) f.
  Proof.
    etrans.
    2: { apply STLC_eta_gen_natural. }
    apply idpath.
  Qed.

  Lemma STLC_eta_gen_natural'_pointwise (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort) :
    pr1 f u · pr1 (pr1 STLC_eta_gen ξ') u = pr1 (pr1 STLC_eta_gen ξ) u · pr1 (# (pr1 STLC_gen) f) u.
  Proof.
    apply (nat_trans_eq_weq HSET _ _ (STLC_eta_gen_natural' ξ ξ' f)).
  Qed.

  Lemma STLC_eta_gen_natural'_ppointwise (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort) (elem : pr1 (pr1 (pr1 ξ) u)) :
    pr1 (pr1 STLC_eta_gen ξ') u (pr1 f u elem) =  pr1 (# (pr1 STLC_gen) f) u (pr1 (pr1 STLC_eta_gen ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ (STLC_eta_gen_natural'_pointwise ξ ξ' f u)).
  Qed.

  (** the algebra maps (the "domain-specific constructors") for STLC *)
  Definition STLC_tau_gen : STLC_Functor_H STLC_gen --> STLC_gen  := SigmaMonoid_τ θSTLC σ.

  (** the individual sorted constructors for application and lambda-abstraction *)

  Definition app_source_gen_oldstyle_abstracted (s t : sort) : functor sortToSet2 sortToSet2 :=
    (post_comp_functor (projSortToSet (s ⇒ t)) ⊗ post_comp_functor (projSortToSet s))
      ∙ (post_comp_functor (hat_functorSet t)).

  (** this old-style definition coincides with [STLC_alt.v] *)
  Lemma app_source_gen_oldstyle_abstracted_ok (s t : sort) :
    app_source_gen_oldstyle_abstracted s t = SubstitutionSystems.STLC_alt.app_source sort arr s t.
  Proof.
    apply idpath.
  Qed.

  Definition app_source_gen_newstyle (s t : sort) : sortToSet2 :=
    BinProduct_of_functors BPsortToSet
      (functor_compose STLC_gen (projSortToSet (s ⇒ t) ∙ hat_functorSet t))
      (functor_compose STLC_gen (projSortToSet s ∙ hat_functorSet t)).

  Definition app_source_gen (s t : sort) : sortToSet2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET
      BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort STLC_Sig (inl (s,, t))) STLC_gen.

  Lemma app_source_gen_ok (s t : sort) : app_source_gen s t  = app_source_gen_newstyle s t.
  Proof.
    apply idpath.
  Qed.

  Lemma app_source_gen_mor_pr1 (s t : sort) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    (u : sort) (arg : pr1 (pr1 (pr1 (app_source_gen s t) ξ) u)) :
    pr1 (pr1 (# (pr1 (app_source_gen s t)) f) u arg) =
      pr1 (# (pr1 (functor_compose STLC_gen (projSortToSet (s ⇒ t) ∙ hat_functorSet t))) f) u (pr1 arg).
  Proof.
    apply idpath.
  Qed.

  Lemma app_source_gen_mor_pr2 (s t : sort) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    (u : sort) (arg : pr1 (pr1 (pr1 (app_source_gen s t) ξ) u)) :
    pr2 (pr1 (# (pr1 (app_source_gen s t)) f) u arg) =
      pr1 (# (pr1 (functor_compose STLC_gen (projSortToSet s ∙ hat_functorSet t))) f) u (pr2 arg).
  Proof.
    apply idpath.
  Qed.

  (** The application constructor *)
  Definition app_map_gen (s t : sort) : sortToSet2⟦app_source_gen s t,STLC_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (ii1 (s,,t)) · STLC_tau_gen.

  Definition app_map_gen_natural (s t : sort) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    : # (pr1 (app_source_gen s t)) f · pr1 (app_map_gen s t) ξ' = pr1 (app_map_gen s t) ξ · # (pr1 STLC_gen) f
    := nat_trans_ax (app_map_gen s t) ξ ξ' f.

  Lemma app_map_gen_natural_pointwise (s t : sort) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort)
    : pr1 (# (pr1 (app_source_gen s t)) f) u · pr1 (pr1 (app_map_gen s t) ξ') u =
        pr1 (pr1 (app_map_gen s t) ξ) u · pr1 (# (pr1 STLC_gen) f) u.
  Proof.
    apply (nat_trans_eq_weq HSET _ _ (app_map_gen_natural s t ξ ξ' f)).
  Qed.

  Lemma app_map_gen_natural_ppointwise (s t : sort) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    (u : sort) (elem : pr1 (pr1 (pr1 (app_source_gen s t) ξ) u)) :
    pr1 (pr1 (app_map_gen s t) ξ') u (pr1 (# (pr1 (app_source_gen s t)) f) u elem) =
      pr1 (# (pr1 STLC_gen) f) u (pr1 (pr1 (app_map_gen s t) ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ (app_map_gen_natural_pointwise s t ξ ξ' f u)).
  Qed.


  Definition lam_source_gen_oldstyle_abstracted (s t : sort) : functor sortToSet2 sortToSet2 :=
    pre_comp_functor (sorted_option_functorSet s)
      ∙ post_comp_functor (projSortToSet t) ∙ post_comp_functor (hat_functorSet (s ⇒ t)).

  (** this old-style definition coincides with [STLC_alt.v] *)
  Lemma lam_source_gen_oldstyle_abstracted_ok (s t : sort) :
    lam_source_gen_oldstyle_abstracted s t = SubstitutionSystems.STLC_alt.lam_source sort arr s t.
  Proof.
    apply idpath.
  Qed.

  Definition lam_source_gen_newstyle (s t : sort) : sortToSet2 :=
    functor_compose
      (functor_compose
         (sorted_option_functorSet s)
         STLC_gen)
      (projSortToSet t ∙ hat_functorSet (s ⇒ t)).

  Definition lam_source_gen (s t : sort) : sortToSet2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET
      BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort STLC_Sig (inr (s,, t))) STLC_gen.

  Lemma lam_source_gen_ok (s t : sort) : lam_source_gen s t  = lam_source_gen_newstyle s t.
  Proof.
    apply idpath.
  Qed.

  (** the outcome of the second component of the hat functor in this construction: *)
  Lemma lam_source_gen_mor_pr2 (s t : sort) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    (u : sort) (pr : pr1 (pr1 (pr1 (lam_source_gen s t) ξ) u))
    : pr2 (pr1 (# (pr1 (lam_source_gen s t)) f) u pr) =
        # (pr1 (functor_compose (functor_compose (sorted_option_functorSet s) STLC_gen) (projSortToSet t))) f (pr2 pr).
  Proof.
    apply idpath.
  Qed.

  (** The lambda-abstraction constructor *)
  Definition lam_map_gen (s t : sort) : sortToSet2⟦lam_source_gen s t,STLC_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (ii2 (s,,t)) · STLC_tau_gen.

  Definition lam_map_gen_natural (s t : sort) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    : # (pr1 (lam_source_gen s t)) f · pr1 (lam_map_gen s t) ξ' = pr1 (lam_map_gen s t) ξ · # (pr1 STLC_gen) f
    := nat_trans_ax (lam_map_gen s t) ξ ξ' f.

  Lemma lam_map_gen_natural_pointwise (s t : sort) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort)
    : pr1 (# (pr1 (lam_source_gen s t)) f) u · pr1 (pr1 (lam_map_gen s t) ξ') u =
        pr1 (pr1 (lam_map_gen s t) ξ) u · pr1 (# (pr1 STLC_gen) f) u.
  Proof.
    apply (nat_trans_eq_weq HSET _ _ (lam_map_gen_natural s t ξ ξ' f)).
  Qed.

  Lemma lam_map_gen_natural_ppointwise (s t : sort) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    (u : sort) (elem : pr1 (pr1 (pr1 (lam_source_gen s t) ξ) u)) :
    pr1 (pr1 (lam_map_gen s t) ξ') u (pr1 (# (pr1 (lam_source_gen s t)) f) u elem) =
      pr1 (# (pr1 STLC_gen) f) u (pr1 (pr1 (lam_map_gen s t) ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ (lam_map_gen_natural_pointwise s t ξ ξ' f u)).
  Qed.

  Section Church.

    (** fix a sort, viewed as an atom *)
    Context (s : sort).

    Definition ChurchZero_gen (ξ : sortToSet) : STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s)).
    Proof.
      (** abstract a first variable - forced to be of type [s ⇒ s] *)
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      change (STLC_gen_ctx_sort (ctx_ext ξ (s ⇒ s)) (s ⇒ s)).
      (** abstract a second variable - forced to be of type [s] *)
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      change (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
      (** take a variable *)
      simple refine (pr1 (pr1 STLC_eta_gen _) _ _).
      cbn.
      (** the available variables are seen, pick the last added variable of type [s] *)
      apply ii1.
      exists (idpath _).
      exact tt.
    Defined.

    Definition ChurchOne_gen (ξ : sortToSet) : STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s)).
    Proof.
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      (** do an application with argument type [s] - not giving this argument would slow down the further steps *)
      refine (pr1 (pr1 (app_map_gen s _) _) _ _).
      split; exists (idpath _).
      - change (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) (s ⇒ s)).
        simple refine (pr1 (pr1 STLC_eta_gen _) _ _).
        cbn.
        (** the available variables are seen, pick the first added variable of type [s ⇒ s] *)
        apply ii2.
        apply ii1.
        exists (idpath _).
        exact tt.
      - change (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
        simple refine (pr1 (pr1 STLC_eta_gen _) _ _).
        cbn.
        (** pick the last added variable of type [s] *)
        apply ii1.
        exists (idpath _).
        exact tt.
    Defined.


    Definition Church_gen_body (n : nat) (ξ : sortToSet) : STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s.
    Proof.
      induction n.
      - simple refine (pr1 (pr1 STLC_eta_gen _) _ _).
        cbn.
        apply ii1.
        exists (idpath _).
        exact tt.
      - refine (pr1 (pr1 (app_map_gen s _) _) _ _).
        split; exists (idpath _).
        + change (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) (s ⇒ s)).
          simple refine (pr1 (pr1 STLC_eta_gen _) _ _).
          cbn.
          apply ii2.
          apply ii1.
          exists (idpath _).
          exact tt.
        + exact IHn.
    Defined.

    Lemma Church_gen_body_rec_eq (n : nat) (ξ : sortToSet) :
      Church_gen_body (S n) ξ =
        pr1 (pr1 (app_map_gen s s) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s
     ((idpath s,,
       pr1 (pr1 STLC_eta_gen (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) (s ⇒ s)
         (inr (inl (idpath (s ⇒ s),, tt)) : pr1 (pr1 (Id (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) (s ⇒ s)))),,
        idpath s,, Church_gen_body n ξ).
    Proof.
      apply idpath.
    Qed.

    Definition Church_gen_header (ξ : sortToSet) :
      STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s -> STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s)).
    Proof.
      intro body.
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      exact body.
    Defined.

    Definition Church_gen (n : nat) (ξ : sortToSet) : STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s))
      := Church_gen_header ξ (Church_gen_body n ξ).

  End Church.

  Section Church_functor.

    Definition Church_gen_body_target_data: functor_data sortToSet sortToSet.
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
                      (# (sorted_option_functorSet s)
                         (# (sorted_option_functorSet (s ⇒ s)) f))) s).
    Defined.

    Lemma Church_gen_body_target_data_ok : is_functor Church_gen_body_target_data.
    Proof.
      split; red.
      - intro ξ.
        apply nat_trans_eq; try apply HSET.
        intro s.
        apply funextfun.
        intro elem.
        unfold functor_on_morphisms.
        unfold Church_gen_body_target_data.
        unfold pr2.
        unfold make_functor_data.
        unfold nat_trans_functor_path_pregroupoid.
        unfold make_nat_trans.
        unfold nat_trans_data_from_nat_trans_funclass.
        unfold pr1.
        do 2 rewrite functor_id.
        rewrite (functor_id STLC_gen).
        apply idpath.
      - intros ξ1 ξ2 ξ3 f g.
        apply nat_trans_eq; try apply HSET.
        intro s.
        apply funextfun.
        intro elem.
        unfold functor_on_morphisms.
        unfold Church_gen_body_target_data.
        unfold make_functor_data.
        unfold nat_trans_functor_path_pregroupoid.
        unfold make_nat_trans.
        unfold pr2.
        unfold nat_trans_data_from_nat_trans_funclass.
        unfold pr1.
        do 2 rewrite functor_comp.
        rewrite (functor_comp STLC_gen).
        apply idpath.
    Qed.

    Definition Church_gen_body_target : sortToSet2 := _,, Church_gen_body_target_data_ok.

    Definition Church_gen_body_sortToSet_data (n : nat) (ξ : sortToSet) : global_element TsortToSet (pr1 Church_gen_body_target ξ).
    Proof.
      use nat_trans_functor_path_pregroupoid.
      intros s _.
      exact (Church_gen_body s n ξ).
    Defined.

    Lemma Church_gen_body_sortToSet_data_ok (n : nat) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) :
      Church_gen_body_sortToSet_data n ξ · # (pr1 Church_gen_body_target) f = Church_gen_body_sortToSet_data n ξ'.
    Proof.
      induction n.
      - apply nat_trans_eq; try apply HSET.
        intros s. apply funextfun.
        intros one. cbn in one. induction one.
        etrans.
        2: { apply pathsinv0, (STLC_eta_gen_natural'_ppointwise _ _
                                 (# (sorted_option_functorSet s)
                                    (# (sorted_option_functorSet (s ⇒ s)) f))
                                 s (inl (idpath s,, tt))). }
        apply idpath.
      - apply nat_trans_eq; try apply HSET.
        intros s. apply funextfun.
        intros one. cbn in one. induction one.
        set (aux := (λ (s0 : path_pregroupoid sort Hsort) (_ : pr1 (pr1 (pr1 TsortToSet) s0)),
                      Church_gen_body s0 (S n) ξ) : ∏ x : path_pregroupoid sort Hsort,
                   SET ⟦ pr1 (pr1 TsortToSet) x, pr1 (pr1 Church_gen_body_target ξ) x ⟧).
        match goal with |[ |- _ = ?rhs] => set (therhs := rhs) end.
        change (pr1 (# (pr1 Church_gen_body_target) f) s (aux s tt) = therhs).
        change (pr1 (# (pr1 Church_gen_body_target) f) s (Church_gen_body s (S n) ξ) =
                  Church_gen_body s (S n) ξ').
        do 2 rewrite Church_gen_body_rec_eq.
        clear aux therhs.
        assert (IHnpointwise : pr1 (# (pr1 Church_gen_body_target) f) s (Church_gen_body s n ξ) =
                                 Church_gen_body s n ξ').
        { apply (toforallpaths _ _ _ (toforallpaths _ _ _ (maponpaths pr1 IHn) s) tt). }
        rewrite <- IHnpointwise.
        clear IHnpointwise.
        unfold Church_gen_body_target.
        unfold pr1.
        unfold Church_gen_body_target_data.
        unfold make_functor_data.
        unfold functor_on_morphisms at 4.
        unfold pr2.
        unfold nat_trans_functor_path_pregroupoid.
        unfold make_nat_trans.
        apply pathsinv0.
        unfold functor_on_morphisms at 7.
        unfold pr2.
        apply pathsinv0.
        (** now begins the naturality reasoning *)
        etrans.
        match goal with |[ |- _ ?arg = _] => set (thearg := arg) end.
        use (maponpaths (fun x : SET
                                 ⟦ pr1 (pr1 STLC_gen (sorted_option_functorSet s (sorted_option_functorSet (s ⇒ s) ξ))) s,
                                   pr1 (pr1 STLC_gen (sorted_option_functorSet s (sorted_option_functorSet (s ⇒ s) ξ'))) s ⟧
                         => x thearg)).
        2: { apply sortToSet2_comp_on_mor. }
        rewrite <- app_map_gen_natural_ppointwise.
        apply maponpaths.
        use dirprodeq; [unfold pr1 | unfold pr2].
        + rewrite app_source_gen_mor_pr1.
          unfold pr1.
          use dirprodeq.
          * apply idpath.
          * unfold pr2.
            etrans.
            2: { apply pathsinv0, (STLC_eta_gen_natural'_ppointwise _ _
                                     (# (pr1 (sorted_option_functorSet s))
                                        (# (pr1 (sorted_option_functorSet (s ⇒ s))) f))
                                     (s ⇒ s) (inr (inl (idpath (s ⇒ s),, tt)))). }
            apply idpath.
        + apply app_source_gen_mor_pr2.
    Qed. (* slow *)

    Definition Church_gen_body_sortToSet (n : nat) : global_element TsortToSet2 Church_gen_body_target.
    Proof.
      use make_global_element_functor_precat.
      - exact (Church_gen_body_sortToSet_data n).
      - exact (Church_gen_body_sortToSet_data_ok n).
    Defined.

    Definition Church_gen_header_sortToSet_data : nat_trans_data (pr1 Church_gen_body_target)
            (pr1 (functor_compose STLC_gen (projSortToSetvariable (λ s : sort, (s ⇒ s) ⇒ s ⇒ s)))).
    Proof.
      intro ξ.
      use nat_trans_functor_path_pregroupoid.
      intros s body.
      exact (Church_gen_header s ξ body).
    Defined.

    Lemma Church_gen_header_sortToSet_data_ok : is_nat_trans _ _ Church_gen_header_sortToSet_data.
      intros ξ ξ' f.
      apply nat_trans_eq; try apply HSET.
      intros s. apply funextfun.
      intro body.
      simpl. unfold compose. simpl.
      (** the following for better readability *)
      match goal with |[ |- Church_gen_header s ξ' (pr1 (# (pr1 STLC_gen) ?uglyxi ) s body)= _] => set (theuglyxi := uglyxi) end.
      unfold Church_gen_header.
      rewrite <- lam_map_gen_natural_ppointwise.
      apply maponpaths.
      use dirprodeq.
      - apply idpath.
      - unfold pr2.
        etrans.
        2: { apply pathsinv0, lam_source_gen_mor_pr2. }
        unfold pr2.
        etrans.
        2: { apply pathsinv0, postcomp_with_projSortToSet_on_mor. }
        unfold functor_compose.
        etrans.
        2: { match goal with |[ |- _= _ ?arg ] => set (thearg := arg) end.
             use (maponpaths (fun x : SET
                                      ⟦ pr1 (pr1 (sorted_option_functorSet (s ⇒ s) ∙ STLC_gen) ξ) (s ⇒ s),
                                        pr1 (pr1 (sorted_option_functorSet (s ⇒ s) ∙ STLC_gen) ξ') (s ⇒ s) ⟧
                              =>  x thearg)).
              2: { apply pathsinv0, sortToSet2_comp_on_mor. }
        }
        etrans.
        2: { apply lam_map_gen_natural_ppointwise. }
        apply maponpaths.
        use dirprodeq.
        + apply idpath.
        + unfold pr2.
          etrans.
          2: { apply pathsinv0, lam_source_gen_mor_pr2. }
          apply idpath.
    Qed.

    Definition Church_gen_header_sortToSet : sortToSet2⟦Church_gen_body_target,
         functor_compose STLC_gen (projSortToSetvariable (fun s => (s ⇒ s) ⇒ (s ⇒ s)))⟧
      := _,, Church_gen_header_sortToSet_data_ok.

     Definition Church_gen_sortToSet (n : nat) : global_element TsortToSet2
           (functor_compose STLC_gen (projSortToSetvariable (fun s => (s ⇒ s) ⇒ (s ⇒ s))))
      := Church_gen_body_sortToSet n · Church_gen_header_sortToSet.


     (** this makes superfluous the lengthy definitions below that are kept for comparison *)

    Definition old_Church_gen_sortToSet_data (n : nat) (ξ : sortToSet):
      global_element TsortToSet
        (pr1 (functor_compose STLC_gen (projSortToSetvariable (λ s : sort, (s ⇒ s) ⇒ s ⇒ s))) ξ).
    Proof.
      use nat_trans_functor_path_pregroupoid.
      intros s _.
      change (STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s))).
      exact (Church_gen s n ξ).
    Defined.


    Lemma old_Church_gen_sortToSet_data_ok (n : nat) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧):
      old_Church_gen_sortToSet_data n ξ ·
        # (pr1 (functor_compose STLC_gen (projSortToSetvariable (λ s : sort, (s ⇒ s) ⇒ s ⇒ s)))) f =
        old_Church_gen_sortToSet_data n ξ'.
    Proof.
      apply nat_trans_eq; try apply HSET.
      intros s. apply funextfun.
      intros one. cbn in one. induction one.
      simpl. unfold compose. simpl. induction n.
      - change (pr1 (# (pr1 STLC_gen) f) ((s ⇒ s) ⇒ s ⇒ s) (ChurchZero_gen s ξ) = ChurchZero_gen s ξ').
        unfold ChurchZero_gen.
        rewrite <- lam_map_gen_natural_ppointwise.
        apply maponpaths.
        use dirprodeq.
        + apply idpath.
        + unfold pr2.
          etrans.
          { apply lam_source_gen_mor_pr2. }
          unfold pr2.
          etrans.
          { apply postcomp_with_projSortToSet_on_mor. }
          unfold functor_compose.
          etrans.
          match goal with |[ |- _ ?arg = _] => set (thearg := arg) end.
          use (maponpaths (fun x : SET
                                   ⟦ pr1 (pr1 (sorted_option_functorSet (s ⇒ s) ∙ STLC_gen) ξ) (s ⇒ s),
                                     pr1 (pr1 (sorted_option_functorSet (s ⇒ s) ∙ STLC_gen) ξ') (s ⇒ s) ⟧
                           =>  x thearg)).
          2: { apply sortToSet2_comp_on_mor. }
          etrans.
          { apply pathsinv0, lam_map_gen_natural_ppointwise. }
          apply maponpaths.
          use dirprodeq.
          * apply idpath.
          * unfold pr2.
            etrans.
            { apply lam_source_gen_mor_pr2. }
            unfold pr2.
            etrans.
            { apply postcomp_with_projSortToSet_on_mor. }
            etrans.
            match goal with |[ |- _ ?arg = _] => set (thearg := arg) end.
            use (maponpaths (fun x : SET
       ⟦ pr1 (pr1 (functor_compose (sorted_option_functorSet s) STLC_gen) (pr1 (sorted_option_functorSet (s ⇒ s)) ξ)) s,
        pr1 (pr1 (functor_compose (sorted_option_functorSet s) STLC_gen) (pr1 (sorted_option_functorSet (s ⇒ s)) ξ')) s ⟧
                             => x thearg)).
            2: { apply sortToSet2_comp_on_mor. }
            etrans.
            { apply pathsinv0, STLC_eta_gen_natural'_ppointwise. }
            apply maponpaths.
            apply idpath.
      - (** the successor case - this will not go through since there is the common prefix with the two lambda abstractions *)
        induction n.
        + change (pr1 (# (pr1 STLC_gen) f) ((s ⇒ s) ⇒ s ⇒ s) (ChurchOne_gen s ξ) = ChurchOne_gen s ξ').
          unfold ChurchOne_gen.
          rewrite <- lam_map_gen_natural_ppointwise.
          apply maponpaths.
          use dirprodeq.
          * apply idpath.
          * unfold pr2.
            etrans.
            { apply lam_source_gen_mor_pr2. }
            unfold pr2.
            etrans.
            { apply postcomp_with_projSortToSet_on_mor. }
            unfold functor_compose.
            etrans.
            match goal with |[ |- _ ?arg = _] => set (thearg := arg) end.
            use (maponpaths (fun x : SET
       ⟦ pr1 (pr1 (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET (s ⇒ s) ∙ STLC_gen) ξ) (s ⇒ s),
       pr1 (pr1 (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET (s ⇒ s) ∙ STLC_gen) ξ') (s ⇒ s) ⟧
                             => x thearg)).
            2: { apply sortToSet2_comp_on_mor. }
            rewrite <- lam_map_gen_natural_ppointwise.
            apply maponpaths.
            use dirprodeq.
            -- apply idpath.
            -- unfold pr2.
               etrans.
               { apply lam_source_gen_mor_pr2. }
               unfold pr2.
               etrans.
               { apply postcomp_with_projSortToSet_on_mor. }
               unfold functor_compose.
               etrans.
               match goal with |[ |- _ ?arg = _] => set (thearg := arg) end.
               use (maponpaths (fun x : SET
       ⟦ pr1 (pr1 (sorted_option_functorSet s ∙ STLC_gen) (pr1 (sorted_option_functorSet (s ⇒ s)) ξ)) s,
        pr1 (pr1 (sorted_option_functorSet s ∙ STLC_gen) (pr1 (sorted_option_functorSet (s ⇒ s)) ξ')) s ⟧
                                => x thearg)).
               2: { apply sortToSet2_comp_on_mor. }
               rewrite <- app_map_gen_natural_ppointwise.
               apply maponpaths.
               use dirprodeq; [unfold pr1 | unfold pr2].
               ++ rewrite app_source_gen_mor_pr1.
                  unfold pr1.
                  use dirprodeq.
                  --- apply idpath.
                  --- unfold pr2.
                      etrans.
                      2: { apply pathsinv0, (STLC_eta_gen_natural'_ppointwise _ _
                                               (# (sorted_option_functorSet s) (# (sorted_option_functorSet (s ⇒ s)) f))
                                               (s ⇒ s) (inr (inl (idpath (s ⇒ s),, tt)))). }
                      apply idpath.
               ++ rewrite app_source_gen_mor_pr2.
                  unfold pr2.
                  use dirprodeq.
                  --- apply idpath.
                  --- unfold pr2.
                      etrans.
                      2: { apply pathsinv0, (STLC_eta_gen_natural'_ppointwise _ _
                                               (# (sorted_option_functorSet s) (# (sorted_option_functorSet (s ⇒ s)) f))
                                               s (inl (idpath s,, tt))). }
                      apply idpath.
        + (** case of n>=2 *)
          admit.
    Abort.

(*   Definition old_Church_gen_sortToSet (n : nat) : global_element TsortToSet2
                                                 (functor_compose STLC_gen (projSortToSetvariable (fun s => (s ⇒ s) ⇒ (s ⇒ s)))).
    Proof.
      use make_global_element_functor_precat.
      - exact (old_Church_gen_sortToSet_data n).
      - exact (old_Church_gen_sortToSet_data_ok n).
    Defined.
*)

  End Church_functor.

End IndAndCoind.

Definition STLC_ctx_sort_ind (ξ : sortToSet) (s : sort) : UU
  := STLC_gen_ctx_sort σind ξ s.
Definition STLC_ctx_sort_coind (ξ : sortToSet) (s : sort) : UU
  := STLC_gen_ctx_sort σcoind ξ s.

Definition STLC_ind : sortToSet2 := STLC_gen σind.
Definition STLC_coind : sortToSet2 := STLC_gen σcoind.

Definition STLC_eta_ind : sortToSet2⟦Id,STLC_ind⟧ := STLC_eta_gen σind.
Definition STLC_eta_coind : sortToSet2⟦Id,STLC_coind⟧ := STLC_eta_gen σcoind.

Definition STLC_tau_ind : STLC_Functor_H STLC_ind --> STLC_ind  := SigmaMonoid_τ θSTLC σind.
Definition STLC_tau_coind : STLC_Functor_H STLC_coind --> STLC_coind  := SigmaMonoid_τ θSTLC σcoind.

Definition app_source_ind (s t : sort) : sortToSet2 := app_source_gen σind s t.
Definition app_map_ind (s t : sort) : sortToSet2⟦app_source_ind s t,STLC_ind⟧ := app_map_gen σind s t.
Definition lam_source_ind (s t : sort) : sortToSet2 := lam_source_gen σind s t.
Definition lam_map_ind (s t : sort) : sortToSet2⟦lam_source_ind s t,STLC_ind⟧ := lam_map_gen σind s t.

Definition app_source_coind (s t : sort) : sortToSet2 := app_source_gen σcoind s t.
Definition app_map_coind (s t : sort) : sortToSet2⟦app_source_coind s t,STLC_coind⟧ := app_map_gen σcoind s t.
Definition lam_source_coind (s t : sort) : sortToSet2 := lam_source_gen σcoind s t.
Definition lam_map_coind (s t : sort) : sortToSet2⟦lam_source_coind s t,STLC_coind⟧ := lam_map_gen σcoind s t.


(** get a handle on the recursion principles *)

(** the initial algebra *)
Definition STLC_ind_IA : Initial (FunctorAlg STLC_Functor_Id_H)
  := DatatypeOfMultisortedBindingSig_CAT sort Hsort SET TerminalHSET InitialHSET BinProductsHSET
       BinCoproductsHSET (fun s s' => ProductsHSET (s=s')) CoproductsHSET (EsortToSet2 sort Hsort)
       (ColimsHSET_of_shape nat_graph) STLC_Sig.
(** notice that this is only the initial algebra and not the initial sigma monoid *)

(** the final coalgebra *)
Definition STLC_coind_FC : Terminal (CoAlg_category STLC_Functor_Id_H)
  := coindCodatatypeOfMultisortedBindingSig_CAT sort Hsort HSET TerminalHSET
         BinProductsHSET BinCoproductsHSET CoproductsHSET (LimsHSET_of_shape conat_graph)
         I_coproduct_distribute_over_omega_limits_HSET STLC_Sig is_univalent_HSET.

Section Church.
(** This section compiled when it was commented out so as to avoid [Admitted]. *)

(*
  Definition ChurchInfinity_body_sortToSet : global_element TsortToSet2 (Church_gen_body_target σcoind).
  Proof.
    (** has to use [STLC_coind_FC] in the right way *)
  Admitted.

  Definition ChurchInfinity_body (ξ : sortToSet) (s: sort) : STLC_gen_ctx_sort σcoind (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s.
  Proof.
    exact (pr1 ((pr1 ChurchInfinity_body_sortToSet) ξ) s tt).
  Defined.

  Definition ChurchInfinity_body_sortToSet_rec_eq_statement (ξ : sortToSet) (s : sort) : UU :=
    ChurchInfinity_body ξ s =
      pr1 (pr1 (app_map_coind s s) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s
        ((idpath s,,
            pr1 (pr1 STLC_eta_coind (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) (s ⇒ s)
            (inr (inl (idpath (s ⇒ s),, tt)) : pr1 (pr1 (Id (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) (s ⇒ s)))),,
           idpath s,, ChurchInfinity_body ξ s).

  Lemma ChurchInfinity_body_sortToSet_rec_eq (ξ : sortToSet) (s : sort) : ChurchInfinity_body_sortToSet_rec_eq_statement ξ s.
  Proof.
  Admitted.

  Definition ChurchInfinity_sortToSet : global_element TsortToSet2
           (functor_compose STLC_coind (projSortToSetvariable (fun s => (s ⇒ s) ⇒ (s ⇒ s))))
      := ChurchInfinity_body_sortToSet · (Church_gen_header_sortToSet σcoind).

  Definition ChurchInfinity (s : sort) (ξ : sortToSet) : STLC_ctx_sort_coind ξ ((s ⇒ s) ⇒ (s ⇒ s)).
  Proof.
    exact (pr1 ((pr1 ChurchInfinity_sortToSet) ξ) s tt).
  Defined.
*)
End Church.

End A.
