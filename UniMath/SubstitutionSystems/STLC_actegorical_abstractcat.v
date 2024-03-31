(**

Syntax of the simply-typed lambda calculus as a multisorted signature based on the actegorical development,
with an abstract base category [C] instead of [HSET] (the objects of [C] serve to represent collections of terms of a given sort in a given context, but also collections of names of variables of a given sort).

The development is "point-free" in the sense that no assumption of well-pointedness of [C] is made (that would allow to replay the point-wise reasoning that is possible in [HSET], as it is done in STLC_actegorical.v).

Thanks to that actegorical development, the inductive and the coinductive calculus are exposed in parallel.
The Church numerals are developed independently from the choice for inductive or coinductive syntax.

There is also the construction (by primitive corecursion) of the Church numeral for infinity in the coinductive calculus, with a proof that it satisfies a proper recursive equation.

Written by: Ralph Matthes, 2024 (generalized and expanded from STLC_actegorical.v)

 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.PartA.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
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
Require Import UniMath.SubstitutionSystems.MultiSortedBindingSig.
Require UniMath.SubstitutionSystems.SortIndexing.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_coind_actegorical.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.InstantiateHSET.
Require Import UniMath.SubstitutionSystems.MultiSortedEmbeddingIndCoindHSET.

Local Open Scope cat.

Section A.

  Context (sort : hSet) (arr : sort → sort → sort).

  Let Hsort : isofhlevel 3 sort := MultiSortedBindingSig.STLC_Hsort sort.

  Local Definition STLC_Sig := STLC_Sig sort arr.

  Context (C : category) (BP : BinProducts C) (BC : BinCoproducts C)
                         (TC : Terminal C) (CC : ∏ I : UU, isaset I → Coproducts I C).

  Let sortToC : category := SortIndexing.sortToC sort Hsort C.

  Let make_sortToC (f : sort → C) : sortToC := SortIndexing.make_sortToC sort Hsort C f.

  Let make_sortToC_mor := SortIndexing.make_sortToC_mor sort Hsort C.

  Local Lemma sortToC_comp {ξ1 ξ2 ξ3 : sortToC} (f : sortToC⟦ ξ1, ξ2 ⟧) (g : sortToC⟦ ξ2, ξ3 ⟧) (s : sort) :
    pr1 (f · g) s = pr1 f s · pr1 g s.
  Proof.
    apply idpath.
  Qed.

  Let BPsortToC : BinProducts sortToC := SortIndexing.BPsortToC sort Hsort _ BP.

  Let BCsortToC : BinCoproducts sortToC := SortIndexing.BCsortToC sort Hsort _ BC.

  Let TsortToC : Terminal sortToC := SortIndexing.TsortToC sort Hsort _ TC.

  Let sortToCC : category := SortIndexing.sortToCC sort Hsort C.

  Local Definition BPsortToCC : BinProducts sortToCC := SortIndexing.BPsortToCC sort Hsort _ BP.

  Local Definition CCsortToC : ∏ I : UU, isaset I → Coproducts I sortToC := SortIndexing.CCsortToC sort Hsort _ CC.

(** Some notations *)
(* Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set. *)
Local Notation "s ⇒ t" := (arr s t).
Local Notation "'Id'" := (functor_identity _).
(*Local Notation "a ⊕ b" := (BinCoproductObject (BinCoprodSortToSet a b)). *)
(* Local Notation "'1'" := (TerminalObject TerminalSortToSet). *)
Local Notation "F ⊗ G" := (BinProduct_of_functors BPsortToCC F G).

Let sortToC2 : category := SortIndexing.sortToC2 sort Hsort C.

Let projSortToC : sort -> sortToCC := projSortToC sort Hsort C.
Let hat_functorC : sort -> C ⟶ sortToC := hat_functor sort Hsort C CC.
Let sorted_option_functorC : sort → sortToC2 := sorted_option_functor sort Hsort C TC BC CC.

(*
Local Lemma sortToC2_comp {F1 F2 F3 : sortToC2} (f : sortToC2⟦F1, F2⟧) (g : sortToC2⟦F2, F3⟧) (ξ : sortToC) :
  pr1 (f · g) ξ = pr1 f ξ · pr1 g ξ.
Proof.
  apply idpath.
Qed.
 *)

(*
Local Lemma coproduct_of_functors_sortToC2_mor (I : UU) (isaset : isaset I) (F : I → sortToC2) (ξ ξ' : sortToC) (f : sortToC ⟦ ξ, ξ' ⟧) (s : sort) :
  pr1 (# (coproduct_of_functors I sortToC sortToC (CCsortToC _ isaset) F) f) s = CoproductOfArrows _ _ _ _ (λ i, pr1 (# (pr1 (F i)) f) s).
Proof.
  apply idpath.
Qed.
*)

Let TsortToC2 : Terminal sortToC2 := SortIndexing.TsortToC2 sort Hsort _ TC.

Local Definition BPsortToC2 : BinProducts sortToC2 := SortIndexing.BPsortToC2 sort Hsort _ BP.

Local Definition BCsortToC2 : BinCoproducts sortToC2 := SortIndexing.BCsortToC2 sort Hsort _ BC.

Local Definition CCsortToC2 : ∏ I : UU, isaset I → Coproducts I sortToC2 := SortIndexing.CCsortToC2 sort Hsort _ CC.

Let sortToC3 : category := SortIndexing.sortToC3 sort Hsort C.

Local Definition coproduct_of_functors_sortToC3_mor (I : UU) (isa : isaset I) (F : I → sortToC3) (G G' : sortToC2) (α : sortToC2 ⟦ G, G' ⟧) (ξ : sortToC) (s : sort) :
  pr1 (pr1 (# (coproduct_of_functors I sortToC2 sortToC2 (CCsortToC2 _ isa) F) α) ξ) s = CoproductOfArrows _ _ _ _ (λ i, pr1 (pr1 (# (pr1 (F i)) α) ξ) s)
  := SortIndexing.coproduct_of_functors_sortToC3_mor sort Hsort C CC I isa F G G' α ξ s.

Lemma postcomp_with_projSortToC_on_mor (F : sortToC2) (s: sort) (ξ ξ' : sortToC) (f : sortToC ⟦ ξ, ξ' ⟧)
(* (arg : global_element TC (pr1 (functor_compose F (projSortToC s)) ξ)) *)
  : # (pr1 (functor_compose F (projSortToC s))) f  = pr1 (# (pr1 F) f) s.
Proof.
  apply idpath.
Qed.


(** the canonical functor associated with STLC_Sig *)
Definition STLC_Functor_H : functor sortToC2 sortToC2 :=
  MultiSorted_actegorical.MultiSortedSigToFunctor' sort Hsort C
    TC BP BC CC STLC_Sig.

(** the functor of which the fixed points are considered *)
Definition STLC_Functor_Id_H : functor sortToC2 sortToC2 :=
  SubstitutionSystems.Id_H sortToC BCsortToC STLC_Functor_H.

(** the canonical strength associated with STLC_Sig *)
Let θSTLC := MultiSortedMonadConstruction_actegorical.MultiSortedSigToStrength' sort Hsort C
               TC BP BC CC STLC_Sig.

Definition ctx_ext (ξ : sortToC) (s : sort) : sortToC
  := pr1 (sorted_option_functor sort Hsort C TC BC CC s) ξ.
(*  := pr1 (option_list sort Hsort C TC BC CC (s :: [])) ξ. *)

(** the sigma-monoids for wellfounded and non-wellfounded syntax for STLC *)
Context (IC : Initial C)
  (* (ProductsC : ∏ I : UU, Products.Products I C) *) (eqsetPC : forall (s s' : sort), Products.Products (s=s') C)
  (EsortToC2 : exponentials.Exponentials BPsortToC2)
  (ColimsC_of_shape_nat_graph : Colimits.Colims_of_shape nat_graph C).

Let σind : SigmaMonoid θSTLC := pr1 (InitialSigmaMonoidOfMultiSortedSig_CAT sort Hsort C TC IC BP BC eqsetPC CC EsortToC2 ColimsC_of_shape_nat_graph STLC_Sig).

Context (LimsC_of_shape_conat_graph : Graphs.Limits.Lims_of_shape conat_graph C)
    (I_coproduct_distribute_over_omega_limits_C : ∏ I : SET,
          CommutingOfOmegaLimitsAndCoproducts.ω_limits_distribute_over_I_coproducts C I
            LimsC_of_shape_conat_graph (CC (pr1 I) (pr2 I)))
    (is_univalent_C : is_univalent C). (** univalence is there to shorten one argument in the construction of the following *)

Let σcoind : SigmaMonoid θSTLC := coindSigmaMonoidOfMultiSortedSig_CAT sort Hsort C TC
         BP BC CC LimsC_of_shape_conat_graph
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
    (post_comp_functor (projSortToC (s ⇒ t)) ⊗ post_comp_functor (projSortToC s))
      ∙ (post_comp_functor (hat_functorC t)).

  Definition app_source_gen_newstyle (s t : sort) : sortToC2 :=
    BinProduct_of_functors BPsortToC
      (functor_compose STLC_gen
         (projSortToC (s ⇒ t) ∙ hat_functorC t))
      (functor_compose STLC_gen
         (projSortToC s ∙ hat_functorC t)).

  Definition app_source_gen (s t : sort) : sortToC2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort C TC
      BP BC CC (arity sort STLC_Sig (inl (s,, t))) STLC_gen.

  Lemma app_source_gen_ok (s t : sort) : app_source_gen s t  = app_source_gen_newstyle s t.
  Proof.
    apply idpath.
  Qed.

  Definition app_source_gen_mor_eq_statement (s t : sort) {ξ ξ' : sortToC} (f : sortToC ⟦ ξ, ξ' ⟧)
    (u : sort) : UU.
  Proof.
    refine (pr1 (# (pr1 (app_source_gen s t)) f) u =  BinProductOfArrows C (BP _ _) (BP _ _)  _ _).
    - exact (pr1 (# (pr1 (functor_compose STLC_gen
                            (projSortToC (s ⇒ t) ∙ hat_functorC t))) f) u).
    - exact (pr1 (# (pr1 (functor_compose STLC_gen
                            (projSortToC s ∙ hat_functorC t))) f) u).
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
    pre_comp_functor (sorted_option_functor sort Hsort C TC BC CC s)
      ∙ post_comp_functor (projSortToC t)
      ∙ post_comp_functor (hat_functorC (s ⇒ t)).

  Definition lam_source_gen_newstyle (s t : sort) : sortToC2 :=
    functor_compose
      (functor_compose
         (sorted_option_functor sort Hsort C TC BC CC s)
         STLC_gen)
      (projSortToC t ∙ hat_functorC (s ⇒ t)).

  Definition lam_source_gen (s t : sort) : sortToC2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort C TC
      BP BC CC (arity sort STLC_Sig (inr (s,, t))) STLC_gen.

  Lemma lam_source_gen_ok (s t : sort) : lam_source_gen s t  = lam_source_gen_newstyle s t.
  Proof.
    apply idpath.
  Qed.

  Lemma lam_source_gen_mor_eq (s t : sort) {ξ ξ' : sortToC} (f : sortToC ⟦ ξ, ξ' ⟧) (u : sort)
    : pr1 (# (pr1 (lam_source_gen s t)) f) u =
        pr1 (# (pr1 (functor_compose
      (functor_compose
         (sorted_option_functor sort Hsort C TC BC CC s)
         STLC_gen)
      (projSortToC t ∙ hat_functorC (s ⇒ t)))) f) u.
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

    Definition ChurchZero_gen (ξ : sortToC) : global_element TC (STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s))).
    Proof.
      (** abstract a first variable - forced to be of type [s ⇒ s] *)
      refine (_ · pr1 (pr1 (lam_map_gen _ _) _) _).
      refine (_ · CoproductIn _ _ _ (idpath _)).
      change (global_element TC (STLC_gen_ctx_sort (ctx_ext ξ (s ⇒ s)) (s ⇒ s))).
      (** abstract a second variable - forced to be of type [s] *)
      refine (_ · pr1 (pr1 (lam_map_gen _ _) _) _).
      refine (_ · CoproductIn _ _ _ (idpath _)).
      change (global_element TC (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s)).
      (** take a variable *)
      simple refine (_ · pr1 (pr1 STLC_eta_gen _) _).
      (* unfold functor_identity, functor_identity_data, functor_data_constr, functor_data_from_functor, functor_on_objects, pr1. *)
      (** the available variables are seen, pick the last added variable of type [s] *)
      refine (_ · BinCoproductIn1 _).
      cbn.
      exact (CoproductIn _ _ _ (idpath _)).
    Defined.

    Definition ChurchOne_gen (ξ : sortToC) : global_element TC (STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s))).
    Proof.
      refine (_ · pr1 (pr1 (lam_map_gen _ _) _) _).
      refine (_ · CoproductIn _ _ _ (idpath _)).
      refine (_ · pr1 (pr1 (lam_map_gen _ _) _) _).
      refine (_ · CoproductIn _ _ _ (idpath _)).
      refine (_ · pr1 (pr1 (app_map_gen s _) _) _).
      (** do an application with argument type [s] - not giving this argument would potentially slow down the further steps *)
      apply BinProductArrow; refine (_ · CoproductIn _ _ _ (idpath _)).
      - change (global_element TC (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) (s ⇒ s))).
        simple refine (_ · pr1 (pr1 STLC_eta_gen _) _).
        (** the available variables are seen, pick the first added variable of type [s ⇒ s] *)
        refine (_ · BinCoproductIn2 _).
        refine (_ · BinCoproductIn1 _).
        cbn.
        exact (CoproductIn _ _ _ (idpath _)).
      - change (global_element TC (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s)).
        simple refine (_ · pr1 (pr1 STLC_eta_gen _) _).
        (** pick the last added variable of type [s] *)
        refine (_ · BinCoproductIn1 _).
        cbn.
        exact (CoproductIn _ _ _ (idpath _)).
    Defined.


    Definition Church_gen_body (n : nat) (ξ : sortToC) : global_element TC (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
    Proof.
      induction n.
      - simple refine (_ · pr1 (pr1 STLC_eta_gen _) _).
        refine (_ · BinCoproductIn1 _).
        cbn.
        exact (CoproductIn _ _ _ (idpath _)).
      - refine (_ · pr1 (pr1 (app_map_gen s _) _) _).
        apply BinProductArrow; refine (_ · CoproductIn _ _ _ (idpath _)).
        + change (global_element TC (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) (s ⇒ s))).
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
    Arguments BP {_ _}.
    Arguments CoproductIn {_ _ _ _}.
    Arguments BinCoproductIn1 {_ _ _ _}.
    Arguments BinCoproductIn2 {_ _ _ _}.

    (** by careful inspection of the generated term, one can obtain the following recursive equation *)
    Lemma Church_gen_body_rec_eq (n : nat) (ξ : sortToC) :
      Church_gen_body (S n) ξ =
        BinProductArrow BP
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
      : global_element TC (STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s)))
      := (Church_gen_body n ξ) · Church_gen_header ξ.

  End Church.

  Section Church_functor.

    Arguments BinProductArrow {_ _ _} _ {_}.
    Arguments BP {_ _}.
    Arguments CoproductIn {_ _ _ _}.
    Arguments BinCoproductIn1 {_ _ _ _}.
    Arguments BinCoproductIn2 {_ _ _ _}.

    Definition Church_gen_body_target_data: functor_data sortToC sortToC.
    Proof.
      use make_functor_data.
      - intro ξ.
        apply make_sortToC.
        intro s.
        exact (pr1 (pr1 STLC_gen (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s).
        (** this is the pointwise formula - with context and sort argument *)
      - intros ξ ξ' f.
        apply make_sortToC_mor.
        intro s.
        simpl.
        exact (pr1 (# (pr1 STLC_gen)
                      (# (sorted_option_functor sort Hsort C TC BC CC s)
                         (# (sorted_option_functor sort Hsort C TC BC CC (s ⇒ s)) f))) s).
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
        rewrite (functor_id (sorted_option_functor sort Hsort C TC BC CC (s ⇒ s))).
        rewrite (functor_id (sorted_option_functor sort Hsort C TC BC CC s)).
        rewrite (functor_id STLC_gen).
        apply idpath.
      - intros ξ1 ξ2 ξ3 f g.
        apply nat_trans_eq; try apply C.
        intro s.
        unfold Church_gen_body_target_data.
        Opaque STLC_gen sorted_option_functor.
        simpl.
        rewrite (functor_comp (sorted_option_functor sort Hsort C TC BC CC (s ⇒ s))).
        rewrite (functor_comp (sorted_option_functor sort Hsort C TC BC CC s)).
        rewrite (functor_comp STLC_gen).
        apply idpath.
    Qed.

    Transparent STLC_gen sorted_option_functor.

    Definition Church_gen_body_target : sortToC2 := _,, Church_gen_body_target_data_ok.

    Definition Church_gen_body_sortToC_data (n : nat) (ξ : sortToC) : global_element TsortToC (pr1 Church_gen_body_target ξ).
    Proof.
      use make_sortToC_mor.
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
                                 (# (sorted_option_functor sort Hsort C TC BC CC s)
                                    (# (sorted_option_functor sort Hsort C TC BC CC (s ⇒ s)) f))
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
               2: { apply pathsinv0, BinCoproductIn1Commutes. }
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
        unfold make_sortToC_mor, nat_trans_functor_path_pregroupoid.
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
                                 (# (sorted_option_functor sort Hsort C TC BC CC s)
                                    (# (sorted_option_functor sort Hsort C TC BC CC (s ⇒ s)) f))
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
                      unfold make_sortToC_mor, nat_trans_functor_path_pregroupoid, make_nat_trans, nat_trans_data_from_nat_trans_funclass.
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

    Definition Church_gen_body_sortToC (n : nat) : global_element TsortToC2 Church_gen_body_target.
    Proof.
      use make_global_element_functor_precat.
      - exact (Church_gen_body_sortToC_data n).
      - exact (Church_gen_body_sortToC_data_ok n).
    Defined.

    Definition Church_gen_header_sortToC_data : nat_trans_data (pr1 Church_gen_body_target)
            (pr1 (functor_compose STLC_gen (projSortToCvariable sort Hsort C (λ s : sort, (s ⇒ s) ⇒ s ⇒ s)))).
    Proof.
      intro ξ.
      use make_sortToC_mor.
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

     Definition Church_gen_sortToC (n : nat) : global_element TsortToC2
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
  := DatatypeOfMultisortedBindingSig_CAT sort Hsort C TC IC BP
       BC eqsetPC CC EsortToC2
       ColimsC_of_shape_nat_graph STLC_Sig.
(** notice that this is only the initial algebra and not the initial sigma monoid *)

(** the final coalgebra *)
Definition STLC_coind_FC : Terminal (CoAlg_category STLC_Functor_Id_H)
  := coindCodatatypeOfMultisortedBindingSig_CAT sort Hsort C TC
         BP BC CC LimsC_of_shape_conat_graph
         I_coproduct_distribute_over_omega_limits_C STLC_Sig is_univalent_C.

Section Church.

  (** we are defining the Church numeral for infinity *)

  Let corecsource : sortToC2 := functor_compose STLC_coind (projSortToCvariable sort Hsort C (fun s => (s ⇒ s))).


  Definition IterateInfinite_rec_coalg_data_data (ξ : sortToC) (s : sort)
    : C⟦pr1 (pr1 corecsource ξ) s, pr1 (pr1 (STLC_Functor_Id_H (BCsortToC2 corecsource STLC_coind)) ξ) s⟧.
  Proof.
    refine (_ · BinCoproductIn2 _).
    refine (_ · CoproductIn _ _ _ (ii1 (s,,s))).
    use BinProductArrow.
    - (** the term to be applied is the original argument *)
      refine (_ · CoproductIn _ _ _ (idpath _)).
      change (C ⟦ pr1 (pr1 corecsource ξ) s, pr1 (pr111 (BCsortToC2 corecsource STLC_coind) ξ) (s ⇒ s)⟧).
      apply BinCoproductIn2.
    - (** the argument of the application is the result of the corecursive call *)
      refine (_ · CoproductIn _ _ _ (idpath _)).
      change (C ⟦ pr1 (pr1 corecsource ξ) s, pr1 (pr111 (BCsortToC2 corecsource STLC_coind) ξ) s⟧).
      apply BinCoproductIn1.
  Defined.

  Definition IterateInfinite_rec_coalg_data
    : nat_trans_data (pr1 corecsource) (pr1 (STLC_Functor_Id_H (BCsortToC2 corecsource STLC_coind))).
  Proof.
    intro ξ.
    use make_sortToC_mor.
    intro s.
    exact (IterateInfinite_rec_coalg_data_data ξ s).
  Defined.

  Arguments BinProductArrow {_ _ _} _ {_}.
  Arguments BP {_ _}.
  Arguments CoproductIn {_ _ _ _}.
  Arguments BinCoproductIn1 {_ _ _ _}.
  Arguments BinCoproductIn2 {_ _ _ _}.


  Lemma IterateInfinite_rec_coalg_data_ok : is_nat_trans _ _ IterateInfinite_rec_coalg_data.
  Proof.
    intros ξ ξ' f.
    apply nat_trans_eq; try apply C.
    intro s.
    change (pr1 (# (pr1 corecsource) f · IterateInfinite_rec_coalg_data ξ') s =
              pr1 (IterateInfinite_rec_coalg_data ξ · # (pr1 (STLC_Functor_Id_H (BCsortToC2 corecsource STLC_coind))) f) s).
    change (pr1 (# (pr1 STLC_coind) f) (s ⇒ s) · IterateInfinite_rec_coalg_data_data ξ' s =
              IterateInfinite_rec_coalg_data_data ξ s · pr1 (# (pr1 (STLC_Functor_Id_H ((BCsortToC2 corecsource STLC_coind) : sortToC2))) f) s).
    unfold IterateInfinite_rec_coalg_data_data.
    etrans.
    2: { repeat rewrite assoc'.
         do 2 apply maponpaths.
         apply pathsinv0.
         apply BinCoproductOfArrowsIn2. }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    2: { repeat rewrite assoc'.
         apply maponpaths.
         apply pathsinv0.
         refine (CoproductOfArrowsIn _ _ _ _ _ (inl (s,, s))). }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    match goal with |[   |- _ =_ · ?sndmor] => set (thesndmor := sndmor) end.
    change thesndmor with (BinProductOfArrows _ (BP) (BP)
                             (pr1 (# (hat_functor _ Hsort C CC s) (pr1 (# (pr1 ((BCsortToC2 corecsource STLC_coind) : sortToC2)) f) (s ⇒ s))) s)
                             (pr1 (# (hat_functor _ Hsort C CC s) (pr1 (# (pr1 ((BCsortToC2 corecsource STLC_coind) : sortToC2)) f) s)) s)).
    etrans.
    2: { apply pathsinv0, postcompWithBinProductArrow. }
    etrans.
    { apply precompWithBinProductArrow. }
    apply maponpaths_12.
    - etrans.
      2: { rewrite assoc'.
           apply maponpaths, pathsinv0.
           use (CoproductOfArrowsIn _ _ _ _ _ (idpath s)). }
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0, BinCoproductOfArrowsIn2.
    - etrans.
      2: { rewrite assoc'.
           apply maponpaths, pathsinv0.
           use (CoproductOfArrowsIn _ _ _ _ _ (idpath s)). }
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0, BinCoproductOfArrowsIn1.
  Qed.

  Definition IterateInfinite_rec_coalg : sortToC2⟦corecsource, STLC_Functor_Id_H (BCsortToC2 corecsource STLC_coind)⟧
    := _,, IterateInfinite_rec_coalg_data_ok.

  Definition IterateInfinite : sortToC2⟦corecsource, STLC_coind⟧ := pr11 (primitive_corecursion _ (pr2 STLC_coind_FC) IterateInfinite_rec_coalg).

  Definition ChurchInfinity_body_sortToC_data_data (ξ : sortToC) (s : sort) : global_element TC (pr1 (pr1 STLC_coind (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s).
  Proof.
    refine (_ · pr1 (pr1 IterateInfinite (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s).
    refine (_ · pr1 (pr1 (STLC_eta_gen σcoind) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) (s ⇒ s)).
    refine (_ · BinCoproductIn2).
    refine (_ · BinCoproductIn1).
    exact (CoproductIn (idpath _)).
  Defined.

  Definition ChurchInfinity_body_sortToC_data (ξ : sortToC) : global_element TsortToC (pr1 (Church_gen_body_target σcoind) ξ).
  Proof.
    use make_sortToC_mor.
    intro s.
    change (global_element TC (pr1 (pr1 STLC_coind (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s)).
    exact (ChurchInfinity_body_sortToC_data_data ξ s).
  Defined.

  Lemma ChurchInfinity_body_sortToC_data_ok (ξ ξ' : sortToC) (f : sortToC ⟦ξ,ξ'⟧) :
    ChurchInfinity_body_sortToC_data ξ · # (pr1 (Church_gen_body_target σcoind)) f = ChurchInfinity_body_sortToC_data ξ'.
  Proof.
    apply nat_trans_eq; try apply C.
    intros s.
    change (((((CoproductIn (idpath _) · BinCoproductIn1) · BinCoproductIn2) · pr1 (pr1 (STLC_eta_gen σcoind) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) (s ⇒ s))  ·
               pr1 (pr1 IterateInfinite (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s)  · pr1 (#(pr1 (Church_gen_body_target σcoind)) f) s
            = (((CoproductIn (idpath _) · BinCoproductIn1) · BinCoproductIn2) · pr1 (pr1 (STLC_eta_gen σcoind) (ctx_ext (ctx_ext ξ' (s ⇒ s)) s)) (s ⇒ s))  ·
                pr1 (pr1 IterateInfinite (ctx_ext (ctx_ext ξ' (s ⇒ s)) s)) s).
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    { do 3 apply maponpaths.
      assert (aux := nat_trans_ax IterateInfinite _ _ (# (sorted_option_functor sort Hsort C TC BC CC s)
                                                         (# (sorted_option_functor sort Hsort C TC BC CC (s ⇒ s)) f))).
      apply pathsinv0, (nat_trans_eq_weq C _ _ aux).
    }
    etrans.
    { do 3 apply maponpaths.
      exact (sortToC_comp (# (pr1 corecsource)
     (# (sorted_option_functor sort Hsort C TC BC CC s)
        (# (sorted_option_functor sort Hsort C TC BC CC (s ⇒ s)) f))) (pr1 IterateInfinite
       (sorted_option_functor sort Hsort C TC BC CC s
          (sorted_option_functor sort Hsort C TC BC CC (s ⇒ s) ξ'))) s).
    }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    { repeat rewrite assoc'.
      do 2 apply maponpaths.
      apply pathsinv0.
      exact (STLC_eta_gen_natural'_pointwise σcoind _ _ (# (sorted_option_functor sort Hsort C TC BC CC s)
                                                         (# (sorted_option_functor sort Hsort C TC BC CC (s ⇒ s)) f)) (s ⇒ s)).
    }
    repeat rewrite assoc.
    apply cancel_postcomposition.
    etrans.
    { rewrite assoc'.
      apply maponpaths.
      apply BinCoproductIn2Commutes. }
    simpl.
    rewrite assoc.
    etrans.
    { apply cancel_postcomposition.
      apply BinCoproductIn1Commutes. }
    rewrite (id_left(C:=sortToC)).
    apply idpath.
  Qed.

  Definition ChurchInfinity_body_sortToC : global_element TsortToC2 (Church_gen_body_target σcoind).
  Proof.
    use make_global_element_functor_precat.
    - exact ChurchInfinity_body_sortToC_data.
    - exact ChurchInfinity_body_sortToC_data_ok.
  Defined.

  Definition ChurchInfinity_body (ξ : sortToC) (s: sort)
    : global_element TC (STLC_gen_ctx_sort σcoind (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
  Proof.
    exact (pr1 ((pr1 ChurchInfinity_body_sortToC) ξ) s).
  Defined.

  Let out_STLC_coind : sortToC2⟦STLC_Functor_Id_H STLC_coind, STLC_coind⟧
      := inv_from_z_iso (finalcoalgebra_z_iso _ STLC_Functor_Id_H _ (pr2 STLC_coind_FC)).

  Definition IterateInfinite_rec_eq : IterateInfinite = IterateInfinite_rec_coalg
       · # STLC_Functor_Id_H
       (BinCoproductArrow (BCsortToC2 corecsource STLC_coind) IterateInfinite (identity STLC_coind))
       · out_STLC_coind.
  Proof.
    exact (primitive_corecursion_formula_with_inverse _ (pr2 STLC_coind_FC) IterateInfinite_rec_coalg).
  Qed.

  Definition ChurchInfinity_body_sortToC_rec_eq_statement (ξ : sortToC) (s : sort) : UU :=
    ChurchInfinity_body ξ s =
        BinProductArrow BP
          ((((CoproductIn (idpath _) · BinCoproductIn1) · BinCoproductIn2)
              · pr1 (pr1 (STLC_eta_gen σcoind) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) _)
             · CoproductIn (idpath _))
          (ChurchInfinity_body ξ s · CoproductIn (idpath _))
          · pr1 (pr1 (app_map_coind s _) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s.

  Lemma ChurchInfinity_body_sortToC_rec_eq (ξ : sortToC) (s : sort)
    : ChurchInfinity_body_sortToC_rec_eq_statement ξ s.
  Proof.
    assert (aux := toforallpaths _ _ _ (maponpaths pr1 (toforallpaths _ _ _ (maponpaths pr1 IterateInfinite_rec_eq) (ctx_ext (ctx_ext ξ (s ⇒ s)) s))) s).
    red.
    change (ChurchInfinity_body ξ s) with (ChurchInfinity_body_sortToC_data_data ξ s).
    unfold ChurchInfinity_body_sortToC_data_data.
    etrans.
    { apply maponpaths.
      exact aux. }
    clear aux.
    unfold app_map_coind, app_map_gen, STLC_tau_gen.
    change (SigmaMonoid_τ θSTLC σcoind) with (@BinCoproductIn2 _ _ _ (BCsortToC2 _ _) · out_STLC_coind).
    match goal with |[   |- _ =  _ · ?sndmor ] => set (thesndmor := sndmor) end.
    change thesndmor with (CoproductIn (inl (s,, s)) · (BinCoproductIn2 · pr1 (pr1 out_STLC_coind (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s)).
    clear thesndmor.
    match goal with |[   |- _ · ?sndmor = _ ] => set (thesndmor := sndmor) end.
    change thesndmor with (pr1 (pr1 IterateInfinite_rec_coalg (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s ·
                             pr1 (pr1 (# STLC_Functor_Id_H (BinCoproductArrow (BCsortToC2 corecsource STLC_coind)
                                                              IterateInfinite (identity STLC_coind))) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s ·
                             pr1 (pr1 out_STLC_coind (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s).
    clear thesndmor.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    change (pr1 (pr1 IterateInfinite_rec_coalg (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s)
      with (IterateInfinite_rec_coalg_data_data (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
    unfold IterateInfinite_rec_coalg_data_data.
    Opaque IterateInfinite.
    etrans.
    { repeat rewrite assoc'.
      do 5 apply maponpaths.
      etrans.
      { apply maponpaths.
        apply BinCoproductIn2Commutes. }
      match goal with |[   |- _ · ?sndmor = _] => set (thesndmor := sndmor) end.
      change thesndmor with (pr1 (pr1 (# STLC_Functor_H (BinCoproductArrow (BCsortToC2 corecsource STLC_coind)
                                                              IterateInfinite (identity STLC_coind))) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s
                               · BinCoproductIn2(CC:=BC (pr1 (Id (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s)
                                                       (pr1 (pr1 (pr1 STLC_Functor_H STLC_coind) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s))).
      clear thesndmor.
      rewrite assoc.
      apply cancel_postcomposition.
      unfold STLC_Functor_H, MultiSorted_actegorical.MultiSortedSigToFunctor', ContinuityOfMultiSortedSigToFunctor.MultiSortedSigToFunctor'.
      etrans.
      { apply maponpaths.
        apply coproduct_of_functors_sortToC3_mor. }
      refine (CoproductOfArrowsIn _ _ _ _ _ (inl (s,, s))).
    }
    repeat rewrite assoc.
    do 2 apply cancel_postcomposition.
    match goal with |[   |- _ · ?sndmor = _] => set (thesndmor := sndmor) end.
    (* assert (bla : ∏ X,
               pr1 (pr1 (pr1 (ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort C TC (@BP) BC
                                CC (arity sort STLC_Sig (inl (s,, s)))) X)
                      (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s =
                 @BP
                   ((@functor_path_pregroupoid sort C Hsort
                       (λ s0 : sort, CC (s = s0) (Hsort s s0) (λ _ : s = s0, (@pr1 _ _ (pr1 X (ctx_ext (ctx_ext ξ (s ⇒ s)) s))) (s ⇒ s)))) s)
                   ((@functor_path_pregroupoid sort C Hsort
                       (λ s0 : sort, CC (s = s0) (Hsort s s0) (λ _ : s = s0, (@pr1 _ _ (pr1 X (ctx_ext (ctx_ext ξ (s ⇒ s)) s))) s))) s)).
    { intro X. apply idpath. }
    assert (bla1 : ∏ X,
               pr1 (pr1 (pr1 (ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort C TC (@BP) BC
                                CC (arity sort STLC_Sig (inl (s,, s)))) X)
                      (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s =
                 BP(c:=pr1 (hat_functor _ Hsort C CC s ((pr1 (pr1 X (ctx_ext (ctx_ext ξ (s ⇒ s)) s))) (s ⇒ s))) s)
                   (d:=pr1 (hat_functor _ Hsort C CC s ((pr1 (pr1 X (ctx_ext (ctx_ext ξ (s ⇒ s)) s))) s)) s)).
    { intro X. apply idpath. }
    assert (bla2 : ∏ (X Y : sortToC2) (G : sortToC2 ⟦ X, Y ⟧),
               pr1 (pr1 (# (pr1 (ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort C TC (@BP) BC
                                   CC (arity sort STLC_Sig (inl (s,, s))))) G)
                      (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s =
                 BinProductOfArrows _ (BP) (BP) ((pr1 (# (hat_functor _ Hsort C CC s) (pr1 (pr1 G (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) (s ⇒ s))) s))
                   ((pr1 (# (hat_functor _ Hsort C CC s) (pr1 (pr1 G (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s)) s))).
    { intros X Y G. apply idpath. }
    clear bla bla1 bla2.
    set (aux := BinProductOfArrows _ (BP) (BP)
                  (pr1 (# (hat_functor _ Hsort C CC s) (pr1 (pr1 (BinCoproductArrow (BCsortToC2 corecsource STLC_coind) IterateInfinite (identity STLC_coind)) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) (s ⇒ s))) s)
                  (pr1 (# (hat_functor _ Hsort C CC s) (pr1 (pr1 (BinCoproductArrow (BCsortToC2 corecsource STLC_coind) IterateInfinite (identity STLC_coind)) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s)) s)).
    change thesndmor with aux.
    clear thesndmor. *)
    set (aux2 := BinProductOfArrows _ (BP) (BP)
                   (CoproductOfArrows (s=s) C (CC (s=s) (Hsort s s) _) (CC (s=s) (Hsort s s) _) (fun _ => pr1 (pr1 (BinCoproductArrow (BCsortToC2 corecsource STLC_coind) IterateInfinite (identity STLC_coind)) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) (s ⇒ s)))
                   (CoproductOfArrows (s=s) C (CC (s=s) (Hsort s s) _) (CC (s=s) (Hsort s s) _) (fun _ => pr1 (pr1 (BinCoproductArrow (BCsortToC2 corecsource STLC_coind) IterateInfinite (identity STLC_coind)) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s))).
    change thesndmor with aux2.
    clear thesndmor.
    (* clear aux. *)
    etrans.
    { repeat rewrite assoc'. do 4 apply maponpaths.
      apply postcompWithBinProductArrow. }
    clear aux2.
    etrans.
    { repeat rewrite assoc.
      apply precompWithBinProductArrow. }
    apply maponpaths_12.
    - repeat rewrite assoc'.
      do 4 apply maponpaths.
      etrans.
      { apply maponpaths.
        use (CoproductOfArrowsIn _ _ _ _ _ (idpath s)). }
      etrans.
      { rewrite assoc.
        apply cancel_postcomposition.
        match goal with |[   |- _ · ?sndmor = _] => set (thesndmor := sndmor) end.
        change thesndmor with (BinCoproductArrow (BC _ _)
                                 (pr1 (pr1 IterateInfinite (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) (s ⇒ s))
                                 (pr1 (pr1 (identity STLC_coind) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) (s ⇒ s))).
        apply BinCoproductIn2Commutes. }
      apply id_left.
    - repeat rewrite assoc'.
      do 4 apply maponpaths.
      etrans.
      { apply maponpaths.
        use (CoproductOfArrowsIn _ _ _ _ _ (idpath s)). }
      etrans.
      { rewrite assoc.
        apply cancel_postcomposition.
        match goal with |[   |- _ · ?sndmor = _] => set (thesndmor := sndmor) end.
        change thesndmor with (BinCoproductArrow (BC _ _)
                                 (pr1 (pr1 IterateInfinite (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s)
                                 (pr1 (pr1 (identity STLC_coind) (ctx_ext (ctx_ext ξ (s ⇒ s)) s)) s)).
        apply BinCoproductIn1Commutes. }
      apply idpath.
  Qed.

  Transparent IterateInfinite.

  Definition ChurchInfinity_sortToC : global_element TsortToC2
           (functor_compose STLC_coind (projSortToCvariable sort Hsort C (fun s => (s ⇒ s) ⇒ (s ⇒ s))))
      := ChurchInfinity_body_sortToC · (Church_gen_header_sortToC σcoind).

  Definition ChurchInfinity (ξ : sortToC) (s : sort) : global_element TC (STLC_ctx_sort_coind ξ ((s ⇒ s) ⇒ (s ⇒ s))).
  Proof.
    exact (pr1 ((pr1 ChurchInfinity_sortToC) ξ) s).
  Defined.

End Church.

End A.
