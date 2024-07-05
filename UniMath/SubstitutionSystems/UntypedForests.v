(**

Syntax of the forest calculus (see https://arxiv.org/abs/1602.04382 by José Espírito Santo, Ralph Matthes, Luís Pinto)
in pure Curry style (untyped) as a multisorted signature based on the actegorical development.
Thanks to that development, the inductive and the coinductive calculus are exposed in parallel.
The entire development is only done for the base category [HSET] and thus profits from having inhabitants of the objects
and having functions as morphisms.

*)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

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
Require Import UniMath.CategoryTheory.Core.Isos.
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
Require Import UniMath.SubstitutionSystems.SortIndexing.

Local Open Scope cat.

Section Signature.

(** Some notations *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.
Local Notation "'Id'" := (functor_identity _).

(** Sorts are syntactic categories for the untyped calculus *)
Definition sort : UU := stn 3.

Local Definition  Hsort : isofhlevel 3 sort.
Proof.
exact (isofhlevelssnset 1 sort (setproperty (stnset 3))).
Qed.

Local Definition Hsort' : isofhlevel 2 sort := (setproperty (stnset 3)).

(* variables sort *)
Definition sv : sort := make_stn 3 0 (idpath true : 0 < 3).
(* terms sort *)
Definition st : sort := make_stn 3 0 (idpath true : 1 < 3).
(* elimination alternatives sort *)
Definition se : sort := make_stn 3 0 (idpath true : 2 < 3).

Local Definition sortToSet : category := SortIndexing.sortToSet sort Hsort.
Local Definition sortToSetSet : category := SortIndexing.sortToSetSet sort Hsort.
Local Definition sortToSet2 : category := SortIndexing.sortToSet2 sort Hsort.

Definition TsortToSetSet : Terminal sortToSetSet := TsortToCC _ Hsort HSET TerminalHSET.

Let projSortToSet : sort -> sortToSetSet := MultiSortedMonadConstruction_alt.projSortToSet sort Hsort.
Let projSortToSetvariable : (sort → sort) → sortToSet2 := projSortToCvariable sort Hsort HSET.
Let hat_functorSet : sort -> HSET ⟶ sortToSet := MultiSortedMonadConstruction_alt.hat_functorSet sort Hsort.
Let sorted_option_functorSet : sort → functor sortToSet sortToSet := MultiSortedMonadConstruction_alt.sorted_option_functorSet sort Hsort.

Local Definition BCsortToSet : BinCoproducts sortToSet := SortIndexing.BCsortToSet sort Hsort.
Local Definition BPsortToSet : BinProducts sortToSet := SortIndexing.BPsortToSet sort Hsort.

Local Definition TsortToSet : Terminal sortToSet := SortIndexing.TsortToSet sort Hsort.
Local Definition TsortToSet2 : Terminal sortToSet2 := SortIndexing.TsortToSet2 sort Hsort.

Local Definition BPsortToSetSet : BinProducts sortToSetSet := SortIndexing.BPsortToSetSet sort Hsort.

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

Definition UntypedForest_Sig : MultiSortedSig (⟦3⟧%stn).
Proof.
  use (make_MultiSortedSig (stn 3)).
  - apply ((((unit,,isasetunit) + (nat,,isasetnat)) + (nat,, isasetnat))%set).
    - intros H. induction H  as [term_construct | elim_construct].
      + induction term_construct as [abs|sum].
        * exact ((((sv :: []) ,,st) :: []),,st).
        * exact ((functionToList sum (fun _ => ([] ,, se))) ,, st ).
      + exact ((([],,sv) :: ((functionToList elim_construct (fun _ => ([] ,, st))))),, se).
Defined.

(** The canonical functor associated with UntypedForest_Sig **)
Definition UntypedForest_Functor_H : functor sortToSet2 sortToSet2 :=
  MultiSorted_actegorical.MultiSortedSigToFunctor' sort Hsort SET
    TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET UntypedForest_Sig.


(** the functor of which the fixed points are considered *)
Definition UntypedForest_Functor_Id_H : functor sortToSet2 sortToSet2 :=
  SubstitutionSystems.Id_H sortToSet BCsortToSet UntypedForest_Functor_H.

(** the canonical strength associated with UntypedForest_Sig *)
Local Definition θUntypedForest := MultiSortedMonadConstruction_actegorical.MultiSortedSigToStrength' sort Hsort SET
               TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET UntypedForest_Sig.

Definition ctx_ext (ξ : sortToSet) (s : sort) : sortToSet
  := sorted_option_functorSet s ξ.

Definition ctx_equiv (ξ ξ' : sortToSet) : UU :=  ∏ s : sort, (z_iso ((pr1 ξ) s)  ((pr1 ξ') s)).

(** the sigma-monoids for wellfounded and non-wellfounded syntax for UntypedForests *)
Local Definition σind : SigmaMonoid θUntypedForest := MultiSortedEmbeddingIndCoindHSET.σind sort Hsort UntypedForest_Sig.
Local Definition σcoind : SigmaMonoid θUntypedForest := MultiSortedEmbeddingIndCoindHSET.σcoind sort Hsort UntypedForest_Sig.

Section IndAndCoind.

Context (σ : SigmaMonoid θUntypedForest).

Definition UntypedForest_gen : sortToSet2 := SigmaMonoid_carrier θUntypedForest σ.

(** the type of terms in a context of a sort *)
Definition UntypedForest_gen_ctx_sort (ξ : sortToSet) (s : sort) : UU
  := pr1 (pr1 (pr1 UntypedForest_gen ξ) s).

(** variable inclusion for syntax for UntypedForests *)
Definition UntypedForest_eta_gen : sortToSet2⟦Id,UntypedForest_gen⟧ := SigmaMonoid_η θUntypedForest σ.

Definition UntypedForest_eta_gen_natural (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) :
# Id f · pr1 UntypedForest_eta_gen ξ' = pr1 UntypedForest_eta_gen ξ · # (pr1 UntypedForest_gen) f
:= nat_trans_ax (UntypedForest_eta_gen) ξ ξ' f.

Lemma UntypedForest_eta_gen_natural' (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) :
  f · pr1 UntypedForest_eta_gen ξ' = pr1 UntypedForest_eta_gen ξ · # (pr1 UntypedForest_gen) f.
Proof.
  etrans.
  2: { apply UntypedForest_eta_gen_natural. }
  apply idpath.
Qed.

Lemma UntypedForest_eta_gen_natural'_pointwise (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort) :
  pr1 f u · pr1 (pr1 UntypedForest_eta_gen ξ') u = pr1 (pr1 UntypedForest_eta_gen ξ) u · pr1 (# (pr1 UntypedForest_gen) f) u.
Proof.
  apply (nat_trans_eq_weq HSET _ _ (UntypedForest_eta_gen_natural' ξ ξ' f)).
Qed.

Lemma UntypedForest_eta_gen_natural'_ppointwise (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort) (elem : pr1 (pr1 (pr1 ξ) u)) :
  pr1 (pr1 UntypedForest_eta_gen ξ') u (pr1 f u elem) =  pr1 (# (pr1 UntypedForest_gen) f) u (pr1 (pr1 UntypedForest_eta_gen ξ) u elem).
Proof.
  apply (toforallpaths _ _ _ (UntypedForest_eta_gen_natural'_pointwise ξ ξ' f u)).
Qed.

Definition UntypedForest_tau_gen : UntypedForest_Functor_H UntypedForest_gen --> UntypedForest_gen := SigmaMonoid_τ θUntypedForest σ.

Definition app_source_gen (n : nat) : sortToSet2 :=
  ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort UntypedForest_Sig (inr n)) UntypedForest_gen.

Definition app_source_gen_newstyle_zero : sortToSet2 :=
  functor_compose UntypedForest_gen (projSortToSet sv ∙ hat_functorSet st).

Definition app_source_gen_newstyle_nonzero_aux (n : nat) : sortToSet2 :=
   nat_rect (fun _ =>  sortToSet2)
     (functor_compose UntypedForest_gen (projSortToSet se ∙ hat_functorSet st))
     (fun _ IHn => BinProduct_of_functors BPsortToSet
                  (functor_compose UntypedForest_gen (projSortToSet se ∙
hat_functorSet st)) IHn) n.

Definition app_source_gen_newstyle_nonzero (n : nat) : sortToSet2 :=
      BinProduct_of_functors BPsortToSet
        (functor_compose UntypedForest_gen (projSortToSet sv ∙ hat_functorSet st))
        (app_source_gen_newstyle_nonzero_aux n).


Lemma app_source_gen_nonzero_eq (n : nat):
   app_source_gen (S n) = BinProduct_of_functors BPsortToSet
     (functor_compose UntypedForest_gen (projSortToSet sv ∙ hat_functorSet st))
(ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized
sort Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET
CoproductsHSET ((functionToList (S n)  (fun _ => ([] ,, st)),,se)) UntypedForest_gen).
Proof.
   apply idpath.
Qed.

Lemma app_source_gen_newstyle_nonzero_aux_eq (n : nat):
   app_source_gen_newstyle_nonzero_aux n =
ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort
Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET
((functionToList (S n)  (fun _ => ([] ,, st)),,se)) UntypedForest_gen.
Proof.
   induction n.
   - apply idpath.
   - change (app_source_gen_newstyle_nonzero_aux (S n)) with
       (BinProduct_of_functors BPsortToSet
       (functor_compose UntypedForest_gen (projSortToSet se ∙ hat_functorSet st))
       (app_source_gen_newstyle_nonzero_aux n)).
     rewrite IHn.
     apply idpath.
Qed.


Lemma app_source_zero_gen_ok : app_source_gen_newstyle_zero = app_source_gen 0.
Proof.
  apply idpath.
Qed.

Lemma app_source_nonzero_gen_ok (n : nat) : app_source_gen_newstyle_nonzero n = app_source_gen (S n).
Proof.
   unfold app_source_gen_newstyle_nonzero.
   rewrite app_source_gen_newstyle_nonzero_aux_eq.
   apply idpath.
Qed.

Definition app_map_gen (n : nat) : sortToSet2⟦app_source_gen n,UntypedForest_gen⟧.
  Proof.
    exact (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _ , _ )) (inr n) · UntypedForest_tau_gen) .
  Defined.

Definition app_map_gen_natural (n : nat) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    : # (pr1 (app_source_gen n)) f · pr1 (app_map_gen n) ξ' = pr1 (app_map_gen n) ξ · # (pr1 UntypedForest_gen) f
    := nat_trans_ax (app_map_gen n) ξ ξ' f.

Lemma app_map_gen_natural_pointwise (n : nat) (ξ ξ' : sortToSet) (f : sortToSet  ⟦ ξ, ξ' ⟧) (u : sort) :
  pr1 (# (pr1 (app_source_gen n)) f) u · pr1 (pr1 (app_map_gen n) ξ') u =
  pr1 (pr1 (app_map_gen n) ξ) u · pr1 (# (pr1 UntypedForest_gen) f) u.
Proof.
   apply (nat_trans_eq_weq HSET _ _ (app_map_gen_natural n ξ ξ' f)).
Qed.

Lemma app_map_gen_natural_ppointwise (n : nat) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    (u : sort) (elem : pr1 (pr1 (pr1 (app_source_gen n) ξ) u)) :
    pr1 (pr1 (app_map_gen n) ξ') u (pr1 (# (pr1 (app_source_gen n)) f) u elem) =
      pr1 (# (pr1 UntypedForest_gen) f) u (pr1 (pr1 (app_map_gen n) ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ (app_map_gen_natural_pointwise n ξ ξ' f u)).
  Qed.

Definition lam_source_gen_newstyle :  sortToSet2 :=
    functor_compose
      (functor_compose
         (sorted_option_functorSet sv)
         UntypedForest_gen)
      (projSortToSet st ∙ hat_functorSet st).

Definition lam_source_gen : sortToSet2 :=
  ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET
      BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort UntypedForest_Sig (inl (inl tt ))) UntypedForest_gen.

Lemma lam_source_ok : lam_source_gen = lam_source_gen_newstyle.
Proof.
  apply idpath.
Qed.

Definition lam_map_gen : sortToSet2⟦lam_source_gen ,UntypedForest_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (inl (inl tt)) · UntypedForest_tau_gen.

Definition lam_map_gen_natural (ξ ξ' : sortToSet) (f :  sortToSet ⟦ ξ, ξ' ⟧)
  : # (pr1 lam_source_gen) f · pr1 lam_map_gen ξ' = (pr1 lam_map_gen ξ) · # (pr1 UntypedForest_gen) f
  := nat_trans_ax lam_map_gen ξ ξ' f.

Lemma lam_map_gen_natural_pointwise (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort)
    : pr1 (# (pr1 lam_source_gen) f) u · pr1 (pr1 lam_map_gen ξ') u =
        pr1 (pr1 lam_map_gen ξ) u · pr1 (# (pr1 UntypedForest_gen) f) u.
  Proof.
    apply (nat_trans_eq_weq HSET _ _ (lam_map_gen_natural ξ ξ' f)).
  Qed.

Lemma lam_map_gen_natural_ppointwise (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    (u : sort) (elem : pr1 (pr1 (pr1 lam_source_gen ξ) u)) :
    pr1 (pr1 lam_map_gen ξ') u (pr1 (# (pr1 lam_source_gen) f) u elem) =
      pr1 (# (pr1 UntypedForest_gen) f) u (pr1 (pr1 lam_map_gen ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ (lam_map_gen_natural_pointwise ξ ξ' f u)).
Qed.

Definition sum_source_gen (n : nat) : sortToSet2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort UntypedForest_Sig (inl (inr n))) UntypedForest_gen.

Definition sum_source_gen_newstyle_zero : sortToSet2 :=
  functor_compose TsortToSetSet (hat_functorSet st).

Definition sum_source_gen_newstyle_nonzero (n : nat) : sortToSet2 :=
  nat_rect (fun _ =>  sortToSet2)
  (functor_compose UntypedForest_gen (projSortToSet se ∙ hat_functorSet st))
  (fun _ IHn => BinProduct_of_functors BPsortToSet
    (functor_compose UntypedForest_gen (projSortToSet se ∙ hat_functorSet st)) IHn) n.

Lemma sum_source_gen_eq (n : nat):
   sum_source_gen  n =
(ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized
sort Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET
CoproductsHSET ((functionToList n  (fun _ => ([] ,, se)),,st)) UntypedForest_gen).
Proof.
   apply idpath.
Qed.

Lemma sum_source_gen_newstyle_nonzero_eq (n : nat) :
  sum_source_gen_newstyle_nonzero  n  =
(ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized
sort Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET
CoproductsHSET ((functionToList  (S n)  (fun _ => ([] ,, se)),,st)) UntypedForest_gen).
Proof.
  induction n.
  -apply idpath.
  -change (sum_source_gen_newstyle_nonzero (S n))  with
     (BinProduct_of_functors BPsortToSet
       (functor_compose UntypedForest_gen (projSortToSet se ∙ hat_functorSet st))
       (sum_source_gen_newstyle_nonzero  n )).
   rewrite IHn.
   apply idpath.
Qed.

Lemma sum_source_zero_gen_ok : sum_source_gen_newstyle_zero = sum_source_gen 0.
Proof.
   apply idpath.
Qed.

Lemma sum_source_nonzero_gen_ok (n : nat) : sum_source_gen_newstyle_nonzero n = sum_source_gen (S n).
Proof.
  rewrite sum_source_gen_eq.
  rewrite sum_source_gen_newstyle_nonzero_eq.
  apply idpath.
Qed.

Definition sum_map_gen (n : nat) : sortToSet2⟦sum_source_gen n,UntypedForest_gen⟧.
  Proof.
    exact (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _ , _ )) (inl (inr n)) · UntypedForest_tau_gen) .
  Defined.

Definition sum_map_gen_natural (n : nat) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    : # (pr1 (sum_source_gen n)) f · pr1 (sum_map_gen n) ξ' = pr1 (sum_map_gen n) ξ · # (pr1 UntypedForest_gen) f
    := nat_trans_ax (sum_map_gen n) ξ ξ' f.

Lemma sum_map_gen_natural_pointwise (n : nat) (ξ ξ' : sortToSet) (f : sortToSet  ⟦ ξ, ξ' ⟧) (u : sort) :
  pr1 (# (pr1 (sum_source_gen n)) f) u · pr1 (pr1 (sum_map_gen n) ξ') u =
  pr1 (pr1 (sum_map_gen n) ξ) u · pr1 (# (pr1 UntypedForest_gen) f) u.
Proof.
   apply (nat_trans_eq_weq HSET _ _ (sum_map_gen_natural n ξ ξ' f)).
Qed.

Lemma sum_map_gen_natural_ppointwise (n : nat) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    (u : sort) (elem : pr1 (pr1 (pr1 (sum_source_gen n) ξ) u)) :
    pr1 (pr1 (sum_map_gen n) ξ') u (pr1 (# (pr1 (sum_source_gen n)) f) u elem) =
      pr1 (# (pr1 UntypedForest_gen) f) u (pr1 (pr1 (sum_map_gen n) ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ (sum_map_gen_natural_pointwise n ξ ξ' f u)).
  Qed.

Section Church_int.

  (* The goal fo the following section is to define church integers *)

  Definition ChurchZero_gen (ξ : sortToSet) : UntypedForest_gen_ctx_sort ξ st.
  Proof.
    refine (pr1 (pr1 lam_map_gen _) _ _).
    exists (idpath _).
    change (UntypedForest_gen_ctx_sort (ctx_ext ξ sv)  sv).
    refine (pr1 (pr1 lam_map_gen _) _ _).
    exists (idpath _).
    change (UntypedForest_gen_ctx_sort (ctx_ext (ctx_ext ξ  sv) sv) sv).
    simple refine (pr1 (pr1 UntypedForest_eta_gen _) _ _).
    cbn.
    apply ii1.
    exists (idpath _).
    exact tt.
  Defined.

  Definition ChurchOne_gen (ξ : sortToSet) :  UntypedForest_gen_ctx_sort ξ st.
  Proof.
    refine (pr1 (pr1 lam_map_gen _) _ _).
    exists (idpath _).
    refine (pr1 (pr1 lam_map_gen _) _ _).
    exists (idpath _).
    refine (pr1 (pr1 (app_map_gen 1) _) _ _).
    split ; exists (idpath _).
    - change (UntypedForest_gen_ctx_sort (ctx_ext (ctx_ext ξ  sv)  sv)  sv).
      simple refine (pr1 (pr1 UntypedForest_eta_gen _) _ _).
      cbn.
      apply ii2 ; apply ii1.
      exists (idpath _).
      exact tt.
    - change (UntypedForest_gen_ctx_sort (ctx_ext (ctx_ext ξ sv) sv) sv).
      simple refine (pr1 (pr1 UntypedForest_eta_gen _) _ _).
      cbn.
      apply ii1.
      exists (idpath _).
      exact tt.
  Defined.

  Definition Church_gen_body (n : nat) (ξ : sortToSet) : UntypedForest_gen_ctx_sort (ctx_ext (ctx_ext ξ  sv)  sv)  st.
  Proof.
    induction n.
    - simple refine (pr1 (pr1 UntypedForest_eta_gen _) _ _).
      cbn.
      apply ii1.
      exists (idpath _).
      exact tt.
    - refine (pr1 (pr1 (app_map_gen 1) _) _ _).
       split ; exists (idpath _).
       + change (UntypedForest_gen_ctx_sort (ctx_ext (ctx_ext ξ  sv)  sv)  sv).
         simple refine (pr1 (pr1 UntypedForest_eta_gen _) _ _).
         cbn.
         apply ii2.
         apply ii1.
         exists (idpath _).
         exact tt.
       + exact IHn.
  Defined.

  Lemma Church_gen_body_rec_eq (n : nat) (ξ : sortToSet) :
   Church_gen_body (S n) ξ =
      pr1 (pr1 (app_map_gen 1) (ctx_ext (ctx_ext ξ  sv) sv))  st
      ((idpath se,,
        pr1 (pr1 UntypedForest_eta_gen (ctx_ext (ctx_ext ξ  sv) sv)) sv
        (inr (inl (idpath sv,, tt)) : pr1 (pr1 (Id (ctx_ext (ctx_ext ξ  sv) sv))
              sv))),,
        idpath se,, Church_gen_body n  ξ).
    Proof.
      apply idpath.
    Qed.

    Definition  Church_gen_header (ξ : sortToSet) :
      UntypedForest_gen_ctx_sort (ctx_ext (ctx_ext ξ  sv) sv) st -> UntypedForest_gen_ctx_sort ξ st.
      Proof.
        intro body.
        refine (pr1 (pr1 lam_map_gen _) _ _).
        exists (idpath _).
        refine (pr1 (pr1 lam_map_gen _) _ _).
        exists (idpath _).
        exact body.
      Defined.

    Definition Church_gen (n : nat) (ξ  : sortToSet) : UntypedForest_gen_ctx_sort ξ st := Church_gen_header ξ (Church_gen_body n ξ).


End Church_int.

End IndAndCoind.

Definition UntypedForest_ctx_sort_ind (ξ : sortToSet) (s : sort) : UU := UntypedForest_gen_ctx_sort σind ξ s.

Definition UntypedForest_ctx_sort_coind (ξ : sortToSet) (s : sort) : UU := UntypedForest_gen_ctx_sort σcoind ξ s.

Definition UntypedForest_ind : sortToSet2 := UntypedForest_gen σind.
Definition UntypedForest_coind : sortToSet2 := UntypedForest_gen σcoind.

Definition UntypedForest_eta_ind : sortToSet2⟦Id,UntypedForest_ind⟧ := UntypedForest_eta_gen σind.
Definition UntypedForest_eta_coind : sortToSet2⟦Id,UntypedForest_coind⟧ := UntypedForest_eta_gen σcoind.

Definition UntypedForest_tau_ind : UntypedForest_Functor_H UntypedForest_ind --> UntypedForest_ind  := SigmaMonoid_τ θUntypedForest σind.
Definition UntypedForest_tau_coind : UntypedForest_Functor_H UntypedForest_coind --> UntypedForest_coind  := SigmaMonoid_τ θUntypedForest σcoind.

Definition app_source_ind (n : nat) : sortToSet2 := app_source_gen σind n.
Definition app_map_ind (n : nat)  : sortToSet2⟦app_source_ind n, UntypedForest_ind⟧ := app_map_gen σind n.
Definition lam_source_ind : sortToSet2 := lam_source_gen σind.
Definition lam_map_ind : sortToSet2⟦lam_source_ind, UntypedForest_ind⟧ := lam_map_gen σind.
Definition sum_source_ind (n : nat) : sortToSet2 := sum_source_gen σind n.
Definition sum_map_ind (n : nat) : sortToSet2⟦sum_source_ind n, UntypedForest_ind⟧ := sum_map_gen σind n.

Definition app_source_coind (n : nat) : sortToSet2 := app_source_gen σcoind n.
Definition app_map_coind  (n : nat) : sortToSet2⟦app_source_coind n, UntypedForest_coind⟧ := app_map_gen σcoind n.
Definition lam_source_coind : sortToSet2 := lam_source_gen σcoind.
Definition lam_map_coind : sortToSet2⟦lam_source_coind, UntypedForest_coind⟧ := lam_map_gen σcoind.
Definition sum_source_coind (n : nat) : sortToSet2 := sum_source_gen σcoind n.
Definition sum_map_coind (n : nat) : sortToSet2⟦sum_source_coind n, UntypedForest_coind⟧ := sum_map_gen σcoind n.

(** get a handle on the recursion principles *)

(** the initial algebra *)
Definition UntypedForest_ind_IA : Initial (FunctorAlg UntypedForest_Functor_Id_H)
  := DatatypeOfMultisortedBindingSig_CAT sort Hsort SET TerminalHSET InitialHSET BinProductsHSET
       BinCoproductsHSET (fun s s' => ProductsHSET (s=s')) CoproductsHSET (EsortToSet2 sort Hsort)
       (ColimsHSET_of_shape nat_graph) UntypedForest_Sig.
(** notice that this is only the initial algebra and not the initial sigma monoid *)

(** the final coalgebra *)
Definition UntypedForest_coind_FC : Terminal (CoAlg_category UntypedForest_Functor_Id_H)
  := coindCodatatypeOfMultisortedBindingSig_CAT sort Hsort HSET TerminalHSET
         BinProductsHSET BinCoproductsHSET CoproductsHSET (LimsHSET_of_shape conat_graph)
         I_coproduct_distribute_over_omega_limits_HSET UntypedForest_Sig is_univalent_HSET.

End Signature.
