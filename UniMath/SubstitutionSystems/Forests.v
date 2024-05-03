(**

Syntax of the forest calculus (see https://arxiv.org/abs/1602.04382 by José Espírito Santo, Ralph Matthes, Luís Pinto)
)  in fully typed format as a multisorted signature based on the actegorical development.
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

Context (atom : hSet) (otype : hSet) (atotype : atom -> otype) (arr : otype → otype → otype) (plus : nat -> atom -> atom).

Local Notation "s ⇒ t" := (arr s t).
Local Notation "0" := (plus nil).

(** same as "sorts" for the untyped calculus, which are syntactic categories. See UntypedForests.v *)
Definition syntcat : UU := stn 3.

(* variables category *)
Definition sv : syntcat := make_stn 3 0 (idpath true : 0 < 3).
(* terms category *)
Definition st : syntcat := make_stn 3 0 (idpath true : 1 < 3).
(* elimination alternatives category *)
Definition se : syntcat := make_stn 3 0 (idpath true : 2 < 3).

(** A sort is a type ('object type', i.e types for the forests, not types from coq) and a syntactic category *)
Definition sort : UU := otype × syntcat.

Local Definition Hotype : isofhlevel 3 otype := MultiSortedBindingSig.STLC_Hsort otype.

Local Definition Hsyntcat : isofhlevel 3 syntcat := isofhlevelssnset 1 syntcat (setproperty (stnset 3)).

Local Definition Hsort : isofhlevel 3 sort := isofhleveldirprod 3 otype syntcat Hotype Hsyntcat.

Let sortToSet : category := SortIndexing.sortToSet sort Hsort.
Let sortToSetSet : category := SortIndexing.sortToSetSet sort Hsort.
Let sortToSet2 : category := SortIndexing.sortToSet2 sort Hsort.

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

Definition otype_list_set : isaset (list otype).
Proof.
  apply isofhlevellist.
  apply otype.
Qed.

Definition otype_list_as_set := (list otype ,, otype_list_set).

Definition wrap_sig_app : otype -> (list sort × sort).
Proof.
  intros t.
  exact ([] ,, (t ,, st)).
Qed.

Definition sig_app_var_otype : atom ->  list otype -> otype.
Proof.
  intros p l.
  exact (foldr arr (atotype p) l).
Qed.

Definition wrap_sig_sum (n : nat) (p : atom) : list(list sort × sort).
Proof.
    use tpair.
    - exact n.
    - apply weqvecfun.
      intro i. apply ( [] ,, (atotype p ,, se) ).
Defined.

Definition Forest_Sig : MultiSortedSig sort.
Proof.
  use (make_MultiSortedSig sort ).
  - apply ((( (otype × otype) + (atom × (nat ,, isasetnat )) ) + (otype_list_as_set × atom))%set).
    - intros H. induction H  as [term_construct | elim_construct].
      + induction term_construct as [abs|sum].
        * induction abs as [a b].
          exact ((((cons (a ,, sv)  []) ,, (b ,, st)) :: []) ,,  ((a ⇒ b),, st) ).
        * induction sum as [p n].
          exact ( (wrap_sig_sum  n  p) ,, ((atotype p)  ,, st)).
      + induction elim_construct as [B p].
        exact (( ([],, ( sig_app_var_otype p B,, sv)) :: (map wrap_sig_app B))  ,, ((atotype p) ,, se)).
Defined.

(** The canonical functor associated with Forest_Sig **)
Definition Forest_Functor_H : functor sortToSet2 sortToSet2 :=
  MultiSorted_actegorical.MultiSortedSigToFunctor' sort Hsort SET
    TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET Forest_Sig.


(** the functor of which the fixed points are considered *)
Definition Forest_Functor_Id_H : functor sortToSet2 sortToSet2 :=
  SubstitutionSystems.Id_H sortToSet BCsortToSet Forest_Functor_H.

(** the canonical strength associated with Forest_Sig *)
Let θForest := MultiSortedMonadConstruction_actegorical.MultiSortedSigToStrength' sort Hsort SET
               TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET Forest_Sig.

Definition ctx_ext (ξ : sortToSet) (s : sort) : sortToSet
  := sorted_option_functorSet s ξ.

(** the sigma-monoids for wellfounded and non-wellfounded syntax for Forests *)
Let σind : SigmaMonoid θForest := MultiSortedEmbeddingIndCoindHSET.σind sort Hsort Forest_Sig.
Let σcoind : SigmaMonoid θForest := MultiSortedEmbeddingIndCoindHSET.σcoind sort Hsort Forest_Sig.

Section IndAndCoind.

Context (σ : SigmaMonoid θForest).

Definition Forest_gen : sortToSet2 := SigmaMonoid_carrier θForest σ.

(** the type of terms in a context of a sort *)
Definition Forest_gen_ctx_sort (ξ : sortToSet) (s : sort) : UU
  := pr1 (pr1 (pr1 Forest_gen ξ) s).

(** variable inclusion for syntax for forests *)
Definition Forest_eta_gen : sortToSet2⟦Id,Forest_gen⟧ := SigmaMonoid_η θForest σ.

Definition Forest_eta_gen_natural (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) :
# Id f · pr1 Forest_eta_gen ξ' = pr1 Forest_eta_gen ξ · # (pr1 Forest_gen) f
:= nat_trans_ax (Forest_eta_gen) ξ ξ' f.

Lemma Forest_eta_gen_natural' (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) :
  f · pr1 Forest_eta_gen ξ' = pr1 Forest_eta_gen ξ · # (pr1 Forest_gen) f.
Proof.
  etrans.
  2: { apply Forest_eta_gen_natural. }
  apply idpath.
Qed.

Lemma Forest_eta_gen_natural'_pointwise (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort) :
  pr1 f u · pr1 (pr1 Forest_eta_gen ξ') u = pr1 (pr1 Forest_eta_gen ξ) u · pr1 (# (pr1 Forest_gen) f) u.
Proof.
  apply (nat_trans_eq_weq HSET _ _ (Forest_eta_gen_natural' ξ ξ' f)).
Qed.

Lemma Forest_eta_gen_natural'_ppointwise (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort) (elem : pr1 (pr1 (pr1 ξ) u)) :
  pr1 (pr1 Forest_eta_gen ξ') u (pr1 f u elem) =  pr1 (# (pr1 Forest_gen) f) u (pr1 (pr1 Forest_eta_gen ξ) u elem).
Proof.
  apply (toforallpaths _ _ _ (Forest_eta_gen_natural'_pointwise ξ ξ' f u)).
Qed.

Definition Forest_tau_gen : Forest_Functor_H Forest_gen --> Forest_gen := SigmaMonoid_τ θForest σ.

Definition app_source_gen (l : list otype) (p : atom) : sortToSet2 :=
  ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort Forest_Sig (inr (l ,,  p))) Forest_gen.

Definition lam_source_gen (a b : otype) : sortToSet2 :=
  ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET
      BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort Forest_Sig (inl (inl (a ,, b) ))) Forest_gen.

Definition lam_map_gen (a b : otype) : sortToSet2⟦lam_source_gen a b,Forest_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (inl (inl (a ,, b) )) · Forest_tau_gen.

Definition lam_map_gen_natural (a b : otype) (ξ ξ' : sortToSet) (f :  sortToSet ⟦ ξ, ξ' ⟧)
  : # (pr1 (lam_source_gen a b)) f · pr1 (lam_map_gen a b) ξ' = (pr1 (lam_map_gen a b) ξ) · # (pr1 Forest_gen) f
  := nat_trans_ax (lam_map_gen a b) ξ ξ' f.

Lemma lam_map_gen_natural_pointwise (a b : otype) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort)
    : pr1 (# (pr1 (lam_source_gen a b)) f) u · pr1 (pr1 (lam_map_gen a b) ξ') u =
        pr1 (pr1 (lam_map_gen a b) ξ) u · pr1 (# (pr1 Forest_gen) f) u.
  Proof.
    apply (nat_trans_eq_weq HSET _ _ ((lam_map_gen_natural a b) ξ ξ' f)).
  Qed.

Lemma lam_map_gen_natural_ppointwise (a b : otype) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    (u : sort) (elem : pr1 (pr1 (pr1 (lam_source_gen a b) ξ) u)) :
    pr1 (pr1 (lam_map_gen a b) ξ') u (pr1 (# (pr1 (lam_source_gen a b)) f) u elem) =
      pr1 (# (pr1 Forest_gen) f) u (pr1 (pr1 (lam_map_gen a b) ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ ((lam_map_gen_natural_pointwise a b )ξ ξ' f u)).
Qed.

Definition sum_source_gen (p : atom) (n : nat) : sortToSet2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort Forest_Sig (inl (inr (p ,, n)))) Forest_gen.

End IndAndCoind.

End Signature.
