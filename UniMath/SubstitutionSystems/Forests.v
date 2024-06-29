(**

Syntax of the forest calculus (see https://arxiv.org/abs/1602.04382 by José Espírito Santo, Ralph Matthes, Luís Pinto)
in fully typed format as a multisorted signature based on the actegorical development.
Thanks to that development, the inductive and the coinductive calculus are exposed in parallel.
The entire development is only done for the base category [HSET] and thus profits from having inhabitants of the objects
and having functions as morphisms.

*)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Notations.

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
Require Import UniMath.CategoryTheory.Core.Isos.
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
Require  UniMath.SubstitutionSystems.UntypedForests.

Local Open Scope cat.

Section Signature.

(** Some notations *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.
Local Notation "'Id'" := (functor_identity _).

Context (atom : hSet) (otype : hSet) (atotype : atom -> otype) (arr : otype → otype → otype).

Local Notation "s ⇒ t" := (arr s t).

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

Local Definition Hotype' : isofhlevel 2 otype := pr2 otype .

Local Definition Hsyntcat' : isofhlevel 2 syntcat := (setproperty (stnset 3)).

Local Definition Hsort' : isofhlevel 2 sort :=  isofhleveldirprod 2 otype syntcat Hotype' Hsyntcat'.

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

Lemma  wrap_sig_app : otype -> (list sort × sort).
Proof.
  intros t.
  exact ([] ,, (t ,, st)).
Defined.

Lemma  sig_app_var_otype : atom ->  list otype -> otype.
Proof.
  intros p l.
  exact (foldr arr (atotype p) l).
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
          exact ( (functionToList n (fun _ => ([] ,, (atotype p ,, se))))  ,, ((atotype p)  ,, st)).
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

Definition ctx_equiv (ξ ξ' : sortToSet) : UU :=  ∏ s : sort, (z_iso ((pr1 ξ) s)  ((pr1 ξ') s)).

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

Definition app_map_gen (l : list otype) (p : atom) : sortToSet2⟦app_source_gen l p, Forest_gen⟧.
Proof.
  exact (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _ , _ )) (inr (l ,, p)) · Forest_tau_gen).
Defined.

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

Definition sum_map_gen (p : atom) (n : nat) : sortToSet2⟦sum_source_gen p n, Forest_gen⟧.
Proof.
  exact (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _ , _ )) (inl (inr (p ,, n))) · Forest_tau_gen).
Defined.

Section Church_int.

  (* The goal fo the following section is to define Church integers. We view a as an atom, but use a' for the definitions (since an atom is a type) *)

  Context (a : atom).

  Definition a' : otype := atotype a.

  Definition ChurchZero_gen (ξ : sortToSet) : Forest_gen_ctx_sort ξ ((((a' ⇒  a') ⇒ (a' ⇒ a')) ,, st)).
  Proof.
    refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
    exists (idpath _).
    change (Forest_gen_ctx_sort (ctx_ext ξ ((a' ⇒ a') ,, sv )) ((a' ⇒ a') ,, sv)).
    refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
    exists (idpath _).
    change (Forest_gen_ctx_sort (ctx_ext (ctx_ext ξ ((a' ⇒ a') ,, sv)) (a' ,, sv)) (a' ,, sv)).
    simple refine (pr1 (pr1 Forest_eta_gen _) _ _).
    cbn.
    apply ii1.
    exists (idpath _).
    exact tt.
  Defined.

  Definition ChurchOne_gen (ξ : sortToSet) :  Forest_gen_ctx_sort ξ ((((a' ⇒  a') ⇒ (a' ⇒ a')) ,, st)).
  Proof.
    refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
    exists (idpath _).
    refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
    exists (idpath _).
    refine (pr1 (pr1 (app_map_gen (a' :: nil)  a) _) _ _).
    split ; exists (idpath _).
    - change (Forest_gen_ctx_sort (ctx_ext (ctx_ext ξ ((a' ⇒ a') ,, sv)) (a' ,, sv)) ((a' ⇒ a') ,, sv)).
      simple refine (pr1 (pr1 Forest_eta_gen _) _ _).
      cbn.
      apply ii2 ; apply ii1.
      exists (idpath _).
      exact tt.
    - change (Forest_gen_ctx_sort (ctx_ext (ctx_ext ξ ((a' ⇒ a') ,, sv)) (a' ,, sv)) (a' ,, sv)).
      simple refine (pr1 (pr1 Forest_eta_gen _) _ _).
      cbn.
      apply ii1.
      exists (idpath _).
      exact tt.
  Defined.

  Definition Church_gen_body (n : nat) (ξ : sortToSet) : Forest_gen_ctx_sort (ctx_ext (ctx_ext ξ ((a' ⇒ a') ,, sv)) (a' ,, sv)) (a' ,, st).
  Proof.
    induction n.
    - simple refine (pr1 (pr1 Forest_eta_gen _) _ _).
      cbn.
      apply ii1.
      exists (idpath _).
      exact tt.
    - refine (pr1 (pr1 (app_map_gen (a' :: [] )  _) _) _ _).
       split ; exists (idpath _).
       + change (Forest_gen_ctx_sort (ctx_ext (ctx_ext ξ ((a' ⇒ a') ,, sv)) (a' ,, sv)) ((a' ⇒ a') ,, sv)).
         simple refine (pr1 (pr1 Forest_eta_gen _) _ _).
         cbn.
         apply ii2.
         apply ii1.
         exists (idpath _).
         exact tt.
       + exact IHn.
  Defined.

  Lemma Church_gen_body_rec_eq (n : nat) (ξ : sortToSet) :
   Church_gen_body (S n) ξ =
      pr1 (pr1 (app_map_gen (a' :: []) a) (ctx_ext (ctx_ext ξ ((a' ⇒ a'),, sv)) (a',, sv))) (a',, st)
      ((idpath (atotype a,, se),,
        pr1 (pr1 Forest_eta_gen (ctx_ext (ctx_ext ξ ((a' ⇒ a'),, sv)) (a',, sv))) ((a' ⇒ a'),, sv)
        (inr (inl (idpath ((a' ⇒ a'),, sv),, tt)) : pr1 (pr1 (Id (ctx_ext (ctx_ext ξ ((a' ⇒ a'),, sv)) (a',, sv)))
             ((a' ⇒ a'),, sv)))),,
        idpath (atotype a,, se),, Church_gen_body n  ξ).
    Proof.
      apply idpath.
    Qed.

    Definition  Church_gen_header (ξ : sortToSet) :
      Forest_gen_ctx_sort (ctx_ext (ctx_ext ξ ((a' ⇒ a') ,, sv )) (a' ,, sv)) (a' ,, st) -> Forest_gen_ctx_sort ξ (((a' ⇒ a') ⇒ (a' ⇒ a')) ,, st ).
      Proof.
        intro body.
        refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
        exists (idpath _).
        refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
        exists (idpath _).
        exact body.
      Defined.

    Definition Church_gen (n : nat) (ξ  : sortToSet) : Forest_gen_ctx_sort ξ (( (a' ⇒ a') ⇒ (a' ⇒ a')) ,,st ) := Church_gen_header ξ (Church_gen_body n ξ).


End Church_int.

End IndAndCoind.

Definition Forest_ctx_sort_ind (ξ : sortToSet) (s : sort) : UU := Forest_gen_ctx_sort σind ξ s.

Definition Forest_ctx_sort_coind (ξ : sortToSet) (s : sort) : UU := Forest_gen_ctx_sort σcoind ξ s.

Definition Forest_ind : sortToSet2 := Forest_gen σind.
Definition Forest_coind : sortToSet2 := Forest_gen σcoind.

Definition Forest_eta_ind : sortToSet2⟦Id,Forest_ind⟧ := Forest_eta_gen σind.
Definition Forest_eta_coind : sortToSet2⟦Id, Forest_coind⟧ := Forest_eta_gen σcoind.

Definition Forest_tau_ind : Forest_Functor_H Forest_ind --> Forest_ind  := SigmaMonoid_τ θForest σind.
Definition Forest_tau_coind : Forest_Functor_H Forest_coind --> Forest_coind  := SigmaMonoid_τ θForest σcoind.

Definition app_source_ind (l : list  otype) (p : atom) : sortToSet2 := app_source_gen σind l p.
Definition app_map_ind (l : list otype) (p : atom)  : sortToSet2⟦app_source_ind l p, Forest_ind⟧ := app_map_gen σind l p.
Definition lam_source_ind (s t : otype) : sortToSet2 := lam_source_gen σind s t.
Definition lam_map_ind (s t : otype) : sortToSet2⟦lam_source_ind s t, Forest_ind⟧ := lam_map_gen σind s t.
Definition sum_source_ind (p : atom) (n : nat) : sortToSet2 := sum_source_gen σind p n.
Definition sum_map_ind (p : atom) (n : nat) : sortToSet2⟦sum_source_ind p n, Forest_ind⟧  := sum_map_gen σind p n.



Definition app_source_coind (l :  list otype) (p : atom) : sortToSet2 := app_source_gen σcoind l p.
Definition app_map_coind  (l : list otype) (p : atom) : sortToSet2⟦app_source_coind l p, Forest_coind⟧ := app_map_gen σcoind l p.
Definition lam_source_coind (s t : otype) : sortToSet2 := lam_source_gen σcoind s t.
Definition lam_map_coind (s t : otype) : sortToSet2⟦lam_source_coind s t, Forest_coind⟧ := lam_map_gen σcoind s t.
Definition sum_source_coind (p : atom) (n : nat) : sortToSet2 := sum_source_gen σcoind p n.
Definition sum_map_coind (p : atom) (n : nat) : sortToSet2⟦sum_source_coind p n, Forest_coind⟧  := sum_map_gen σcoind p n.


(** get a handle on the recursion principles *)

(** the initial algebra *)
Definition Forest_ind_IA : Initial (FunctorAlg Forest_Functor_Id_H)
  := DatatypeOfMultisortedBindingSig_CAT sort Hsort SET TerminalHSET InitialHSET BinProductsHSET
       BinCoproductsHSET (fun s s' => ProductsHSET (s=s')) CoproductsHSET (EsortToSet2 sort Hsort)
       (ColimsHSET_of_shape nat_graph) Forest_Sig.
(** notice that this is only the initial algebra and not the initial sigma monoid *)

(** the final coalgebra *)
Definition Forest_coind_FC : Terminal (CoAlg_category Forest_Functor_Id_H)
  := coindCodatatypeOfMultisortedBindingSig_CAT sort Hsort HSET TerminalHSET
         BinProductsHSET BinCoproductsHSET CoproductsHSET (LimsHSET_of_shape conat_graph)
         I_coproduct_distribute_over_omega_limits_HSET Forest_Sig is_univalent_HSET.

Section Typing.

Context (cl : UntypedForests.sort -> syntcat).

Coercion cl :  UntypedForests.sort >-> syntcat.


(** Transforms a "typed context" into an "untyped context" *)
Definition Down_Context (ξ : sortToSet) : UntypedForests.sortToSet.
Proof.
  apply functor_path_pregroupoid.
  intro s.
  refine (CoproductsHSET otype (pr2 otype) (fun a => _)).
  apply (pr1 ξ).
  simpl.
  exact (a,, s ).
Defined.

(** Shows homogeneity for down context on morphisms *)
Definition Down_Context_on_mor  {ξ ξ' : sortToSet}  (η : sortToSet⟦ξ, ξ'⟧)
  : UntypedForests.sortToSet⟦Down_Context ξ, Down_Context ξ'⟧.
Proof.
  apply nat_trans_functor_path_pregroupoid.
  intros s.
  use CoproductOfArrows.
  intro c.
  simpl.
  apply η.
Defined.

Definition Down_context_functor_data : functor_data sortToSet UntypedForests.sortToSet.
Proof.
  use make_functor_data.
  - apply Down_Context.
  - intros a b f; exact (Down_Context_on_mor f).
Defined.

Lemma is_functor_down_context : is_functor Down_context_functor_data.
Proof.
  split ; red.
  - intro ξ.
    apply nat_trans_eq.
    { apply has_homsets_HSET. }
    intro x.
    apply funextfun.
    intro elem.
    apply idpath.
  - intros a b c f g.
    apply nat_trans_eq.
    { apply has_homsets_HSET. }
    intro x.
    apply funextfun.
    intro elem.
    apply idpath.
Qed.

Definition Down_Context_functor : functor sortToSet UntypedForests.sortToSet
  := (Down_context_functor_data ,, is_functor_down_context).

Let option_fun_summand2 := option_fun_summand sort Hsort HSET TerminalHSET CoproductsHSET.

Let option_fun_summand2_u := option_fun_summand UntypedForests.sort UntypedForests.Hsort HSET TerminalHSET CoproductsHSET.

Definition Down_works_option_fun_summand_to (s : sort) (s0 : UntypedForests.sort) :
  SET ⟦ pr1 (Down_Context (option_fun_summand2 s)) s0, pr1 (option_fun_summand2_u (pr2 s)) s0 ⟧.
Proof.
  unfold Down_Context.
  unfold functor_path_pregroupoid.
  simpl.
  intro x.
  destruct x as [a [p q]].
  rewrite <- p.
  use tpair.
  - apply idpath.
  - exact q.
Defined.

Definition Down_works_option_fun_summand_from (s : sort) (s0 : UntypedForests.sort) :
  SET ⟦ pr1 (option_fun_summand2_u (pr2 s)) s0, pr1 (Down_Context (option_fun_summand2 s)) s0 ⟧.
Proof.
  simpl.
  intro x.
  destruct x as [p q].
  exists (pr1 s).
  rewrite  p.
  use tpair.
  - apply idpath.
  - exact q.
Defined.

Lemma Down_works_option_fun_summand_aux (s : sort) (s0 : UntypedForests.sort) :
  is_inverse_in_precat (Down_works_option_fun_summand_to s s0)
                       (Down_works_option_fun_summand_from s s0).
Proof.
  split.
  - apply funextfun.
    intro x.
    destruct x as [a [p q]].
    cbn.
    use total2_paths_f.
    + simpl.
      rewrite <- p.
      apply idpath.
    + use total2_paths_f.
      * apply Hsort'.
      * apply isapropunit.
  - apply funextfun.
    intro x.
    destruct x as [p q].
    cbn.
    use total2_paths_f.
    + apply (setproperty (stnset 3)).
    + apply isapropunit.
Qed.

Definition Down_works_option_fun_summand (s : sort) :
  UntypedForests.ctx_equiv
    (Down_Context (option_fun_summand2 s))
    (option_fun_summand2_u (pr2 s)).
Proof.
  red.
  intros s0.
  use make_z_iso.
  - apply Down_works_option_fun_summand_to.
  - apply Down_works_option_fun_summand_from.
  - apply Down_works_option_fun_summand_aux.
Defined.

Definition Down_works_with_ext_to (ξ : sortToSet) (s : sort) (s0 : UntypedForests.sort) :
  SET ⟦ pr1 (Down_Context (ctx_ext ξ s)) s0, pr1 (UntypedForests.ctx_ext (Down_Context ξ) (pr2 s)) s0 ⟧.
Proof.
  intro x.
  destruct x as [a x'].
  simpl in x'.
  destruct x' as [option | base].
  - apply ii1.
    exact (pr1 (Down_works_option_fun_summand s s0) (a ,, option)).
  - apply ii2.
    simpl.
    exists a.
    exact base.
Defined.

Definition Down_works_with_ext_from (ξ : sortToSet) (s : sort) (s0 : UntypedForests.sort) :
  SET ⟦ pr1 (UntypedForests.ctx_ext (Down_Context ξ) (pr2 s)) s0, pr1 (Down_Context (ctx_ext ξ s)) s0 ⟧.
Proof.
  intro x.
  destruct x as [option | base].
  - simpl in option.
    simpl.
    exists (pr1 s).
    apply ii1.
    set (auxarg := pr1 (pr1 (option_fun_summand2_u (pr2 s)) s0)).
    simpl in auxarg.
    set (aux := pr12 (Down_works_option_fun_summand s s0) option).
    simpl in aux.
    destruct aux as [a [p q]].
    use tpair.
    + rewrite <- p. simpl. apply idpath.
    + exact q.
  - simpl in base.
    destruct base as [a  t].
    simpl.
    exists a.
    apply ii2.
    exact t.
Defined.

Lemma Down_works_with_ext_aux (ξ : sortToSet) (s : sort) (s0 : UntypedForests.sort) :
  is_inverse_in_precat (Down_works_with_ext_to ξ s s0) (Down_works_with_ext_from ξ s s0).
Proof.
  split.
  - apply funextfun.
    intro y.
    simpl.
    destruct y as [ot b].
    destruct b as [f1 | f2].
    + destruct f1 as [p q].
      use total2_paths_f.
      * cbn.
        apply (maponpaths pr1) in p.
        exact (!p).
      * induction p.
        apply idpath.
    + cbn. apply idpath.
  - apply funextfun.
    intro x.
    destruct x as [p | q] ; cbn.
    + apply maponpaths.
      use total2_paths_f.
      * apply UntypedForests.Hsort'.
      * apply isProofIrrelevantUnit.
    + apply idpath.
Qed.

Lemma Down_works_with_ext (ξ : sortToSet) (s : sort) :
  UntypedForests.ctx_equiv
    (Down_Context (ctx_ext ξ s))
    (UntypedForests.ctx_ext (Down_Context ξ) (pr2 s)).
Proof.
   red.
   intros s0.
   use make_z_iso.
   - apply Down_works_with_ext_to.
   - apply Down_works_with_ext_from.
   - apply Down_works_with_ext_aux.
Defined.

Definition Carrier_detype_data_ind : functor_data sortToSet sortToSet.
Proof.
  use make_functor_data.
  - intros ξ.
    apply functor_path_pregroupoid.
    intros s.
    exact (pr1 (pr1 UntypedForests.UntypedForest_ind (Down_Context ξ)) (pr2 s)).
  - intros ξ ξ' η.
    apply nat_trans_functor_path_pregroupoid.
    intros s.
    change (pr1 (pr1 (pr1 UntypedForests.UntypedForest_ind (Down_Context ξ)) (pr2 s)) ->
            pr1 (pr1 (pr1 UntypedForests.UntypedForest_ind (Down_Context ξ')) (pr2 s))).
    set (aux := # (pr1 UntypedForests.UntypedForest_ind) (Down_Context_on_mor η)).
    exact (pr1 aux (pr2 s)).
Defined.

Lemma Carrier_detype_data_ind_is_functor : is_functor Carrier_detype_data_ind.
Proof.
  split; red.
  - intro ξ.
    apply nat_trans_eq.
    { exact has_homsets_HSET. }
    intro x.
    apply funextfun.
    intro elem.
    unfold functor_on_morphisms.
    unfold Carrier_detype_data_ind.
    unfold make_functor_data.
    unfold nat_trans_functor_path_pregroupoid.
    unfold make_nat_trans.
    unfold nat_trans_data_from_nat_trans_funclass.
    unfold pr1. unfold pr2.
    change (Down_Context_on_mor (identity ξ)) with (# Down_Context_functor (identity ξ)).
    rewrite (functor_id).
    rewrite (functor_id UntypedForests.UntypedForest_ind).
    apply idpath.
  - intros ξ1 ξ2 ξ3 f g.
    apply nat_trans_eq.
    { exact has_homsets_HSET. }
    intro x.
    apply funextfun.
    intro elem.
    unfold functor_on_morphisms.
    unfold Carrier_detype_data_ind.
    unfold make_functor_data.
    unfold nat_trans_functor_path_pregroupoid.
    unfold make_nat_trans.
    unfold nat_trans_data_from_nat_trans_funclass.
    unfold pr1. unfold pr2.
    change (Down_Context_on_mor (f · g)) with (# Down_Context_functor (f · g)).
    rewrite functor_comp.
    rewrite (functor_comp UntypedForests.UntypedForest_ind).
    apply idpath.
Qed.

Definition Carrier_detype_ind : sortToSet2 :=
  Carrier_detype_data_ind ,, Carrier_detype_data_ind_is_functor.

Definition Detype_ind_alg_data
  : nat_trans_data (pr1 (Forest_Functor_Id_H Carrier_detype_ind)) (pr1 Carrier_detype_ind).
Proof.
  intro ξ.
  apply nat_trans_functor_path_pregroupoid.
  intro s.
  use BinCoproductArrow.
  - change (SET⟦ pr1 ξ s, pr1 (pr1 Carrier_detype_ind ξ) s ⟧).
    intro x.
    refine (pr1 (pr1 UntypedForests.UntypedForest_eta_ind _) _ _).
    exists (pr1 s).
    exact x.
  - use CoproductArrow.
    intro op.
    change (SET⟦
                pr1 (pr1
                       (ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort
                          Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET
                          CoproductsHSET
                          (arity sort Forest_Sig op) Carrier_detype_ind) ξ) s,
                pr1 (pr1 Carrier_detype_ind ξ) s ⟧).
Abort.

(*

Those definitions need a full proof of Detype_ind_alg_data to be complete.

Definition Detype_ind_alg : FunctorAlg Forest_Functor_Id_H.
Proof.
  use tpair.
  - exact Carrier_detype_ind.
  - change (Forest_Functor_Id_H Carrier_detype_ind --> Carrier_detype_ind).
    exact (Detype_ind_alg_data ,, Detype_ind_alg_data_is_nat_trans).
Defined.



Definition Detype_ind : Forest_ind --> Carrier_detype_ind.
Proof.
  exact (pr1 (InitialArrow Forest_ind_IA Detype_ind_alg)).
Defined.

*)

Definition Down_ops : ops _ Forest_Sig -> ops _
UntypedForests.UntypedForest_Sig.
Proof.
  intro op.
  induction op  as [term_construct | elim_construct].
  + induction term_construct as [abs|sum].
    * exact (inl (inl tt)).
    * induction sum as [p n].
      exact (inl (inr n)).
  + induction elim_construct as [B p].
    exact (inr (length B)).
Defined.

Definition Carrier_detype_data_coind : functor_data sortToSet sortToSet.
Proof.
  use make_functor_data.
  - intros ξ.
    apply functor_path_pregroupoid.
    intros s.
    exact (pr1 (pr1 UntypedForests.UntypedForest_coind (Down_Context ξ)) (pr2 s)).
  - intros ξ ξ' η.
    apply nat_trans_functor_path_pregroupoid.
    intros s.
    change (pr1 (pr1 (pr1 UntypedForests.UntypedForest_coind (Down_Context ξ)) (pr2 s)) ->
            pr1 (pr1 (pr1 UntypedForests.UntypedForest_coind (Down_Context ξ')) (pr2 s))).
    set (aux := # (pr1 UntypedForests.UntypedForest_coind)
                  (Down_Context_on_mor η)).
    exact (pr1 aux (pr2 s)).
Defined.

Lemma Carrier_detype_data_coind_is_functor : is_functor Carrier_detype_data_coind.
Proof.
  split ; red.
  - intro ξ.
    apply nat_trans_eq.
    { exact has_homsets_HSET. }
    intro x.
    apply funextfun.
    intro elem.
    unfold functor_on_morphisms.
    unfold Carrier_detype_data_coind.
    unfold make_functor_data.
    unfold nat_trans_functor_path_pregroupoid.
    unfold make_nat_trans.
    unfold nat_trans_data_from_nat_trans_funclass.
    unfold pr1. unfold pr2.
    change (Down_Context_on_mor (identity ξ)) with (# Down_Context_functor (identity ξ)).
    rewrite (functor_id).
    rewrite (functor_id UntypedForests.UntypedForest_coind).
    apply idpath.
  - intros ξ1 ξ2 ξ3 f g.
    apply nat_trans_eq.
    { exact has_homsets_HSET. }
    intro x.
    apply funextfun.
    intro elem.
    unfold functor_on_morphisms.
    unfold Carrier_detype_data_coind.
    unfold make_functor_data.
    unfold nat_trans_functor_path_pregroupoid.
    unfold make_nat_trans.
    unfold nat_trans_data_from_nat_trans_funclass.
    unfold pr1. unfold pr2.
    change (Down_Context_on_mor (f · g)) with (# Down_Context_functor (f · g)).
    rewrite functor_comp.
    rewrite (functor_comp UntypedForests.UntypedForest_coind).
    apply idpath.
Qed.

Definition Carrier_detype_coind : sortToSet2
  := Carrier_detype_data_ind ,, Carrier_detype_data_ind_is_functor.

End Typing.

End Signature.
