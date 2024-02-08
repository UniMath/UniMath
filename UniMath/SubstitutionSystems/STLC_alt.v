(**

Syntax of the simply typed lambda calculus as a
multisorted signature.

Written by: Anders Mörtberg, 2021 (adapted from STLC.v)

*)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.
Require Import UniMath.SubstitutionSystems.MonadsFromSubstitutionSystems.
Require Import UniMath.SubstitutionSystems.SignatureExamples.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_alt.
Require Import UniMath.SubstitutionSystems.MonadsMultiSorted_alt.

Local Open Scope cat.

(** * The simply typed lambda calculus from a multisorted binding signature *)
Section Lam.

Context (sort : hSet) (arr : sort → sort → sort).

Local Lemma hsort : isofhlevel 3 sort.
Proof.
exact (isofhlevelssnset 1 sort (setproperty sort)).
Defined.

Let sortToSet : category := [path_pregroupoid sort hsort,HSET].

Local Lemma TerminalSortToSet : Terminal sortToSet.
Proof.
apply Terminal_functor_precat, TerminalHSET.
Defined.

Local Lemma BinCoprodSortToSet : BinCoproducts sortToSet.
Proof.
apply BinCoproducts_functor_precat, BinCoproductsHSET.
Defined.

Local Lemma BinProd : BinProducts [sortToSet,HSET].
Proof.
apply BinProducts_functor_precat, BinProductsHSET.
Defined.

(** Some notations *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.
Local Notation "s ⇒ t" := (arr s t).
Local Notation "'Id'" := (functor_identity _).
Local Notation "a ⊕ b" := (BinCoproductObject (BinCoprodSortToSet a b)).
Local Notation "'1'" := (TerminalObject TerminalSortToSet).
Local Notation "F ⊗ G" := (BinProduct_of_functors BinProd F G).

Let sortToSet2 := [sortToSet,sortToSet].

Local Lemma BinCoprodSortToSet2 : BinCoproducts sortToSet2.
Proof.
apply BinCoproducts_functor_precat, BinCoprodSortToSet.
Defined.

(** The signature of the simply typed lambda calculus *)
Definition STLC_Sig : MultiSortedSig sort.
Proof.
use make_MultiSortedSig.
- apply ((sort × sort) + (sort × sort))%set.
- intros H; induction H as [st|st]; induction st as [s t].
  + exact ((([],,(s ⇒ t)) :: ([],,s) :: nil),,t).
  + exact (((cons s [],,t) :: []),,(s ⇒ t)).
Defined.

(** The signature with strength for the simply typed lambda calculus *)
Definition STLC_Signature : Signature sortToSet _ _ :=
  MultiSortedSigToSignatureSet sort hsort STLC_Sig.

Definition STLC_Functor : functor sortToSet2 sortToSet2 :=
  Id_H _ BinCoprodSortToSet STLC_Signature.

Lemma STLC_Functor_Initial : Initial (FunctorAlg STLC_Functor).
Proof.
apply SignatureInitialAlgebra.
- apply InitialHSET.
- apply ColimsHSET_of_shape.
- apply is_omega_cocont_MultiSortedSigToSignature.
  + apply ProductsHSET.
  + apply Exponentials_functor_HSET.
  + apply ColimsHSET_of_shape.
Defined.

Definition STLC_Monad : Monad sortToSet :=
  MultiSortedSigToMonadSet sort hsort STLC_Sig.

(** Extract the constructors of the STLC from the initial algebra *)
Definition STLC_M : sortToSet2 :=
  alg_carrier _ (InitialObject STLC_Functor_Initial).

(* The functor parts coincide *)
Lemma STLC_Monad_ok : STLC_M = pr1 STLC_Monad.
Proof.
apply idpath.
Qed.

Let STLC_M_mor : sortToSet2⟦STLC_Functor STLC_M,STLC_M⟧ :=
  alg_map _ (InitialObject STLC_Functor_Initial).

Let STLC_M_alg : algebra_ob STLC_Functor :=
  InitialObject STLC_Functor_Initial.

(** The variables *)
Definition var_map : sortToSet2⟦Id,STLC_M⟧ :=
  BinCoproductIn1 (BinCoprodSortToSet2 _ _) · STLC_M_mor.

(** The source of the application constructor *)
Definition app_source (s t : sort) : functor sortToSet2 sortToSet2 :=
    (post_comp_functor (projSortToSet sort hsort (s ⇒ t)) ⊗ post_comp_functor (projSortToSet sort hsort s))
  ∙ (post_comp_functor (hat_functorSet sort hsort t)).

(** The application constructor *)
Definition app_map (s t : sort) : sortToSet2⟦app_source s t STLC_M,STLC_M⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (ii1 (s,,t))
  · BinCoproductIn2 (BinCoprodSortToSet2 _ _)
  · STLC_M_mor.

(** The source of the lambda constructor *)
Definition lam_source (s t : sort) : functor sortToSet2 sortToSet2 :=
    pre_comp_functor (sorted_option_functorSet sort hsort s)
  ∙ post_comp_functor (projSortToC sort hsort _ t)
  ∙ post_comp_functor (hat_functorSet sort hsort (s ⇒ t)).

Definition lam_map (s t : sort) : sortToSet2⟦lam_source s t STLC_M,STLC_M⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (ii2 (s,,t))
  · BinCoproductIn2 (BinCoprodSortToSet2 _ _)
  · STLC_M_mor.

Definition make_STLC_M_Algebra X (fvar : sortToSet2⟦Id,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧) :
    algebra_ob STLC_Functor.
Proof.
apply (tpair _ X), (BinCoproductArrow _ fvar), CoproductArrow; intros b.
induction b as [st|st]; induction st as [s t].
- exact (fapp s t).
- exact (flam s t).
Defined.

(** The recursor for the stlc *)
Definition foldr_map X (fvar : sortToSet2⟦Id,X⟧)
                       (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
                       (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧) :
                        algebra_mor _ STLC_M_alg (make_STLC_M_Algebra X fvar fapp flam) :=
  InitialArrow STLC_Functor_Initial (make_STLC_M_Algebra X fvar fapp flam).

(** The equation for variables *)
Lemma foldr_var X (fvar : sortToSet2⟦Id,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧) :
  var_map · foldr_map X fvar fapp flam = fvar.
Proof.
unfold var_map.
rewrite <- assoc, (algebra_mor_commutes _ _ _ (foldr_map _ _ _ _)), assoc.
etrans; [eapply cancel_postcomposition, BinCoproductOfArrowsIn1|].
rewrite id_left.
apply BinCoproductIn1Commutes.
Qed.

Lemma foldr_app X (fvar : sortToSet2⟦Id,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧)
  (s t : sort) :
  app_map s t · foldr_map X fvar fapp flam =
  # (pr1 (app_source s t)) (foldr_map X fvar fapp flam) · fapp s t.
Proof.
unfold app_map.
rewrite <- assoc.
etrans; [apply maponpaths, (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))|].
rewrite assoc.
etrans; [eapply cancel_postcomposition; rewrite <- assoc;
         apply maponpaths, BinCoproductOfArrowsIn2|].
rewrite <- !assoc.
etrans; [apply maponpaths, maponpaths, BinCoproductIn2Commutes|].
rewrite assoc.
etrans; [apply cancel_postcomposition; use (CoproductOfArrowsIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)))|].
rewrite <- assoc.
apply maponpaths.
exact (CoproductInCommutes _ _ _ _ _ _ (inl (s,,t))).
Qed.

Lemma foldr_lam X (fvar : sortToSet2⟦Id,X⟧)
  (fapp : ∏ s t, sortToSet2⟦app_source s t X,X⟧)
  (flam : ∏ s t, sortToSet2⟦lam_source s t X,X⟧)
  (s t : sort) :
  lam_map s t · foldr_map X fvar fapp flam =
  # (pr1 (lam_source s t)) (foldr_map X fvar fapp flam) · flam s t.
Proof.
unfold lam_map.
rewrite <- assoc.
etrans; [apply maponpaths, (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))|].
rewrite assoc.
etrans; [eapply cancel_postcomposition; rewrite <- assoc;
         apply maponpaths, BinCoproductOfArrowsIn2|].
rewrite <- !assoc.
etrans; [apply maponpaths, maponpaths, BinCoproductIn2Commutes|].
rewrite assoc.
etrans; [apply cancel_postcomposition; use (CoproductOfArrowsIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)))|].
rewrite <- assoc.
apply maponpaths.
exact (CoproductInCommutes _ _ _ _ _ _ (inr (s,,t))).
Qed.


(* Now substitution *)
Let STLC := STLC_Monad.

(* Parallel substitution *)
Definition psubst {X Y : sortToSet} (f : sortToSet⟦X, STLC Y ⟧) :
  sortToSet⟦ STLC (X ⊕ Y), STLC Y ⟧ := monadSubstGen_instantiated _ _ _ _ f.

(* Substitution of a single variable *)
Definition subst {X : sortToSet} (f : sortToSet⟦ 1, STLC X ⟧) :
  sortToSet⟦ STLC (1 ⊕ X), STLC X ⟧ := monadSubstGen_instantiated _ _ _ _ f.

Definition weak {X Y : sortToSet} : sortToSet⟦STLC Y,STLC (X ⊕ Y)⟧ :=
  mweak_instantiated sort hsort HSET BinCoproductsHSET.

Definition exch {X Y Z : sortToSet} : sortToSet⟦STLC (X ⊕ (Y ⊕ Z)), STLC (Y ⊕ (X ⊕ Z))⟧ :=
  mexch_instantiated sort hsort HSET BinCoproductsHSET.

Lemma psubst_interchange {X Y Z : sortToSet}
        (f : sortToSet⟦X,STLC (Y ⊕ Z)⟧) (g : sortToSet⟦Y, STLC Z⟧) :
        psubst f · psubst g = exch · psubst (g · weak) · psubst (f · psubst g).
Proof.
apply subst_interchange_law_gen_instantiated.
Qed.

Lemma subst_interchange {X : sortToSet}
        (f : sortToSet⟦1,STLC (1 ⊕ X)⟧) (g : sortToSet⟦1,STLC X⟧) :
  subst f · subst g = exch · subst (g · weak) · subst (f · subst g).
Proof.
apply subst_interchange_law_gen_instantiated.
Qed.

(* We could also unfold these as statements about sort-indexed sets, but
   this quickly gets very cumbersome: *)
(* Definition psubst {X Y : sort → hSet} (f : ∏ t, X t → STLC Y t) (t : sort) : *)
(*   STLC (λ t, (X t + Y t)%set) t → STLC Y t. *)
(* Proof. *)
(* intros u. *)
(* transparent assert (X' : (sortToSet)). *)
(* { use (functor_path_pregroupoid _); apply X. } *)
(* transparent assert (Y' : (sortToSet)). *)
(* { use (functor_path_pregroupoid _); apply Y. } *)
(* transparent assert (f' : (sortToSet⟦ X' , STLC_Monad Y' ⟧)). *)
(* { use nat_trans_functor_path_pregroupoid; apply homset_property; use f. } *)
(* use (pr1 (@monadSubstGen_instantiated sort SET BinCoproductsHSET STLC_Monad X' Y' f') t). *)

End Lam.
