Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseBinProduct.
Require Import UniMath.CategoryTheory.limits.FunctorsPointwiseBinCoproduct.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.cats.limits.
Require Import UniMath.CategoryTheory.BinProductPrecategory.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.EquivalencesExamples.
Require Import UniMath.CategoryTheory.AdjunctionHomTypesWeq.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.SubstitutionSystems.GenSigToMonad.
Require Import UniMath.SubstitutionSystems.SigToMonad.

Definition Arity_to_Signature : lists.list nat -> Signatures.Signature HSET has_homsets_HSET.
Proof.
  exact @SigToMonad.Arity_to_Signature.
Defined.

Definition GenSigToSignature
  : GenSig → Signatures.Signature HSET has_homsets_HSET.
Proof.
  exact UniMath.SubstitutionSystems.GenSigToMonad.GenSigToSignature.
Defined.


Definition algebra_ob_pair {C : precategory} {F : functor C C} X (f : C⟦F X, X⟧)
  : algebra_ob F.
Proof.
  exists X.
  exact f.
Defined.

Lemma colim_of_chain_is_initial_alg
  : Π (C : precategory) (hsC : has_homsets C) (InitC : Initial C)
      (F : functor C C) (HF : is_omega_cocont F)
      (CC : ColimCocone (initChain InitC F)),
    isInitial (FunctorAlg F hsC)
              (algebra_ob_pair (colim CC) (colim_algebra_mor C InitC F HF CC)).
Proof.
  exact CocontFunctors.colimAlgIsInitial.
Defined.


Lemma is_omega_cocont_pre_composition_functor
  : Π (M C A : precategory) (K : functor M C) (hsC : has_homsets C)
     (hsA : has_homsets A),
   Lims A → is_omega_cocont (pre_composition_functor M C A hsC hsA K).
Proof.
  exact CocontFunctors.is_omega_cocont_pre_composition_functor.
Defined.

Definition RightKanExtension_from_limits
  : Π (M C A : precategory) (K : functor M C) (hsC : has_homsets C)
    (hsA : has_homsets A),
  Lims A → RightKanExtension.GlobalRightKanExtensionExists M C K A hsC hsA.
Proof.
  exact CocontFunctors.RightKanExtension_from_limits.
Defined.

Definition ColimCoconeHSET
  : Π (g : graph) (D : diagram g HSET), ColimCocone D.
Proof.
  exact category_hset_structures.ColimCoconeHSET.
Defined.

Lemma is_omega_cocont_binproduct_functor
  : Π (C : precategory) (PC : BinProducts C), has_homsets C →
    (Π x : C, is_omega_cocont (constprod_functor1 PC x)) →
    (Π x : C, is_omega_cocont (constprod_functor2 PC x)) →
    is_omega_cocont (binproduct_functor PC).
Proof.
  exact CocontFunctors.is_omega_cocont_binproduct_functor.
Defined.

Lemma left_adjoint_cocont
  : Π (C D : precategory) (F : functor C D),
    is_left_adjoint F → has_homsets C → has_homsets D → is_cocont F.
Proof.
  exact @CocontFunctors.left_adjoint_cocont.
Defined.
