(**

This file provides a stable interface to the formalization of the paper:

  From binding signatures to monads in UniMath

  https://arxiv.org/abs/1612.00693

by Benedikt Ahrens, Ralph Matthes and Anders Mörtberg.


PLEASE DO NOT RENAME THIS FILE - its name is referenced in the article
about this formalization.

*)
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.NumberSystems.NaturalNumbers.
Require Import UniMath.Foundations.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.total2_paths.
Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.category_hset.
Require Import UniMath.CategoryTheory.category_hset_structures.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.equivalences.
Require Import UniMath.CategoryTheory.EquivalencesExamples.
Require Import UniMath.CategoryTheory.AdjunctionHomTypesWeq.
Require Import UniMath.CategoryTheory.CocontFunctors.
Require Import UniMath.CategoryTheory.ProductPrecategory.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.SignatureCategory.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.

Local Notation "[ C , D , hsD ]" := (functor_precategory C D hsD).

(** Definition 1: Binding signature *)
Definition BindingSig : UU :=
  @UniMath.SubstitutionSystems.BindingSigToMonad.BindingSig.

(** Definition 4: Signatures with strength *)
Definition Signature : Π C : precategory, has_homsets C → UU :=
  @UniMath.SubstitutionSystems.Signatures.Signature.

(** Definition 5: Morphism of signatures with strength *)
Definition SignatureMor :
  Π C : Precategory, Signature C (homset_property C) → Signature C (homset_property C) → UU :=
  @UniMath.SubstitutionSystems.SignatureCategory.SignatureMor.

(** Definition 6: Coproduct of signatures with strength *)
Definition Sum_of_Signatures :
  Π (I : UU) (C : precategory) (hsC : has_homsets C), Coproducts I C
  → (I → Signature C hsC) → Signature C hsC :=
    @UniMath.SubstitutionSystems.SumOfSignatures.Sum_of_Signatures.

(** Definition 7: Binary product of signatures with strength *)
Definition BinProduct_of_Signatures :
  Π (C : precategory) (hsC : has_homsets C), BinProducts C
  → Signature C hsC → Signature C hsC → Signature C hsC :=
    @UniMath.SubstitutionSystems.BinProductOfSignatures.BinProduct_of_Signatures.

(** Problem 8: Signatures with strength from binding signatures *)
Definition BindingSigToSignature :
  Π {C : precategory} (hsC : has_homsets C), BinProducts C → BinCoproducts C → Terminal C
  → Π sig : BindingSig, Coproducts (BindingSigIndex sig) C → Signature C hsC :=
    @UniMath.SubstitutionSystems.BindingSigToMonad.BindingSigToSignature.

(** Definition 10 and Lemma 11 and 12: see UniMath/SubstitutionSystems/SignatureExamples.v *)

(** Definition 15: Graph *)
Definition graph : UU := @UniMath.CategoryTheory.limits.graphs.colimits.graph.

(** Definition 16: Diagram *)
Definition diagram : graph → precategory → UU :=
  @UniMath.CategoryTheory.limits.graphs.colimits.diagram.

(** Definition 18: Cocone *)
Definition cocone : Π {C : precategory} {g : graph}, diagram g C → C → UU :=
  @UniMath.CategoryTheory.limits.graphs.colimits.cocone.

(** Definition 19: Colimiting cocone *)
Definition isColimCocone : Π {C : precategory} {g : graph} (d : diagram g C)
  (c0 : C), cocone d c0 → UU :=
    @UniMath.CategoryTheory.limits.graphs.colimits.isColimCocone.

(** Colimits of a specific shape *)
Definition Colims_of_shape : graph → precategory → UU :=
  @UniMath.CategoryTheory.limits.graphs.colimits.Colims_of_shape.

(** Colimits of any shape *)
Definition Colims : precategory → UU :=
  @UniMath.CategoryTheory.limits.graphs.colimits.Colims.

(** Remark 20: Uniqueness of colimits *)
Lemma isaprop_Colims : Π C : category, isaprop (Colims C).
Proof.
exact @UniMath.CategoryTheory.limits.graphs.colimits.isaprop_Colims.
Defined.

(** Definition 21: Preservation of colimits *)
Definition preserves_colimit : Π {C D : precategory}, functor C D
  → Π {g : graph} (d : diagram g C) (L : C), cocone d L → UU :=
    @UniMath.CategoryTheory.CocontFunctors.preserves_colimit.

Definition is_cocont : Π {C D : precategory}, functor C D → UU :=
  @UniMath.CategoryTheory.CocontFunctors.is_cocont.

Definition is_omega_cocont : Π {C D : precategory}, functor C D → UU :=
  @UniMath.CategoryTheory.CocontFunctors.is_omega_cocont.

(** Lemma 22: Invariance of cocontinuity under isomorphism *)
Lemma preserves_colimit_iso :
  Π (C D : precategory) (hsD : has_homsets D) (F G : functor C D) (α : @iso [C,D,hsD] F G)
    (g : graph) (d : diagram g C) (L : C) (cc : cocone d L),
  preserves_colimit F d L cc → preserves_colimit G d L cc.
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.preserves_colimit_iso.
Defined.

(** Problem 23: Colimits in functor categories *)
Definition ColimsFunctorCategory_of_shape :
  Π (g : graph) (A C : precategory) (hsC : has_homsets C),
  Colims_of_shape g C → Colims_of_shape g [A,C,hsC] :=
    @UniMath.CategoryTheory.limits.graphs.colimits.ColimsFunctorCategory_of_shape.

(** Problem 25: Initial algebras of ω-cocontinuous functors *)
Definition colimAlgInitial :
  Π (C : precategory) (hsC : has_homsets C) (InitC : Initial C)
    (F : functor C C), is_omega_cocont F → ColimCocone (initChain InitC F) →
  Initial (FunctorAlg F hsC) :=
    @UniMath.CategoryTheory.CocontFunctors.colimAlgInitial.

(** Lemma 26: Lambek's lemma *)
Lemma initialAlg_is_iso :
  Π (C : precategory) (hsC : has_homsets C) (F : functor C C)
    (Aa : algebra_ob F), isInitial (FunctorAlg F hsC) Aa → is_iso (alg_map F Aa).
Proof.
exact @UniMath.CategoryTheory.FunctorAlgebras.initialAlg_is_iso.
Defined.

(** Problem 28: Colimits in Set *)
Lemma ColimsHSET_of_shape : Π (g : graph), Colims_of_shape g HSET.
Proof.
exact @UniMath.CategoryTheory.category_hset_structures.ColimsHSET_of_shape.
Defined.

(** Lemma 32: Left adjoints preserve colimits *)
Lemma left_adjoint_cocont :
  Π (C D : precategory) (F : functor C D), is_left_adjoint F
  → has_homsets C → has_homsets D → is_cocont F.
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.left_adjoint_cocont.
Defined.

(** Lemma 33: Examples of preservation of colimits *)
(** (i): Identity functor *)
Lemma preserves_colimit_identity : Π C : precategory, has_homsets C
  → Π (g : colimits.graph) (d : colimits.diagram g C)
    (L : C) (cc : colimits.cocone d L),
  preserves_colimit (functor_identity C) d L cc.
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.preserves_colimit_identity.
Defined.

(** (ii): Constant functor *)
Lemma is_omega_cocont_constant_functor : Π C D : precategory, has_homsets D
  → Π x : D, CocontFunctors.is_omega_cocont (constant_functor C D x).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_omega_cocont_constant_functor.
Defined.

(** (iii): Diagonal functor *)
Lemma is_cocont_delta_functor : Π (I : UU) (C : precategory),
  Products I C → has_homsets C → is_cocont (delta_functor I C).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_cocont_delta_functor.
Defined.

Lemma is_omega_cocont_delta_functor : Π (I : UU) (C : precategory),
  Products I C → has_homsets C → is_omega_cocont (delta_functor I C).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_omega_cocont_delta_functor.
Defined.

(** (iv): Coproduct functor *)
Lemma is_cocont_coproduct_functor :
  Π (I : UU) (C : precategory) (PC : Coproducts I C),
  has_homsets C → is_cocont (coproduct_functor I PC).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_cocont_coproduct_functor.
Defined.

Lemma is_omega_cocont_coproduct_functor :
  Π (I : UU) (C : precategory) (PC : Coproducts I C),
  has_homsets C → is_omega_cocont (coproduct_functor I PC).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_omega_cocont_coproduct_functor.
Defined.

(** Lemma 34: Examples of preservation of cocontinuity *)
(** (i): Composition of functors *)
Lemma preserves_colimit_functor_composite :
  Π C D E : precategory, has_homsets E
  → Π (F : functor C D) (G : functor D E) (g : graph)
      (d : diagram g C) (L : C) (cc : cocone d L),
      preserves_colimit F d L cc
  → preserves_colimit G (mapdiagram F d) (F L) (mapcocone F d cc)
  → preserves_colimit (functor_composite F G) d L cc.
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.preserves_colimit_functor_composite.
Defined.

Lemma is_cocont_functor_composite :
  Π C D E : precategory, has_homsets E
  → Π (F : functor C D) (G : functor D E), is_cocont F → is_cocont G
  → is_cocont (functor_composite F G).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_cocont_functor_composite.
Defined.

Lemma is_omega_cocont_functor_composite :
  Π C D E : precategory, has_homsets E
  → Π (F : functor C D) (G : functor D E), is_omega_cocont F → is_omega_cocont G
  → is_omega_cocont (functor_composite F G).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_omega_cocont_functor_composite.
Defined.

(** (ii): Families of functors *)
Lemma is_cocont_family_functor :
  Π (I : UU) (A B : precategory), has_homsets A → has_homsets B → isdeceq I
  → Π F : I → functor A B, (Π i : I, is_cocont (F i))
  → is_cocont (family_functor I F).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_cocont_family_functor.
Defined.

Lemma is_omega_cocont_family_functor :
  Π (I : UU) (A B : precategory), has_homsets A → has_homsets B → isdeceq I
  → Π F : I → functor A B, (Π i : I, is_omega_cocont (F i))
  → is_omega_cocont (family_functor I F).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_omega_cocont_family_functor.
Defined.

(** Example 36: Exponentials in Set *)
Definition has_exponentials_HSET : has_exponentials BinProductsHSET :=
  @UniMath.CategoryTheory.category_hset_structures.has_exponentials_HSET.

(** Lemma 37: Left and right product functors preserves colimits *)
Lemma is_cocont_constprod_functor1 :
  Π (C : precategory) (PC : BinProducts C), has_homsets C → has_exponentials PC
  → Π x : C, is_cocont (constprod_functor1 PC x).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_cocont_constprod_functor1.
Defined.

Lemma is_omega_cocont_constprod_functor1 :
  Π (C : precategory) (PC : BinProducts C), has_homsets C → has_exponentials PC
  → Π x : C, is_omega_cocont (constprod_functor1 PC x).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_omega_cocont_constprod_functor1.
Defined.

Lemma is_cocont_constprod_functor2 :
  Π (C : precategory) (PC : BinProducts C), has_homsets C → has_exponentials PC
  → Π x : C, is_cocont (constprod_functor2 PC x).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_cocont_constprod_functor2.
Defined.

Lemma is_omega_cocont_constprod_functor2 :
  Π (C : precategory) (PC : BinProducts C), has_homsets C → has_exponentials PC
  → Π x : C, is_omega_cocont (constprod_functor2 PC x).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_omega_cocont_constprod_functor2.
Defined.

(** Theorem 38: Binary product functor is ω-cocontinuous *)
Lemma is_omega_cocont_binproduct_functor :
  Π (C : precategory) (PC : BinProducts C), has_homsets C
  → (Π x : C, is_omega_cocont (constprod_functor1 PC x))
  → is_omega_cocont (binproduct_functor PC).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_omega_cocont_binproduct_functor.
Defined.

(** Example 39: Lists of sets *)
(* see: UniMath/CategoryTheory/Inductives/Lists.v *)

(** Theorem 42: Precomposition functor preserves colimits *)
Lemma preserves_colimit_pre_composition_functor :
  Π (A B C : precategory) (F : functor A B) (hsB : has_homsets B) (hsC : has_homsets C)
    (g : graph) (d : diagram g [B, C, hsC]) (G : [B, C, hsC]) (ccG : cocone d G),
    (Π b : B, ColimCocone (diagram_pointwise hsC d b))
  → preserves_colimit (pre_composition_functor A B C hsB hsC F) d G ccG.
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.preserves_colimit_pre_composition_functor.
Defined.

Lemma is_omega_cocont_pre_composition_functor :
  Π (A B C : precategory) (F : functor A B) (hsB : has_homsets B) (hsC : has_homsets C),
  Colims_of_shape nat_graph C → is_omega_cocont (pre_composition_functor A B C hsB hsC F).
Proof.
exact @UniMath.CategoryTheory.CocontFunctors.is_omega_cocont_pre_composition_functor.
Defined.

(** Theorem 44: Signature functor associated to a binding signature is ω-cocontinuous *)
Lemma is_omega_cocont_BindingSigToSignature :
  Π (C : precategory) (hsC : has_homsets C)
  (BPC : BinProducts C) (BCC : BinCoproducts C) (TC : Terminal C),
  Colims_of_shape nat_graph C →
  (Π F : functor_precategory C C hsC, is_omega_cocont
       (constprod_functor1 (BinProducts_functor_precat C C BPC hsC) F))
  → Π (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C),
                          Products (BindingSigIndex sig) C →
  is_omega_cocont (pr1 (BindingSigToSignature hsC BPC BCC TC sig CC)).
Proof.
exact @UniMath.SubstitutionSystems.BindingSigToMonad.is_omega_cocont_BindingSigToSignature.
Defined.

(** Construction 46: Datatypes specified by binding signatures (initial algebra of Id_H + H) *)
Definition SignatureInitialAlgebra :
  Π {C : precategory} (hsC : has_homsets C) (BPC : BinProducts C) (BCC : BinCoproducts C),
  Initial C → Colims_of_shape nat_graph C
  → Π s : Signature C hsC, is_omega_cocont (Signature_Functor C hsC s)
  → Initial (FunctorAlg (Id_H C hsC BCC s) (BindingSigToMonad.has_homsets_C2 hsC)).
Proof.
exact @UniMath.SubstitutionSystems.BindingSigToMonad.SignatureInitialAlgebra.
Defined.

(** Theorem 48: Construction of a substitution operation on an initial algebra *)
Definition InitHSS :
  Π (C : precategory) (hsC : has_homsets C) (CP : BinCoproducts C),
  BinProducts C → Initial C → Colims_of_shape nat_graph C →
  Π H : Signature C hsC, is_omega_cocont (pr1 H) → hss_precategory CP H.
Proof.
exact @UniMath.SubstitutionSystems.LiftingInitial_alt.InitHSS.
Defined.

Lemma isInitial_InitHSS :
  Π (C : precategory) (hsC : has_homsets C) (CP : BinCoproducts C)
  (BPC : BinProducts C) (IC : Initial C)
  (CC : Colims_of_shape nat_graph C) (H : Signature C hsC)
  (HH : is_omega_cocont (pr1 H)),
  isInitial (hss_precategory CP H) (InitHSS C hsC CP BPC IC CC H HH).
Proof.
exact @UniMath.SubstitutionSystems.LiftingInitial_alt.isInitial_InitHSS.
Defined.

(** Section 4.2: Binding signatures to monads *)
Definition BindingSigToMonad :
  Π (C : precategory) (hsC : has_homsets C) (BPC : BinProducts C),
  BinCoproducts C → Terminal C → Initial C → Colims_of_shape nat_graph C
  → (Π F, is_omega_cocont (constprod_functor1 (BinProducts_functor_precat C C BPC hsC) F))
  → Π sig : BindingSig, Products (BindingSigIndex sig) C
  → Coproducts (BindingSigIndex sig) C
  → Monad C.
Proof.
  exact @UniMath.SubstitutionSystems.BindingSigToMonad.BindingSigToMonad.
Defined.

(** Example 50: Untyped lambda calculus *)
(* See: UniMath/SubstitutionSystems/LamFromBindingSig.v *)

(** Example 51: Raw syntax of Martin-Löf type theory *)
(* See: UniMath/SubstitutionSystems/MLTT79.v *)
