(**

This file provides a stable interface to the formalization of the paper:

  From binding signatures to monads in UniMath

  https://arxiv.org/abs/1612.00693

by Benedikt Ahrens, Ralph Matthes and Anders Mörtberg.


PLEASE DO NOT RENAME THIS FILE - its name is referenced in the article
about this formalization.

*)

Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import UniMath.SubstitutionSystems.SignatureCategory.
Require Import UniMath.SubstitutionSystems.SubstitutionSystems.
Require Import UniMath.SubstitutionSystems.BindingSigToMonad.
Require Import UniMath.SubstitutionSystems.LiftingInitial_alt.

Local Open Scope cat.

Local Notation "[ C , D ]" := (functor_category C D).

(** Definition 1: Binding signature *)
Definition BindingSig : UU :=
  @UniMath.SubstitutionSystems.BindingSigToMonad.BindingSig.

(** Definition 4: Signatures with strength *)
Definition Signature : ∏ (C D D' : category), UU :=
  @UniMath.SubstitutionSystems.Signatures.Signature.

(** Definition 5: Morphism of signatures with strength *)
Definition SignatureMor :
  ∏ C D D' : category, Signatures.Signature C D D' → Signatures.Signature C D D' → UU :=
  @UniMath.SubstitutionSystems.SignatureCategory.SignatureMor.

(** Definition 6: Coproduct of signatures with strength *)
Definition Sum_of_Signatures :
  ∏ (I : UU) (C D D': category), Coproducts I D
  → (I → Signature C D D') → Signature C D D' :=
  @UniMath.SubstitutionSystems.SumOfSignatures.Sum_of_Signatures.

(** Definition 7: Binary product of signatures with strength *)
Definition BinProduct_of_Signatures :
  ∏ (C D D' : category), BinProducts D →
    Signature C D D' → Signature C D D' → Signature C D D' :=
  @UniMath.SubstitutionSystems.BinProductOfSignatures.BinProduct_of_Signatures.

(** Problem 8: Signatures with strength from binding signatures *)
Definition BindingSigToSignature :
  ∏ {C : category},
    BinProducts C → BinCoproducts C → Terminal C
  → ∏ sig : BindingSig, Coproducts (BindingSigIndex sig) C →
    Signature C C C :=
    @UniMath.SubstitutionSystems.BindingSigToMonad.BindingSigToSignature.

(** Definition 10 and Lemma 11 and 12: see UniMath/SubstitutionSystems/SignatureExamples.v *)

(** Definition 15: Graph *)
Definition graph : UU := @UniMath.CategoryTheory.limits.graphs.colimits.graph.

(** Definition 16: Diagram *)
Definition diagram : graph → category → UU :=
  @UniMath.CategoryTheory.limits.graphs.colimits.diagram.

(** Definition 17: Cocone *)
Definition cocone : ∏ {C : category} {g : graph}, diagram g C → C → UU :=
  @UniMath.CategoryTheory.limits.graphs.colimits.cocone.

(** Definition 18: Colimiting cocone *)
Definition isColimCocone : ∏ {C : category} {g : graph} (d : diagram g C)
  (c0 : C), cocone d c0 → UU :=
    @UniMath.CategoryTheory.limits.graphs.colimits.isColimCocone.

(** Colimits of a specific shape *)
Definition Colims_of_shape : graph → category → UU :=
  @UniMath.CategoryTheory.limits.graphs.colimits.Colims_of_shape.

(** Colimits of any shape *)
Definition Colims : category → UU :=
  @UniMath.CategoryTheory.limits.graphs.colimits.Colims.

(** Remark 19: Uniqueness of colimits *)
Lemma isaprop_Colims : ∏ C : univalent_category, isaprop (Colims C).
Proof.
exact @UniMath.CategoryTheory.limits.graphs.colimits.isaprop_Colims.
Defined.

(** Definition 20: Preservation of colimits *)
Definition preserves_colimit : ∏ {C D : category}, functor C D
  → ∏ {g : graph} (d : diagram g C) (L : C), cocone d L → UU :=
    @UniMath.CategoryTheory.limits.graphs.colimits.preserves_colimit.

Definition is_cocont : ∏ {C D : category}, functor C D → UU :=
  @UniMath.CategoryTheory.Chains.Chains.is_cocont.

Definition is_omega_cocont : ∏ {C D : category}, functor C D → UU :=
  @UniMath.CategoryTheory.Chains.Chains.is_omega_cocont.

(** Lemma 21: Invariance of cocontinuity under isomorphism *)
Lemma preserves_colimit_z_iso :
  ∏ (C D : category)
    (F G : functor C D) (α : @z_iso [C, D] F G)
    (g : graph) (d : diagram g C) (L : C) (cc : cocone d L),
  preserves_colimit F d L cc → preserves_colimit G d L cc.
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.preserves_colimit_z_iso.
Defined.

(** Problem 22: Colimits in functor categories *)
Definition ColimsFunctorCategory_of_shape :
  ∏ (g : graph) (A C : category),
    Colims_of_shape g C → Colims_of_shape g [A, C] :=
  @UniMath.CategoryTheory.limits.graphs.colimits.ColimsFunctorCategory_of_shape.

(** Problem 24: Initial algebras of ω-cocontinuous functors *)
Definition colimAlgInitial :
  ∏ (C : category) (InitC : Initial C)
    (F : functor C C), is_omega_cocont F → ColimCocone (initChain InitC F) →
    Initial (FunctorAlg F) :=
  @UniMath.CategoryTheory.Chains.Adamek.colimAlgInitial.

(** Lemma 25: Lambek's lemma *)
Lemma initialAlg_is_z_iso :
  ∏ (C : category) (F : functor C C)
    (Aa : algebra_ob F), isInitial (FunctorAlg F) Aa → is_z_isomorphism (alg_map F Aa).
Proof.
exact @UniMath.CategoryTheory.FunctorAlgebras.initialAlg_is_z_iso.
Defined.

(** Problem 27: Colimits in Set *)
Lemma ColimsHSET_of_shape : ∏ (g : graph), Colims_of_shape g HSET.
Proof.
exact @UniMath.CategoryTheory.categories.HSET.Colimits.ColimsHSET_of_shape.
Defined.

(** Lemma 31: Left adjoints preserve colimits *)
Lemma left_adjoint_cocont :
  ∏ (C D : category) (F : functor C D), is_left_adjoint F → is_cocont F.
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.left_adjoint_cocont.
Defined.

(** Lemma 32: Examples of preservation of colimits *)
(** (i): Identity functor *)
Lemma preserves_colimit_identity :
  ∏ (C : category) (g : colimits.graph) (d : colimits.diagram g C)
      (L : C) (cc : colimits.cocone d L),
  preserves_colimit (functor_identity C) d L cc.
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.preserves_colimit_identity.
Defined.

(** (ii): Constant functor *)
Lemma is_omega_cocont_constant_functor : ∏ (C D : category) (x : D),
    Chains.Chains.is_omega_cocont (constant_functor C D x).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_omega_cocont_constant_functor.
Defined.

(** (iii): Diagonal functor *)
Lemma is_cocont_delta_functor : ∏ (I : UU) (C : category),
  Products I C → is_cocont (delta_functor I C).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_cocont_delta_functor.
Defined.

Lemma is_omega_cocont_delta_functor : ∏ (I : UU) (C : category),
  Products I C → is_omega_cocont (delta_functor I C).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_omega_cocont_delta_functor.
Defined.

(** (iv): Coproduct functor *)
Lemma is_cocont_coproduct_functor :
  ∏ (I : UU) (C : category) (PC : Coproducts I C), is_cocont (coproduct_functor I PC).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_cocont_coproduct_functor.
Defined.

Lemma is_omega_cocont_coproduct_functor :
  ∏ (I : UU) (C : category) (PC : Coproducts I C), is_omega_cocont (coproduct_functor I PC).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_omega_cocont_coproduct_functor.
Defined.

(** Lemma 33: Examples of preservation of cocontinuity *)
(** (i): Composition of functors *)
Lemma preserves_colimit_functor_composite :
  ∏ (C D E : category) (F : functor C D) (G : functor D E) (g : graph)
      (d : diagram g C) (L : C) (cc : cocone d L),
      preserves_colimit F d L cc
  → preserves_colimit G (mapdiagram F d) (F L) (mapcocone F d cc)
  → preserves_colimit (functor_composite F G) d L cc.
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.preserves_colimit_functor_composite.
Defined.

Lemma is_cocont_functor_composite :
  ∏ (C D E : category) (F : functor C D) (G : functor D E), is_cocont F → is_cocont G
  → is_cocont (functor_composite F G).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_cocont_functor_composite.
Defined.

Lemma is_omega_cocont_functor_composite :
  ∏ (C D E : category) (F : functor C D) (G : functor D E), is_omega_cocont F → is_omega_cocont G
  → is_omega_cocont (functor_composite F G).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_omega_cocont_functor_composite.
Defined.

(** (ii) Tuple functor *)
Lemma is_cocont_tuple_functor :
  ∏ (I : UU) (A : category) (B: I -> category) (F : ∏ i, functor A (B i)), (∏ i, is_cocont (F i))
  -> is_cocont (tuple_functor F).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_cocont_tuple_functor.
Defined.

Lemma is_omega_cocont_tuple_functor :
  ∏ (I : UU) (A : category) (B: I -> category) (F : ∏ i, functor A (B i)), (∏ i, is_omega_cocont (F i))
  -> is_omega_cocont (tuple_functor F).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_omega_cocont_tuple_functor.
Defined.

(** (iii): Families of functors *)
Lemma is_cocont_family_functor :
  ∏ (I : UU) (A B : category), isdeceq I
  → ∏ F : I → functor A B, (∏ i : I, is_cocont (F i))
  → is_cocont (family_functor I F).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_cocont_family_functor.
Defined.

Lemma is_omega_cocont_family_functor :
  ∏ (I : UU) (A B : category), isdeceq I
  → ∏ F : I → functor A B, (∏ i : I, is_omega_cocont (F i))
  → is_omega_cocont (family_functor I F).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_omega_cocont_family_functor.
Defined.

(** Example 35: Exponentials in Set *)
Definition Exponentials_HSET : Exponentials BinProductsHSET :=
  @UniMath.CategoryTheory.categories.HSET.Structures.Exponentials_HSET.

(** Lemma 36: Left and right product functors preserves colimits *)
Lemma is_cocont_constprod_functor1 :
  ∏ (C : category) (PC : BinProducts C), Exponentials PC
  → ∏ x : C, is_cocont (constprod_functor1 PC x).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_cocont_constprod_functor1.
Defined.

Lemma is_omega_cocont_constprod_functor1 :
  ∏ (C : category) (PC : BinProducts C), Exponentials PC
  → ∏ x : C, is_omega_cocont (constprod_functor1 PC x).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_omega_cocont_constprod_functor1.
Defined.

Lemma is_cocont_constprod_functor2 :
  ∏ (C : category) (PC : BinProducts C), Exponentials PC
  → ∏ x : C, is_cocont (constprod_functor2 PC x).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_cocont_constprod_functor2.
Defined.

Lemma is_omega_cocont_constprod_functor2 :
  ∏ (C : category) (PC : BinProducts C), Exponentials PC
  → ∏ x : C, is_omega_cocont (constprod_functor2 PC x).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_omega_cocont_constprod_functor2.
Defined.

(** Theorem 37: Binary product functor is ω-cocontinuous *)
Lemma is_omega_cocont_binproduct_functor :
  ∏ (C : category) (PC : BinProducts C), (∏ x : C, is_omega_cocont (constprod_functor1 PC x))
  → is_omega_cocont (binproduct_functor PC).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_omega_cocont_binproduct_functor.
Defined.

(** Example 38: Lists of sets *)
(* see: UniMath/CategoryTheory/Inductives/Lists.v *)

(** Theorem 41: Precomposition functor preserves colimits *)
Lemma preserves_colimit_pre_composition_functor :
  ∏ (A B C : category) (F : functor A B)
    (g : graph) (d : diagram g [B, C]) (G : [B, C]) (ccG : cocone d G),
    (∏ b : B, ColimCocone (diagram_pointwise d b))
  → preserves_colimit (pre_composition_functor A B C F) d G ccG.
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.preserves_colimit_pre_composition_functor.
Defined.

Lemma is_omega_cocont_pre_composition_functor :
  ∏ (A B C : category) (F : functor A B),
  Colims_of_shape nat_graph C → is_omega_cocont (pre_composition_functor A B C F).
Proof.
exact @UniMath.CategoryTheory.Chains.OmegaCocontFunctors.is_omega_cocont_pre_composition_functor.
Defined.

(** Theorem 43: Signature functor associated to a binding signature is ω-cocontinuous *)
Lemma is_omega_cocont_BindingSigToSignature :
  ∏ (C : category) (BPC : BinProducts C) (BCC : BinCoproducts C) (TC : Terminal C),
  Colims_of_shape nat_graph C →
  (∏ F : functor_category C C, is_omega_cocont
       (constprod_functor1 (BinProducts_functor_precat C C BPC) F))
  → ∏ (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C),
  is_omega_cocont (pr1 (BindingSigToSignature BPC BCC TC sig CC)).
Proof.
exact @UniMath.SubstitutionSystems.BindingSigToMonad.is_omega_cocont_BindingSigToSignature.
Defined.

(** Problem 45: Datatypes specified by binding signatures *)
Definition DatatypeOfBindingSig :
  ∏ (C : category) (BPC : BinProducts C) (BCC : BinCoproducts C)
    (_ : Initial C) (TC : Terminal C)
    (_ : Colims_of_shape nat_graph C)
    (_ : ∏ (F : functor_category C C),
            is_omega_cocont (constprod_functor1 (BinProducts_functor_precat C C BPC) F))
    (sig : BindingSig) (CC : Coproducts (BindingSigIndex sig) C),
  Initial (FunctorAlg (Id_H C BCC (pr1 (BindingSigToSignature BPC BCC TC sig CC)))).
Proof.
exact @UniMath.SubstitutionSystems.BindingSigToMonad.DatatypeOfBindingSig.
Defined.

(** Theorem 48: Construction of a substitution operation on an initial algebra *)
Definition InitHSS :
  ∏ (C : category) (CP : BinCoproducts C),
  Initial C → Colims_of_shape nat_graph C →
  ∏ H : UniMath.SubstitutionSystems.Signatures.Presignature C C C, is_omega_cocont (pr1 H) → hss_category CP H.
Proof.
exact @UniMath.SubstitutionSystems.LiftingInitial_alt.InitHSS.
Defined.

Lemma isInitial_InitHSS :
  ∏ (C : category) (CP : BinCoproducts C)
    (IC : Initial C) (CC : Colims_of_shape nat_graph C)
    (H : UniMath.SubstitutionSystems.Signatures.Presignature C C C)
  (HH : is_omega_cocont (pr1 H)),
  isInitial (hss_category CP H) (InitHSS C CP IC CC H HH).
Proof.
exact @UniMath.SubstitutionSystems.LiftingInitial_alt.isInitial_InitHSS.
Defined.

(** Section 4.2: Binding signatures to monads *)
Definition BindingSigToMonad :
  ∏ (C : category) (BPC : BinProducts C),
  BinCoproducts C → Terminal C → Initial C → Colims_of_shape nat_graph C
  → (∏ F, is_omega_cocont (constprod_functor1 (BinProducts_functor_precat C C BPC) F))
  → ∏ sig : BindingSig, Coproducts (BindingSigIndex sig) C
  → Monad C.
Proof.
  exact @UniMath.SubstitutionSystems.BindingSigToMonad.BindingSigToMonad.
Defined.

(** Example 50: Untyped lambda calculus *)
(* See: UniMath/SubstitutionSystems/LamFromBindingSig.v *)

(** Example 51: Raw syntax of Martin-Löf type theory *)
(* See: UniMath/SubstitutionSystems/MLTT79.v *)
