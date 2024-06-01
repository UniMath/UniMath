(******************************************************************************************

 Benabou cosmos

 In the theory of enriched categories, one often is interested in categories enriched over
 a monoidal category with sufficient structure. The reason for that is that structure on the
 category over which we enrich, allows us to do more sophisticated constructions.

 A key notion is given by the notion of a Benabou cosmos. A Benabou cosmos is given by a
 complete and cocomplete symmetric monoidal closed category. Let us understand why this
 notion is nice in the context of enriched category theory.
 - To construct the opposite of enriched categories, we assume that the category over which
   we enrich, is symmetric monoidal.
 - To construct Eilenberg-Moore categories of enriched monads, we assume that the category
   over which we enrich, has equalizers.
 - To construct the self-enriched category, we assume that the category over which we enrich,
   is symmetric monoidal closed.
 - To construct enriched functor categories, we assume that the category over which we enrich,
   is complete and symmetric monoidal closed.
 - To construct the composition of enriched profunctors, we assume that the category over
   which we enrich, is cocomplete.
 Note that from the last point, we see that to construct a double (bi)category of enriched
 categories and profunctors, we need to assume that we are enriched over a cocomplete
 monoidal category.

 A Benabou cosmos collects each of these assumptions and combines it all into one notion.

 We also define the notion of quantales. Essentially, a quantale is given by a Benabou cosmos
 that is also a posetal category (see, e.g., Section 2.1 in "A point-free perspective on lax
 extensions and predicate liftings"). Note that in this file, we define commutative quantales.

 References
 - "Elementary Cosmos I" by Street
 - "A point-free perspective on lax extensions and predicate liftings" by Goncharov, Hofmann,
   Nora, Schröder and Wild

 Contents
 1. Benabou cosmos
 2. Accessors
 3. Quantales

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Coends.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

(** * 1. Benabou cosmos *)
Definition benabou_cosmos
  : UU
  := ∑ (V : sym_mon_closed_cat),
     (∏ (I : UU), Products I V)
     ×
     Equalizers V
     ×
     (∏ (I : UU), Coproducts I V)
     ×
     Coequalizers V.

(** * 2. Accessors *)
Coercion benabou_cosmos_to_sym_mon_closed_cat
         (V : benabou_cosmos)
  : sym_mon_closed_cat.
Proof.
  exact (pr1 V).
Defined.

Definition benabou_cosmos_products
           (V : benabou_cosmos)
           (I : UU)
  : Products I V
  := pr12 V I.

Definition benabou_cosmos_binproducts
           (V : benabou_cosmos)
  : BinProducts V.
Proof.
  use BinProducts_from_Products.
  apply benabou_cosmos_products.
Defined.

Definition benabou_cosmos_equalizers
           (V : benabou_cosmos)
  : Equalizers V
  := pr122 V.

Definition benabou_cosmos_coproducts
           (V : benabou_cosmos)
           (I : UU)
  : Coproducts I V
  := pr1 (pr222 V) I.

Definition benabou_cosmos_initial
           (V : benabou_cosmos)
  : Initial V
  := initial_from_empty_coproduct V (benabou_cosmos_coproducts V ∅ _).

Definition benabou_cosmos_coequalizers
           (V : benabou_cosmos)
  : Coequalizers V
  := pr2 (pr222 V).

Definition benabou_cosmos_coends
           (V : benabou_cosmos)
           {C : category}
           (F : category_binproduct (C^opp) C ⟶ V)
  : coend_colimit F.
Proof.
  use construction_of_coends.
  - apply benabou_cosmos_coequalizers.
  - apply benabou_cosmos_coproducts.
  - apply benabou_cosmos_coproducts.
Defined.

#[global] Opaque benabou_cosmos_initial.
#[global] Opaque benabou_cosmos_coends.
#[global] Opaque benabou_cosmos_binproducts.

Definition is_initial_tensor_initial_l
           {V : benabou_cosmos}
           (v : V)
  : isInitial V (v ⊗ benabou_cosmos_initial V).
Proof.
  exact ((left_adjoint_preserves_initial
            _
            (sym_mon_closed_left_tensor_left_adjoint V v))
           _
           (pr2 (benabou_cosmos_initial V))).
Qed.

Definition is_initial_tensor_initial_r
           {V : benabou_cosmos}
           (v : V)
  : isInitial V (benabou_cosmos_initial V ⊗ v).
Proof.
  exact ((left_adjoint_preserves_initial
            _
            (sym_mon_closed_right_tensor_left_adjoint V v))
           _
           (pr2 (benabou_cosmos_initial V))).
Qed.

Definition arrow_from_tensor_initial_l_benabou_cosmos
           {V : benabou_cosmos}
           (v w : V)
  : v ⊗ benabou_cosmos_initial V --> w.
Proof.
  exact (InitialArrow
           (make_Initial
              _
              (is_initial_tensor_initial_l v))
           w).
Qed.

Definition arrow_from_tensor_initial_r_benabou_cosmos
           {V : benabou_cosmos}
           (v w : V)
  : benabou_cosmos_initial V ⊗ v --> w.
Proof.
  exact (InitialArrow
           (make_Initial
              _
              (is_initial_tensor_initial_r v))
           w).
Qed.

Proposition arrow_from_tensor_initial_l_benabou_cosmos_eq
            {V : benabou_cosmos}
            {v w : V}
            (f g : v ⊗ benabou_cosmos_initial V --> w)
  : f = g.
Proof.
  apply (@InitialArrowEq _ (make_Initial _ (is_initial_tensor_initial_l v))).
Qed.

Proposition arrow_from_tensor_initial_r_benabou_cosmos_eq
            {V : benabou_cosmos}
            {v w : V}
            (f g : benabou_cosmos_initial V ⊗ v --> w)
  : f = g.
Proof.
  apply (@InitialArrowEq _ (make_Initial _ (is_initial_tensor_initial_r v))).
Qed.

Definition is_initial_tensor_initial_1
           {V : benabou_cosmos}
           (v₁ v₂ : V)
  : isInitial V (benabou_cosmos_initial V ⊗ v₁ ⊗ v₂).
Proof.
  refine ((left_adjoint_preserves_initial
             _
             (sym_mon_closed_right_tensor_left_adjoint V _))
            _
            _).
  apply is_initial_tensor_initial_r.
Qed.

Proposition arrow_from_tensor_initial_1_benabou_cosmos_eq
            {V : benabou_cosmos}
            {v₁ v₂ w : V}
            (f g : benabou_cosmos_initial V ⊗ v₁ ⊗ v₂ --> w)
  : f = g.
Proof.
  apply (@InitialArrowEq _ (make_Initial _ (is_initial_tensor_initial_1 _ _))).
Qed.

Definition is_initial_tensor_initial_2
           {V : benabou_cosmos}
           (v₁ v₂ : V)
  : isInitial V (v₁ ⊗ benabou_cosmos_initial V ⊗ v₂).
Proof.
  refine ((left_adjoint_preserves_initial
             _
             (sym_mon_closed_right_tensor_left_adjoint V _))
            _
            _).
  apply is_initial_tensor_initial_l.
Qed.

Proposition arrow_from_tensor_initial_2_benabou_cosmos_eq
            {V : benabou_cosmos}
            {v₁ v₂ w : V}
            (f g : v₁ ⊗ benabou_cosmos_initial V ⊗ v₂ --> w)
  : f = g.
Proof.
  apply (@InitialArrowEq _ (make_Initial _ (is_initial_tensor_initial_2 _ _))).
Qed.

Definition is_initial_tensor_initial_3
           {V : benabou_cosmos}
           (v₁ v₂ : V)
  : isInitial V (v₁ ⊗ (v₂ ⊗ benabou_cosmos_initial V)).
Proof.
  refine ((left_adjoint_preserves_initial
             _
             (sym_mon_closed_left_tensor_left_adjoint V _))
            _
            _).
  apply is_initial_tensor_initial_l.
Qed.

Proposition arrow_from_tensor_initial_3_benabou_cosmos_eq
            {V : benabou_cosmos}
            {v₁ v₂ w : V}
            (f g : v₁ ⊗ (v₂ ⊗ benabou_cosmos_initial V) --> w)
  : f = g.
Proof.
  apply (@InitialArrowEq _ (make_Initial _ (is_initial_tensor_initial_3 _ _))).
Qed.

Definition arrow_from_tensor_coproduct_benabou_cosmos
           {V : benabou_cosmos}
           {v w : V}
           {I : UU}
           {D : I → V}
           (fs : ∏ (i : I), v ⊗ D i --> w)
  : v ⊗ benabou_cosmos_coproducts V I D --> w.
Proof.
  use (CoproductArrow
         _ _
         (make_Coproduct
            _ _ _ _ _
            (left_adjoint_preserves_coproduct
               _
               (sym_mon_closed_left_tensor_left_adjoint V v)
               I
               _ _ _
               (isCoproduct_Coproduct _ _ (benabou_cosmos_coproducts V I D))))).
  exact fs.
Qed.

(** * 3. Quantales *)
Definition quantale_cosmos
  : UU
  := ∑ (V : benabou_cosmos)
       (HV : is_univalent V),
     is_poset_category (_ ,, HV).

Coercion quantale_cosmos_to_benabou_cosmos
         (V : quantale_cosmos)
  : benabou_cosmos.
Proof.
  exact (pr1 V).
Defined.

Proposition is_univalent_quantale_cosmos
            (V : quantale_cosmos)
  : is_univalent V.
Proof.
  exact (pr12 V).
Defined.

Definition univalent_category_of_quantale_cosmos
           (V : quantale_cosmos)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact V.
  - exact (is_univalent_quantale_cosmos V).
Defined.

Proposition is_poset_category_quantale_cosmos
            (V : quantale_cosmos)
  : is_poset_category (_ ,, is_univalent_quantale_cosmos V).
Proof.
  exact (pr22 V).
Defined.
