(*********************************************************************************

 Colimits of categories

 Contents:
 1. Initial object
 2. Coproducts
 3. Extensivity

 *********************************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.CategorySum.
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.Colimits.Coproducts.
Require Import UniMath.Bicategories.Colimits.Extensive.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.
Require Import UniMath.Bicategories.Limits.CommaObjects.
Require Import UniMath.Bicategories.Limits.Examples.BicatOfUnivCatsLimits.

Local Open Scope cat.

(**
 1. Initial object
 *)
Definition empty_category_is_biinitial
  : @is_biinitial bicat_of_univ_cats empty_category.
Proof.
  use make_is_biinitial.
  - exact (λ C, functor_from_empty (pr1 C)).
  - exact (λ _ F G, nat_trans_from_empty F G).
  - abstract
      (intros Y f g α β ;
       use nat_trans_eq ; [ apply homset_property | ] ;
       exact (λ z, fromempty z)).
Defined.

Definition biinitial_obj_bicat_of_univ_cats
  : biinitial_obj bicat_of_univ_cats
  := empty_category ,, empty_category_is_biinitial.

Definition strict_biinitial_univ_cats
  : @is_strict_biinitial_obj bicat_of_univ_cats empty_category.
Proof.
  refine (empty_category_is_biinitial ,, _).
  intros C F.
  use equiv_to_adjequiv.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, _)).
  - exact (functor_from_empty _).
  - apply nat_trans_to_empty.
  - exact (nat_trans_from_empty _ _).
  - use is_nat_iso_to_is_invertible_2cell.
    apply nat_trans_to_empty_is_nat_iso.
  - use is_nat_iso_to_is_invertible_2cell.
    intro z.
    apply (fromempty z).
Defined.

(**
 2. Coproducts
 *)
Definition bincoprod_cocone_bicat_of_univ_cats
           (C₁ C₂ : bicat_of_univ_cats)
  : bincoprod_cocone C₁ C₂.
Proof.
  use make_bincoprod_cocone.
  - exact (bincoprod_of_univalent_category C₁ C₂).
  - exact (inl_functor (pr1 C₁) (pr1 C₂)).
  - exact (inr_functor (pr1 C₁) (pr1 C₂)).
Defined.

Section BincoprodUMP.
  Context (C₁ C₂ : bicat_of_univ_cats).

  Definition has_bincoprod_ump_1_bicat_of_univ_cats
    : bincoprod_ump_1 (bincoprod_cocone_bicat_of_univ_cats C₁ C₂).
  Proof.
    intros Q.
    use make_bincoprod_1cell.
    - exact (sum_of_functors
               (bincoprod_cocone_inl Q)
               (bincoprod_cocone_inr Q)).
    - use nat_iso_to_invertible_2cell.
      exact (sum_of_functor_inl_nat_iso
               (bincoprod_cocone_inl Q)
               (bincoprod_cocone_inr Q)).
    - use nat_iso_to_invertible_2cell.
      exact (sum_of_functor_inr_nat_iso
               (bincoprod_cocone_inl Q)
               (bincoprod_cocone_inr Q)).
  Defined.

  Definition has_bincoprod_ump_2_bicat_of_univ_cats_unique
             {Q : bicat_of_univ_cats}
             {F G : bincoprod_cocone_bicat_of_univ_cats C₁ C₂ --> Q}
             (α : bincoprod_cocone_inl (bincoprod_cocone_bicat_of_univ_cats C₁ C₂) · F
                  ==>
                  bincoprod_cocone_inl (bincoprod_cocone_bicat_of_univ_cats C₁ C₂) · G)
             (β : bincoprod_cocone_inr (bincoprod_cocone_bicat_of_univ_cats C₁ C₂) · F
                  ==>
                  bincoprod_cocone_inr (bincoprod_cocone_bicat_of_univ_cats C₁ C₂) · G)
    : isaprop
        (∑ γ,
         bincoprod_cocone_inl (bincoprod_cocone_bicat_of_univ_cats C₁ C₂) ◃ γ = α
         ×
         bincoprod_cocone_inr (bincoprod_cocone_bicat_of_univ_cats C₁ C₂) ◃ γ = β).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ].
    use nat_trans_eq ; [ apply homset_property | ].
    intro z ; induction z as [ x | y ].
    - exact (nat_trans_eq_pointwise (pr12 φ₁) x @ !(nat_trans_eq_pointwise (pr12 φ₂) x)).
    - exact (nat_trans_eq_pointwise (pr22 φ₁) y @ !(nat_trans_eq_pointwise (pr22 φ₂) y)).
  Qed.

  Definition has_bincoprod_ump_2_bicat_of_univ_cats
    : bincoprod_ump_2 (bincoprod_cocone_bicat_of_univ_cats C₁ C₂).
  Proof.
    intros Q F G α β.
    use iscontraprop1.
    - exact (has_bincoprod_ump_2_bicat_of_univ_cats_unique α β).
    - simple refine (_ ,, _ ,, _).
      + exact (sum_of_nat_trans α β).
      + exact (sum_of_nat_trans_inl α β).
      + exact (sum_of_nat_trans_inr α β).
  Defined.

  Definition has_bincoprod_ump_bicat_of_univ_cats
    : has_bincoprod_ump (bincoprod_cocone_bicat_of_univ_cats C₁ C₂).
  Proof.
    split.
    - exact has_bincoprod_ump_1_bicat_of_univ_cats.
    - exact has_bincoprod_ump_2_bicat_of_univ_cats.
  Defined.
End BincoprodUMP.

Definition bincoprod_bicat_of_univ_cats
  : has_bincoprod bicat_of_univ_cats
  := λ C₁ C₂,
     bincoprod_cocone_bicat_of_univ_cats C₁ C₂
     ,,
     has_bincoprod_ump_bicat_of_univ_cats C₁ C₂.

Definition bicat_of_univ_cats_with_biinitial_bincoprod
  : bicat_with_biinitial_bincoprod
  := bicat_of_univ_cats ,, biinitial_obj_bicat_of_univ_cats ,, bincoprod_bicat_of_univ_cats.

(**
 3. Extensivity
 *)
Section DisjointCoproducts.
  Context (C₁ C₂ : bicat_of_univ_cats_with_biinitial_bincoprod).

  Notation "∁" := bicat_of_univ_cats_with_biinitial_bincoprod.

  Let R := @biinitial_comma_cone
             ∁
             C₁ C₂
             (pr1 (bincoprod_of ∁ C₁ C₂))
             (inl_functor _ _)
             (inr_functor _ _).

  Section OneCell.
    Context (Q : @comma_cone
                   ∁
                   C₁ C₂
                   (pr1 (bincoprod_of ∁ C₁ C₂))
                   (inl_functor _ _)
                   (inr_functor _ _)).

    Definition bicat_of_univ_cats_inl_inr_1cell_functor_data
      : functor_data (pr11 Q) (pr11 R).
    Proof.
      use make_functor_data.
      - exact (λ q, pr1 (comma_cone_cell Q) q).
      - exact (λ q _ _, fromempty (pr1 (comma_cone_cell Q) q)).
    Defined.

    Definition bicat_of_univ_cats_inl_inr_1cell_functor_is_functor
      : is_functor bicat_of_univ_cats_inl_inr_1cell_functor_data.
    Proof.
      split.
      - intro q.
        exact (fromempty (pr1 (comma_cone_cell Q) q)).
      - intros q ? ? ? ?.
        exact (fromempty (pr1 (comma_cone_cell Q) q)).
    Qed.

    Definition bicat_of_univ_cats_inl_inr_1cell_functor
      : Q --> R.
    Proof.
      use make_functor.
      - exact bicat_of_univ_cats_inl_inr_1cell_functor_data.
      - exact bicat_of_univ_cats_inl_inr_1cell_functor_is_functor.
    Defined.

    Definition bicat_of_univ_cats_inl_inr_1cell_pr1_nat_trans
      : bicat_of_univ_cats_inl_inr_1cell_functor · comma_cone_pr1 R
        ==>
        comma_cone_pr1 Q.
    Proof.
      use make_nat_trans.
      - intro q.
        exact (fromempty (pr1 (comma_cone_cell Q) q)).
      - abstract
          (intros q ? ? ;
           exact (fromempty (pr1 (comma_cone_cell Q) q))).
    Defined.

    Definition bicat_of_univ_cats_inl_inr_1cell_pr1
      : nat_iso
          (bicat_of_univ_cats_inl_inr_1cell_functor · comma_cone_pr1 R)
          (comma_cone_pr1 Q).
    Proof.
      use make_nat_iso.
      - exact bicat_of_univ_cats_inl_inr_1cell_pr1_nat_trans.
      - intro q.
        exact (fromempty (pr1 (comma_cone_cell Q) q)).
    Defined.

    Definition bicat_of_univ_cats_inl_inr_1cell_pr2_nat_trans
      : bicat_of_univ_cats_inl_inr_1cell_functor · comma_cone_pr2 R
        ==>
        comma_cone_pr2 Q.
    Proof.
      use make_nat_trans.
      - intro q.
        exact (fromempty (pr1 (comma_cone_cell Q) q)).
      - abstract
          (intros q ? ? ;
           exact (fromempty (pr1 (comma_cone_cell Q) q))).
    Defined.

    Definition bicat_of_univ_cats_inl_inr_1cell_pr2
      : nat_iso
          (bicat_of_univ_cats_inl_inr_1cell_functor · comma_cone_pr2 R)
          (comma_cone_pr2 Q).
    Proof.
      use make_nat_iso.
      - exact bicat_of_univ_cats_inl_inr_1cell_pr2_nat_trans.
      - intro q.
        exact (fromempty (pr1 (comma_cone_cell Q) q)).
    Defined.

    Definition bicat_of_univ_cats_inl_inr_1cell
      : comma_1cell Q R.
    Proof.
      use make_comma_1cell.
      + exact bicat_of_univ_cats_inl_inr_1cell_functor.
      + use nat_iso_to_invertible_2cell.
        exact bicat_of_univ_cats_inl_inr_1cell_pr1.
      + use nat_iso_to_invertible_2cell.
        exact bicat_of_univ_cats_inl_inr_1cell_pr2.
      + abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intro q ;
           exact (fromempty (pr1 (comma_cone_cell Q) q))).
    Defined.
  End OneCell.

  Definition bicat_of_univ_cats_inl_inr
    : has_comma_ump R.
  Proof.
    split.
    - exact bicat_of_univ_cats_inl_inr_1cell.
    - intros Q φ ψ α β p.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros τ₁ τ₂ ;
           use subtypePath ;
           [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
           use nat_trans_eq ;
           [ apply homset_property | ] ;
           intros q ;
           exact (fromempty (pr1 φ q))).
      + simple refine (_ ,, _ ,, _).
        * use make_nat_trans.
          ** intros q.
             exact (fromempty (pr1 φ q)).
          ** abstract
               (intros q ? ? ;
                exact (fromempty (pr1 φ q))).
        * abstract
            (use nat_trans_eq ; [ apply homset_property | ] ;
             intros q ;
             exact (fromempty (pr1 φ q))).
        * abstract
            (use nat_trans_eq ; [ apply homset_property | ] ;
             intros q ;
             exact (fromempty (pr1 φ q))).
  Defined.

  Let R' := @biinitial_comma_cone
              ∁
              C₂ C₁
              (pr1 (bincoprod_of ∁ C₁ C₂))
              (inr_functor _ _)
              (inl_functor _ _).

  Section OneCell.
    Context (Q : @comma_cone
                   ∁
                   C₂ C₁
                   (pr1 (bincoprod_of ∁ C₁ C₂))
                   (inr_functor _ _)
                   (inl_functor _ _)).

    Definition bicat_of_univ_cats_inr_inl_1cell_functor_data
      : functor_data (pr11 Q) (pr11 R').
    Proof.
      use make_functor_data.
      - exact (λ q, pr1 (comma_cone_cell Q) q).
      - exact (λ q _ _, fromempty (pr1 (comma_cone_cell Q) q)).
    Defined.

    Definition bicat_of_univ_cats_inr_inl_1cell_functor_is_functor
      : is_functor bicat_of_univ_cats_inr_inl_1cell_functor_data.
    Proof.
      split.
      - intro q.
        exact (fromempty (pr1 (comma_cone_cell Q) q)).
      - intros q ? ? ? ?.
        exact (fromempty (pr1 (comma_cone_cell Q) q)).
    Qed.

    Definition bicat_of_univ_cats_inr_inl_1cell_functor
      : Q --> R.
    Proof.
      use make_functor.
      - exact bicat_of_univ_cats_inr_inl_1cell_functor_data.
      - exact bicat_of_univ_cats_inr_inl_1cell_functor_is_functor.
    Defined.

    Definition bicat_of_univ_cats_inr_inl_1cell_pr1_nat_trans
      : bicat_of_univ_cats_inr_inl_1cell_functor · comma_cone_pr1 R'
        ==>
        comma_cone_pr1 Q.
    Proof.
      use make_nat_trans.
      - intro q.
        exact (fromempty (pr1 (comma_cone_cell Q) q)).
      - abstract
          (intros q ? ? ;
           exact (fromempty (pr1 (comma_cone_cell Q) q))).
    Defined.

    Definition bicat_of_univ_cats_inr_inl_1cell_pr1
      : nat_iso
          (bicat_of_univ_cats_inr_inl_1cell_functor · comma_cone_pr1 R')
          (comma_cone_pr1 Q).
    Proof.
      use make_nat_iso.
      - exact bicat_of_univ_cats_inr_inl_1cell_pr1_nat_trans.
      - intro q.
        exact (fromempty (pr1 (comma_cone_cell Q) q)).
    Defined.

    Definition bicat_of_univ_cats_inr_inl_1cell_pr2_nat_trans
      : bicat_of_univ_cats_inr_inl_1cell_functor · comma_cone_pr2 R'
        ==>
        comma_cone_pr2 Q.
    Proof.
      use make_nat_trans.
      - intro q.
        exact (fromempty (pr1 (comma_cone_cell Q) q)).
      - abstract
          (intros q ? ? ;
           exact (fromempty (pr1 (comma_cone_cell Q) q))).
    Defined.

    Definition bicat_of_univ_cats_inr_inl_1cell_pr2
      : nat_iso
          (bicat_of_univ_cats_inr_inl_1cell_functor · comma_cone_pr2 R')
          (comma_cone_pr2 Q).
    Proof.
      use make_nat_iso.
      - exact bicat_of_univ_cats_inr_inl_1cell_pr2_nat_trans.
      - intro q.
        exact (fromempty (pr1 (comma_cone_cell Q) q)).
    Defined.

    Definition bicat_of_univ_cats_inr_inl_1cell
      : comma_1cell Q R'.
    Proof.
      use make_comma_1cell.
      + exact bicat_of_univ_cats_inr_inl_1cell_functor.
      + use nat_iso_to_invertible_2cell.
        exact bicat_of_univ_cats_inr_inl_1cell_pr1.
      + use nat_iso_to_invertible_2cell.
        exact bicat_of_univ_cats_inr_inl_1cell_pr2.
      + abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intro q ;
           exact (fromempty (pr1 (comma_cone_cell Q) q))).
    Defined.
  End OneCell.

  Definition bicat_of_univ_cats_inr_inl
    : has_comma_ump R'.
  Proof.
    split.
    - exact bicat_of_univ_cats_inr_inl_1cell.
    - intros Q φ ψ α β p.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros τ₁ τ₂ ;
           use subtypePath ;
           [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
           use nat_trans_eq ;
           [ apply homset_property | ] ;
           intros q ;
           exact (fromempty (pr1 φ q))).
      + simple refine (_ ,, _ ,, _).
        * use make_nat_trans.
          ** intros q.
             exact (fromempty (pr1 φ q)).
          ** abstract
               (intros q ? ? ;
                exact (fromempty (pr1 φ q))).
        * abstract
            (use nat_trans_eq ; [ apply homset_property | ] ;
             intros q ;
             exact (fromempty (pr1 φ q))).
        * abstract
            (use nat_trans_eq ; [ apply homset_property | ] ;
             intros q ;
             exact (fromempty (pr1 φ q))).
  Defined.
End DisjointCoproducts.

Section UniversalCoproducts.
  Notation "∁" := bicat_of_univ_cats_with_biinitial_bincoprod.

  Context {C₁ C₂ Z : ∁}
          (F : Z --> pr1 (bincoprod_of ∁ C₁ C₂)).

  Let ι₁ : C₁ --> pr1 (bincoprod_of ∁ C₁ C₂)
    := inl_functor (pr1 C₁) (pr1 C₂).
  Let ι₂ : C₂ --> pr1 (bincoprod_of ∁ C₁ C₂)
    := inr_functor (pr1 C₁) (pr1 C₂).

  Let κ₁ : bicat_of_univ_cats ⟦ univalent_iso_comma ι₁ F , Z ⟧
    := iso_comma_pr2 _ _.
  Let κ₂ : bicat_of_univ_cats ⟦ univalent_iso_comma ι₂ F , Z ⟧
    := iso_comma_pr2 _ _.

  Section UniversalCoproductsOne.
    Context (W : @bincoprod_cocone
                   bicat_of_univ_cats
                   (univalent_iso_comma ι₁ F)
                   (univalent_iso_comma ι₂ F)).

    Local Definition pb_of_sum_cats_ob
          {z : pr1 Z}
          {q : pr111 (bincoprod_of ∁ C₁ C₂)}
          (i : iso q (pr1 F z))
      : pr11 W.
    Proof.
      induction q as [ x | y ].
      - apply (bincoprod_cocone_inl W).
        exact ((x ,, z) ,, i).
      - apply (bincoprod_cocone_inr W).
        exact ((y ,, z) ,, i).
    Defined.

    Notation "'H₀'" := pb_of_sum_cats_ob.

    Local Definition pb_of_sum_cats_mor
          {z₁ z₂ : pr1 Z}
          (f : z₁ --> z₂)
          {q₁ q₂ : pr111 (bincoprod_of ∁ C₁ C₂)}
          (g : q₁ --> q₂)
          (i₁ : iso q₁ (pr1 F z₁))
          (i₂ : iso q₂ (pr1 F z₂))
          (p : g · i₂ = i₁ · # (pr1 F) f)
      : H₀ i₁ --> H₀ i₂.
    Proof.
      induction q₁ as [ x₁ | y₁ ] ; induction q₂ as [ x₂ | y₂ ] ; cbn.
      - use (#(pr1 (bincoprod_cocone_inl W))).
        exact ((g ,, f) ,, p).
      - exact (fromempty g).
      - exact (fromempty g).
      - use (#(pr1 (bincoprod_cocone_inr W))).
        exact ((g ,, f) ,, p).
    Defined.

    Local Notation "'H₁'" := pb_of_sum_cats_mor.

    Local Definition pb_of_sum_cats_mor_eq
          {z₁ z₂ : pr1 Z}
          (f : z₁ --> z₂)
          {q₁ q₂ : pr111 (bincoprod_of ∁ C₁ C₂)}
          {g₁ g₂ : q₁ --> q₂}
          (p : g₁ = g₂)
          (i₁ : iso q₁ (pr1 F z₁))
          (i₂ : iso q₂ (pr1 F z₂))
          (r₁ : g₁ · i₂ = i₁ · # (pr1 F) f)
          (r₂ : g₂ · i₂ = i₁ · # (pr1 F) f)
      : H₁ f g₁ i₁ i₂ r₁
        =
        H₁ f g₂ i₁ i₂ r₂.
    Proof.
      induction p ; cbn.
      apply maponpaths.
      apply homset_property.
    Qed.

    Local Definition pb_of_sum_cats_data
      : functor_data (pr1 Z) (pr11 W).
    Proof.
      use make_functor_data.
      - exact (λ z, H₀ (identity_iso (pr1 F z))).
      - refine (λ z₁ z₂ f,
                H₁ f (#(pr1 F) f) (identity_iso _) (identity_iso _) _).
        abstract
          (rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Local Lemma pb_of_sum_cats_id
          (z : pr1 Z)
          (q : pr111 (bincoprod_of ∁ C₁ C₂))
          (i : iso q (pr1 F z))
          (p : id₁ q · i = i · # (pr1 F) (id₁ z))
      : H₁ (identity z) (identity q) i i p
        =
        identity _.
    Proof.
      induction q as [ x | y ] ; cbn.
      - refine (_ @ functor_id (bincoprod_cocone_inl W) _).
        apply maponpaths ; cbn.
        apply maponpaths.
        apply (homset_property
                 (pr111 (bincoprod_of ∁ C₁ C₂))
                 (inl x)
                 (pr1 F z)).
      - refine (_ @ functor_id (bincoprod_cocone_inr W) _).
        apply maponpaths ; cbn.
        apply maponpaths.
        apply (homset_property
                 (pr111 (bincoprod_of ∁ C₁ C₂))
                 (inr y)
                 (pr1 F z)).
    Qed.

    Local Lemma pb_of_sum_cats_comp
          {z₁ z₂ z₃ : pr1 Z}
          (f : z₁ --> z₂)
          (g : z₂ --> z₃)
          {q₁ q₂ q₃ : pr111 (bincoprod_of ∁ C₁ C₂)}
          (ff : q₁ --> q₂)
          (gg : q₂ --> q₃)
          (i₁ : iso q₁ (pr1 F z₁))
          (i₂ : iso q₂ (pr1 F z₂))
          (i₃ : iso q₃ (pr1 F z₃))
          (p₁ : ff · gg · i₃ = i₁ · # (pr1 F) (f · g))
          (p₂ : ff · i₂ = i₁ · # (pr1 F) f)
          (p₃ : gg · i₃ = i₂ · # (pr1 F) g)
      : H₁ (f · g) (ff · gg) i₁ i₃ p₁
        =
        H₁ f ff i₁ i₂ p₂ · H₁ g gg i₂ i₃ p₃.
    Proof.
      induction q₁ as [ x₁ | y₁ ] ;
      induction q₂ as [ x₂ | y₂ ] ;
      induction q₃ as [ x₃ | y₃ ] ; cbn.
      - refine (_ @ functor_comp _ _ _).
        apply maponpaths ; cbn.
        apply maponpaths.
        apply (homset_property (pr111 (bincoprod_of ∁ C₁ C₂)) (inl x₁)).
      - apply (fromempty gg).
      - apply (fromempty gg).
      - apply (fromempty ff).
      - apply (fromempty ff).
      - apply (fromempty gg).
      - apply (fromempty gg).
      - refine (_ @ functor_comp _ _ _).
        apply maponpaths ; cbn.
        apply maponpaths.
        apply (homset_property (pr111 (bincoprod_of ∁ C₁ C₂)) (inr y₁)).
    Qed.

    Local Lemma pb_of_sum_cats_is_functor
      : is_functor pb_of_sum_cats_data.
    Proof.
      split.
      - intro z ; cbn.
        simple refine (_ @ pb_of_sum_cats_id z (pr1 F z) (identity_iso _) _).
        + use pb_of_sum_cats_mor_eq.
          apply functor_id.
        + exact (id_left _ @ !(functor_id _ _) @ !(id_left _)).
      - intros z₁ z₂ z₃ f g ; cbn.
        simple refine (_ @ pb_of_sum_cats_comp _ _ _ _ _ _ _ _ _ _).
        + use pb_of_sum_cats_mor_eq.
          apply functor_comp.
        + refine (id_right _ @ !_ @ !(id_left _)).
          apply functor_comp.
    Qed.

    Local Definition pb_of_sum_cats
      : Z --> W.
    Proof.
      use make_functor.
      - exact pb_of_sum_cats_data.
      - exact pb_of_sum_cats_is_functor.
    Defined.

    Local Definition pb_of_cats_iso_mor
          (z : pr1 Z)
          (q₁ q₂ : pr111 (bincoprod_of ∁ C₁ C₂))
          (i₁ : iso q₁ (pr1 F z))
          (i₂ : iso q₂ (pr1 F z))
          (k : q₁ --> q₂)
          (p : k · i₂ = i₁)
      : H₀ i₁ --> H₀ i₂.
    Proof.
      induction q₁ as [ x₁ | y₁ ] ; induction q₂ as [ x₂ | y₂ ].
      - cbn.
        refine (#(pr1 (bincoprod_cocone_inl W)) _).
        simple refine ((k ,, identity _) ,, _).
        abstract
          (simpl ;
           refine (_ @ maponpaths (λ z, i₁ · z) (!(functor_id F z))) ;
           refine (_ @ !(id_right _)) ;
           exact p).
      - apply fromempty.
        exact (pr1 i₁ · inv_from_iso i₂).
      - apply fromempty.
        exact (pr1 i₁ · inv_from_iso i₂).
      - cbn.
        refine (#(pr1 (bincoprod_cocone_inr W)) _).
        simple refine ((k ,, identity _) ,, _).
        abstract
          (simpl ;
           refine (_ @ maponpaths (λ z, i₁ · z) (!(functor_id F z))) ;
           refine (_ @ !(id_right _)) ;
           exact p).
    Defined.

    Local Definition pb_of_cats_is_iso
          (z : pr1 Z)
          (q₁ q₂ : pr111 (bincoprod_of ∁ C₁ C₂))
          (i₁ : iso q₁ (pr1 F z))
          (i₂ : iso q₂ (pr1 F z))
          (k : iso q₁ q₂)
          (p : pr1 k · i₂ = i₁)
      : is_iso (pb_of_cats_iso_mor z q₁ q₂ i₁ i₂ k p).
    Proof.
      induction q₁ as [ x₁ | y₁ ] ; induction q₂ as [ x₂ | y₂ ].
      - use functor_on_is_iso_is_iso.
        use is_iso_iso_comma.
        + cbn.
          use is_iso_qinv ; [ | split ].
          * exact (inv_from_iso k).
          * apply (iso_inv_after_iso k).
          * apply (iso_after_iso_inv k).
        + cbn.
          apply identity_is_iso.
      - apply fromempty.
        exact (pr1 i₁ · inv_from_iso i₂).
      - apply fromempty.
        exact (pr1 i₁ · inv_from_iso i₂).
      - use functor_on_is_iso_is_iso.
        use is_iso_iso_comma.
        + cbn.
          use is_iso_qinv ; [ | split ].
          * exact (inv_from_iso k).
          * apply (iso_inv_after_iso k).
          * apply (iso_after_iso_inv k).
        + cbn.
          apply identity_is_iso.
    Defined.

    Local Definition pb_of_sum_cats_iso
          (z : pr1 Z)
          (q : pr111 (bincoprod_of ∁ C₁ C₂))
          (i : iso q (pr1 F z))
      : iso (H₀ (identity_iso (pr1 F z))) (H₀ i).
    Proof.
      use make_iso.
      - use pb_of_cats_iso_mor.
        + exact (iso_inv_from_iso i).
        + simpl.
          exact (iso_after_iso_inv i).
      - apply pb_of_cats_is_iso.
    Defined.

    Local Definition pb_of_sum_cats_inl_data
      : nat_trans_data
          (κ₁ ∙ pb_of_sum_cats)
          (pr1 (bincoprod_cocone_inl W))
      := λ z, pb_of_sum_cats_iso (pr21 z) _ (pr2 z).

    Local Lemma pb_of_sum_cats_nat_trans_help
          {z₁ z₂ : pr1 Z}
          (f : z₁ --> z₂)
          {q₁ q₂ q₃ q₄ : pr111 (bincoprod_of ∁ C₁ C₂)}
          (g₁ : q₁ --> q₂)
          (g₂ : q₂ --> q₃)
          (g₃ : q₃ --> q₄)
          (i₁ : iso q₁ (pr1 F z₁))
          (i₂ : iso q₂ (pr1 F z₁))
          (i₃ : iso q₃ (pr1 F z₂))
          (i₄ : iso q₄ (pr1 F z₂))
          (p₁ : g₁ · i₂ = i₁)
          (p₂ : g₃ · i₄ = i₃)
          (r₁ : g₁ · g₂ · i₃ = i₁ · # (pr1 F) f)
          (r₂ : g₂ · g₃ · i₄ = i₂ · # (pr1 F) f)
      : H₁ f (g₁ · g₂) i₁ i₃ r₁
        · pb_of_cats_iso_mor z₂ q₃ q₄ i₃ i₄ g₃ p₂
        =
        pb_of_cats_iso_mor z₁ q₁ q₂ i₁ i₂ g₁ p₁
        · H₁ f (g₂ · g₃) i₂ i₄ r₂.
    Proof.
      induction q₁, q₂, q₃, q₄ ; cbn.
      - refine (!functor_comp _ _ _ @ _ @ functor_comp _ _ _).
        apply maponpaths.
        use subtypePath ; [ intro ; apply homset_property | ].
        cbn.
        use pathsdirprod.
        + rewrite assoc.
          apply idpath.
        + rewrite id_left, id_right.
          apply idpath.
      - exact (fromempty g₃).
      - exact (fromempty g₂).
      - exact (fromempty g₂).
      - exact (fromempty g₂).
      - exact (fromempty g₂).
      - exact (fromempty g₁).
      - exact (fromempty g₁).
      - exact (fromempty g₁).
      - exact (fromempty g₁).
      - exact (fromempty g₁).
      - exact (fromempty g₁).
      - exact (fromempty g₂).
      - exact (fromempty g₂).
      - exact (fromempty g₃).
      - refine (!functor_comp _ _ _ @ _ @ functor_comp _ _ _).
        apply maponpaths.
        use subtypePath ; [ intro ; apply homset_property | ].
        cbn.
        use pathsdirprod.
        + rewrite assoc.
          apply idpath.
        + rewrite id_left, id_right.
          apply idpath.
    Qed.

    Local Lemma pb_of_sum_cats_inl_is_nat_trans
      : is_nat_trans _ _ pb_of_sum_cats_inl_data.
    Proof.
      intros x y f.
      cbn.
      simple refine (maponpaths (λ z, z · _) _
                     @ pb_of_sum_cats_nat_trans_help
                         (pr21 f)
                         (inv_from_iso (pr2 x))
                         (pr12 x · # (pr1 F) (pr21 f))
                         (inv_from_iso (pr2 y))
                         (identity_iso (pr1 F (pr21 x)))
                         (pr2 x)
                         (identity_iso (pr1 F (pr21 y)))
                         (pr2 y)
                         (iso_after_iso_inv _)
                         (iso_after_iso_inv _)
                         _
                         _
                     @ maponpaths (λ z, _ · z) _).
      - use pb_of_sum_cats_mor_eq.
        rewrite !assoc.
        rewrite iso_after_iso_inv.
        rewrite id_left.
        apply idpath.
      - abstract
          (rewrite id_left, id_right ;
           rewrite assoc ;
           rewrite iso_after_iso_inv ;
           apply id_left).
      - abstract
          (rewrite !assoc' ;
           rewrite iso_after_iso_inv ;
           rewrite id_right ;
           apply idpath).
      - use pb_of_sum_cats_mor_eq.
        pose (pr2 f) as p.
        simpl in p.
        etrans.
        {
          apply maponpaths_2.
          exact (!p).
        }
        rewrite !assoc'.
        rewrite iso_inv_after_iso.
        apply id_right.
    Qed.

    Local Definition pb_of_sum_cats_inl_nat_trans
      : κ₁ ∙ pb_of_sum_cats ⟹ pr1 (bincoprod_cocone_inl W).
    Proof.
      use make_nat_trans.
      - exact pb_of_sum_cats_inl_data.
      - exact pb_of_sum_cats_inl_is_nat_trans.
    Defined.

    Local Definition pb_of_sum_cats_inl
      : nat_iso
          (κ₁ ∙ pb_of_sum_cats)
          (bincoprod_cocone_inl W).
    Proof.
      use make_nat_iso.
      - exact pb_of_sum_cats_inl_nat_trans.
      - intro.
        apply iso_is_iso.
    Defined.

    Local Definition pb_of_sum_cats_inr_data
      : nat_trans_data
          (κ₂ ∙ pb_of_sum_cats)
          (pr1 (bincoprod_cocone_inr W))
      := λ z, pb_of_sum_cats_iso (pr21 z) _ (pr2 z).

    Local Lemma pb_of_sum_cats_inr_is_nat_trans
      : is_nat_trans _ _ pb_of_sum_cats_inr_data.
    Proof.
      intros x y f.
      cbn.
      simple refine (maponpaths (λ z, z · _) _
                     @ pb_of_sum_cats_nat_trans_help
                         (pr21 f)
                         (inv_from_iso (pr2 x))
                         (pr12 x · # (pr1 F) (pr21 f))
                         (inv_from_iso (pr2 y))
                         (identity_iso (pr1 F (pr21 x)))
                         (pr2 x)
                         (identity_iso (pr1 F (pr21 y)))
                         (pr2 y)
                         (iso_after_iso_inv _)
                         (iso_after_iso_inv _)
                         _
                         _
                     @ maponpaths (λ z, _ · z) _).
      - use pb_of_sum_cats_mor_eq.
        rewrite !assoc.
        rewrite iso_after_iso_inv.
        rewrite id_left.
        apply idpath.
      - abstract
          (rewrite id_left, id_right ;
           rewrite assoc ;
           rewrite iso_after_iso_inv ;
           apply id_left).
      - abstract
          (rewrite !assoc' ;
           rewrite iso_after_iso_inv ;
           rewrite id_right ;
           apply idpath).
      - use pb_of_sum_cats_mor_eq.
        pose (pr2 f) as p.
        simpl in p.
        etrans.
        {
          apply maponpaths_2.
          exact (!p).
        }
        rewrite !assoc'.
        rewrite iso_inv_after_iso.
        apply id_right.
    Qed.

    Local Definition pb_of_sum_cats_inr_nat_trans
      : κ₂ ∙ pb_of_sum_cats ⟹ pr1 (bincoprod_cocone_inr W).
    Proof.
      use make_nat_trans.
      - exact pb_of_sum_cats_inr_data.
      - exact pb_of_sum_cats_inr_is_nat_trans.
    Defined.

    Local Definition pb_of_sum_cats_inr
      : nat_iso
          (κ₂ ∙ pb_of_sum_cats)
          (bincoprod_cocone_inr W).
    Proof.
      use make_nat_iso.
      - exact pb_of_sum_cats_inr_nat_trans.
      - intro.
        apply iso_is_iso.
    Defined.
  End UniversalCoproductsOne.

  Section UniversalCoproductsTwo.
    Context {W : ∁}
            {φ ψ : ∁ ⟦ make_bincoprod_cocone Z κ₁ κ₂, W ⟧}
            (α : κ₁ · φ ==> κ₁ · ψ)
            (β : κ₂ · φ ==> κ₂ · ψ).

    Local Definition pb_of_sum_cats_nat_trans_ob
          (z : pr1 Z)
          (q : pr111 (bincoprod_of ∁ C₁ C₂))
          (i : iso q (pr1 F z))
      : pr1 φ z --> pr1 ψ z.
    Proof.
      induction q as [ x | y ].
      - exact (pr1 α ((x ,, z) ,, i)).
      - exact (pr1 β ((y ,, z) ,, i)).
    Defined.

    Local Definition pb_of_sum_cats_nat_trans_data
      : nat_trans_data (pr1 φ) (pr1 ψ)
      := λ z, pb_of_sum_cats_nat_trans_ob z (pr1 F z) (identity_iso _).

    Local Definition pb_of_sum_cats_is_nat_trans_help
          {z₁ z₂ : pr1 Z}
          (f : z₁ --> z₂)
          {q₁ q₂ : pr111 (bincoprod_of ∁ C₁ C₂)}
          (g : q₁ --> q₂)
          (i₁ : iso q₁ (pr1 F z₁))
          (i₂ : iso q₂ (pr1 F z₂))
          (p : g · i₂ = i₁ · # (pr1 F) f)
      : # (pr1 φ) f · pb_of_sum_cats_nat_trans_ob _ _ i₂
        =
        pb_of_sum_cats_nat_trans_ob _ _ i₁ · # (pr1 ψ) f.
    Proof.
      induction q₁ as [ x₁ | y₁ ] ; induction q₂ as [ x₂ | y₂ ] ; cbn.
      - exact (nat_trans_ax
                 α
                 ((x₁ ,, z₁) ,, i₁)
                 ((x₂ ,, z₂) ,, i₂)
                 ((g ,, _) ,, p)).
      - exact (fromempty (i₁ · # (pr1 F) f · inv_from_iso i₂)).
      - exact (fromempty (i₁ · # (pr1 F) f · inv_from_iso i₂)).
      - exact (nat_trans_ax
                 β
                 ((y₁ ,, z₁) ,, i₁)
                 ((y₂ ,, z₂) ,, i₂)
                 ((g ,, _) ,, p)).
    Qed.

    Local Lemma pb_of_sum_cats_is_nat_trans
      : is_nat_trans _ _ pb_of_sum_cats_nat_trans_data.
    Proof.
      intros x y f ; unfold pb_of_sum_cats_nat_trans_data ; cbn.
      use pb_of_sum_cats_is_nat_trans_help.
      - exact (# (pr1 F) f).
      - rewrite id_left, id_right.
        apply idpath.
    Qed.

    Local Definition pb_of_sum_cats_nat_trans
      : φ ==> ψ.
    Proof.
      use make_nat_trans.
      - exact pb_of_sum_cats_nat_trans_data.
      - exact pb_of_sum_cats_is_nat_trans.
    Defined.

    Local Lemma pb_of_sum_cats_nat_trans_ob_id
          (z : pr1 Z)
          (q : pr111 (bincoprod_of ∁ C₁ C₂))
          (i : iso q (pr1 F z))
      : pb_of_sum_cats_nat_trans_ob z _ (identity_iso _)
        =
        pb_of_sum_cats_nat_trans_ob z q i.
    Proof.
      refine (!(id_left _) @ _ @ id_right _).
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply functor_id.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply functor_id.
      }
      refine (!_).
      refine (pb_of_sum_cats_is_nat_trans_help
                (identity z)
                i
                i
                (identity_iso _)
                _).
      rewrite (functor_id F).
      rewrite !id_right.
      apply idpath.
    Qed.

    Local Definition pb_of_sum_cats_nat_trans_inl
      : κ₁ ◃ pb_of_sum_cats_nat_trans = α.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn ; unfold pb_of_sum_cats_nat_trans_data.
      exact (pb_of_sum_cats_nat_trans_ob_id _ _ (pr2 x)).
    Qed.

    Local Definition pb_of_sum_cats_nat_trans_inr
      : κ₂ ◃ pb_of_sum_cats_nat_trans = β.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x ; cbn ; unfold pb_of_sum_cats_nat_trans_data.
      exact (pb_of_sum_cats_nat_trans_ob_id _ _ (pr2 x)).
    Qed.

    Local Lemma pb_of_sum_cats_nat_trans_unique
      : isaprop
          (∑ (γ : φ ==> ψ), κ₁ ◃ γ = α × κ₂ ◃ γ = β).
    Proof.
      use invproofirrelevance.
      intros τ₁ τ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply cellset_property.
      }
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro z ; cbn in z.
      pose (q := pr1 F z).
      assert (i := identity_iso _ : iso q (pr1 F z)).
      induction q as [ x | y] ; cbn.
      - refine (nat_trans_eq_pointwise (pr12 τ₁) ((x ,, z) ,, i) @ !_).
        exact (nat_trans_eq_pointwise (pr12 τ₂) ((x ,, z) ,, i)).
      - refine (nat_trans_eq_pointwise (pr22 τ₁) ((y ,, z) ,, i) @ !_).
        exact (nat_trans_eq_pointwise (pr22 τ₂) ((y ,, z) ,, i)).
    Qed.
  End UniversalCoproductsTwo.

  Definition universal_bicat_of_univ_cats
    : has_bincoprod_ump (make_bincoprod_cocone Z κ₁ κ₂).
  Proof.
    split.
    - intro W.
      use make_bincoprod_1cell.
      + exact (pb_of_sum_cats W).
      + use nat_iso_to_invertible_2cell.
        exact (pb_of_sum_cats_inl W).
      + use nat_iso_to_invertible_2cell.
        exact (pb_of_sum_cats_inr W).
    - intros W φ ψ α β.
      use iscontraprop1.
      + exact (pb_of_sum_cats_nat_trans_unique α β).
      + simple refine (_ ,, _ ,, _).
        * exact (pb_of_sum_cats_nat_trans α β).
        * exact (pb_of_sum_cats_nat_trans_inl α β).
        * exact (pb_of_sum_cats_nat_trans_inr α β).
  Defined.
End UniversalCoproducts.

Definition is_extensive_bicat_of_univ_cats
  : is_extensive bicat_of_univ_cats_with_biinitial_bincoprod.
Proof.
  intros C₁ C₂.
  split.
  - refine (_ ,, _ ,, _ ,, _).
    + apply cat_fully_faithful_is_fully_faithful_1cell.
      apply fully_faithful_inl_functor.
    + apply cat_fully_faithful_is_fully_faithful_1cell.
      apply fully_faithful_inr_functor.
    + apply bicat_of_univ_cats_inl_inr.
    + apply bicat_of_univ_cats_inr_inl.
  - use is_universal_from_pb_alt.
    + apply has_pb_bicat_of_univ_cats.
    + intros Z F.
      exact (universal_bicat_of_univ_cats F).
Defined.
