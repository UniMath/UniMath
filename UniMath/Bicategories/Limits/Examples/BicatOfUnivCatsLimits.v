(*********************************************************************************

 Limits of categories

 Contents:
 1. Final object
 2. Products
 3. Pullbacks
 4. Strict pullbacks
 5. Comma objects
 6. Inserters
 7. Equifiers

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.Subcategory.Core.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.IsoCommaCategory.
Require Import UniMath.CategoryTheory.CommaCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.CommaObjects.
Require Import UniMath.Bicategories.Limits.Inserters.
Require Import UniMath.Bicategories.Limits.Equifiers.

Local Open Scope cat.

(**
 1. Final object
 *)

(** MOVE??? *)
Definition unit_category_nat_trans
           {C : category}
           (F G : C ⟶ unit_category)
  : F ⟹ G.
Proof.
  use make_nat_trans.
  - exact (λ _, pr1 (isapropunit _ _)).
  - abstract
      (intro ; intros ;
       apply isasetunit).
Defined.

Lemma nat_trans_to_unit_eq
      {X : category}
      (F G : X ⟶ unit_category)
      (α β : F ⟹ G)
  : α = β.
Proof.
  apply nat_trans_eq.
  - apply homset_property.
  - intro z. apply isasetunit.
Qed.

Definition bifinal_cats
  : @is_bifinal bicat_of_univ_cats unit_category.
Proof.
  use make_is_bifinal.
  - exact (λ C, functor_to_unit (pr1 C)).
  - exact (λ C F G, unit_category_nat_trans F G).
  - intros Y f g α β.
    apply nat_trans_to_unit_eq.
Defined.

(**
 2. Products
 *)
Definition univ_cat_binprod_cone
           (C₁ C₂ : bicat_of_univ_cats)
  : binprod_cone C₁ C₂.
Proof.
  use make_binprod_cone.
  - exact (univalent_category_binproduct C₁ C₂).
  - apply pr1_functor.
  - apply pr2_functor.
Defined.

Section CatsBinprodUMP.
  Context (C₁ C₂ : bicat_of_univ_cats).

  Definition binprod_ump_1_univ_cat
    : binprod_ump_1 (univ_cat_binprod_cone C₁ C₂).
  Proof.
    intro q.
    use make_binprod_1cell.
    - exact (bindelta_pair_functor (binprod_cone_pr1 q) (binprod_cone_pr2 q)).
    - apply nat_z_iso_to_invertible_2cell.
      apply bindelta_pair_pr1_z_iso.
    - apply nat_z_iso_to_invertible_2cell.
      apply bindelta_pair_pr2_z_iso.
  Defined.

  Definition binprod_ump_2_cell_univ_cat
    : has_binprod_ump_2_cell (univ_cat_binprod_cone C₁ C₂).
  Proof.
    intros q F₁ F₂ α β ; cbn -[functor_composite] in *.
    use make_nat_trans.
    - exact (λ x, α x ,, β x).
    - intros x y f.
      use pathsdirprod.
      + apply (nat_trans_ax α).
      + apply (nat_trans_ax β).
  Defined.

  Definition binprod_ump_2_cell_pr1_univ_cat
    : has_binprod_ump_2_cell_pr1
        (univ_cat_binprod_cone C₁ C₂)
        binprod_ump_2_cell_univ_cat.
  Proof.
    intros q F₁ F₂ α β.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x ; cbn.
    apply idpath.
  Qed.

  Definition binprod_ump_2_cell_pr2_univ_cat
    : has_binprod_ump_2_cell_pr2
        (univ_cat_binprod_cone C₁ C₂)
        binprod_ump_2_cell_univ_cat.
  Proof.
    intros q F₁ F₂ α β.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x ; cbn.
    apply idpath.
  Qed.

  Definition binprod_ump_2_cell_unique_univ_cat
    : has_binprod_ump_2_cell_unique (univ_cat_binprod_cone C₁ C₂).
  Proof.
    intros q F₁ F₂ α β γ δ p₁ p₂ p₃ p₄.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use pathsdirprod.
    - exact (nat_trans_eq_pointwise p₁ x @ !(nat_trans_eq_pointwise p₃ x)).
    - exact (nat_trans_eq_pointwise p₂ x @ !(nat_trans_eq_pointwise p₄ x)).
  Qed.

  Definition has_binprod_ump_univ_cats
    : has_binprod_ump (univ_cat_binprod_cone C₁ C₂).
  Proof.
    use make_binprod_ump.
    - exact binprod_ump_1_univ_cat.
    - exact binprod_ump_2_cell_univ_cat.
    - exact binprod_ump_2_cell_pr1_univ_cat.
    - exact binprod_ump_2_cell_pr2_univ_cat.
    - exact binprod_ump_2_cell_unique_univ_cat.
  Defined.
End CatsBinprodUMP.

Definition has_binprod_bicat_of_univ_cats
  : has_binprod bicat_of_univ_cats.
Proof.
  intros C₁ C₂.
  simple refine (_ ,, _).
  - exact (univ_cat_binprod_cone C₁ C₂).
  - exact (has_binprod_ump_univ_cats C₁ C₂).
Defined.

(**
 3. Pullbacks
 *)
Definition iso_comma_pb_cone
           {C₁ C₂ C₃ : bicat_of_univ_cats}
           (F : C₁ --> C₃)
           (G : C₂ --> C₃)
  : pb_cone F G.
Proof.
  use make_pb_cone.
  - exact (univalent_iso_comma F G).
  - exact (iso_comma_pr1 F G).
  - exact (iso_comma_pr2 F G).
  - apply nat_z_iso_to_invertible_2cell.
    exact (iso_comma_commute F G).
Defined.

Section IsoCommaUMP.
  Context {C₁ C₂ C₃ : bicat_of_univ_cats}
          (F : C₁ --> C₃)
          (G : C₂ --> C₃).

  Definition pb_ump_1_iso_comma
    : pb_ump_1 (iso_comma_pb_cone F G).
  Proof.
    intro q.
    use make_pb_1cell.
    - use iso_comma_ump1.
      + exact (pb_cone_pr1 q).
      + exact (pb_cone_pr2 q).
      + apply invertible_2cell_to_nat_z_iso.
        exact (pb_cone_cell q).
    - apply nat_z_iso_to_invertible_2cell.
      apply iso_comma_ump1_pr1.
    - apply nat_z_iso_to_invertible_2cell.
      apply iso_comma_ump1_pr2.
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ; unfold pb_cone_cell ;
         rewrite (functor_id F), (functor_id G) ;
         rewrite !id_left, !id_right ;
         apply idpath).
  Defined.

  Section CellUMP.
    Let p := iso_comma_pb_cone F G.

    Context {q : bicat_of_univ_cats}
            (φ ψ : q --> p)
            (α : φ · pb_cone_pr1 p ==> ψ · pb_cone_pr1 p)
            (β : φ · pb_cone_pr2 p ==> ψ · pb_cone_pr2 p)
            (r : (φ ◃ pb_cone_cell p)
                 • lassociator _ _ _
                 • (β ▹ G)
                 • rassociator _ _ _
                 =
                 lassociator _ _ _
                 • (α ▹ F)
                 • rassociator _ _ _
                 • (ψ ◃ pb_cone_cell p)).

    Definition pb_ump_2_nat_trans
      : φ ==> ψ.
    Proof.
      use (iso_comma_ump2 _ _ _ _ α β).
      abstract
        (intros x ;
         pose (nat_trans_eq_pointwise r x) as z ;
         cbn in z ;
         unfold iso_comma_commute_nat_trans_data in z ;
         rewrite !id_left, !id_right in z ;
         exact z).
    Defined.

    Definition pb_ump_2_nat_trans_pr1
      : pb_ump_2_nat_trans ▹ pb_cone_pr1 (iso_comma_pb_cone F G) = α.
    Proof.
      apply iso_comma_ump2_pr1.
    Qed.

    Definition pb_ump_2_nat_trans_pr2
      : pb_ump_2_nat_trans ▹ pb_cone_pr2 (iso_comma_pb_cone F G) = β.
    Proof.
      apply iso_comma_ump2_pr2.
    Qed.
  End CellUMP.

  Definition pb_ump_2_iso_comma
    : pb_ump_2 (iso_comma_pb_cone F G).
  Proof.
    intros C φ ψ α β r.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros τ₁ τ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         exact (iso_comma_ump_eq _ _ _ _ α β (pr12 τ₁) (pr22 τ₁) (pr12 τ₂) (pr22 τ₂))).
    - simple refine (_ ,, _).
      + exact (pb_ump_2_nat_trans φ ψ α β r).
      + split.
        * exact (pb_ump_2_nat_trans_pr1 φ ψ α β r).
        * exact (pb_ump_2_nat_trans_pr2 φ ψ α β r).
  Defined.

  Definition iso_comma_has_pb_ump
    : has_pb_ump (iso_comma_pb_cone F G).
  Proof.
    split.
    - exact pb_ump_1_iso_comma.
    - exact pb_ump_2_iso_comma.
  Defined.
End IsoCommaUMP.

Definition has_pb_bicat_of_univ_cats
  : has_pb bicat_of_univ_cats.
Proof.
  intros C₁ C₂ C₃ F G.
  simple refine (_ ,, _).
  - exact (iso_comma_pb_cone F G).
  - exact (iso_comma_has_pb_ump F G).
Defined.

(**
 4. Strict pullbacks
 *)
Section ReindexingPullback.
  Context {C₁ C₂ : bicat_of_univ_cats}
          (F : C₁ --> C₂)
          (D₂ : disp_univalent_category (pr1 C₂))
          (HD₂ : iso_cleaving (pr1 D₂)).

  Let tot_D₂ : bicat_of_univ_cats
    := total_univalent_category D₂.
  Let pb : bicat_of_univ_cats
    := univalent_reindex_cat F D₂.
  Let π₁ : pb --> _
    := pr1_category _.
  Let π₂ : pb --> tot_D₂
    := total_functor (reindex_disp_cat_disp_functor F D₂).
  Let γ : invertible_2cell (π₁ · F) (π₂ · pr1_category D₂)
    := nat_z_iso_to_invertible_2cell
         (π₁ · F)
         (π₂ · pr1_category D₂)
         (total_functor_commute_z_iso (reindex_disp_cat_disp_functor F (pr1 D₂))).
  Let cone : pb_cone F (pr1_category _ : tot_D₂ --> C₂)
    := make_pb_cone pb π₁ π₂ γ.

  Definition reindexing_has_pb_ump_1_cell
             (q : pb_cone F (pr1_category _ : tot_D₂ --> C₂))
    : q --> cone.
  Proof.
    use reindex_pb_ump_1.
    - exact HD₂.
    - exact (pb_cone_pr2 q).
    - exact (pb_cone_pr1 q).
    - apply invertible_2cell_to_nat_z_iso.
      exact (pb_cone_cell q).
  Defined.

  Definition reindexing_has_pb_ump_1_pr1
             (q : pb_cone F (pr1_category _ : tot_D₂ --> C₂))
    : invertible_2cell
        (reindexing_has_pb_ump_1_cell q · pb_cone_pr1 cone)
        (pb_cone_pr1 q).
  Proof.
    use nat_z_iso_to_invertible_2cell.
    exact (reindex_pb_ump_1_pr1_nat_iso
             F D₂ HD₂
             (pb_cone_pr2 q)
             (pb_cone_pr1 q)
             (invertible_2cell_to_nat_z_iso
                _ _
                (pb_cone_cell q))).
  Defined.

  Definition reindexing_has_pb_ump_1_pr2
             (q : pb_cone F (pr1_category _ : tot_D₂ --> C₂))
    : invertible_2cell
        (reindexing_has_pb_ump_1_cell q · pb_cone_pr2 cone)
        (pb_cone_pr2 q).
  Proof.
    use nat_z_iso_to_invertible_2cell.
    exact (reindex_pb_ump_1_pr2_nat_z_iso
             F D₂ HD₂
             (pb_cone_pr2 q)
             (pb_cone_pr1 q)
             (invertible_2cell_to_nat_z_iso
                _ _
                (pb_cone_cell q))).
  Defined.

  Definition reindexing_has_pb_ump_1_pb_cell
             (q : pb_cone F (pr1_category _ : tot_D₂ --> C₂))
    : reindexing_has_pb_ump_1_cell q ◃ pb_cone_cell cone
      =
      lassociator _ _ _
      • (reindexing_has_pb_ump_1_pr1 q ▹ F)
      • pb_cone_cell q
      • ((reindexing_has_pb_ump_1_pr2 q)^-1 ▹ _)
      • rassociator _ _ _.
  Proof.
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    refine (!_).
    refine (id_right _ @ _).
    etrans.
    {
      do 2 refine (maponpaths (λ z, z · _) _).
      apply id_left.
    }
    etrans.
    {
      do 2 refine (maponpaths (λ z, z · _) _).
      exact (functor_id F _).
    }
    etrans.
    {
      refine (maponpaths (λ z, z · _) _).
      apply id_left.
    }
    etrans.
    {
      apply maponpaths.
      exact (inv_from_z_iso_in_total
               (is_invertible_2cell_to_is_nat_z_iso _ (pr2 (pb_cone_cell q)) x)
               _).
    }
    exact (nat_trans_eq_pointwise
             (vcomp_rinv
                (pb_cone_cell q))
             x).
  Qed.

  Definition reindexing_has_pb_ump_1
    : pb_ump_1 cone.
  Proof.
    intro q.
    use make_pb_1cell.
    - exact (reindexing_has_pb_ump_1_cell q).
    - exact (reindexing_has_pb_ump_1_pr1 q).
    - exact (reindexing_has_pb_ump_1_pr2 q).
    - exact (reindexing_has_pb_ump_1_pb_cell q).
  Defined.

  Definition reindexing_has_pb_ump_2
    : pb_ump_2 cone.
  Proof.
    intros C₀ G₁ G₂ τ₁ τ₂ p.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         exact (reindex_pb_ump_eq
                  _ _ _ _
                  τ₁ τ₂
                  _ _
                  (pr12 φ₁)
                  (pr22 φ₁)
                  (pr12 φ₂)
                  (pr22 φ₂))).
    - simple refine (_ ,, _ ,, _).
      + use reindex_pb_ump_2.
        * exact τ₁.
        * exact τ₂.
        * abstract
            (intro x ;
             pose (nat_trans_eq_pointwise p x) as q ;
             cbn in q ;
             rewrite !id_left, !id_right in q ;
             exact q).
      + apply reindex_pb_ump_2_pr1.
      + apply reindex_pb_ump_2_pr2.
  Defined.

  Definition reindexing_has_pb_ump
    : has_pb_ump cone.
  Proof.
    split.
    - exact reindexing_has_pb_ump_1.
    - exact reindexing_has_pb_ump_2.
  Defined.
End ReindexingPullback.

(**
 5. Comma objects
 *)
Section CommaObject.
  Context {C₁ C₂ C₃ : bicat_of_univ_cats}
          (F : C₁ --> C₃)
          (G : C₂ --> C₃).

  Definition comma_comma_cone
    : comma_cone F G.
  Proof.
    use make_comma_cone.
    - exact (univalent_comma F G).
    - exact (comma_pr1 F G).
    - exact (comma_pr2 F G).
    - exact (comma_commute F G).
  Defined.

  Definition comma_ump_1_comma
    : comma_ump_1 comma_comma_cone.
  Proof.
    intro q.
    use make_comma_1cell.
    - use comma_ump1.
      + exact (comma_cone_pr1 q).
      + exact (comma_cone_pr2 q).
      + exact (comma_cone_cell q).
    - apply nat_z_iso_to_invertible_2cell.
      apply comma_ump1_pr1.
    - apply nat_z_iso_to_invertible_2cell.
      apply comma_ump1_pr2.
    - abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ; unfold pb_cone_cell ;
         rewrite (functor_id F), (functor_id G) ;
         rewrite !id_left, !id_right ;
         apply idpath).
  Defined.

  Section CellUMP.
    Let p := comma_comma_cone.

    Context {q : bicat_of_univ_cats}
            (φ ψ : q --> p)
            (α : φ · comma_cone_pr1 p ==> ψ · comma_cone_pr1 p)
            (β : φ · comma_cone_pr2 p ==> ψ · comma_cone_pr2 p)
            (r : (φ ◃ comma_cone_cell p)
                 • lassociator _ _ _
                 • (β ▹ G)
                 • rassociator _ _ _
                 =
                 lassociator _ _ _
                 • (α ▹ F)
                 • rassociator _ _ _
                 • (ψ ◃ comma_cone_cell p)).

    Definition comma_ump_2_nat_trans
      : φ ==> ψ.
    Proof.
      use (comma_ump2 _ _ _ _ α β).
      abstract
        (intros x ;
         pose (nat_trans_eq_pointwise r x) as z ;
         cbn in z ;
         unfold iso_comma_commute_nat_trans_data in z ;
         rewrite !id_left, !id_right in z ;
         exact z).
    Defined.

    Definition comma_ump_2_nat_trans_pr1
      : comma_ump_2_nat_trans ▹ comma_cone_pr1 comma_comma_cone = α.
    Proof.
      apply comma_ump2_pr1.
    Qed.

    Definition comma_ump_2_nat_trans_pr2
      : comma_ump_2_nat_trans ▹ comma_cone_pr2 comma_comma_cone = β.
    Proof.
      apply comma_ump2_pr2.
    Qed.
  End CellUMP.

  Definition comma_ump_2_comma
    : comma_ump_2 comma_comma_cone.
  Proof.
    intros C φ ψ α β r.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros τ₁ τ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         exact (comma_ump_eq_nat_trans
                  _ _ _ _
                  α β
                  (pr12 τ₁) (pr22 τ₁) (pr12 τ₂) (pr22 τ₂))).
    - simple refine (_ ,, _).
      + exact (comma_ump_2_nat_trans φ ψ α β r).
      + split.
        * exact (comma_ump_2_nat_trans_pr1 φ ψ α β r).
        * exact (comma_ump_2_nat_trans_pr2 φ ψ α β r).
  Defined.

  Definition comma_has_ump
    : has_comma_ump comma_comma_cone.
  Proof.
    split.
    - exact comma_ump_1_comma.
    - exact comma_ump_2_comma.
  Defined.
End CommaObject.

Definition has_comma_bicat_of_univ_cats
  : has_comma bicat_of_univ_cats
  := λ C₁ C₂ C₃ F G, comma_comma_cone F G ,, comma_has_ump F G.

(**
 6. Inserters
 *)
Definition dialgebra_inserter_cone
           {C₁ C₂ : bicat_of_univ_cats}
           (F G : C₁ --> C₂)
  : inserter_cone F G.
Proof.
  use make_inserter_cone.
  - exact (univalent_dialgebra F G).
  - exact (dialgebra_pr1 F G).
  - exact (dialgebra_nat_trans F G).
Defined.

Definition dialgebra_inserter_ump_1
           {C₁ C₂ : bicat_of_univ_cats}
           (F G : C₁ --> C₂)
  : has_inserter_ump_1 (dialgebra_inserter_cone F G).
Proof.
  intros q.
  use make_inserter_1cell.
  - exact (functor_to_dialgebra
             (inserter_cone_pr1 q)
             (inserter_cone_cell q)).
  - use nat_z_iso_to_invertible_2cell.
    exact (functor_to_dialgebra_pr1_nat_z_iso
             (inserter_cone_pr1 q)
             (inserter_cone_cell q)).
  - abstract
      (use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ; cbn ;
       rewrite !(functor_id F), !(functor_id G) ;
       rewrite !id_left, !id_right ;
       apply idpath).
Defined.

Definition dialgebra_inserter_ump_2
           {C₁ C₂ : bicat_of_univ_cats}
           (F G : C₁ --> C₂)
  : has_inserter_ump_2 (dialgebra_inserter_cone F G).
Proof.
  intros C₀ K₁ K₂ α p.
  simple refine (_ ,, _).
  - apply (nat_trans_to_dialgebra K₁ K₂ α).
    abstract
      (intro x ;
       pose (nat_trans_eq_pointwise p x) as p' ;
       cbn in p' ;
       rewrite !id_left, !id_right in p' ;
       exact p').
  - abstract
      (use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ; cbn ;
       apply idpath).
Defined.

Definition dialgebra_inserter_ump_eq
           {C₁ C₂ : bicat_of_univ_cats}
           (F G : C₁ --> C₂)
  : has_inserter_ump_eq (dialgebra_inserter_cone F G).
Proof.
  intros C₀ K₁ K₂ α p n₁ n₂ q₁ q₂.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro x.
  use eq_dialgebra.
  exact (nat_trans_eq_pointwise q₁ x @ !(nat_trans_eq_pointwise q₂ x)).
Qed.

Definition has_inserters_bicat_of_univ_cats
  : has_inserters bicat_of_univ_cats.
Proof.
  intros C₁ C₂ F G.
  simple refine (univalent_dialgebra F G ,, _ ,, _ ,, _).
  - exact (dialgebra_pr1 F G).
  - exact (dialgebra_nat_trans F G).
  - refine (_ ,, _ ,, _).
    + exact (dialgebra_inserter_ump_1 F G).
    + exact (dialgebra_inserter_ump_2 F G).
    + exact (dialgebra_inserter_ump_eq F G).
Defined.

(**
 7. Equifiers
 *)
Section EquifiersCat.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F G : C₁ --> C₂}
          (n₁ n₂ : F ==> G).

  Definition equifier_bicat_of_univ_cats
    : bicat_of_univ_cats.
  Proof.
    use (subcategory_univalent C₁).
    intro x.
    use make_hProp.
    - exact (pr1 n₁ x = pr1 n₂ x).
    - apply homset_property.
  Defined.

  Definition equifier_bicat_of_univ_cats_pr1
    : equifier_bicat_of_univ_cats --> C₁
    := sub_precategory_inclusion _ _.

  Definition equifier_bicat_of_univ_cats_eq
    : equifier_bicat_of_univ_cats_pr1 ◃ n₁
      =
      equifier_bicat_of_univ_cats_pr1 ◃ n₂.
  Proof.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    exact (pr2 x).
  Qed.

  Definition equifier_bicat_of_univ_cats_cone
    : equifier_cone F G n₁ n₂
    := make_equifier_cone
         equifier_bicat_of_univ_cats
         equifier_bicat_of_univ_cats_pr1
         equifier_bicat_of_univ_cats_eq.

  Section EquifierUMP1.
    Context (q : equifier_cone F G n₁ n₂).

    Definition equifier_bicat_of_univ_cats_ump_1_mor_data
      : functor_data
          (pr11 q)
          (pr1 equifier_bicat_of_univ_cats).
    Proof.
      use make_functor_data.
      - refine (λ x, pr1 (equifier_cone_pr1 q) x ,, _).
        exact (nat_trans_eq_pointwise (equifier_cone_eq q) x).
      - exact (λ x y f, # (pr1 (equifier_cone_pr1 q)) f ,, tt).
    Defined.

    Definition equifier_bicat_of_univ_cats_ump_1_mor_is_functor
      : is_functor equifier_bicat_of_univ_cats_ump_1_mor_data.
    Proof.
      split ; intro ; intros.
      - use subtypePath ; [ intro ; apply isapropunit | ] ; cbn.
        apply functor_id.
      - use subtypePath ; [ intro ; apply isapropunit | ] ; cbn.
        apply functor_comp.
    Qed.

    Definition equifier_bicat_of_univ_cats_ump_1_mor
      : q --> equifier_bicat_of_univ_cats_cone.
    Proof.
      use make_functor.
      - exact equifier_bicat_of_univ_cats_ump_1_mor_data.
      - exact equifier_bicat_of_univ_cats_ump_1_mor_is_functor.
    Defined.

    Definition equifier_bicat_of_univ_cats_ump_1_pr1
      : equifier_bicat_of_univ_cats_ump_1_mor ∙ equifier_bicat_of_univ_cats_pr1
        ⟹
        pr1 (equifier_cone_pr1 q).
    Proof.
      use make_nat_trans.
      - exact (λ _, identity _).
      - abstract
          (intros x y f ; cbn ;
           rewrite id_left, id_right ;
           apply idpath).
    Defined.

    Definition equifier_bicat_of_univ_cats_ump_1_pr1_nat_z_iso
      : nat_z_iso
          (equifier_bicat_of_univ_cats_ump_1_mor ∙ equifier_bicat_of_univ_cats_pr1)
          (equifier_cone_pr1 q).
    Proof.
      use make_nat_z_iso.
      - exact equifier_bicat_of_univ_cats_ump_1_pr1.
      - intro.
        apply identity_is_z_iso.
    Defined.
  End EquifierUMP1.

  Definition equifier_bicat_of_univ_cats_ump_1
    : has_equifier_ump_1 equifier_bicat_of_univ_cats_cone.
  Proof.
    intro q.
    use make_equifier_1cell.
    - exact (equifier_bicat_of_univ_cats_ump_1_mor q).
    - apply nat_z_iso_to_invertible_2cell.
      exact (equifier_bicat_of_univ_cats_ump_1_pr1_nat_z_iso q).
  Defined.

  Section EquifierUMP2.
    Context {C₀ : bicat_of_univ_cats}
            {K₁ K₂ : C₀ --> equifier_bicat_of_univ_cats_cone}
            (α : K₁ · equifier_cone_pr1 equifier_bicat_of_univ_cats_cone
                 ==>
                 K₂ · equifier_cone_pr1 equifier_bicat_of_univ_cats_cone).

    Definition equifier_bicat_of_univ_cats_ump_2_cell
      : K₁ ==> K₂.
    Proof.
      use make_nat_trans.
      - exact (λ x, pr1 α x ,, tt).
      - abstract
          (intros x y f ;
           use subtypePath ; [ intro ; apply isapropunit | ] ;
           cbn ;
           exact (nat_trans_ax α _ _ f)).
    Defined.

    Definition equifier_bicat_of_univ_cats_ump_2_eq
      : equifier_bicat_of_univ_cats_ump_2_cell ▹ _  = α.
    Proof.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      intro x.
      apply idpath.
    Qed.
  End EquifierUMP2.

  Definition equifier_bicat_of_univ_cats_ump_2
    : has_equifier_ump_2 equifier_bicat_of_univ_cats_cone.
  Proof.
    intros C₀ K₁ K₂ α.
    simple refine (_ ,, _).
    - exact (equifier_bicat_of_univ_cats_ump_2_cell α).
    - exact (equifier_bicat_of_univ_cats_ump_2_eq α).
  Defined.

  Definition equifier_bicat_of_univ_cats_ump_eq
    : has_equifier_ump_eq equifier_bicat_of_univ_cats_cone.
  Proof.
    intros C₀ K₁ K₂ α β₁ β₂ p₁ p₂.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use subtypePath.
    {
      intro.
      apply isapropunit.
    }
    exact (nat_trans_eq_pointwise p₁ x @ !(nat_trans_eq_pointwise p₂ x)).
  Qed.
End EquifiersCat.

Definition has_equifiers_bicat_of_univ_cats
  : has_equifiers bicat_of_univ_cats.
Proof.
  intros C₁ C₂ F G n₁ n₂.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (equifier_bicat_of_univ_cats n₁ n₂).
  - exact (equifier_bicat_of_univ_cats_pr1 n₁ n₂).
  - exact (equifier_bicat_of_univ_cats_eq n₁ n₂).
  - simple refine (_ ,, _ ,, _).
    + exact (equifier_bicat_of_univ_cats_ump_1 n₁ n₂).
    + exact (equifier_bicat_of_univ_cats_ump_2 n₁ n₂).
    + exact (equifier_bicat_of_univ_cats_ump_eq n₁ n₂).
Defined.
