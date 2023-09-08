(*****************************************************************

 The category of posets

 We construct the category of posets as a displayed category over
 the category of sets. In addition, we equip this category with a
 terminal object and with binary products. We also construct
 equalizers and exponentials for this category.

 Contents
 1. The category of posets
 2. Terminal object
 3. Binary products and type indexed products
 4. Equalizers
 5. Exponentials

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Binproducts.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.categories.HSET.All.

Local Open Scope cat.

(**
 1. The category of posets
 *)
Definition poset_disp_cat
  : disp_cat SET.
Proof.
  use disp_struct.
  - exact (λ X, PartialOrder X).
  - exact (λ X₁ X₂ R₁ R₂ f, is_monotone R₁ R₂ f).
  - exact (λ X₁ X₂ R₁ R₂ f, isaprop_is_monotone R₁ R₂ f).
  - exact (λ X R, idfun_is_monotone R).
  - exact (λ X₁ X₂ X₃ R₁ R₂ R₃ f g Hf Hg, comp_is_monotone Hf Hg).
Defined.

Lemma poset_disp_cat_locally_prop : locally_propositional poset_disp_cat.
Proof.
  intro; intros; apply isaprop_is_monotone.
Qed.

Proposition is_univalent_poset_disp_cat
  : is_univalent_disp poset_disp_cat.
Proof.
  use is_univalent_disp_from_SIP_data.
  - exact (λ X, isaset_PartialOrder X).
  - cbn.
    refine (λ X R₁ R₂ p q, _).
    use subtypePath.
    {
      intro.
      apply isaprop_isPartialOrder.
    }
    use funextsec ; intro.
    use funextsec ; intro.
    use weqtopathshProp.
    use weqimplimpl.
    + apply p.
    + apply q.
    + apply (pr1 R₁).
    + apply (pr1 R₂).
Qed.

Definition category_of_posets
  : category
  := total_category poset_disp_cat.

Definition is_univalent_category_of_posets
  : is_univalent category_of_posets.
Proof.
  use is_univalent_total_category.
  - exact is_univalent_HSET.
  - exact is_univalent_poset_disp_cat.
Defined.

(**
 2. Terminal object
 *)
Definition dispTerminal_poset_disp_cat
  : dispTerminal poset_disp_cat TerminalHSET.
Proof.
  use make_dispTerminal_locally_prop.
  - exact poset_disp_cat_locally_prop.
  - exact unit_PartialOrder.
  - intros X RX.
    exact (λ x y p, tt).
Defined.

Definition Terminal_category_of_posets
  : Terminal category_of_posets.
Proof.
  use total_category_Terminal.
  - exact TerminalHSET.
  - exact dispTerminal_poset_disp_cat.
Defined.

(**
 3. Binary products
 *)
Definition dispBinProducts_poset_disp_cat
  : dispBinProducts poset_disp_cat BinProductsHSET.
Proof.
  intros X₁ X₂ R₁ R₂.
  use make_dispBinProduct_locally_prop.
  - exact poset_disp_cat_locally_prop.
  - exists (prod_PartialOrder R₁ R₂).
    split ; cbn.
    + exact (dirprod_pr1_is_monotone R₁ R₂).
    + exact (dirprod_pr2_is_monotone R₁ R₂).
  - cbn.
    intros W f g RW Hf Hg.
    exact (prodtofun_is_monotone Hf Hg).
Defined.

Definition BinProducts_category_of_posets
  : BinProducts category_of_posets.
Proof.
  use total_category_Binproducts.
  - exact BinProductsHSET.
  - exact dispBinProducts_poset_disp_cat.
Defined.

Definition Products_category_of_posets
           (J : UU)
  : Products J category_of_posets.
Proof.
  intro D.
  use make_Product.
  - exact (_ ,, depfunction_poset _ (λ j, pr2 (D j))).
  - exact (λ j, _ ,, is_monotone_depfunction_poset_pr _ _ j).
  - intros R f.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; use impred ; intro ; apply homset_property | ] ;
         use eq_monotone_function ;
         intro  x ;
         use funextsec ;
         intro j ;
         exact (eqtohomot (maponpaths pr1 (pr2 φ₁ j @ !(pr2 φ₂ j))) x)).
    + simple refine (_ ,, _).
      * exact (_ ,, is_monotone_depfunction_poset_pair (λ j, pr1 (f j)) (λ j, pr2 (f j))).
      * abstract
          (intro j ;
           use eq_monotone_function ; cbn ;
           intro x ;
           apply idpath).
Defined.

(**
 4. Equalizers
 *)
Definition Equalizers_category_of_posets
  : Equalizers category_of_posets.
Proof.
  intros X Y f g.
  simple refine ((_ ,, _) ,, (_ ,, _)).
  - exact (_ ,, Equalizer_order (pr2 X) (pr1 Y) (pr1 f) (pr1 g)).
  - exact (_ ,, Equalizer_pr1_monotone (pr2 X) (pr1 Y) (pr1 f) (pr1 g)).
  - abstract
      (use eq_monotone_function ;
       intro w ; cbn in w ; cbn ;
       exact (pr2 w)).
  - simpl.
    intros W h p.
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use eq_monotone_function ;
         intro w ;
         use subtypePath ; [ intro ; apply (pr1 Y) | ] ;
         refine (eqtohomot (maponpaths pr1 (pr2 φ₁)) w @ !_) ;
         exact (eqtohomot (maponpaths pr1 (pr2 φ₂)) w)).
    + simple refine (_ ,, _).
      * exact (_ ,, Equalizer_map_monotone _ _ _ _ _ (pr2 h) (eqtohomot (maponpaths pr1 p))).
      * abstract
          (use eq_monotone_function ;
           intro w ;
           apply idpath).
Defined.

(**
 5. Exponentials
 *)
Definition Exponentials_category_of_posets
  : Exponentials BinProducts_category_of_posets.
Proof.
  intros X.
  use left_adjoint_from_partial.
  - exact (λ Y, _ ,, monotone_function_PartialOrder (pr2 X) (pr2 Y)).
  - exact (λ Y, eval_monotone_function (pr2 X) (pr2 Y)).
  - refine (λ Y Z f, _).
    use iscontraprop1.
    + abstract
        (use invproofirrelevance ;
         intros g₁ g₂ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use eq_monotone_function ; intro z ;
         use eq_monotone_function ; intro x ;
         refine (!(eqtohomot (maponpaths pr1 (pr2 g₁)) (x ,, z)) @ _) ;
         exact (eqtohomot (maponpaths pr1 (pr2 g₂)) (x ,, z))).
    + simple refine (_ ,, _).
      * exact (lam_monotone_function (pr2 X) (pr2 Y) f).
      * abstract
          (use subtypePath ; [ intro ; apply isaprop_is_monotone | ] ;
           apply idpath).
Defined.
