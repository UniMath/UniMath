(******************************************************************************

 Pseudofunctors into categories from a discrete bicategory

 In this file, we compare pseudofunctors from a discrete bicategory into the
 bicategory of univalent categories with indexed categories. For that, we first
 provide a constructor to build pseudofunctors into any bicategory starting in
 a discrete bicategory.

 Contents
 1. Pseudofunctors from a discrete bicategory
 2. Every indexed category gives rise to a pseudofunctor
 3. Pseudofunctor into categories give an indexed category
 4. Transport on pseudofunctors into categories

 ******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Discreteness.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.DiscreteBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.

(**
 1. Pseudofunctors from a discrete bicategory
 *)
Section PseudoFunctorFromCat.
  Context {C : category}
          {B : bicat}
          (F₀ : C → B)
          (F₁ : ∏ (x y : C), x --> y → F₀ x --> F₀ y)
          (Fid : ∏ (a : C), invertible_2cell (id₁ (F₀ a)) (F₁ a a (id₁ a)))
          (Fc : ∏ (a b c : C)
                  (f : a --> b)
                  (g : b --> c),
                invertible_2cell
                  (F₁ a b f · F₁ b c g)
                  (F₁ a c (f · g)))
          (Flun : ∏ (x y : C)
                    (f : x --> y),
                  lunitor _
                  =
                  (Fid x ▹ F₁ x y f)
                  • Fc x x y (id₁ x) f
                  • idtoiso_2_1 _ _ (maponpaths (F₁ x y) (id_left _)))
          (Frun : ∏ (x y : C)
                    (f : x --> y),
                  runitor _
                  =
                  (F₁ x y f ◃ Fid y)
                  • Fc x y y f (id₁ y)
                  • idtoiso_2_1 _ _ (maponpaths (F₁ x y) (id_right _)))
          (Fassoc : ∏ (w x y z : C)
                      (f : w --> x)
                      (g : x --> y)
                      (h : y --> z),
                    (F₁ w x f ◃ Fc x y z g h) • Fc w x z f (g · h)
                    • idtoiso_2_1 _ _ (maponpaths (F₁ w z) (assoc f g h))
                    =
                    lassociator _ _ _
                    • (Fc w x y f g ▹ F₁ y z h)
                    • Fc w y z (f · g) h).

  Definition make_psfunctor_from_cat_data
    : psfunctor_data (cat_to_bicat C) B.
  Proof.
    use make_psfunctor_data.
    - exact F₀.
    - exact F₁.
    - exact (λ x y f g p, idtoiso_2_1 _ _ (maponpaths (F₁ x y) p)).
    - exact Fid.
    - exact Fc.
  Defined.

  Proposition make_psfunctor_from_cat_laws
    : psfunctor_laws make_psfunctor_from_cat_data.
  Proof.
    repeat split.
    - unfold psfunctor_id2_law ; cbn ; intros x y f.
      assert (@id2 (cat_to_bicat C) _ _ f = idpath _) as p.
      {
        apply homset_property.
      }
      etrans.
      {
        do 3 apply maponpaths.
        exact p.
      }
      cbn.
      apply idpath.
    - unfold psfunctor_vcomp2_law ; cbn ; intros x y f g h p q.
      induction p, q ; cbn.
      assert (@id2 (cat_to_bicat C) _ _ f = idpath _) as p.
      {
        apply homset_property.
      }
      rewrite <- !p.
      etrans.
      {
        do 3 apply maponpaths.
        refine (@id2_left (cat_to_bicat C) _ _ _ _ _ @ _).
        exact p.
      }
      cbn.
      rewrite id2_right.
      apply idpath.
    - unfold psfunctor_lunitor_law ; cbn ; intros x y f.
      refine (Flun x y f @ _).
      do 4 apply maponpaths.
      apply homset_property.
    - unfold psfunctor_runitor_law ; cbn ; intros x y f.
      refine (Frun x y f @ _).
      do 4 apply maponpaths.
      apply homset_property.
    - unfold psfunctor_lassociator_law ; cbn ; intros w x y z f g h.
      refine (_ @ Fassoc w x y z f g h).
      do 4 apply maponpaths.
      apply homset_property.
    - unfold psfunctor_lwhisker_law ; cbn ; intros x y z f g₁ g₂ p.
      induction p.
      cbn.
      rewrite lwhisker_id2.
      rewrite id2_left.
      assert (@id2 (cat_to_bicat C) _ _ g₁ = idpath _) as p.
      {
        apply homset_property.
      }
      assert (@id2 (cat_to_bicat C) _ _ (f · g₁) = idpath _) as q.
      {
        apply homset_property.
      }
      rewrite <- p.
      etrans.
      {
        do 4 apply maponpaths.
        refine (@lwhisker_id2 (cat_to_bicat C) _ _ _ _ _ @ _).
        exact q.
      }
      cbn.
      apply id2_right.
    - unfold psfunctor_rwhisker_law ; cbn ; intros x y z f₁ f₂ g p.
      induction p.
      cbn.
      rewrite id2_rwhisker.
      rewrite id2_left.
      assert (@id2 (cat_to_bicat C) _ _ f₁ = idpath _) as p.
      {
        apply homset_property.
      }
      assert (@id2 (cat_to_bicat C) _ _ (f₁ · g) = idpath _) as q.
      {
        apply homset_property.
      }
      rewrite <- p.
      etrans.
      {
        do 4 apply maponpaths.
        refine (@id2_rwhisker (cat_to_bicat C) _ _ _ _ _ @ _).
        exact q.
      }
      cbn.
      apply id2_right.
  Qed.

  Definition make_psfunctor_from_cat
    : psfunctor (cat_to_bicat C) B.
  Proof.
    use make_psfunctor.
    - exact make_psfunctor_from_cat_data.
    - exact make_psfunctor_from_cat_laws.
    - split ; intros ; apply property_from_invertible_2cell.
  Defined.
End PseudoFunctorFromCat.

(**
 2. Every indexed category gives rise to a pseudofunctor
 *)
Definition indexed_cat_to_psfunctor
           {C : category}
           (Φ : indexed_cat C)
  : psfunctor (cat_to_bicat C) bicat_of_univ_cats.
Proof.
  use make_psfunctor_from_cat.
  - exact Φ.
  - exact (λ _ _ f, Φ $ f).
  - intro x.
    use nat_z_iso_to_invertible_2cell.
    use make_nat_z_iso.
    + exact (indexed_cat_id Φ x).
    + intro xx.
      exact (is_z_isomorphism_indexed_cat_id Φ xx).
  - intros x y z f g.
    use nat_z_iso_to_invertible_2cell.
    use make_nat_z_iso.
    + exact (indexed_cat_comp Φ f g).
    + intro xx.
      exact (is_z_isomorphism_indexed_cat_comp Φ f g xx).
  - abstract
      (intros x y f ;
       use nat_trans_eq ; [ apply homset_property | ] ; cbn ;
       intro xx ;
       refine (indexed_cat_lunitor Φ f xx @ _) ;
       apply maponpaths ;
       refine (!_) ;
       refine (idtoiso_2_1_in_bicat_of_univ_cats
                 (maponpaths (λ h, Φ $ h) (id_left f))
                 xx
               @ _) ;
       do 2 apply maponpaths ;
       exact (maponpathscomp (λ h, Φ $ h) (λ H, pr11 H xx) (id_left f))).
  - abstract
      (intros x y f ;
       use nat_trans_eq ; [ apply homset_property | ] ; cbn ;
       intro xx ;
       refine (indexed_cat_runitor Φ f xx @ _) ;
       apply maponpaths ;
       refine (!_) ;
       refine (idtoiso_2_1_in_bicat_of_univ_cats
                 (maponpaths (λ h, Φ $ h) (id_right f))
                 xx
               @ _) ;
       do 2 apply maponpaths ;
       exact (maponpathscomp (λ h, Φ $ h) (λ H, pr11 H xx) (id_right f))).
  - abstract
      (intros w x y z f g h ;
       use nat_trans_eq ; [ apply homset_property | ] ; cbn ;
       intro ww ;
       rewrite id_left ;
       refine (_ @ indexed_cat_lassociator Φ f g h ww) ;
       apply maponpaths ;
       refine (idtoiso_2_1_in_bicat_of_univ_cats
                 (maponpaths (λ h, Φ $ h) (assoc f g h))
                 ww
               @ _) ;
       do 2 apply maponpaths ;
       exact (maponpathscomp (λ h, Φ $ h) (λ H, pr11 H ww) (assoc f g h))).
Defined.

(**
 3. Pseudofunctor into categories give an indexed category
 *)
Section PseudofunctorToIndexedCat.
  Context {C : category}
          (F : psfunctor (cat_to_bicat C) bicat_of_univ_cats).

  Definition psfunctor_to_indexed_cat_data
    : indexed_cat_data C.
  Proof.
    use make_indexed_cat_data.
    - exact (λ x, F x).
    - exact (λ x y f, #F f).
    - exact (λ x, pr1 (psfunctor_id F x)).
    - exact (λ x y z f g, pr1 (psfunctor_comp F f g)).
  Defined.

  Definition psfunctor_to_indexed_cat_isos
    : indexed_cat_isos psfunctor_to_indexed_cat_data.
  Proof.
    split.
    - intros x xx.
      exact (pr2 (invertible_2cell_to_nat_z_iso _ _ (psfunctor_id F x)) xx).
    - intros x y z f g xx.
      exact (pr2 (invertible_2cell_to_nat_z_iso _ _ (psfunctor_comp F f g)) xx).
  Defined.

  Lemma psfunctor_idtoiso
        {x y : C}
        {f g : x --> y}
        (p : f = g)
        (xx : pr1 (F x))
    : pr1 (##F p) xx = idtoiso (maponpaths (λ h, pr1 (#F h) xx) p).
  Proof.
    induction p ; cbn.
    refine (_ @ nat_trans_eq_pointwise (psfunctor_id2 F _) xx).
    refine (maponpaths (λ h, h xx) _).
    do 2 apply maponpaths.
    apply homset_property.
  Qed.

  Proposition psfunctor_to_indexed_cat_laws
    : indexed_cat_laws psfunctor_to_indexed_cat_data.
  Proof.
    repeat split.
    - intros x y f xx.
      pose (p := nat_trans_eq_pointwise (psfunctor_lunitor F f) xx).
      cbn in p ; cbn.
      refine (p @ _) ; clear p.
      rewrite !assoc'.
      do 2 apply maponpaths.
      refine (psfunctor_idtoiso _ _ @ _).
      do 3 apply maponpaths.
      apply homset_property.
    - intros x y f xx.
      pose (p := nat_trans_eq_pointwise (psfunctor_runitor F f) xx).
      cbn in p ; cbn.
      refine (p @ _) ; clear p.
      rewrite !assoc'.
      do 2 apply maponpaths.
      refine (psfunctor_idtoiso _ _ @ _).
      do 3 apply maponpaths.
      apply homset_property.
    - intros w x y z f g h ww.
      pose (p := nat_trans_eq_pointwise (psfunctor_lassociator F f g h) ww).
      cbn in p ; cbn.
      rewrite id_left in p.
      refine (_ @ p) ; clear p.
      apply maponpaths.
      refine (!_).
      refine (psfunctor_idtoiso _ _ @ _).
      do 3 apply maponpaths.
      apply homset_property.
  Qed.

  Definition psfunctor_to_indexed_cat
    : indexed_cat C.
  Proof.
    use make_indexed_cat.
    - exact psfunctor_to_indexed_cat_data.
    - exact psfunctor_to_indexed_cat_isos.
    - exact psfunctor_to_indexed_cat_laws.
  Defined.
End PseudofunctorToIndexedCat.

(**
 4. Transport on pseudofunctors into categories
 *)
Proposition transportf_psfunctor_into_cat
            {C : category}
            {F : psfunctor (cat_to_bicat C^op) bicat_of_univ_cats}
            {x y : C}
            (f : x --> y)
            (yy : pr1 (F y))
            {g h : x --> y}
            (p : g = h)
            (ff : pr1 (# F f) yy --> pr1 (# F g) yy)
  : transportf
      (λ z, pr1 (#F f) yy --> pr1 (#F z) yy)
      p
      ff
    =
    ff · pr1 (##F p) yy.
Proof.
  induction p ; cbn.
  refine (!(id_right _) @ _).
  apply maponpaths.
  refine (!(nat_trans_eq_pointwise (psfunctor_id2 F _) _) @ _).
  refine (maponpaths (λ z, pr1 (##F z) yy) _).
  apply homset_property.
Qed.
