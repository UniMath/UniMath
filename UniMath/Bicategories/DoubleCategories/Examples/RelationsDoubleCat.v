(*************************************************************************************

 The double category of relations

 We define two double categories of relations: one is the double category of relations
 valued in propositions and the other is the double category of relations valued in
 sets. The first double category (relations valued in propositiions) is defined as
 follows:
 - Objects: sets
 - Vertical morphisms: functions
 - Horizontal morphisms: relations valued in `hProp`
 - Squares with sides `f : X₁ → Y₁`, `g : X₂ → Y₂`, `R₁ : X₁ → X₂ → hProp`, and
   `R₂ : Y₁ → Y₂ → hProp` are proofs that `R₂ (f x₁) (g x₂)` hold for all `x₁ : X₁` and
   `x₂ : X₂` such that `R₁ x₁ x₂`.
 The double category of relations valued in sets is defined similarly, but the only
 difference is that the horizontal morphisms are relations valued in `hSet`.

 Note that if you use relations valued in `hProp`, then you obtain a symmetric univalent
 pseudo double category. This is not the case for relations valued in `hSet`, which is
 caused by the fact that `hSet` is not an `hSet` while `hProp` is. In addition, relations
 valued in `hSet` are equivalent to spans of sets.

 Contents
 1. Relations valued in propositions
 1.1. Horizontal identities
 1.2. Horizontal composition
 1.3. The unitors and associators
 1.4. The triangle and pentagon equations
 1.5. The double category of relations valued in propositions
 1.6. Companions and conjoints
 2. Relations valued in sets
 2.1. Horizontal identities
 2.2. Horizontal composition
 2.3. The unitors and associators
 2.4. The triangle and pentagon equations
 2.5. The double category of relations
 2.6. Companions and conjoints

 *************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Relations.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Categories.Rel.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DoubleCategories.Basics.DoubleCategoryBasics.
Require Import UniMath.Bicategories.DoubleCategories.Core.DoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.UnivalentDoubleCats.
Require Import UniMath.Bicategories.DoubleCategories.Core.SymmetricUnivalent.
Require Import UniMath.Bicategories.DoubleCategories.Core.CompanionsAndConjoints.

Local Open Scope cat.
Local Open Scope double_cat.

(** * 1. Relations valued in propositions *)

(** * 1.1. Horizontal identities *)
Definition rel_double_cat_hor_id_data
  : hor_id_data rel_disp_cat.
Proof.
  use make_hor_id_data.
  - exact (λ X x y, (x = y)%logic).
  - abstract
      (exact (λ X Y f x y p, maponpaths f p)).
Defined.

Proposition rel_double_cat_hor_id_laws
  : hor_id_laws rel_double_cat_hor_id_data.
Proof.
  split ; intros ; repeat (use funextsec ; intro) ; apply propproperty.
Qed.

Definition rel_double_cat_hor_id
  : hor_id rel_disp_cat.
Proof.
  use make_hor_id.
  - exact rel_double_cat_hor_id_data.
  - exact rel_double_cat_hor_id_laws.
Defined.

(** * 1.2. Horizontal composition *)
Definition rel_double_cat_hor_comp_data
  : hor_comp_data rel_disp_cat.
Proof.
  use make_hor_comp_data.
  - exact (λ (X Y Z : hSet) R₁ R₂ x z, ∃ (y : Y), R₁ x y × R₂ y z).
  - abstract
      (refine (λ (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : hSet)
                 (f : X₁ → X₂)
                 (g : Y₁ → Y₂)
                 (h : Z₁ → Z₂)
                 (R₁ : X₁ → Y₁ → hProp)
                 (S₁ : Y₁ → Z₁ → hProp)
                 (R₂ : X₂ → Y₂ → hProp)
                 (S₂ : Y₂ → Z₂ → hProp)
                 fR gR x z,
               _) ;
       use factor_through_squash_hProp ;
       intros ( y & p & q ) ;
       use hinhpr ;
       exact (g y ,, fR _ _ p ,, gR _ _ q)).
Defined.

Proposition rel_double_cat_hor_comp_laws
  : hor_comp_laws rel_double_cat_hor_comp_data.
Proof.
  split ; intros ; repeat (use funextsec ; intro) ; apply propproperty.
Qed.

Definition rel_double_cat_hor_comp
  : hor_comp rel_disp_cat.
Proof.
  use make_hor_comp.
  - exact rel_double_cat_hor_comp_data.
  - exact rel_double_cat_hor_comp_laws.
Defined.

(** * 1.3. The unitors and associators *)
Definition rel_double_cat_lunitor_data
  : double_lunitor_data
      rel_double_cat_hor_id
      rel_double_cat_hor_comp.
Proof.
  intros X Y R.
  use to_iso_rel_disp_cat.
  intros x y.
  split.
  - use factor_through_squash_hProp.
    intros ( x' & p & q ).
    cbn in *.
    induction p.
    exact q.
  - intros p.
    use hinhpr.
    cbn.
    refine (x ,, idpath _ ,, _).
    exact p.
Qed.

Proposition rel_double_cat_lunitor_laws
  : double_lunitor_laws rel_double_cat_lunitor_data.
Proof.
  intro ; intros ; repeat (use funextsec ; intro) ; apply propproperty.
Qed.

Definition rel_double_cat_lunitor
  : double_cat_lunitor
      rel_double_cat_hor_id
      rel_double_cat_hor_comp.
Proof.
  use make_double_lunitor.
  - exact rel_double_cat_lunitor_data.
  - exact rel_double_cat_lunitor_laws.
Defined.

Definition rel_double_cat_runitor_data
  : double_runitor_data
      rel_double_cat_hor_id
      rel_double_cat_hor_comp.
Proof.
  intros X Y R.
  use to_iso_rel_disp_cat.
  intros x y.
  split.
  - use factor_through_squash_hProp.
    intros ( x' & p & q ).
    cbn in *.
    induction q.
    exact p.
  - intros p.
    use hinhpr.
    cbn.
    refine (y ,, _ ,, idpath _).
    exact p.
Qed.

Proposition rel_double_cat_runitor_laws
  : double_runitor_laws rel_double_cat_runitor_data.
Proof.
  intro ; intros ; repeat (use funextsec ; intro) ; apply propproperty.
Qed.

Definition rel_double_cat_runitor
  : double_cat_runitor
      rel_double_cat_hor_id
      rel_double_cat_hor_comp.
Proof.
  use make_double_runitor.
  - exact rel_double_cat_runitor_data.
  - exact rel_double_cat_runitor_laws.
Defined.

Definition rel_double_cat_associator_data
  : double_associator_data rel_double_cat_hor_comp.
Proof.
  intros W X Y Z R₁ R₂ R₃.
  use to_iso_rel_disp_cat.
  intros w z.
  split.
  - use factor_through_squash_hProp.
    intros ( x & p₁ & q ).
    revert q.
    use factor_through_squash_hProp.
    intros ( y & p₂ & p₃ ).
    use hinhpr.
    refine (y ,, _ ,, _).
    + use hinhpr.
      exact (x ,, p₁ ,, p₂).
    + exact p₃.
  - use factor_through_squash_hProp.
    intros ( y & q & p₃ ).
    revert q.
    use factor_through_squash_hProp.
    intros ( x & p₁ & p₂ ).
    use hinhpr.
    refine (x ,, _ ,, _).
    + exact p₁.
    + use hinhpr.
      exact (y ,, p₂ ,, p₃).
Defined.

Proposition rel_double_cat_associator_laws
  : double_associator_laws rel_double_cat_associator_data.
Proof.
  intro ; intros ; repeat (use funextsec ; intro) ; apply propproperty.
Qed.

Definition rel_double_cat_associator
  : double_cat_associator rel_double_cat_hor_comp.
Proof.
  use make_double_associator.
  - exact rel_double_cat_associator_data.
  - exact rel_double_cat_associator_laws.
Defined.

(** * 1.4. The triangle and pentagon equations *)
Proposition rel_double_cat_triangle
  : triangle_law
      rel_double_cat_lunitor
      rel_double_cat_runitor
      rel_double_cat_associator.
Proof.
  intro ; intros ; repeat (use funextsec ; intro) ; apply propproperty.
Qed.

Proposition rel_double_cat_pentagon
  : pentagon_law rel_double_cat_associator.
Proof.
  intro ; intros ; repeat (use funextsec ; intro) ; apply propproperty.
Qed.

(** * 1.5. The double category of relations valued in propositions *)
Definition rel_double_cat
  : double_cat.
Proof.
  use make_double_cat.
  - exact SET.
  - exact rel_disp_cat.
  - exact rel_double_cat_hor_id.
  - exact rel_double_cat_hor_comp.
  - exact rel_double_cat_lunitor.
  - exact rel_double_cat_runitor.
  - exact rel_double_cat_associator.
  - exact rel_double_cat_triangle.
  - exact rel_double_cat_pentagon.
Defined.

Definition rel_univalent_double_cat
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact rel_double_cat.
  - split.
    + exact is_univalent_HSET.
    + exact is_univalent_rel_twosided_disp_cat.
Defined.

Definition symmetric_univalent_rel_univalent_double_cat
  : symmetric_univalent rel_univalent_double_cat.
Proof.
  use make_symmetric_univalent.
  - intros X Y.
    use funspace_isaset.
    use funspace_isaset.
    apply isasethProp.
  - intros X Y.
    use weqhomot.
    + exact (bin_hrel_z_iso_equiv_hset_z_iso X Y ∘ make_weq _ (is_univalent_HSET X Y))%weq.
    + intro p ; induction p.
      use (z_iso_eq (C := REL)).
      do 2 (apply funextsec ; intro).
      apply idpath.
  - intros X X' Y Y' p q f g.
    induction p, q.
    cbn in X, Y, f, g.
    use isweqimplimpl.
    + intro p.
      use funextsec.
      intro x ; cbn.
      apply (pr1 p x).
      apply idpath.
    + use funspace_isaset.
      apply setproperty.
    + use isaproptotal2.
      * intro.
        apply isaprop_is_iso_twosided_disp.
      * intros.
        do 3 (use funextsec ; intro).
        apply setproperty.
Qed.

Definition rel_double_cat_ver_weq_square
  : ver_weq_square rel_double_cat.
Proof.
  refine (λ (X Y : hSet) (f g : X → Y), _).
  use isweqimplimpl.
  - cbn.
    intro p.
    apply funextsec.
    intros x.
    apply p.
    apply idpath.
  - use funspace_isaset.
    apply setproperty.
  - repeat (use impred ; intro).
    apply propproperty.
Qed.

(** * 1.6. Companions and conjoints *)
Definition all_companions_rel
  : all_companions_double_cat rel_double_cat.
Proof.
  refine (λ (X Y : hSet) (f : X → Y), _).
  simple refine (_ ,, _).
  - exact (λ x y, (f x = y)%logic).
  - use make_double_cat_are_companions'.
    + abstract
        (exact (λ x y p, p)).
    + abstract
        (exact (λ x y p, maponpaths f p)).
    + abstract
        (repeat (use funextsec ; intro) ; apply propproperty).
    + abstract
        (repeat (use funextsec ; intro) ; apply propproperty).
Defined.

Definition all_conjoints_rel
  : all_conjoints_double_cat rel_double_cat.
Proof.
  refine (λ (X Y : hSet) (f : X → Y), _).
  simple refine (_ ,, _).
  - exact (λ y x, (f x = y)%logic).
  - use make_double_cat_are_conjoints'.
    + abstract
        (refine (λ x y p, maponpaths f (!p))).
    + abstract
        (exact (λ x y p, !p)).
    + abstract
        (repeat (use funextsec ; intro) ; apply propproperty).
    + abstract
        (repeat (use funextsec ; intro) ; apply propproperty).
Defined.

(** * 2. Relations valued in sets *)

(** * 2.1. Horizontal identities *)
Definition set_rel_double_cat_hor_id_data
  : hor_id_data set_rel_disp_cat.
Proof.
  use make_hor_id_data.
  - exact (λ X x y, hProp_to_hSet (x = y)%logic).
  - abstract
      (exact (λ X Y f x y p, maponpaths f p)).
Defined.

Proposition set_rel_double_cat_hor_id_laws
  : hor_id_laws set_rel_double_cat_hor_id_data.
Proof.
  split ; intros ; repeat (use funextsec ; intro) ; apply propproperty.
Qed.

Definition set_rel_double_cat_hor_id
  : hor_id set_rel_disp_cat.
Proof.
  use make_hor_id.
  - exact set_rel_double_cat_hor_id_data.
  - exact set_rel_double_cat_hor_id_laws.
Defined.

(** * 2.2. Horizontal composition *)
Definition set_rel_double_cat_hor_comp_data
  : hor_comp_data set_rel_disp_cat.
Proof.
  use make_hor_comp_data.
  - refine (λ (X Y Z : hSet) R₁ R₂ x z, make_hSet (∑ (y : Y), R₁ x y × R₂ y z) _).
    abstract
      (use isaset_total2 ; [ apply setproperty | ] ;
       intro ;
       apply isasetdirprod ; apply setproperty).
  - exact (λ (X₁ X₂ Y₁ Y₂ Z₁ Z₂ : hSet)
             (f : X₁ → X₂)
             (g : Y₁ → Y₂)
             (h : Z₁ → Z₂)
             (R₁ : X₁ → Y₁ → hSet)
             (S₁ : Y₁ → Z₁ → hSet)
             (R₂ : X₂ → Y₂ → hSet)
             (S₂ : Y₂ → Z₂ → hSet)
             (fR : ∏ (x : X₁) (y : Y₁), R₁ x y → R₂ (f x) (g y))
             (gR : ∏ (x : Y₁) (y : Z₁), S₁ x y → S₂ (g x) (h y))
             (x : X₁)
             (z : Z₁)
             (p : ∑ (y : Y₁), R₁ x y × S₁ y z),
           g (pr1 p) ,, fR _ _ (pr12 p) ,, gR _ _ (pr22 p)).
Defined.

Proposition set_rel_double_cat_hor_comp_laws
  : hor_comp_laws set_rel_double_cat_hor_comp_data.
Proof.
  split ; intro ; intros ; apply idpath.
Qed.

Definition set_rel_double_cat_hor_comp
  : hor_comp set_rel_disp_cat.
Proof.
  use make_hor_comp.
  - exact set_rel_double_cat_hor_comp_data.
  - exact set_rel_double_cat_hor_comp_laws.
Defined.

(** * 2.3. The unitors and associators *)
Definition set_rel_double_cat_lunitor_data
  : double_lunitor_data
      set_rel_double_cat_hor_id
      set_rel_double_cat_hor_comp.
Proof.
  refine (λ (X Y : hSet) (R : X → Y → hSet), _).
  use to_iso_set_rel_disp_cat.
  intros x y ; cbn.
  use weq_iso.
  - exact (λ p, transportf (λ z, R z y) (!(pr12 p)) (pr22 p)).
  - exact (λ p, x ,, idpath _ ,, p).
  - abstract
      (intros p ;
       induction p as [ x' [ p q ]] ;
       induction p ;
       apply idpath).
  - abstract
      (intro ;
       apply idpath).
Defined.

Proposition set_rel_double_cat_lunitor_laws
  : double_lunitor_laws set_rel_double_cat_lunitor_data.
Proof.
  intros X₁ X₂ Y₁ Y₂ R₁ R₂ f g fgR.
  use funextsec ; intro x.
  use funextsec ; intro y.
  use funextsec ; intro p.
  etrans.
  {
    apply transportf_set_rel.
  }
  cbn.
  induction p as [ y' [ p q ]].
  induction p.
  cbn.
  etrans.
  {
    apply maponpaths.
    use (transportf_set (R₂ (f x))).
    apply setproperty.
  }
  apply maponpaths_2.
  apply setproperty.
Qed.

Definition set_rel_double_cat_lunitor
  : double_cat_lunitor
      set_rel_double_cat_hor_id
      set_rel_double_cat_hor_comp.
Proof.
  use make_double_lunitor.
  - exact set_rel_double_cat_lunitor_data.
  - exact set_rel_double_cat_lunitor_laws.
Defined.

Definition set_rel_double_cat_runitor_data
  : double_runitor_data
      set_rel_double_cat_hor_id
      set_rel_double_cat_hor_comp.
Proof.
  refine (λ (X Y : hSet) (R : X → Y → hSet), _).
  use to_iso_set_rel_disp_cat.
  intros x y ; cbn.
  use weq_iso.
  - exact (λ p, transportf (λ z, R x z) (pr22 p) (pr12 p)).
  - exact (λ p, y ,, p ,, idpath _).
  - abstract
      (intros p ;
       induction p as [ x' [ p q ]] ;
       induction q ;
       apply idpath).
  - abstract
      (intro ;
       apply idpath).
Defined.

Proposition set_rel_double_cat_runitor_laws
  : double_runitor_laws set_rel_double_cat_runitor_data.
Proof.
  intros X₁ X₂ Y₁ Y₂ R₁ R₂ f g fgR.
  use funextsec ; intro x.
  use funextsec ; intro y.
  use funextsec ; intro p.
  etrans.
  {
    apply transportf_set_rel.
  }
  cbn.
  induction p as [ y' [ p q ]].
  induction q.
  cbn.
  etrans.
  {
    apply maponpaths.
    use (transportf_set (R₂ (f x))).
    apply setproperty.
  }
  etrans.
  {
    use (transportf_set (λ z, R₂ z _)).
    apply setproperty.
  }
  refine (!_).
  etrans.
  {
    use (transportf_set (R₂ (f x))).
    apply setproperty.
  }
  apply idpath.
Qed.

Definition set_rel_double_cat_runitor
  : double_cat_runitor
      set_rel_double_cat_hor_id
      set_rel_double_cat_hor_comp.
Proof.
  use make_double_runitor.
  - exact set_rel_double_cat_runitor_data.
  - exact set_rel_double_cat_runitor_laws.
Defined.

Definition set_rel_double_cat_associator_data
  : double_associator_data set_rel_double_cat_hor_comp.
Proof.
  refine (λ (W X Y Z : hSet)
            (R₁ : W → X → hSet)
            (R₂ : X → Y → hSet)
            (R₃ : Y → Z → hSet),
          _).
  use to_iso_set_rel_disp_cat.
  intros w z.
  cbn.
  use weq_iso.
  - simple refine (λ p, _ ,, (_ ,, _ ,, _) ,, _).
    + exact (pr1 (pr22 p)).
    + exact (pr1 p).
    + exact (pr12 p).
    + exact (pr12 (pr22 p)).
    + exact (pr22 (pr22 p)).
  - simple refine (λ p, _ ,, _ ,, (_ ,, _ ,, _)).
    + exact (pr1 (pr12 p)).
    + exact (pr12 (pr12 p)).
    + exact (pr1 p).
    + exact (pr22 (pr12 p)).
    + exact (pr22 p).
  - abstract
      (intro p ;
       apply idpath).
  - abstract
      (intro p ;
       apply idpath).
Defined.

Proposition set_rel_double_cat_associator_laws
  : double_associator_laws set_rel_double_cat_associator_data.
Proof.
  intros W₁ W₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ R₁ R₂ S₁ S₂ T₁ T₂ f g h k H₁ H₂ H₃.
  use funextsec ; intro x.
  use funextsec ; intro y.
  use funextsec ; intro p.
  etrans.
  {
    apply transportf_set_rel.
  }
  cbn.
  etrans.
  {
    apply maponpaths.
    use transportf_set.
    apply setproperty.
  }
  etrans.
  {
    use transportf_set.
    apply setproperty.
  }
  apply idpath.
Qed.

Definition set_rel_double_cat_associator
  : double_cat_associator set_rel_double_cat_hor_comp.
Proof.
  use make_double_associator.
  - exact set_rel_double_cat_associator_data.
  - exact set_rel_double_cat_associator_laws.
Defined.

(** * 2.4. The triangle and pentagon equations *)
Proposition set_rel_double_cat_triangle
  : triangle_law
      set_rel_double_cat_lunitor
      set_rel_double_cat_runitor
      set_rel_double_cat_associator.
Proof.
  intros X Y Z R₁ R₂.
  use funextsec ; intro x.
  use funextsec ; intro y.
  use funextsec ; intro p.
  refine (!_).
  etrans.
  {
    apply transportf_set_rel.
  }
  cbn.
  etrans.
  {
    apply maponpaths.
    use transportf_set.
    apply setproperty.
  }
  etrans.
  {
    use transportf_set.
    apply setproperty.
  }
  cbn in p.
  induction p as [ y' [ p [ y'' [ q r ]]]].
  induction q.
  cbn.
  apply idpath.
Qed.

Proposition set_rel_double_cat_pentagon
  : pentagon_law set_rel_double_cat_associator.
Proof.
  intros V W X Y Z R₁ R₂ R₃ R₄.
  use funextsec ; intro x.
  use funextsec ; intro y.
  use funextsec ; intro p.
  etrans.
  {
    apply transportf_set_rel.
  }
  cbn.
  etrans.
  {
    apply maponpaths.
    use transportf_set.
    apply setproperty.
  }
  etrans.
  {
    use transportf_set.
    apply setproperty.
  }
  apply idpath.
Qed.

(** * 2.5. The double category of relations *)
Definition set_rel_double_cat
  : double_cat.
Proof.
  use make_double_cat.
  - exact SET.
  - exact set_rel_disp_cat.
  - exact set_rel_double_cat_hor_id.
  - exact set_rel_double_cat_hor_comp.
  - exact set_rel_double_cat_lunitor.
  - exact set_rel_double_cat_runitor.
  - exact set_rel_double_cat_associator.
  - exact set_rel_double_cat_triangle.
  - exact set_rel_double_cat_pentagon.
Defined.

Definition set_rel_univalent_double_cat
  : univalent_double_cat.
Proof.
  use make_univalent_double_cat.
  - exact set_rel_double_cat.
  - split.
    + exact is_univalent_HSET.
    + exact is_univalent_set_rel_twosided_disp_cat.
Defined.

Definition set_rel_double_cat_ver_weq_square
  : ver_weq_square set_rel_double_cat.
Proof.
  refine (λ (X Y : hSet) (f g : X → Y), _).
  use isweqimplimpl.
  - cbn.
    intro p.
    apply funextsec.
    intros x.
    apply p.
    apply idpath.
  - use funspace_isaset.
    apply setproperty.
  - repeat (use impred ; intro).
    apply propproperty.
Qed.

(** * 2.6. Companions and conjoints *)
Definition all_companions_set_rel
  : all_companions_double_cat set_rel_double_cat.
Proof.
  refine (λ (X Y : hSet) (f : X → Y), _).
  simple refine (_ ,, _).
  - exact (λ x y, hProp_to_hSet (f x = y)%logic).
  - use make_double_cat_are_companions'.
    + abstract
        (exact (λ x y p, p)).
    + abstract
        (exact (λ x y p, maponpaths f p)).
    + abstract
        (repeat (use funextsec ; intro) ; apply propproperty).
    + abstract
        (repeat (use funextsec ; intro) ; apply propproperty).
Defined.

Definition all_conjoints_set_rel
  : all_conjoints_double_cat set_rel_double_cat.
Proof.
  refine (λ (X Y : hSet) (f : X → Y), _).
  simple refine (_ ,, _).
  - exact (λ y x, hProp_to_hSet (f x = y)%logic).
  - use make_double_cat_are_conjoints'.
    + abstract
        (refine (λ x y p, maponpaths f (!p))).
    + abstract
        (exact (λ x y p, !p)).
    + abstract
        (repeat (use funextsec ; intro) ; apply propproperty).
    + abstract
        (repeat (use funextsec ; intro) ; apply propproperty).
Defined.
