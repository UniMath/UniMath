(**

 The displayed category of families of sets

 There are two common ways to construct the set model of type theory. The first way is to
 use the arrow category: we have a fibration from the arrow category of `SET` to `SET`,
 namely the codomain fibration. We can equip this fibration with the structure necessary
 for a comprehension category. To interpret type formers in this comprehension category,
 we use that `SET` is locally Cartesian closed.

 The other common way is to use an equivalent, but more convenient, presentation of the
 codomain fibration of sets, and for that we use families of sets. Specifically, we
 consider the fibration over `SET` such that the objects over `X : hSet` are families
 `Y : X → hSet`. Note that in set-theoretic foundations this fibration is a split
 replacement of the codomain fibration for sets.

 In this file, we establish basic facts about the fibration of families of sets. We first
 construct the necessary displayed category, and we show that it is univalent. We also
 constructor a comprehension functor, and we show that this functor is both Cartesian
 and fully faithful. Finally, we consider the structure of the fibers of this fibration.
 Specifically, we construct finite limits in each fiber, and we equip each fiber with
 a subobject classifier and a parameterized natural numbers object.

 Content
 1. The displayed categories of families of sets
 2. Isomorphisms in the displayed category of families of sets
 3. The displayed categories of families of sets is univalent
 4. A cleaving for this displayed category
 5. The comprehension functor
 6. Some useful lemmas
 7. The fiberwise terminal object
 8. Fiberwise binary products
 9. Fiberwise equalizers
 10. The family of elements equal to some given element
 11. The fiberwise subobject classifier
 12. The fiberwise parameterized natural numbers object

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.PreservesSubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseSubobjectClassifier.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.

Local Open Scope cat.

(** * 1. The displayed categories of families of sets *)
Definition fam_disp_cat_ob_mor
  : disp_cat_ob_mor HSET.
Proof.
  simple refine (_ ,, _).
  - exact (λ (X : hSet), X → hSet).
  - exact (λ (X₁ X₂ : hSet)
             (Y₁ : X₁ → hSet)
             (Y₂ : X₂ → hSet)
             (f : X₁ → X₂),
           ∏ (x : X₁), Y₁ x → Y₂ (f x)).
Defined.

Definition fam_disp_cat_id_comp
  : disp_cat_id_comp SET fam_disp_cat_ob_mor.
Proof.
  simple refine (_ ,, _).
  - exact (λ (X : hSet) (Y : X → hSet) (x : X) (y : Y x), y).
  - exact (λ (X₁ X₂ X₃ : hSet)
             (f : X₁ → X₂) (g : X₂ → X₃)
             (Y₁ : X₁ → hSet)
             (Y₂ : X₂ → hSet)
             (Y₃ : X₃ → hSet)
             (ff : ∏ (x : X₁), Y₁ x → Y₂ (f x))
             (gg : ∏ (x : X₂), Y₂ x → Y₃ (g x))
             (x : X₁)
             (y : Y₁ x),
           gg (f x) (ff x y)).
Defined.

Definition fam_disp_cat_data
  : disp_cat_data HSET.
Proof.
  simple refine (_ ,, _).
  - exact fam_disp_cat_ob_mor.
  - exact fam_disp_cat_id_comp.
Defined.

Proposition fam_disp_cat_transportb
            {X₁ X₂ : hSet}
            {f g : X₁ → X₂}
            (p : g = f)
            {Y₁ : fam_disp_cat_data X₁}
            {Y₂ : fam_disp_cat_data X₂}
            (ff : Y₁ -->[ f ] Y₂)
            (x : X₁)
            (y : Y₁ x)
  : transportb (λ (z : HSET ⟦ _ , _ ⟧), _ -->[ z ] _) p ff x y
    =
    transportb Y₂ (eqtohomot p x) (ff x y).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition fam_disp_cat_transportf
            {X₁ X₂ : hSet}
            {f g : X₁ → X₂}
            (p : f = g)
            {Y₁ : fam_disp_cat_data X₁}
            {Y₂ : fam_disp_cat_data X₂}
            (ff : Y₁ -->[ f ] Y₂)
            (x : X₁)
            (y : Y₁ x)
  : transportf (λ (z : HSET ⟦ _ , _ ⟧), _ -->[ z ] _) p ff x y
    =
    transportf Y₂ (eqtohomot p x) (ff x y).
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition fam_disp_cat_axioms
  : disp_cat_axioms SET fam_disp_cat_data.
Proof.
  repeat split.
  - intros X₁ X₂ f Y₁ Y₂ ff.
    use funextsec ; intro x.
    use funextsec ; intro y.
    rewrite fam_disp_cat_transportb.
    cbn.
    refine (!_).
    apply (transportf_set Y₂).
    apply setproperty.
  - intros X₁ X₂ f Y₁ Y₂ ff.
    use funextsec ; intro x.
    use funextsec ; intro y.
    rewrite fam_disp_cat_transportb.
    cbn.
    refine (!_).
    apply (transportf_set Y₂).
    apply setproperty.
  - intros X₁ X₂ X₃ X₄ f g h Y₁ Y₂ Y₃ Y₄ ff gg hh.
    use funextsec ; intro x.
    use funextsec ; intro y.
    rewrite fam_disp_cat_transportb.
    cbn.
    refine (!_).
    apply (transportf_set Y₄).
    apply setproperty.
  - intros X₁ X₂ f Y₁ Y₂.
    apply impred_isaset ; intro x.
    apply impred_isaset ; intro y.
    apply setproperty.
Qed.

Definition fam_disp_cat
  : disp_cat HSET.
Proof.
  simple refine (_ ,, _).
  - exact fam_disp_cat_data.
  - exact fam_disp_cat_axioms.
Defined.

(** * 2. Isomorphisms in the displayed category of families of sets *)
Definition make_z_iso_disp_fam_disp_cat
           {X : hSet}
           {Y₁ Y₂ : X → hSet}
           (ff : ∏ (x : X), Y₁ x ≃ Y₂ x)
  : z_iso_disp (D := fam_disp_cat) (identity_z_iso _) Y₁ Y₂.
Proof.
  simple refine (_ ,, _ ,, _ ,, _).
  - exact (λ x y, ff x y).
  - exact (λ x y, invmap (ff x) y).
  - abstract
      (use funextsec ; intro x ;
       use funextsec ; intro y ;
       rewrite fam_disp_cat_transportb ;
       cbn ;
       refine (homotweqinvweq (ff x) y @ !_) ;
       apply (transportf_set Y₂) ;
       apply setproperty).
  - abstract
      (use funextsec ; intro x ;
       use funextsec ; intro y ;
       rewrite fam_disp_cat_transportb ;
       cbn ;
       refine (homotinvweqweq (ff x) y @ !_) ;
       apply (transportf_set Y₁) ;
       apply setproperty).
Defined.

Definition from_z_iso_disp_fam_disp_cat
           {X : hSet}
           {Y₁ Y₂ : X → hSet}
           (ff : z_iso_disp (D := fam_disp_cat) (identity_z_iso _) Y₁ Y₂)
           (x : X)
  : Y₁ x ≃ Y₂ x.
Proof.
  use weq_iso.
  - exact (λ y, pr1 ff x y).
  - exact (λ y, pr12 ff x y).
  - abstract
      (intro y ;
       refine (eqtohomot (eqtohomot (pr222 ff) x) y @ _) ;
       rewrite fam_disp_cat_transportb ;
       apply (transportf_set Y₁) ;
       apply setproperty).
  - abstract
      (intro y ;
       refine (eqtohomot (eqtohomot (pr122 ff) x) y @ _) ;
       rewrite fam_disp_cat_transportb ;
       apply (transportf_set Y₂) ;
       apply setproperty).
Defined.

Definition fam_disp_cat_z_iso_weq
           {X : hSet}
           (Y₁ Y₂ : X → hSet)
  : (∏ (x : X), Y₁ x ≃ Y₂ x)
    ≃
    z_iso_disp (D := fam_disp_cat) (identity_z_iso _) Y₁ Y₂.
Proof.
  use weq_iso.
  - exact (λ ff, make_z_iso_disp_fam_disp_cat ff).
  - exact (λ ff, from_z_iso_disp_fam_disp_cat ff).
  - abstract
      (intros ff ;
       use funextsec ; intro x ;
       use subtypePath ; [ intro ; apply isapropisweq | ] ;
       apply idpath).
  - abstract
      (intros ff ;
       use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
       apply idpath).
Defined.

(** * 3. The displayed categories of families of sets is univalent *)
Proposition is_univalent_disp_fam_disp_cat
  : is_univalent_disp fam_disp_cat.
Proof.
  use is_univalent_disp_from_fibers.
  refine (λ (X : hSet) (Y₁ Y₂ : X → hSet), _).
  use weqhomot.
  - exact (fam_disp_cat_z_iso_weq _ _
           ∘ weqonsecfibers _ _ (λ x, hSet_univalence _ _)
           ∘ weqtoforallpaths _ _ _)%weq.
  - intro p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_z_iso_disp.
    }
    cbn.
    apply idpath.
Qed.

Definition univalent_fam_disp_cat
  : disp_univalent_category HSET.
Proof.
  simple refine (_ ,, _).
  - exact fam_disp_cat.
  - exact is_univalent_disp_fam_disp_cat.
Defined.

(** * 4. A cleaving for this displayed category *)
Definition cleaving_fam_disp_cat
  : cleaving fam_disp_cat.
Proof.
  refine (λ (X₂ X₁ : hSet) (f : X₁ → X₂) (Y₂ : X₂ → hSet), _).
  simple refine (_ ,, _).
  - exact (λ (x : X₁), Y₂ (f x)).
  - simple refine (_ ,, _).
    + exact (λ x y, y).
    + refine (λ (X₀ : hSet)
                (g : X₀ → X₁)
                (Y₀ : X₀ → hSet)
                (gg : ∏ (x : X₀), Y₀ x → Y₂ (f (g x))),
              _).
      use make_iscontr.
      * exact (gg ,, idpath _).
      * abstract
          (intros gg' ;
           use subtypePath ; [ intro ; apply homsets_disp | ] ;
           exact (pr2 gg')).
Defined.

(** * 5. The comprehension functor *)
Definition fam_disp_cat_comprehension_data
  : disp_functor_data (functor_identity _) fam_disp_cat (disp_codomain HSET).
Proof.
  simple refine (_ ,, _).
  - exact (λ (X : hSet) (Y : X → hSet), (∑ (x : X), Y x)%set ,, pr1).
  - exact (λ (X₁ X₂ : hSet)
             (Y₁ : X₁ → hSet)
             (Y₂ : X₂ → hSet)
             (f : X₁ → X₂)
             (ff : ∏ (x : X₁), Y₁ x → Y₂ (f x)),
           (λ (xy : ∑ (x : X₁), Y₁ x), f (pr1 xy) ,, ff (pr1 xy) (pr2 xy))
           ,,
           idpath _).
Defined.

Proposition fam_disp_cat_comprehension_axioms
  : disp_functor_axioms fam_disp_cat_comprehension_data.
Proof.
  split.
  - intros X Y.
    use subtypePath ; [ intro ; apply homset_property | ].
    cbn.
    apply idpath.
  - intros X₁ X₂ X₃ Y₁ Y₂ Y₃ f g ff gg.
    use subtypePath ; [ intro ; apply homset_property | ].
    cbn.
    apply idpath.
Qed.

Definition fam_disp_cat_comprehension
  : disp_functor (functor_identity _) fam_disp_cat (disp_codomain HSET).
Proof.
  simple refine (_ ,, _).
  - exact fam_disp_cat_comprehension_data.
  - exact fam_disp_cat_comprehension_axioms.
Defined.

Proposition is_cartesian_fam_disp_cat_comprehension
  : is_cartesian_disp_functor fam_disp_cat_comprehension.
Proof.
  use is_cartesian_disp_functor_chosen_lifts.
  {
    exact cleaving_fam_disp_cat.
  }
  refine (λ (X₁ X₂ : hSet) (f : X₁ → X₂) (Y : X₂ → hSet), _).
  use isPullback_cartesian_in_cod_disp.
  cbn.
  refine (λ (W : hSet) (g₁ : W → ∑ (x : X₂), Y x) (g₂ : W → X₁), _).
  intro p.
  use make_iscontr.
  - simple refine (_ ,, _ ,, _).
    + exact (λ (w : W),
             g₂ w
             ,,
             transportf Y (eqtohomot p w) (pr2 (g₁ w))).
    + abstract
        (use funextsec ; intro w ;
         refine (!_) ;
         use total2_paths_f ; [ exact (eqtohomot p w) | ] ;
         cbn ;
         apply idpath).
    + abstract
        (cbn ;
         apply idpath).
  - abstract
      (intros h ;
       use subtypePath ;
       [ intro ; apply isapropdirprod ; apply homset_property | ] ;
       use funextsec ; intro w ;
       cbn ;
       use total2_paths_f ; [ exact (eqtohomot (pr22 h) w) | ] ;
       cbn ;
       rewrite (functtransportf f Y) ;
       pose (fiber_paths (eqtohomot (pr12 h) w)) as q ;
       cbn in q ;
       rewrite <- q ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply setproperty).
Defined.

Proposition disp_functor_ff_fam_disp_cat_comprehension
  : disp_functor_ff fam_disp_cat_comprehension.
Proof.
  refine (λ (X₁ X₂ : hSet) (Y₁ : X₁ → hSet) (Y₂ : X₂ → hSet) (f : X₁ → X₂), _).
  use isweq_iso.
  - cbn.
    intros ff x y.
    exact (transportf Y₂ (eqtohomot (pr2 ff) (x ,, y)) (pr2 (pr1 ff (x ,, y)))).
  - abstract
      (intros ff ; cbn ;
       apply idpath).
  - abstract
      (intros ff ;
       use subtypePath ; [ intro ; apply homset_property | ] ;
       use funextsec ;
       intros xy ; cbn ;
       refine (!_) ;
       use total2_paths_f ; [ exact (eqtohomot (pr2 ff) xy) | ] ;
       cbn ;
       apply idpath).
Defined.

(** * 6. Some useful lemmas *)
Proposition fam_disp_cat_fiber_comp
            {X : hSet}
            {Y₁ Y₂ Y₃ : X → hSet}
            (ff : (fam_disp_cat [{ X }]) ⟦ Y₁ , Y₂ ⟧)
            (gg : (fam_disp_cat [{ X }]) ⟦ Y₂ , Y₃ ⟧)
            {x : X}
            (y : Y₁ x)
  : (ff · gg) x y = gg x (ff x y).
Proof.
  cbn.
  etrans.
  {
    exact (fam_disp_cat_transportf (id_right (C := HSET) _) _ x y).
  }
  apply (transportf_set Y₃).
  apply setproperty.
Qed.

Proposition fam_disp_cat_fiber_functor_from_cleaving
            {X₁ X₂ : hSet}
            (f : X₁ → X₂)
            {Y₁ Y₂ : X₂ → hSet}
            (ff : ∏ (x : X₂), Y₁ x → Y₂ x)
            {x : X₁}
            (y : Y₁ (f x))
  : #(fiber_functor_from_cleaving fam_disp_cat cleaving_fam_disp_cat f) ff x y
    =
    ff (f x) y.
Proof.
  cbn.
  etrans.
  {
    exact (fam_disp_cat_transportf (id_right (C := HSET) _ @ !(id_left _)) _ x y).
  }
  apply (transportf_set Y₂).
  apply setproperty.
Qed.

Proposition fam_disp_cat_fiber_functor_from_cleaving_comp
            {X₁ X₂ X₃ : hSet}
            (f₁ : X₁ → X₂)
            (f₂ : X₂ → X₃)
            (Y : X₃ → hSet)
            {x : X₁}
            (y : Y (f₂ (f₁ x)))
  : fiber_functor_from_cleaving_comp cleaving_fam_disp_cat f₂ f₁ Y x y = y.
Proof.
  cbn -[fam_disp_cat].
  etrans.
  {
    exact (fam_disp_cat_transportb _ (_ ;; _)%mor_disp x _).
  }
  apply (transportf_set Y).
  apply setproperty.
Qed.

Proposition fam_disp_cat_fiber_functor_from_cleaving_comp_inv
            {X₁ X₂ X₃ : hSet}
            (f₁ : X₁ → X₂)
            (f₂ : X₂ → X₃)
            (Y : X₃ → hSet)
            {x : X₁}
            (y : Y (f₂ (f₁ x)))
  : fiber_functor_from_cleaving_comp_inv cleaving_fam_disp_cat f₂ f₁ Y x y = y.
Proof.
  cbn -[fam_disp_cat].
  etrans.
  {
    exact (fam_disp_cat_transportf _ _ _ _).
  }
  apply (transportf_set Y).
  apply setproperty.
Qed.

Proposition fam_disp_cat_fiber_functor_on_eq
            {X₁ X₂ : hSet}
            {f g : X₁ → X₂}
            (p : f = g)
            (Y : X₂ → hSet)
            {x : X₁}
            (y : Y (f x))
  : fiber_functor_on_eq cleaving_fam_disp_cat p Y x y
    =
    transportf Y (eqtohomot p x) y.
Proof.
  induction p ; cbn.
  apply idpath.
Qed.

Proposition fam_disp_cat_comm_nat_z_iso
            {X₁ X₂ X₃ X₄ : hSet}
            (f : X₂ → X₁)
            (g : X₃ → X₁)
            (h : X₄ → X₃)
            (k : X₄ → X₂)
            (p : (λ x, f(k x)) = (λ x, g(h x)))
            (Y : X₁ → hSet)
            {x : X₄}
            (y : Y (f (k x)))
  : comm_nat_z_iso cleaving_fam_disp_cat f g h k p Y x y
    =
    transportf Y (eqtohomot p x) y.
Proof.
  rewrite comm_nat_z_iso_ob.
  rewrite !fam_disp_cat_fiber_comp.
  etrans.
  {
    do 2 apply maponpaths.
    apply fam_disp_cat_fiber_functor_from_cleaving_comp.
  }
  etrans.
  {
    apply maponpaths.
    apply fam_disp_cat_fiber_functor_on_eq.
  }
  apply fam_disp_cat_fiber_functor_from_cleaving_comp_inv.
Qed.

Proposition fam_disp_cat_comm_nat_z_iso_inv
            {X₁ X₂ X₃ X₄ : hSet}
            (f : X₂ → X₁)
            (g : X₃ → X₁)
            (h : X₄ → X₃)
            (k : X₄ → X₂)
            (p : (λ x, f(k x)) = (λ x, g(h x)))
            (Y : X₁ → hSet)
            {x : X₄}
            (y : Y (g (h x)))
  : comm_nat_z_iso_inv cleaving_fam_disp_cat f g h k p Y x y
    =
    transportb Y (eqtohomot p x) y.
Proof.
  rewrite comm_nat_z_iso_inv_ob.
  rewrite !fam_disp_cat_fiber_comp.
  etrans.
  {
    do 2 apply maponpaths.
    apply fam_disp_cat_fiber_functor_from_cleaving_comp.
  }
  etrans.
  {
    apply maponpaths.
    apply fam_disp_cat_fiber_functor_on_eq.
  }
  etrans.
  {
    apply fam_disp_cat_fiber_functor_from_cleaving_comp_inv.
  }
  unfold transportb.
  apply maponpaths_2.
  apply setproperty.
Qed.

(** * 7. The fiberwise terminal object *)
Definition fam_disp_cat_fiber_terminal
           (X : hSet)
  : Terminal (fam_disp_cat [{ X }]).
Proof.
  use make_Terminal.
  - exact (λ (x : X), unitset).
  - refine (λ (Y : X → hSet), _).
    use make_iscontr.
    + exact (λ (x : X) (y : Y x), tt).
    + abstract
        (intros ff ;
         use funextsec ; intro x ;
         use funextsec ; intro y ;
         apply isapropunit).
Defined.

Proposition preserves_terminal_fiber_functor_fam_disp_cat
            {X₁ X₂ : hSet}
            (f : X₁ → X₂)
  : preserves_terminal
      (fiber_functor_from_cleaving fam_disp_cat cleaving_fam_disp_cat f).
Proof.
  use preserves_terminal_if_preserves_chosen.
  {
    apply fam_disp_cat_fiber_terminal.
  }
  use iso_to_Terminal.
  {
    apply fam_disp_cat_fiber_terminal.
  }
  use make_z_iso.
  - exact (λ _ _, tt).
  - exact (λ _ _, tt).
  - split.
    + abstract
        (use funextsec ; intro x ;
         use funextsec ; intro y ;
         apply isapropunit).
    + abstract
        (use funextsec ; intro x ;
         use funextsec ; intro y ;
         apply isapropunit).
Defined.

Definition fam_disp_cat_fiberwise_terminal
  : fiberwise_terminal cleaving_fam_disp_cat.
Proof.
  split.
  - exact fam_disp_cat_fiber_terminal.
  - intros X₁ X₂ f.
    exact (preserves_terminal_fiber_functor_fam_disp_cat f).
Defined.

(** * 8. Fiberwise binary products *)
Definition fam_disp_cat_fiber_binproducts
           (X : hSet)
  : BinProducts (fam_disp_cat [{ X }]).
Proof.
  refine (λ (Y₁ Y₂ : X → hSet), _).
  use make_BinProduct.
  - exact (λ (x : X), Y₁ x × Y₂ x)%set.
  - exact (λ (x : X) (y : Y₁ x × Y₂ x), pr1 y).
  - exact (λ (x : X) (y : Y₁ x × Y₂ x), pr2 y).
  - refine (λ (Y₀ : X → hSet)
              (ff : ∏ (x : X), Y₀ x → Y₁ x)
              (gg : ∏ (x : X), Y₀ x → Y₂ x), _).
    use make_iscontr.
    + refine ((λ (x : X) (y : Y₀ x), ff x y ,, gg x y) ,, _ ,, _).
      * abstract
          (use funextsec ; intro x ;
           use funextsec ; intro y ;
           apply fam_disp_cat_fiber_comp).
      * abstract
          (use funextsec ; intro x ;
           use funextsec ; intro y ;
           apply fam_disp_cat_fiber_comp).
    + abstract
        (intros hh ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         use funextsec ; intro x ;
         use funextsec ; intro y ;
         cbn ;
         pose (p₁ := eqtohomot (eqtohomot (pr12 hh) x) y) ;
         pose (p₂ := eqtohomot (eqtohomot (pr22 hh) x) y) ;
         rewrite fam_disp_cat_fiber_comp in p₁ ;
         rewrite fam_disp_cat_fiber_comp in p₂ ;
         exact (pathsdirprod p₁ p₂)).
Defined.

Proposition preserves_binproduct_fiber_functor_fam_disp_cat
            {X₁ X₂ : hSet}
            (f : X₁ → X₂)
  : preserves_binproduct
      (fiber_functor_from_cleaving fam_disp_cat cleaving_fam_disp_cat f).
Proof.
  use preserves_binproduct_if_preserves_chosen.
  {
    apply fam_disp_cat_fiber_binproducts.
  }
  intros Y₁ Y₂.
  use (isBinProduct_z_iso (isBinProduct_BinProduct _ (fam_disp_cat_fiber_binproducts _ _ _))).
  - use make_z_iso.
    + exact (λ x y, y).
    + exact (λ x y, y).
    + abstract
        (split ;
         use funextsec ; intro x ;
         use funextsec ; intro y ;
         rewrite fam_disp_cat_fiber_comp ;
         cbn ;
         apply idpath).
  - use funextsec ; intro x.
    use funextsec ; intro y.
    cbn -[fiber_category fiber_functor_from_cleaving].
    etrans.
    {
      apply fam_disp_cat_fiber_functor_from_cleaving.
    }
    rewrite fam_disp_cat_fiber_comp.
    apply idpath.
  - use funextsec ; intro x.
    use funextsec ; intro y.
    cbn -[fiber_category fiber_functor_from_cleaving].
    etrans.
    {
      apply fam_disp_cat_fiber_functor_from_cleaving.
    }
    rewrite fam_disp_cat_fiber_comp.
    apply idpath.
Qed.

Definition fam_disp_cat_fiberwise_binproduct
  : fiberwise_binproducts cleaving_fam_disp_cat.
Proof.
  split.
  - exact fam_disp_cat_fiber_binproducts.
  - intros X₁ X₂ f.
    exact (preserves_binproduct_fiber_functor_fam_disp_cat f).
Defined.

(** * 9. Fiberwise equalizers *)
Definition fam_disp_cat_fiber_equalizers
           (X : hSet)
  : Equalizers (fam_disp_cat [{ X }]).
Proof.
  refine (λ (Y₁ Y₂ : X → hSet) (ff gg : ∏ (x : X), Y₁ x → Y₂ x), _).
  use make_Equalizer.
  - exact (λ (x : X), ∑ (y : Y₁ x), hProp_to_hSet (ff x y = gg x y)%logic)%set.
  - exact (λ (x : X) (e : ∑ (y : Y₁ x), ff x y = gg x y), pr1 e).
  - abstract
      (use funextsec ; intro x ;
       use funextsec ; intro e ;
       rewrite !fam_disp_cat_fiber_comp ;
       exact (pr2 e)).
  - refine (λ (Y₀ : X → hSet) (hh : ∏ (x : X), Y₀ x → Y₁ x), _).
    intro p.
    use make_iscontr.
    + simple refine ((λ (x : X) (y : Y₀ x), hh x y ,, _) ,, _).
      * abstract
          (cbn ;
           pose (q := eqtohomot (eqtohomot p x) y) ;
           cbn -[fiber_category] in q ;
           rewrite !fam_disp_cat_fiber_comp in q ;
           exact q).
      * abstract
          (use funextsec ; intro x ;
           use funextsec ; intro y ;
           rewrite fam_disp_cat_fiber_comp ;
           cbn ;
           apply idpath).
    + abstract
        (intros kk ;
         use subtypePath ;
         [ intro ; apply homset_property | ] ;
         use funextsec ; intro x ;
         use funextsec ; intro y ;
         use subtypePath ;
         [ intro ; apply setproperty | ] ;
         cbn ;
         pose (q := eqtohomot (eqtohomot (pr2 kk) x) y) ;
         rewrite fam_disp_cat_fiber_comp in q ;
         exact q).
Defined.

Proposition preserves_equalizer_fiber_functor_fam_disp_cat
            {X₁ X₂ : hSet}
            (f : X₁ → X₂)
  : preserves_equalizer
      (fiber_functor_from_cleaving fam_disp_cat cleaving_fam_disp_cat f).
Proof.
  use preserves_equalizer_if_preserves_chosen.
  {
    apply fam_disp_cat_fiber_equalizers.
  }
  intros Y₁ Y₂ ff gg p.
  use (isEqualizer_z_iso (isEqualizer_Equalizer (fam_disp_cat_fiber_equalizers _ _ _ _ _))).
  - use make_z_iso.
    + refine (λ x y, pr1 y ,, _).
      abstract
        (cbn -[fiber_functor_from_cleaving] ;
         rewrite !(fam_disp_cat_fiber_functor_from_cleaving f) ;
         exact (pr2 y)).
    + refine (λ x y, pr1 y ,, _).
      abstract
        (cbn -[fiber_functor_from_cleaving] ;
         pose (q := pr2 y) ;
         cbn -[fiber_functor_from_cleaving] in q ;
         rewrite !(fam_disp_cat_fiber_functor_from_cleaving f) in q ;
         exact q).
    + abstract
        (split ;
         use funextsec ; intro x ;
         use funextsec ; intro y ;
         rewrite fam_disp_cat_fiber_comp ;
         cbn ;
         (use subtypePath ; [ intro ; apply setproperty | ]) ;
         apply idpath).
  - use funextsec ; intro x.
    use funextsec ; intro y.
    cbn -[fiber_functor_from_cleaving fiber_category].
    rewrite (fam_disp_cat_fiber_functor_from_cleaving f).
    rewrite fam_disp_cat_fiber_comp.
    cbn.
    apply idpath.
Qed.

Definition fam_disp_cat_fiberwise_equalizers
  : fiberwise_equalizers cleaving_fam_disp_cat.
Proof.
  split.
  - exact fam_disp_cat_fiber_equalizers.
  - intros X₁ X₂ f.
    exact (preserves_equalizer_fiber_functor_fam_disp_cat f).
Defined.

(** * 10. The family of elements equal to some given element *)
Definition fam_disp_cat_eq_fam
           {X : hSet}
           (x : X)
  : X → hSet
  := (λ (x' : X), hProp_to_hSet (x = x'))%logic.

Definition fam_disp_cat_eq_fam_mor
           {X : hSet}
           {Y : X → hSet}
           {x : X}
           (y : Y x)
  : fam_disp_cat[{X}] ⟦ fam_disp_cat_eq_fam x , Y ⟧
  := λ (x' : X) p, transportf Y p y.

(** * 11. The fiberwise subobject classifier *)
Definition prop_set_fam
           (X : hSet)
  : fam_disp_cat[{X}]
  := λ _, hPropset.

Definition set_fam_truth_mor
           (X : hSet)
  : fam_disp_cat[{X}] ⟦ fam_disp_cat_fiber_terminal X, prop_set_fam X ⟧
  := λ _ _, htrue.

Section FiberSubobjectClassifier.
  Context {X : hSet}
          {Y₁ Y₂ : X → hSet}
          (mM : Monic (fam_disp_cat[{X}]) Y₁ Y₂).

  Let m : ∏ (x : X), Y₁ x → Y₂ x := pr1 mM.

  Proposition fam_disp_cat_fiber_monic_pt
              {x : X}
              {y₁ y₂ : Y₁ x}
              (p : m x y₁ = m x y₂)
    : y₁ = y₂.
  Proof.
    assert (fam_disp_cat_eq_fam_mor y₁ · pr1 mM = fam_disp_cat_eq_fam_mor y₂ · pr1 mM)
      as q.
    {
      use funextsec ; intro x'.
      use funextsec ; intro q.
      cbn in q.
      induction q.
      rewrite !fam_disp_cat_fiber_comp.
      cbn.
      exact p.
    }
    pose (eqtohomot (eqtohomot (pr2 mM _ _ _ q) x) (idpath _)) as r.
    cbn in r.
    exact r.
  Qed.

  Definition fam_disp_cat_characteristic_mor
    : fam_disp_cat[{X}] ⟦ Y₂ , prop_set_fam X ⟧.
  Proof.
    intros x y.
    use make_hProp.
    - exact (∑ (y' : Y₁ x), m x y' = y).
    - abstract
        (use invproofirrelevance ;
         intros z₁ z₂ ;
         use subtypePath ; [ intro ; apply setproperty | ] ;
         use fam_disp_cat_fiber_monic_pt ;
         exact (pr2 z₁ @ !(pr2 z₂))).
  Defined.

  Proposition fam_disp_cat_characteristic_mor_eq
    : mM · fam_disp_cat_characteristic_mor
      =
      TerminalArrow (fam_disp_cat_fiber_terminal X) Y₁ · set_fam_truth_mor X.
  Proof.
    use funextsec ; intro x.
    use funextsec ; intro y.
    rewrite !fam_disp_cat_fiber_comp.
    use hPropUnivalence.
    - exact (λ _, tt).
    - intros _ ; cbn.
      refine (y ,, _).
      apply idpath.
  Qed.

  Definition fam_disp_cat_characteristic_ex_unique
             {x : X}
             (y : Y₂ x)
             (q : fam_disp_cat_characteristic_mor x y = htrue)
    : ∃! (y' : Y₁ x), m x y' = y.
  Proof.
    use iscontraprop1.
    - use invproofirrelevance.
      intros ξ₁ ξ₂.
      use subtypePath ; [ intro ; apply setproperty | ].
      use fam_disp_cat_fiber_monic_pt.
      exact (pr2 ξ₁ @ !(pr2 ξ₂)).
    - exact (pr2 (weqlogeq _ _ q) tt).
  Defined.

  Proposition fam_disp_cat_characteristic_ex_unique_eq
              {x : X}
              (y : Y₂ x)
              (q : fam_disp_cat_characteristic_mor x y = htrue)
              (y' : Y₁ x)
              (r : m x y' = y)
    : y' = pr11 (fam_disp_cat_characteristic_ex_unique y q).
  Proof.
    refine (maponpaths pr1 (pr2 (fam_disp_cat_characteristic_ex_unique y q) (_ ,, _))).
    exact r.
  Qed.

  Proposition fam_disp_cat_characteristic_pb
    : isPullback fam_disp_cat_characteristic_mor_eq.
  Proof.
    refine (λ (Y₀ : X → hSet)
              (ff : ∏ (x : X), Y₀ x → Y₂ x)
              (gg : ∏ (x : X), Y₀ x → unit), _).
    intro p.
    use make_iscontr.
    - simple refine (_ ,, _ ,, _).
      + refine (λ (x : X) (y : Y₀ x),
                pr11 (fam_disp_cat_characteristic_ex_unique (ff x y) _)).
        abstract
          (pose (eqtohomot (eqtohomot p x) y) as q ;
           rewrite !fam_disp_cat_fiber_comp in q ;
           refine (q @ _) ;
           assert (gg x y = tt) as -> by apply isapropunit ;
           apply idpath).
      + abstract
          (use funextsec ; intro x ;
           use funextsec ; intro y ;
           rewrite fam_disp_cat_fiber_comp ;
           exact (pr21 (fam_disp_cat_characteristic_ex_unique _ _))).
      + abstract
          (use funextsec ;
           intro x ;
           use funextsec ;
           intro y ;
           apply isapropunit).
    - abstract
        (intros ξ ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         use funextsec ;
         intro x ;
         use funextsec ;
         intro y ;
         cbn ;
         use fam_disp_cat_characteristic_ex_unique_eq ;
         refine (_ @ eqtohomot (eqtohomot (pr12 ξ) x) y) ;
         rewrite fam_disp_cat_fiber_comp ;
         apply idpath).
  Defined.

  Proposition fam_disp_cat_characteristic_unique
              (χ : fam_disp_cat[{X}] ⟦ Y₂ , prop_set_fam X ⟧)
              (p : mM · χ
                   =
                   TerminalArrow (fam_disp_cat_fiber_terminal X) Y₁ · set_fam_truth_mor X)
              (H : isPullback p)
    : χ = fam_disp_cat_characteristic_mor.
  Proof.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use hPropUnivalence ; cbn.
    - pose (PB := make_Pullback _ H).
      intros z.
      assert (fam_disp_cat_eq_fam_mor y · χ
              =
              fam_disp_cat_eq_fam_mor (Y := λ _, unitset) tt · set_fam_truth_mor X)
        as r.
      {
        use funextsec ; intro x'.
        use funextsec ; intro q.
        cbn in q.
        induction q.
        rewrite !fam_disp_cat_fiber_comp.
        cbn.
        use hPropUnivalence.
        {
          exact (λ _, tt).
        }
        exact (λ _, z).
      }
      pose (PullbackArrow
              PB
              (fam_disp_cat_eq_fam x)
              (fam_disp_cat_eq_fam_mor y)
              (fam_disp_cat_eq_fam_mor (Y := λ _, unitset) tt)
              r)
        as h.
      cbn in h.
      simple refine (_ ,, _).
      + exact (h x (idpath _)).
      + cbn.
        pose (PullbackArrow_PullbackPr1
                PB
                (fam_disp_cat_eq_fam x)
                (fam_disp_cat_eq_fam_mor y)
                (fam_disp_cat_eq_fam_mor (Y := λ _, unitset) tt)
                r)
          as r'.
        refine (_ @ eqtohomot (eqtohomot r' x) (idpath _)).
        rewrite fam_disp_cat_fiber_comp.
        cbn.
        apply idpath.
    - intros [ y' q ].
      rewrite <- q.
      pose (eqtohomot (eqtohomot p x) y') as r.
      rewrite !fam_disp_cat_fiber_comp in r.
      cbn in r.
      exact (pr2 (weqlogeq _ _ r) tt).
  Qed.
End FiberSubobjectClassifier.

Definition fam_disp_cat_fiber_subobject_classifier
           (X : hSet)
  : subobject_classifier (fam_disp_cat_fiber_terminal X).
Proof.
  use make_subobject_classifier.
  - exact (prop_set_fam X).
  - exact (set_fam_truth_mor X).
  - refine (λ (Y₁ Y₂ : X → hSet) (m : Monic (fam_disp_cat[{X}]) Y₁ Y₂), _).
    use make_iscontr.
    + simple refine (_ ,, _ ,, _).
      * exact (fam_disp_cat_characteristic_mor m).
      * exact (fam_disp_cat_characteristic_mor_eq m).
      * exact (fam_disp_cat_characteristic_pb m).
    + abstract
        (intro χ ;
         use subtypePath ;
         [ intro ;
           apply isaproptotal2 ; [ intro ; apply isaprop_isPullback | ] ;
           intros ;
           apply homset_property
         | ] ;
         exact (fam_disp_cat_characteristic_unique m (pr1 χ) (pr12 χ) (pr22 χ))).
Defined.

Proposition preserves_subobject_classifier_fiber_functor_fam_disp_cat
            {X₁ X₂ : hSet}
            (f : X₁ → X₂)
  : preserves_subobject_classifier
      (fiber_functor_from_cleaving fam_disp_cat cleaving_fam_disp_cat f)
      (fam_disp_cat_fiber_terminal X₂)
      (fam_disp_cat_fiber_terminal X₁)
      (preserves_terminal_fiber_functor_fam_disp_cat f).
Proof.
  use preserves_chosen_to_preserves_subobject_classifier'.
  - use is_univalent_fiber.
    apply is_univalent_disp_fam_disp_cat.
  - use is_univalent_fiber.
    apply is_univalent_disp_fam_disp_cat.
  - apply fam_disp_cat_fiber_subobject_classifier.
  - use (z_iso_to_is_subobject_classifier
           (C := univalent_fiber_category univalent_fam_disp_cat _)).
    + apply fam_disp_cat_fiber_subobject_classifier.
    + use make_z_iso.
      * exact (λ _ P, P).
      * exact (λ _ P, P).
      * abstract
          (split ;
           use funextsec ; intro x ;
           use funextsec ; intro y ;
           apply fam_disp_cat_fiber_comp).
    + use funextsec ; intro x.
      use funextsec ; intro y.
      cbn -[fiber_functor_from_cleaving fiber_category].
      rewrite !fam_disp_cat_fiber_comp.
      rewrite !(fam_disp_cat_fiber_functor_from_cleaving f).
      apply idpath.
Qed.

Definition fam_disp_cat_fiberwise_subobject_classifier
  : fiberwise_subobject_classifier fam_disp_cat_fiberwise_terminal.
Proof.
  split.
  - exact fam_disp_cat_fiber_subobject_classifier.
  - intros X₁ X₂ f.
    exact (preserves_subobject_classifier_fiber_functor_fam_disp_cat f).
Defined.

(** * 12. The fiberwise parameterized natural numbers object *)
Section NNO.
  Context (X : hSet).

  Definition fam_disp_cat_nno_fam
             (x : X)
    : hSet
    := natset.

  Definition fam_disp_cat_nno_Z
    : fam_disp_cat[{X}] ⟦ fam_disp_cat_fiber_terminal X , fam_disp_cat_nno_fam ⟧
    := λ _ _, 0.

  Definition fam_disp_cat_nno_S
    : fam_disp_cat[{X}] ⟦ fam_disp_cat_nno_fam , fam_disp_cat_nno_fam ⟧
    := λ _ n, S n.

  Definition fam_disp_cat_nno_rec
             {Y₁ Y₂ : X → hSet}
             (zy : ∏ (x : X), Y₁ x → Y₂ x)
             (sy : ∏ (x : X), Y₂ x → Y₂ x)
             (x : X)
             (yn : Y₁ x × ℕ)
    : Y₂ x.
  Proof.
    induction yn as [ y n ].
    induction n as [ | n IHn ].
    - exact (zy x y).
    - exact (sy x IHn).
  Defined.

  Definition fam_disp_cat_fiber_parameterized_NNO
    : parameterized_NNO
        (fam_disp_cat_fiber_terminal X)
        (fam_disp_cat_fiber_binproducts X).
  Proof.
    use make_parameterized_NNO.
    - exact fam_disp_cat_nno_fam.
    - exact fam_disp_cat_nno_Z.
    - exact fam_disp_cat_nno_S.
    - intros Y₁ Y₂ zy sy.
      use make_iscontr.
      + simple refine (_ ,, _ ,, _).
        * exact (fam_disp_cat_nno_rec zy sy).
        * abstract
            (use funextsec ; intro x ;
             use funextsec ; intro z ;
             rewrite fam_disp_cat_fiber_comp ;
             cbn -[fiber_category] ;
             rewrite fam_disp_cat_fiber_comp ;
             cbn ;
             apply idpath).
        * abstract
            (use funextsec ; intro x ;
             use funextsec ; intro z ;
             rewrite !fam_disp_cat_fiber_comp ;
             cbn -[fiber_category] ;
             rewrite !fam_disp_cat_fiber_comp ;
             cbn ;
             apply idpath).
      + abstract
          (intros [ φ [ φz φs ]] ;
           use subtypePath ;
           [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           use funextsec ;
           intro x ;
           use funextsec ; cbn ;
           intro yn ;
           induction yn as [ y n ] ;
           pose (p := eqtohomot (eqtohomot φz x) y) ;
           rewrite fam_disp_cat_fiber_comp in p ;
           cbn -[fiber_category] in p ;
           rewrite fam_disp_cat_fiber_comp in p ;
           cbn in p ;
           induction n as [ | n IHn ] ; cbn ; [ exact p | ] ;
           pose (q := eqtohomot (eqtohomot φs x) (y ,, n)) ;
           rewrite !fam_disp_cat_fiber_comp in q ;
           cbn -[fiber_category] in q ;
           rewrite !fam_disp_cat_fiber_comp in q ;
           cbn in q ;
           refine (q @ _) ;
           apply maponpaths ;
           exact IHn).
  Defined.
End NNO.

Definition set_fiberwise_nno_stable
           {X₁ X₂ : hSet}
           (f : X₁ → X₂)
  : preserves_parameterized_NNO
      (fam_disp_cat_fiber_parameterized_NNO X₂)
      (fam_disp_cat_fiber_parameterized_NNO X₁)
      (fiber_functor_from_cleaving
         fam_disp_cat
         cleaving_fam_disp_cat
         f)
      (preserves_terminal_fiber_functor_fam_disp_cat f).
Proof.
  use make_is_z_isomorphism.
  - exact (λ _ n, n).
  - abstract
      (split ;
       use funextsec ; intro x ;
       use funextsec ; intro n ;
       rewrite fam_disp_cat_fiber_comp ;
       unfold preserves_parameterized_NNO_mor, is_NNO_parameterized_NNO_mor ;
       cbn -[fiber_category fiber_functor_from_cleaving] ;
       unfold fam_disp_cat_nno_rec ;
       rewrite !fam_disp_cat_fiber_comp ;
       rewrite (fam_disp_cat_fiber_functor_from_cleaving f) ;
       cbn -[fiber_functor_from_cleaving] ;
       (induction n as [ | n IHn ] ; [ apply idpath | ]) ;
       cbn -[fiber_category fiber_functor_from_cleaving] ;
       rewrite (fam_disp_cat_fiber_functor_from_cleaving f) ; refine (maponpaths S _) ;
       exact IHn).
Defined.
