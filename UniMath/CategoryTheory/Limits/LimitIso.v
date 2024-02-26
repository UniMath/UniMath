(*************************************************************************************

 Limits and isomorphisms

 If we have two cones `C₁` and `C₂` that are isomorphic, then a limit for `C₁` is also
 a limit for `C₂`. We consider this statement for binary products, equalizers, and
 binary coproducts.

 Contents
 1. Binary products on isomorphisc cones
 2. Equalizers on isomorphic cones
 3. Binary coproducts on isomorphic cocones

 *************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.

Local Open Scope cat.

(** * 1. Binary products on isomorphisc cones *)
Section BinProductIsoComp.
  Context {C : category}
          {x₁ x₂ y₁ y₂ : C}
          (p : BinProduct C x₁ y₁)
          (l : z_iso x₂ x₁)
          (r : z_iso y₂ y₁).

  Let π₁ : p --> x₂ := BinProductPr1 _ p · inv_from_z_iso l.
  Let π₂ : p --> y₂ := BinProductPr2 _ p · inv_from_z_iso r.

  Proposition BinProduct_z_iso_lr_unique
              {w : C}
              (f : w --> x₂)
              (g : w --> y₂)
    : isaprop (∑ fg, fg · π₁ = f × fg · π₂ = g).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply homset_property.
    }
    use BinProductArrowsEq.
    - refine (_ @ maponpaths (λ z, z · l) (pr12 φ₁ @ !(pr12 φ₂)) @ _).
      + unfold π₁.
        rewrite !assoc'.
        rewrite z_iso_after_z_iso_inv.
        rewrite id_right.
        apply idpath.
      + unfold π₁.
        rewrite !assoc'.
        rewrite z_iso_after_z_iso_inv.
        rewrite id_right.
        apply idpath.
    - refine (_ @ maponpaths (λ z, z · r) (pr22 φ₁ @ !(pr22 φ₂)) @ _).
      + unfold π₂.
        rewrite !assoc'.
        rewrite z_iso_after_z_iso_inv.
        rewrite id_right.
        apply idpath.
      + unfold π₂.
        rewrite !assoc'.
        rewrite z_iso_after_z_iso_inv.
        rewrite id_right.
        apply idpath.
  Qed.

  Definition BinProduct_z_iso_lr
    : BinProduct C x₂ y₂.
  Proof.
    use make_BinProduct.
    - exact p.
    - exact π₁.
    - exact π₂.
    - intros w f g.
      use iscontraprop1.
      + apply BinProduct_z_iso_lr_unique.
      + refine (BinProductArrow _ p (f · l) (g · r) ,, _ ,, _).
        * abstract
            (unfold π₁ ;
             rewrite !assoc ;
             rewrite BinProductPr1Commutes ;
             rewrite !assoc' ;
             rewrite z_iso_inv_after_z_iso ;
             apply id_right).
        * abstract
            (unfold π₂ ;
             rewrite !assoc ;
             rewrite BinProductPr2Commutes ;
             rewrite !assoc' ;
             rewrite z_iso_inv_after_z_iso ;
             apply id_right).
  Defined.
End BinProductIsoComp.

(** * 2. Equalizers on isomorphic cones *)
Section EqualizerIsoComp.
  Context {C : category}
          {x₁ x₂ y₁ y₂ : C}
          {f₁ g₁ : x₁ --> y₁}
          {f₂ g₂ : x₂ --> y₂}
          (E : Equalizer f₁ g₁)
          (l : z_iso x₂ x₁)
          (r : z_iso y₂ y₁)
          (p : l · f₁ = f₂ · r)
          (q : l · g₁ = g₂ · r).

  Let ι : E --> x₂ := EqualizerArrow E · inv_from_z_iso l.

  Lemma Equalizer_z_iso_lr_eq
    : ι · f₂ = ι · g₂.
  Proof.
    unfold ι.
    pose proof (maponpaths (λ z, inv_from_z_iso l · z · inv_from_z_iso r) p) as p'.
    pose proof (maponpaths (λ z, inv_from_z_iso l · z · inv_from_z_iso r) q) as q'.
    cbn in p', q'.
    rewrite !assoc in p', q'.
    rewrite z_iso_after_z_iso_inv in p', q'.
    rewrite id_left in p', q'.
    rewrite !assoc' in p', q'.
    rewrite z_iso_inv_after_z_iso in p', q'.
    rewrite id_right in p', q'.
    rewrite !assoc'.
    rewrite <- p', <- q'.
    rewrite !assoc.
    apply maponpaths_2.
    apply EqualizerEqAr.
  Qed.

  Proposition Equalizer_z_iso_lr_unique
              {w : C}
              (h : w --> x₂)
    : isaprop (∑ φ, φ · ι = h).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    use EqualizerInsEq.
    refine (_ @ maponpaths (λ z, z · l) (pr2 φ₁ @ !(pr2 φ₂)) @ _).
    - unfold ι.
      rewrite !assoc'.
      rewrite z_iso_after_z_iso_inv.
      rewrite id_right.
      apply idpath.
    - unfold ι.
      rewrite !assoc'.
      rewrite z_iso_after_z_iso_inv.
      rewrite id_right.
      apply idpath.
  Qed.

  Definition Equalizer_z_iso_lr
    : Equalizer f₂ g₂.
  Proof.
    use make_Equalizer.
    - exact E.
    - exact ι.
    - exact Equalizer_z_iso_lr_eq.
    - intros w h s.
      use iscontraprop1.
      + exact (Equalizer_z_iso_lr_unique h).
      + simple refine (EqualizerIn E w (h · l) _ ,, _).
        * abstract
            (rewrite !assoc' ;
             rewrite p, q ;
             rewrite !assoc ;
             rewrite s ;
             apply idpath).
        * abstract
            (cbn ;
             unfold ι ;
             rewrite !assoc ;
             rewrite EqualizerCommutes ;
             rewrite !assoc' ;
             rewrite z_iso_inv_after_z_iso ;
             apply id_right).
  Defined.
End EqualizerIsoComp.

(** * 3. Binary coproducts on isomorphic cocones *)
Section BinCoproductIsoComp.
  Context {C : category}
          {x₁ x₂ y₁ y₂ : C}
          (p : BinCoproduct x₁ y₁)
          (l : z_iso x₁ x₂)
          (r : z_iso y₁ y₂).

  Let ι₁ : x₂ --> p := inv_from_z_iso l · BinCoproductIn1 p.
  Let ι₂ : y₂ --> p := inv_from_z_iso r · BinCoproductIn2 p.

  Proposition BinCoproduct_z_iso_lr_unique
              {w : C}
              (f : x₂ --> w)
              (g : y₂ --> w)
    : isaprop (∑ fg, ι₁ · fg = f × ι₂ · fg = g).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply homset_property.
    }
    use BinCoproductArrowsEq.
    - refine (_ @ maponpaths (λ z, l · z) (pr12 φ₁ @ !(pr12 φ₂)) @ _).
      + unfold ι₁.
        rewrite !assoc.
        rewrite z_iso_inv_after_z_iso.
        rewrite id_left.
        apply idpath.
      + unfold ι₁.
        rewrite !assoc.
        rewrite z_iso_inv_after_z_iso.
        rewrite id_left.
        apply idpath.
    - refine (_ @ maponpaths (λ z, r · z) (pr22 φ₁ @ !(pr22 φ₂)) @ _).
      + unfold ι₂.
        rewrite !assoc.
        rewrite z_iso_inv_after_z_iso.
        rewrite id_left.
        apply idpath.
      + unfold ι₂.
        rewrite !assoc.
        rewrite z_iso_inv_after_z_iso.
        rewrite id_left.
        apply idpath.
  Qed.

  Definition BinCoproduct_z_iso_lr
    : BinCoproduct x₂ y₂.
  Proof.
    use make_BinCoproduct.
    - exact p.
    - exact ι₁.
    - exact ι₂.
    - intros w f g.
      use iscontraprop1.
      + apply BinCoproduct_z_iso_lr_unique.
      + refine (BinCoproductArrow p (l · f) (r · g) ,, _ ,, _).
        * abstract
            (unfold ι₁ ;
             rewrite !assoc' ;
             rewrite BinCoproductIn1Commutes ;
             rewrite !assoc ;
             rewrite z_iso_after_z_iso_inv ;
             apply id_left).
        * abstract
            (unfold ι₂ ;
             rewrite !assoc' ;
             rewrite BinCoproductIn2Commutes ;
             rewrite !assoc ;
             rewrite z_iso_after_z_iso_inv ;
             apply id_left).
  Defined.
End BinCoproductIsoComp.
