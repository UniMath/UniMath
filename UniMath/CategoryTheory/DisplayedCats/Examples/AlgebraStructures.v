(*****************************************************************

 Algebra structures

 In this file, we construct the Eilenberg-Moore category of monads
 over set as a category of structured sets. Note that we can
 instantiate this with, for example, the free abelian group monad,
 and that way we get the category of abelian groups.

 Contents
 1. Algebra structures
 2. The cartesian structure of algebras
 3. Equalizers of algebras
 4. Type indexed products of algebras

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

Section MonadToStruct.
  Context (M : Monad SET).

  (**
   1. Algebra structures
   *)
  Definition Monad_algebra_laws
             {X : SET}
             (f : M X --> X)
    : UU
    := (η M X · f = identity X)
       ×
       (μ M X · f = #M f · f).

  Definition Monad_algebra
             (X : SET)
    : UU
    := ∑ (f : M X --> X), Monad_algebra_laws f.

  Definition make_Monad_algebra
             {X : SET}
             (f : M X --> X)
             (p : Monad_algebra_laws f)
    : Monad_algebra X
    := f ,, p.

  Coercion Monad_algebra_struct_to_mor
           {X : hSet}
           (f : Monad_algebra X)
    : M X --> X
    := pr1 f.

  Proposition Monad_algebra_unit
              {X : hSet}
              (f : Monad_algebra X)
    : η M X · f = identity _.
  Proof.
    exact (pr12 f).
  Qed.

  Proposition Monad_algebra_mu
              {X : hSet}
              (f : Monad_algebra X)
    : μ M X · f = #M f · f.
  Proof.
    exact (pr22 f).
  Qed.

  Definition Monad_to_hset_struct_data
    : hset_struct_data.
  Proof.
    simple refine (_ ,, _).
    - exact Monad_algebra.
    - exact (λ X Y f g h, f · h = #M h · g).
  Defined.

  Proposition Monad_to_hset_struct_laws
    : hset_struct_laws Monad_to_hset_struct_data.
  Proof.
    repeat split.
    - intro X.
      use isaset_total2.
      + apply homset_property.
      + intro f.
        apply isasetaprop.
        apply isapropdirprod ; apply homset_property.
    - intros X Y f g h.
      apply homset_property.
    - intros X f ; cbn.
      rewrite (functor_id M).
      apply idpath.
    - intros X Y Z fX fY fZ h₁ h₂ Mh₁ Mh₂ ; cbn in *.
      use funextsec.
      intro x.
      rewrite (eqtohomot Mh₁).
      rewrite (eqtohomot Mh₂).
      rewrite (eqtohomot (functor_comp M h₁ h₂)).
      apply idpath.
    - intros X fX fX' p q.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      cbn in *.
      use funextsec.
      intro x.
      refine (eqtohomot p x @ _).
      apply maponpaths.
      exact (eqtohomot (functor_id M X) x).
  Qed.

  Definition Monad_to_hset_struct
    : hset_struct
    := Monad_to_hset_struct_data ,, Monad_to_hset_struct_laws.

  (**
   2. The cartesian structure of algebras
   *)
  Proposition unit_Monad_algebra_laws
    : @Monad_algebra_laws unitHSET (λ _, tt).
  Proof.
    split.
    - cbn.
      use funextsec.
      intro x.
      apply isapropunit.
    - apply idpath.
  Qed.

  Definition unit_Monad_algebra
    : Monad_algebra unitHSET.
  Proof.
    use make_Monad_algebra.
    - exact (λ _, tt).
    - exact unit_Monad_algebra_laws.
  Defined.

  Section ProdAlgebra.
    Context {X Y : SET}
            (f : Monad_algebra X)
            (g : Monad_algebra Y).

    Let XY : SET := (X × Y)%set.
    Let p₁ : XY --> X := dirprod_pr1.
    Let p₂ : XY --> Y := dirprod_pr2.

    Definition prod_Monad_algebra_map
      : M XY --> XY
      := BinProductArrow _ (BinProductsHSET X Y) (#M p₁ · f) (#M p₂ · g).

    Proposition prod_Monad_algebra_laws
      : Monad_algebra_laws prod_Monad_algebra_map.
    Proof.
      split.
      - use (BinProductArrowsEq _ _ _ (BinProductsHSET X Y)).
        + rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply (BinProductPr1Commutes _ _ _ (BinProductsHSET X Y)).
          }
          rewrite !assoc.
          rewrite id_left.
          rewrite <- (nat_trans_ax (η M) _ _ p₁).
          rewrite !assoc'.
          rewrite (Monad_algebra_unit f).
          apply idpath.
        + rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply (BinProductPr2Commutes _ _ _ (BinProductsHSET X Y)).
          }
          rewrite !assoc.
          rewrite id_left.
          rewrite <- (nat_trans_ax (η M) _ _ p₂).
          rewrite !assoc'.
          rewrite (Monad_algebra_unit g).
          apply idpath.
      - use (BinProductArrowsEq _ _ _ (BinProductsHSET X Y)).
        + rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply (BinProductPr1Commutes _ _ _ (BinProductsHSET X Y)).
          }
          refine (!_).
          etrans.
          {
            apply maponpaths.
            apply (BinProductPr1Commutes _ _ _ (BinProductsHSET X Y)).
          }
          rewrite !assoc.
          rewrite <- functor_comp.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply (BinProductPr1Commutes _ _ _ (BinProductsHSET X Y)).
          }
          rewrite <- (nat_trans_ax (μ M) _ _ p₁).
          rewrite functor_comp.
          rewrite !assoc'.
          rewrite (Monad_algebra_mu f).
          apply idpath.
        + rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply (BinProductPr2Commutes _ _ _ (BinProductsHSET X Y)).
          }
          refine (!_).
          etrans.
          {
            apply maponpaths.
            apply (BinProductPr2Commutes _ _ _ (BinProductsHSET X Y)).
          }
          rewrite !assoc.
          rewrite <- functor_comp.
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            apply (BinProductPr2Commutes _ _ _ (BinProductsHSET X Y)).
          }
          rewrite <- (nat_trans_ax (μ M) _ _ p₂).
          rewrite functor_comp.
          rewrite !assoc'.
          rewrite (Monad_algebra_mu g).
          apply idpath.
    Qed.

    Definition prod_Monad_algebra
      : Monad_algebra XY.
    Proof.
      use make_Monad_algebra.
      - exact prod_Monad_algebra_map.
      - exact prod_Monad_algebra_laws.
    Defined.
  End ProdAlgebra.

  Definition Monad_to_hset_cartesian_struct_data
    : hset_cartesian_struct_data
    := Monad_to_hset_struct ,, unit_Monad_algebra ,, λ X Y f g, prod_Monad_algebra f g.

  Proposition Monad_to_hset_cartesian_struct_laws
    : hset_cartesian_struct_laws Monad_to_hset_cartesian_struct_data.
  Proof.
    split4.
    - intros X f ; cbn.
      apply idpath.
    - intros X Y f g ; cbn.
      apply idpath.
    - intros X Y f g ; cbn.
      apply idpath.
    - intros W X Y fW fX fY g₁ g₂ Mg₁ Mg₂ ; cbn in *.
      use funextsec.
      intro x.
      use pathsdirprod ; cbn.
      + refine (eqtohomot Mg₁ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          refine (!_).
          apply (eqtohomot (functor_comp M _ _)).
        }
        apply idpath.
      + refine (eqtohomot Mg₂ _ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          refine (!_).
          apply (eqtohomot (functor_comp M _ _)).
        }
        apply idpath.
  Qed.

  Definition Monad_to_hset_cartesian_struct
    : hset_cartesian_struct
    := Monad_to_hset_cartesian_struct_data
       ,,
       Monad_to_hset_cartesian_struct_laws.

  (**
   3. Equalizers of algebras
   *)
  Section EqualizerAlgebra.
    Context {X Y : SET}
            {f g : X --> Y}
            (hX : Monad_algebra X)
            (hY : Monad_algebra Y)
            (Mf : hX · f = #M f · hY)
            (Mg : hX · g = #M g · hY).

    Let E : SET := (∑ x, hProp_to_hSet (eqset (f x) (g x)))%set.
    Let π : E --> X := λ z, pr1 z.

    Definition eqalizer_algebra_map
      : M E --> E.
    Proof.
      use (EqualizerIn (Equalizers_in_HSET X Y f g)).
      - exact (#M π · hX).
      - abstract
          (rewrite !assoc' ;
           rewrite Mf, Mg ;
           rewrite !assoc ;
           apply maponpaths_2 ;
           rewrite <- !functor_comp ;
           apply maponpaths ;
           apply (EqualizerEqAr (Equalizers_in_HSET X Y f g))).
    Defined.

    Proposition eqalizer_algebra_laws
      : Monad_algebra_laws eqalizer_algebra_map.
    Proof.
      split.
      - use (EqualizerInsEq (Equalizers_in_HSET X Y f g)).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (EqualizerCommutes (Equalizers_in_HSET X Y f g)).
        }
        rewrite !id_left.
        rewrite !assoc.
        rewrite <- (nat_trans_ax (η M) _ _ π).
        rewrite !assoc'.
        rewrite Monad_algebra_unit.
        rewrite id_right.
        apply idpath.
      - use (EqualizerInsEq (Equalizers_in_HSET X Y f g)).
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (EqualizerCommutes (Equalizers_in_HSET X Y f g)).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply (EqualizerCommutes (Equalizers_in_HSET X Y f g)).
        }
        rewrite !assoc.
        rewrite <- functor_comp.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          apply (EqualizerCommutes (Equalizers_in_HSET X Y f g)).
        }
        rewrite <- (nat_trans_ax (μ M) _ _ π).
        rewrite functor_comp.
        rewrite !assoc'.
        rewrite (Monad_algebra_mu hX).
        apply idpath.
    Qed.

    Definition equalizer_algebra
      : Monad_algebra E.
    Proof.
      use make_Monad_algebra.
      - exact eqalizer_algebra_map.
      - exact eqalizer_algebra_laws.
    Defined.
  End EqualizerAlgebra.

  Definition Monad_to_hset_equalizer_struct_data
    : hset_equalizer_struct_data Monad_to_hset_struct
    := λ X Y f g hX hY Mf Mg, equalizer_algebra hX hY Mf Mg.

  Proposition Monad_to_hset_equalizer_struct_laws
    : hset_equalizer_struct_laws Monad_to_hset_equalizer_struct_data.
  Proof.
    split.
    - intros X Y f g hX hY Mf Mg.
      apply idpath.
    - intros X Y f g hX hY Mf Mg W hW k Mk q.
      use funextsec.
      intro x.
      use subtypePath.
      {
        intro.
        apply setproperty.
      }
      cbn in *.
      refine (eqtohomot Mk x @ _).
      apply maponpaths.
      refine (!_).
      exact (!(eqtohomot (functor_comp M _ _) _)).
  Qed.

  Definition Monad_to_hset_equalizer_struct
    : hset_equalizer_struct Monad_to_hset_struct
    := Monad_to_hset_equalizer_struct_data
       ,,
       Monad_to_hset_equalizer_struct_laws.

  (**
   4. Type indexed products of algebras
   *)
  Section TypeProdAlgebra.
    Context {J : UU}
            {D : J → hSet}
            (p : ∏ (i : J), Monad_algebra (D i)).

    Let prod : Product J SET D := ProductsHSET J D.

    Definition Monad_type_prod_map
      : M prod --> prod
      := ProductArrow _ _ prod (λ i, #M (ProductPr _ _ _ i) · p i).

    Proposition Monad_type_prod_laws
      : Monad_algebra_laws Monad_type_prod_map.
    Proof.
      split.
      - use (ProductArrow_eq _ _ _ prod).
        intro i.
        rewrite id_left.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply ProductPrCommutes.
        }
        rewrite !assoc.
        rewrite <- (nat_trans_ax (η M)).
        rewrite !assoc'.
        rewrite (Monad_algebra_unit (p i)).
        rewrite id_right.
        apply idpath.
      - use (ProductArrow_eq _ _ _ prod).
        intro i.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply ProductPrCommutes.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply ProductPrCommutes.
        }
        rewrite !assoc.
        rewrite <- functor_comp.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          apply ProductPrCommutes.
        }
        rewrite <- (nat_trans_ax (μ M)).
        rewrite functor_comp.
        rewrite !assoc'.
        rewrite (Monad_algebra_mu (p i)).
        apply idpath.
    Qed.
  End TypeProdAlgebra.

  Definition Monad_to_hset_struct_type_prod_data
             (J : UU)
    : hset_struct_type_prod_data Monad_to_hset_struct J.
  Proof.
    intros D p.
    use make_Monad_algebra.
    - exact (Monad_type_prod_map p).
    - exact (Monad_type_prod_laws p).
  Defined.

  Proposition Monad_to_hset_struct_type_prod_laws
              (J : UU)
    : hset_struct_type_prod_laws (Monad_to_hset_struct_type_prod_data J).
  Proof.
    split.
    - intros D PD i.
      apply idpath.
    - intros D PD W hW ps Mps.
      cbn in *.
      use funextsec ; intro x.
      use funextsec ; intro i.
      refine (eqtohomot (Mps i) x @ _).
      apply maponpaths.
      refine (!_).
      exact (!(eqtohomot (functor_comp M _ _) _)).
  Qed.

  Definition Monad_to_hset_struct_type_prod
             (J : UU)
    : hset_struct_type_prod Monad_to_hset_struct J
    := Monad_to_hset_struct_type_prod_data J
       ,,
       Monad_to_hset_struct_type_prod_laws J.
End MonadToStruct.
