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
 5. The free algebra adjunction
 6. Every algebra is a coequalizer of a free algebra

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.Preservation.
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
  Definition monad_algebra_laws
             {X : SET}
             (f : M X --> X)
    : UU
    := (η M X · f = identity X)
       ×
       (μ M X · f = #M f · f).

  Definition monad_algebra
             (X : SET)
    : UU
    := ∑ (f : M X --> X), monad_algebra_laws f.

  Definition make_monad_algebra
             {X : SET}
             (f : M X --> X)
             (p : monad_algebra_laws f)
    : monad_algebra X
    := f ,, p.

  #[reversible=no] Coercion monad_algebra_struct_to_mor
           {X : hSet}
           (f : monad_algebra X)
    : M X --> X
    := pr1 f.

  Proposition monad_algebra_unit
              {X : hSet}
              (f : monad_algebra X)
    : η M X · f = identity _.
  Proof.
    exact (pr12 f).
  Qed.

  Proposition monad_algebra_mu
              {X : hSet}
              (f : monad_algebra X)
    : μ M X · f = #M f · f.
  Proof.
    exact (pr22 f).
  Qed.

  Definition monad_to_hset_struct_data
    : hset_struct_data.
  Proof.
    simple refine (_ ,, _).
    - exact monad_algebra.
    - exact (λ X Y f g h, f · h = #M h · g).
  Defined.

  Proposition monad_to_hset_struct_laws
    : hset_struct_laws monad_to_hset_struct_data.
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
    - intros X Y Z fX fY fZ h₁ h₂ Mh₁ Mh₂ ; cbn -[Monad] in *.
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
      cbn -[Monad] in *.
      use funextsec.
      intro x.
      refine (eqtohomot p x @ _).
      apply maponpaths.
      exact (eqtohomot (functor_id M X) x).
  Qed.

  Definition monad_to_hset_struct
    : hset_struct
    := monad_to_hset_struct_data ,, monad_to_hset_struct_laws.

  Definition category_of_monad_algebra
    : category
    := category_of_hset_struct monad_to_hset_struct.

  (**
   2. The cartesian structure of algebras
   *)
  Proposition unit_monad_algebra_laws
    : @monad_algebra_laws unitHSET (λ _, tt).
  Proof.
    split.
    - cbn.
      use funextsec.
      intro x.
      apply isapropunit.
    - apply idpath.
  Qed.

  Definition unit_monad_algebra
    : monad_algebra unitHSET.
  Proof.
    use make_monad_algebra.
    - exact (λ _, tt).
    - exact unit_monad_algebra_laws.
  Defined.

  Section ProdAlgebra.
    Context {X Y : SET}
            (f : monad_algebra X)
            (g : monad_algebra Y).

    Let XY : SET := (X × Y)%set.
    Let p₁ : XY --> X := dirprod_pr1.
    Let p₂ : XY --> Y := dirprod_pr2.

    Definition prod_monad_algebra_map
      : M XY --> XY
      := BinProductArrow _ (BinProductsHSET X Y) (#M p₁ · f) (#M p₂ · g).

    Proposition prod_monad_algebra_laws
      : monad_algebra_laws prod_monad_algebra_map.
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
          rewrite (monad_algebra_unit f).
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
          rewrite (monad_algebra_unit g).
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
          rewrite (monad_algebra_mu f).
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
          rewrite (monad_algebra_mu g).
          apply idpath.
    Qed.

    Definition prod_monad_algebra
      : monad_algebra XY.
    Proof.
      use make_monad_algebra.
      - exact prod_monad_algebra_map.
      - exact prod_monad_algebra_laws.
    Defined.
  End ProdAlgebra.

  Definition monad_to_hset_cartesian_struct_data
    : hset_cartesian_struct_data
    := monad_to_hset_struct
       ,, unit_monad_algebra
       ,, λ X Y f g, prod_monad_algebra f g.

  Proposition monad_to_hset_cartesian_struct_laws
    : hset_cartesian_struct_laws monad_to_hset_cartesian_struct_data.
  Proof.
    split4.
    - intros X f ; cbn.
      apply idpath.
    - intros X Y f g ; cbn.
      apply idpath.
    - intros X Y f g ; cbn.
      apply idpath.
    - intros W X Y fW fX fY g₁ g₂ Mg₁ Mg₂ ; cbn -[Monad] in *.
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

  Definition monad_to_hset_cartesian_struct
    : hset_cartesian_struct
    := monad_to_hset_cartesian_struct_data
       ,,
       monad_to_hset_cartesian_struct_laws.

  (**
   3. Equalizers of algebras
   *)
  Section EqualizerAlgebra.
    Context {X Y : SET}
            {f g : X --> Y}
            (hX : monad_algebra X)
            (hY : monad_algebra Y)
            (Mf : hX · f = #M f · hY)
            (Mg : hX · g = #M g · hY).

    Let E : SET := (∑ x, hProp_to_hSet (eqset (f x) (g x)))%set.
    Let π : E --> X := λ z, pr1 z.

    Definition equalizer_algebra_map
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

    Proposition equalizer_algebra_laws
      : monad_algebra_laws equalizer_algebra_map.
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
        rewrite monad_algebra_unit.
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
        rewrite (monad_algebra_mu hX).
        apply idpath.
    Qed.

    Definition equalizer_algebra
      : monad_algebra E.
    Proof.
      use make_monad_algebra.
      - exact equalizer_algebra_map.
      - exact equalizer_algebra_laws.
    Defined.
  End EqualizerAlgebra.

  Definition monad_to_hset_equalizer_struct_data
    : hset_equalizer_struct_data monad_to_hset_struct
    := λ X Y f g hX hY Mf Mg, equalizer_algebra hX hY Mf Mg.

  Proposition monad_to_hset_equalizer_struct_laws
    : hset_equalizer_struct_laws monad_to_hset_equalizer_struct_data.
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
      cbn -[Monad] in *.
      refine (eqtohomot Mk x @ _).
      apply maponpaths.
      refine (!_).
      exact (!(eqtohomot (functor_comp M _ _) _)).
  Qed.

  Definition monad_to_hset_equalizer_struct
    : hset_equalizer_struct monad_to_hset_struct
    := monad_to_hset_equalizer_struct_data
       ,,
       monad_to_hset_equalizer_struct_laws.

  (**
   4. Type indexed products of algebras
   *)
  Section TypeProdAlgebra.
    Context {J : UU}
            {D : J → hSet}
            (p : ∏ (i : J), monad_algebra (D i)).

    Let prod : Product J SET D := ProductsHSET J D.

    Definition monad_type_prod_map
      : M prod --> prod
      := ProductArrow _ _ prod (λ i, #M (ProductPr _ _ _ i) · p i).

    Proposition monad_type_prod_laws
      : monad_algebra_laws monad_type_prod_map.
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
        rewrite (monad_algebra_unit (p i)).
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
        rewrite (monad_algebra_mu (p i)).
        apply idpath.
    Qed.
  End TypeProdAlgebra.

  Definition monad_to_hset_struct_type_prod_data
             (J : UU)
    : hset_struct_type_prod_data monad_to_hset_struct J.
  Proof.
    intros D p.
    use make_monad_algebra.
    - exact (monad_type_prod_map p).
    - exact (monad_type_prod_laws p).
  Defined.

  Proposition monad_to_hset_struct_type_prod_laws
              (J : UU)
    : hset_struct_type_prod_laws (monad_to_hset_struct_type_prod_data J).
  Proof.
    split.
    - intros D PD i.
      apply idpath.
    - intros D PD W hW ps Mps.
      cbn -[Monad] in *.
      use funextsec ; intro x.
      use funextsec ; intro i.
      refine (eqtohomot (Mps i) x @ _).
      apply maponpaths.
      refine (!_).
      exact (!(eqtohomot (functor_comp M _ _) _)).
  Qed.

  Definition monad_to_hset_struct_type_prod
             (J : UU)
    : hset_struct_type_prod monad_to_hset_struct J
    := monad_to_hset_struct_type_prod_data J
       ,,
       monad_to_hset_struct_type_prod_laws J.

  (**
   5. The free algebra adjunction
   *)
  Proposition monad_free_alg_laws
              (X : hSet)
    : monad_algebra_laws (μ M X).
  Proof.
    split.
    - apply Monad_law1.
    - exact (!(@Monad_law3 _ M X)).
  Qed.

  Definition monad_free_alg_struct
             (X : hSet)
    : monad_algebra (M X).
  Proof.
    use make_monad_algebra.
    - exact (μ M X).
    - exact (monad_free_alg_laws X).
  Defined.

  Definition monad_free_alg
             (X : hSet)
    : category_of_monad_algebra
    := M X ,, monad_free_alg_struct X.

  Section FreeAlgAdjunction.
    Context {X : hSet}
            {Y : hSet}
            (hY : monad_algebra Y)
            (f : X → Y).

    Let YY : category_of_monad_algebra
      := Y ,, hY.

    Proposition monad_to_hset_struct_adj_lift_unique
      : isaprop
          (∑ f' : monad_free_alg X --> YY,
            η M X · # (underlying_of_hset_struct monad_to_hset_struct) f'
            =
            f).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use eq_mor_hset_struct.
      cbn ; intro x.
      pose (eqtohomot (@Monad_law2 _ M X) x) as p.
      cbn in p.
      rewrite <- p ; clear p.
      pose (eqtohomot (pr21 φ₁) (# M (η M X) x)) as p.
      cbn in p.
      rewrite p ; clear p.
      pose (eqtohomot (pr21 φ₂) (# M (η M X) x)) as p.
      cbn in p.
      rewrite p ; clear p.
      apply maponpaths.
      refine (!(eqtohomot (functor_comp M (η M X) (pr11 φ₁)) x) @ _).
      refine (_ @ eqtohomot (functor_comp M (η M X) (pr11 φ₂)) x).
      apply maponpaths_2.
      exact (pr2 φ₁ @ !(pr2 φ₂)).
    Qed.

    Definition monad_to_hset_struct_adj_lift
      : monad_free_alg X --> YY.
    Proof.
      refine (#M f · hY ,, _).
      cbn.
      use funextsec.
      intro x.
      etrans.
      {
        apply maponpaths.
        exact (!(eqtohomot (nat_trans_ax (μ M) _ _ f) x)).
      }
      cbn.
      refine (eqtohomot (monad_algebra_mu hY) (# M (# M f) x) @ _).
      cbn.
      apply maponpaths.
      exact (!(eqtohomot (functor_comp M _ _) _)).
    Defined.

    Proposition monad_to_hset_struct_adj_lift_eq
      : η M X · #M f · hY = f.
    Proof.
      rewrite <- (nat_trans_ax (η M) _ _ f).
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      exact (monad_algebra_unit hY).
    Qed.
  End FreeAlgAdjunction.

  Definition monad_underlying_is_right_adjoint
    : is_right_adjoint (underlying_of_hset_struct monad_to_hset_struct).
  Proof.
    use right_adjoint_left_from_partial.
    - exact (λ X, monad_free_alg X).
    - exact (λ X, η M X).
    - refine (λ X Y f, _).
      use iscontraprop1.
      + exact (monad_to_hset_struct_adj_lift_unique (pr2 Y) f).
      + simple refine (_ ,, _).
        * exact (monad_to_hset_struct_adj_lift (pr2 Y) f).
        * exact (monad_to_hset_struct_adj_lift_eq (pr2 Y) f).
  Defined.

  Definition monad_free_alg_functor
    : SET ⟶ category_of_monad_algebra
    := left_adjoint
         monad_underlying_is_right_adjoint.

  Definition monad_free_alg_unit
    : functor_identity _
      ⟹
      monad_free_alg_functor ∙ underlying_of_hset_struct monad_to_hset_struct
    := unit_from_right_adjoint monad_underlying_is_right_adjoint.

  Definition monad_free_alg_counit
    : underlying_of_hset_struct monad_to_hset_struct ∙ monad_free_alg_functor
      ⟹
      functor_identity _
    := counit_from_right_adjoint monad_underlying_is_right_adjoint.

  Definition free_alg_coproduct
             (X Y : hSet)
    : BinCoproduct (monad_free_alg X) (monad_free_alg Y)
    := (monad_free_alg (setcoprod X Y) ,, _ ,, _)
       ,,
       left_adjoint_preserves_bincoproduct
         (left_adjoint
            monad_underlying_is_right_adjoint)
         (is_left_adjoint_left_adjoint _)
         _ _ _ _ _
         (pr2 (BinCoproductsHSET X Y)).

  Proposition mor_from_free_alg_eq
              {X : hSet}
              {Y : category_of_monad_algebra}
              {f g : monad_free_alg_functor X --> Y}
              (p : η M X · pr1 f = η M X · pr1 g)
    : f = g.
  Proof.
    refine (!(id_left _) @ _ @ id_left _).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      exact (triangle_id_left_ad
               (pr2 monad_underlying_is_right_adjoint)
               X).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      exact (triangle_id_left_ad
               (pr2 monad_underlying_is_right_adjoint)
               X).
    }
    refine (!_).
    rewrite !assoc'.
    use subtypePath.
    {
      intro ; apply homset_property.
    }
    enough (# M (η M X · η M (M X)) · μ M (M X) · (# M (identity _) · μ M X · pr1 f)
            =
            # M (η M X · η M (M X)) · μ M (M X) · (# M (identity _) · μ M X · pr1 g))
      as q.
    {
      exact q.
    }
    rewrite !functor_id.
    rewrite id_left.
    etrans.
    {
      apply maponpaths.
      exact (pr2 f).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (pr2 g).
    }
    refine (!_).
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !functor_comp.
    rewrite !assoc'.
    rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (@Monad_law2 _ M (M X)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (@Monad_law2 _ M (M X)).
    }
    refine (!_).
    rewrite !id_left.
    rewrite <- !functor_comp.
    apply maponpaths.
    exact p.
  Qed.

  (**
   6. Every algebra is a coequalizer of a free algebra
   *)
  Section AlgebraAsCoequalizer.
    Context {X : hSet}
            (hX : monad_algebra X).

    Let F : SET ⟶ category_of_monad_algebra := monad_free_alg_functor.
    Let AX : category_of_monad_algebra := X ,, hX.

    Let FX : category_of_monad_algebra := monad_free_alg X.
    Let FUFX : category_of_monad_algebra := monad_free_alg (pr1 FX).

    Definition algebra_as_coequalizer_left_map
      : FUFX --> FX
      := monad_free_alg_counit FX.

    Let ℓ : FUFX --> FX := algebra_as_coequalizer_left_map.

    Definition algebra_as_coequalizer_right_map
      : FUFX --> FX
      := #F hX.

    Let ρ : FUFX --> FX := algebra_as_coequalizer_right_map.

    Definition algebra_as_coequalizer_arr
      : FX --> AX.
    Proof.
      simple refine (_ ,, _).
      - exact hX.
      - exact (monad_algebra_mu hX).
    Defined.

    Proposition algebra_as_coequalizer_arr_eq
      : ℓ · algebra_as_coequalizer_arr
        =
        ρ · algebra_as_coequalizer_arr.
    Proof.
      unfold ℓ, ρ.
      unfold algebra_as_coequalizer_left_map.
      unfold algebra_as_coequalizer_right_map.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      simpl.
      rewrite (functor_id M).
      etrans.
      {
        apply maponpaths_2.
        exact (id_left (μ M X)).
      }
      refine (monad_algebra_mu hX @ _).
      apply maponpaths_2.
      rewrite (functor_comp M).
      refine (_ @ assoc _ _ _).
      refine (!(id_right _) @ _).
      apply maponpaths.
      refine (!_).
      apply Monad_law2.
    Qed.

    Section UMP.
      Context {Y : category_of_monad_algebra}
              (g : FX --> Y)
              (p : ℓ · g = ρ · g).

      Proposition algebra_as_coequalizer_ump_unique
        : isaprop (∑ φ, algebra_as_coequalizer_arr · φ = g).
      Proof.
        use invproofirrelevance.
        intros φ₁ φ₂.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        refine (!(id_left _) @ _ @ id_left _).
        etrans.
        {
          apply maponpaths_2.
          exact (!(monad_algebra_unit hX)).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          exact (!(monad_algebra_unit hX)).
        }
        rewrite !assoc'.
        apply maponpaths.
        refine (!_).
        exact (maponpaths pr1 (pr2 φ₁ @ !(pr2 φ₂))).
      Qed.

      Lemma algebra_as_coequalizer_ump_eq_lem_1
        : # M hX · pr1 g = μ M X · pr1 g.
      Proof.
        refine (_ @ maponpaths pr1 (!p) @ _).
        - refine (maponpaths (λ z, z · _) _).
          simpl.
          rewrite (functor_comp M).
          refine (_ @ assoc (#M hX) _ _).
          refine (!(id_right _) @ _).
          apply maponpaths.
          refine (!_).
          apply Monad_law2.
        - refine (maponpaths (λ z, z · _) _).
          refine (_ @ id_left _).
          refine (maponpaths (λ z, z · _) _).
          apply functor_id.
      Qed.

      Lemma algebra_as_coequalizer_ump_eq_lem_2
        : hX · η M X · pr1 g = pr1 g.
      Proof.
        etrans.
        {
          apply maponpaths_2.
          exact (nat_trans_ax (η M) _ _ hX).
        }
        rewrite !assoc'.
        rewrite algebra_as_coequalizer_ump_eq_lem_1.
        rewrite !assoc.
        refine (_ @ id_left _).
        apply maponpaths_2.
        apply Monad_law1.
      Qed.

      Lemma algebra_as_coequalizer_ump_eq
        : hX · (η M X · pr1 g) = # M (η M X · pr1 g) · pr12 Y.
      Proof.
        rewrite functor_comp.
        rewrite !assoc'.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(pr2 g)).
        }
        rewrite !assoc.
        rewrite (@Monad_law2 _ M).
        rewrite id_left.
        refine (!_).
        apply algebra_as_coequalizer_ump_eq_lem_2.
      Qed.

      Definition algebra_as_coequalizer_ump
        : AX --> Y.
      Proof.
        simple refine (_ ,, _).
        - exact (η M X · pr1 g).
        - exact algebra_as_coequalizer_ump_eq.
      Defined.

      Proposition algebra_as_coequalizer_ump_comm
        : algebra_as_coequalizer_arr · algebra_as_coequalizer_ump = g.
      Proof.
        use subtypePath.
        {
          intro.
          apply homset_property.
        }
        simpl.
        apply algebra_as_coequalizer_ump_eq_lem_2.
      Qed.
    End UMP.

    Definition algebra_as_coequalizer
      : Coequalizer ℓ ρ.
    Proof.
      use make_Coequalizer.
      - exact AX.
      - exact algebra_as_coequalizer_arr.
      - exact algebra_as_coequalizer_arr_eq.
      - intros Y g p.
        use iscontraprop1.
        + exact (algebra_as_coequalizer_ump_unique g).
        + simple refine (_ ,, _).
          * exact (algebra_as_coequalizer_ump g p).
          * exact (algebra_as_coequalizer_ump_comm g p).
    Defined.
  End AlgebraAsCoequalizer.
End MonadToStruct.
