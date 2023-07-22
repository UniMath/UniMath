(*****************************************************************

 Cocompleteness of the category of algebras

 In this file, we look at the cocompleteness of the category of
 algebras for a monad. We proceed in the following steps.

 We start by looking when the category of algbras has reflexive
 coequalizers. This is the case if the monad preserves reflexive
 coequalizers. Note that this holds more generally (although we do
 not formalize that): if a monad preserves a class of colimits,
 then the category of algebras also has that class of colimits.

 The next step is to construct coproducts in the category of
 algebras, and this is where the main work happens. Here we
 assume that the category of algebras has reflexive coequalizers.

 Finally, we conclude cocompleteness, and for that, it suffices to
 construct coequalizers. Here we use a general statement: if a
 category has reflexive coequalizers and binary coproducts, then
 it also has coequalizers.

 Concluding, if the category of algebras has reflexive
 coequalizers, then it is cocomplete. Note that reflexive
 coequalizers are colimits, so these two statements are in fact
 equivalent.

 Note that the underlying assumption in this whole story is that
 the category of algebras has reflexive coequalizers, which is the
 case if the monad preserves reflexive coequalizers. It is
 worthwhile to note that every finitary monad preserves reflexive
 coequalizers. As such, the category of algebras for every finitary
 algebraic theory is thus cocomplete.

 Contents
 1. Reflexive coequalizers in the Eilenberg-Moore category
 2. Binary Coproducts
 3. Coequalizers

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.equalizers.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coequalizers.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.AlgebraStructures.
Require Import UniMath.CategoryTheory.Monads.Monads.

Local Open Scope cat.

Section MonadToStruct.
  Context (M : Monad SET).

  Definition monad_on_reflexive_coequalizer
             (HM : preserves_reflexive_coequalizer M)
             {X Y : hSet}
             {f g : SET ⟦ X , Y ⟧}
             {σ : SET ⟦ Y , X ⟧}
             (pf : ∏ (y : Y), f(σ y) = y)
             (pg : ∏ (y : Y), g(σ y) = y)
    : Coequalizer (#M f) (#M g).
  Proof.
    pose (C := pr11 (Coequalizers_HSET _ _ f g)).
    pose (π := CoequalizerArrow (Coequalizers_HSET _ _ f g)).
    simple refine ((M C ,, #M π) ,, _ ,, _).
    - abstract
        (refine (!(functor_comp M _ _) @ _ @ functor_comp M _ _) ;
         apply maponpaths ;
         exact (CoequalizerEqAr (Coequalizers_HSET _ _ f g))).
    - refine (HM X Y C f g σ _ _ π _ _ (pr22 (Coequalizers_HSET _ _ f g))).
      + abstract
          (use funextsec ;
           exact pf).
      + abstract
          (use funextsec ;
           exact pg).
  Defined.

  Definition monad_on_reflexive_coequalizer_2
             (HM : preserves_reflexive_coequalizer M)
             {X Y : hSet}
             {f g : SET ⟦ X , Y ⟧}
             {σ : SET ⟦ Y , X ⟧}
             (pf : ∏ (y : Y), f(σ y) = y)
             (pg : ∏ (y : Y), g(σ y) = y)
    : Coequalizer (#M(#M f)) (#M(#M g)).
  Proof.
    pose (C := pr11 (Coequalizers_HSET _ _ f g)).
    pose (π := CoequalizerArrow (Coequalizers_HSET _ _ f g)).
    simple refine ((M(M C) ,, #M(#M π)) ,, _ ,, _).
    - abstract
        (refine (!(functor_comp M _ _) @ _ @ functor_comp M _ _) ;
         apply maponpaths ;
         refine (!(functor_comp M _ _) @ _ @ functor_comp M _ _) ;
         apply maponpaths ;
         exact (CoequalizerEqAr (Coequalizers_HSET _ _ f g))).
    - simple refine (HM (M X) (M Y) (M C) (#M f) (#M g) (#M σ) _ _ (#M π) _ _ _).
      + abstract
          (refine (!(functor_comp M _ _) @ _ @ functor_id M _) ;
           apply maponpaths ;
           use funextsec ;
           exact pf).
      + abstract
          (refine (!(functor_comp M _ _) @ _ @ functor_id M _) ;
           apply maponpaths ;
           use funextsec ;
           exact pg).
      + abstract
          (refine (!(functor_comp M _ _) @ _ @ functor_comp M _ _) ;
           apply maponpaths ;
           exact (CoequalizerEqAr (Coequalizers_HSET _ _ f g))).
      + refine (HM X Y C f g σ _ _ π _ _ (pr22 (Coequalizers_HSET _ _ f g))).
        * abstract
            (use funextsec ;
             exact pf).
        * abstract
            (use funextsec ;
             exact pg).
  Defined.

  (**
   1. Reflexive coequalizers in the Eilenberg-Moore category
   *)
  Section ReflexiveCoequalizers.
    Context (HM : preserves_reflexive_coequalizer M).

    Section ReflexiveCoequalizerConstruction.
      Context {X Y : hSet}
              {hX : monad_algebra M X}
              {hY : monad_algebra M Y}
              {f g : SET ⟦ X , Y ⟧}
              (hf : hX · f = # M f · hY)
              (hg : hX · g = # M g · hY)
              {σ : SET ⟦ Y , X ⟧}
              (hσ : hY · σ = #M σ · hX)
              (pf : ∏ (y : Y), f(σ y) = y)
              (pg : ∏ (y : Y), g(σ y) = y).

      Let AX : category_of_monad_algebra M := X ,, hX.
      Let AY : category_of_monad_algebra M := Y ,, hY.
      Let Af : AX --> AY := f ,, hf.
      Let Ag : AX --> AY := g ,, hg.
      Let Aσ : AY --> AX := σ ,, hσ.

      Let C : hSet := pr11 (Coequalizers_HSET _ _ f g).
      Let π : SET ⟦ Y , C ⟧ := CoequalizerArrow (Coequalizers_HSET _ _ f g).
      Let Cp : f · π = g · π
        := CoequalizerEqAr (Coequalizers_HSET _ _ f g).
      Let Coeq : Coequalizer _ _
        := Coequalizers_HSET _ _ f g.

      Definition monad_reflexive_coequalizer_algebra_mor
        : M C --> C.
      Proof.
        use (CoequalizerOut (monad_on_reflexive_coequalizer HM pf pg)).
        - exact (hY · π).
        - abstract
            (rewrite !assoc ;
             rewrite <- hf, <- hg ;
             rewrite !assoc' ;
             rewrite Cp ;
             apply idpath).
      Defined.

      Proposition monad_reflexive_coequalizer_algebra_laws
        : monad_algebra_laws M monad_reflexive_coequalizer_algebra_mor.
      Proof.
        split.
        - use (CoequalizerOutsEq Coeq).
          rewrite id_right.
          unfold monad_reflexive_coequalizer_algebra_mor.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact (nat_trans_ax (η M) _ _ (CoequalizerArrow Coeq)).
          }
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply (CoequalizerCommutes (monad_on_reflexive_coequalizer _ _ _)).
          }
          rewrite !assoc.
          rewrite monad_algebra_unit.
          apply id_left.
        - use (CoequalizerOutsEq (monad_on_reflexive_coequalizer_2 HM pf pg)).
          unfold monad_reflexive_coequalizer_algebra_mor.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            apply (nat_trans_ax (μ M)).
          }
          rewrite !assoc'.
          etrans.
          {
            apply maponpaths.
            apply (CoequalizerCommutes (monad_on_reflexive_coequalizer _ _ _)).
          }
          rewrite !assoc.
          rewrite monad_algebra_mu.
          refine (!_).
          etrans.
          {
            apply maponpaths_2.
            refine (!(functor_comp _ _ _) @ _).
            apply maponpaths.
            apply (CoequalizerCommutes (monad_on_reflexive_coequalizer _ _ _)).
          }
          rewrite functor_comp.
          rewrite !assoc'.
          apply maponpaths.
          apply (CoequalizerCommutes (monad_on_reflexive_coequalizer _ _ _)).
      Qed.

      Definition monad_reflexive_coequalizer_algebra
        : monad_algebra M (coequalizer_hSet f g).
      Proof.
        use make_monad_algebra.
        - exact monad_reflexive_coequalizer_algebra_mor.
        - exact monad_reflexive_coequalizer_algebra_laws.
      Defined.

      Definition monad_reflexive_coequalizer_ob
        : category_of_monad_algebra M
        := C ,, monad_reflexive_coequalizer_algebra.

      Definition monad_reflexive_coequalizer_arrow
        : AY --> monad_reflexive_coequalizer_ob.
      Proof.
        refine (π ,, _).
        abstract
          (refine (!_) ;
           apply (CoequalizerCommutes (monad_on_reflexive_coequalizer _ _ _))).
      Defined.

      Proposition monad_reflexive_coequalizer_arrow_eq
        : Af · monad_reflexive_coequalizer_arrow
          =
          Ag · monad_reflexive_coequalizer_arrow.
      Proof.
        use subtypePath.
        {
          intro ; apply homset_property.
        }
        exact Cp.
      Qed.

      Section UMP.
        Context {W : hSet}
                (hW : monad_algebra M W)
                {l : Y → W}
                (hl : hY · l = #M l · hW)
                (p : f · l = g · l).

        Let AW : category_of_monad_algebra M := W ,, hW.

        Proposition monad_reflexive_coequalizer_ump_unique
          : isaprop
              (∑ (φ : monad_reflexive_coequalizer_ob --> AW),
               monad_reflexive_coequalizer_arrow · φ = l ,, hl).
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
          use (CoequalizerOutsEq Coeq).
          exact (maponpaths pr1 (pr2 φ₁ @ !(pr2 φ₂))).
        Qed.

        Definition monad_reflexive_coequalizer_ump_mor
          : monad_reflexive_coequalizer_ob --> AW.
        Proof.
          simple refine (_ ,, _).
          - exact (CoequalizerOut Coeq _ l p).
          - abstract
              (use (CoequalizerOutsEq (monad_on_reflexive_coequalizer HM pf pg)) ;
               refine (assoc _ monad_reflexive_coequalizer_algebra_mor _ @ _) ;
               unfold monad_reflexive_coequalizer_algebra_mor ;
               rewrite !assoc ;
               rewrite (CoequalizerCommutes (monad_on_reflexive_coequalizer HM pf pg)) ;
               rewrite !assoc' ;
               rewrite (CoequalizerCommutes Coeq) ;
               refine (hl @ _) ;
               rewrite !assoc ;
               refine (maponpaths (λ z, z · _) (!_)) ;
               refine (!(functor_comp M _ _) @ _) ;
               apply maponpaths ;
               apply (CoequalizerCommutes Coeq)).
        Defined.

        Proposition monad_reflexive_coequalizer_ump_commutes
          : monad_reflexive_coequalizer_arrow
            · monad_reflexive_coequalizer_ump_mor
            =
            l ,, hl.
        Proof.
          use subtypePath.
          {
            intro ; apply homset_property.
          }
          apply idpath.
        Qed.
      End UMP.

      Definition monad_reflexive_coequalizer
        : Coequalizer Af Ag.
      Proof.
        use make_Coequalizer.
        - exact monad_reflexive_coequalizer_ob.
        - exact monad_reflexive_coequalizer_arrow.
        - exact monad_reflexive_coequalizer_arrow_eq.
        - intros W h p.
          use iscontraprop1.
          + exact (monad_reflexive_coequalizer_ump_unique (pr2 W) (pr2 h)).
          + simple refine (_ ,, _).
            * apply (monad_reflexive_coequalizer_ump_mor (pr2 W) (pr2 h)).
              exact (maponpaths pr1 p).
            * apply monad_reflexive_coequalizer_ump_commutes.
      Defined.
    End ReflexiveCoequalizerConstruction.

    Definition monad_algebra_reflexive_coequalizers
      : reflexive_coequalizers (category_of_monad_algebra M).
    Proof.
      intros hx hy hf hg hh pf pg.
      use (monad_reflexive_coequalizer (pr2 hf) (pr2 hg) _ _).
      - exact (pr1 hh).
      - exact (eqtohomot (maponpaths pr1 pf)).
      - exact (eqtohomot (maponpaths pr1 pg)).
    Defined.
  End ReflexiveCoequalizers.

  (**
   2. Binary Coproducts
   *)
  Section BinaryCoproductsEM.
    Context (RC : reflexive_coequalizers (category_of_monad_algebra M)).

    Section CoproductAlgebra.
      Context (alg_X alg_Y : category_of_monad_algebra M).

      Let F : SET ⟶ category_of_monad_algebra M
        := monad_free_alg_functor M.

      Let U : category_of_monad_algebra M ⟶ SET
        := underlying_of_hset_struct (monad_to_hset_struct M).

      Let X : hSet := underlying_of_hset_struct _ alg_X.
      Let Y : hSet := underlying_of_hset_struct _ alg_Y.

      Let XY : @BinCoproduct HSET X Y := BinCoproductsHSET X Y.
      Let ι₁ : SET ⟦ X , XY ⟧ := inl.
      Let ι₂ : SET ⟦ Y , XY ⟧ := inr.

      Let hX : monad_algebra M X := pr2 alg_X.
      Let hY : monad_algebra M Y := pr2 alg_Y.

      Let S₁ : BinCoproduct (F X) (F Y)
        := free_alg_coproduct M X Y.

      Let S₂ : BinCoproduct (F(U(F X))) (F(U(F Y)))
        := free_alg_coproduct M (U(F X)) (U(F Y)).

      Definition binary_coprod_algebra_left_map
        : S₂ --> S₁.
      Proof.
        use BinCoproductOfArrows.
        - exact (monad_free_alg_counit M (F X)).
        - exact (monad_free_alg_counit M (F Y)).
      Defined.

      Let l : S₂ --> S₁
        := binary_coprod_algebra_left_map.

      Definition binary_coprod_algebra_right_map
        : S₂ --> S₁.
      Proof.
        use BinCoproductOfArrows.
        - exact (#F(#U (monad_free_alg_counit M alg_X))).
        - exact (#F(#U (monad_free_alg_counit M alg_Y))).
      Defined.

      Let r : S₂ --> S₁
        := binary_coprod_algebra_right_map.

      Definition binary_coprod_algebra_section
        : S₁ --> S₂.
      Proof.
        use BinCoproductOfArrows.
        - exact (#F (monad_free_alg_unit M X)).
        - exact (#F (monad_free_alg_unit M Y)).
      Defined.

      Let s : S₁ --> S₂
        := binary_coprod_algebra_section.

      Proposition binary_coprod_algebra_section_left_map
        : s · l = identity _.
      Proof.
        unfold s, l.
        use BinCoproductArrowsEq.
        - rewrite id_right.
          rewrite !assoc.
          unfold binary_coprod_algebra_section.
          rewrite BinCoproductOfArrowsIn1.
          rewrite !assoc'.
          unfold binary_coprod_algebra_left_map.
          rewrite BinCoproductOfArrowsIn1.
          rewrite !assoc.
          refine (_ @ id_left _).
          apply maponpaths_2.
          exact (triangle_id_left_ad
                   (pr2 (monad_underlying_is_right_adjoint M))
                   X).
        - rewrite id_right.
          rewrite !assoc.
          unfold binary_coprod_algebra_section.
          rewrite BinCoproductOfArrowsIn2.
          rewrite !assoc'.
          unfold binary_coprod_algebra_left_map.
          rewrite BinCoproductOfArrowsIn2.
          rewrite !assoc.
          refine (_ @ id_left _).
          apply maponpaths_2.
          exact (triangle_id_left_ad
                   (pr2 (monad_underlying_is_right_adjoint M))
                   Y).
      Qed.

      Let sl : s · l = identity _
        := binary_coprod_algebra_section_left_map.

      Proposition binary_coprod_algebra_section_right_map
        : s · r = identity _.
      Proof.
        unfold s, r.
        use BinCoproductArrowsEq.
        - rewrite id_right.
          rewrite !assoc.
          unfold binary_coprod_algebra_section.
          rewrite BinCoproductOfArrowsIn1.
          rewrite !assoc'.
          unfold binary_coprod_algebra_right_map.
          rewrite BinCoproductOfArrowsIn1.
          rewrite !assoc.
          refine (_ @ id_left _).
          apply maponpaths_2.
          rewrite <- (functor_comp F).
          refine (_ @ functor_id F _).
          apply maponpaths.
          exact (triangle_id_right_ad
                   (pr2 (monad_underlying_is_right_adjoint M))
                   alg_X).
        - rewrite id_right.
          rewrite !assoc.
          unfold binary_coprod_algebra_section.
          rewrite BinCoproductOfArrowsIn2.
          rewrite !assoc'.
          unfold binary_coprod_algebra_right_map.
          rewrite BinCoproductOfArrowsIn2.
          rewrite !assoc.
          refine (_ @ id_left _).
          apply maponpaths_2.
          rewrite <- (functor_comp F).
          refine (_ @ functor_id F _).
          apply maponpaths.
          exact (triangle_id_right_ad
                   (pr2 (monad_underlying_is_right_adjoint M))
                   alg_Y).
      Qed.

      Let sr : s · r = identity _
        := binary_coprod_algebra_section_right_map.

      Definition binary_coprod_algebra_ob
        : Coequalizer l r
        := RC _ _ l r s sl sr.

      Let C : hSet := pr111 binary_coprod_algebra_ob.
      Let hC : monad_algebra M C := pr211 binary_coprod_algebra_ob.

      Lemma binary_coprod_algebra_in1_eq
        : μ M X
          · #M(ι₁ · η M XY)
          · μ M XY
          · pr1 (CoequalizerArrow binary_coprod_algebra_ob)
          =
          #M (hX · η M X)
          · μ M X
          · #M(ι₁ · η M XY)
          · μ M XY
          · pr1 (CoequalizerArrow binary_coprod_algebra_ob).
      Proof.
        assert (BinCoproductIn1 S₂ · (l · CoequalizerArrow binary_coprod_algebra_ob)
                =
                BinCoproductIn1 S₂ · (r · CoequalizerArrow binary_coprod_algebra_ob))
          as p.
        {
          exact (maponpaths
                   (λ z, BinCoproductIn1 _ · z)
                   (CoequalizerEqAr binary_coprod_algebra_ob)).
        }
        unfold l in p.
        unfold r in p.
        unfold binary_coprod_algebra_left_map in p.
        unfold binary_coprod_algebra_right_map in p.
        rewrite !assoc in p.
        rewrite !BinCoproductOfArrowsIn1 in p.
        assert (# M (identity (M X))
                · μ M X
                · (# M (ι₁ · η M XY) · μ M XY)
                · pr1 (CoequalizerArrow binary_coprod_algebra_ob)
                =
                # M (# M (identity _)
                     · hX
                     · η M X)
                · μ M X
                · (# M (ι₁ · η M XY) · μ M XY)
                · pr1 (CoequalizerArrow binary_coprod_algebra_ob))
          as q.
        {
          exact (maponpaths pr1 p).
        }
        rewrite !functor_id in q.
        rewrite !id_left in q.
        refine (_ @ q).
        rewrite !assoc'.
        apply idpath.
      Qed.

      Definition binary_coprod_algebra_in1
        : alg_X --> binary_coprod_algebra_ob.
      Proof.
        use (CoequalizerOut (algebra_as_coequalizer M hX)).
        - exact (BinCoproductIn1 _ · CoequalizerArrow binary_coprod_algebra_ob).
        - abstract
            (use subtypePath ; [ intro ; apply homset_property | ] ;
             refine (_ @ binary_coprod_algebra_in1_eq) ;
             simpl ;
             rewrite (functor_id M) ;
             exact (maponpaths (λ z, z · _) (id_left (μ M X)))).
      Defined.

      Lemma binary_coprod_algebra_in2_eq
        : μ M Y
          · #M(ι₂ · η M XY)
          · μ M XY
          · pr1 (CoequalizerArrow binary_coprod_algebra_ob)
          =
          #M (hY · η M Y)
          · μ M Y
          · #M(ι₂ · η M XY)
          · μ M XY
          · pr1 (CoequalizerArrow binary_coprod_algebra_ob).
      Proof.
        assert (BinCoproductIn2 S₂ · (l · CoequalizerArrow binary_coprod_algebra_ob)
                =
                BinCoproductIn2 S₂ · (r · CoequalizerArrow binary_coprod_algebra_ob))
          as p.
        {
          exact (maponpaths
                   (λ z, BinCoproductIn2 _ · z)
                   (CoequalizerEqAr binary_coprod_algebra_ob)).
        }
        unfold l in p.
        unfold r in p.
        unfold binary_coprod_algebra_left_map in p.
        unfold binary_coprod_algebra_right_map in p.
        rewrite !assoc in p.
        rewrite !BinCoproductOfArrowsIn2 in p.
        assert (# M (identity (M Y))
                · μ M Y
                · (# M (ι₂ · η M XY) · μ M XY)
                · pr1 (CoequalizerArrow binary_coprod_algebra_ob)
                =
                # M (# M (identity _)
                     · hY
                     · η M Y)
                · μ M Y
                · (# M (ι₂ · η M XY) · μ M XY)
                · pr1 (CoequalizerArrow binary_coprod_algebra_ob))
          as q.
        {
          exact (maponpaths pr1 p).
        }
        rewrite !functor_id in q.
        rewrite !id_left in q.
        refine (_ @ q).
        rewrite !assoc'.
        apply idpath.
      Qed.

      Definition binary_coprod_algebra_in2
        : alg_Y --> binary_coprod_algebra_ob.
      Proof.
        use (CoequalizerOut (algebra_as_coequalizer M hY)).
        - exact (BinCoproductIn2 _ · CoequalizerArrow binary_coprod_algebra_ob).
        - abstract
            (use subtypePath ; [ intro ; apply homset_property | ] ;
             refine (_ @ binary_coprod_algebra_in2_eq) ;
             simpl ;
             rewrite (functor_id M) ;
             exact (maponpaths (λ z, z · _) (id_left (μ M Y)))).
      Defined.

      Section UMP.
        Context {Z : category_of_monad_algebra M}
                (φ₁ : alg_X --> Z)
                (φ₂ : alg_Y --> Z).

        Definition binary_coprod_algebra_arrow_ob
          : S₁ --> Z.
        Proof.
          use BinCoproductArrow.
          - exact (monad_free_alg_counit M alg_X · φ₁).
          - exact (monad_free_alg_counit M alg_Y · φ₂).
        Defined.

        Definition binary_coprod_algebra_arrow
          : binary_coprod_algebra_ob --> Z.
        Proof.
          use CoequalizerOut.
          - exact binary_coprod_algebra_arrow_ob.
          - use BinCoproductArrowsEq.
            + abstract
                (rewrite !assoc ;
                 unfold l, binary_coprod_algebra_left_map ;
                 unfold r, binary_coprod_algebra_right_map ;
                 unfold binary_coprod_algebra_arrow_ob ;
                 rewrite !BinCoproductOfArrowsIn1 ;
                 rewrite !assoc' ;
                 rewrite BinCoproductIn1Commutes ;
                 rewrite !assoc ;
                 apply maponpaths_2 ;
                 exact (!(nat_trans_ax (monad_free_alg_counit M) _ _ _))).
            + abstract
                (rewrite !assoc ;
                 unfold l, binary_coprod_algebra_left_map ;
                 unfold r, binary_coprod_algebra_right_map ;
                 unfold binary_coprod_algebra_arrow_ob ;
                 rewrite !BinCoproductOfArrowsIn2 ;
                 rewrite !assoc' ;
                 rewrite BinCoproductIn2Commutes ;
                 rewrite !assoc ;
                 apply maponpaths_2 ;
                 exact (!(nat_trans_ax (monad_free_alg_counit M) _ _ _))).
        Defined.

        Proposition binary_coprod_algebra_arrow_in1
          : binary_coprod_algebra_in1 · binary_coprod_algebra_arrow = φ₁.
        Proof.
          use subtypePath.
          {
            intro.
            apply homset_property.
          }
          enough (η M X
                  · (# M (ι₁ · η M XY) · μ M XY
                     · pr1 (CoequalizerArrow binary_coprod_algebra_ob))
                  · pr1 binary_coprod_algebra_arrow
                  =
                  pr1 φ₁)
            as p.
          {
            exact p.
          }
          rewrite !assoc'.
          etrans.
          {
            do 3 apply maponpaths.
            exact (maponpaths
                     pr1
                     (CoequalizerCommutes binary_coprod_algebra_ob _ _ _)).
          }
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            apply maponpaths_2.
            rewrite functor_comp.
            rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              exact (@Monad_law2 _ M XY).
            }
            apply id_right.
          }
          etrans.
          {
            apply maponpaths.
            pose (maponpaths
                    pr1
                    (BinCoproductIn1Commutes
                       _ _ _
                       S₁
                       Z
                       (monad_free_alg_counit M alg_X · φ₁)
                       (monad_free_alg_counit M alg_Y · φ₂)))
              as p.
            refine (_ @ p).
            refine (maponpaths (λ z, z · _) _).
            refine (!(id_right _) @ _).
            simpl.
            rewrite (functor_comp M).
            refine (_ @ assoc (#M ι₁) _ _).
            apply maponpaths.
            refine (!_).
            apply (Monad_law2(T:=M)).
          }
          refine (_ @ id_left _).
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          simpl.
          rewrite (functor_id M).
          etrans.
          {
            apply maponpaths.
            exact (id_left hX).
          }
          apply monad_algebra_unit.
        Qed.

        Proposition binary_coprod_algebra_arrow_in2
          : binary_coprod_algebra_in2 · binary_coprod_algebra_arrow = φ₂.
        Proof.
          use subtypePath.
          {
            intro.
            apply homset_property.
          }
          enough (η M Y
                  · (# M (ι₂ · η M XY) · μ M XY
                     · pr1 (CoequalizerArrow binary_coprod_algebra_ob))
                  · pr1 binary_coprod_algebra_arrow
                  =
                  pr1 φ₂)
            as p.
          {
            exact p.
          }
          rewrite !assoc'.
          etrans.
          {
            do 3 apply maponpaths.
            exact (maponpaths
                     pr1
                     (CoequalizerCommutes binary_coprod_algebra_ob _ _ _)).
          }
          etrans.
          {
            apply maponpaths.
            rewrite !assoc.
            apply maponpaths_2.
            rewrite functor_comp.
            rewrite !assoc'.
            etrans.
            {
              apply maponpaths.
              exact (@Monad_law2 _ M XY).
            }
            apply id_right.
          }
          etrans.
          {
            apply maponpaths.
            pose (maponpaths
                    pr1
                    (BinCoproductIn2Commutes
                       _ _ _
                       S₁
                       Z
                       (monad_free_alg_counit M alg_X · φ₁)
                       (monad_free_alg_counit M alg_Y · φ₂)))
              as p.
            refine (_ @ p).
            refine (maponpaths (λ z, z · _) _).
            refine (!(id_right _) @ _).
            simpl.
            rewrite (functor_comp M).
            refine (_ @ assoc (#M ι₂) _ _).
            apply maponpaths.
            refine (!_).
            apply (Monad_law2(T:=M)).
          }
          refine (_ @ id_left _).
          refine (assoc _ _ _ @ _).
          apply maponpaths_2.
          simpl.
          rewrite (functor_id M).
          etrans.
          {
            apply maponpaths.
            exact (id_left hY).
          }
          apply monad_algebra_unit.
        Qed.

        Proposition binary_coprod_algebra_arrow_unique
          : isaprop
              (∑ fg,
               (binary_coprod_algebra_in1 · fg = φ₁)
               ×
               (binary_coprod_algebra_in2 · fg = φ₂)).
        Proof.
          use invproofirrelevance.
          intros ψ₁ ψ₂.
          use subtypePath.
          {
            intro.
            apply isapropdirprod ; apply homset_property.
          }
          use CoequalizerOutsEq.
          use BinCoproductArrowsEq.
          - use mor_from_free_alg_eq.
            exact (maponpaths pr1 (pr12 ψ₁ @ !(pr12 ψ₂))).
          - use mor_from_free_alg_eq.
            exact (maponpaths pr1 (pr22 ψ₁ @ !(pr22 ψ₂))).
        Qed.
      End UMP.

      Definition binary_coprod_algebra
        : BinCoproduct alg_X alg_Y.
      Proof.
        use make_BinCoproduct.
        - exact binary_coprod_algebra_ob.
        - exact binary_coprod_algebra_in1.
        - exact binary_coprod_algebra_in2.
        - intros Z φ₁ φ₂.
          use iscontraprop1.
          + exact (binary_coprod_algebra_arrow_unique φ₁ φ₂).
          + simple refine (_ ,, _ ,, _).
            * exact (binary_coprod_algebra_arrow φ₁ φ₂).
            * exact (binary_coprod_algebra_arrow_in1 φ₁ φ₂).
            * exact (binary_coprod_algebra_arrow_in2 φ₁ φ₂).
      Defined.
    End CoproductAlgebra.

    Definition monad_algebra_binary_coproducts
      : BinCoproducts (category_of_monad_algebra M).
    Proof.
      intros hx hy.
      exact (binary_coprod_algebra hx hy).
    Defined.
  End BinaryCoproductsEM.

  (**
   3. Coequalizers
   *)
  Definition monad_algebra_coequalizers
             (RC : reflexive_coequalizers (category_of_monad_algebra M))
    : Coequalizers (category_of_monad_algebra M).
  Proof.
    use coequalizers_from_reflexive.
    - exact RC.
    - exact (monad_algebra_binary_coproducts RC).
  Defined.
End MonadToStruct.
