(**

 A parameterized natural numbers object for presheaves

 We verify that presheaves come with a (parameterized) natural numbers object. This
 object is construct as a constant presheaf using the natural numbers. The structure
 maps correspond to the structure maps in sets. We also prove that the natural
 numbers object is stable under substitution.

 Content
 1. The presheaf of natural numbers
 2. Zero and successor
 3. Recursion
 4. The parameterized natural numbers object
 5. Stability

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Arithmetic.NNO.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.

Local Open Scope cat.

Section ParameterizedNNO.
  Context {C : category}.

  (** * 1. The presheaf of natural numbers *)
  Definition nno_dep_psh
             (Γ : C^op ⟶ HSET)
    : dep_psh Γ
    := constant_dep_psh Γ natset.

  (** * 2. Zero and successor *)
  Definition nno_dep_psh_Z
             (Γ : C^op ⟶ HSET)
    : dep_psh_nat_trans
        (unit_dep_psh Γ)
        (nno_dep_psh Γ)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx _, 0).
    - abstract
        (intros x y xx yy f p q t ;
         cbn ;
         apply idpath).
  Defined.

  Definition nno_dep_psh_S
             (Γ : C^op ⟶ HSET)
    : dep_psh_nat_trans
        (nno_dep_psh Γ)
        (nno_dep_psh Γ)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx n, S n).
    - abstract
        (intros x y xx yy f p q t ;
         cbn ;
         apply idpath).
  Defined.

  (** * 3. Recursion *)
  Section Recursion.
    Context {Γ : C^op ⟶ HSET}
            {A B : dep_psh Γ}
            (zτ : dep_psh_nat_trans A B (nat_trans_id _))
            (sτ : dep_psh_nat_trans B B (nat_trans_id _)).

    Definition nno_dep_psh_rec_mor
               (x : C)
               (xx : (Γ x : hSet))
               (an : A x xx × ℕ)
      : B x xx.
    Proof.
      induction an as [ a n ].
      induction n as [ | n IHn ].
      - exact (zτ x xx a).
      - exact (sτ x xx IHn).
    Defined.

    Proposition nno_dep_psh_rec_laws
      : dep_psh_nat_trans_naturality
          (A := prod_dep_psh A (nno_dep_psh Γ))
          (B := B)
          (s := nat_trans_id _)
          nno_dep_psh_rec_mor.
    Proof.
      intros x y xx yy s p q an.
      induction an as [ a n ].
      induction n as [ | n IHn ].
      - exact (dep_psh_nat_trans_ax zτ s p q a).
      - refine (!_).
        etrans.
        {
          refine (!_).
          exact (dep_psh_nat_trans_ax sτ s p q (nno_dep_psh_rec_mor x xx (a ,, n))).
        }
        etrans.
        {
          apply maponpaths.
          refine (_ @ !IHn).
          apply dep_psh_mor_path_eq.
          apply idpath.
        }
        apply idpath.
    Qed.

    Definition nno_dep_psh_rec
      : dep_psh_nat_trans
          (prod_dep_psh A (nno_dep_psh Γ))
          B
          (nat_trans_id _).
    Proof.
      use make_dep_psh_nat_trans.
      - exact nno_dep_psh_rec_mor.
      - exact nno_dep_psh_rec_laws.
    Defined.

    Proposition nno_dep_psh_rec_Z
      : BinProductArrow
          ((disp_cat_dep_psh C) [{Γ}])
          (dep_psh_fiber_binproducts Γ A (nno_dep_psh Γ))
          (identity _)
          (TerminalArrow (dep_psh_fiber_terminal Γ) A · nno_dep_psh_Z Γ)
        · nno_dep_psh_rec
        =
        zτ.
    Proof.
      cbn -[fiber_category].
      use dep_psh_nat_trans_eq.
      intros x xx a.
      refine (dep_psh_fiber_comp _ _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        cbn -[fiber_category].
        apply maponpaths.
        exact (dep_psh_fiber_comp _ _ (nno_dep_psh_Z Γ) a).
      }
      cbn.
      apply idpath.
    Qed.

    Proposition nno_dep_psh_rec_S
      : BinProductOfArrows
          ((disp_cat_dep_psh C) [{Γ}])
          (dep_psh_fiber_binproducts Γ A (nno_dep_psh Γ))
          (dep_psh_fiber_binproducts Γ A (nno_dep_psh Γ))
          (identity _)
          (nno_dep_psh_S Γ)
        · nno_dep_psh_rec
        =
        compose (C := (disp_cat_dep_psh C)[{Γ}]) nno_dep_psh_rec sτ.
    Proof.
      use dep_psh_nat_trans_eq.
      intros x xx a.
      refine (dep_psh_fiber_comp _ _ _ _ @ _).
      etrans.
      {
        apply maponpaths.
        cbn -[fiber_category].
        rewrite !dep_psh_fiber_comp.
        apply idpath.
      }
      refine (_ @ !(dep_psh_fiber_comp _ _ _ _)).
      cbn.
      apply idpath.
    Qed.

    Proposition nno_dep_psh_rec_unique
                (τ' : ∑ f,
                      (BinProductArrow
                         ((disp_cat_dep_psh C) [{Γ}])
                         (dep_psh_fiber_binproducts Γ A (nno_dep_psh Γ))
                         (identity _)
                         (TerminalArrow (dep_psh_fiber_terminal Γ) A
                          · nno_dep_psh_Z Γ)
                       · f
                       =
                       zτ)
                      ×
                      (BinProductOfArrows
                         ((disp_cat_dep_psh C) [{Γ}])
                         (dep_psh_fiber_binproducts Γ A (nno_dep_psh Γ))
                         (dep_psh_fiber_binproducts Γ A (nno_dep_psh Γ))
                         (identity _)
                         (nno_dep_psh_S Γ)
                       · f
                       =
                       f · sτ))
      : pr1 τ' = nno_dep_psh_rec.
    Proof.
      use dep_psh_nat_trans_eq.
      cbn.
      intros x xx an.
      induction an as [ a n ].
      induction n as [ | n IHn ].
      - cbn.
        refine (_ @ maponpaths (λ (z : dep_psh_nat_trans _ _ _), z x xx a) (pr12 τ')).
        refine (_ @ !(dep_psh_fiber_comp _ _ _ _)).
        apply maponpaths.
        cbn -[fiber_category].
        rewrite dep_psh_fiber_comp.
        cbn.
        apply idpath.
      - refine (!_).
        etrans.
        {
          cbn.
          apply maponpaths.
          exact (!IHn).
        }
        pose (maponpaths
                (λ (z : dep_psh_nat_trans (prod_dep_psh A (nno_dep_psh Γ)) _ _),
                 z x xx (a ,, n))
                (pr22 τ'))
          as p.
        refine (_ @ !p @ _) ; clear p.
        + exact (!(dep_psh_fiber_comp _ _ _ _)).
        + refine (dep_psh_fiber_comp _ _ _ _ @ _).
          apply maponpaths.
          cbn -[fiber_category].
          rewrite !dep_psh_fiber_comp.
          cbn.
          apply idpath.
    Qed.
  End Recursion.

  (** * 4. The parameterized natural numbers object *)
  Definition dep_psh_fiberwise_nno
             (Γ : C^op ⟶ HSET)
    : parameterized_NNO
        (dep_psh_fiber_terminal Γ)
        (dep_psh_fiber_binproducts Γ).
  Proof.
    use make_parameterized_NNO.
    - exact (nno_dep_psh Γ).
    - exact (nno_dep_psh_Z Γ).
    - exact (nno_dep_psh_S Γ).
    - intros A B zτ sτ.
      use make_iscontr.
      + simple refine (_ ,, _ ,, _).
        * exact (nno_dep_psh_rec zτ sτ).
        * apply nno_dep_psh_rec_Z.
        * apply nno_dep_psh_rec_S.
      + abstract
          (intro τ' ;
           use subtypePath ;
           [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           apply nno_dep_psh_rec_unique).
  Defined.

  (** * 5. Stability *)
  Definition dep_psh_fiberwise_nno_stable_inv
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : dep_psh_nat_trans
        (dep_psh_subst s (nno_dep_psh Γ₂))
        (nno_dep_psh Γ₁)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx n, n).
    - abstract
        (intros x y xx yy f p q n ;
         cbn ;
         apply idpath).
  Defined.

  Proposition dep_psh_fiberwise_nno_stable_laws
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : is_inverse_in_precat
        (preserves_parameterized_NNO_mor
           (dep_psh_fiberwise_nno Γ₂)
           (dep_psh_fiberwise_nno Γ₁)
           (fiber_functor_from_cleaving
              (disp_cat_dep_psh C)
              (cleaving_disp_cat_dep_psh C)
              s)
           (dep_psh_preserves_terminal s))
        (dep_psh_fiberwise_nno_stable_inv s).
  Proof.
    split.
    - use dep_psh_nat_trans_eq.
      intros x xx n.
      refine (dep_psh_fiber_comp _ _ _ _ @ _).
      cbn -[fiber_category fiber_functor_from_cleaving].
      unfold preserves_parameterized_NNO_mor, is_NNO_parameterized_NNO_mor.
      rewrite dep_psh_fiber_comp.
      cbn -[fiber_category fiber_functor_from_cleaving].
      rewrite !dep_psh_fiber_comp.
      induction n as [ | n IHn ].
      + cbn -[fiber_functor_from_cleaving].
        rewrite (dep_psh_fiber_functor_from_cleaving _ s).
        cbn.
        apply idpath.
      + cbn -[fiber_functor_from_cleaving].
        rewrite (dep_psh_fiber_functor_from_cleaving _ s).
        cbn.
        apply maponpaths.
        exact IHn.
    - use dep_psh_nat_trans_eq.
      intros x xx n.
      refine (dep_psh_fiber_comp _ _ _ _ @ _).
      cbn -[fiber_category fiber_functor_from_cleaving].
      unfold preserves_parameterized_NNO_mor, is_NNO_parameterized_NNO_mor.
      rewrite dep_psh_fiber_comp.
      cbn -[fiber_category fiber_functor_from_cleaving].
      rewrite !dep_psh_fiber_comp.
      induction n as [ | n IHn ].
      + cbn -[fiber_functor_from_cleaving].
        rewrite (dep_psh_fiber_functor_from_cleaving _ s).
        cbn.
        apply idpath.
      + cbn -[fiber_functor_from_cleaving].
        rewrite (dep_psh_fiber_functor_from_cleaving _ s).
        cbn.
        apply maponpaths.
        exact IHn.
  Qed.

  Definition dep_psh_fiberwise_nno_stable
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : preserves_parameterized_NNO
        (dep_psh_fiberwise_nno Γ₂)
        (dep_psh_fiberwise_nno Γ₁)
        (fiber_functor_from_cleaving
           (disp_cat_dep_psh C)
           (cleaving_disp_cat_dep_psh C)
           s)
        (dep_psh_preserves_terminal s).
  Proof.
    use make_is_z_isomorphism.
    - exact (dep_psh_fiberwise_nno_stable_inv s).
    - exact (dep_psh_fiberwise_nno_stable_laws s).
  Defined.
End ParameterizedNNO.
