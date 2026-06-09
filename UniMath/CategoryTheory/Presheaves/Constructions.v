(**

 Constructions of dependent presheaves

 We give various constructions of dependent presheaves, which allows us to establish
 simple type formers in the presheaf model. Specifically, we show that the displayed
 category of dependent presheaves has fiberwise finite limits and fiberwise finite
 coproducts. We also construct constant dependent presheaves and we show that the
 resulting model is democratic.

 Content
 1. Fiberwise initial object
 2. Fiberwise terminal object
 3. Fiberwise binary products
 4. Fiberwise binary coproducts
 5. Fiberwise equalizers
 6. Constant dependent presheaves
 7. Democracy of the presheaf model
 8. Statements for fiberwise limits and colimits

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseInitial.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseCoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.

Local Open Scope cat.

Section ExamplesDepPsh.
  Context {C : category}.

  (** * 1. Fiberwise initial object *)
  Definition empty_dep_psh
             (Γ : C^op ⟶ HSET)
    : dep_psh Γ.
  Proof.
    use make_dep_psh.
    - exact (λ _ _, emptyset).
    - intros x y xx yy s p a.
      induction a.
    - abstract
        (intros ; cbn ;
         apply isapropempty).
    - abstract
        (intros ; cbn ;
         apply isapropempty).
  Defined.

  Definition dep_psh_nat_trans_from_empty
             {Γ : C^op ⟶ HSET}
             (A : dep_psh Γ)
    : dep_psh_nat_trans
        (empty_dep_psh Γ)
        A
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - intros x xx a.
      induction a.
    - abstract
        (intros x y xx yy f p q a ;
         induction a).
  Defined.

  Proposition dep_psh_nat_trans_from_empty_eq
              {Γ : C^op ⟶ HSET}
              {A : dep_psh Γ}
              (τ₁ τ₂ : dep_psh_nat_trans
                         (empty_dep_psh Γ)
                         A
                         (nat_trans_id _))
    : τ₁ = τ₂.
  Proof.
    use dep_psh_nat_trans_eq.
    intros x xx a.
    induction a.
  Qed.

  Definition empty_dep_psh_subst
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : dep_psh_nat_trans
        (empty_dep_psh Γ₁)
        (dep_psh_subst s (empty_dep_psh Γ₂))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx a, a).
    - abstract
        (intros x y xx yy f p q a ;
         induction a).
  Defined.

  Definition empty_dep_psh_subst_inv
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : dep_psh_nat_trans
        (dep_psh_subst s (empty_dep_psh Γ₂))
        (empty_dep_psh Γ₁)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx a, a).
    - abstract
        (intros x y xx yy f p q a ;
         induction a).
  Defined.

  Definition dep_psh_fiber_initial
             (Γ : C^op ⟶ HSET)
    : Initial ((disp_cat_dep_psh C) [{ Γ }]).
  Proof.
    use make_Initial.
    - exact (empty_dep_psh Γ).
    - intros A.
      use make_iscontr.
      + exact (dep_psh_nat_trans_from_empty A).
      + intro.
        apply dep_psh_nat_trans_from_empty_eq.
  Defined.

  Definition dep_psh_preserves_initial
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : preserves_initial
        (fiber_functor_from_cleaving
           (disp_cat_dep_psh C)
           (cleaving_disp_cat_dep_psh C)
           s).
  Proof.
    use preserves_initial_if_preserves_chosen.
    {
      apply dep_psh_fiber_initial.
    }
    use iso_to_Initial.
    {
      apply dep_psh_fiber_initial.
    }
    use make_z_iso.
    - exact (empty_dep_psh_subst s).
    - exact (empty_dep_psh_subst_inv s).
    - split.
      + abstract
          (use dep_psh_nat_trans_eq ;
           intros x xx a ;
           induction a).
      + abstract
          (use dep_psh_nat_trans_eq ;
           intros x xx a ;
           induction a).
  Defined.

  (** * 2. Fiberwise terminal object *)
  Definition unit_dep_psh
             (Γ : C^op ⟶ HSET)
    : dep_psh Γ.
  Proof.
    use make_dep_psh.
    - exact (λ _ _, unitset).
    - exact (λ _ _ _ _ _ _ _, tt).
    - abstract
        (intros ; cbn ;
         apply isapropunit).
    - abstract
        (intros ; cbn ;
         apply isapropunit).
  Defined.

  Definition dep_psh_nat_trans_to_unit
             {Γ : C^op ⟶ HSET}
             (A : dep_psh Γ)
    : dep_psh_nat_trans
        A
        (unit_dep_psh Γ)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx a, tt).
    - abstract
        (intro ; intros ;
         apply isapropunit).
  Defined.

  Proposition dep_psh_nat_trans_to_unit_eq
              {Γ : C^op ⟶ HSET}
              {A : dep_psh Γ}
              (τ₁ τ₂ : dep_psh_nat_trans
                         A
                         (unit_dep_psh Γ)
                         (nat_trans_id _))
    : τ₁ = τ₂.
  Proof.
    use dep_psh_nat_trans_eq.
    intros x xx a.
    apply isapropunit.
  Qed.

  Definition unit_dep_psh_subst
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : dep_psh_nat_trans
        (unit_dep_psh Γ₁)
        (dep_psh_subst s (unit_dep_psh Γ₂))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx a, a).
    - abstract
        (intros x y xx yy f p q a ;
         apply isapropunit).
  Defined.

  Definition unit_dep_psh_subst_inv
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : dep_psh_nat_trans
        (dep_psh_subst s (unit_dep_psh Γ₂))
        (unit_dep_psh Γ₁)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx a, a).
    - abstract
        (intros x y xx yy f p q a ;
         apply isapropunit).
  Defined.

  Definition dep_psh_fiber_terminal
             (Γ : C^op ⟶ HSET)
    : Terminal ((disp_cat_dep_psh C) [{ Γ }]).
  Proof.
    use make_Terminal.
    - exact (unit_dep_psh Γ).
    - intros A.
      use make_iscontr.
      + exact (dep_psh_nat_trans_to_unit A).
      + intro.
        apply dep_psh_nat_trans_to_unit_eq.
  Defined.

  Definition dep_psh_preserves_terminal
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : preserves_terminal
        (fiber_functor_from_cleaving
           (disp_cat_dep_psh C)
           (cleaving_disp_cat_dep_psh C)
           s).
  Proof.
    use preserves_terminal_if_preserves_chosen.
    {
      apply dep_psh_fiber_terminal.
    }
    use iso_to_Terminal.
    {
      apply dep_psh_fiber_terminal.
    }
    use make_z_iso.
    - exact (unit_dep_psh_subst s).
    - exact (unit_dep_psh_subst_inv s).
    - split.
      + abstract
          (use dep_psh_nat_trans_eq ;
           intros x xx a ;
           apply isapropunit).
      + abstract
          (use dep_psh_nat_trans_eq ;
           intros x xx a ;
           apply isapropunit).
  Defined.

  Definition dep_psh_unit_z_iso
             (Γ : C^op ⟶ HSET)
    : is_z_isomorphism (C := PreShv C) (total_psh_pr (unit_dep_psh Γ)).
  Proof.
    use make_is_z_isomorphism.
    - use make_nat_trans.
      + exact (λ x xx, xx ,, tt).
      + abstract
          (intros x y f ; cbn ;
           apply idpath).
    - abstract
        (split ;
         (use nat_trans_eq ; [ apply homset_property | ]) ;
         intro x ;
         use funextsec ;
         intros xx ;
         [ | apply idpath ] ;
         induction xx as [ xx [ ] ] ;
         apply idpath).
  Defined.

  (** * 3. Fiberwise binary products *)
  Definition prod_dep_psh
             {Γ : C^op ⟶ HSET}
             (A B : dep_psh Γ)
    : dep_psh Γ.
  Proof.
    use make_dep_psh.
    - exact (λ x xx, A x xx × B x xx)%set.
    - exact (λ x y xx yy s p ab, #d A s p (pr1 ab) ,, #d B s p (pr2 ab)).
    - abstract
        (intros x xx p a ;
         use pathsdirprod ;
         apply dep_psh_mor_id).
    - abstract
        (intros x y z xx yy zz s₁ s₂ p q r a ;
         use pathsdirprod ;
         apply dep_psh_mor_comp).
  Defined.

  Definition prod_dep_psh_pr1
             {Γ : C^op ⟶ HSET}
             (A B : dep_psh Γ)
    : dep_psh_nat_trans
        (prod_dep_psh A B)
        A
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx ab, pr1 ab).
    - abstract
        (intro ; intros ; cbn ;
         apply dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition prod_dep_psh_pr2
             {Γ : C^op ⟶ HSET}
             (A B : dep_psh Γ)
    : dep_psh_nat_trans
        (prod_dep_psh A B)
        B
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx ab, pr2 ab).
    - abstract
        (intro ; intros ; cbn ;
         apply dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition prod_dep_psh_pair
             {Γ : C^op ⟶ HSET}
             {Z A B : dep_psh Γ}
             (τ₁ : dep_psh_nat_trans Z A (nat_trans_id _))
             (τ₂ : dep_psh_nat_trans Z B (nat_trans_id _))
    : dep_psh_nat_trans Z (prod_dep_psh A B) (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx z, τ₁ x xx z ,, τ₂ x xx z).
    - abstract
        (intros x y xx yy f p q z ; cbn ;
         use (pathsdirprod (dep_psh_nat_trans_ax τ₁ f p q z)) ;
         exact (dep_psh_nat_trans_ax τ₂ f p q z)).
  Defined.

  Definition prod_dep_psh_subst
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
             (A B : dep_psh Γ₂)
    : dep_psh_nat_trans
        (dep_psh_subst s (prod_dep_psh A B))
        (prod_dep_psh (dep_psh_subst s A) (dep_psh_subst s B))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx ab, ab).
    - abstract
        (cbn ;
         intros ;
         apply pathsdirprod ;
         apply dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition prod_dep_psh_subst_inv
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
             (A B : dep_psh Γ₂)
    : dep_psh_nat_trans
        (prod_dep_psh (dep_psh_subst s A) (dep_psh_subst s B))
        (dep_psh_subst s (prod_dep_psh A B))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx ab, ab).
    - abstract
        (cbn ;
         intros ;
         apply pathsdirprod ;
         apply dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition dep_psh_fiber_binproducts
             (Γ : C^op ⟶ HSET)
    : BinProducts ((disp_cat_dep_psh C) [{ Γ }]).
  Proof.
    intros A B.
    use make_BinProduct.
    - exact (prod_dep_psh A B).
    - exact (prod_dep_psh_pr1 A B).
    - exact (prod_dep_psh_pr2 A B).
    - intros Z τ₁ τ₂.
      use make_iscontr.
      + simple refine (_ ,, _ ,, _).
        * exact (prod_dep_psh_pair τ₁ τ₂).
        * abstract
            (use dep_psh_nat_trans_eq ;
             intros x xx a ;
             exact (dep_psh_fiber_comp _ _ _ _)).
        * abstract
            (use dep_psh_nat_trans_eq ;
             intros x xx a ;
             exact (dep_psh_fiber_comp _ _ _ _)).
      + abstract
          (intros τ ;
           use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           use dep_psh_nat_trans_eq ;
           intros x xx a ;
           use pathsdirprod ;
           [ refine (!_ @ maponpaths (λ (z : dep_psh_nat_trans _ _ _), z x xx a) (pr12 τ)) ;
             refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
             apply idpath
           | refine (!_ @ maponpaths (λ (z : dep_psh_nat_trans _ _ _), z x xx a) (pr22 τ)) ;
             refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
             apply idpath ]).
  Defined.

  Definition dep_psh_preserves_binproduct
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : preserves_binproduct
        (fiber_functor_from_cleaving
           (disp_cat_dep_psh C)
           (cleaving_disp_cat_dep_psh C)
           s).
  Proof.
    use preserves_binproduct_if_preserves_chosen.
    {
      apply dep_psh_fiber_binproducts.
    }
    intros A B.
    use (isBinProduct_z_iso (isBinProduct_BinProduct _ (dep_psh_fiber_binproducts Γ₁ _ _))).
    - use make_z_iso.
      + exact (prod_dep_psh_subst s A B).
      + exact (prod_dep_psh_subst_inv s A B).
      + abstract
          (split ;
           use dep_psh_nat_trans_eq ;
           intros x xx a ;
           refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
           cbn ;
           apply idpath).
    - abstract
        (use dep_psh_nat_trans_eq ;
         intros x xx a ;
         refine (dep_psh_fiber_functor_from_cleaving _ s _ _ @ _) ;
         refine (_ @ !(dep_psh_fiber_comp _ _ _ _)) ;
         apply idpath).
    - abstract
        (use dep_psh_nat_trans_eq ;
         intros x xx a ;
         refine (dep_psh_fiber_functor_from_cleaving _ s _ _ @ _) ;
         refine (_ @ !(dep_psh_fiber_comp _ _ _ _)) ;
         apply idpath).
  Defined.

  (** * 4. Fiberwise binary coproducts *)
  Definition coprod_dep_psh
             {Γ : C^op ⟶ HSET}
             (A B : dep_psh Γ)
    : dep_psh Γ.
  Proof.
    use make_dep_psh.
    - exact (λ x xx, setcoprod (A x xx) (B x xx))%set.
    - intros x y xx yy s p ab.
      induction ab as [ a | b ].
      + exact (inl (#d A s p a)).
      + exact (inr (#d B s p b)).
    - abstract
        (intros x xx p ab ;
         induction ab ;
         cbn ;
         apply maponpaths ;
         apply dep_psh_mor_id).
    - abstract
        (intros x y z xx yy zz s₁ s₂ p q r ab ;
         induction ab ;
         cbn ;
         apply maponpaths ;
         apply dep_psh_mor_comp).
  Defined.

  Definition coprod_dep_psh_inl
             {Γ : C^op ⟶ HSET}
             (A B : dep_psh Γ)
    : dep_psh_nat_trans
        A
        (coprod_dep_psh A B)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx a, inl a).
    - abstract
        (intro ; intros ; cbn ;
         apply maponpaths ;
         apply dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition coprod_dep_psh_inr
             {Γ : C^op ⟶ HSET}
             (A B : dep_psh Γ)
    : dep_psh_nat_trans
        B
        (coprod_dep_psh A B)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx a, inr a).
    - abstract
        (intro ; intros ; cbn ;
         apply maponpaths ;
         apply dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition coprod_dep_psh_copair
             {Γ : C^op ⟶ HSET}
             {Z A B : dep_psh Γ}
             (τ₁ : dep_psh_nat_trans A Z (nat_trans_id _))
             (τ₂ : dep_psh_nat_trans B Z (nat_trans_id _))
    : dep_psh_nat_trans
        (coprod_dep_psh A B)
        Z
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - intros x xx ab.
      induction ab as [ a | b ].
      + exact (τ₁ x xx a).
      + exact (τ₂ x xx b).
    - abstract
        (intros x y xx yy f p q ab ;
         induction ab as [ a | b ] ;
         [ apply (dep_psh_nat_trans_ax τ₁) | ] ;
      apply (dep_psh_nat_trans_ax τ₂)).
  Defined.

  Definition coprod_dep_psh_subst
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
             (A B : dep_psh Γ₂)
    : dep_psh_nat_trans
        (dep_psh_subst s (coprod_dep_psh A B))
        (coprod_dep_psh (dep_psh_subst s A) (dep_psh_subst s B))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx ab, ab).
    - abstract
        (cbn ;
         intros x y xx yy f p q ab ;
         induction ab ;
         cbn ;
         apply maponpaths ;
         apply dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition coprod_dep_psh_subst_inv
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
             (A B : dep_psh Γ₂)
    : dep_psh_nat_trans
        (coprod_dep_psh (dep_psh_subst s A) (dep_psh_subst s B))
        (dep_psh_subst s (coprod_dep_psh A B))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx ab, ab).
    - abstract
        (cbn ;
         intros x y xx yy f p q ab ;
         induction ab ;
         cbn ;
         apply maponpaths ;
         apply dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition dep_psh_fiber_bincoproducts
             (Γ : C^op ⟶ HSET)
    : BinCoproducts ((disp_cat_dep_psh C) [{ Γ }]).
  Proof.
    intros A B.
    use make_BinCoproduct.
    - exact (coprod_dep_psh A B).
    - exact (coprod_dep_psh_inl A B).
    - exact (coprod_dep_psh_inr A B).
    - intros Z τ₁ τ₂.
      use make_iscontr.
      + simple refine (_ ,, _ ,, _).
        * exact (coprod_dep_psh_copair τ₁ τ₂).
        * abstract
            (use dep_psh_nat_trans_eq ;
             intros x xx a ;
             exact (dep_psh_fiber_comp _ _ _ _)).
        * abstract
            (use dep_psh_nat_trans_eq ;
             intros x xx a ;
             exact (dep_psh_fiber_comp _ _ _ _)).
      + abstract
          (intros τ ;
           use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
           use dep_psh_nat_trans_eq ;
           intros x xx ab ;
           induction ab as [ a | b ] ;
           [ refine (!_ @ maponpaths (λ (z : dep_psh_nat_trans _ _ _), z x xx a) (pr12 τ)) ;
             refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
             apply idpath
           | refine (!_ @ maponpaths (λ (z : dep_psh_nat_trans _ _ _), z x xx b) (pr22 τ)) ;
             refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
             apply idpath ]).
  Defined.

  Definition dep_psh_preserves_bincoproduct
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : preserves_bincoproduct
        (fiber_functor_from_cleaving
           (disp_cat_dep_psh C)
           (cleaving_disp_cat_dep_psh C)
           s).
  Proof.
    use preserves_bincoproduct_if_preserves_chosen.
    {
      apply dep_psh_fiber_bincoproducts.
    }
    intros A B.
    use (isBinCoproduct_z_iso
           (isBinCoproduct_BinCoproduct _ (dep_psh_fiber_bincoproducts Γ₁ _ _))).
    - use make_z_iso.
      + exact (coprod_dep_psh_subst s A B).
      + exact (coprod_dep_psh_subst_inv s A B).
      + abstract
          (split ;
           use dep_psh_nat_trans_eq ;
           intros x xx a ;
           refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
           cbn ;
           apply idpath).
    - abstract
        (use dep_psh_nat_trans_eq ;
         intros x xx a ;
         refine (dep_psh_fiber_functor_from_cleaving _ s _ _ @ _) ;
         refine (_ @ !(dep_psh_fiber_comp _ _ _ _)) ;
         apply idpath).
    - abstract
        (use dep_psh_nat_trans_eq ;
         intros x xx a ;
         refine (dep_psh_fiber_functor_from_cleaving _ s _ _ @ _) ;
         refine (_ @ !(dep_psh_fiber_comp _ _ _ _)) ;
         apply idpath).
  Defined.

  (** * 5. Fiberwise equalizers *)
  Definition equalizer_dep_psh
             {Γ : C^op ⟶ HSET}
             {A B : dep_psh Γ}
             (τ₁ τ₂ : dep_psh_nat_trans A B (nat_trans_id _))
    : dep_psh Γ.
  Proof.
    use make_dep_psh.
    - exact (λ x xx, ∑ (a : A x xx), hProp_to_hSet (τ₁ x xx a = τ₂ x xx a)%logic)%set.
    - intros x y xx yy s p aq.
      simple refine (_ ,, _).
      + exact (#d A s p (pr1 aq)).
      + abstract
          (refine (dep_psh_nat_trans_ax τ₁ s p p _ @ _) ;
           refine (_ @ !(dep_psh_nat_trans_ax τ₂ s p p _)) ;
           apply maponpaths ;
           exact (pr2 aq)).
    - abstract
        (intros x xx p a ;
         use subtypePath ; [ intro ; apply setproperty | ] ;
         apply dep_psh_mor_id).
    - abstract
        (intros x y z xx yy zz s₁ s₂ p q r a ;
         use subtypePath ; [ intro ; apply setproperty | ] ;
         apply dep_psh_mor_comp).
  Defined.

  Definition equalizer_dep_psh_arrow
             {Γ : C^op ⟶ HSET}
             {A B : dep_psh Γ}
             (τ₁ τ₂ : dep_psh_nat_trans A B (nat_trans_id _))
    : dep_psh_nat_trans
        (equalizer_dep_psh τ₁ τ₂)
        A
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx ap, pr1 ap).
    - abstract
        (intros x y xx yy f p q ap ; cbn ;
         apply dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition equalizer_dep_psh_in
             {Γ : C^op ⟶ HSET}
             {Z A B : dep_psh Γ}
             {τ₁ τ₂ : dep_psh_nat_trans A B (nat_trans_id _)}
             (θ : dep_psh_nat_trans Z A (nat_trans_id _))
             (q : ∏ (x : C)
                    (xx : Γ x : hSet)
                    (z : Z x xx),
                  τ₁ x xx (θ x xx z) = τ₂ x xx (θ x xx z))
    : dep_psh_nat_trans
        Z
        (equalizer_dep_psh τ₁ τ₂)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx z, θ x xx z ,, q x xx z).
    - abstract
        (intros x y xx yy f r₁ r₂ z ; cbn ;
         use subtypePath ; [ intro ; apply setproperty | ] ;
         cbn ;
         apply (dep_psh_nat_trans_ax θ)).
  Defined.

  Definition equalizer_dep_psh_subst
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
             {A B : dep_psh Γ₂}
             (τ₁ τ₂ : dep_psh_nat_trans A B (nat_trans_id _))
    : dep_psh_nat_trans
        (dep_psh_subst s (equalizer_dep_psh τ₁ τ₂))
        (equalizer_dep_psh
           (# (fiber_functor_from_cleaving _ (cleaving_disp_cat_dep_psh C) s) τ₁)
           (# (fiber_functor_from_cleaving _ (cleaving_disp_cat_dep_psh C) s) τ₂))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - refine (λ x xx ap, pr1 ap ,, _).
      abstract
        (refine (dep_psh_fiber_functor_from_cleaving _ s _ _ @ _) ;
         refine (_ @ !(dep_psh_fiber_functor_from_cleaving _ s _ _)) ;
         cbn ;
         exact (pr2 ap)).
    - abstract
        (intros x y xx yy f p q ap ;
         use subtypePath ; [ intro ; apply setproperty | ] ;
         cbn ;
         apply dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition equalizer_dep_psh_subst_inv
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
             {A B : dep_psh Γ₂}
             (τ₁ τ₂ : dep_psh_nat_trans A B (nat_trans_id _))
    : dep_psh_nat_trans
        (equalizer_dep_psh
           (# (fiber_functor_from_cleaving _ (cleaving_disp_cat_dep_psh C) s) τ₁)
           (# (fiber_functor_from_cleaving _ (cleaving_disp_cat_dep_psh C) s) τ₂))
        (dep_psh_subst s (equalizer_dep_psh τ₁ τ₂))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - refine (λ x xx ap, pr1 ap ,, _).
      abstract
        (refine (!(dep_psh_fiber_functor_from_cleaving _ s _ _) @ _) ;
         refine (_ @ dep_psh_fiber_functor_from_cleaving _ s _ _) ;
         cbn ;
         exact (pr2 ap)).
    - abstract
        (intros x y xx yy f p q ap ;
         use subtypePath ; [ intro ; apply setproperty | ] ;
         cbn ;
         apply dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Proposition dep_psh_fiber_equalizers_eq
              {Γ : C^op ⟶ HSET}
              {A B Z : dep_psh Γ}
              (τ₁ τ₂ : dep_psh_nat_trans A B (nat_trans_id _))
              (θ : dep_psh_nat_trans Z A (nat_trans_id _))
              (p : compose
                     (C := (disp_cat_dep_psh C) [{ Γ }])
                     θ τ₁
                   =
                   compose
                     (C := (disp_cat_dep_psh C) [{ Γ }])
                     θ τ₂)
              (x : C)
              (xx : (Γ x : hSet))
              (z : Z x xx)
    : τ₁ x xx (θ x xx z) = τ₂ x xx (θ x xx z).
  Proof.
    refine (!(dep_psh_fiber_comp _ _ _ _) @ _ @ dep_psh_fiber_comp _ _ _ _).
    exact (maponpaths (λ (ζ : dep_psh_nat_trans _ _ _), ζ x xx z) p).
  Qed.

  Definition dep_psh_fiber_equalizers
             (Γ : C^op ⟶ HSET)
    : Equalizers ((disp_cat_dep_psh C) [{ Γ }]).
  Proof.
    intros A B τ₁ τ₂.
    use make_Equalizer.
    - exact (equalizer_dep_psh τ₁ τ₂).
    - exact (equalizer_dep_psh_arrow τ₁ τ₂).
    - abstract
        (use dep_psh_nat_trans_eq ;
         intros x xx a ;
         refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
         refine (_ @ !(dep_psh_fiber_comp _ _ _ _)) ;
         exact (pr2 a)).
    - intros Z θ p.
      pose (q := dep_psh_fiber_equalizers_eq τ₁ τ₂ θ p).
      use make_iscontr.
      + simple refine (_ ,, _).
        * exact (equalizer_dep_psh_in θ q).
        * abstract
            (use dep_psh_nat_trans_eq ;
             intros x xx a ;
             exact (dep_psh_fiber_comp _ _ _ _)).
      + abstract
          (intros τ ;
           use subtypePath ; [ intro ; apply homset_property | ] ;
           use dep_psh_nat_trans_eq ;
           intros x xx a ;
           use subtypePath ; [ intro ; apply setproperty | ] ;
           refine (!_ @ maponpaths (λ (z : dep_psh_nat_trans _ _ _), z x xx a) (pr2 τ)) ;
           refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
           apply idpath).
  Defined.

  Definition dep_psh_preserves_equalizer
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
    : preserves_equalizer
        (fiber_functor_from_cleaving
           (disp_cat_dep_psh C)
           (cleaving_disp_cat_dep_psh C)
           s).
  Proof.
    use preserves_equalizer_if_preserves_chosen.
    {
      apply dep_psh_fiber_equalizers.
    }
    intros A B τ₁ τ₂ p.
    use (isEqualizer_z_iso (isEqualizer_Equalizer (dep_psh_fiber_equalizers Γ₁ _ _ _ _))).
    - use make_z_iso.
      + exact (equalizer_dep_psh_subst s τ₁ τ₂).
      + exact (equalizer_dep_psh_subst_inv s τ₁ τ₂).
      + abstract
          (split ;
           use dep_psh_nat_trans_eq ;
           intros x xx a ;
           refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
           (use subtypePath ; [ intro ; apply setproperty | ]) ;
           cbn ;
           apply idpath).
    - abstract
        (use dep_psh_nat_trans_eq ;
         intros x xx a ;
         refine (dep_psh_fiber_functor_from_cleaving _ s _ _ @ _) ;
         refine (_ @ !(dep_psh_fiber_comp _ _ _ _)) ;
         apply idpath).
  Defined.

  (** * 6. Constant dependent presheaves *)
  Definition constant_dep_psh
             (Γ : C^op ⟶ HSET)
             (A : hSet)
    : dep_psh Γ.
  Proof.
    use make_dep_psh.
    - exact (λ _ _, A).
    - exact (λ x y xx yy s p a, a).
    - abstract
        (intros ; apply idpath).
    - abstract
        (intros ; apply idpath).
  Defined.

  Definition constant_dep_psh_el
             {Γ : C^op ⟶ HSET}
             (A : dep_psh Γ)
             {B : hSet}
             (b : B)
    : dep_psh_nat_trans A (constant_dep_psh Γ B) (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ _ _ _, b).
    - abstract
        (intro ; intros ; cbn ;
         apply idpath).
  Defined.

  (** * 7. Democracy of the presheaf model *)
  Definition constant_dep_psh_map
             {Γ : C^op ⟶ HSET}
             {A B : hSet}
             (f : A → B)
    : dep_psh_nat_trans
        (constant_dep_psh Γ A)
        (constant_dep_psh Γ B)
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx a, f a).
    - abstract
        (intro ; intros ; cbn ;
         apply idpath).
  Defined.

  Definition psh_to_dep_psh
             (Γ : C^op ⟶ HSET)
    : dep_psh (constant_functor C^op HSET unitHSET).
  Proof.
    use make_dep_psh.
    - exact (λ x _, (Γ x : hSet)).
    - exact (λ x y _ _ f p a, #Γ f a).
    - abstract
        (intros x ? ? a ; cbn ;
         exact (eqtohomot (functor_id Γ _) a)).
    - abstract
        (intros x y z ? ? ? s₁ s₂ ? ? ? a ;
         exact (eqtohomot (functor_comp Γ _ _) a)).
  Defined.

  Definition psh_to_dep_psh_z_iso_mor
             (Γ : C^op ⟶ HSET)
    : Γ ⟹ total_psh (psh_to_dep_psh Γ).
  Proof.
    use make_nat_trans.
    - exact (λ x xx, tt ,, xx).
    - abstract
        (intros x y f ;
         apply idpath).
  Defined.

  Definition psh_to_dep_psh_z_iso_inv
             (Γ : C^op ⟶ HSET)
    : total_psh (psh_to_dep_psh Γ) ⟹ Γ.
  Proof.
    use make_nat_trans.
    - exact (λ x xx, pr2 xx).
    - abstract
        (intros x y f ;
         apply idpath).
  Defined.

  Definition psh_to_dep_psh_z_iso
             (Γ : C^op ⟶ HSET)
    : z_iso (C := PreShv C) Γ (total_psh (psh_to_dep_psh Γ)).
  Proof.
    use make_z_iso.
    - exact (psh_to_dep_psh_z_iso_mor Γ).
    - exact (psh_to_dep_psh_z_iso_inv Γ).
    - abstract
        (split ;
         (use nat_trans_eq ; [ apply homset_property | ]) ;
         intros ; cbn ; [ apply idpath | ] ;
         use funextsec ;
         intro xx ;
         induction xx as [ [ ] xx ] ;
         cbn ;
         apply idpath).
  Defined.
End ExamplesDepPsh.

(** * 8. Statements for fiberwise limits and colimits *)
Definition dep_psh_fiberwise_terminal
           (C : category)
  : fiberwise_terminal (cleaving_disp_cat_dep_psh C).
Proof.
  split.
  - exact dep_psh_fiber_terminal.
  - intros Γ₁ Γ₂ s.
    exact (dep_psh_preserves_terminal s).
Defined.

Definition dep_psh_fiberwise_initial
           (C : category)
  : fiberwise_initial (cleaving_disp_cat_dep_psh C).
Proof.
  split.
  - exact dep_psh_fiber_initial.
  - intros Γ₁ Γ₂ s.
    exact (dep_psh_preserves_initial s).
Defined.

Definition dep_psh_fiberwise_binproducts
           (C : category)
  : fiberwise_binproducts (cleaving_disp_cat_dep_psh C).
Proof.
  split.
  - exact dep_psh_fiber_binproducts.
  - intros Γ₁ Γ₂ s.
    exact (dep_psh_preserves_binproduct s).
Defined.

Definition dep_psh_fiberwise_bincoproducts
           (C : category)
  : fiberwise_bincoproducts (cleaving_disp_cat_dep_psh C).
Proof.
  split.
  - exact dep_psh_fiber_bincoproducts.
  - intros Γ₁ Γ₂ s.
    exact (dep_psh_preserves_bincoproduct s).
Defined.

Definition dep_psh_fiberwise_equalizers
           (C : category)
  : fiberwise_equalizers (cleaving_disp_cat_dep_psh C).
Proof.
  split.
  - exact dep_psh_fiber_equalizers.
  - intros Γ₁ Γ₂ s.
    exact (dep_psh_preserves_equalizer s).
Defined.
