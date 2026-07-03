(**

 Stability of ∏-types for presheaves

 We show that ∏-types in the presheaf model are preserved by substitution. To do
 so, we show the usual Beck-Chevalley condition for right adjoints. To prove the
 Beck-Chevalley condition, we define an inverse for the canonical morphism and we
 prove that it is indeed an inverse. For that purpose, we give concrete condition
 of the Beck-Chevalley morphism for which we prove various calculational lemmas.

 Content
 1. Calculational lemmas
 2. The inverse of the Beck-Chevalley morphism
 3. Calculation of the Beck-Chevalley morphism
 4. Stability under substitution

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Coreflections.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.SigmaTypes.
Require Import UniMath.CategoryTheory.Presheaves.PiTypes.

Local Open Scope cat.

Section PiTypesStable.
  Context {C : category}.

  (** * 1. Calculational lemmas *)
  Proposition dep_prod_psh_right_adj_mor
              {Γ : C^op ⟶ HSET}
              {A : dep_psh Γ}
              {B₁ B₂ : dep_psh (total_psh A)}
              (θ : dep_psh_nat_trans B₁ B₂ (nat_trans_id _))
              {x y : C}
              {xx : (Γ x : hSet)}
              (φ : dep_pi_psh_function A B₁ x xx)
              {f : y --> x}
              (a : A y (# Γ f xx))
    : ((#(right_adjoint (dependent_product_dep_psh A)) θ : dep_psh_nat_trans _ _ _)
         x xx φ : dep_pi_psh_function _ _ _ _) y f a
      =
      θ _ _ (φ _ _ _).
  Proof.
    cbn -[fiber_category].
    rewrite dep_psh_fiber_comp.
    cbn.
    apply maponpaths.
    rewrite dep_psh_mor_comp'.
    etrans.
    {
      apply maponpaths.
      refine (dep_pi_psh_function_on_fun_eq _ _ _ _ _ _).
      apply id_left.
    }
    rewrite dep_psh_mor_comp'.
    etrans.
    {
      apply maponpaths.
      refine (dep_pi_psh_function_on_pt_eq _ _ _ _ _ _).
      do 2 refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
      apply (dep_psh_mor_id' A).
      rewrite !id_left.
      apply idpath.
    }
    rewrite dep_psh_mor_comp'.
    use dep_psh_mor_id'.
    rewrite !id_left.
    apply idpath.
  Qed.

  Proposition dep_prod_psh_counit_eq
              {Γ : C^op ⟶ HSET}
              {A : dep_psh Γ}
              {B : dep_psh (total_psh A)}
              {x : C}
              (xx : dep_psh_total_space A x)
              (φ : dep_pi_psh_function A B x (pr1 xx))
    : (counit_from_left_adjoint
         (dependent_product_dep_psh A) B : dep_psh_nat_trans _ _ _)
        x xx φ
      =
      #d B (identity _)
           (pi_dep_psh_eval_eq _ xx)
           (φ x (identity _) (#d A (identity _) (idpath _) (pr2 xx))).
  Proof.
    apply idpath.
  Qed.

  Proposition comm_nat_z_iso_inv_dep_psh_eq_path
              {Γ₁ Γ₂ Γ₃ Γ₄ : C^op ⟶ HSET}
              {τ₁ : Γ₃ ⟹ Γ₄}
              {τ₂ : Γ₂ ⟹ Γ₄}
              {τ₃ : Γ₁ ⟹ Γ₂}
              {τ₄ : Γ₁ ⟹ Γ₃}
              (p : nat_trans_comp _ _ _ τ₄ τ₁ = nat_trans_comp _ _ _ τ₃ τ₂)
              (A : dep_psh Γ₄)
              {x : C}
              (xx : (Γ₁ x : hSet))
    : #Γ₄ (identity x) (τ₂ x (τ₃ x xx)) = τ₁ x (τ₄ x xx).
  Proof.
    refine (eqtohomot (functor_id Γ₄ _) _  @ _).
    cbn.
    exact (!(eqtohomot (nat_trans_eq_pointwise p x) xx)).
  Qed.

  Proposition comm_nat_z_iso_inv_dep_psh_eq
              {Γ₁ Γ₂ Γ₃ Γ₄ : C^op ⟶ HSET}
              {τ₁ : Γ₃ ⟹ Γ₄}
              {τ₂ : Γ₂ ⟹ Γ₄}
              {τ₃ : Γ₁ ⟹ Γ₂}
              {τ₄ : Γ₁ ⟹ Γ₃}
              (p : nat_trans_comp _ _ _ τ₄ τ₁ = nat_trans_comp _ _ _ τ₃ τ₂)
              (A : dep_psh Γ₄)
              {x : C}
              (xx : (Γ₁ x : hSet))
              (a : A x (τ₂ x (τ₃ x xx)))
    : (comm_nat_z_iso_inv (cleaving_disp_cat_dep_psh C) _ _ _ _ p A : dep_psh_nat_trans _ _ _)
        x xx a
      =
      #d A (identity _) (comm_nat_z_iso_inv_dep_psh_eq_path p A xx) a.
  Proof.
    rewrite (comm_nat_z_iso_inv_ob (cleaving_disp_cat_dep_psh C) _ _ _ _ p A).
    refine (dep_psh_fiber_comp _ _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply dep_psh_fiber_comp.
    }
    etrans.
    {
      apply dep_psh_fiber_functor_from_cleaving_comp_inv_eq.
    }
    etrans.
    {
      apply maponpaths.
      apply dep_psh_fiber_functor_from_cleaving_comp_eq.
    }
    etrans.
    {
      exact (dep_psh_fiber_functor_on_eq_eq (!p) A a).
    }
    apply (dep_psh_mor_path_eq A).
    apply idpath.
  Qed.

  (** * 2. The inverse of the Beck-Chevalley morphism *)
  Section Stability.
    Context {Γ₁ Γ₂ : C^op ⟶ HSET}
            (s : Γ₁ ⟹ Γ₂)
            (A : dep_psh Γ₂)
            (B : dep_psh (total_psh A)).

    Let sA : dep_psh Γ₁ := dep_psh_subst s A.
    Let sB : dep_psh (total_psh sA)
      := dep_psh_subst (total_psh_nat_trans s (dep_psh_subst_nat_trans s A)) B.

    Proposition dep_psh_pi_subst_fun_eq1
                {x y : C}
                (f : y --> x)
                (xx : (Γ₁ x : hSet))
      : # Γ₂ (identity y) (# Γ₂ f (s x xx)) = s y (# Γ₁ f xx).
    Proof.
      refine (eqtohomot (functor_id Γ₂ _) _ @ _).
      cbn.
      exact (!(eqtohomot (nat_trans_ax s _ _ f) xx)).
    Qed.

    Proposition dep_psh_pi_subst_fun_eq2
                {x y : C}
                (f : y --> x)
                (xx : (Γ₁ x : hSet))
                (a : A y (# Γ₂ f (s x xx)))
      : # (total_psh A)
          (identity _)
          (total_psh_nat_trans
             s
             (dep_psh_subst_nat_trans s A)
             y
             (#Γ₁ f xx,, #d A (identity y) (dep_psh_pi_subst_fun_eq1 f xx) a))
        =
        # Γ₂ f (s x xx),, a.
    Proof.
      use dep_psh_total_space_path.
      - cbn.
        refine (eqtohomot (functor_id Γ₂ _) _ @ _).
        exact (eqtohomot (nat_trans_ax s _ _ f) xx).
      - cbn.
        rewrite !dep_psh_mor_comp'.
        use dep_psh_mor_id'.
        rewrite !id_left.
        apply idpath.
    Qed.

    Definition dep_psh_pi_subst_fun_mor
               (x : C)
               (xx : (Γ₁ x : hSet))
               (φ : dep_pi_psh_function sA sB x xx)
               (y : C)
               (f : y --> x)
               (a : A y (#Γ₂ f (s x xx)))
      : B y (#Γ₂ f (s x xx) ,, a)
      := #d B (identity _)
              (dep_psh_pi_subst_fun_eq2 f xx a)
              (φ y f (#d A (identity _) (dep_psh_pi_subst_fun_eq1 f xx) a)).

    Arguments dep_psh_pi_subst_fun_mor /.

    Proposition dep_psh_pi_subst_fun_natural
                (x : C)
                (xx : (Γ₁ x : hSet))
                (φ : dep_pi_psh_function sA sB x xx)
      : is_natural_dep_pi_psh_function A B (dep_psh_pi_subst_fun_mor x xx φ).
    Proof.
      intros y₁ y₂ f₁ f₂ a.
      cbn.
      rewrite dep_psh_mor_comp'.
      pose (dep_pi_psh_function_natural' _ _ φ f₁ f₂)
        as p.
      simple refine (_ @ maponpaths (#d B (identity _) _) (p _ _) @ _).
      - cbn.
        rewrite dep_psh_mor_comp'.
        use dep_psh_mor_path_eq.
        rewrite id_left, id_right.
        apply idpath.
      - abstract
          (use dep_psh_total_space_path ;
          [ cbn ;
            refine (eqtohomot (functor_id Γ₂ _) _ @ _) ;
            exact (eqtohomot (nat_trans_ax s _ _ (f₁ · f₂)) xx)
          | cbn ;
            rewrite !dep_psh_mor_comp' ;
            use dep_psh_mor_path_eq ;
            rewrite !id_left, id_right ;
            apply idpath ]).
      - abstract
          (use dep_psh_total_space_path ;
           [ cbn ;
             exact (eqtohomot (!(functor_comp Γ₁ _ _)) xx)
           | cbn ;
             rewrite !dep_psh_mor_comp' ;
             use dep_psh_mor_path_eq ;
             rewrite id_left, !id_right ;
             apply idpath ]).
      - cbn.
        assert (#Γ₂ f₁ (#Γ₂ f₂ (s x xx))
                =
                s y₂ (#Γ₁ (f₁ · f₂) xx))
          as mid.
        {
          refine (eqtohomot (!(functor_comp Γ₂ _ _)) _ @ _).
          exact (!(eqtohomot (nat_trans_ax s _ _ (f₁ · f₂)) xx)).
        }
        etrans.
        {
          apply maponpaths.
          refine (dep_pi_psh_function_on_pt_eq _ _ φ _ _ _).
          refine (dep_psh_mor_comp' A (identity _) f₁ _ _ _ @ _).
          refine (dep_psh_mor_path_eq _ _ _ (id_right _) _).
          exact mid.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (dep_pi_psh_function_on_pt_eq _ _ φ _ _ _).
          refine (dep_psh_mor_comp' A f₁ (identity _) _ _ _ @ _).
          refine (dep_psh_mor_path_eq _ _ _ (id_left _) _).
          exact mid.
        }
        cbn.
        refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _ @ !(dep_psh_mor_comp' _ _ _ _ _ _)).
        use dep_psh_mor_path_eq.
        apply idpath.
    Qed.

    Definition dep_psh_pi_subst_fun
               (x : C)
               (xx : (Γ₁ x : hSet))
               (φ : dep_pi_psh_function sA sB x xx)
      : dep_pi_psh_function A B x (s x xx).
    Proof.
      use make_dep_pi_psh_function.
      - exact (dep_psh_pi_subst_fun_mor x xx φ).
      - exact (dep_psh_pi_subst_fun_natural x xx φ).
    Defined.

    Proposition dep_psh_pi_subst_laws
      : dep_psh_nat_trans_naturality
          (A := pi_dep_psh
                  (dep_psh_subst s A)
                  (dep_psh_subst (total_psh_nat_trans s (dep_psh_subst_nat_trans s A)) B))
          (B := dep_psh_subst s (pi_dep_psh A B))
          (s := nat_trans_id _)
          dep_psh_pi_subst_fun.
    Proof.
      intros x₁ x₂ xx₁ xx₂ f p q φ.
      use dep_pi_psh_function_eq.
      cbn.
      intros y g a.
      rewrite !dep_psh_mor_comp'.
      assert (#Γ₂ (identity y) (#Γ₂ g (s x₂ xx₂))
              =
              s y (#Γ₁ (g · f) xx₁))
        as mid.
      {
        refine (eqtohomot (functor_id Γ₂ _) _ @ _).
        refine (!(eqtohomot (nat_trans_ax s _ _ g) _) @ _).
        cbn.
        apply maponpaths.
        rewrite <- p.
        exact (!(eqtohomot (functor_comp Γ₁ _ _) _)).
      }
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_pt_eq _ _ φ _ _ _).
        refine (dep_psh_mor_comp' A (identity _) (identity _) _ _ _ @ _).
        refine (dep_psh_mor_path_eq _ _ _ (id_right _) _).
        exact mid.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_pt_eq _ _ φ _ _ _).
        refine (dep_psh_mor_comp' A (identity _) (identity _) _ _ _ @ _).
        refine (dep_psh_mor_path_eq _ _ _ (id_right _) _).
        exact mid.
      }
      cbn.
      refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _ @ !(dep_psh_mor_comp' _ _ _ _ _ _)).
      use dep_psh_mor_path_eq.
      apply idpath.
    Qed.

    Definition dep_psh_pi_subst
      : dep_psh_nat_trans
          (pi_dep_psh
             (dep_psh_subst s A)
             (dep_psh_subst
                (total_psh_nat_trans s (dep_psh_subst_nat_trans s A))
                B))
          (dep_psh_subst
             s
             (pi_dep_psh A B))
          (nat_trans_id _).
    Proof.
      use make_dep_psh_nat_trans.
      - exact dep_psh_pi_subst_fun.
      - exact dep_psh_pi_subst_laws.
    Defined.

    (** * 3. Calculation of the Beck-Chevalley morphism *)
    Context (p : nat_trans_comp
                   _ _ _
                   (total_psh_nat_trans s (dep_psh_subst_nat_trans s A))
                   (total_psh_pr A)
                 =
                 nat_trans_comp
                   _ _ _
                   (total_psh_pr (dep_psh_subst s A))
                   s).

    Let τ : dep_psh_nat_trans
              (dep_psh_subst s (pi_dep_psh A B))
              (pi_dep_psh
                 sA
                 (dep_psh_subst (total_psh_nat_trans s (dep_psh_subst_nat_trans s A)) B))
              (nat_trans_id _)
      := right_beck_chevalley_nat_trans
           (dependent_product_dep_psh A)
           (dependent_product_dep_psh sA)
           (comm_nat_z_iso_inv
              (cleaving_disp_cat_dep_psh C)
              (total_psh_pr A)
              s
              (total_psh_pr (dep_psh_subst s A))
              (total_psh_nat_trans s (dep_psh_subst_nat_trans s A))
              p)
           B.

    Proposition dep_psh_pi_right_beck_chevalley_nat_trans_eq1
                {x y : C}
                (xx : (Γ₁ x : hSet))
                (f : y --> x)
      : #Γ₂ (identity y) (s y (#Γ₁ f xx)) = #Γ₂ f (s x xx).
    Proof.
      refine (eqtohomot (functor_id Γ₂ _) _ @ _).
      cbn.
      exact (eqtohomot (nat_trans_ax s _ _ f) _).
    Qed.

    Let e₁ := @dep_psh_pi_right_beck_chevalley_nat_trans_eq1.

    Proposition dep_psh_pi_right_beck_chevalley_nat_trans_eq2
                {x y : C}
                (xx : (Γ₁ x : hSet))
                (f : y --> x)
                (a : A y (s y (#Γ₁ f xx)))
      : # (total_psh A)
          (identity y)
          (#Γ₂ f (s x xx) ,, #d A (identity y) (e₁ x y xx f) a)
        =
        total_psh_nat_trans
          s
          (dep_psh_subst_nat_trans s A)
          y
          (#Γ₁ f xx ,, a).
    Proof.
      use dep_psh_total_space_path.
      - cbn.
        refine (eqtohomot (functor_id Γ₂ _) _ @ _).
        exact (!(eqtohomot (nat_trans_ax s _ _ f) xx)).
      - cbn.
        rewrite !dep_psh_mor_comp'.
        use dep_psh_mor_id'.
        rewrite !id_left.
        apply idpath.
    Qed.

    Let e₂ := @dep_psh_pi_right_beck_chevalley_nat_trans_eq2.

    Proposition dep_psh_pi_right_beck_chevalley_nat_trans
                {x y : C}
                (xx : (Γ₁ x : hSet))
                (φ : dep_pi_psh_function A B x (s x xx))
                (f : y --> x)
                (a : A y (s y (#Γ₁ f xx)))
      : (τ x xx φ : dep_pi_psh_function _ _ _ _) y f a
        =
        #d B (identity _) (e₂ x y xx f a) (φ y f (#d A (identity _) (e₁ x y xx f) a)).
    Proof.
      cbn -[τ].
      unfold τ.
      rewrite right_beck_chevalley_nat_trans_ob.
      etrans.
      {
        refine (maponpaths (λ z, z y f a) _).
        rewrite !dep_psh_fiber_comp.
        apply idpath.
      }
      etrans.
      {
        exact (dep_prod_psh_right_adj_mor
                 (#(fiber_functor_from_cleaving
                      (disp_cat_dep_psh C)
                      (cleaving_disp_cat_dep_psh C)
                      (total_psh_nat_trans s (dep_psh_subst_nat_trans s A)))
                    (counit_from_left_adjoint (dependent_product_dep_psh A) B)) _ _).
      }
      rewrite (dep_psh_fiber_functor_from_cleaving
                 _
                 (total_psh_nat_trans s (dep_psh_subst_nat_trans s A))
                 (counit_from_left_adjoint (dependent_product_dep_psh A) B)).
      etrans.
      {
        apply dep_prod_psh_counit_eq.
      }
      rewrite (dep_prod_psh_right_adj_mor
                 (comm_nat_z_iso_inv
                    (cleaving_disp_cat_dep_psh C)
                    (total_psh_pr A)
                    s
                    (total_psh_pr (dep_psh_subst s A))
                    (total_psh_nat_trans s (dep_psh_subst_nat_trans s A)) p
                    (right_adjoint (dependent_product_dep_psh A) B))
                 ((unit_from_left_adjoint
                     (dependent_product_dep_psh sA)
                     (fiber_functor_from_cleaving
                        (disp_cat_dep_psh C)
                        (cleaving_disp_cat_dep_psh C) s
                        (right_adjoint (dependent_product_dep_psh A) B))
                    : dep_psh_nat_trans _ _ _) x xx φ)).
      rewrite (comm_nat_z_iso_inv_dep_psh_eq p).
      cbn.
      rewrite !dep_psh_mor_comp'.
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_fun_eq _ _ _ _ _ _).
        refine (assoc' _ _ _ @ _).
        refine (id_left _ @ _).
        apply id_left.
      }
      rewrite dep_psh_mor_comp'.
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_pt_eq _ _ _ _ _ _).
        do 3 refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
        use dep_psh_mor_path_eq.
        - apply identity.
        - apply e₁.
        - rewrite !id_left.
          apply idpath.
      }
      rewrite dep_psh_mor_comp'.
      use dep_psh_mor_path_eq.
      rewrite !id_left.
      apply idpath.
    Qed.

    (** * 4. Stability under substitution *)
    Proposition dep_psh_pi_subst_inv_laws
      : is_inverse_in_precat
          (C := fiber_category (disp_cat_dep_psh C) Γ₁)
          τ
          dep_psh_pi_subst.
    Proof.
      split.
      - use dep_psh_nat_trans_eq.
        intros x xx φ.
        refine (dep_psh_fiber_comp _ _ _ _ @ _).
        use dep_pi_psh_function_eq.
        intros y f a.
        cbn -[τ].
        etrans.
        {
          apply maponpaths.
          apply dep_psh_pi_right_beck_chevalley_nat_trans.
        }
        etrans.
        {
          do 2 apply maponpaths.
          refine (dep_pi_psh_function_on_pt_eq _ _ _ _ _ _).
          refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
          apply (dep_psh_mor_id' A).
          rewrite !id_left.
          apply idpath.
        }
        rewrite !dep_psh_mor_comp'.
        apply (dep_psh_mor_id' B).
        rewrite !id_left.
        apply idpath.
      - use dep_psh_nat_trans_eq.
        intros x xx φ.
        refine (dep_psh_fiber_comp _ _ _ _ @ _).
        use dep_pi_psh_function_eq.
        intros y f a.
        etrans.
        {
          apply dep_psh_pi_right_beck_chevalley_nat_trans.
        }
        cbn.
        etrans.
        {
          do 2 apply maponpaths.
          refine (dep_pi_psh_function_on_pt_eq _ _ φ _ _ _).
          refine (dep_psh_mor_comp' A _ _ _ _ _ @ _).
          apply (dep_psh_mor_id' A).
          rewrite !id_left.
          apply idpath.
        }
        cbn.
        rewrite !dep_psh_mor_comp'.
        apply (dep_psh_mor_id' B).
        rewrite !id_left.
        apply idpath.
    Qed.
  End Stability.
End PiTypesStable.
