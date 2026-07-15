(**

 ∏-types for presheaves

 In this file, we give the necessary constructions to show that the presheaf model
 supports ∏-types. The construction of these types amounts to proving that the category
 of presheaves is locally Cartesian closed. There are several ways to prove this
 statement, and we use a direct approach. Specifically, we directly construct the
 dependent product as a dependent presheaf. Such an approach is advantageous for certain
 concrete calculations.

 Content
 1. Elements of the ∏-type
 2. Some useful lemmas
 3. Action on morphisms
 4. Functoriality laws
 5. Evaluation
 6. λ-abstraction
 7. β and η equations
 8. The dependent product

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

Local Open Scope cat.

Section PiTypes.
  Context {C : category}.

  (** * 1. Elements of the ∏-type *)
  Section PiDepPsh.
    Context {Γ : C^op ⟶ HSET}
            (A : dep_psh Γ)
            (B : dep_psh (total_psh A)).

    Proposition dep_pi_psh_function_path
                {x y y' : C}
                (xx : (Γ x : hSet))
                (f₁ : y' --> y)
                (f₂ : y --> x)
                (a : A y (#Γ f₂ xx))
      : #(total_psh A) f₁ (#Γ f₂ xx ,, a)
        =
        #Γ (f₁ · f₂) xx ,, #d A f₁ (!(eqtohomot (functor_comp Γ f₂ f₁) xx)) a.
    Proof.
      use dep_psh_total_space_path.
      - exact (!(eqtohomot (functor_comp Γ f₂ f₁) xx)).
      - cbn.
        rewrite dep_psh_mor_comp'.
        apply dep_psh_mor_path_eq.
        apply id_left.
    Qed.

    Definition is_natural_dep_pi_psh_function
               {x : C}
               {xx : (Γ x : hSet)}
               (φ : ∏ (y : C)
                      (f : y --> x)
                      (a : A y (#Γ f xx)),
                    B y (#Γ f xx ,, a))
      : UU
      := ∏ (y y' : C)
           (f₁ : y' --> y)
           (f₂ : y --> x)
           (a : A y (#Γ f₂ xx)),
         #d B f₁ (dep_pi_psh_function_path xx f₁ f₂ a) (φ y f₂ a)
         =
         φ y' (f₁ · f₂) (#d A f₁ _ a).

    Proposition isaprop_is_natural_dep_pi_psh_function
                {x : C}
                {xx : (Γ x : hSet)}
                (φ : ∏ (y : C)
                       (f : y --> x)
                       (a : A y (#Γ f xx)),
                     B y (#Γ f xx ,, a))
      : isaprop (is_natural_dep_pi_psh_function φ).
    Proof.
      repeat (use impred ; intro).
      apply setproperty.
    Qed.

    Definition dep_pi_psh_function
               (x : C)
               (xx : (Γ x : hSet))
      : UU
      := ∑ (φ : ∏ (y : C)
                  (f : y --> x)
                  (a : A y (#Γ f xx)),
                B y (#Γ f xx ,, a)),
         is_natural_dep_pi_psh_function φ.

    Definition dep_pi_psh_function_hSet
               (x : C)
               (xx : (Γ x : hSet))
      : hSet.
    Proof.
      use make_hSet.
      - exact (dep_pi_psh_function x xx).
      - use isaset_total2.
        + repeat (use impred_isaset ; intro).
          apply setproperty.
        + intro.
          apply isasetaprop.
          repeat (use impred ; intro).
          apply setproperty.
    Defined.

    Definition make_dep_pi_psh_function
               (x : C)
               (xx : (Γ x : hSet))
               (φ : ∏ (y : C)
                      (f : y --> x)
                      (a : A y (#Γ f xx)),
                    B y (#Γ f xx ,, a))
               (H : is_natural_dep_pi_psh_function φ)
      : dep_pi_psh_function x xx
      := φ ,, H.

    Definition dep_pi_psh_function_pt
               {x : C}
               {xx : (Γ x : hSet)}
               (φ : dep_pi_psh_function x xx)
               (y : C)
               (f : y --> x)
               (a : A y (#Γ f xx))
      : B y (#Γ f xx ,, a)
      := pr1 φ y f a.

    Coercion dep_pi_psh_function_pt : dep_pi_psh_function >-> Funclass.

    Proposition dep_pi_psh_function_natural
                {x : C}
                {xx : (Γ x : hSet)}
                (φ : dep_pi_psh_function x xx)
                {y y' : C}
                (f₁ : y' --> y)
                (f₂ : y --> x)
                (a : A y (#Γ f₂ xx))
      : #d B f₁ (dep_pi_psh_function_path xx f₁ f₂ a) (φ y f₂ a)
        =
        φ y' (f₁ · f₂) (#d A f₁ _ a).
    Proof.
      exact (pr2 φ y y' f₁ f₂ a).
    Qed.

    (** * 2. Some useful lemmas *)
    Proposition dep_pi_psh_function_natural'
                {x : C}
                {xx : (Γ x : hSet)}
                (φ : dep_pi_psh_function x xx)
                {y y' : C}
                (f₁ : y' --> y)
                (f₂ : y --> x)
                (a : A y (#Γ f₂ xx))
                (p := !eqtohomot (functor_comp Γ f₂ f₁) xx)
                (q : #(total_psh A) f₁ (#Γ f₂ xx,, a) = #Γ (f₁ · f₂) xx ,, #d A f₁ p a)
      : #d B f₁ q (φ y f₂ a)
        =
        φ y' (f₁ · f₂) (#d A f₁ p a).
    Proof.
      refine (_ @ dep_pi_psh_function_natural φ f₁ f₂ a).
      apply dep_psh_mor_path_eq.
      apply idpath.
    Qed.

    Proposition dep_pi_psh_function_on_pt_eq_path
                {x : C}
                {xx : (Γ x : hSet)}
                (y : C)
                (f : y --> x)
                {a a' : A y (#Γ f xx)}
                (p : a = a')
      : #(total_psh A) (identity y) (#Γ f xx ,, a') = #Γ f xx ,, a.
    Proof.
      induction p ; cbn.
      use dep_psh_total_space_path.
      - cbn.
        exact (eqtohomot (functor_id Γ _) _).
      - cbn.
        rewrite dep_psh_mor_comp'.
        use dep_psh_mor_id'.
        rewrite id_left.
        apply idpath.
    Qed.

    Proposition dep_pi_psh_function_on_pt_eq
                {x : C}
                {xx : (Γ x : hSet)}
                (φ : dep_pi_psh_function x xx)
                (y : C)
                (f : y --> x)
                {a a' : A y (#Γ f xx)}
                (p : a = a')
      : φ y f a
        =
        #d B (identity _) (dep_pi_psh_function_on_pt_eq_path y f p) (φ y f a').
    Proof.
      induction p ; cbn.
      refine (!_).
      use dep_psh_mor_id'.
      apply idpath.
    Qed.

    Proposition dep_pi_psh_function_on_fun_eq_eq1
                {x : C}
                {xx : (Γ x : hSet)}
                {y : C}
                {f f' : y --> x}
                (p : f = f')
      : #Γ (identity y) (# Γ f xx) = #Γ f' xx.
    Proof.
      induction p ; cbn.
      exact (eqtohomot (functor_id Γ _) _).
    Qed.

    Proposition dep_pi_psh_function_on_fun_eq_eq2
                {x : C}
                {xx : (Γ x : hSet)}
                {y : C}
                {f f' : y --> x}
                (p : f = f')
                (a : A y (#Γ f xx))
      : #(total_psh A)
         (identity y)
         (#Γ f' xx ,, #d A (identity y) (dep_pi_psh_function_on_fun_eq_eq1 p) a)
        =
        #Γ f xx ,, a.
    Proof.
      induction p ; cbn.
      use dep_psh_total_space_path.
      - cbn.
        exact (eqtohomot (functor_id Γ _) _).
      - cbn.
        rewrite !dep_psh_mor_comp'.
        use dep_psh_mor_id'.
        rewrite !id_left.
        apply idpath.
    Qed.

    Proposition dep_pi_psh_function_on_fun_eq
                {x : C}
                {xx : (Γ x : hSet)}
                (φ : dep_pi_psh_function x xx)
                (y : C)
                {f f' : y --> x}
                (p : f = f')
                (a : A y (#Γ f xx))
      : φ y f a
        =
        #d B (identity _)
             (dep_pi_psh_function_on_fun_eq_eq2 p a)
             (φ y f' (#d A (identity _) (dep_pi_psh_function_on_fun_eq_eq1 p) a)).
    Proof.
      induction p.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_pt_eq _ _ _ _).
        apply (dep_psh_mor_id A).
      }
      rewrite dep_psh_mor_comp'.
      use dep_psh_mor_id'.
      rewrite id_left.
      apply idpath.
    Qed.

    Proposition dep_pi_psh_function_eq
                {x : C}
                {xx : (Γ x : hSet)}
                {φ₁ φ₂ : dep_pi_psh_function x xx}
                (p : ∏ (y : C) (f : y --> x) (a : A y (#Γ f xx)), φ₁ y f a = φ₂ y f a)
      : φ₁ = φ₂.
    Proof.
      use subtypePath.
      {
        intro.
        apply isaprop_is_natural_dep_pi_psh_function.
      }
      repeat (use funextsec ; intro).
      apply p.
    Qed.

    (** * 3. Action on morphisms *)
    Proposition dep_pi_psh_function_mor_eq1
                {x₁ x₂ y : C}
                {xx₁ : (Γ x₁ : hSet)}
                {xx₂ : (Γ x₂ : hSet)}
                (f : y --> x₂)
                (s : x₂ --> x₁)
                (p : #Γ s xx₁ = xx₂)
      : #Γ (identity y) (#Γ f xx₂) = # Γ (f · s) xx₁.
    Proof.
      refine (eqtohomot (functor_id Γ _) _ @ _).
      rewrite <- p.
      cbn.
      exact (eqtohomot (!(functor_comp Γ _ _)) _).
    Qed.

    Proposition dep_pi_psh_function_mor_eq2
                {x₁ x₂ y : C}
                {xx₁ : (Γ x₁ : hSet)}
                {xx₂ : (Γ x₂ : hSet)}
                (f : y --> x₂)
                (s : x₂ --> x₁)
                (p : #Γ s xx₁ = xx₂)
                (a : A y (#Γ f xx₂))
      : #(total_psh A)
         (identity y)
         (#Γ (f · s) xx₁ ,, #d A (identity y) (dep_pi_psh_function_mor_eq1 f s p) a)
        =
        #Γ f xx₂ ,, a.
    Proof.
      use dep_psh_total_space_path.
      - abstract
          (cbn ;
           refine (eqtohomot (functor_id Γ _) _ @ _) ;
           rewrite <- p ;
           cbn ;
           exact (eqtohomot (functor_comp Γ _ _) _)).
      - cbn.
        rewrite !dep_psh_mor_comp'.
        apply dep_psh_mor_id'.
        rewrite !id_left.
        apply idpath.
    Qed.

    Proposition dep_pi_psh_function_mor_naturality
                {x₁ x₂ : C}
                {xx₁ : (Γ x₁ : hSet)}
                {xx₂ : (Γ x₂ : hSet)}
                (s : x₂ --> x₁)
                (p : #Γ s xx₁ = xx₂)
                (φ : dep_pi_psh_function x₁ xx₁)
      : is_natural_dep_pi_psh_function
          (λ y f a,
            #d B (identity y)
                 (dep_pi_psh_function_mor_eq2 f s p a)
                 (φ y (f · s) (#d A (identity y) (dep_pi_psh_function_mor_eq1 f s p) a))).
    Proof.
      intros y y' f₁ f₂ a ; cbn.
      rewrite !dep_psh_mor_comp'.
      pose (p' := !(eqtohomot (functor_comp Γ (f₂ · s) f₁) xx₁)).
      pose (q := dep_pi_psh_function_mor_eq1 f₂ s p).
      assert (#(total_psh A) f₁ (#Γ (f₂ · s) xx₁ ,, #d A (identity _) q a)
              =
              #Γ (f₁ · (f₂ · s)) xx₁ ,, #d A f₁ p' (#d A (identity _) q a))
        as r.
      {
        cbn.
        use dep_psh_total_space_path.
        {
          cbn.
          exact (!(eqtohomot (functor_comp Γ _ _) _)).
        }
        cbn.
        rewrite dep_psh_mor_comp'.
        apply dep_psh_mor_path_eq.
        apply id_left.
      }
      assert (#Γ f₁ (#Γ f₂ xx₂) = #Γ (f₁ · (f₂ · s)) xx₁) as lem.
      {
        rewrite <- p.
        etrans.
        {
          apply maponpaths.
          exact (!(eqtohomot (functor_comp Γ _ _) _)).
        }
        exact (!(eqtohomot (functor_comp Γ _ _) _)).
      }
      assert (#(total_psh A)
               (identity y')
               (#Γ (f₁ · (f₂ · s)) xx₁
                ,,
                #d A f₁ (!(eqtohomot (functor_comp Γ (f₂ · s) f₁) xx₁)) (#d A (identity y) q a))
              =
              #Γ (f₁ · f₂) xx₂
              ,,
              #d A f₁ (! eqtohomot (functor_comp Γ f₂ f₁) xx₂) a)
        as mid.
      {
        cbn.
        use dep_psh_total_space_path.
        - cbn.
          refine (eqtohomot (functor_id Γ _) _ @ _).
          refine (_ @ !(eqtohomot (functor_comp Γ _ _) _)).
          refine (eqtohomot (functor_comp Γ _ _) _ @ _).
          cbn.
          apply maponpaths.
          refine (eqtohomot (functor_comp Γ _ _) _ @ _).
          cbn.
          apply maponpaths.
          exact p.
        - cbn.
          rewrite !dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          rewrite !id_left, id_right.
          apply idpath.
      }
      pose (dep_pi_psh_function_natural' φ f₁ (f₂ · s) (#d A (identity _) q a) r)
        as φnat.
      simple refine (_ @ maponpaths (#d B (identity _) mid) φnat @ _).
      - rewrite dep_psh_mor_comp'.
        use dep_psh_mor_path_eq.
        rewrite id_left, id_right.
        apply idpath.
      - rewrite (dep_pi_psh_function_on_fun_eq φ _ (assoc' f₁ f₂ s)).
        rewrite !dep_psh_mor_comp'.
        etrans.
        {
          apply maponpaths.
          refine (dep_pi_psh_function_on_pt_eq _ _ _ _).
          rewrite !dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          + exact f₁.
          + exact lem.
          + apply id_right.
        }
        rewrite dep_psh_mor_comp'.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (dep_pi_psh_function_on_pt_eq _ _ _ _).
          rewrite !dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          + exact f₁.
          + exact lem.
          + rewrite !id_left.
            apply idpath.
        }
        rewrite dep_psh_mor_comp'.
        use dep_psh_mor_path_eq.
        rewrite !id_left.
        apply idpath.
    Qed.

    Definition dep_pi_psh_function_mor
               {x₁ x₂ : C}
               {xx₁ : (Γ x₁ : hSet)}
               {xx₂ : (Γ x₂ : hSet)}
               (s : x₂ --> x₁)
               (p : #Γ s xx₁ = xx₂)
               (φ : dep_pi_psh_function x₁ xx₁)
      : dep_pi_psh_function x₂ xx₂.
    Proof.
      use make_dep_pi_psh_function.
      - exact (λ y f a,
               #d B (identity _)
                    (dep_pi_psh_function_mor_eq2 f s p a)
                    (φ y (f · s) (#d A (identity _) (dep_pi_psh_function_mor_eq1 f s p) a))).
      - exact (dep_pi_psh_function_mor_naturality s p φ).
    Defined.

    (** * 4. Functoriality laws *)
    Lemma pi_dep_psh_id_mor
          (x : C)
          (xx : (Γ x : hSet))
          (p : #Γ (identity x) xx = xx)
          (φ : dep_pi_psh_function x xx)
      : dep_pi_psh_function_mor (identity x) p φ = φ.
    Proof.
      use  dep_pi_psh_function_eq.
      intros y f a ; cbn.
      etrans.
      {
        apply maponpaths.
        exact (dep_pi_psh_function_on_fun_eq _ _ (id_right _) _).
      }
      rewrite dep_psh_mor_comp'.
      assert (#d A (identity y)
                   (dep_pi_psh_function_on_fun_eq_eq1 (id_right f))
                   (#d A (identity y) (dep_pi_psh_function_mor_eq1 f (identity x) p) a)
              =
              a)
        as lem.
      {
        rewrite !dep_psh_mor_comp'.
        apply dep_psh_mor_id'.
        rewrite id_right.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        exact (dep_pi_psh_function_on_pt_eq _ _ _ lem).
      }
      rewrite dep_psh_mor_comp'.
      use dep_psh_mor_id'.
      rewrite !id_left.
      apply idpath.
    Qed.

    Lemma pi_dep_psh_comp_mor
          (x₁ x₂ x₃ : C)
          (xx₁ : (Γ x₁ : hSet))
          (xx₂ : (Γ x₂ : hSet))
          (xx₃ : (Γ x₃ : hSet))
          (s₁ : x₂ --> x₁)
          (s₂ : x₃ --> x₂)
          (p : #Γ s₁ xx₁ = xx₂)
          (q : #Γ s₂ xx₂ = xx₃)
          (r : #Γ (s₂ · s₁) xx₁ = xx₃)
          (φ : dep_pi_psh_function x₁ xx₁)
      : dep_pi_psh_function_mor (s₂ · s₁) r φ
        =
        dep_pi_psh_function_mor s₂ q (dep_pi_psh_function_mor s₁ p φ).
    Proof.
      use  dep_pi_psh_function_eq.
      intros y f a ; cbn.
      etrans.
      {
        apply maponpaths.
        exact (dep_pi_psh_function_on_fun_eq _ _ (assoc _ _ _) _).
      }
      rewrite !dep_psh_mor_comp'.
      assert (#Γ (identity y) (#Γ f xx₃) = #Γ (f · s₂ · s₁) xx₁) as path.
      {
        refine (eqtohomot (functor_id Γ _) _ @ _).
        cbn.
        rewrite <- q.
        do 2 refine (_ @ !(eqtohomot (functor_comp Γ _ _) _)).
        cbn.
        do 2 apply maponpaths.
        exact (!p).
      }
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_pt_eq _ _ _ _).
        refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
        refine (dep_psh_mor_path_eq _ _ _ (id_left _) _).
        exact path.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (dep_pi_psh_function_on_pt_eq _ _ _ _).
        refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
        refine (dep_psh_mor_path_eq _ _ _ (id_left _) _).
        exact path.
      }
      rewrite !dep_psh_mor_comp'.
      use dep_psh_mor_path_eq.
      apply idpath.
    Qed.

    Definition pi_dep_psh
      : dep_psh Γ.
    Proof.
      use make_dep_psh.
      - exact (λ x xx, dep_pi_psh_function_hSet x xx).
      - exact (λ x₁ x₂ xx₁ xx₂ s p φ, dep_pi_psh_function_mor s p φ).
      - exact pi_dep_psh_id_mor.
      - exact pi_dep_psh_comp_mor.
    Defined.

    (** * 5. Evaluation *)
    Proposition pi_dep_psh_eval_eq
                {x : C}
                (xx : dep_psh_total_space A x)
      : #(total_psh A)
         (identity x)
         (#Γ (identity x) (pr1 xx)
          ,,
          #d A (identity x) (idpath _) (pr2 xx))
        =
        xx.
    Proof.
      use dep_psh_total_space_path.
      - cbn.
        refine (eqtohomot (functor_id Γ _) _ @ _).
        exact (eqtohomot (functor_id Γ _) _).
      - cbn.
        rewrite !dep_psh_mor_comp'.
        use dep_psh_mor_id'.
        rewrite !id_left.
        apply idpath.
    Qed.

    Proposition pi_dep_psh_eval_laws
      : dep_psh_nat_trans_naturality
          (A := dep_psh_subst (total_psh_pr A) pi_dep_psh)
          (B := B)
          (s := nat_trans_id _)
          (λ x xx (φ : dep_pi_psh_function x (pr1 xx)),
          #d B (identity x) (pi_dep_psh_eval_eq xx)
               (φ x (identity x) (#d A (identity x) (idpath _) (pr2 xx)))).
    Proof.
      intros x₁ x₂ xx₁ xx₂ f p q φ.
      cbn.
      rewrite !dep_psh_mor_comp'.
      refine (!_).
      pose (dep_pi_psh_function_natural' φ f (identity _)) as r.
      assert (# (total_psh A)
                (identity x₂)
                (#Γ (f · identity x₁) (pr1 xx₁)
                 ,,
                 #d A f (! eqtohomot (functor_comp Γ (identity x₁) f) (pr1 xx₁))
                      (#d A (identity x₁) (idpath (# Γ (identity x₁) (pr1 xx₁))) (pr2 xx₁)))
              =
              xx₂)
        as lem₁.
      {
        use dep_psh_total_space_path.
        - cbn.
          refine (eqtohomot (functor_id Γ _) _ @ _).
          refine (eqtohomot (functor_comp Γ _ _) _ @ _).
          refine (_ @ maponpaths pr1 p).
          cbn.
          apply maponpaths.
          exact (eqtohomot (functor_id Γ _) _).
        - cbn.
          rewrite !dep_psh_mor_comp'.
          refine (_ @ dep_psh_total_space_pr2_path _ p).
          cbn.
          rewrite !dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          rewrite !id_left, id_right.
          apply idpath.
      }
      assert (# (total_psh A) f
                (#Γ (identity x₁) (pr1 xx₁)
                 ,,
                 #d A (identity x₁) (idpath (# Γ (identity x₁) (pr1 xx₁))) (pr2 xx₁))
              =
              #Γ (f · identity x₁) (pr1 xx₁)
              ,,
              #d A f (!(eqtohomot (functor_comp Γ (identity x₁) f) (pr1 xx₁)))
                     (#d A (identity x₁) (idpath (# Γ (identity x₁) (pr1 xx₁))) (pr2 xx₁)))
        as lem₂.
      {
        use dep_psh_total_space_path.
        - exact (eqtohomot (!(functor_comp Γ _ _)) _).
        - cbn.
          rewrite !dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          rewrite !id_left, id_right.
          apply idpath.
      }
      simple refine (_ @ maponpaths (#d B (identity _) _) (r _ _) @ _).
      - rewrite dep_psh_mor_comp'.
        use dep_psh_mor_path_eq.
        rewrite id_left, id_right.
        apply idpath.
      - exact lem₁.
      - exact lem₂.
      - cbn.
        etrans.
        {
          apply maponpaths.
          apply (dep_pi_psh_function_on_fun_eq _ _ (id_right _)).
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply (dep_pi_psh_function_on_fun_eq _ _ (id_left _)).
        }
        rewrite !dep_psh_mor_comp'.
        etrans.
        {
          apply maponpaths.
          refine (dep_pi_psh_function_on_pt_eq _ _ _ _).
          etrans.
          {
            do 3 apply maponpaths.
            exact (!(dep_psh_total_space_pr2_path _ p)).
          }
          refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
          refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
          refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
          refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
          refine (dep_psh_mor_path_eq _ _ (idpath _) _ _).
          rewrite !id_left.
          apply idpath.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (dep_pi_psh_function_on_pt_eq _ _ _ _).
          refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
          refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
          refine (dep_psh_mor_path_eq _ _ (idpath _) _ _).
          rewrite !id_left, id_right.
          apply idpath.
        }
        rewrite !dep_psh_mor_comp'.
        use dep_psh_mor_path_eq.
        rewrite !id_left.
        apply idpath.
    Qed.

    Definition pi_dep_psh_eval
      : dep_psh_nat_trans
          (dep_psh_subst (total_psh_pr A) pi_dep_psh)
          B
          (nat_trans_id _).
    Proof.
      use make_dep_psh_nat_trans.
      - exact (λ x xx (φ : dep_pi_psh_function x (pr1 xx)),
               #d B (identity _)
                  (pi_dep_psh_eval_eq xx)
                  (φ x (identity _) (#d A (identity _) (idpath _) (pr2 xx)))).
      - exact pi_dep_psh_eval_laws.
    Defined.

    Arguments pi_dep_psh_eval /.

    (** * 6. λ-abstraction *)
    Section Lambda.
      Context {Z : dep_psh Γ}
              (τ : dep_psh_nat_trans
                     (dep_psh_subst (total_psh_pr A) Z)
                     B
                     (nat_trans_id _)).

      Proposition pi_dep_psh_lam_fun_laws
                  {x : C}
                  {xx : (Γ x : hSet)}
                  (z : Z x xx)
        : is_natural_dep_pi_psh_function
            (λ y f a,
              τ y (#Γ f xx ,, a)
                  (#d Z f (idpath _) z)).
      Proof.
        intros y₁ y₂ f₁ f₂ a ; cbn.
        simple refine (!(dep_psh_nat_trans_ax τ _ _ _ _) @ _).
        - use dep_psh_total_space_path.
          + exact (!(eqtohomot (functor_comp Γ _ _) _)).
          + cbn.
            rewrite !dep_psh_mor_comp'.
            use dep_psh_mor_path_eq.
            apply id_left.
        - cbn.
          apply maponpaths.
          rewrite dep_psh_mor_comp'.
          use (dep_psh_mor_path_eq Z).
          apply idpath.
      Qed.

      Definition pi_dep_psh_lam_fun
                 {x : C}
                 {xx : (Γ x : hSet)}
                 (z : Z x xx)
        : dep_pi_psh_function x xx.
      Proof.
        use make_dep_pi_psh_function.
        - intros y f a.
          refine (τ _ _ (#d Z f _ z)).
          apply idpath.
        - exact (pi_dep_psh_lam_fun_laws z).
      Defined.

      Proposition pi_dep_psh_lam_laws
        : dep_psh_nat_trans_naturality
            (A := Z)
            (B := pi_dep_psh)
            (s := nat_trans_id _)
            (λ x xx z, pi_dep_psh_lam_fun z).
      Proof.
        intros x₁ x₂ xx₁ xx₂ f p q z.
        use dep_pi_psh_function_eq.
        intros y g a.
        cbn.
        simple refine (_ @ dep_psh_nat_trans_ax τ _ _ _ _).
        - apply maponpaths.
          cbn.
          rewrite !dep_psh_mor_comp'.
          use dep_psh_mor_path_eq.
          rewrite id_left.
          apply idpath.
        - use dep_psh_total_space_path.
          + refine (eqtohomot (functor_id Γ _) _ @ _).
            refine (eqtohomot (functor_comp Γ _ _) _ @ _).
            cbn.
            apply maponpaths.
            exact p.
          + cbn.
            rewrite !dep_psh_mor_comp'.
            use dep_psh_mor_id'.
            rewrite !id_left.
            apply idpath.
      Qed.

      Definition pi_dep_psh_lam
        : dep_psh_nat_trans Z pi_dep_psh (nat_trans_id _).
      Proof.
        use make_dep_psh_nat_trans.
        - intros x xx z.
          exact (pi_dep_psh_lam_fun z).
        - exact pi_dep_psh_lam_laws.
      Defined.

      Arguments pi_dep_psh_lam /.

      (** * 7. β and η equations *)
      Proposition pi_dep_psh_lam_beta
        : τ
          =
          #(fiber_functor_from_cleaving
              (disp_cat_dep_psh C)
              (cleaving_disp_cat_dep_psh C)
              (total_psh_pr A))
            pi_dep_psh_lam
          · pi_dep_psh_eval.
      Proof.
        use dep_psh_nat_trans_eq.
        intros x xx a.
        refine (!_).
        refine (dep_psh_fiber_comp _ _ _ _ @ _).
        cbn -[fiber_functor_from_cleaving].
        etrans.
        {
          apply maponpaths.
          exact (maponpaths
                   (λ (z : dep_pi_psh_function _ _), z _ _ _)
                   (dep_psh_fiber_functor_from_cleaving
                      _
                      (total_psh_pr A)
                      pi_dep_psh_lam
                      a)).
        }
        cbn.
        simple refine (!(dep_psh_nat_trans_ax τ _ _ _ _) @ _).
        {
          use dep_psh_total_space_path.
          - cbn.
            refine (eqtohomot (functor_id Γ _) _ @ _).
            exact (eqtohomot (functor_id Γ _) _).
          - cbn.
            rewrite !dep_psh_mor_comp'.
            apply dep_psh_mor_id'.
            rewrite !id_left.
            apply idpath.
        }
        apply maponpaths.
        cbn.
        rewrite dep_psh_mor_comp'.
        use dep_psh_mor_id'.
        rewrite !id_left.
        apply idpath.
      Qed.

      Proposition pi_dep_psh_lam_eta
                  (τ' : dep_psh_nat_trans Z pi_dep_psh (nat_trans_id _))
                  (p : τ
                       =
                       #(fiber_functor_from_cleaving
                           (disp_cat_dep_psh C)
                           (cleaving_disp_cat_dep_psh C)
                           (total_psh_pr A))
                         τ'
                       · pi_dep_psh_eval)
        : τ' = pi_dep_psh_lam.
      Proof.
        use dep_psh_nat_trans_eq.
        intros x xx z.
        use dep_pi_psh_function_eq.
        intros y f a.
        cbn.
        rewrite p.
        refine (!_).
        refine (dep_psh_fiber_comp _ _ _ _ @ _).
        cbn -[fiber_functor_from_cleaving].
        etrans.
        {
          apply maponpaths.
          refine (maponpaths
                    (λ (z : dep_pi_psh_function _ _), z _ _ _)
                    _).
          exact (dep_psh_fiber_functor_from_cleaving
                   _
                   (total_psh_pr A)
                   τ'
                   (xx := # Γ f xx,, a)
                   (#d Z f _ z)).
        }
        cbn.
        etrans.
        {
          apply maponpaths.
          exact (maponpaths
                   (λ (h : dep_pi_psh_function y (# Γ f xx)), h y _ _)
                   (dep_psh_nat_trans_ax τ' f (idpath (#Γ f xx)) (idpath _) z)).
        }
        cbn.
        rewrite !dep_psh_mor_comp'.
        etrans.
        {
          apply maponpaths.
          exact (dep_pi_psh_function_on_fun_eq _ _ (id_left _) _).
        }
        rewrite dep_psh_mor_comp'.
        etrans.
        {
          apply maponpaths.
          refine (dep_pi_psh_function_on_pt_eq _ _ _ _).
          do 2 refine (dep_psh_mor_comp' _ _ _ _ _ _ @ _).
          apply (dep_psh_mor_id' A).
          rewrite !id_left.
          apply idpath.
        }
        rewrite dep_psh_mor_comp'.
        apply dep_psh_mor_id'.
        rewrite !id_left.
        apply idpath.
      Qed.
    End Lambda.
  End PiDepPsh.

  (** * 8. The dependent product *)
  Definition dependent_product_dep_psh
             {Γ : C^op ⟶ HSET}
             (A : dep_psh Γ)
    : dependent_product (cleaving_disp_cat_dep_psh C) (total_psh_pr A).
  Proof.
    use coreflections_to_is_left_adjoint.
    intro B.
    use make_coreflection.
    - use make_coreflection_data.
      + exact (pi_dep_psh A B).
      + exact (pi_dep_psh_eval A B).
    - intros [ Z τ ].
      use make_iscontr.
      + simple refine (_ ,, _).
        * exact (pi_dep_psh_lam A B τ).
        * apply pi_dep_psh_lam_beta.
      + abstract
          (intros τ' ;
           use subtypePath ; [ intro ; apply homset_property | ] ;
           exact (pi_dep_psh_lam_eta _ _ _ (pr1 τ') (pr2 τ'))).
  Defined.
End PiTypes.
