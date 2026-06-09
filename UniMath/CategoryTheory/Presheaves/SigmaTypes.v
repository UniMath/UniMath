(**

 Dependent sums in the presheaf model

 In this file, we define the basic operations to show that the presheaf model of
 Martin-Löf type theory supports dependent sums. We use the formulation of quantifiers
 as adjoints, since presheaves form a full comprehension category. In addition, we
 only show that weakening has a left adjoint.

 Content
 1. The presheaf representing the dependent sum
 2. Pairing and elimination
 3. Useful calculational lemmas
 4. Stability under substitution

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Reflections.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.

Local Open Scope cat.

Section SigmaTypes.
  Context {C : category}.

  (** 1. The presheaf representing the dependent sum *)
  Section SigmaDepPsh.
    Context {Γ : C^op ⟶ HSET}
            (A : dep_psh Γ)
            (B : dep_psh (total_psh A)).

    Definition sigma_dep_psh_ob
               {x : C}
               (xx : (Γ x : hSet))
      : hSet
      := (∑ (a : A x xx), B x (xx ,, a))%set.

    Proposition path_sigma_dep_psh_ob_path
                {x : C}
                {xx : (Γ x : hSet)}
                {ab₁ ab₂ : sigma_dep_psh_ob xx}
                (p : pr1 ab₁ = pr1 ab₂)
      : #(total_psh A) (identity x) (xx ,, pr1 ab₂) = xx ,, pr1 ab₁.
    Proof.
      use dep_psh_total_space_path.
      - exact (eqtohomot (functor_id Γ _) _).
      - cbn.
        rewrite p.
        rewrite dep_psh_mor_comp'.
        apply dep_psh_mor_id'.
        exact (!(id_left _)).
    Qed.

    Proposition path_sigma_dep_psh_ob
                {x : C}
                {xx : (Γ x : hSet)}
                {ab₁ ab₂ : sigma_dep_psh_ob xx}
                (p : pr1 ab₁ = pr1 ab₂)
                (q : pr2 ab₁
                     =
                     #d B (identity _) (path_sigma_dep_psh_ob_path p) (pr2 ab₂))
      : ab₁ = ab₂.
    Proof.
      induction ab₁ as [ a₁ b₁ ], ab₂ as [ a₂ b₂ ].
      cbn in *.
      induction p.
      apply maponpaths.
      refine (q @ _).
      apply dep_psh_mor_id.
    Qed.

    Definition sigma_dep_psh_mor
               {x y : C}
               {xx : (Γ x : hSet)}
               {yy : (Γ y : hSet)}
               (s : y --> x)
               (p : #Γ s xx = yy)
               (ab : sigma_dep_psh_ob xx)
      : sigma_dep_psh_ob yy.
    Proof.
      refine (#d A s p (pr1 ab) ,, #d B s _ (pr2 ab)).
      abstract
        (cbn ;
         induction p ;
         apply idpath).
    Defined.

    Proposition sigma_dep_psh_mor_id
                {x : C}
                {xx : (Γ x : hSet)}
                (p : #Γ (identity x) xx = xx)
                (ab : sigma_dep_psh_ob xx)
      : sigma_dep_psh_mor (identity x) p ab = ab.
    Proof.
      use path_sigma_dep_psh_ob ; cbn.
      - apply dep_psh_mor_id.
      - apply dep_psh_mor_path_eq.
        apply idpath.
    Qed.

    Proposition sigma_dep_psh_mor_comp
                {x y z : C}
                {xx : (Γ x : hSet)}
                {yy : (Γ y : hSet)}
                {zz : (Γ z : hSet)}
                {s₁ : y --> x}
                {s₂ : z --> y}
                (p : #Γ s₁ xx = yy)
                (q : #Γ s₂ yy = zz)
                (r : #Γ (s₂ · s₁) xx = zz)
                (a : sigma_dep_psh_ob xx)
      : sigma_dep_psh_mor (s₂ · s₁) r a
        =
        sigma_dep_psh_mor s₂ q (sigma_dep_psh_mor s₁ p a).
    Proof.
      use path_sigma_dep_psh_ob ; cbn.
      - apply dep_psh_mor_comp.
      - rewrite !dep_psh_mor_comp'.
        apply dep_psh_mor_path_eq.
        rewrite id_left.
        apply idpath.
    Qed.

    Definition sigma_dep_psh
      : dep_psh Γ.
    Proof.
      use make_dep_psh.
      - exact (λ x xx, sigma_dep_psh_ob xx).
      - exact (λ x y xx yy s p ab, sigma_dep_psh_mor s p ab).
      - intros x xx p ab.
        exact (sigma_dep_psh_mor_id p ab).
      - intros x y z xx yy zz s₁ s₂ p q r a.
        exact (sigma_dep_psh_mor_comp p q r a).
    Defined.

    (** * 2. Pairing and elimination *)
    Definition sigma_dep_psh_pair
      : dep_psh_nat_trans
          B
          (dep_psh_subst (total_psh_pr A) sigma_dep_psh)
          (nat_trans_id (total_psh_data A)).
    Proof.
      use make_dep_psh_nat_trans.
      - exact (λ x xx ab, pr2 xx ,, ab).
      - abstract
          (intros x y xx yy f p q ab ;
           induction p ; cbn ;
           use path_sigma_dep_psh_ob ;
           [ cbn ;
             apply dep_psh_mor_path_eq ;
             apply idpath
           | cbn ;
             rewrite dep_psh_mor_comp' ;
             use dep_psh_mor_path_eq ;
             rewrite id_left ;
             apply idpath ]).
    Defined.

    Definition sigma_dep_psh_elim
               {Z : dep_psh Γ}
               (τ : dep_psh_nat_trans
                      B
                      (dep_psh_subst (total_psh_pr A) Z)
                      (nat_trans_id _))
      : dep_psh_nat_trans sigma_dep_psh Z (nat_trans_id _).
    Proof.
      use make_dep_psh_nat_trans.
      - exact (λ x xx ab, τ x (xx ,, pr1 ab) (pr2 ab)).
      - abstract
          (intros x y xx yy f p q ab ;
           induction p ; cbn ;
           refine (dep_psh_nat_trans_ax τ f _ (idpath _) (pr2 ab) @ _) ;
           cbn ;
           apply dep_psh_mor_path_eq ;
           apply idpath).
    Defined.

    Definition dep_psh_sigma_total_inv_data
      : nat_trans_data (total_psh sigma_dep_psh) (total_psh B)
      := λ x ab, (pr1 ab ,, pr12 ab) ,, pr22 ab.

    Arguments dep_psh_sigma_total_inv_data /.

    Proposition dep_psh_sigma_total_inv_laws
      : is_nat_trans _ _ dep_psh_sigma_total_inv_data.
    Proof.
      intros x y f.
      use funextsec.
      intro ab.
      use dep_psh_total_space_path.
      - apply idpath.
      - cbn.
        rewrite dep_psh_mor_comp'.
        apply dep_psh_mor_path_eq.
        apply id_left.
    Qed.

    Definition dep_psh_sigma_total_inv
      : total_psh sigma_dep_psh ⟹ total_psh B.
    Proof.
      use make_nat_trans.
      - exact dep_psh_sigma_total_inv_data.
      - exact dep_psh_sigma_total_inv_laws.
    Defined.
  End SigmaDepPsh.

  Definition dependent_sum_dep_psh
             {Γ : C^op ⟶ HSET}
             (A : dep_psh Γ)
    : dependent_sum (cleaving_disp_cat_dep_psh C) (total_psh_pr A).
  Proof.
    use reflections_to_is_right_adjoint.
    intros B.
    use make_reflection.
    - use make_reflection_data.
      + exact (sigma_dep_psh A B).
      + exact (sigma_dep_psh_pair A B).
    - intro f.
      use make_iscontr.
      + simple refine (_ ,, _).
        * exact (sigma_dep_psh_elim A B (pr2 f)).
        * abstract
            (use dep_psh_nat_trans_eq ;
             intros x xx a ;
             refine (_ @ !(dep_psh_fiber_comp _ _ _ _)) ;
             refine (_ @ !(dep_psh_fiber_functor_from_cleaving _ (total_psh_pr A) _ _)) ;
             apply idpath).
      + abstract
          (intro τ' ;
           use subtypePath ; [ intro ; apply homset_property | ] ;
           use dep_psh_nat_trans_eq ;
           intros x xx a ;
           refine (_ @ !(dep_psh_nat_trans_eq_pt (pr2 τ') (xx ,, pr1 a) (pr2 a))) ;
           refine (_ @ !(dep_psh_fiber_comp _ _ _ _)) ;
           exact (!(dep_psh_fiber_functor_from_cleaving _ (total_psh_pr A) _ _))).
  Defined.

  (** * 3. Useful calculational lemmas *)
  Definition left_adjoint_dependent_sum_psh_eq
             {Γ : C^op ⟶ HSET}
             (A : dep_psh Γ)
             {B₁ B₂ : dep_psh (total_psh A)}
             (τ : dep_psh_nat_trans B₁ B₂ (nat_trans_id _))
             {x : C}
             (xx : (Γ x : hSet))
             (ab : sigma_dep_psh A B₁ x xx)
    : (#(left_adjoint (dependent_sum_dep_psh A)) τ : dep_psh_nat_trans _ _ _) x xx ab
      =
      pr1 ab ,, τ x _ (pr2 ab).
  Proof.
    refine (dep_psh_fiber_comp _ τ (sigma_dep_psh_pair A B₂) (pr2 ab) @ _).
    cbn.
    apply idpath.
  Qed.

  Proposition unit_dependent_sum_psh_eq
              {Γ : C^op ⟶ HSET}
              {A : dep_psh Γ}
              (B : dep_psh (total_psh A))
              {x : C}
              (xx : dep_psh_total_space A x)
              (b : B x xx)
    : (unit_from_right_adjoint (dependent_sum_dep_psh A) B : dep_psh_nat_trans _ _ _)
        x xx b
      =
      pr2 xx ,, b.
  Proof.
    apply idpath.
  Qed.

  Proposition counit_dependent_sum_psh_eq
              {Γ : C^op ⟶ HSET}
              (A B : dep_psh Γ)
              {x : C}
              (xx : (Γ x : hSet))
              (ab : sigma_dep_psh A (dep_psh_subst (total_psh_pr A) B) x xx)
    : (counit_from_right_adjoint (dependent_sum_dep_psh A) B : dep_psh_nat_trans _ _ _)
        x xx ab
      =
      pr2 ab.
  Proof.
    apply idpath.
  Qed.

  Proposition comm_nat_z_iso_dep_psh_eq_path
              {Γ₁ Γ₂ Γ₃ Γ₄ : C^op ⟶ HSET}
              {τ₁ : Γ₃ ⟹ Γ₄}
              {τ₂ : Γ₂ ⟹ Γ₄}
              {τ₃ : Γ₁ ⟹ Γ₂}
              {τ₄ : Γ₁ ⟹ Γ₃}
              (p : nat_trans_comp _ _ _ τ₄ τ₁ = nat_trans_comp _ _ _ τ₃ τ₂)
              (A : dep_psh Γ₄)
              {x : C}
              (xx : (Γ₁ x : hSet))
    : #Γ₄ (identity x) (τ₁ x (τ₄ x xx)) = τ₂ x (τ₃ x xx).
  Proof.
    refine (eqtohomot (functor_id Γ₄ _) _  @ _).
    cbn.
    exact (eqtohomot (nat_trans_eq_pointwise p x) xx).
  Qed.

  Proposition dep_psh_fiber_functor_from_cleaving_comp_inv_eq
              {Γ₁ Γ₂ Γ₃ : C^op ⟶ HSET}
              (τ₁ : Γ₂ ⟹ Γ₁)
              (τ₂ : Γ₃ ⟹ Γ₂)
              (A : dep_psh Γ₁)
              {x : C}
              {xx : (Γ₃ x : hSet)}
              (a : A x (τ₁ x (τ₂ x xx)))
    : (fiber_functor_from_cleaving_comp_inv (cleaving_disp_cat_dep_psh C) τ₁ τ₂ A
        : dep_psh_nat_trans _ _ _) x xx a
      =
      a.
  Proof.
    cbn.
    rewrite transportf_dep_psh_nat_trans.
    cbn.
    apply (transportf_set (A x)).
    apply setproperty.
  Qed.

  Proposition dep_psh_fiber_functor_from_cleaving_comp_eq
              {Γ₁ Γ₂ Γ₃ : C^op ⟶ HSET}
              (τ₁ : Γ₂ ⟹ Γ₁)
              (τ₂ : Γ₃ ⟹ Γ₂)
              (A : dep_psh Γ₁)
              {x : C}
              {xx : (Γ₃ x : hSet)}
              (a : A x (τ₁ x (τ₂ x xx)))
    : (fiber_functor_from_cleaving_comp (cleaving_disp_cat_dep_psh C) τ₁ τ₂ A
        : dep_psh_nat_trans _ _ _) x xx a
      =
      a.
  Proof.
    cbn.
    rewrite transportb_dep_psh_nat_trans.
    cbn.
    apply (transportf_set (A x)).
    apply setproperty.
  Qed.

  Proposition dep_psh_fiber_functor_on_eq_eq
              {Γ₁ Γ₂ : C^op ⟶ HSET}
              {τ₁ τ₂ : Γ₁ ⟹ Γ₂}
              (p : τ₁ = τ₂)
              (A : dep_psh Γ₂)
              {x : C}
              {xx : (Γ₁ x : hSet)}
              (a : A x (τ₁ x xx))
    : (fiber_functor_on_eq (cleaving_disp_cat_dep_psh C) p A : dep_psh_nat_trans _ _ _)
        x xx a
      =
      #d A (identity _)
           (eqtohomot (functor_id Γ₂ _) _ @ eqtohomot (nat_trans_eq_pointwise p _) _)
           a.
  Proof.
    induction p ; cbn.
    refine (!_).
    apply dep_psh_mor_id.
  Qed.

  Proposition comm_nat_z_iso_dep_psh_eq
              {Γ₁ Γ₂ Γ₃ Γ₄ : C^op ⟶ HSET}
              {τ₁ : Γ₃ ⟹ Γ₄}
              {τ₂ : Γ₂ ⟹ Γ₄}
              {τ₃ : Γ₁ ⟹ Γ₂}
              {τ₄ : Γ₁ ⟹ Γ₃}
              (p : nat_trans_comp _ _ _ τ₄ τ₁ = nat_trans_comp _ _ _ τ₃ τ₂)
              (A : dep_psh Γ₄)
              {x : C}
              (xx : (Γ₁ x : hSet))
              (a : A x (τ₁ x (τ₄ x xx)))
    : (comm_nat_z_iso (cleaving_disp_cat_dep_psh C) _ _ _ _ p A : dep_psh_nat_trans _ _ _)
        x xx a
      =
      #d A (identity _) (comm_nat_z_iso_dep_psh_eq_path p A xx) a.
  Proof.
    rewrite (comm_nat_z_iso_ob (cleaving_disp_cat_dep_psh C) _ _ _ _ p A).
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
      exact (dep_psh_fiber_functor_on_eq_eq p A a).
    }
    apply (dep_psh_mor_path_eq A).
    apply idpath.
  Qed.

  (** * 4. Stability under substitution *)
  Definition dep_psh_sigma_subst
             {Γ₁ Γ₂ : C^op ⟶ HSET}
             (s : Γ₁ ⟹ Γ₂)
             (A : dep_psh Γ₂)
             (B : dep_psh (total_psh A))
    : dep_psh_nat_trans
        (dep_psh_subst s (sigma_dep_psh A B))
        (sigma_dep_psh
           (dep_psh_subst s A)
           (dep_psh_subst
              (total_psh_nat_trans s (dep_psh_subst_nat_trans s A))
              B))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx ab, ab).
    - abstract
        (intros x y xx yy f p q a ; cbn ;
         assert (p = q) as r by apply setproperty ;
         induction r ;
         unfold sigma_dep_psh_mor ; cbn ;
         apply maponpaths ;
         apply dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Proposition dep_psh_sigma_beck_chevalley
              {Γ₁ Γ₂ : C^op ⟶ HSET}
              (s : Γ₁ ⟹ Γ₂)
              (A : dep_psh Γ₂)
              (B : dep_psh (total_psh A))
              {x : C}
              {xx : (Γ₁ x : hSet)}
              (ab : sigma_dep_psh
                      (dep_psh_subst s A)
                      (dep_psh_subst
                         (total_psh_nat_trans s (dep_psh_subst_nat_trans s A))
                         B)
                      x
                      xx)
              (p : nat_trans_comp
                     _ _ _
                     (total_psh_nat_trans s (dep_psh_subst_nat_trans s A))
                     (total_psh_pr A)
                   =
                   nat_trans_comp
                     _ _ _
                     (total_psh_pr (dep_psh_subst s A))
                     s)
    : (left_beck_chevalley_nat_trans
         (dependent_sum_dep_psh A)
         (dependent_sum_dep_psh (dep_psh_subst s A))
         (comm_nat_z_iso
            (cleaving_disp_cat_dep_psh C)
            (total_psh_pr A)
            s
            (total_psh_pr (dep_psh_subst s A))
            (total_psh_nat_trans s (dep_psh_subst_nat_trans s A))
            p)
         B : dep_psh_nat_trans _ _ _) x xx ab
      =
      ab.
  Proof.
    pose (left_beck_chevalley_nat_trans_ob
            (dependent_sum_dep_psh A)
            (dependent_sum_dep_psh (dep_psh_subst s A))
            (comm_nat_z_iso
               (cleaving_disp_cat_dep_psh C)
               (total_psh_pr A)
               s
               (total_psh_pr (dep_psh_subst s A))
               (total_psh_nat_trans s (dep_psh_subst_nat_trans s A))
               p)
            B)
      as q.
    refine (maponpaths (λ (z : dep_psh_nat_trans _ _ _), z x xx ab) q @ _).
    clear q.
    refine (dep_psh_fiber_comp _ _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      apply dep_psh_fiber_comp.
    }
    refine (counit_dependent_sum_psh_eq (dep_psh_subst s A) _ _ _ @ _).
    etrans.
    {
      do 2 apply maponpaths.
      refine (left_adjoint_dependent_sum_psh_eq _ _ _ _ @ _).
      apply maponpaths.
      exact (dep_psh_fiber_functor_from_cleaving _ _ _ _).
    }
    etrans.
    {
      apply maponpaths.
      exact (left_adjoint_dependent_sum_psh_eq _ _ _ _).
    }
    cbn -[comm_nat_z_iso].
    etrans.
    {
      exact (comm_nat_z_iso_dep_psh_eq p (sigma_dep_psh A B) (xx ,, pr1 ab) ab).
    }
    apply (dep_psh_mor_id (sigma_dep_psh A B)).
  Qed.
End SigmaTypes.
