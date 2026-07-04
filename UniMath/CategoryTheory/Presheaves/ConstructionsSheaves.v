(**

 Constructions of sheaves and dependent sheaves

 We show that various constructions of presheaves lift to constructions of sheaves. These
 constructions give us the usual type formers in extensional type theory. By showing that
 these constructions lift to the level of sheaves, we can deduce that the sheaf model of
 extensional type theory supports these type formers. Note that we discuss ∑-types and
 ∏-types in different files.

 Content
 1. The terminal sheaf (empty context), binary products, and pullbacks
 2. The unit dependent sheaf (unit type)
 3. Substitution of dependent sheaves
 4. Binary products of dependent sheaves (product types)
 5. Equalizers of sheaves (extensional identity types)
 6. Democracy of the sheaf model
 7. The total space of a dependent sheaf (context extension)
 8. Fiberwise limits for dependent sheaves
 9. The inclusion preserves fiberwise limits
 10. Sections of the projection

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Limits.PreservationProperties.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.FullSubcategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.FullSubDispCat.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.SubobjectClassifier.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Sites.
Require Import UniMath.CategoryTheory.Presheaves.Sheaves.
Require Import UniMath.CategoryTheory.IdempotentsAndSplitting.Retracts.

Local Open Scope cat.

(** * 1. The terminal sheaf (empty context), binary products, and pullbacks *)
Definition is_sheaf_terminal
           (C : site)
  : is_sheaf (constant_functor C^op HSET unitset).
Proof.
  intros x ω p z.
  use make_iscontr.
  - use make_amalgamation.
    + exact tt.
    + abstract
        (intro ; intros ;
         apply isapropunit).
  - abstract
      (intros ;
       use amalgamation_eq ;
       apply isapropunit).
Defined.

Definition sheaf_terminal
           (C : site)
  : Terminal (cat_of_sheaves C).
Proof.
  use make_Terminal.
  - use make_sheaf.
    + exact (constant_functor C^op HSET unitset).
    + exact (is_sheaf_terminal C).
  - intros Γ.
    use make_iscontr.
    + refine (_ ,, tt).
      use make_nat_trans.
      * exact (λ x xx, tt).
      * abstract
          (intros x y f ;
           use funextsec ;
           intro xx ;
           apply isapropunit).
    + abstract
        (intros τ ;
         use sheaf_nat_trans_eq ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intros x ;
         use funextsec ;
         intro xx ;
         apply isapropunit).
Defined.

Definition pr1_matching_family
           {C : site}
           {Γ₁ Γ₂ : C^op ⟶ HSET}
           {x : C}
           {ω : sieve x}
           (z : matching_family (BinProduct_of_functors C^op SET BinProductsHSET Γ₁ Γ₂) ω)
  : matching_family Γ₁ ω.
Proof.
  use make_matching_family.
  - exact (λ y f p, pr1 (z y f p)).
  - abstract
      (intros y₁ y₂ f₁ f₂ g p q₁ q₂ ; cbn ;
       exact (maponpaths pr1 (matching_family_restr z p q₁ q₂))).
Defined.

Definition pr2_matching_family
           {C : site}
           {Γ₁ Γ₂ : C^op ⟶ HSET}
           {x : C}
           {ω : sieve x}
           (z : matching_family (BinProduct_of_functors C^op SET BinProductsHSET Γ₁ Γ₂) ω)
  : matching_family Γ₂ ω.
Proof.
  use make_matching_family.
  - exact (λ y f p, pr2 (z y f p)).
  - abstract
      (intros y₁ y₂ f₁ f₂ g p q₁ q₂ ; cbn ;
       exact (maponpaths dirprod_pr2 (matching_family_restr z p q₁ q₂))).
Defined.

Section IsSheafBinaryProd.
  Context {C : site}
          {Γ₁ Γ₂ : C^op ⟶ HSET}
          (HΓ₁ : is_sheaf Γ₁)
          (HΓ₂ : is_sheaf Γ₂)
          {x : C}
          {ω : sieve x}
          (p : C x ω)
          (z : matching_family (BinProduct_of_functors C^op SET BinProductsHSET Γ₁ Γ₂) ω).

  Definition prod_sheaf_amalgamation
    : amalgamation z.
  Proof.
    use make_amalgamation.
    - refine (_ ,, _).
      + exact (sheaf_amalgamation HΓ₁ p (pr1_matching_family z)).
      + exact (sheaf_amalgamation HΓ₂ p (pr2_matching_family z)).
    - abstract
        (intros y f q ;
         use pathsdirprod ; cbn ;
         [ apply (amalgamation_restr (sheaf_amalgamation HΓ₁ p (pr1_matching_family z)))
         | apply (amalgamation_restr (sheaf_amalgamation HΓ₂ p (pr2_matching_family z))) ]).
  Defined.

  Proposition prod_sheaf_amalgamation_unique
              (a : amalgamation z)
    : a = prod_sheaf_amalgamation.
  Proof.
    use amalgamation_eq ; cbn.
    use pathsdirprod.
    - use (sheaf_amalgamation_unique HΓ₁ p).
      + exact (pr1_matching_family z).
      + intros y f q.
        exact (maponpaths pr1 (amalgamation_restr a f q)).
      + intros y f q.
        apply (amalgamation_restr (sheaf_amalgamation HΓ₁ p (pr1_matching_family z))).
    - use (sheaf_amalgamation_unique HΓ₂ p).
      + exact (pr2_matching_family z).
      + intros y f q.
        exact (maponpaths dirprod_pr2 (amalgamation_restr a f q)).
      + intros y f q.
        apply (amalgamation_restr (sheaf_amalgamation HΓ₂ p (pr2_matching_family z))).
  Qed.
End IsSheafBinaryProd.

Definition is_sheaf_binproduct
           {C : site}
           {Γ₁ Γ₂ : C^op ⟶ HSET}
           (HΓ₁ : is_sheaf Γ₁)
           (HΓ₂ : is_sheaf Γ₂)
  : is_sheaf (BinProduct_of_functors _ _ BinProductsHSET Γ₁ Γ₂).
Proof.
  intros x ω p z.
  use make_iscontr.
  - exact (prod_sheaf_amalgamation HΓ₁ HΓ₂ p z).
  - exact (prod_sheaf_amalgamation_unique HΓ₁ HΓ₂ p z).
Defined.

Section IsSheafPullback.
  Context {C : site}
          {Γ₁ Γ₂ Γ₃ : sheaf C}
          (τ₁ : sheaf_nat_trans Γ₁ Γ₃)
          (τ₂ : sheaf_nat_trans Γ₂ Γ₃).

  Let Δ : C^op ⟶ HSET
    := PullbackObject (Pullbacks_PreShv _ _ _ (pr1 τ₁) (pr1 τ₂)).
  Let π₁ : Δ ⟹ Γ₁
    := PullbackPr1 (Pullbacks_PreShv _ _ _ (pr1 τ₁) (pr1 τ₂)).
  Let π₂ : Δ ⟹ Γ₂
    := PullbackPr2 (Pullbacks_PreShv _ _ _ (pr1 τ₁) (pr1 τ₂)).

  Section Amalgamation.
    Context {x : C}
            {ω : sieve x}
            (p : C x ω)
            (z : matching_family Δ ω).

    Let z₁ : matching_family Γ₁ ω := nat_trans_matching_family π₁ z.
    Let z₂ : matching_family Γ₂ ω := nat_trans_matching_family π₂ z.
    Let z₃ : matching_family Γ₃ ω
      := nat_trans_matching_family (nat_trans_comp _ _ _ π₂ τ₂) z.

    Definition pullback_amalgamation_pr1
      : (Γ₁ x : hSet)
      := sheaf_amalgamation (is_sheaf_sheaf Γ₁) p z₁.

    Definition pullback_amalgamation_pr2
      : (Γ₂ x : hSet)
      := sheaf_amalgamation (is_sheaf_sheaf Γ₂) p z₂.

    Proposition pullback_amalgamation_eq
      : τ₁ x pullback_amalgamation_pr1
        =
        τ₂ x pullback_amalgamation_pr2.
    Proof.
      use (sheaf_amalgamation_unique (is_sheaf_sheaf Γ₃) p).
      - exact z₃.
      - intros y g q ; unfold pullback_amalgamation_pr1 ; cbn.
        refine (!(eqtohomot (nat_trans_ax τ₁ _ _ g) _) @ _).
        cbn.
        etrans.
        {
          apply maponpaths.
          exact (amalgamation_restr (sheaf_amalgamation (is_sheaf_sheaf Γ₁) p z₁) g q).
        }
        cbn.
        exact (pr2 (z y g q)).
      - intros y g q ; unfold pullback_amalgamation_pr2 ; cbn.
        refine (!(eqtohomot (nat_trans_ax τ₂ _ _ g) _) @ _).
        cbn.
        apply maponpaths.
        exact (amalgamation_restr (sheaf_amalgamation (is_sheaf_sheaf Γ₂) p z₂) g q).
    Qed.

    Definition pullback_amalgamation_el
      : (Δ x : hSet).
    Proof.
      simple refine ((_ ,, _) ,, _).
      - exact pullback_amalgamation_pr1.
      - exact pullback_amalgamation_pr2.
      - exact pullback_amalgamation_eq.
    Defined.

    Proposition pullback_amalgamation_law
      : amalgamation_law z pullback_amalgamation_el.
    Proof.
      intros y g q.
      use subtypePath.
      {
        intro.
        apply setproperty.
      }
      use pathsdirprod.
      - cbn.
        exact (amalgamation_restr (sheaf_amalgamation (is_sheaf_sheaf Γ₁) p z₁) g q).
      - cbn.
        exact (amalgamation_restr (sheaf_amalgamation (is_sheaf_sheaf Γ₂) p z₂) g q).
    Qed.

    Definition pullback_amalgamation
      : amalgamation z.
    Proof.
      use make_amalgamation.
      - exact pullback_amalgamation_el.
      - exact pullback_amalgamation_law.
    Defined.

    Proposition pullback_amalgamation_unique
                (a : amalgamation z)
      : a = pullback_amalgamation.
    Proof.
      use amalgamation_eq.
      use subtypePath.
      {
        intro.
        apply setproperty.
      }
      use pathsdirprod.
      - use (sheaf_amalgamation_unique (is_sheaf_sheaf Γ₁) p).
        + exact z₁.
        + intros y g q ; cbn.
          exact (maponpaths (λ w, pr11 w) (amalgamation_restr a g q)).
        + intros y g q ; unfold pullback_amalgamation_pr1 ; cbn.
          exact (amalgamation_restr (sheaf_amalgamation (is_sheaf_sheaf Γ₁) p z₁) g q).
      - use (sheaf_amalgamation_unique (is_sheaf_sheaf Γ₂) p).
        + exact z₂.
        + intros y g q ; cbn.
          exact (maponpaths (λ w, dirprod_pr2 (pr1 w)) (amalgamation_restr a g q)).
        + intros y g q ; unfold pullback_amalgamation_pr2 ; cbn.
          exact (amalgamation_restr (sheaf_amalgamation (is_sheaf_sheaf Γ₂) p z₂) g q).
    Qed.
  End Amalgamation.

  Definition is_sheaf_pullback
    : is_sheaf Δ.
  Proof.
    intros x ω p z.
    use make_iscontr.
    - exact (pullback_amalgamation p z).
    - exact (pullback_amalgamation_unique p z).
  Defined.

  Definition pullback_sheaf
    : sheaf C.
  Proof.
    use make_sheaf.
    - exact Δ.
    - exact is_sheaf_pullback.
  Defined.
End IsSheafPullback.

Definition pullback_cat_of_sheaves
           (C : site)
  : Pullbacks (cat_of_sheaves C).
Proof.
  intros Γ₁ Γ₂ Γ₃ τ₁ τ₂.
  pose (PB := Pullbacks_PreShv _ _ _ (pr1 τ₁) (pr1 τ₂)).
  use make_Pullback.
  - exact (pullback_sheaf τ₁ τ₂).
  - use make_sheaf_nat_trans.
    exact (PullbackPr1 PB).
  - use make_sheaf_nat_trans.
    exact (PullbackPr2 PB).
  - use sheaf_nat_trans_eq.
    exact (PullbackSqrCommutes PB).
  - intros Δ θ₁ θ₂ p.
    use make_iscontr.
    + simple refine (_ ,, _ ,, _).
      * use make_sheaf_nat_trans.
        refine (PullbackArrow PB _ (pr1 θ₁) (pr1 θ₂) _).
        abstract
          (exact (maponpaths pr1 p)).
      * abstract
          (use sheaf_nat_trans_eq ;
           apply (PullbackArrow_PullbackPr1 PB)).
      * abstract
          (use sheaf_nat_trans_eq ;
           apply (PullbackArrow_PullbackPr2 PB)).
    + abstract
        (intros [ ζ q ] ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply homset_property | ] ;
         use sheaf_nat_trans_eq ;
         exact (PullbackArrowUnique
                  _
                  (isPullback_Pullback PB)
                  _ _ _ _ _
                  (maponpaths pr1 (pr1 q))
                  (maponpaths pr1 (pr2 q)))).
Defined.

Proposition preserves_pb_sheaf_incl
            (C : site)
  : preserves_pullback (sheaf_incl C).
Proof.
  use preserves_pullback_if_preserves_chosen.
  {
    exact (pullback_cat_of_sheaves C).
  }
  intros Γ₁ Γ₂ Γ₃ τ₁ τ₂.
  pose (PB := Pullbacks_PreShv _ _ _ (pr1 τ₁) (pr1 τ₂)).
  use (isPullback_z_iso _ _ (isPullback_Pullback PB)).
  - apply identity_z_iso.
  - apply id_left.
  - apply id_left.
Defined.

Proposition isMonic_sheaf_injective
            {C : site}
            {Γ₁ Γ₂ : sheaf C}
            {τ : sheaf_nat_trans Γ₁ Γ₂}
            (H : isMonic τ)
            {x : C}
            {xx₁ xx₂ : (Γ₁ x : hSet)}
            (p : τ x xx₁ = τ x xx₂)
  : xx₁ = xx₂.
Proof.
  use (isMonic_presheaf_injective _ p).
  use (@is_monic_functor_preserves_pb _ _ (sheaf_incl C)).
  - exact (preserves_pb_sheaf_incl C).
  - exact H.
Qed.

(** * 2. The unit dependent sheaf (unit type) *)
Definition is_dep_sheaf_unit_dep_psh
           {C : site}
           (Γ : C^op ⟶ HSET)
  : is_dep_sheaf (unit_dep_psh Γ).
Proof.
  intros x ω H z a zz.
  use make_iscontr.
  - use make_amalgamation_dep.
    + exact tt.
    + abstract
        (intro ; intros ;
         cbn ;
         apply isapropunit).
  - abstract
      (intros aa ;
       use amalgamation_dep_eq ;
       apply isapropunit).
Defined.

(** * 3. Substitution of dependent sheaves *)
Definition subst_matching_family
           {C : site}
           {Γ₁ Γ₂ : C^op ⟶ SET}
           (s : Γ₁ ⟹ Γ₂)
           {x : C}
           {ω : sieve x}
           (z : matching_family Γ₁ ω)
  : matching_family Γ₂ ω.
Proof.
  use make_matching_family.
  - exact (λ y f p, s y (z y f p)).
  - abstract
      (intros y₁ y₂ f₁ f₂ g p q₁ q₂ ; cbn ;
       refine (!eqtohomot (nat_trans_ax s _ _ g) _ @ _) ;
       cbn ;
       apply maponpaths ;
       exact (matching_family_restr z p q₁ q₂)).
Defined.

Definition subst_amalgamation
           {C : site}
           {Γ₁ Γ₂ : C^op ⟶ SET}
           (s : Γ₁ ⟹ Γ₂)
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ₁ ω}
           (a : amalgamation z)
  : amalgamation (subst_matching_family s z).
Proof.
  use make_amalgamation.
  - exact (s x a).
  - abstract
      (intros y f p ; cbn ;
       refine (!eqtohomot (nat_trans_ax s _ _ f) _ @ _) ;
       cbn ;
       apply maponpaths ;
       exact (amalgamation_restr a f p)).
Defined.

Definition subst_matching_family_dep
           {C : site}
           {Γ₁ Γ₂ : C^op ⟶ SET}
           (s : Γ₁ ⟹ Γ₂)
           {A : dep_psh Γ₂}
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ₁ ω}
           (zz : matching_family_dep (dep_psh_subst s A) z)
  : matching_family_dep A (subst_matching_family s z).
Proof.
  use make_matching_family_dep.
  - exact (λ y f p, zz y f p).
  - abstract
      (intros y₁ y₂ f₁ f₂ g p q₁ q₂ ; cbn ;
       refine (_ @ matching_family_dep_restr zz p q₁ q₂) ;
       cbn ;
       use dep_psh_mor_path_eq ;
       apply idpath).
Defined.

Section SubstSheaf.
  Context {C : site}
          {Γ₁ Γ₂ : C^op ⟶ HSET}
          (s : Γ₁ ⟹ Γ₂)
          {A : dep_psh Γ₂}
          (HA : is_dep_sheaf A)
          {x : C}
          {ω : sieve x}
          (H : C x ω)
          {z : matching_family Γ₁ ω}
          (a : amalgamation z)
          (zz : matching_family_dep (dep_psh_subst s A) z).

  Proposition dep_sheaf_subst_amalgamation_law
    : amalgamation_dep_law
        zz
        (dep_sheaf_amalgamation
           HA
           H
           (subst_matching_family s z)
           (subst_amalgamation s a)
           (subst_matching_family_dep s zz)).
  Proof.
    intros y f p ; cbn.
    pose (dep_sheaf_amalgamation_restr
            HA
            H
            (subst_matching_family s z)
            (subst_amalgamation s a)
            (subst_matching_family_dep s zz)
            p)
      as q.
    refine (_ @ q) ; cbn.
    apply dep_psh_mor_path_eq.
    apply idpath.
  Qed.

  Definition dep_sheaf_subst_amalgamation
    : amalgamation_dep a zz.
  Proof.
    use make_amalgamation_dep.
    - exact (dep_sheaf_amalgamation
               HA
               H
               (subst_matching_family s z)
               (subst_amalgamation s a)
               (subst_matching_family_dep s zz)).
    - exact dep_sheaf_subst_amalgamation_law.
  Defined.

  Proposition dep_sheaf_subst_amalgamation_unique
              (aa : amalgamation_dep a zz)
    : aa = dep_sheaf_subst_amalgamation.
  Proof.
    use amalgamation_dep_eq.
    use (dep_sheaf_amalgamation_unique HA H (a := subst_amalgamation s a)).
    - exact (subst_matching_family_dep s zz).
    - intros y f p ; cbn.
      refine (_ @ amalgamation_dep_restr aa f p).
      cbn.
      use dep_psh_mor_path_eq.
      apply idpath.
    - intros y f p ; cbn.
      pose (dep_sheaf_amalgamation_restr
              HA
              H
              (subst_matching_family s z)
              (subst_amalgamation s a)
              (subst_matching_family_dep s zz)
              p)
        as q.
      refine (_ @ q).
      cbn.
      use dep_psh_mor_path_eq.
      apply idpath.
  Qed.
End SubstSheaf.

Definition is_dep_sheaf_dep_psh_subst
           {C : site}
           {Γ₁ Γ₂ : C^op ⟶ HSET}
           (s : Γ₁ ⟹ Γ₂)
           {A : dep_psh Γ₂}
           (HA : is_dep_sheaf A)
  : is_dep_sheaf (dep_psh_subst s A).
Proof.
  intros x ω H z a zz.
  use make_iscontr.
  - exact (dep_sheaf_subst_amalgamation s HA H a zz).
  - exact (dep_sheaf_subst_amalgamation_unique s HA H a zz).
Defined.

Definition dep_sheaf_subst
           {C : site}
           {Γ₁ Γ₂ : sheaf C}
           (s : Γ₁ ⟹ Γ₂)
           (A : dep_sheaf Γ₂)
  : dep_sheaf Γ₁.
Proof.
  use make_dep_sheaf.
  - exact (dep_psh_subst s A).
  - apply is_dep_sheaf_dep_psh_subst.
    apply is_dep_sheaf_dep_sheaf.
Defined.

(** * 4. Binary products of dependent sheaves (product types) *)
Definition pr1_matching_family_dep
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A B : dep_psh Γ}
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ ω}
           (zz : matching_family_dep (prod_dep_psh A B) z)
  : matching_family_dep A z.
Proof.
  use make_matching_family_dep.
  - exact (λ y f p, pr1 (zz y f p)).
  - exact (λ y₁ y₂ f₁ f₂ g p q₁ q₂,
           maponpaths pr1 (matching_family_dep_restr zz p q₁ q₂)).
Defined.

Definition pr2_matching_family_dep
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A B : dep_psh Γ}
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ ω}
           (zz : matching_family_dep (prod_dep_psh A B) z)
  : matching_family_dep B z.
Proof.
  use make_matching_family_dep.
  - exact (λ y f p, pr2 (zz y f p)).
  - exact (λ y₁ y₂ f₁ f₂ g p q₁ q₂,
           maponpaths dirprod_pr2 (matching_family_dep_restr zz p q₁ q₂)).
Defined.

Section ProdDepSheaf.
  Context {C : site}
          {Γ : C^op ⟶ HSET}
          {A B : dep_psh Γ}
          (HA : is_dep_sheaf A)
          (HB : is_dep_sheaf B)
          {x : C}
          {ω : sieve x}
          (H : C x ω)
          {z : matching_family Γ ω}
          (a : amalgamation z)
          (zz : matching_family_dep (prod_dep_psh A B) z).

  Definition prod_dep_sheaf_amalgamation
    : amalgamation_dep a zz.
  Proof.
    use make_amalgamation_dep.
    - refine (_ ,, _).
      + exact (dep_sheaf_amalgamation HA H z a (pr1_matching_family_dep zz)).
      + exact (dep_sheaf_amalgamation HB H z a (pr2_matching_family_dep zz)).
    - abstract
        (intros y f p ;
         use pathsdirprod ;
         [ exact (dep_sheaf_amalgamation_restr HA H z a (pr1_matching_family_dep zz) p)
         | exact (dep_sheaf_amalgamation_restr HB H z a (pr2_matching_family_dep zz) p) ]).
  Defined.

  Proposition prod_dep_sheaf_amalgamation_unique
              (aa : amalgamation_dep a zz)
    : aa = prod_dep_sheaf_amalgamation.
  Proof.
    use amalgamation_dep_eq.
    use pathsdirprod.
    - use (dep_sheaf_amalgamation_unique HA H).
      + exact (pr1_matching_family_dep zz).
      + intros y f p.
        exact (maponpaths pr1 (amalgamation_dep_restr aa f p)).
      + intros y f p.
        exact (dep_sheaf_amalgamation_restr HA H z a (pr1_matching_family_dep zz) p).
    - use (dep_sheaf_amalgamation_unique HB H).
      + exact (pr2_matching_family_dep zz).
      + intros y f p.
        exact (maponpaths dirprod_pr2 (amalgamation_dep_restr aa f p)).
      + intros y f p.
        exact (dep_sheaf_amalgamation_restr HB H z a (pr2_matching_family_dep zz) p).
  Qed.
End ProdDepSheaf.

Definition is_dep_sheaf_prod_dep_psh
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A B : dep_psh Γ}
           (HA : is_dep_sheaf A)
           (HB : is_dep_sheaf B)
  : is_dep_sheaf (prod_dep_psh A B).
Proof.
  intros x ω H z a zz.
  use make_iscontr.
  - exact (prod_dep_sheaf_amalgamation HA HB H a zz).
  - exact (prod_dep_sheaf_amalgamation_unique HA HB H a zz).
Defined.

(** * 5. Equalizers of sheaves (extensional identity types) *)
Definition pr1_matching_family_dep_equalizer
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A B : dep_psh Γ}
           (τ₁ τ₂ : dep_psh_nat_trans A B (nat_trans_id Γ))
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ ω}
           (zz : matching_family_dep (equalizer_dep_psh τ₁ τ₂) z)
  : matching_family_dep A z.
Proof.
  use make_matching_family_dep.
  - exact (λ y f p, pr1 (zz y f p)).
  - exact (λ y₁ y₂ f₁ f₂ g p q₁ q₂,
           maponpaths pr1 (matching_family_dep_restr zz p q₁ q₂)).
Defined.

Definition im_matching_family_dep_equalizer
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A B : dep_psh Γ}
           (τ₁ τ₂ : dep_psh_nat_trans A B (nat_trans_id Γ))
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ ω}
           (zz : matching_family_dep (equalizer_dep_psh τ₁ τ₂) z)
  : matching_family_dep B z.
Proof.
  use make_matching_family_dep.
  - exact (λ y f p, τ₁ _ _ (pr1 (zz y f p))).
  - intros y₁ y₂ f₁ f₂ g p q₁ q₂ ; cbn.
    refine (!(dep_psh_nat_trans_ax τ₁ _ _ _ _) @ _).
    apply maponpaths.
    exact (maponpaths pr1 (matching_family_dep_restr zz p q₁ q₂)).
Defined.

Section EqualizerDepSheaf.
  Context {C : site}
          {Γ : C^op ⟶ HSET}
          {A B : dep_psh Γ}
          (τ₁ τ₂ : dep_psh_nat_trans A B (nat_trans_id _))
          (HA : is_dep_sheaf A)
          (HB : is_dep_sheaf B)
          {x : C}
          {ω : sieve x}
          (H : C x ω)
          {z : matching_family Γ ω}
          (a : amalgamation z)
          (zz : matching_family_dep (equalizer_dep_psh τ₁ τ₂) z).

  Let amalg : A x a
    := dep_sheaf_amalgamation
         HA H
         z a
         (pr1_matching_family_dep_equalizer τ₁ τ₂ zz).

  Proposition equalizer_dep_sheaf_amalgamation_eq
    : τ₁ x a amalg = τ₂ x a amalg.
  Proof.
    use (dep_sheaf_amalgamation_unique HB H).
    - exact (im_matching_family_dep_equalizer τ₁ τ₂ zz).
    - cbn.
      intros y f p.
      refine (!(dep_psh_nat_trans_ax τ₁ _ _ _ _) @ _).
      apply maponpaths.
      exact (dep_sheaf_amalgamation_restr HA H z a _ _).
    - cbn.
      intros y f p.
      refine (_ @ !(pr2 (zz y f p))).
      refine (!(dep_psh_nat_trans_ax τ₂ _ _ _ _) @ _).
      apply maponpaths.
      exact (dep_sheaf_amalgamation_restr HA H z a _ _).
  Qed.

  Definition equalizer_dep_sheaf_amalgamation
    : amalgamation_dep a zz.
  Proof.
    use make_amalgamation_dep.
    - simple refine (_ ,, _).
      + exact amalg.
      + exact equalizer_dep_sheaf_amalgamation_eq.
    - abstract
        (intros y f p ; cbn ;
         use subtypePath ; [ intro ; apply setproperty | ] ;
         exact (dep_sheaf_amalgamation_restr HA H z a _ p)).
  Defined.

  Proposition equalizer_dep_sheaf_amalgamation_unique
              (aa : amalgamation_dep a zz)
    : aa = equalizer_dep_sheaf_amalgamation.
  Proof.
    use amalgamation_dep_eq.
    use subtypePath ; [ intro ; apply setproperty | ].
    cbn.
    use (dep_sheaf_amalgamation_unique HA H).
    - exact (pr1_matching_family_dep_equalizer τ₁ τ₂ zz).
    - intros y f p.
      exact (maponpaths pr1 (amalgamation_dep_restr aa f p)).
    - intros y f p.
      exact (dep_sheaf_amalgamation_restr HA H z a _ p).
  Qed.
End EqualizerDepSheaf.

Definition is_dep_sheaf_equalizer_dep_psh
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A B : dep_psh Γ}
           (τ₁ τ₂ : dep_psh_nat_trans A B (nat_trans_id _))
           (HA : is_dep_sheaf A)
           (HB : is_dep_sheaf B)
  : is_dep_sheaf (equalizer_dep_psh τ₁ τ₂).
Proof.
  intros x ω H z a zz.
  use make_iscontr.
  - exact (equalizer_dep_sheaf_amalgamation τ₁ τ₂ HA HB H a zz).
  - exact (equalizer_dep_sheaf_amalgamation_unique τ₁ τ₂ HA HB H a zz).
Defined.

(** * 6. Democracy of the sheaf model *)
Proposition is_dep_sheaf_psh_to_dep_psh_unique
            {C : site}
            {Γ : C^op ⟶ HSET}
            (HΓ : is_sheaf Γ)
            {x : C}
            {ω : sieve x}
            (H : C x ω)
            {z : matching_family (constant_functor C^op SET unitHSET) ω}
            (a : amalgamation z)
            (zz : matching_family_dep (psh_to_dep_psh Γ) z)
            (aa : amalgamation_dep a zz)
  : aa = sheaf_amalgamation HΓ H zz.
Proof.
  use amalgamation_eq.
  use (sheaf_amalgamation_unique HΓ H).
  - exact zz.
  - intros y f p.
    exact (amalgamation_dep_restr aa f p).
  - intros y f p.
    exact (amalgamation_restr (sheaf_amalgamation HΓ H zz) f p).
Qed.

Definition is_dep_sheaf_psh_to_dep_psh
           {C : site}
           {Γ : C^op ⟶ HSET}
           (HΓ : is_sheaf Γ)
  : is_dep_sheaf (psh_to_dep_psh Γ).
Proof.
  intros x ω H z a zz.
  use make_iscontr.
  - exact (sheaf_amalgamation HΓ H zz).
  - apply is_dep_sheaf_psh_to_dep_psh_unique.
Defined.

(** * 7. The total space of a dependent sheaf (context extension) *)
Definition total_psh_matching_family_pr1
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           {x : C}
           {ω : sieve x}
           (z : matching_family (total_psh A) ω)
  : matching_family Γ ω.
Proof.
  use make_matching_family.
  - exact (λ y f p, pr1 (z y f p)).
  - intros y₁ y₂ f₁ f₂ g p q₁ q₂ ; cbn.
    exact (dep_psh_total_space_pr1_path _ (matching_family_restr z p q₁ q₂)).
Defined.

Definition total_psh_matching_family_pr2
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           {x : C}
           {ω : sieve x}
           (z : matching_family (total_psh A) ω)
  : matching_family_dep A (total_psh_matching_family_pr1 z).
Proof.
  use make_matching_family_dep.
  - exact (λ y f p, pr2 (z y f p)).
  - abstract
      (intros y₁ y₂ f₁ f₂ g p q₁ q₂ ; cbn ;
       refine (_ @ dep_psh_total_space_pr2_path _ (matching_family_restr z p q₁ q₂)) ;
       cbn ;
       rewrite dep_psh_mor_comp' ;
       use dep_psh_mor_path_eq ;
       rewrite id_left ;
       apply idpath).
Defined.

Definition make_matching_family_total_psh
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           {x : C}
           {ω : sieve x}
           (z : matching_family Γ ω)
           (zz : matching_family_dep A z)
  : matching_family (total_psh A) ω.
Proof.
  use make_matching_family.
  - exact (λ y f p, z y f p ,, zz y f p).
  - intros y₁ y₂ f₁ f₂ g p q₁ q₂.
    use dep_psh_total_space_path.
    + exact (matching_family_restr z p q₁ q₂).
    + abstract
        (refine (_ @ matching_family_dep_restr zz p q₁ q₂) ;
         cbn;
         rewrite dep_psh_mor_comp' ;
         use dep_psh_mor_path_eq ;
         apply id_left).
Defined.

Definition make_amalgamation_total_psh
           {C : site}
           {Γ : C^op ⟶ HSET}
           {A : dep_psh Γ}
           {x : C}
           {ω : sieve x}
           {z : matching_family Γ ω}
           {a : amalgamation z}
           {zz : matching_family_dep A z}
           (aa : amalgamation_dep a zz)
  : amalgamation (make_matching_family_total_psh z zz).
Proof.
  use make_amalgamation.
  - simple refine (_ ,, _).
    + exact a.
    + exact aa.
  - intros y f p.
    use dep_psh_total_space_path.
    + exact (amalgamation_restr a f p).
    + refine (_ @ amalgamation_dep_restr aa f p).
      cbn.
      rewrite dep_psh_mor_comp' ;
         use dep_psh_mor_path_eq ;
         apply id_left.
Defined.

Section TotalSpace.
  Context {C : site}
          {Γ : C^op ⟶ HSET}
          (HΓ : is_sheaf Γ)
          {A : dep_psh Γ}
          (HA : is_dep_sheaf A)
          {x : C}
          {ω : sieve x}
          (p : C x ω)
          (z : matching_family (total_psh A) ω).

  Definition total_sheaf_amalgamation_ob
    : (total_psh A x : hSet).
  Proof.
    simple refine (_ ,, _).
    - exact (sheaf_amalgamation HΓ p (total_psh_matching_family_pr1 z)).
    - exact (dep_sheaf_amalgamation HA p _ _ (total_psh_matching_family_pr2 z)).
  Defined.

  Proposition total_sheaf_amalgamation_law
    : amalgamation_law z total_sheaf_amalgamation_ob.
  Proof.
    intros y f q.
    use dep_psh_total_space_path.
    - exact (amalgamation_restr
               (sheaf_amalgamation HΓ p (total_psh_matching_family_pr1 z))
               f q).
    - cbn.
      rewrite dep_psh_mor_comp'.
      refine (_ @ dep_sheaf_amalgamation_restr
                    HA p
                    _ _
                    (total_psh_matching_family_pr2 z) q).
      use dep_psh_mor_path_eq.
      apply id_left.
  Qed.

  Definition total_sheaf_amalgamation
    : amalgamation z.
  Proof.
    use make_amalgamation.
    - exact total_sheaf_amalgamation_ob.
    - exact total_sheaf_amalgamation_law.
  Defined.

  Proposition total_sheaf_amalgamation_unique
              (a : amalgamation z)
    : a = total_sheaf_amalgamation.
  Proof.
    use amalgamation_eq.
    use dep_psh_total_space_path.
    - use (sheaf_amalgamation_unique HΓ p).
      + exact (total_psh_matching_family_pr1 z).
      + intros y f q ; cbn.
        exact (dep_psh_total_space_pr1_path _ (amalgamation_restr a f q)).
      + intros y f q ; cbn.
        exact (amalgamation_restr
                 (sheaf_amalgamation HΓ p (total_psh_matching_family_pr1 z))
                 f q).
    - use (dep_sheaf_amalgamation_unique HA p).
      + exact (total_psh_matching_family_pr2 z).
      + intros y f q ; cbn.
        refine (_ @ dep_psh_total_space_pr2_path _ (amalgamation_restr a f q)).
        cbn.
        rewrite !dep_psh_mor_comp'.
        use dep_psh_mor_path_eq.
        rewrite id_left, id_right.
        apply idpath.
      + intros y f q ; cbn.
        refine (_ @ dep_sheaf_amalgamation_restr HA p _ _ (total_psh_matching_family_pr2 z) q).
        use dep_psh_mor_path_eq.
        apply idpath.
  Qed.
End TotalSpace.

Definition is_sheaf_total_psh
           {C : site}
           {Γ : C^op ⟶ HSET}
           (HΓ : is_sheaf Γ)
           {A : dep_psh Γ}
           (HA : is_dep_sheaf A)
  : is_sheaf (total_psh A).
Proof.
  intros x ω p z.
  use make_iscontr.
  - exact (total_sheaf_amalgamation HΓ HA p z).
  - exact (total_sheaf_amalgamation_unique HΓ HA p z).
Defined.

Definition total_sheaf
           {C : site}
           {Γ : sheaf C}
           (A : dep_sheaf Γ)
  : sheaf C.
Proof.
  use make_sheaf.
  - exact (total_psh A).
  - use is_sheaf_total_psh.
    + apply is_sheaf_sheaf.
    + apply is_dep_sheaf_dep_sheaf.
Defined.

Definition total_sheaf_pr
           {C : site}
           {Γ : sheaf C}
           (A : dep_sheaf Γ)
  : sheaf_nat_trans (total_sheaf A) Γ.
Proof.
  use make_sheaf_nat_trans.
  exact (total_psh_pr A).
Defined.

(** * 8. Fiberwise limits for dependent sheaves *)
Definition cleaving_disp_cat_of_dep_sheaves
           (C : site)
  : cleaving (disp_cat_of_dep_sheaves C).
Proof.
  use cleaving_full_sub_disp_cat.
  - exact (cleaving_disp_cat_dep_psh C).
  - exact (λ Γ₁ Γ₂ s A HΓ₁ HΓ₂ HA, is_dep_sheaf_dep_psh_subst _ HA).
Defined.

Proposition fiber_functor_from_cleaving_dep_sheaf
            {C : site}
            {Γ₁ Γ₂ : sheaf C}
            (s : sheaf_nat_trans Γ₁ Γ₂)
            {A B : dep_sheaf Γ₂}
            (τ : dep_psh_nat_trans A B (nat_trans_id _))
            {x : C}
            {xx : (Γ₁ x : hSet)}
            (a : A x (s x xx))
            (HD := cleaving_disp_cat_of_dep_sheaves C)
  :  (# (fiber_functor_from_cleaving _ HD s) τ : dep_psh_nat_trans _ _ _) x xx a
     =
     τ x (s x xx) a.
Proof.
  etrans.
  {
    exact (maponpaths
             (λ (ζ : dep_psh_nat_trans (dep_sheaf_subst s A) _ _), ζ x xx a)
             (transportf_full_sub_disp_cat
                (disp_cat_dep_psh C)
                is_sheaf
                (λ Γ HΓ A, is_dep_sheaf A)
                (id_right _ @ !(id_left _))
                _)).
  }
  rewrite transportf_dep_psh_nat_trans.
  apply (transportf_set (B x)).
  apply setproperty.
Qed.

Definition fiberwise_terminal_disp_cat_of_dep_sheaves
           (C : site)
  : fiberwise_terminal (cleaving_disp_cat_of_dep_sheaves C).
Proof.
  use full_sub_disp_cat_fiberwise_terminal.
  - exact (dep_psh_fiberwise_terminal C).
  - exact (λ Γ HΓ, is_dep_sheaf_unit_dep_psh Γ).
Defined.

Definition dep_sheaves_terminal
           {C : site}
           (Γ : sheaf C)
  : Terminal ((disp_cat_of_dep_sheaves C)[{Γ}]).
Proof.
  exact (terminal_in_fib (fiberwise_terminal_disp_cat_of_dep_sheaves C) Γ).
Defined.

Definition dep_sheaves_preserves_terminal
           {C : site}
           {Γ₁ Γ₂ : sheaf C}
           (s : sheaf_nat_trans Γ₁ Γ₂)
  : preserves_terminal
      (fiber_functor_from_cleaving
         (disp_cat_of_dep_sheaves C)
         (cleaving_disp_cat_of_dep_sheaves C)
         s)
  := pr2 (fiberwise_terminal_disp_cat_of_dep_sheaves C) Γ₁ Γ₂ s.

Definition fiberwise_binproducts_disp_cat_of_dep_sheaves
           (C : site)
  : fiberwise_binproducts (cleaving_disp_cat_of_dep_sheaves C).
Proof.
  use full_sub_disp_cat_fiberwise_binproducts.
  - exact (dep_psh_fiberwise_binproducts C).
  - exact (λ Γ HΓ A B HA HB, is_dep_sheaf_prod_dep_psh HA HB).
Defined.

Definition fiberwise_equalizers_disp_cat_of_dep_sheaves
           (C : site)
  : fiberwise_equalizers (cleaving_disp_cat_of_dep_sheaves C).
Proof.
  use full_sub_disp_cat_fiberwise_equalizers.
  - exact (dep_psh_fiberwise_equalizers C).
  - exact (λ Γ HΓ A B HA HB ff gg, is_dep_sheaf_equalizer_dep_psh ff gg HA HB).
Defined.

(** * 9. The inclusion preserves fiberwise limits *)
Definition preserves_terminal_dep_sheaf_incl
           {C : site}
           (Γ : sheaf C)
  : preserves_terminal (fiber_functor (dep_sheaf_incl C) Γ).
Proof.
  use preserves_terminal_if_preserves_chosen.
  {
    apply fiberwise_terminal_disp_cat_of_dep_sheaves.
  }
  use iso_to_Terminal.
  {
    apply dep_psh_fiber_terminal.
  }
  apply identity_z_iso.
Qed.

Definition preserves_binproduct_dep_sheaf_incl
           {C : site}
           (Γ : sheaf C)
  : preserves_binproduct (fiber_functor (dep_sheaf_incl C) Γ).
Proof.
  use preserves_binproduct_if_preserves_chosen.
  {
    apply fiberwise_binproducts_disp_cat_of_dep_sheaves.
  }
  intros A B.
  use (isBinProduct_z_iso (isBinProduct_BinProduct _ (dep_psh_fiber_binproducts Γ _ _))).
  - apply identity_z_iso.
  - refine (_ @ !(id_left _)).
    apply fiber_functor_dep_sheaf_incl.
  - refine (_ @ !(id_left _)).
    apply fiber_functor_dep_sheaf_incl.
Qed.

Definition preserves_equalizer_dep_sheaf_incl
           {C : site}
           (Γ : sheaf C)
  : preserves_equalizer (fiber_functor (dep_sheaf_incl C) Γ).
Proof.
  use preserves_equalizer_if_preserves_chosen.
  {
    apply fiberwise_equalizers_disp_cat_of_dep_sheaves.
  }
  intros A B τ₁ τ₂ p.
  simple refine (isEqualizer_eq
                   _ _
                   (!(fiber_functor_dep_sheaf_incl _))
                   (!(fiber_functor_dep_sheaf_incl _))
                   (!(fiber_functor_dep_sheaf_incl _))
                   _).
  - abstract
      (use dep_psh_nat_trans_eq ;
       intros x xx a ;
       refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
       refine (_ @ !(dep_psh_fiber_comp _ _ _ _)) ;
       exact (pr2 a)).
  - use (isEqualizer_z_iso (isEqualizer_Equalizer (dep_psh_fiber_equalizers Γ _ _ _ _))).
    + apply identity_z_iso.
    + refine (!_).
      apply id_left.
Qed.

Definition preserves_pullback_dep_sheaf_incl
           {C : site}
           (Γ : sheaf C)
  : preserves_pullback (fiber_functor (dep_sheaf_incl C) Γ).
Proof.
  use preserves_pullback_from_binproduct_equalizer.
  - apply fiberwise_binproducts_disp_cat_of_dep_sheaves.
  - apply fiberwise_equalizers_disp_cat_of_dep_sheaves.
  - apply preserves_binproduct_dep_sheaf_incl.
  - apply preserves_equalizer_dep_sheaf_incl.
Qed.

Definition preserves_monic_dep_sheaf_incl
           {C : site}
           {Γ : sheaf C}
           {A B : dep_sheaf Γ}
           (τ : dep_psh_nat_trans A B (nat_trans_id _))
           (Hτ : isMonic (C := (disp_cat_of_dep_sheaves C)[{Γ}]) τ)
  : isMonic (C := (disp_cat_dep_psh C)[{pr1 Γ}]) τ.
Proof.
  refine (transportf
            (λ τ, isMonic τ)
            _
            (is_monic_functor_preserves_pb (preserves_pullback_dep_sheaf_incl Γ) τ Hτ)).
  apply fiber_functor_dep_sheaf_incl.
Qed.

(** * 10. Sections of the projection *)
Definition sheaf_section_to_term
           {C : site}
           {Γ : sheaf C}
           {A : dep_sheaf Γ}
           (t : section_of_mor (C := cat_of_sheaves C) (total_sheaf_pr A))
  : psh_term A.
Proof.
  use make_psh_term.
  - exact (λ x xx, psh_section_pt (functor_on_section (sheaf_incl C) t) xx).
  - exact (psh_section_natural (functor_on_section (sheaf_incl C) t)).
Defined.

Definition sheaf_term_to_section
           {C : site}
           {Γ : sheaf C}
           {A : dep_sheaf Γ}
           (t : psh_term A)
  : section_of_mor (C := cat_of_sheaves C) (total_sheaf_pr A).
Proof.
  use make_section_of_mor.
  - use make_sheaf_nat_trans.
    use make_nat_trans.
    + exact (λ x xx, xx ,, t x xx).
    + abstract
        (intros x y f ;
         use funextsec ;
         intro xx ; cbn ;
         apply maponpaths ;
         exact (psh_term_naturality t f xx)).
  - abstract
      (use sheaf_nat_trans_eq ;
       use nat_trans_eq ; [ apply homset_property | ] ;
       intros x ;
       apply idpath).
Defined.

Definition sheaf_section_weq
           {C : site}
           {Γ : sheaf C}
           (A : dep_sheaf Γ)
  : section_of_mor (C := cat_of_sheaves C) (total_sheaf_pr A)
    ≃
    psh_term A.
Proof.
  use weq_iso.
  - exact sheaf_section_to_term.
  - exact sheaf_term_to_section.
  - abstract
      (intros t ;
       use eq_section_of_mor ;
       use sheaf_nat_trans_eq ;
       use nat_trans_eq ; [ apply homset_property | ] ;
       intro x ; cbn ;
       use funextsec ;
       intro xx ;
       use dep_psh_total_space_path ;
       [ exact (!(eqtohomot
                    (nat_trans_eq_pointwise
                       (maponpaths pr1 (section_of_mor_eq t))
                       x)
                    xx))
       | ] ;
       cbn ;
       unfold psh_section_pt ;
       rewrite dep_psh_mor_comp' ;
       apply dep_psh_mor_id' ;
       rewrite id_left ;
       apply idpath).
  - abstract
      (intros t ;
       use psh_term_eq ;
       intros x xx ;
       unfold psh_section_pt ; cbn ;
       apply dep_psh_mor_id).
Defined.
