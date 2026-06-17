(**

 The precomposition functor for presheaves

 if we have a functor `F : C₁ ⟶ C₂`, then precomposition with `F` induces a functor
 on the categories of presheaves. This functors lifts to the presheaf model. Specifically,
 one can lift it to dependent presheaves, and one can show that it preserves the type
 formers that arise from finite limits (i.e., extensional identity, binary products, and
 ∑-types). We also show how to lift natural transformations.

 Content
 1. The precomposition functor
 2. Precomposition for dependent presheaves
 3. Preservation of comprehension
 4. Preservation of type formers
 5. Natural transformations between precomposition functors

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
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Section Precomposition.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂).

  (** * 1. The precomposition functor *)
  Definition precomp_psh_functor_data
    : functor_data (PreShv C₂) (PreShv C₁).
  Proof.
    use make_functor_data.
    - exact (λ Γ, functor_opp F ∙ Γ).
    - exact (λ Γ₁ Γ₂ s, pre_whisker (functor_opp F) s).
  Defined.

  Proposition precomp_psh_functor_laws
    : is_functor precomp_psh_functor_data.
  Proof.
    split.
    - intro Γ.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      cbn.
      intro x.
      apply idpath.
    - intros Γ₁ Γ₂ Γ₃ s₁ s₂.
      use nat_trans_eq.
      {
        apply homset_property.
      }
      cbn.
      intro x.
      apply idpath.
  Qed.

  Definition precomp_psh
    : PreShv C₂ ⟶ PreShv C₁.
  Proof.
    use make_functor.
    - exact precomp_psh_functor_data.
    - exact precomp_psh_functor_laws.
  Defined.

  Proposition preserves_terminal_precomp_psh
    : preserves_terminal precomp_psh.
  Proof.
    use preserves_terminal_if_preserves_chosen.
    {
      exact Terminal_PreShv.
    }
    unfold preserves_chosen_terminal.
    use iso_to_Terminal.
    {
      exact Terminal_PreShv.
    }
    use make_z_iso.
    - apply nat_trans_id.
    - apply nat_trans_id.
    - abstract
        (split ;
         (use nat_trans_eq ; [ apply homset_property | ]) ;
         intros ;
         apply idpath).
  Defined.

  (** * 2. Precomposition for dependent presheaves *)
  Definition precomp_dep_psh
             {Γ : C₂^op ⟶ HSET}
             (A : dep_psh Γ)
    : dep_psh (precomp_psh Γ).
  Proof.
    use make_dep_psh.
    - exact (λ (x : C₁) (xx : (Γ (F x) : hSet)), A (F x) xx).
    - exact (λ x y xx yy s p a, #d A _ p a).
    - abstract
        (cbn ;
         intros x xx p a ;
         apply dep_psh_mor_id' ;
         rewrite functor_id ;
         apply idpath).
    - abstract
        (cbn ;
         intros x y z xx yy zz s₁ s₂ p q r a ;
         rewrite dep_psh_mor_comp' ;
         use dep_psh_mor_path_eq ;
         apply functor_comp).
  Defined.

  Definition precomp_dep_psh_nat_trans
             {Γ₁ Γ₂ : C₂^op ⟶ HSET}
             {A : dep_psh Γ₁}
             {B : dep_psh Γ₂}
             {s : Γ₁ ⟹ Γ₂}
             (τ : dep_psh_nat_trans A B s)
    : dep_psh_nat_trans
        (precomp_dep_psh A)
        (precomp_dep_psh B)
        (pre_whisker (functor_opp_data F) s).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx a, τ (F x) xx a).
    - abstract
        (intros x y xx yy f p q a ;
         cbn in * ;
         exact (dep_psh_nat_trans_ax τ (#F f) p q a)).
  Defined.

  Definition precomp_dep_psh_disp_functor_data
    : disp_functor_data
        precomp_psh
        (disp_cat_dep_psh _)
        (disp_cat_dep_psh _).
  Proof.
    simple refine (_ ,, _).
    - exact (λ Γ A, precomp_dep_psh A).
    - exact (λ Γ₁ Γ₂ A B s τ, precomp_dep_psh_nat_trans τ).
  Defined.

  Proposition precomp_dep_psh_disp_functor_axioms
    : disp_functor_axioms precomp_dep_psh_disp_functor_data.
  Proof.
    split.
    - intros Γ A ; cbn in *.
      use dep_psh_nat_trans_eq.
      intros x xx a.
      rewrite transportb_dep_psh_nat_trans.
      refine (!_).
      use (transportf_set (A (F x))).
      apply setproperty.
    - intros Γ₁ Γ₂ Γ₃ A₁ A₂ A₃ s₁ s₂ τ₁ τ₂ ; cbn in *.
      use dep_psh_nat_trans_eq.
      intros x xx a.
      rewrite transportb_dep_psh_nat_trans.
      refine (!_).
      use (transportf_set (A₃ (F x))).
      apply setproperty.
  Qed.

  Definition precomp_dep_psh_disp_functor
    : disp_functor
        precomp_psh
        (disp_cat_dep_psh _)
        (disp_cat_dep_psh _).
  Proof.
    simple refine (_ ,, _).
    - exact precomp_dep_psh_disp_functor_data.
    - exact precomp_dep_psh_disp_functor_axioms.
  Defined.

  Proposition precomp_dep_psh_disp_functor_mor
              {Γ : C₂^op ⟶ HSET}
              {A B : dep_psh Γ}
              (τ : dep_psh_nat_trans A B (nat_trans_id _))
              {x : C₁}
              {xx : (Γ (F x) : hSet)}
              (a : A (F x) xx)
    : (#(fiber_functor precomp_dep_psh_disp_functor Γ) τ
        : dep_psh_nat_trans _ _ _) x xx a
      =
      τ _ xx a.
  Proof.
    cbn.
    rewrite transportf_dep_psh_nat_trans.
    apply (transportf_set (B (F x))).
    apply setproperty.
  Qed.

  Section CartesianPrecomp.
    Context {Γ₁ : C₁^op ⟶ HSET}
            {Γ₂ Γ₃ : C₂^op ⟶ HSET}
            {A : dep_psh Γ₁}
            {B : dep_psh Γ₃}
            (s₁ : Γ₁ ⟹ functor_opp F ∙ Γ₂)
            (s₂ : Γ₂ ⟹ Γ₃)
            (τ : dep_psh_nat_trans
                   A
                   (precomp_dep_psh B)
                   (nat_trans_comp
                      _ _ _
                      s₁
                      (pre_whisker (functor_opp_data F) s₂))).

    Definition is_cartesian_precomp_dep_psh_disp_functor_factor
      : dep_psh_nat_trans A (precomp_dep_psh (dep_psh_subst s₂ B)) s₁.
    Proof.
      use make_dep_psh_nat_trans.
      - exact (λ x xx a, τ x xx a).
      - abstract
          (intros x y xx yy f p q a ; cbn ;
           exact (dep_psh_nat_trans_ax τ f p _ a)).
    Defined.

    Proposition is_cartesian_precomp_dep_psh_disp_functor_factor_eq
      : dep_psh_comp_nat_trans
          is_cartesian_precomp_dep_psh_disp_functor_factor
          (precomp_dep_psh_nat_trans (dep_psh_subst_nat_trans s₂ B))
        =
        τ.
    Proof.
      use dep_psh_nat_trans_eq.
      intros x xx a ; cbn.
      apply idpath.
    Qed.
  End CartesianPrecomp.

  Proposition is_cartesian_precomp_dep_psh_disp_functor
    : is_cartesian_disp_functor precomp_dep_psh_disp_functor.
  Proof.
    use is_cartesian_disp_functor_chosen_lifts.
    {
      exact (cleaving_disp_cat_dep_psh C₂).
    }
    intros Γ₂ Γ₃ s₂ B Γ₁ s₁ A τ.
    use make_iscontr.
    - simple refine (_ ,, _).
      + exact (is_cartesian_precomp_dep_psh_disp_functor_factor s₁ s₂ τ).
      + exact (is_cartesian_precomp_dep_psh_disp_functor_factor_eq s₁ s₂ τ).
    - abstract
        (intros τ' ;
         use subtypePath ;
         [ intro ; apply homsets_disp | ] ;
         use dep_psh_nat_trans_eq ;
         intros x xx a ; cbn ;
         exact (maponpaths (λ (z : dep_psh_nat_trans _ _ _), z x xx a) (pr2 τ'))).
  Defined.

  (** * 3. Preservation of comprehension *)
  Definition precomp_dep_psh_comprehension_nat_trans
             {Γ : C₂^op ⟶ HSET}
             (A : dep_psh Γ)
    : functor_opp F ∙ total_psh A
      ⟹
      total_psh (precomp_dep_psh A).
  Proof.
    use make_nat_trans.
    - exact (λ x xx, xx).
    - abstract
        (intros x y f ; cbn ;
         apply idpath).
  Defined.

  Definition precomp_dep_psh_disp_functor_comprehension
    : disp_nat_trans
        (nat_trans_id _)
        (disp_functor_composite
           (dep_psh_comprehension C₂)
           (disp_codomain_functor precomp_psh))
        (disp_functor_composite
           precomp_dep_psh_disp_functor
           (dep_psh_comprehension C₁)).
  Proof.
    simple refine (_ ,, _).
    - refine (λ Γ A, precomp_dep_psh_comprehension_nat_trans A ,, _).
      abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         apply idpath).
    - abstract
        (intros Γ₁ Γ₂ s A₁ A₂ τ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         refine (_ @ !(transportb_cod_disp _ _ _)) ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         apply idpath).
  Defined.

  Definition precomp_dep_psh_disp_functor_comprehension_z_iso
             {Γ : C₂^op ⟶ HSET}
             (A : dep_psh Γ)
    : is_z_isomorphism
        (C := PreShv C₁)
        (precomp_dep_psh_comprehension_nat_trans A).
  Proof.
    use nat_trafo_z_iso_if_pointwise_z_iso.
    intro x.
    use make_is_z_isomorphism.
    - exact (λ x, x).
    - abstract
        (split ; apply idpath).
  Defined.

  (** * 4. Preservation of type formers *)
  Definition precomp_dep_psh_disp_functor_preserves_terminal
             (Γ : C₂^op ⟶ HSET)
    : preserves_terminal (fiber_functor precomp_dep_psh_disp_functor Γ).
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
    - apply nat_trans_id.
    - apply nat_trans_id.
    - abstract
        (split ;
         use dep_psh_nat_trans_eq ;
         intros x xx a ;
         exact (dep_psh_fiber_comp _ _ _ _)).
  Defined.

  Definition precomp_dep_psh_disp_functor_preserves_binproduct_mor
             {Γ : C₂^op ⟶ HSET}
             (A B : dep_psh Γ)
    : dep_psh_nat_trans
        (precomp_dep_psh (prod_dep_psh A B))
        (prod_dep_psh (precomp_dep_psh A) (precomp_dep_psh B))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx ab, ab).
    - abstract
        (intros x y xx yy f p q a ; cbn ;
         use pathsdirprod ;
         use dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition precomp_dep_psh_disp_functor_preserves_binproduct_inv
             {Γ : C₂^op ⟶ HSET}
             (A B : dep_psh Γ)
    : dep_psh_nat_trans
        (prod_dep_psh (precomp_dep_psh A) (precomp_dep_psh B))
        (precomp_dep_psh (prod_dep_psh A B))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx ab, ab).
    - abstract
        (intros x y xx yy f p q a ; cbn ;
         use pathsdirprod ;
         use dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition precomp_dep_psh_disp_functor_preserves_binproduct
             (Γ : C₂^op ⟶ HSET)
    : preserves_binproduct (fiber_functor precomp_dep_psh_disp_functor Γ).
  Proof.
    use preserves_binproduct_if_preserves_chosen.
    {
      apply dep_psh_fiber_binproducts.
    }
    intros A B.
    use (isBinProduct_z_iso (isBinProduct_BinProduct _ (dep_psh_fiber_binproducts _ _ _))).
    - use make_z_iso.
      + exact (precomp_dep_psh_disp_functor_preserves_binproduct_mor A B).
      + exact (precomp_dep_psh_disp_functor_preserves_binproduct_inv A B).
      + abstract
          (split ;
           use dep_psh_nat_trans_eq ;
           intros x xx a ;
           exact (dep_psh_fiber_comp _ _ _ _)).
    - abstract
        (use dep_psh_nat_trans_eq ;
         intros x xx a ;
         rewrite precomp_dep_psh_disp_functor_mor ;
         rewrite dep_psh_fiber_comp ;
         cbn ;
         apply idpath).
    - abstract
        (use dep_psh_nat_trans_eq ;
         intros x xx a ;
         rewrite precomp_dep_psh_disp_functor_mor ;
         rewrite dep_psh_fiber_comp ;
         cbn ;
         apply idpath).
  Defined.

  Definition precomp_dep_psh_disp_functor_preserves_equalizer_mor
             {Γ : C₂^op ⟶ HSET}
             {A B : dep_psh Γ}
             {τ₁ τ₂ : dep_psh_nat_trans A B (nat_trans_id _)}
             (p : # (fiber_functor precomp_dep_psh_disp_functor Γ)
                    (equalizer_dep_psh_arrow τ₁ τ₂)
                  · # (fiber_functor precomp_dep_psh_disp_functor Γ) τ₁
                  =
                  # (fiber_functor precomp_dep_psh_disp_functor Γ)
                    (equalizer_dep_psh_arrow τ₁ τ₂)
                  · # (fiber_functor precomp_dep_psh_disp_functor Γ) τ₂)
    : dep_psh_nat_trans
        (precomp_dep_psh (equalizer_dep_psh τ₁ τ₂))
        (equalizer_dep_psh
           (# (fiber_functor precomp_dep_psh_disp_functor Γ) τ₁)
           (# (fiber_functor precomp_dep_psh_disp_functor Γ) τ₂))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - refine (λ x xx a, pr1 a ,, _).
      abstract
        (cbn -[fiber_functor] ;
         refine (precomp_dep_psh_disp_functor_mor τ₁ (pr1 a) @ _) ;
         refine (_ @ !(precomp_dep_psh_disp_functor_mor τ₂ (pr1 a))) ;
         exact (pr2 a)).
    - abstract
        (intros x y xx yy f q₁ q₂ a ; cbn ;
         use subtypePath ; [ intro ; apply setproperty | ] ;
         cbn ;
         use dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition precomp_dep_psh_disp_functor_preserves_equalizer_inv
             {Γ : C₂^op ⟶ HSET}
             {A B : dep_psh Γ}
             {τ₁ τ₂ : dep_psh_nat_trans A B (nat_trans_id _)}
             (p : # (fiber_functor precomp_dep_psh_disp_functor Γ)
                    (equalizer_dep_psh_arrow τ₁ τ₂)
                  · # (fiber_functor precomp_dep_psh_disp_functor Γ) τ₁
                  =
                  # (fiber_functor precomp_dep_psh_disp_functor Γ)
                    (equalizer_dep_psh_arrow τ₁ τ₂)
                  · # (fiber_functor precomp_dep_psh_disp_functor Γ) τ₂)
    : dep_psh_nat_trans
        (equalizer_dep_psh
           (# (fiber_functor precomp_dep_psh_disp_functor Γ) τ₁)
           (# (fiber_functor precomp_dep_psh_disp_functor Γ) τ₂))
        (precomp_dep_psh (equalizer_dep_psh τ₁ τ₂))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - refine (λ x xx a, pr1 a ,, _).
      abstract
        (cbn -[fiber_functor] ;
         refine (!(precomp_dep_psh_disp_functor_mor τ₁ (pr1 a)) @ _) ;
         refine (_ @ precomp_dep_psh_disp_functor_mor τ₂ (pr1 a)) ;
         exact (pr2 a)).
    - abstract
        (intros x y xx yy f q₁ q₂ a ; cbn ;
         use subtypePath ; [ intro ; apply setproperty | ] ;
         cbn ;
         use dep_psh_mor_path_eq ;
         apply idpath).
  Defined.

  Definition precomp_dep_psh_disp_functor_preserves_equalizer
             (Γ : C₂^op ⟶ HSET)
    : preserves_equalizer (fiber_functor precomp_dep_psh_disp_functor Γ).
  Proof.
    use preserves_equalizer_if_preserves_chosen.
    {
      apply dep_psh_fiber_equalizers.
    }
    intros A B τ₁ τ₂ p.
    use (isEqualizer_z_iso (isEqualizer_Equalizer (dep_psh_fiber_equalizers _ _ _ _ _))).
    - use make_z_iso.
      + exact (precomp_dep_psh_disp_functor_preserves_equalizer_mor p).
      + exact (precomp_dep_psh_disp_functor_preserves_equalizer_inv p).
      + abstract
          (split ;
           use dep_psh_nat_trans_eq ;
           intros x xx a ;
           refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
           (use subtypePath ; [ intro ; apply setproperty | ]) ;
           apply idpath).
    - abstract
        (use dep_psh_nat_trans_eq ;
         intros x xx a ;
         rewrite precomp_dep_psh_disp_functor_mor ;
         refine (_ @ !(dep_psh_fiber_comp _ _ _ _)) ;
         cbn ;
         apply idpath).
  Defined.
End Precomposition.

Section PrecompositionNatTrans.
  Context {C₁ C₂ : category}
          {F G : C₁ ⟶ C₂}
          (τ : F ⟹ G).

  (** * 5. Natural transformations between precomposition functors *)
  Definition precomp_psh_nat_trans
    : precomp_psh G ⟹ precomp_psh F.
  Proof.
    use make_nat_trans.
    - exact (λ Γ, post_whisker (op_nt τ) Γ).
    - abstract
        (intros Γ₁ Γ₂ s ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ;
         use funextsec ;
         intro xx ;
         cbn in * ;
         exact (!(eqtohomot (nat_trans_ax s _ _ (τ x)) xx))).
  Defined.

  Definition precomp_psh_disp_nat_trans_pt
             {Γ : C₂^op ⟶ HSET}
             (A : dep_psh Γ)
    : dep_psh_nat_trans
        (precomp_dep_psh G A)
        (precomp_dep_psh F A)
        (post_whisker (op_nt τ) Γ).
  Proof.
    use make_dep_psh_nat_trans.
    - exact (λ x xx a, #d A (τ x) (idpath _) a).
    - abstract
        (intros x y xx yy f p q a ;
         cbn in * ;
         rewrite !dep_psh_mor_comp' ;
         use dep_psh_mor_path_eq ;
         exact (!(nat_trans_ax τ _ _ f))).
  Defined.

  Definition precomp_psh_disp_nat_trans_data
    : disp_nat_trans_data
        precomp_psh_nat_trans
        (precomp_dep_psh_disp_functor G)
        (precomp_dep_psh_disp_functor F)
    := λ Γ A, precomp_psh_disp_nat_trans_pt A.

  Arguments precomp_psh_disp_nat_trans_data /.

  Proposition precomp_psh_disp_nat_trans_axioms
    : disp_nat_trans_axioms precomp_psh_disp_nat_trans_data.
  Proof.
    intros Γ₁ Γ₂ s A B θ.
    use dep_psh_nat_trans_eq.
    intros x xx a.
    rewrite transportb_dep_psh_nat_trans.
    cbn in *.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (dep_psh_nat_trans_ax' θ (τ x) (idpath _) a).
    }
    etrans.
    {
      apply transport_dep_psh_mor.
    }
    cbn.
    rewrite !dep_psh_mor_comp'.
    use dep_psh_mor_path_eq.
    apply id_left.
  Qed.

  Definition precomp_psh_disp_nat_trans
    : disp_nat_trans
        precomp_psh_nat_trans
        (precomp_dep_psh_disp_functor G)
        (precomp_dep_psh_disp_functor F).
  Proof.
    simple refine (_ ,, _).
    - exact precomp_psh_disp_nat_trans_data.
    - exact precomp_psh_disp_nat_trans_axioms.
  Defined.
End PrecompositionNatTrans.
