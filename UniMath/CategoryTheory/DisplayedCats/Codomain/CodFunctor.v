(*******************************************************************************************

 Pseudofunctoriality of the arrow category

 We have a pseudofunctor that assigns to every category its arrow category. In this file,
 we look at this construction.

 We show that whenever we have a functor `F` from a category `C₁` to a category `C₂`, then we
 also have a displayed functor between their codomain displayed categories. The obtained
 functor is cartesian if `F` preserves pullbacks, and we show that this functor preserves
 finite limits in the fiber category. We also show how a natural transformation gives rise
 to a displayed natural transformation.

 Contents
 1. Displayed functor between codomain displayed categories
 2. Displayed natural transformation between codomain displayed categories
 3. Cartesianness of the displayed functor
 4. Preservation of limits
 5. Preservation of colimits
 6. Naturality for the slice of terminal objects

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodLimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.

Local Open Scope cat.

(** * 1. Displayed functor between codomain displayed categories *)
Definition disp_codomain_functor_data
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : disp_functor_data F (disp_codomain C₁) (disp_codomain C₂).
Proof.
  simple refine (_ ,, _).
  - exact (λ x yf, F (pr1 yf) ,, #F (pr2 yf)).
  - refine (λ x₁ x₂ yf₁ yf₂ g hp, #F (pr1 hp) ,, _).
    abstract
      (cbn ;
       rewrite <- !functor_comp ;
       apply maponpaths ;
       exact (pr2 hp)).
Defined.

Proposition disp_codomain_functor_axioms
            {C₁ C₂ : category}
            (F : C₁ ⟶ C₂)
  : disp_functor_axioms (disp_codomain_functor_data F).
Proof.
  split.
  - intros x yf.
    use eq_cod_mor.
    rewrite transportb_cod_disp.
    cbn.
    rewrite functor_id.
    apply idpath.
  - intros x₁ x₂ y₃ yf₁ yf₂ yf₃ f₁ f₂ gp₁ gp₂.
    use eq_cod_mor.
    rewrite transportb_cod_disp.
    cbn.
    rewrite functor_comp.
    apply idpath.
Qed.

Definition disp_codomain_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : disp_functor F (disp_codomain C₁) (disp_codomain C₂).
Proof.
  simple refine (_ ,, _).
  - exact (disp_codomain_functor_data F).
  - exact (disp_codomain_functor_axioms F).
Defined.

Proposition disp_codomain_fiber_functor_mor
            {C₁ C₂ : category}
            (F : C₁ ⟶ C₂)
            (x : C₁)
            {f g : C₁/x}
            (h : f --> g)
  : dom_mor (#(fiber_functor (disp_codomain_functor F) x) h)
    =
    #F(dom_mor h).
Proof.
  cbn ; unfold dom_mor.
  rewrite transportf_cod_disp.
  cbn.
  apply idpath.
Qed.

(** * 2. Displayed natural transformation between codomain displayed categories *)
Definition disp_codomain_nat_trans
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           (τ : F ⟹ G)
  : disp_nat_trans τ (disp_codomain_functor F) (disp_codomain_functor G).
Proof.
  simple refine (_ ,, _).
  - refine (λ y xf, τ _ ,, _).
    abstract
      (cbn ;
       apply (!(nat_trans_ax τ _ _ _))).
  - abstract
      (intros y₁ y₂ g xf₁ xf₂ p ;
       use eq_cod_mor ;
       rewrite transportb_cod_disp ;
       apply (nat_trans_ax τ _ _ _)).
Defined.

(** * 3. Cartesianness of the displayed functor *)
Definition is_cartesian_disp_codomain_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (HF : preserves_pullback F)
  : is_cartesian_disp_functor (disp_codomain_functor F).
Proof.
  intros x y f xx yy ff H.
  use isPullback_cartesian_in_cod_disp.
  exact (HF _ _ _ _ _ _ _ _ _ _ (cartesian_isPullback_in_cod_disp _ H)).
Defined.

(** * 4. Preservation of limits *)
Proposition preserves_terminal_fiber_disp_codomain_functor
            {C₁ C₂ : category}
            (F : C₁ ⟶ C₂)
            (x : C₁)
  : preserves_terminal (fiber_functor (disp_codomain_functor F) x).
Proof.
  intros y Hy.
  use isTerminal_codomain_fib ; cbn.
  use functor_on_is_z_isomorphism.
  exact (is_z_iso_from_isTerminal_codomain _ Hy).
Defined.

Proposition preserves_binproduct_fiber_disp_codomain_functor
            {C₁ C₂ : category}
            (F : C₁ ⟶ C₂)
            (HF : preserves_pullback F)
            (x : C₁)
  : preserves_binproduct (fiber_functor (disp_codomain_functor F) x).
Proof.
  intros y₁ y₂ z π₁ π₂ H.
  use isPullback_to_isBinProduct_cod_fib.
  apply isBinProduct_to_isPullback_cod_fib in H.
  use (isPullback_mor_paths _ _ _ _ _ _ (HF _ _ _ _ _ _ _ _ _ _ H)).
  - apply idpath.
  - apply idpath.
  - rewrite disp_codomain_fiber_functor_mor.
    apply idpath.
  - rewrite disp_codomain_fiber_functor_mor.
    apply idpath.
  - rewrite <- !functor_comp.
    apply maponpaths.
    exact (fib_isPullback π₁ π₂).
Qed.

Proposition preserves_equalizer_fiber_disp_codomain_functor
            {C₁ C₂ : category}
            (F : C₁ ⟶ C₂)
            (HF : preserves_equalizer F)
            (x : C₁)
  : preserves_equalizer (fiber_functor (disp_codomain_functor F) x).
Proof.
  intros y₁ y₂ z f g e p Fp H.
  assert (# F (dom_mor e) · # F (dom_mor f) = # F (dom_mor e) · # F (dom_mor g)) as q.
  {
    refine (!(functor_comp F _ _) @ _ @ functor_comp F _ _).
    apply maponpaths.
    unfold dom_mor.
    exact (!(comp_in_cod_fib _ _) @ maponpaths dom_mor p @ comp_in_cod_fib _ _).
  }
  use to_isEqualizer_cod_fib.
  - abstract
      (rewrite !disp_codomain_fiber_functor_mor ;
       exact q).
  - use (isEqualizer_eq
           _ _ _ _ _
           (HF _ _ _ _ _ _ _ _ (from_isEqualizer_cod_fib _ _ _ _ _ H))).
    + exact q.
    + rewrite disp_codomain_fiber_functor_mor.
      apply idpath.
    + rewrite disp_codomain_fiber_functor_mor.
      apply idpath.
    + rewrite disp_codomain_fiber_functor_mor.
      apply idpath.
    + unfold dom_mor.
      exact (!(comp_in_cod_fib _ _) @ maponpaths dom_mor p @ comp_in_cod_fib _ _).
Qed.

(** * 5. Preservation of colimits *)
Proposition preserves_initial_fiber_disp_codomain_functor
            {C₁ C₂ : category}
            (I : Initial C₁)
            (F : C₁ ⟶ C₂)
            (HF : preserves_initial F)
            (x : C₁)
  : preserves_initial (fiber_functor (disp_codomain_functor F) x).
Proof.
  use preserves_initial_if_preserves_chosen.
  - exact (initial_cod_fib x I).
  - use (iso_to_Initial (initial_cod_fib _ (make_Initial _ (HF _ (pr2 I))))).
    use z_iso_fiber_from_z_iso_disp.
    use make_z_iso_disp.
    + use make_cod_fib_mor.
      * apply identity.
      * abstract
          (use InitialArrowEq).
    + use is_z_iso_disp_codomain.
      apply is_z_isomorphism_identity.
Defined.

Proposition preserves_bincoproduct_fiber_disp_codomain_functor
            {C₁ C₂ : category}
            (HC₁ : BinCoproducts C₁)
            (F : C₁ ⟶ C₂)
            (HF : preserves_bincoproduct F)
            (x : C₁)
  : preserves_bincoproduct (fiber_functor (disp_codomain_functor F) x).
Proof.
  use preserves_bincoproduct_if_preserves_chosen.
  - exact (bincoproducts_cod_fib x HC₁).
  - intros y₁ y₂.
    use to_bincoproduct_slice.
    pose (HC₁ (cod_dom y₁) (cod_dom y₂)) as coprod.
    pose (HF _ _ _ _ _ (isBinCoproduct_BinCoproduct _ coprod))
      as Fcoprod.
    use (isBinCoproduct_eq_arrow _ _ Fcoprod).
    + abstract
        (rewrite disp_codomain_fiber_functor_mor ;
         apply idpath).
    + abstract
        (rewrite disp_codomain_fiber_functor_mor ;
         apply idpath).
Defined.

(** * 6. Naturality for the slice of terminal objects *)
Definition cod_fib_terminal_to_base_nat_trans
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (HF : preserves_terminal F)
           (T₁ : Terminal C₁)
           (T₂ := make_Terminal _ (HF _ (pr2 T₁)))
  : fiber_functor (disp_codomain_functor F) T₁ ∙ cod_fib_terminal_to_base T₂
    ⟹
    cod_fib_terminal_to_base T₁ ∙ F.
Proof.
  use make_nat_trans.
  - exact (λ _, identity _).
  - abstract
      (intros x y f ;
       rewrite id_right, id_left ;
       cbn ; unfold dom_mor ;
       rewrite transportf_cod_disp ;
       apply idpath).
Defined.

Definition cod_fib_terminal_to_base_nat_z_iso
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (HF : preserves_terminal F)
           (T₁ : Terminal C₁)
           (T₂ := make_Terminal _ (HF _ (pr2 T₁)))
  : nat_z_iso
      (fiber_functor (disp_codomain_functor F) T₁ ∙ cod_fib_terminal_to_base T₂)
      (cod_fib_terminal_to_base T₁ ∙ F).
Proof.
  use make_nat_z_iso.
  - exact (cod_fib_terminal_to_base_nat_trans F HF T₁).
  - intro.
    apply is_z_isomorphism_identity.
Defined.
