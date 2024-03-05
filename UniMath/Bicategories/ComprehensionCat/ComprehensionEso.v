(*******************************************************************************************

 The comprehension functor of full DFL comprehension categories is essentially surjective

 In this file, we prove that the comprehension functor of full DFL comprehension categories
 is essentially surjective. This corresponds to Proposition 2.9 in the paper 'The biequivalence
 of locally cartesian closed categories and Martin-Löf type theories' by Clairambault and
 Dybjer. While the construction is essentially the same, there are quite some differences in
 the notation. Here the notation and vocabulary is closer to category theory, whereas the
 language in Clairambault and Dybjer is closer to syntax. This is due to the fact that
 different formalisms are used.

 References
 - 'The biequivalence of locally cartesian closed categories and Martin-Löf type theories'
   by Clairambault and Dybjer.

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.DisplayedCats.EquivalenceOverId.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseTerminal.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.FiberwiseEqualizers.
Require Import UniMath.CategoryTheory.DisplayedCats.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.FullyFaithfulDispFunctor.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCatNotations.

Local Open Scope cat.
Local Open Scope comp_cat.

Section ComprehensionEso.
  Context (C : dfl_full_comp_cat).

  Section Eso.
    Context {Γ Δ : C}
            (δ : Δ --> Γ).

    Let Δδ : disp_codomain C Γ := (Δ ,, δ).

    (**
       We first use democracy to obtain types representing the involved contexts
     *)
    Let DΓ : ty [] := dfl_con_to_ty Γ.
    Let DΔ : ty [] := dfl_con_to_ty Δ.

    Let γΓ : z_iso Γ ([] & DΓ)
      := dfl_con_to_z_iso Γ.
    Let γΔ : z_iso Δ ([] & DΔ)
      := dfl_con_to_z_iso Δ.

    Let DΔ' : ty Γ
      := DΔ [[ TerminalArrow _ Γ ]].
    Let DΓ' : ty (Γ & DΔ')
      := DΓ [[ TerminalArrow _ (Γ & DΔ') ]].

    (**
       Now we have two pullback squares coming from substitution
     *)
    Let HΔ : Pullback (π DΔ) (TerminalArrow [] Γ)
      := comp_cat_pullback DΔ (TerminalArrow _ Γ).

    Let HΓ : Pullback (π DΓ) (TerminalArrow [] (Γ & DΔ'))
      := comp_cat_pullback DΓ (TerminalArrow _ (Γ & DΔ')).

    (**
       We define two terms of type `Γ` in context `Γ & DΔ'`
       Of these terms, we shall take the equalizer
     *)
    Local Definition left_mor
      : C ⟦ Γ & DΔ', (Γ & DΔ') & DΓ' ⟧.
    Proof.
      use (PullbackArrow HΓ).
      - exact (π _ · γΓ).
      - apply identity.
      - apply TerminalArrowEq.
    Defined.

    Local Definition left_tm
      : comp_cat_tm (Γ & DΔ') DΓ'.
    Proof.
      use make_comp_cat_tm.
      - exact left_mor.
      - abstract
          (exact (PullbackArrow_PullbackPr2 HΓ _ _ _ _)).
    Defined.

    Local Lemma left_tm_pr1
      : left_tm · PullbackPr1 HΓ = π DΔ' · γΓ.
    Proof.
      exact (PullbackArrow_PullbackPr1 HΓ _ _ _ _).
    Qed.

    Local Lemma left_tm_pr2
      : left_tm · π _ = identity _.
    Proof.
      exact (PullbackArrow_PullbackPr2 HΓ _ _ _ _).
    Qed.

    Local Definition right_mor
      : C ⟦ Γ & DΔ', (Γ & DΔ') & DΓ' ⟧.
    Proof.
      use (PullbackArrow HΓ).
      - exact (PullbackPr1 HΔ · inv_from_z_iso γΔ · δ · γΓ).
      - apply identity.
      - apply TerminalArrowEq.
    Defined.

    Local Definition right_tm
      : comp_cat_tm (Γ & DΔ') DΓ'.
    Proof.
      use make_comp_cat_tm.
      - exact right_mor.
      - abstract
          (exact (PullbackArrow_PullbackPr2 HΓ _ _ _ _)).
    Defined.

    Local Lemma right_tm_pr1
      : right_tm · PullbackPr1 HΓ
        =
        PullbackPr1 HΔ · inv_from_z_iso γΔ · δ · γΓ.
    Proof.
      exact (PullbackArrow_PullbackPr1 HΓ _ _ _ _).
    Qed.

    Local Lemma right_tm_pr2
      : right_tm · π _ = identity _.
    Proof.
      exact (PullbackArrow_PullbackPr2 HΓ _ _ _ _).
    Qed.

    Local Definition comprehension_eso_ty_help
      : ty (Γ & DΔ')
      := EqualizerObject (dfl_ext_identity left_tm right_tm).

    (**
       Now we define a preimage of the map `δ` (which is needed for essential surjectivity).
       Intuitively, this type represents the fiber of `δ`.
       For every `y : Γ`, the inhabitants of this type are elements `x` of `Δ` such that
       `δ` maps `x` to `y`.
     *)
    Definition comprehension_eso_ty
      : ty Γ
      := dfl_sigma_type DΔ' comprehension_eso_ty_help.

    Let fib : ty Γ := comprehension_eso_ty.

    (**
       Note that since we have strong sigma types, we can make this a context extension
       with two types.
       We also give a name to this extended context.
     *)
    Let FΓ : C := Γ & DΔ' & comprehension_eso_ty_help.

    Definition comprehension_eso_ty_iso
      : z_iso FΓ (Γ & fib)
      := dfl_sigma_type_strong DΔ' comprehension_eso_ty_help.

    Definition comprehension_eso_mor_help : FΓ --> Δ
      := π _ · PullbackPr1 HΔ · inv_from_z_iso γΔ.

    Definition comprehension_eso_inv_mor_help_sub : Δ --> Γ & DΔ'.
    Proof.
      use (PullbackArrow HΔ).
      - exact γΔ.
      - exact δ.
      - apply TerminalArrowEq.
    Defined.

    Proposition comprehension_eso_inv_mor_help_sub_pr1
      : comprehension_eso_inv_mor_help_sub · PullbackPr1 HΔ = γΔ.
    Proof.
      apply (PullbackArrow_PullbackPr1 HΔ).
    Qed.

    Proposition comprehension_eso_inv_mor_help_sub_pr2
      : comprehension_eso_inv_mor_help_sub · π _ = δ.
    Proof.
      apply (PullbackArrow_PullbackPr2 HΔ).
    Qed.

    Definition comprehension_eso_inv_mor_help_tm
      : comp_cat_tm
          Δ
          (dfl_ext_identity_type
             (sub_comp_cat_tm
                left_tm
                comprehension_eso_inv_mor_help_sub)
             (sub_comp_cat_tm
                right_tm
                comprehension_eso_inv_mor_help_sub)).
    Proof.
      use dfl_ext_identity_type_tm.
      use (MorphismsIntoPullbackEqual
             (isPullback_Pullback
                (comp_cat_pullback DΓ' comprehension_eso_inv_mor_help_sub))).
      - rewrite !assoc'.
        rewrite !sub_comp_cat_tm_pr1.
        use (MorphismsIntoPullbackEqual (isPullback_Pullback HΓ)).
        + rewrite !assoc'.
          apply maponpaths.
          rewrite left_tm_pr1, right_tm_pr1.
          rewrite !assoc.
          etrans.
          {
            apply maponpaths_2.
            exact comprehension_eso_inv_mor_help_sub_pr2.
          }
          refine (!_).
          etrans.
          {
            do 3 apply maponpaths_2.
            exact comprehension_eso_inv_mor_help_sub_pr1.
          }
          rewrite z_iso_inv_after_z_iso.
          rewrite id_left.
          apply idpath.
        + rewrite !assoc'.
          etrans.
          {
            do 2 apply maponpaths.
            apply left_tm_pr2.
          }
          refine (!_).
          etrans.
          {
            do 2 apply maponpaths.
            apply right_tm_pr2.
          }
          rewrite !id_right.
          apply idpath.
      - rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply sub_comp_cat_tm_pr2.
        }
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply sub_comp_cat_tm_pr2.
        }
        apply idpath.
    Qed.

    Definition comprehension_eso_inv_mor_help : Δ --> FΓ.
    Proof.
      use sub_to_extension.
      - exact comprehension_eso_inv_mor_help_sub.
      - use dfl_ext_identity_sub_tm.
        exact comprehension_eso_inv_mor_help_tm.
    Defined.

    Definition comprehension_eso_mor
      : Γ & fib --> Δ
      := inv_from_z_iso comprehension_eso_ty_iso · comprehension_eso_mor_help.

    Proposition comprehension_eso_mor_eq
      : comprehension_eso_mor · δ = π fib.
    Proof.
      unfold comprehension_eso_mor.
      rewrite !assoc'.
      use z_iso_inv_on_right.
      refine (_ @ !(dependent_sum_map_eq _ _ _)).
      unfold comprehension_eso_mor_help.
      use (cancel_z_iso _ _ γΓ).
      rewrite !assoc'.
      pose (maponpaths
              (λ z, z · PullbackPr1 HΓ)
              (!(dfl_ext_identity_eq left_tm right_tm))) as p.
      cbn -[left_tm right_tm PullbackPr1] in p.
      rewrite !assoc' in p.
      rewrite left_tm_pr1, right_tm_pr1 in p.
      rewrite !assoc' in p.
      exact p.
    Qed.

    Definition comprehension_eso_inv_mor
      : Δ --> Γ & fib
      := comprehension_eso_inv_mor_help · comprehension_eso_ty_iso.

    (**
       The two constructed morphisms are inverses
     *)
    Proposition comprehension_eso_mor_inv_mor
      : comprehension_eso_mor · comprehension_eso_inv_mor
        =
        identity _.
    Proof.
      unfold comprehension_eso_mor, comprehension_eso_inv_mor.
      rewrite !assoc'.
      use z_iso_inv_on_right.
      rewrite id_right.
      refine (_ @ id_left _).
      rewrite !assoc.
      apply maponpaths_2.
      unfold comprehension_eso_mor_help, comprehension_eso_inv_mor_help.
      unfold sub_to_extension.
      use eq_sub_to_extension.
      -  rewrite id_left.
        rewrite !assoc'.
        etrans.
        {
          do 4 apply maponpaths.
          exact (PullbackSqrCommutes
                   (comp_cat_pullback
                      comprehension_eso_ty_help
                      comprehension_eso_inv_mor_help_sub)).
        }
        etrans.
        {
          do 3 apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          apply comp_cat_tm_eq.
        }
        rewrite id_left.
        unfold comprehension_eso_inv_mor_help_sub.
        refine (_ @ id_right _).
        use (MorphismsIntoPullbackEqual (isPullback_Pullback HΔ)).
        + rewrite !assoc'.
          rewrite (PullbackArrow_PullbackPr1 HΔ).
          rewrite z_iso_after_z_iso_inv.
          rewrite id_left, id_right.
          apply idpath.
        + rewrite !assoc'.
          rewrite (PullbackArrow_PullbackPr2 HΔ).
          rewrite id_left.
          use (cancel_z_iso _ _ γΓ).
          rewrite !assoc'.
          pose (maponpaths
                  (λ z, z · PullbackPr1 HΓ)
                  (!(dfl_ext_identity_eq left_tm right_tm))) as p.
          cbn -[left_tm right_tm PullbackPr1] in p.
          rewrite !assoc' in p.
          rewrite left_tm_pr1, right_tm_pr1 in p.
          rewrite !assoc' in p.
          cbn in p.
          exact p.
      - apply dfl_eq_subst_equalizer_tm.
    Qed.

    Proposition comprehension_eso_inv_mor_mor
      : comprehension_eso_inv_mor · comprehension_eso_mor
        =
        identity _.
    Proof.
      unfold comprehension_eso_mor, comprehension_eso_inv_mor.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite z_iso_inv_after_z_iso.
        apply id_left.
      }
      unfold comprehension_eso_mor_help, comprehension_eso_inv_mor_help.
      unfold sub_to_extension.
      unfold dfl_ext_identity_sub_tm.
      simpl.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          do 2 apply maponpaths_2.
          exact (PullbackSqrCommutes
                   (comp_cat_pullback
                      comprehension_eso_ty_help
                      comprehension_eso_inv_mor_help_sub)).
        }
        rewrite !assoc.
        etrans.
        {
          do 3 apply maponpaths_2.
          unfold comp_cat_comp_mor.
          apply comprehension_functor_mor_comm.
        }
        rewrite id_right.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          apply comprehension_eso_inv_mor_help_sub_pr1.
        }
        rewrite z_iso_inv_after_z_iso.
        apply id_right.
      }
      apply comp_cat_tm_eq.
    Qed.

    Definition is_z_iso_comprehension_eso_mor
      : is_z_isomorphism comprehension_eso_mor.
    Proof.
      use make_is_z_isomorphism.
      - exact comprehension_eso_inv_mor.
      - split.
        + exact comprehension_eso_mor_inv_mor.
        + exact comprehension_eso_inv_mor_mor.
    Defined.

    Definition comprehension_eso_cod_mor
      : comp_cat_comprehension C Γ comprehension_eso_ty -->[ identity_z_iso Γ ] Δδ.
    Proof.
      refine (comprehension_eso_mor ,, _) ; cbn.
      abstract
        (refine (_ @ !(id_right _)) ;
         exact comprehension_eso_mor_eq).
    Defined.

    Definition comprehension_eso_cod_iso
      : z_iso_disp
          (identity_z_iso Γ)
          (comp_cat_comprehension C Γ (comprehension_eso_ty))
          Δδ.
    Proof.
      refine (comprehension_eso_cod_mor ,, _).
      use is_z_iso_disp_codomain.
      exact is_z_iso_comprehension_eso_mor.
    Defined.
  End Eso.

  (**
     Now we conclude that the comprehension functor is essentially surjective.
     Since we are working with full comprehension categories, we immediately obtain
     that the comprehension functor is an equivalence.
     In addition, this allows us to conclude that it preserves limits.
   *)
  Definition comprehension_eso
    : disp_functor_disp_ess_split_surj (comp_cat_comprehension C)
    := λ Γ Δ,
       comprehension_eso_ty (pr2 Δ)
       ,,
       comprehension_eso_cod_iso (pr2 Δ).

  Definition is_equiv_over_id_comprehension
    : is_equiv_over_id (comp_cat_comprehension C).
  Proof.
    use is_equiv_from_ff_ess_over_id.
    - exact comprehension_eso.
    - exact (full_comp_cat_comprehension_fully_faithful C).
  Defined.

  Definition fiber_functor_comprehension_adj_equiv
             (Γ : C)
    : adj_equivalence_of_cats
        (fiber_functor (comp_cat_comprehension C) Γ)
    := fiber_equiv is_equiv_over_id_comprehension Γ.

  Definition preserves_terminal_fiber_functor_comprehension
             (Γ : C)
    : preserves_terminal (fiber_functor (comp_cat_comprehension C) Γ)
    := right_adjoint_preserves_terminal
         _
         (adj_equivalence_of_cats_inv
            _
            (fiber_functor_comprehension_adj_equiv Γ)).

  Definition preserves_binproduct_fiber_functor_comprehension
             (Γ : C)
    : preserves_binproduct (fiber_functor (comp_cat_comprehension C) Γ)
    := right_adjoint_preserves_binproduct
         _
         (adj_equivalence_of_cats_inv
            _
            (fiber_functor_comprehension_adj_equiv Γ)).

  Definition preserves_equalizer_fiber_functor_comprehension
             (Γ : C)
    : preserves_equalizer (fiber_functor (comp_cat_comprehension C) Γ)
    := right_adjoint_preserves_equalizer
         _
         (adj_equivalence_of_cats_inv
            _
            (fiber_functor_comprehension_adj_equiv Γ)).
End ComprehensionEso.
