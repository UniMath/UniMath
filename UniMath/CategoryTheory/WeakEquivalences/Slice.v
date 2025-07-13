(**
   Rezk Completion Of Slice Categories

   In this file, we show that any weak equivalence induces a weak equivalence between the slices.
   That is, if F : C₀ → C₁ is a weak equivalence, then for every x : C₀,
   there is a weak equivalence F^(x) : C₀/x → C₁/F(x).
   Consequently, if C₁ is univalent, the C₁/F(x) is the Rezk completion of C₀/x.

   Contents
   1. Proof that F^(x) is a weak equivalence if F is a weak equivalence [functor_to_functor_on_slice_is_weq]
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.FiberCod.
Require Import UniMath.CategoryTheory.DisplayedCats.Codomain.CodFunctor.

Local Open Scope cat.

(** * 1. Rezk Completion For Slice Categories *)
Section RezkCompletionOfSliceCategories.

  Context {C₀ C₁ : category} {F : functor C₀ C₁} (x : C₀).

  Lemma functor_to_functor_on_slice_is_ff
    (Ff : fully_faithful F)
    : fully_faithful (codomain_functor F x).
  Proof.
    (* use fiber_functor_fully_faithful *)
    intros a b.
    use isweq_iso.
    - intro f.
      exists (fully_faithful_inv_hom Ff _ _ (pr1 f)).
      abstract (
            apply (faithful_reflects_morphism_equality _ Ff);
            do 2 rewrite functor_comp;
            rewrite functor_on_fully_faithful_inv_hom;
            rewrite functor_id;
            apply (pr2 f)).
    - intro f.
      use subtypePath.
      { intro ; apply homset_property. }
      apply (faithful_reflects_morphism_equality _ Ff).
      etrans. { apply functor_on_fully_faithful_inv_hom. }
      etrans. { apply (@pr1_transportf (C₁⟦_,_⟧) (λ _, C₁⟦_,_⟧)). }
      now rewrite transportf_const.
    - intro f.
      use subtypePath.
      { intro ; apply homset_property. }
      etrans. { apply (@pr1_transportf (C₁⟦_,_⟧) (λ _, C₁⟦_,_⟧)). }
      rewrite transportf_const.
      apply functor_on_fully_faithful_inv_hom.
  Qed.

  (* observe that fully faithfulness is needed to prove essential surjectivity *)
  Lemma functor_to_functor_on_slice_is_eso
    (F_weq : is_weak_equiv F)
    : essentially_surjective (codomain_functor F x).
  Proof.
    (* use fiber_functor_essentially_surjective.*)
    intros [b₁ f₁].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ F_weq b₁)).
    { apply isapropishinh. }
    intros [b₀ f₀].
    apply hinhpr.
    simple refine (_ ,, (_ ,, _)).
    - exact (b₀ ,, fully_faithful_inv_hom (pr2 F_weq) _ _ (f₀ · f₁)).
    - exists f₀.
      rewrite id_right.
      apply pathsinv0, functor_on_fully_faithful_inv_hom.
    - use make_is_z_isomorphism.
      + exists (z_iso_inv f₀).
        cbn ; rewrite id_right.
        etrans.
        { apply maponpaths, functor_on_fully_faithful_inv_hom. }
        rewrite assoc.
        etrans. { apply maponpaths_2, z_iso_after_z_iso_inv. }
        apply id_left.
      + split ; (use subtypePath;
               [ intro ; apply homset_property |
                 etrans ; [ apply (@pr1_transportf (C₁⟦_,_⟧) (λ _, C₁⟦_,_⟧)) | ];
                 rewrite transportf_const;
                 apply z_iso_inv_after_z_iso]).
  Qed.

  Lemma functor_to_functor_on_slice_is_weq
    (F_weq : is_weak_equiv F)
    : is_weak_equiv (codomain_functor F x).
  Proof.
    split.
    - apply functor_to_functor_on_slice_is_eso, F_weq.
    - apply functor_to_functor_on_slice_is_ff, F_weq.
  Defined.

  Lemma Rezk_of_slice
    (F_weq : is_weak_equiv F)
    : weak_equiv (C₀ / x) (C₁ / F x).
  Proof.
    simple refine (_ ,, (_ ,, _)).
    - exact (codomain_functor F x).
    - apply functor_to_functor_on_slice_is_eso, F_weq.
    - apply functor_to_functor_on_slice_is_ff, F_weq.
  Defined.

End RezkCompletionOfSliceCategories.
