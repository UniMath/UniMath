(* ******************************************************************************* *)
(** The inclusion of strict pseudofunctors into pseudofunctors
 ********************************************************************************* *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictPseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictIdentitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictCompositor.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.StrictPseudoFunctor.
Import PseudoFunctor.Notations.
Import StrictPseudoFunctor.Notations.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Modifications.Modification.

Local Open Scope cat.

Section Inclusion.
  Variable (B₁ B₂ : bicat).

  Definition strict_psfunctor_to_psfunctor_map_data
    : strict_psfunctor B₁ B₂ → psfunctor_data B₁ B₂.
  Proof.
    intro F.
    use make_psfunctor_data.
    - exact (λ X, F X).
    - exact (λ _ _ f, #F f).
    - exact (λ _ _ _ _ α, ##F α).
    - exact (strict_psfunctor_id_cell F).
    - exact (λ _ _ _ f g, strict_psfunctor_comp_cell F f g).
  Defined.

  Definition strict_psfunctor_to_psfunctor_map_laws
             (F : strict_psfunctor B₁ B₂)
    : psfunctor_laws (strict_psfunctor_to_psfunctor_map_data F).
  Proof.
    repeat split ; apply F.
  Qed.

  Definition strict_psfunctor_to_psfunctor_map
    : strict_psfunctor B₁ B₂ → psfunctor B₁ B₂.
  Proof.
    intros F.
    use make_psfunctor.
    - exact (strict_psfunctor_to_psfunctor_map_data F).
    - exact (strict_psfunctor_to_psfunctor_map_laws F).
    - split ; cbn.
      + intro a.
        apply (strict_psfunctor_id_cell F a).
      + intros a b c f g.
        apply (strict_psfunctor_comp_cell F f g).
  Defined.

  Definition strict_psfunctor_mor_to_pstrans_data
             (F G : strict_psfunctor_bicat B₁ B₂)
    : F --> G
      →
      pstrans_data
        (strict_psfunctor_to_psfunctor_map F)
        (strict_psfunctor_to_psfunctor_map G).
  Proof.
    intro η.
    use make_pstrans_data.
    - exact (λ X, pr111 η X).
    - exact (pr211 η).
  Defined.

  Definition strict_psfunctor_mor_to_pstrans_is_pstrans
             (F G : strict_psfunctor_bicat B₁ B₂)
             (η : F --> G)
    : is_pstrans (strict_psfunctor_mor_to_pstrans_data F G η).
  Proof.
    repeat split.
    - intros X Y f g α ; cbn.
      exact (pr121 η X Y f g α).
    - intros X ; cbn.
      exact (pr1 (pr221 η) X).
    - intros X Y Z f g ; cbn.
      exact (pr2 (pr221 η) X Y Z f g).
  Qed.

  Definition strict_psfunctor_mor_to_pstrans
             (F G : strict_psfunctor_bicat B₁ B₂)
    : F --> G
      →
      pstrans
        (strict_psfunctor_to_psfunctor_map F)
        (strict_psfunctor_to_psfunctor_map G).
  Proof.
    intros η.
    use make_pstrans.
    - exact (strict_psfunctor_mor_to_pstrans_data F G η).
    - exact (strict_psfunctor_mor_to_pstrans_is_pstrans F G η).
  Defined.

  Definition strict_psfunctor_cell_to_modification
             (F G : strict_psfunctor_bicat B₁ B₂)
             (η₁ η₂ : F --> G)
    : η₁ ==> η₂
      →
      modification
        (strict_psfunctor_mor_to_pstrans _ _ η₁)
        (strict_psfunctor_mor_to_pstrans _ _ η₂).
  Proof.
    intro m.
    use make_modification.
    - intros X.
      exact (pr111 m X).
    - abstract (intros X Y f ; exact (pr211 m X Y f)).
  Defined.

  Definition strict_psfunctor_to_psfunctor_identitor
             (F : strict_psfunctor B₁ B₂)
    : (id₁ (strict_psfunctor_to_psfunctor_map F))
      ==>
        strict_psfunctor_mor_to_pstrans F F (id₁ F).
  Proof.
    use make_modification.
    - exact (λ X, id₂ _).
    - abstract (intros X Y f ; cbn
                ; rewrite lwhisker_id2, id2_rwhisker, id2_left, id2_right
                ; reflexivity).
  Defined.

  Definition strict_psfunctor_to_psfunctor_compositor
             (F₁ F₂ F₃ : strict_psfunctor_bicat B₁ B₂)
             (η₁ : F₁ --> F₂)
             (η₂ : F₂ --> F₃)
    : (strict_psfunctor_mor_to_pstrans _ _ η₁)
        · strict_psfunctor_mor_to_pstrans _ _ η₂
        ==>
        strict_psfunctor_mor_to_pstrans _ _ (η₁ · η₂).
  Proof.
    use make_modification.
    - exact (λ X, id₂ _).
    - abstract (intros X Y f ; cbn
                ; rewrite lwhisker_id2, id2_rwhisker, id2_left, id2_right
                ; reflexivity).
  Defined.

  Definition strict_psfunctor_to_psfunctor_data
    : psfunctor_data (strict_psfunctor_bicat B₁ B₂) (psfunctor_bicat B₁ B₂).
  Proof.
    use make_psfunctor_data.
    - exact strict_psfunctor_to_psfunctor_map.
    - exact strict_psfunctor_mor_to_pstrans.
    - exact strict_psfunctor_cell_to_modification.
    - exact strict_psfunctor_to_psfunctor_identitor.
    - exact strict_psfunctor_to_psfunctor_compositor.
  Defined.

  Definition strict_psfunctor_to_psfunctor_laws
    : psfunctor_laws strict_psfunctor_to_psfunctor_data.
  Proof.
    refine (_ ,, (_ ,, (_ ,, (_ ,, (_ ,, (_ ,, _))))))
    ; intro ; intros ; use modification_eq ; intro ; cbn.
    - exact (idpath _).
    - exact (idpath _).
    - rewrite id2_rwhisker, !id2_left.
      exact (idpath _).
    - rewrite lwhisker_id2, !id2_left.
      exact (idpath _).
    - rewrite id2_rwhisker, lwhisker_id2, !id2_right, id2_left.
      exact (idpath _).
    - rewrite id2_left, id2_right.
      exact (idpath _).
    - rewrite id2_left, id2_right.
      exact (idpath _).
  Qed.

  Definition strict_psfunctor_to_psfunctor
    : psfunctor (strict_psfunctor_bicat B₁ B₂) (psfunctor_bicat B₁ B₂).
  Proof.
    use make_psfunctor.
    - exact strict_psfunctor_to_psfunctor_data.
    - exact strict_psfunctor_to_psfunctor_laws.
    - split ; intros ; apply make_is_invertible_modification
      ; intros ; cbn ; is_iso.
  Defined.
End Inclusion.
