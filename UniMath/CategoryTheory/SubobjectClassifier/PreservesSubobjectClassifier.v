(*******************************************************************************************

 Preservation of subobject classifiers

 In this file, we define when functors `F : C₁ ⟶ C₂` preserve subobject classifiers. We
 give three formulations.

 The first formulation [preserves_subobject_classifier] does not assume that any of the
 involved categories have a subobject classifier. This statement says that every subobject
 classifier is mapped to a subobject classifier.

 The second formulation [preserves_chosen_subobject_classifier] assumes that `C₁` has a
 subobject classifier. For this one, we only say that the chosen subobject classifier is
 mapped to a subobject classifier.

 The final formulation [preserves_chosen_to_chosen_subobject_classifier] assumes that both
 `C₁` and `C₂` have a subobject classifier. This statement is phrased by saying that these
 subobject classifiers are isomorphic such that a certain diagram commutes.

 Note that some statements in this file assumes that the involved categories are univalent.
 This assumption is only used to simplify the involved proofs.

 Contents
 1. Preserving subobject classifiers
 2. Preservation of chosen subobject classifiers
 3. Preservation of subobject classifiers via isomorphisms
 4. Preservation of subobject classifiers is independent of the choice of terminal object
 5. Calculational lemmas

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifierIso.

Local Open Scope cat.

(** * 1. Preserving subobject classifiers *)
Definition preserves_subobject_classifier
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (T₁ : Terminal C₁)
           (T₂ : Terminal C₂)
           (HF : preserves_terminal F)
  : UU
  := ∏ (Ω : C₁)
       (t : T₁ --> Ω),
     is_subobject_classifier T₁ Ω t
     →
     is_subobject_classifier
       T₂ (F Ω)
       (TerminalArrow (preserves_terminal_to_terminal F HF T₁) _ · #F t).

Proposition isaprop_preserves_subobject_classifier
            {C₁ C₂ : category}
            (F : C₁ ⟶ C₂)
            (T₁ : Terminal C₁)
            (T₂ : Terminal C₂)
            (HF : preserves_terminal F)
  : isaprop (preserves_subobject_classifier F T₁ T₂ HF).
Proof.
  do 3 (use impred ; intro).
  apply isaprop_is_subobject_classifier.
Qed.

Definition preserves_subobject_classifier_on_ob
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {T₁ : Terminal C₁}
           {T₂ : Terminal C₂}
           {HF : preserves_terminal F}
           (HF' : preserves_subobject_classifier F T₁ T₂ HF)
           (Ω : subobject_classifier T₁)
  : subobject_classifier T₂
  := F Ω ,, _ ,, HF' _ _ (pr22 Ω).

Definition preserves_subobject_classifier_z_iso
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {T₁ : Terminal C₁}
           {T₂ : Terminal C₂}
           {HF : preserves_terminal F}
           (HF' : preserves_subobject_classifier F T₁ T₂ HF)
           (Ω₁ : subobject_classifier T₁)
           (Ω₂ : subobject_classifier T₂)
  : z_iso (F Ω₁) Ω₂
  := z_iso_subobject_classifier (preserves_subobject_classifier_on_ob HF' Ω₁) Ω₂.

Definition identity_preserves_subobject_classifier
           {C : category}
           (T : Terminal C)
  : preserves_subobject_classifier
      (functor_identity C)
      T T
      (identity_preserves_terminal C).
Proof.
  intros Ω t H.
  use (is_subobject_classifier_eq_ar _ H).
  abstract
    (cbn ;
     refine (!(id_left _) @ _) ;
     apply maponpaths_2 ;
     apply TerminalArrowEq).
Defined.

Definition comp_preserves_subobject_classifier
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {T₁ : Terminal C₁}
           {T₂ : Terminal C₂}
           {T₃ : Terminal C₃}
           {HF : preserves_terminal F}
           {HG : preserves_terminal G}
           (HF' : preserves_subobject_classifier F T₁ T₂ HF)
           (HG' : preserves_subobject_classifier G T₂ T₃ HG)
  : preserves_subobject_classifier
      (F ∙ G)
      T₁ T₃
      (composition_preserves_terminal HF HG).
Proof.
  intros Ω t H.
  pose (HG' (F Ω) (TerminalArrow (preserves_terminal_to_terminal F HF T₁) _ · #F t) (HF' Ω t H))
    as H'.
  use (is_subobject_classifier_eq_ar _ H').
  abstract
    (cbn ;
     rewrite functor_comp ;
     rewrite !assoc ;
     apply maponpaths_2 ;
     apply (TerminalArrowEq
              (T := preserves_terminal_to_terminal
                      _
                      (composition_preserves_terminal HF HG) T₁))).
Defined.

(** * 2. Preservation of chosen subobject classifiers *)
Definition preserves_chosen_subobject_classifier
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
           (T₁ : Terminal C₁)
           (T₂ : Terminal C₂)
           (HF : preserves_terminal F)
           (Ω : subobject_classifier T₁)
  : UU
  := is_subobject_classifier
       T₂
       (F Ω)
       (TerminalArrow (preserves_terminal_to_terminal F HF T₁) _ · #F (true Ω)).

Proposition preserves_chosen_to_preserves_subobject_classifier
            {C₁ C₂ : univalent_category}
            {F : C₁ ⟶ C₂}
            {T₁ : Terminal C₁}
            {T₂ : Terminal C₂}
            {HF : preserves_terminal F}
            {Ω : subobject_classifier T₁}
            (HF' : preserves_chosen_subobject_classifier F T₁ T₂ HF Ω)
  : preserves_subobject_classifier F T₁ T₂ HF.
Proof.
  intros O' t H.
  pose (Ω' := (O' ,, t ,, H) : subobject_classifier T₁).
  pose (f := z_iso_subobject_classifier Ω Ω').
  use z_iso_to_is_subobject_classifier.
  - exact (F Ω
           ,,
           TerminalArrow (preserves_terminal_to_terminal F HF T₁) _ · #F (true Ω)
           ,,
           HF').
  - exact (functor_on_z_iso F f).
  - cbn.
    rewrite !assoc'.
    rewrite <- functor_comp.
    unfold mor_subobject_classifier.
    etrans.
    {
      do 2 apply maponpaths.
      exact (subobject_classifier_square_commutes Ω' (true Ω)).
    }
    rewrite functor_comp.
    rewrite !assoc.
    apply maponpaths_2.
    apply (TerminalArrowEq (T := preserves_terminal_to_terminal F HF T₁)).
Qed.

Proposition preserves_chosen_to_preserves_subobject_classifier'
            {C₁ C₂ : category}
            (HC₁ : is_univalent C₁)
            (HC₂ : is_univalent C₂)
            {F : C₁ ⟶ C₂}
            {T₁ : Terminal C₁}
            {T₂ : Terminal C₂}
            {HF : preserves_terminal F}
            {Ω : subobject_classifier T₁}
            (HF' : preserves_chosen_subobject_classifier F T₁ T₂ HF Ω)
  : preserves_subobject_classifier F T₁ T₂ HF.
Proof.
  exact (preserves_chosen_to_preserves_subobject_classifier
           (C₁ := make_univalent_category C₁ HC₁)
           (C₂ := make_univalent_category C₂ HC₂)
           HF').
Qed.

(** * 3. Preservation of subobject classifiers via isomorphisms *)
Definition preserves_chosen_to_chosen_subobject_classifier
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {T₁ : Terminal C₁}
           {T₂ : Terminal C₂}
           (HF : preserves_terminal F)
           (Ω₁ : subobject_classifier T₁)
           (Ω₂ : subobject_classifier T₂)
  : UU
  := ∑ (f : z_iso (F Ω₁) Ω₂),
     #F (true Ω₁) · f
     =
     TerminalArrow _ _ · true Ω₂.

Proposition preserves_chosen_to_preserves_chosen_subobject_classifier
            {C₁ C₂ : univalent_category}
            {F : C₁ ⟶ C₂}
            {T₁ : Terminal C₁}
            {T₂ : Terminal C₂}
            {HF : preserves_terminal F}
            {Ω₁ : subobject_classifier T₁}
            {Ω₂ : subobject_classifier T₂}
            (HF' : preserves_chosen_to_chosen_subobject_classifier HF Ω₁ Ω₂)
  : preserves_chosen_subobject_classifier F T₁ T₂ HF Ω₁.
Proof.
  use z_iso_to_is_subobject_classifier.
  - exact Ω₂.
  - exact (z_iso_inv (pr1 HF')).
  - cbn.
    refine (!_).
    use z_iso_inv_on_left.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (pr2 HF').
    }
    rewrite !assoc.
    unfold true'.
    refine (_ @ id_left _).
    apply maponpaths_2.
    apply TerminalArrowEq.
Qed.

Proposition preserves_chosen_to_preserves_chosen_subobject_classifier'
            {C₁ C₂ : category}
            (HC₁ : is_univalent C₁)
            (HC₂ : is_univalent C₂)
            {F : C₁ ⟶ C₂}
            {T₁ : Terminal C₁}
            {T₂ : Terminal C₂}
            {HF : preserves_terminal F}
            {Ω₁ : subobject_classifier T₁}
            {Ω₂ : subobject_classifier T₂}
            (HF' : preserves_chosen_to_chosen_subobject_classifier HF Ω₁ Ω₂)
  : preserves_chosen_subobject_classifier F T₁ T₂ HF Ω₁.
Proof.
  exact (preserves_chosen_to_preserves_chosen_subobject_classifier
           (C₁ := make_univalent_category C₁ HC₁)
           (C₂ := make_univalent_category C₂ HC₂)
           HF').
Qed.

(** * 4. Preservation of subobject classifiers is independent of the choice of terminal object *)
Lemma preserves_subobject_classifier_independent_of_chosen_terminal_if_univalent
  {C₁ C₂ : category} {F : functor C₁ C₂} (T₁ : Terminal C₁) (T₂ : Terminal C₂)
  {Ft : preserves_terminal F} (FΩ : preserves_subobject_classifier _ T₁ T₂ Ft)
  : is_univalent C₁ → ∏ T₁' : Terminal C₁, preserves_subobject_classifier _ T₁' T₂ Ft.
Proof.
  intros C₁_univ T₁'.
  induction (Terminal_unique_up_to_id_if_univalent (C₁ ,, C₁_univ) T₁ T₁').
  exact FΩ.
Qed.

(** * 5. Calculational lemmas *)
Proposition mor_subobject_classifier_is_identity
            {C : category}
            {T : Terminal C}
            (Ω : subobject_classifier T)
  : identity _
    =
    mor_subobject_classifier
      (preserves_subobject_classifier_on_ob
         (identity_preserves_subobject_classifier _)
         Ω)
      _.
Proof.
  cbn.
  use subobject_classifier_map_eq'.
  - apply id_right.
  - intros x h k p.
    use iscontraprop1.
    + use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      apply TerminalArrowEq.
    + refine (TerminalArrow _ _ ,, _ ,, _).
      * refine (_ @ id_right _).
        refine (_ @ !p).
        cbn ; unfold true'.
        rewrite !assoc.
        apply maponpaths_2.
        apply TerminalArrowEq.
      * apply TerminalArrowEq.
Qed.

Proposition mor_subobject_classifier_is_composition
            {C₁ C₂ C₃ : category}
            {T₁ : Terminal C₁}
            {T₂ : Terminal C₂}
            {T₃ : Terminal C₃}
            (Ω₁ : subobject_classifier T₁)
            (Ω₂ : subobject_classifier T₂)
            (Ω₃ : subobject_classifier T₃)
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            {HF : preserves_terminal F}
            {HG : preserves_terminal G}
            (HFΩ : preserves_subobject_classifier F T₁ T₂ HF)
            (HGΩ : preserves_subobject_classifier G T₂ T₃ HG)
  : # G(mor_subobject_classifier (preserves_subobject_classifier_on_ob HFΩ Ω₁) Ω₂)
    · mor_subobject_classifier (preserves_subobject_classifier_on_ob HGΩ Ω₂) Ω₃
    =
    mor_subobject_classifier
      (preserves_subobject_classifier_on_ob
         (comp_preserves_subobject_classifier HFΩ HGΩ)
         Ω₁)
      Ω₃.
Proof.
  use subobject_classifier_map_eq'.
  - simpl.
    refine (_ @ subobject_classifier_square_commutes
                  Ω₃
                  (preserves_subobject_classifier_on_ob HGΩ Ω₂)).
    rewrite !assoc.
    apply maponpaths_2.
    use (cancel_z_iso' (preserves_terminal_to_z_iso _ HG T₂ T₃)).
    pose proof (maponpaths
                  (λ z, #G z)
                  (subobject_classifier_square_commutes
                     Ω₂
                     (preserves_subobject_classifier_on_ob HFΩ Ω₁)))
      as p.
    simpl in p.
    refine (_ @ p @ _).
    + rewrite functor_comp.
      rewrite !assoc.
      apply maponpaths_2.
      unfold true' ; cbn.
      rewrite functor_comp.
      rewrite !assoc.
      apply maponpaths_2.
      apply (TerminalArrowEq
               (T := preserves_terminal_to_terminal
                       _
                       (composition_preserves_terminal HF HG)
                       T₁)).
    + rewrite functor_comp.
      unfold true' ; cbn.
      rewrite !assoc.
      apply maponpaths_2.
      apply (TerminalArrowEq (T := preserves_terminal_to_terminal G HG T₂)).
  - intros x h k p.
    use iscontraprop1.
    + use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply isapropdirprod ; apply homset_property.
      }
      apply TerminalArrowEq.
    + refine (k ,, _ ,, _).
      * use (cancel_z_iso
               _ _
               (functor_on_z_iso
                  G
                  (z_iso_subobject_classifier
                     (preserves_subobject_classifier_on_ob HFΩ Ω₁)
                     Ω₂))).
        use (cancel_z_iso
               _ _
               (z_iso_subobject_classifier
                  (preserves_subobject_classifier_on_ob HGΩ Ω₂)
                  Ω₃)).
        refine (!_).
        refine (assoc' _ _ _ @ _).
        refine (p @ _) ; cbn.
        refine (!_).
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        assert  (TerminalArrow
                   (preserves_terminal_to_terminal
                      _
                      (composition_preserves_terminal HF HG)
                      T₁)
                   T₃
                 =
                 TerminalArrow
                   (preserves_terminal_to_terminal G HG T₂)
                   _
                 · #G(TerminalArrow (preserves_terminal_to_terminal F HF T₁) _))
          as r.
        {
          apply TerminalArrowEq.
        }
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc'.
          rewrite <- functor_comp.
          etrans.
          {
            apply maponpaths_2.
            exact r.
          }
          rewrite !assoc'.
          apply maponpaths.
          refine (!(functor_comp G _ _) @ _).
          apply maponpaths.
          rewrite !assoc.
          exact (subobject_classifier_square_commutes
                   Ω₂
                   (preserves_subobject_classifier_on_ob HFΩ Ω₁)).
        }
        clear r.
        rewrite functor_comp.
        rewrite !assoc'.
        etrans.
        {
          pose (subobject_classifier_square_commutes
                  Ω₃
                  (preserves_subobject_classifier_on_ob HGΩ Ω₂))
            as r.
          refine (_ @ r).
          simpl ; cbn.
          rewrite !assoc.
          do 2 apply maponpaths_2.
          apply (TerminalArrowEq (T := preserves_terminal_to_terminal G HG T₂)).
        }
        refine (_ @ id_left _).
        apply maponpaths_2.
        apply TerminalArrowEq.
      * apply TerminalArrowEq.
Qed.
