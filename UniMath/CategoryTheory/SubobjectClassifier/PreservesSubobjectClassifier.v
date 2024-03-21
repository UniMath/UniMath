Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.

Local Open Scope cat.

Definition mor_subobject_classifier
           {C : category}
           {T : Terminal C}
           (Ω Ω' : subobject_classifier T)
  : Ω --> Ω'.
Proof.
  use characteristic_morphism.
  - exact T.
  - exact (true Ω).
Defined.

Proposition mor_subobject_classifier_inv
            {C : category}
            {T : Terminal C}
            (Ω Ω' : subobject_classifier T)
  : mor_subobject_classifier Ω Ω' · mor_subobject_classifier Ω' Ω = identity Ω.
Proof.
  use subobject_classifier_map_eq.
  - exact T.
  - exact (true Ω).
  - abstract
      (cbn ;
       unfold mor_subobject_classifier ;
       rewrite !assoc ;
       refine (maponpaths
                 (λ z, z · _)
                 (subobject_classifier_square_commutes Ω' (true Ω))
               @ _) ;
       rewrite assoc' ;
       refine (maponpaths
                 (λ z, _ · z)
                 (subobject_classifier_square_commutes Ω (true Ω'))
               @ _) ;
       unfold const_true ; cbn ;
       rewrite !assoc ;
       apply maponpaths_2 ;
       apply TerminalArrowEq).
  - abstract
      (unfold const_true ;
       rewrite id_right ;
       refine (!(id_left _) @ _) ;
       apply maponpaths_2 ;
       apply TerminalArrowEq).
  - use (isPullback_mor_paths
           _ _ _ _ _ _
           (isPullback_Pullback
              (pullback_glue_pullback
                 _
                 (subobject_classifier_pullback Ω (true Ω'))
                 (subobject_classifier_pullback Ω' (true Ω))))).
    + apply idpath.
    + apply idpath.
    + apply idpath.
    + apply TerminalArrowEq.
  - use (isPullback_mor_paths
           _ _ _ _ _ _
           (isPullback_Pullback (subobject_classifier_pullback Ω (true Ω)))).
    + apply characteristic_morphism_true.
    + apply idpath.
    + apply idpath.
    + apply idpath.
Qed.

Proposition z_iso_subobject_classifier_inverse
            {C : category}
            {T : Terminal C}
            (Ω Ω' : subobject_classifier T)
  : is_inverse_in_precat
      (mor_subobject_classifier Ω Ω')
      (mor_subobject_classifier Ω' Ω).
Proof.
  split.
  - exact (mor_subobject_classifier_inv Ω Ω').
  - exact (mor_subobject_classifier_inv Ω' Ω).
Qed.

Definition z_iso_subobject_classifier
           {C : category}
           {T : Terminal C}
           (Ω Ω' : subobject_classifier T)
  : z_iso Ω Ω'.
Proof.
  use make_z_iso.
  - exact (mor_subobject_classifier Ω Ω').
  - exact (mor_subobject_classifier Ω' Ω).
  - exact (z_iso_subobject_classifier_inverse Ω Ω').
Defined.

Definition isaprop_subobject_classifier'
           {C : category}
           (HC : is_univalent C)
           (T : Terminal C)
  : isaprop (subobject_classifier T).
Proof.
  use invproofirrelevance.
  intros Ω Ω'.
  use total2_paths_f.
  - exact (isotoid _ HC (z_iso_subobject_classifier Ω Ω')).
  - use subtypePath.
    {
      intro.
      apply isaprop_is_subobject_classifier.
    }
    rewrite pr1_transportf.
    rewrite transportf_isotoid'.
    cbn.
    unfold mor_subobject_classifier.
    etrans.
    {
      apply (subobject_classifier_square_commutes Ω' (true Ω)).
    }
    refine (_ @ id_left _) ; cbn.
    apply maponpaths_2.
    apply TerminalArrowEq.
Qed.

Definition eq_to_is_subobject_classifier
           {C : category}
           {T : Terminal C}
           (Ω : subobject_classifier T)
           (Ω' : C)
           (t : T --> Ω')
           (p : (Ω : C) = Ω')
           (q : true Ω · idtoiso p = t)
  : is_subobject_classifier T Ω' t.
Proof.
  induction p.
  cbn in q.
  rewrite id_right in q.
  induction q.
  apply (pr2 Ω).
Qed.

Proposition z_iso_to_is_subobject_classifier
           {C : univalent_category}
           {T : Terminal C}
           (Ω : subobject_classifier T)
           (Ω' : C)
           (t : T --> Ω')
           (f : z_iso Ω Ω')
           (q : true Ω · f = t)
  : is_subobject_classifier T Ω' t.
Proof.
  use eq_to_is_subobject_classifier.
  - exact Ω.
  - exact (isotoid C (univalent_category_is_univalent C) f).
  - rewrite idtoiso_isotoid.
    exact q.
Qed.


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
