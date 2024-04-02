(********************************************************************************************

 Regular epimorphisms

 There are several variations on the notion of epimorphism. One of them is the notion of
 regular epimorphism, which are epimorphisms that are the coequalizer of some parallel pair
 of morphisms. We also establish some basic facts of regular epimorphisms, and we define
 when functors preserve regular epimorphisms.

 Contents
 1. Regular epimorphisms
 2. Regular epimorphisms are closed under isomorphism
 3. Regular epis are epimorphisms
 4. Preservation of regular epimorphisms
 5. Preservation of regular epimorphisms along chosen pullbacks
 6. Preservation of regular epimorphisms by identity and composition

 ********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Epis.
Local Open Scope cat.

(** * 1. Regular epimorphisms *)
Section RegularEpi.
  Context {C : category}
          {x y : C}
          (f : x --> y).

  Definition is_regular_epi
    : UU
    := ∃ (w : C)
         (g₁ : w --> x)
         (g₂ : w --> x)
         (p : g₁ · f = g₂ · f),
       isCoequalizer g₁ g₂ f p.

  Proposition isaprop_is_regular_epi
    : isaprop is_regular_epi.
  Proof.
    apply isapropishinh.
  Qed.
End RegularEpi.

(** * 2. Regular epimorphisms are closed under isomorphism *)
Proposition is_regular_epi_arrow_z_iso_f
            {C : category}
            {x₁ x₂ y₁ y₂ : C}
            (f₁ : x₁ --> y₁)
            (f₂ : x₂ --> y₂)
            (i₁ : z_iso x₁ x₂)
            (i₂ : z_iso y₁ y₂)
            (p : f₁ · i₂ = i₁ · f₂)
  : is_regular_epi f₁ → is_regular_epi f₂.
Proof.
  assert (inv_from_z_iso i₁ · f₁ = f₂ · inv_from_z_iso i₂) as p'.
  {
    use z_iso_inv_on_left.
    rewrite !assoc'.
    refine (!_).
    use z_iso_inv_on_right.
    exact p.
  }
  use factor_through_squash.
  {
    apply isaprop_is_regular_epi.
  }
  intros ( w & g₁ & g₂ & q & H ).
  pose (Coeq := make_Coequalizer _ _ _ _ H).
  use hinhpr.
  simple refine (w ,, g₁ · i₁ ,, g₂ · i₁ ,, _ ,, _).
  - abstract
      (rewrite !assoc' ;
       rewrite <- !p ;
       rewrite !assoc ;
       rewrite q ;
       apply idpath).
  - intros z h r.
    use iscontraprop1.
    + use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use (cancel_z_iso' i₂).
      use (CoequalizerOutsEq Coeq).
      cbn.
      rewrite !assoc.
      rewrite !p.
      rewrite !assoc'.
      apply maponpaths.
      exact (pr2 φ₁ @ !(pr2 φ₂)).
    + simple refine (_ ,, _).
      * simple refine (inv_from_z_iso i₂ · CoequalizerOut Coeq _ _ _).
        ** exact (i₁ · h).
        ** abstract
            (rewrite !assoc ;
             exact r).
      * cbn.
        refine (assoc _ _ _ @ _).
        rewrite <- p'.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          apply (CoequalizerCommutes Coeq).
        }
        rewrite !assoc.
        rewrite z_iso_after_z_iso_inv.
        apply id_left.
Qed.

(** * 3. Regular epis are epimorphisms *)
Proposition is_epi_regular_epi
            {C : category}
            {x y : C}
            (f : x --> y)
  : is_regular_epi f → isEpi f.
Proof.
  use factor_through_squash.
  {
    apply isapropisEpi.
    apply homset_property.
  }
  intros ( w & g₁ & g₂ & p & H ).
  pose (Coeq := make_Coequalizer _ _ _ _ H).
  intros z h₁ h₂ q.
  assert (g₁ · (f · h₁) = g₂ · (f · h₁)) as r.
  {
    rewrite !assoc.
    rewrite p.
    apply idpath.
  }
  assert (h₁ = CoequalizerOut Coeq z (f · h₁) r) as s₁.
  {
    use (CoequalizerOutsEq Coeq).
    rewrite CoequalizerCommutes.
    apply idpath.
  }
  refine (s₁ @ _).
  use (CoequalizerOutsEq Coeq).
  rewrite CoequalizerCommutes.
  exact q.
Qed.

(** * 4. Preservation of regular epimorphisms *)
Definition preserves_regular_epi
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : UU
  := ∏ (x y : C₁)
       (f : x --> y),
     is_regular_epi f
     → is_regular_epi (#F f).

Proposition isaprop_preserves_regular_epi
            {C₁ C₂ : category}
            (F : C₁ ⟶ C₂)
  : isaprop (preserves_regular_epi F).
Proof.
  do 4 (use impred ; intro).
  apply isaprop_is_regular_epi.
Qed.

Definition regular_epi_pb_stable
           (C : category)
  : UU
  := ∏ (pb x y z : C)
       (f : x --> z)
       (g : y --> z)
       (π₁ : pb --> x)
       (π₂ : pb --> y)
       (p : π₁ · f = π₂ · g)
       (H : isPullback p),
     is_regular_epi f
     → is_regular_epi π₂.

Proposition isaprop_regular_epi_pb_stable
            (C : category)
  : isaprop (regular_epi_pb_stable C).
Proof.
  do 11 (use impred ; intro).
  apply isaprop_is_regular_epi.
Qed.

(** * 5. Preservation of regular epimorphisms along chosen pullbacks *)
Definition regular_epi_chosen_pb_stable
           {C : category}
           (PB : Pullbacks C)
  : UU
  := ∏ (x y z : C)
       (f : x --> z)
       (g : y --> z),
     is_regular_epi f
     → is_regular_epi (PullbackPr2 (PB _ _ _ f g)).

Proposition isaprop_regular_epi_chosen_pb_stable
            {C : category}
            (PB : Pullbacks C)
  : isaprop (regular_epi_chosen_pb_stable PB).
Proof.
  do 6 (use impred ; intro).
  apply isaprop_is_regular_epi.
Qed.

Proposition regular_epi_pb_stable_from_chosen
            {C : category}
            (PB : Pullbacks C)
            (H : regular_epi_chosen_pb_stable PB)
  : regular_epi_pb_stable C.
Proof.
  intros pb x y z f g π₁ π₂ p HP Hf.
  pose (P := make_Pullback _ HP).
  pose (Hpb := H x y z f g Hf).
  use (is_regular_epi_arrow_z_iso_f _ _ _ _ _ Hpb).
  - exact (z_iso_from_Pullback_to_Pullback (PB _ _ _ f g) P).
  - exact (identity_z_iso y).
  - cbn.
    rewrite id_right.
    unfold from_Pullback_to_Pullback.
    refine (!_).
    apply (PullbackArrow_PullbackPr2 P).
Qed.

(** * 6. Preservation of regular epimorphisms by identity and composition *)
Proposition id_preserves_regular_epi
            (C : category)
  : preserves_regular_epi (functor_identity C).
Proof.
  intros x y f Hf.
  exact Hf.
Qed.

Proposition comp_preserves_regular_epi
            {C₁ C₂ C₃ : category}
            {F : C₁ ⟶ C₂}
            {G : C₂ ⟶ C₃}
            (HF : preserves_regular_epi F)
            (HG : preserves_regular_epi G)
  : preserves_regular_epi (F ∙ G).
Proof.
  intros x y f Hf.
  apply HG.
  apply HF.
  exact Hf.
Qed.
