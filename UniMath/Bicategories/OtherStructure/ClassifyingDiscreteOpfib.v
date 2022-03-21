(***********************************************************

 Classifying discrete opfibrations

 Contents:
 1. Help definitions
 2. Definition of classifying discrete opfibrations
 3. Help functions

 ************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Discreteness.
Require Import UniMath.Bicategories.Core.TransportLaws.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.Properties.ClosedUnderPullback.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatSlice.
Require Import UniMath.Bicategories.DisplayMapBicat.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.PullbackFunctions.
Import PullbackFunctions.Notations.

Local Open Scope cat.

Definition disc_sopfib
           {B : bicat}
           {e s : B}
           (p : e --> s)
  : UU
  := internal_sopfib p × discrete_1cell p.

Section ClassifyingDiscreteOpfibration.
  Context {B : bicat}
          (HB : is_univalent_2_1 B)
          {e s : B}
          (p : e --> s)
          (Hp : disc_sopfib p).

  (**
   1. Help definitions
   *)
  Definition disc_sopfib_of
             {x : B}
             (f : x --> s)
    : UU
    := ∑ (z : B)
         (pf : z --> x),
       disc_sopfib pf.

  Definition ob_of_disc_sopfib_of
             {x : B}
             {f : x --> s}
             (pf : disc_sopfib_of f)
    : B
    := pr1 pf.

  Coercion mor_of_disc_sopfib_of
           {x : B}
           {f : x --> s}
           (pf : disc_sopfib_of f)
    : ob_of_disc_sopfib_of pf --> x
    := pr12 pf.

  Definition mor_of_disc_sopfib_of_is_disc_sopfib
             {x : B}
             {f : x --> s}
             (pf : disc_sopfib_of f)
    : disc_sopfib pf
    := pr22 pf.

  Definition disc_sopfib_of_is_pb
             {x : B}
             {f : x --> s}
             (pf : disc_sopfib_of f)
    : UU
    := ∑ (ze : ob_of_disc_sopfib_of pf --> e)
         (γ : invertible_2cell (ze · p) (pf · f)),
       has_pb_ump (make_pb_cone _ ze pf γ).

  Definition map_to_disp_sopfib
    : UU
    := ∏ (x : B)
         (f : x --> s),
       ∑ (pf : disc_sopfib_of f),
       disc_sopfib_of_is_pb pf.

  Context (pb : map_to_disp_sopfib).

  Section ClassifyingDiscreteOpfibrationMor.
    Context {x : B}
            {f g : hom x s}
            (α : f --> g).

    Let φ_ob : B := pr11 (pb x f).
    Let χ_ob : B := pr11 (pb x g).
    Let φ : φ_ob --> x := pr121 (pb x f).
    Let χ : χ_ob --> x := pr121 (pb x g).

    Let φe : φ_ob --> e
      := pr12 (pb x f).
    Let φγ : invertible_2cell (φe · p) (φ · f)
      := pr122 (pb x f).
    Let Hφ : has_pb_ump (make_pb_cone φ_ob φe φ φγ)
      := pr222 (pb x f).

    Let χe : χ_ob --> e
      := pr12 (pb x g).
    Let χγ : invertible_2cell (χe · p) (χ · g)
      := pr122 (pb x g).
    Let Hχ : has_pb_ump (make_pb_cone χ_ob χe χ χγ)
      := pr222 (pb x g).

    Let ℓ : φ_ob --> e
      := pr1 (pr11 Hp φ_ob φe (φ · g) (φγ • (_ ◃ α))).
    Let ζ : φe ==> ℓ
      := pr12 (pr11 Hp φ_ob φe (φ · g) (φγ • (_ ◃ α))).
    Let γ : invertible_2cell (φ · g) (ℓ · p)
      := pr122 (pr11 Hp φ_ob φe (φ · g) (φγ • (_ ◃ α))).
    Let Hζ : is_opcartesian_2cell_sopfib p ζ
      := pr1 (pr222 (pr11 Hp φ_ob φe (φ · g) (φγ • (_ ◃ α)))).

    Definition mor_of_pb_disc_sopfib_mor_cone
      : pb_cone p g
      := make_pb_cone φ_ob ℓ φ (inv_of_invertible_2cell γ).

    Definition mor_of_pb_disc_sopfib_mor
      : φ_ob --> χ_ob
      := pb_ump_mor Hχ mor_of_pb_disc_sopfib_mor_cone.

    Definition pb_disc_sopfib_mor_preserves_opcartesian
      : mor_preserves_opcartesian φ χ mor_of_pb_disc_sopfib_mor.
    Proof.
      use mor_preserves_opcartesian_pb_ump_mor_alt.
      intros z h₁ h₂ β Hβ.
      use (is_opcartesian_2cell_sopfib_precomp _ (_ ◃ ζ)).
      - exact ((β ▹ _) • (_ ◃ ζ)).
      - apply Hp.
        exact Hζ.
      - use vcomp_is_opcartesian_2cell_sopfib.
        + exact (from_pb_opcartesian Hφ (pr1 Hp) _ Hβ).
        + apply Hp.
          exact Hζ.
      - abstract
          (rewrite vcomp_whisker ;
           apply idpath).
    Defined.

    Definition cell_of_pb_disc_sopfib_mor
      : invertible_2cell φ (mor_of_pb_disc_sopfib_mor · χ)
      := inv_of_invertible_2cell
           (pb_ump_mor_pr2 Hχ mor_of_pb_disc_sopfib_mor_cone).
  End ClassifyingDiscreteOpfibrationMor.

  Definition pb_disc_sopfib_mor
             {x : B}
             {f g : hom x s}
             (α : f --> g)
    : disc_sopfib_slice HB x ⟦ pr1 (pb _ f) , pr1 (pb _ g) ⟧.
  Proof.
    simple refine (_ ,, (_ ,, tt) ,, _) ; cbn.
    - exact (mor_of_pb_disc_sopfib_mor α).
    - exact (pb_disc_sopfib_mor_preserves_opcartesian α).
    - exact (cell_of_pb_disc_sopfib_mor α).
  Defined.

  (**
   2. Definition of classifying discrete opfibrations
   *)
  Definition is_classifying_full
    : UU
    := ∏ (x : B)
         (f g : x --> s)
         (β : disc_sopfib_slice HB x ⟦ pr1 (pb _ f) , pr1 (pb _ g) ⟧),
       ∑ (α : f ==> g),
       pb_disc_sopfib_mor α = β.

  (**
   3. Help functions
   *)
  Definition is_classifying_full_help
    : UU
    := ∏ (x : B)
         (f g : x --> s)
         (β : disc_sopfib_slice HB x ⟦ pr1 (pb _ f) , pr1 (pb _ g) ⟧),
       ∑ (α : f ==> g)
         (γ : mor_of_pb_disc_sopfib_mor α ==> pr1 β)
         (Hγ : is_invertible_2cell γ),
       γ ▹ pr121 (pb x g)
       =
       pb_ump_mor_pr2 (pr222 (pb x g)) (mor_of_pb_disc_sopfib_mor_cone α)
       • pr122 β.

  Definition make_is_classifying_full
             (H : is_classifying_full_help)
    : is_classifying_full.
  Proof.
    intros x f g β.
    specialize (H x f g β).
    refine (pr1 H ,, _).
    use (isotoid_2_1
           (pr1 (is_discrete_disp_map_slice
                   HB
                   (discrete_sopfib_subbicat_props B HB)
                   (discrete_sopfib_disp_map_bicat_in_discrete B) x))).
    use make_invertible_2cell.
    - refine (pr12 H ,, _).
      abstract
        (cbn ;
         use vcomp_move_R_pM ; [ is_iso | ] ; cbn ;
         exact (pr222 H)).
    - apply is_invertible_2cell_in_disp_map_slice_bicat ; cbn.
      exact (pr122 H).
  Defined.

  Definition is_classifying_faithful
    : UU
    := ∏ (x : B)
         (f g : x --> s)
         (α β : f ==> g),
       pb_disc_sopfib_mor α = pb_disc_sopfib_mor β
       →
       α = β.

  Definition is_classifying
    : UU
    := is_classifying_full × is_classifying_faithful.

  Definition eq_disc_slice_mor
             {x : B}
             {g₁ g₂ : disc_sopfib_slice HB x}
             {α β : g₁ --> g₂}
             (γ : invertible_2cell (pr1 α) (pr1 β))
             (r : pr22 α • (γ ▹ _) = pr22 β)
    : α = β.
  Proof.
    use total2_paths_f.
    - exact (isotoid_2_1 HB γ).
    - use dirprod_paths.
      + use pathsdirprod ; [ apply isaprop_mor_preserves_opcartesian | apply isapropunit ].
      + cbn.
        use subtypePath.
        {
          intro.
          apply isaprop_is_invertible_2cell.
        }
        etrans.
        {
          refine (maponpaths (λ z, pr1 z) _).
          exact (pr2_transportf _ _).
        }
        cbn.
        refine (pr1_transportf (isotoid_2_1 HB γ) _ @ _).
        rewrite transport_two_cell_FlFr.
        rewrite maponpaths_for_constant_function.
        cbn.
        rewrite id2_left.
        rewrite isotoid_2_1_rwhisker.
        rewrite idtoiso_2_1_isotoid_2_1.
        cbn.
        exact r.
  Qed.

  Definition eq_slice_to_inv2cell
             {x : B}
             {g₁ g₂ : disc_sopfib_slice HB x}
             {α β : g₁ --> g₂}
             (q : α = β)
    : invertible_2cell (pr1 α) (pr1 β)
    := idtoiso_2_1 _ _ (maponpaths pr1 q).

  Definition eq_slice_to_coh
             {x : B}
             {g₁ g₂ : disc_sopfib_slice HB x}
             {α β : g₁ --> g₂}
             (q : α = β)
    : pr122 α • (eq_slice_to_inv2cell q ▹ _)
      =
      pr122 β.
  Proof.
    pose (maponpaths pr1 (maponpaths dirprod_pr2 (fiber_paths q))) as r.
    cbn in r.
    refine (_ @ r).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply (@pr2_transportf
               (pr1 g₁ --> pr1 g₂)
               (λ z, mor_preserves_opcartesian (pr12 g₁) (pr12 g₂) z × unit)
               (λ z, invertible_2cell (pr12 g₁) (z · pr12 g₂))).
    }
    etrans.
    {
      apply (@pr1_transportf
               (pr1 g₁ --> pr1 g₂)
               (λ z, pr12 g₁ ==> z · pr12 g₂)).
    }
    rewrite transport_two_cell_FlFr.
    rewrite maponpaths_for_constant_function.
    cbn.
    rewrite id2_left.
    apply maponpaths.
    rewrite <- idtoiso_2_1_rwhisker.
    apply idpath.
  Qed.

  Definition is_classifying_faithful_help
    : UU
    := ∏ (x : B)
         (f g : x --> s)
         (α β : f ==> g)
         (γ : invertible_2cell
                (mor_of_pb_disc_sopfib_mor α)
                (mor_of_pb_disc_sopfib_mor β))
         (q : (γ ▹ pr121 (pb x g))
              • pb_ump_mor_pr2
                  (pr222 (pb x g))
                  (mor_of_pb_disc_sopfib_mor_cone β)
              =
              (pb_ump_mor_pr2
                 (pr222 (pb x g))
                 (mor_of_pb_disc_sopfib_mor_cone α))),
       α = β.

  Definition make_is_classifying_faithful
             (H : is_classifying_faithful_help)
    : is_classifying_faithful.
  Proof.
    intros x f g α β q.
    simple refine (H x f g α β _ _).
    - exact (eq_slice_to_inv2cell q).
    - use vcomp_move_R_Mp ; [ apply property_from_invertible_2cell | ].
      use vcomp_move_L_pM ; [ apply property_from_invertible_2cell | ].
      exact (eq_slice_to_coh q).
  Qed.

  Definition make_is_classifying
             (H₁ : is_classifying_full_help)
             (H₂ : is_classifying_faithful_help)
    : is_classifying.
  Proof.
    split.
    - use make_is_classifying_full.
      exact H₁.
    - use make_is_classifying_faithful.
      exact H₂.
  Defined.
End ClassifyingDiscreteOpfibration.
