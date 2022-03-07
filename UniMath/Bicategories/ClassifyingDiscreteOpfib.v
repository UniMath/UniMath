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

Definition from_pb_opcartesian
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           {fb : b₁ --> b₂}
           {γ : invertible_2cell (fe · p₂) (p₁ · fb)}
           (H : has_pb_ump (make_pb_cone e₁ fe p₁ γ))
           (Hp₂ : internal_sopfib p₂)
           {x : B}
           {g₁ g₂ : x --> e₁}
           (α : g₁ ==> g₂)
           (Hα : is_opcartesian_2cell_sopfib p₁ α)
  : is_opcartesian_2cell_sopfib p₂ (α ▹ fe).
Proof.
Admitted.

Definition to_pb_opcartesian
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           {fb : b₁ --> b₂}
           {γ : invertible_2cell (fe · p₂) (p₁ · fb)}
           (H : has_pb_ump (make_pb_cone e₁ fe p₁ γ))
           {x : B}
           {g₁ g₂ : x --> e₁}
           (α : g₁ ==> g₂)
           (Hα : is_opcartesian_2cell_sopfib p₂ (α ▹ fe))
  : is_opcartesian_2cell_sopfib p₁ α.
Proof.
Admitted.

Definition mor_preserves_opcartesian_pb_ump_mor_alt
           {B : bicat}
           {e₁ e₂ b₁ b₂ : B}
           {p₁ : e₁ --> b₁}
           {p₂ : e₂ --> b₂}
           {fe : e₁ --> e₂}
           {fb : b₁ --> b₂}
           {γ : invertible_2cell (fe · p₂) (p₁ · fb)}
           (pb := make_pb_cone e₁ fe p₁ γ)
           (H : has_pb_ump pb)
           {e₀ : B}
           (p₀ : e₀ --> b₁)
           (h₁ : e₀ --> e₂)
           (δ : invertible_2cell (h₁ · p₂) (p₀ · fb))
           (cone := make_pb_cone e₀ h₁ p₀ δ)
           (Hh₁ : mor_preserves_opcartesian p₀ p₂ h₁)
  : mor_preserves_opcartesian
      p₀
      p₁
      (pb_ump_mor H cone).
Proof.
Admitted.




Definition disc_sopfib
           {B : bicat}
           {e s : B}
           (p : e --> s)
  : UU
  := internal_sopfib p × discrete_1cell p.

Section ClassifyingDiscreteOpfibration.
  Context {B : bicat}
          {e s : B}
          (p : e --> s)
          (Hp : disc_sopfib p).

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
             (HB : is_univalent_2_1 B)
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

  Definition is_classifying_full
             (HB : is_univalent_2_1 B)
    : UU
    := ∏ (x : B)
         (f g : x --> s)
         (β : disc_sopfib_slice HB x ⟦ pr1 (pb _ f) , pr1 (pb _ g) ⟧),
       ∑ (α : f ==> g),
       pb_disc_sopfib_mor HB α = β.

  Definition is_classifying_faithful
             (HB : is_univalent_2_1 B)
    : UU
    := ∏ (x : B)
         (f g : x --> s)
         (α β : f ==> g),
       pb_disc_sopfib_mor HB α = pb_disc_sopfib_mor HB β
       →
       α = β.

  Definition is_classifying
             (HB : is_univalent_2_1 B)
    : UU
    := is_classifying_full HB × is_classifying_faithful HB.

  Definition eq_disc_slice_mor
             (HB : is_univalent_2_1 B)
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
             (HB : is_univalent_2_1 B)
             {x : B}
             {g₁ g₂ : disc_sopfib_slice HB x}
             {α β : g₁ --> g₂}
             (q : α = β)
    : invertible_2cell (pr1 α) (pr1 β)
    := idtoiso_2_1 _ _ (maponpaths pr1 q).

  Definition eq_slice_to_coh
             (HB : is_univalent_2_1 B)
             {x : B}
             {g₁ g₂ : disc_sopfib_slice HB x}
             {α β : g₁ --> g₂}
             (q : α = β)
    : pr122 α • (eq_slice_to_inv2cell HB q ▹ _)
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
End ClassifyingDiscreteOpfibration.





Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Elements.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Morphisms.Examples.MorphismsInBicatOfUnivCats.

Definition test
  : @map_to_disp_sopfib bicat_of_univ_cats _ _ set_of_pointed_set.
Proof.
  intros X P.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, (_ ,, _))) ; cbn in *.
  - exact (univalent_cat_of_elems P).
  - exact (cat_of_elems_forgetful P).
  - split.
    + admit.
    + split.
      * apply cat_faithful_is_faithful_1cell.
        apply pr1_category_faithful.
        intro ; intros.
        apply disp_mor_elems_isaprop.
      * apply cat_conservative_is_conservative_1cell.
        apply groupoidal_disp_cat_to_conservative.
        intro ; intros.
        apply is_iso_disp_cat_of_elems.
  - exact (cat_of_elems_to_pointed P).
  - use invertible_2cell_is_nat_iso.
    exact (cat_of_elems_commute_iso P).
  - split.
    + intro q.
      use make_pb_1cell.
      * cbn.
        apply (functor_to_cat_of_elems
                 _
                 (pb_cone_pr1 q)
                 (pb_cone_pr2 q)).
        apply invertible_2cell_to_nat_iso.
        apply (pb_cone_cell q).
      * apply nat_iso_to_invertible_2cell.
        apply functor_to_cat_of_elems_pointed.
      * apply nat_iso_to_invertible_2cell.
        apply functor_to_cat_of_elems_forgetful.
      * use nat_trans_eq ; [ apply homset_property | ].
        intro x ; cbn.
        admit.
    + intros C' G₁ G₂ τ₁ τ₂ p.
      use iscontraprop1.
      * admit.
      * simple refine (_ ,, _ ,, _).
        ** refine (nat_trans_to_cat_of_elems P τ₁ τ₂ _).
           intro x.
           pose (q := eqtohomot (nat_trans_eq_pointwise p x)).
           cbn in q.
           apply q.
        ** use nat_trans_eq ; [ apply homset_property | ].
           cbn.
           admit.
        ** use nat_trans_eq ; [ apply homset_property | ].
           cbn.
           admit.
Admitted.




(**
 - It is a pullback

     ∫ F ---> Set_*
      |        |
      V        V
      C ----> Set
 *)




Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Morphisms.Examples.MorphismsInOneTypes.

Definition hSet_one_type
  : one_types.
Proof.
  use make_one_type.
  - exact hSet.
  - apply isofhlevel_HLevel.
Defined.

Definition pointed_set
  : UU
  := ∑ (X : hSet), X.

Definition isofhlevel_3_pointed_set
  : isofhlevel 3 pointed_set.
Proof.
  use isofhleveltotal2.
  - apply isofhlevel_HLevel.
  - intro X.
    apply hlevelntosn.
    exact (pr2 X).
Defined.

Definition pointed_set_one_type
  : one_types.
Proof.
  use make_one_type.
  - exact pointed_set.
  - exact isofhlevel_3_pointed_set.
Defined.

Definition set_of_pointed_set
  : pointed_set_one_type --> hSet_one_type
  := λ X, pr1 X.


Definition internal_sopfib_set_of_pointed_set
  : internal_sopfib set_of_pointed_set.
Proof.
  apply locally_grpd_internal_sopfib.
  apply one_type_2cell_iso.
Defined.

Definition discrete_set_of_pointed_set
  : discrete_1cell set_of_pointed_set.
Proof.
  split.
  - use one_types_is_incl_faithful_1cell.
    intros X Y.
    induction X as [ X x ].
    induction Y as [ Y y ].
    intros p ; cbn in p.
    use isaproptotal2.
    + intros q.
      use invproofirrelevance.
      intros r₁ r₂.
      apply hSet_one_type.
    + cbn.
      intros q₁ q₂ r₁ r₂.
      refine (!(homotinvweqweq (total2_paths_equiv _ _ _) _) @ _).
      refine (_ @ homotinvweqweq (total2_paths_equiv _ _ _) _).
      apply maponpaths.
      cbn.
      use total2_paths_f.
      * exact (r₁ @ !r₂).
      * apply (pr2 Y).
  - apply conservative_1cell_locally_groupoid ; cbn.
    exact one_type_2cell_iso.
Defined.


Section GrothendieckOneTypes.
  Context {X : one_type}
          (P : X → hSet).

  Definition total_of
    : one_type.
  Proof.
    use make_one_type.
    - exact (∑ (x : X), P x).
    - use isofhleveltotal2.
      + exact (pr2 X).
      + intro x.
        apply hlevelntosn.
        exact (pr2 (P x)).
  Defined.

  Definition total_of_pr1
    : total_of → X
    := pr1.

  Definition discrete_total_of
    : discrete_1cell (total_of_pr1 : one_types ⟦ _ , _ ⟧).
  Proof.
    split.
    - use one_types_is_incl_faithful_1cell.
      intros x y.
      induction x as [ x Px ].
      induction y as [ y Py ].
      intros p ; cbn in p.
      use isaproptotal2.
      + intros q.
        use invproofirrelevance.
        intros r₁ r₂.
        apply (pr2 X).
      + cbn.
        intros q₁ q₂ r₁ r₂.
        refine (!(homotinvweqweq (total2_paths_equiv _ _ _) _) @ _).
        refine (_ @ homotinvweqweq (total2_paths_equiv _ _ _) _).
        apply maponpaths.
        cbn.
        use total2_paths_f.
        * exact (r₁ @ !r₂).
        * apply (pr2 (P _)).
    - apply conservative_1cell_locally_groupoid ; cbn.
      exact one_type_2cell_iso.
  Defined.

  Definition disc_sopfib_total_of
    : disc_sopfib (total_of_pr1 : one_types ⟦ _ , _ ⟧).
  Proof.
    split.
    - apply locally_grpd_internal_sopfib.
      apply one_type_2cell_iso.
    - exact discrete_total_of.
  Defined.

  Definition set_of_total
    : total_of → pointed_set
    := λ z, P (pr1 z) ,, pr2 z.

  Definition total_of_comm
    : @invertible_2cell
        one_types
        _ _
        (λ x, set_of_pointed_set (set_of_total x))
        (λ x, P (total_of_pr1 x)).
  Proof.
    use make_invertible_2cell.
    - exact (λ _, idpath _).
    - apply one_type_2cell_iso.
  Defined.

  Let cone : pb_cone set_of_pointed_set P
    := @make_pb_cone
         one_types
         _ _ _ _ _
         total_of
         (set_of_total : one_types ⟦ total_of , pointed_set_one_type ⟧)
         total_of_pr1
         total_of_comm.

  Section TotalUMP1.
    Context (q : pb_cone set_of_pointed_set P).

    Let qπ₁ : q --> pointed_set_one_type
      := pb_cone_pr1 q.
    Let qπ₂ : q --> X
      := pb_cone_pr2 q.
    Let qcell
      := pr1 (pb_cone_cell q).

    Definition pb_ump_1_total_mor
      : q --> cone.
    Proof.
      intro x.
      simple refine (qπ₂ x ,, _).
      exact (transportf (λ Z, Z) (maponpaths pr1hSet (qcell x)) (pr2 (qπ₁ x))).
    Defined.

    Definition pb_ump_1_total_mor_pr1
      : invertible_2cell
          (pb_ump_1_total_mor · pb_cone_pr1 cone)
          (pb_cone_pr1 q).
    Proof.
      use make_invertible_2cell.
      - intro x.
        use total2_paths_f.
        + exact (!(qcell x)).
        + abstract
            (cbn ;
             rewrite <- transport_idfun ;
             rewrite transport_f_f ;
             rewrite pathsinv0r ;
             apply idpath).
      - apply one_type_2cell_iso.
    Defined.

    Definition pb_ump_1_total_mor_pr2
      : invertible_2cell
          (pb_ump_1_total_mor · pb_cone_pr2 cone)
          (pb_cone_pr2 q).
    Proof.
      use make_invertible_2cell.
      - intro x.
        apply idpath.
      - apply one_type_2cell_iso.
    Defined.
  End TotalUMP1.

  Definition pb_ump_1_total
    : pb_ump_1 cone.
  Proof.
    intro q.
    use make_pb_1cell.
    - exact (pb_ump_1_total_mor q).
    - exact (pb_ump_1_total_mor_pr1 q).
    - exact (pb_ump_1_total_mor_pr2 q).
    - cbn.
      use funextsec.
      intro x.
      unfold funhomotsec, homotcomp, homotfun.
      cbn.
      rewrite !pathscomp0rid.
      unfold set_of_pointed_set.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (base_total2_paths
                 (pb_ump_1_total_mor_pr1_subproof q x)).
      }
      apply pathsinv0l.
  Defined.

  Definition pb_ump_2_total
    : pb_ump_2 cone.
  Proof.
  Admitted.

  Definition has_pb_ump_total
    : has_pb_ump cone.
  Proof.
    split.
    - exact pb_ump_1_total.
    - exact pb_ump_2_total.
  Defined.
End GrothendieckOneTypes.

Definition test
  : map_to_disp_sopfib set_of_pointed_set.
Proof.
  intros X P.
  simple refine ((_ ,, (_ ,, _)) ,, (_ ,, (_ ,, _))) ; cbn in *.
  - exact (total_of P).
  - exact (total_of_pr1 P).
  - exact (disc_sopfib_total_of P).
  - exact (set_of_total P).
  - exact (total_of_comm P).
  - exact (has_pb_ump_total P).
Defined.

Definition disc_sopfib_set_of_pointed_set
  : disc_sopfib set_of_pointed_set
  := internal_sopfib_set_of_pointed_set ,, discrete_set_of_pointed_set.

Definition test'
  : is_classifying
      set_of_pointed_set
      disc_sopfib_set_of_pointed_set
      test
      one_types_is_univalent_2_1.
Proof.
  split.
  - intros X f g α.
    simple refine (_ ,, _).
    + admit.
    + use eq_disc_slice_mor ; cbn.
      * use make_invertible_2cell.
        ** intro x.
           cbn in x ; cbn.
           unfold pb_ump_1_total_mor.
           cbn.
           use total2_paths_f.
           *** exact (pr122 α x).
           *** cbn.
               rewrite <- transport_idfun.
               unfold funhomotsec.
               cbn.
               unfold total_of_pr1.
               admit.
        ** apply one_type_2cell_iso.
      * use funextsec.
        intro x.
        unfold homotcomp, invhomot, homotfun ; cbn.
        unfold total_of_pr1.
        admit.
    + intro x.
      induction α as [ h [ Hh γ ]].
      pose (p := pr1 γ).
      cbn in p.
      unfold homotsec in p.
      cbn in h.
      unfold total_of_pr1 in *.
      cbn in γ.

      cbn in *.
      cbn in α.
      cbn.
    cbn.
    admit.
  - intros X f g α β p.
    use funextsec.
    intro x.
    pose (pr1 (eq_slice_to_inv2cell one_types_is_univalent_2_1 p)) as i.
    cbn in i.
    unfold homotsec in i.
    unfold pb_ump_1_total_mor in i.
    cbn in i.
    unfold total_of_pr1 in i.
    pose (eq_slice_to_coh one_types_is_univalent_2_1 p) as j.
    cbn in j.
    unfold homotcomp, invhomot, homotfun in j.
    cbn in j.

    assert (pr1hSet (f x)) as Z.
    {
      admit.
    }
    pose (eqtohomot j (x ,, Z)) as r.
    cbn in r.
    pose (fiber_paths (i (x ,, Z))) as r'.
    cbn in r'.
    unfold base_paths in r'.
    rewrite <- !transport_idfun in r'.
    unfold pr1hSet, funhomotsec in r'.
    cbn in r'.
    unfold total_of_pr1 in r.
    unfold i in r'.
    pose (maponpaths (λ z, transportf _ z _) (!r) @ r') as q.
    cbn in q.
    rewrite <- !transport_idfun in q.
    Search transportf.
    Check transportbfinv.
    rewrite r in r'.
    cbn in r.
    cbn in r'.




(*
    Let ℓ : p /≃ f --> e := pr1 (pr1 Hp₁ (p /≃ f) π₁ (π₂ · g) (pb_cell p f • (π₂ ◃ α))).
    Let ζ : π₁ ==> ℓ
      := pr12 (pr1 Hp₁ (p /≃ f) π₁ (π₂ · g) (pb_cell p f • (π₂ ◃ α))).
    Let γ : invertible_2cell (π₂ · g) (ℓ · p)
      := pr122 (pr1 Hp₁ (p /≃ f) π₁ (π₂ · g) (pb_cell p f • (π₂ ◃ α))).
    Let Hζ : is_opcartesian_2cell_sopfib p ζ
      := pr1 (pr222 (pr1 Hp₁ (p /≃ f) π₁ (π₂ · g) (pb_cell p f • (π₂ ◃ α)))).

    Definition mor_of_pb_disc_sopfib_mor
      : p /≃ f --> p /≃ g
      := ℓ ⊗[ inv_of_invertible_2cell γ ] π₂.

    Definition pb_disc_sopfib_mor_preserves_opcartesian
      : mor_preserves_opcartesian π₂ π₂ mor_of_pb_disc_sopfib_mor.
    Proof.
      use mor_preserves_opcartesian_pb_ump_mor_alt.
      intros z h₁ h₂ β Hβ.
      use (is_opcartesian_2cell_sopfib_precomp _ (_ ◃ ζ)).
      - exact ((β ▹ π₁) • (h₂ ◃ ζ)).
      - apply Hp₁.
        exact Hζ.
      - use vcomp_is_opcartesian_2cell_sopfib.
        + exact (from_pb_opcartesian (pb_obj_has_pb_ump p f) Hp₁ _ Hβ).
        + apply Hp₁.
          exact Hζ.
      - abstract
          (rewrite vcomp_whisker ;
           apply idpath).
    Defined.

    Definition cell_of_pb_disc_sopfib_mor
      : invertible_2cell π₂ (mor_of_pb_disc_sopfib_mor · π₂)
      := inv_of_invertible_2cell (mor_to_pb_obj_pr2 _ _ _).

    Definition pb_disc_sopfib_mor
      : pb_disc_sopfib_ob f --> pb_disc_sopfib_ob g.
    Proof.
      simple refine (_ ,, (_ ,, tt) ,, _) ; cbn.
      - exact mor_of_pb_disc_sopfib_mor.
      - exact pb_disc_sopfib_mor_preserves_opcartesian.
      - exact cell_of_pb_disc_sopfib_mor.
    Defined.
  End PbOfMor.


  Definition disp_sopfib_mor_of
             (pb : map_to_disp_sopfib)
             {x : B}
             {f g : x --> s}
             (α : f ==> g)
    : UU.
  Proof.

End ClassifyingDiscreteOpfibrationBasics.



Section ClassifyingDiscreteOpfibration.
  Context (B : bicat_with_pb)
          (HB : is_univalent_2_1 B)
          {e s : B}
          (p : e --> s)
          (Hp : disc_sopfib p).

  Definition disc_sopfib_of
             {x : B}
             (f : x --> s)
    : UU
    := ∑ (z : B)
         (pf : z --> x),
       disc_sopfib pf.

  Definition disp_sopfib_map
    : UU
    := ∏ (x : B)
         (f : x --> s),
       disc_sopfib_of f.



  Definition pb_disc_sopfib_ob
             {x : B}
             (f : hom x s)
    : disc_sopfib_of f.
  Proof.
    refine (p /≃ f ,, π₂ ,, _ ,, _).
    - exact (pb_of_sopfib
               (pb_obj_has_pb_ump p f)
               (pr1 Hp)).
    - exact (pb_of_discrete_1cell
               (pb_obj_has_pb_ump p f)
               (pr2 Hp)).
  Defined.







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

  Section PbOfMor.
    Context {x : B}
            {f g : hom x s}
            (α : f --> g).

    Let ℓ : p /≃ f --> e := pr1 (pr1 Hp₁ (p /≃ f) π₁ (π₂ · g) (pb_cell p f • (π₂ ◃ α))).
    Let ζ : π₁ ==> ℓ
      := pr12 (pr1 Hp₁ (p /≃ f) π₁ (π₂ · g) (pb_cell p f • (π₂ ◃ α))).
    Let γ : invertible_2cell (π₂ · g) (ℓ · p)
      := pr122 (pr1 Hp₁ (p /≃ f) π₁ (π₂ · g) (pb_cell p f • (π₂ ◃ α))).
    Let Hζ : is_opcartesian_2cell_sopfib p ζ
      := pr1 (pr222 (pr1 Hp₁ (p /≃ f) π₁ (π₂ · g) (pb_cell p f • (π₂ ◃ α)))).

    Definition mor_of_pb_disc_sopfib_mor
      : p /≃ f --> p /≃ g
      := ℓ ⊗[ inv_of_invertible_2cell γ ] π₂.

    Definition pb_disc_sopfib_mor_preserves_opcartesian
      : mor_preserves_opcartesian π₂ π₂ mor_of_pb_disc_sopfib_mor.
    Proof.
      use mor_preserves_opcartesian_pb_ump_mor_alt.
      intros z h₁ h₂ β Hβ.
      use (is_opcartesian_2cell_sopfib_precomp _ (_ ◃ ζ)).
      - exact ((β ▹ π₁) • (h₂ ◃ ζ)).
      - apply Hp₁.
        exact Hζ.
      - use vcomp_is_opcartesian_2cell_sopfib.
        + exact (from_pb_opcartesian (pb_obj_has_pb_ump p f) Hp₁ _ Hβ).
        + apply Hp₁.
          exact Hζ.
      - abstract
          (rewrite vcomp_whisker ;
           apply idpath).
    Defined.

    Definition cell_of_pb_disc_sopfib_mor
      : invertible_2cell π₂ (mor_of_pb_disc_sopfib_mor · π₂)
      := inv_of_invertible_2cell (mor_to_pb_obj_pr2 _ _ _).

    Definition pb_disc_sopfib_mor
      : pb_disc_sopfib_ob f --> pb_disc_sopfib_ob g.
    Proof.
      simple refine (_ ,, (_ ,, tt) ,, _) ; cbn.
      - exact mor_of_pb_disc_sopfib_mor.
      - exact pb_disc_sopfib_mor_preserves_opcartesian.
      - exact cell_of_pb_disc_sopfib_mor.
    Defined.
  End PbOfMor.

  Definition is_classifying_full
    : UU
    := ∏ (x : B)
         (f g : x --> s)
         (β : pb_disc_sopfib_ob f --> pb_disc_sopfib_ob g),
       ∑ (α : f ==> g),
       pb_disc_sopfib_mor α = β.

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














Section ClassifyingDiscreteOpfibration.
  Context (B : bicat_with_pb)
          (HB : is_univalent_2_1 B)
          {e s : B}
          (p : e --> s)
          (Hp₁ : internal_sopfib p)
          (Hp₂ : discrete_1cell p).

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

  Definition pb_disc_sopfib_ob
             {x : B}
             (f : hom x s)
    : disc_sopfib_slice HB x.
  Proof.
    refine (p /≃ f ,, π₂ ,, _ ,, _).
    - exact (pb_of_sopfib
               (pb_obj_has_pb_ump p f)
               Hp₁).
    - exact (pb_of_discrete_1cell
               (pb_obj_has_pb_ump p f)
               Hp₂).
  Defined.

  Section PbOfMor.
    Context {x : B}
            {f g : hom x s}
            (α : f --> g).

    Let ℓ : p /≃ f --> e := pr1 (pr1 Hp₁ (p /≃ f) π₁ (π₂ · g) (pb_cell p f • (π₂ ◃ α))).
    Let ζ : π₁ ==> ℓ
      := pr12 (pr1 Hp₁ (p /≃ f) π₁ (π₂ · g) (pb_cell p f • (π₂ ◃ α))).
    Let γ : invertible_2cell (π₂ · g) (ℓ · p)
      := pr122 (pr1 Hp₁ (p /≃ f) π₁ (π₂ · g) (pb_cell p f • (π₂ ◃ α))).
    Let Hζ : is_opcartesian_2cell_sopfib p ζ
      := pr1 (pr222 (pr1 Hp₁ (p /≃ f) π₁ (π₂ · g) (pb_cell p f • (π₂ ◃ α)))).

    Definition mor_of_pb_disc_sopfib_mor
      : p /≃ f --> p /≃ g
      := ℓ ⊗[ inv_of_invertible_2cell γ ] π₂.

    Definition pb_disc_sopfib_mor_preserves_opcartesian
      : mor_preserves_opcartesian π₂ π₂ mor_of_pb_disc_sopfib_mor.
    Proof.
      use mor_preserves_opcartesian_pb_ump_mor_alt.
      intros z h₁ h₂ β Hβ.
      use (is_opcartesian_2cell_sopfib_precomp _ (_ ◃ ζ)).
      - exact ((β ▹ π₁) • (h₂ ◃ ζ)).
      - apply Hp₁.
        exact Hζ.
      - use vcomp_is_opcartesian_2cell_sopfib.
        + exact (from_pb_opcartesian (pb_obj_has_pb_ump p f) Hp₁ _ Hβ).
        + apply Hp₁.
          exact Hζ.
      - abstract
          (rewrite vcomp_whisker ;
           apply idpath).
    Defined.

    Definition cell_of_pb_disc_sopfib_mor
      : invertible_2cell π₂ (mor_of_pb_disc_sopfib_mor · π₂)
      := inv_of_invertible_2cell (mor_to_pb_obj_pr2 _ _ _).

    Definition pb_disc_sopfib_mor
      : pb_disc_sopfib_ob f --> pb_disc_sopfib_ob g.
    Proof.
      simple refine (_ ,, (_ ,, tt) ,, _) ; cbn.
      - exact mor_of_pb_disc_sopfib_mor.
      - exact pb_disc_sopfib_mor_preserves_opcartesian.
      - exact cell_of_pb_disc_sopfib_mor.
    Defined.
  End PbOfMor.

  Definition is_classifying_full
    : UU
    := ∏ (x : B)
         (f g : x --> s)
         (β : pb_disc_sopfib_ob f --> pb_disc_sopfib_ob g),
       ∑ (α : f ==> g),
       pb_disc_sopfib_mor α = β.

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




  Definition test
    : UU.
  Proof.
    pose @pb_disc_sopfib_ob.
    unfold disc_sopfib_slice in *.
    cbn in *.
    refine (∏ (x : B)
              (f : x --> s),
            ∑ (z : B)
              (p : z --> x),
            discrete_sopfib p
            ×
            _).
    Check pb_disc_sopfib_ob f.
    pose
    Check pb_disc_sopfib_ob.
End ClassifyingDiscreteOpfibration.






Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Limits.Examples.OneTypesLimits.
Require Import UniMath.Bicategories.Morphisms.Examples.MorphismsInOneTypes.

Definition hSet_one_type
  : one_types.
Proof.
  use make_one_type.
  - exact hSet.
  - apply isofhlevel_HLevel.
Defined.

Definition pointed_set
  : UU
  := ∑ (X : hSet), X.

Definition isofhlevel_3_pointed_set
  : isofhlevel 3 pointed_set.
Proof.
  use isofhleveltotal2.
  - apply isofhlevel_HLevel.
  - intro X.
    apply hlevelntosn.
    exact (pr2 X).
Defined.

Definition pointed_set_one_type
  : one_types.
Proof.
  use make_one_type.
  - exact pointed_set.
  - exact isofhlevel_3_pointed_set.
Defined.

Definition set_of_pointed_set
  : pointed_set_one_type --> hSet_one_type
  := λ X, pr1 X.


Definition internal_sopfib_set_of_pointed_set
  : internal_sopfib set_of_pointed_set.
Proof.
  apply locally_grpd_internal_sopfib.
  apply one_type_2cell_iso.
Defined.

Definition discrete_set_of_pointed_set
  : discrete_1cell set_of_pointed_set.
Proof.
  split.
  - use one_types_is_incl_faithful_1cell.
    intros X Y.
    induction X as [ X x ].
    induction Y as [ Y y ].
    intros p ; cbn in p.
    use isaproptotal2.
    + intros q.
      use invproofirrelevance.
      intros r₁ r₂.
      apply hSet_one_type.
    + cbn.
      intros q₁ q₂ r₁ r₂.
      refine (!(homotinvweqweq (total2_paths_equiv _ _ _) _) @ _).
      refine (_ @ homotinvweqweq (total2_paths_equiv _ _ _) _).
      apply maponpaths.
      cbn.
      use total2_paths_f.
      * exact (r₁ @ !r₂).
      * apply (pr2 Y).
  - apply conservative_1cell_locally_groupoid ; cbn.
    exact one_type_2cell_iso.
Defined.

Definition one_types_classifying_disc_opfib
  : is_classifying
      (_ ,, one_types_has_pb)
      one_types_is_univalent_2_1
      set_of_pointed_set
      internal_sopfib_set_of_pointed_set
      discrete_set_of_pointed_set.
Proof.
  split.
  - intros Z f g α.
    cbn in *.
    admit.
  - intros Z f g α β p.
    cbn in *.
    unfold pb_disc_sopfib_mor in p.
    cbn in p.
    pose (eqtohomot (maponpaths pr1 p)) as p0.
    cbn in p0.
    unfold homotsec in p0.
    cbn in p0.
    cbn in p0.
    Check maponpaths pr1 p.
 *)
