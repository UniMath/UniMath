(**
 Properties of projection functions

 Contents:
 1. First projection is a Street fibration
 2. First projection is a Street opfibration
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.

Local Open Scope cat.

(**
 1. First projection is a Street fibration
 *)
Section ProjectionSFib.
  Context {B : bicat_with_binprod}
          (b₁ b₂ : B).

  Section InvertibleToCartesian.
    Context {a : B}
            {f g : a --> b₁ ⊗ b₂}
            (α : f ==> g)
            (Hα : is_invertible_2cell (α ▹ π₂)).

    Definition invertible_to_cartesian_unique
               (h : a --> b₁ ⊗ b₂)
               (β : h ==> g)
               (δp : h · π₁ ==> f · π₁)
               (q : β ▹ π₁ = δp • (α ▹ π₁))
      : isaprop (∑ (δ : h ==> f), δ ▹ π₁ = δp × δ • α = β).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ].
      use binprod_ump_2cell_unique_alt.
      - apply (pr2 B).
      - exact (pr12 φ₁ @ !(pr12 φ₂)).
      - use (vcomp_rcancel _ Hα).
        rewrite !rwhisker_vcomp.
        apply maponpaths.
        exact (pr22 φ₁ @ !(pr22 φ₂)).
    Qed.

    Definition invertible_to_cartesian
      : is_cartesian_2cell_sfib π₁ α.
    Proof.
      intros h β δp q.
      use iscontraprop1.
      - exact (invertible_to_cartesian_unique h β δp q).
      - simple refine (_ ,, _ ,, _).
        + use binprod_ump_2cell.
          * apply (pr2 B).
          * exact δp.
          * exact (β ▹ _ • Hα^-1).
        + apply binprod_ump_2cell_pr1.
        + use binprod_ump_2cell_unique_alt.
          * apply (pr2 B).
          * abstract
              (rewrite <- !rwhisker_vcomp ;
               rewrite binprod_ump_2cell_pr1 ;
               exact (!q)).
          * abstract
              (rewrite <- !rwhisker_vcomp ;
               rewrite binprod_ump_2cell_pr2 ;
               rewrite !vassocl ;
               refine (_ @ id2_right _) ;
               rewrite vcomp_linv ;
               apply idpath).
    Defined.
  End InvertibleToCartesian.

  Section CartesianToInvertible.
    Context {a : B}
            {f g : a --> b₁ ⊗ b₂}
            (α : f ==> g)
            (Hα : is_cartesian_2cell_sfib π₁ α).

    Let h : a --> b₁ ⊗ b₂ := ⟨ f · π₁, g · π₂ ⟩.
    Let δ : h ==> g
      := binprod_ump_2cell
           (pr2 (pr2 B _ _))
           (binprod_ump_1cell_pr1 _ _ _ _ • (α ▹ _))
           (binprod_ump_1cell_pr2 _ _ _ _).
    Let hπ₁ : h · π₁ ==> f · π₁ := binprod_ump_1cell_pr1 _ _ _ _.

    Local Lemma cartesian_to_invertible_eq
      : δ ▹ π₁ = hπ₁ • (α ▹ π₁).
    Proof.
      apply binprod_ump_2cell_pr1.
    Qed.

    Let lift : ∃! δ0 : h ==> f, δ0 ▹ π₁ = hπ₁ × δ0 • α = δ
      := Hα h δ hπ₁ cartesian_to_invertible_eq.
    Let lift_map : h ==> f := pr11 lift.
    Let inv : g · π₂ ==> f · π₂
      := (binprod_ump_1cell_pr2 _ _ _ _)^-1 • (lift_map ▹ π₂).

    Let ζ : f ==> f
      := binprod_ump_2cell
           (pr2 (pr2 B _ _))
           (id2 _)
           ((α ▹ π₂) • inv).

    Local Lemma cartesian_to_invertible_map_inv_help
      : ζ = id₂ f.
    Proof.
      refine (maponpaths
                (λ z, pr1 z)
                (proofirrelevance
                   _
                   (isapropifcontr (Hα f α (id2 _) (!(id2_left _))))
                   (ζ ,, _ ,, _)
                   (id₂ _ ,, _ ,, _))).
      - apply binprod_ump_2cell_pr1.
      - use binprod_ump_2cell_unique_alt.
        + apply (pr2 B).
        + rewrite <- rwhisker_vcomp.
          unfold ζ.
          rewrite binprod_ump_2cell_pr1.
          apply id2_left.
        + unfold ζ, inv.
          rewrite <- rwhisker_vcomp.
          rewrite binprod_ump_2cell_pr2.
          rewrite !vassocl.
          rewrite rwhisker_vcomp.
          etrans.
          {
            do 3 apply maponpaths.
            apply (pr221 lift).
          }
          unfold δ.
          rewrite binprod_ump_2cell_pr2.
          rewrite vcomp_linv.
          apply id2_right.
      - apply id2_rwhisker.
      - apply id2_left.
    Qed.

    Local Lemma cartesian_to_invertible_map_inv
      : (α ▹ π₂) • inv = id₂ (f · π₂).
    Proof.
      refine (_ @ maponpaths (λ z, z ▹ π₂) cartesian_to_invertible_map_inv_help @ _).
      - unfold ζ.
        refine (!_).
        apply binprod_ump_2cell_pr2.
      - apply id2_rwhisker.
    Qed.

    Local Lemma cartesian_to_invertible_inv_map
      : inv • (α ▹ π₂) = id₂ (g · π₂).
    Proof.
      unfold inv.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      etrans.
      {
        do 2 apply maponpaths.
        exact (pr221 lift).
      }
      unfold δ.
      etrans.
      {
        apply maponpaths.
        apply binprod_ump_2cell_pr2.
      }
      apply vcomp_linv.
    Qed.

    Definition cartesian_to_invertible
      : is_invertible_2cell (α ▹ π₂).
    Proof.
      unfold is_cartesian_2cell_sfib in Hα.
      use make_is_invertible_2cell.
      - exact inv.
      - exact cartesian_to_invertible_map_inv.
      - exact cartesian_to_invertible_inv_map.
    Defined.
  End CartesianToInvertible.

  Definition pr1_internal_cleaving
    : internal_sfib_cleaving (π₁ : b₁ ⊗ b₂ --> b₁).
  Proof.
    intros a f g α.
    simple refine (⟨ f , g · π₂ ⟩
                     ,, ⟪ α , id2 _ ⟫ • prod_1cell_eta _ g
                     ,, prod_1cell_pr1 _ f _
                     ,, _
                     ,, _) ; simpl.
    - apply invertible_to_cartesian.
      rewrite <- rwhisker_vcomp.
      use is_invertible_2cell_vcomp.
      + rewrite prod_2cell_pr2.
        is_iso.
        apply prod_1cell_pr2.
      + is_iso.
        apply prod_1cell_eta.
    - abstract
        (unfold prod_1cell_eta_map ;
         rewrite <- !rwhisker_vcomp ;
         etrans ;
         [ apply maponpaths ;
           apply binprod_ump_2cell_pr1
         | ] ;
         rewrite prod_2cell_pr1 ;
         rewrite !vassocl ;
         rewrite vcomp_linv ;
         rewrite id2_right ;
         apply idpath).
  Defined.

  Definition pr1_lwhisker_is_cartesian
    : lwhisker_is_cartesian (π₁ : b₁ ⊗ b₂ --> b₁).
  Proof.
    intros x y h f g γ Hγ.
    apply invertible_to_cartesian.
    pose (cartesian_to_invertible _ Hγ) as i.
    use make_is_invertible_2cell.
    - exact (rassociator _ _ _ • (h ◃ i^-1) • lassociator _ _ _).
    - rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      refine (_ @ rassociator_lassociator _ _ _).
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      apply id2_left.
    - rewrite !vassocl.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocr.
      refine (_ @ rassociator_lassociator _ _ _).
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      apply id2_right.
  Qed.

  Definition pr1_internal_sfib
    : internal_sfib (π₁ : b₁ ⊗ b₂ --> b₁).
  Proof.
    split.
    - exact pr1_internal_cleaving.
    - exact pr1_lwhisker_is_cartesian.
  Defined.
End ProjectionSFib.

(**
 2. First projection is a Street opfibration
 *)
Section ProjectionSOpFib.
  Context {B : bicat_with_binprod}
          (b₁ b₂ : B).

  Section InvertibleToOpCartesian.
    Context {a : B}
            {f g : a --> b₁ ⊗ b₂}
            (α : f ==> g)
            (Hα : is_invertible_2cell (α ▹ π₂)).

    Definition invertible_to_opcartesian_unique
               (h : a --> b₁ ⊗ b₂)
               (β : f ==> h)
               (δp : g · π₁ ==> h · π₁)
               (q : β ▹ π₁ = (α ▹ π₁) • δp)
      : isaprop (∑ (δ : g ==> h), δ ▹ π₁ = δp × α • δ = β).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ].
      use binprod_ump_2cell_unique_alt.
      - apply (pr2 B).
      - exact (pr12 φ₁ @ !(pr12 φ₂)).
      - use (vcomp_lcancel _ Hα).
        rewrite !rwhisker_vcomp.
        apply maponpaths.
        exact (pr22 φ₁ @ !(pr22 φ₂)).
    Qed.

    Definition invertible_to_opcartesian
      : is_opcartesian_2cell_sopfib π₁ α.
    Proof.
      intros h β δp q.
      use iscontraprop1.
      - exact (invertible_to_opcartesian_unique h β δp q).
      - simple refine (_ ,, _ ,, _).
        + use binprod_ump_2cell.
          * apply (pr2 B).
          * exact δp.
          * exact (Hα^-1 • (β ▹ _)).
        + apply binprod_ump_2cell_pr1.
        + use binprod_ump_2cell_unique_alt.
          * apply (pr2 B).
          * abstract
              (rewrite <- !rwhisker_vcomp ;
               rewrite binprod_ump_2cell_pr1 ;
               exact (!q)).
          * abstract
              (rewrite <- !rwhisker_vcomp ;
               rewrite binprod_ump_2cell_pr2 ;
               rewrite !vassocr ;
               refine (_ @ id2_left _) ;
               rewrite vcomp_rinv ;
               apply idpath).
    Defined.
  End InvertibleToOpCartesian.

  Section OpCartesianToInvertible.
    Context {a : B}
            {f g : a --> b₁ ⊗ b₂}
            (α : f ==> g)
            (Hα : is_opcartesian_2cell_sopfib π₁ α).

    Let h : a --> b₁ ⊗ b₂ := ⟨ g · π₁, f · π₂ ⟩.
    Let δ : f ==> h
      := binprod_ump_2cell
           (pr2 (pr2 B _ _))
           (α ▹ _ • (binprod_ump_1cell_pr1 _ _ (g · π₁) (f · π₂))^-1)
           ((binprod_ump_1cell_pr2 _ _ (g · π₁) (f · π₂))^-1).
    Let hπ₁ : g · π₁ ==> h · π₁
      := (binprod_ump_1cell_pr1 _ _ (g · π₁) (f · π₂))^-1.

    Local Lemma opcartesian_to_invertible_eq
      : δ ▹ π₁ = (α ▹ π₁) • hπ₁.
    Proof.
      apply binprod_ump_2cell_pr1.
    Qed.

    Let lift : ∃! (δ0 : g ==> h), δ0 ▹ π₁ = hπ₁ × α • δ0 = δ
      := Hα h δ hπ₁ opcartesian_to_invertible_eq.
    Let lift_map : g ==> h := pr11 lift.
    Let inv : g · π₂ ==> f · π₂
      := lift_map ▹ π₂ • binprod_ump_1cell_pr2 _ _ _ _.

    Let ζ : g ==> g
      := binprod_ump_2cell
           (pr2 (pr2 B _ _))
           (id2 _)
           (inv • (α ▹ π₂)).

    Local Lemma opcartesian_to_invertible_map_inv_help
      : ζ = id₂ g.
    Proof.
      refine (maponpaths
                (λ z, pr1 z)
                (proofirrelevance
                   _
                   (isapropifcontr (Hα g α (id2 _) (!(id2_right _))))
                   (ζ ,, _ ,, _)
                   (id₂ _ ,, _ ,, _))).
      - apply binprod_ump_2cell_pr1.
      - use binprod_ump_2cell_unique_alt.
        + apply (pr2 B).
        + rewrite <- rwhisker_vcomp.
          unfold ζ.
          rewrite binprod_ump_2cell_pr1.
          apply id2_right.
        + unfold ζ, inv.
          rewrite <- rwhisker_vcomp.
          rewrite binprod_ump_2cell_pr2.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          etrans.
          {
            do 2 apply maponpaths_2.
            apply maponpaths.
            exact (pr221 lift).
          }
          unfold δ.
          etrans.
          {
            do 2 apply maponpaths_2.
            apply binprod_ump_2cell_pr2.
          }
          rewrite vcomp_linv.
          apply id2_left.
      - apply id2_rwhisker.
      - apply id2_right.
    Qed.

    Local Lemma opcartesian_to_invertible_map_inv
      : (α ▹ π₂) • inv = id₂ (f · π₂).
    Proof.
      unfold inv.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (pr221 lift).
      }
      unfold δ.
      etrans.
      {
        apply maponpaths_2.
        apply binprod_ump_2cell_pr2.
      }
      apply vcomp_linv.
    Qed.

    Local Lemma opcartesian_to_invertible_inv_map
      : inv • (α ▹ π₂) = id₂ (g · π₂).
    Proof.
      refine (_ @ maponpaths (λ z, z ▹ π₂) opcartesian_to_invertible_map_inv_help @ _).
      - unfold ζ.
        refine (!_).
        apply binprod_ump_2cell_pr2.
      - apply id2_rwhisker.
    Qed.

    Definition opcartesian_to_invertible
      : is_invertible_2cell (α ▹ π₂).
    Proof.
      unfold is_cartesian_2cell_sfib in Hα.
      use make_is_invertible_2cell.
      - exact inv.
      - exact opcartesian_to_invertible_map_inv.
      - exact opcartesian_to_invertible_inv_map.
    Defined.
  End OpCartesianToInvertible.

  Definition pr1_internal_opcleaving
    : internal_sopfib_opcleaving (π₁ : b₁ ⊗ b₂ --> b₁).
  Proof.
    intros a f g α.
    refine (⟨ g , f · π₂ ⟩
            ,,
            (prod_1cell_eta _ f)^-1 • ⟪ α , id2 _ ⟫
            ,,
            inv_of_invertible_2cell (prod_1cell_pr1 _ g _)
            ,,
            _
            ,,
            _).
    - apply invertible_to_opcartesian.
      rewrite <- rwhisker_vcomp.
      use is_invertible_2cell_vcomp.
      + is_iso.
      + rewrite prod_2cell_pr2.
        is_iso.
        apply prod_1cell_pr2.
    - abstract
        (unfold prod_1cell_eta_map ;
         rewrite <- !rwhisker_vcomp ;
         rewrite prod_2cell_pr1 ;
         cbn ;
         etrans ;
         [ apply maponpaths_2 ;
           apply binprod_ump_2cell_pr1
         | ] ;
         rewrite !vassocr ;
         rewrite vcomp_linv ;
         rewrite id2_left ;
         apply idpath).
  Defined.

  Definition pr1_lwhisker_is_opcartesian
    : lwhisker_is_opcartesian (π₁ : b₁ ⊗ b₂ --> b₁).
  Proof.
    intros x y h f g γ Hγ.
    apply invertible_to_opcartesian.
    pose (opcartesian_to_invertible _ Hγ) as i.
    use make_is_invertible_2cell.
    - exact (rassociator _ _ _ • (h ◃ i^-1) • lassociator _ _ _).
    - rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      refine (_ @ rassociator_lassociator _ _ _).
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite lwhisker_id2.
      apply id2_left.
    - rewrite !vassocl.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocr.
      refine (_ @ rassociator_lassociator _ _ _).
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      rewrite vcomp_linv.
      rewrite lwhisker_id2.
      apply id2_right.
  Qed.

  Definition pr1_internal_sopfib
    : internal_sopfib (π₁ : b₁ ⊗ b₂ --> b₁).
  Proof.
    split.
    - exact pr1_internal_opcleaving.
    - exact pr1_lwhisker_is_opcartesian.
  Defined.
End ProjectionSOpFib.
