(**
 Properties of adjoint equivalences

 In this file, we look at properties of adjoint equivalences

 Contents:
 1. Identity is faithful
 2. Identity is fully faithful
 3. Identity is conservative
 4. Identity is discrete
 5. The identity Street fibration
 6. The identity Street opfibration
 7. Adjoint equivalences are faithful
 8. Adjoint equivalences are fully faithful
 9. Adjoint equivalences are conservative
 10. Adjoint equivalences are discrete
 11. Adjoint equivalences preserve cartesian cells
 12. Adjoint equivalences preserve cartesian cells
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat.
Import Notations.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.DiscreteMorphisms.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.

Local Open Scope cat.

(**
 1. Identity is faithful
 *)
Definition id1_faithful
           {B : bicat}
           (a : B)
  : faithful_1cell (id₁ a).
Proof.
  intros z g₁ g₂ α₁ α₂ p.
  use (vcomp_lcancel (runitor _)).
  {
    is_iso.
  }
  rewrite <- !vcomp_runitor.
  rewrite p.
  apply idpath.
Qed.

(**
 2. Identity is fully faithful
 *)
Definition id1_fully_faithful
           {B : bicat}
           (a : B)
  : fully_faithful_1cell (id₁ a).
Proof.
  use make_fully_faithful.
  - apply id1_faithful.
  - intros z g₁ g₂ αf.
    simple refine (_ ,, _).
    + exact (rinvunitor _ • αf • runitor _).
    + abstract
        (cbn ;
         use (vcomp_rcancel (runitor _)) ; [ is_iso | ] ;
         rewrite !vassocl ;
         rewrite vcomp_runitor ;
         rewrite !vassocr ;
         rewrite runitor_rinvunitor ;
         rewrite id2_left ;
         apply idpath).
Defined.

(**
 3. Identity is conservative
 *)
Definition id1_conservative
           {B : bicat}
           (a : B)
  : conservative_1cell (id₁ a).
Proof.
  intros x g₁ g₂ α Hα.
  pose ((α ▹ id₁ a) • runitor _).
  use eq_is_invertible_2cell.
  - exact (rinvunitor _ • (α ▹ id₁ _) • runitor _).
  - rewrite !vassocl.
    rewrite vcomp_runitor.
    rewrite !vassocr.
    rewrite !rinvunitor_runitor.
    apply id2_left.
  - use is_invertible_2cell_vcomp.
    + use is_invertible_2cell_vcomp.
      * apply is_invertible_2cell_rinvunitor.
      * exact Hα.
    + apply is_invertible_2cell_runitor.
Defined.

(**
 4. Identity is discrete
 *)
Definition id1_discrete
           {B : bicat}
           (a : B)
  : discrete_1cell (id₁ a).
Proof.
  split.
  - exact (id1_faithful a).
  - exact (id1_conservative a).
Defined.

(**
 5. The identity Street fibration
 *)
Section IdentityInternalSFib.
  Context {B : bicat}
          (b : B).

  Local Lemma identity_help
        {x : B}
        {f h : x --> b}
        (δp : h · id₁ b ==> f · id₁ b)
    : ((rinvunitor h • δp) • runitor f) ▹ id₁ b = δp.
  Proof.
    rewrite !vassocl.
    rewrite <- rwhisker_vcomp.
    use vcomp_move_R_pM ; [ is_iso | ].
    cbn.
    use (vcomp_rcancel (runitor _)) ; [ is_iso | ].
    rewrite !vassocl.
    rewrite !vcomp_runitor.
    rewrite !vassocr.
    do 2 apply maponpaths_2.
    rewrite <- runitor_triangle.
    use vcomp_move_R_pM ; [ is_iso | ].
    cbn.
    rewrite runitor_rwhisker.
    rewrite runitor_lunitor_identity.
    apply idpath.
  Qed.

  Definition identity_lift
             {x : B}
             {f g : x --> b}
             (α : f ==> g · id₁ b)
    : is_cartesian_2cell_sfib (id₁ b) (α • runitor g).
  Proof.
    intros h β δp q.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use id1_faithful ;
         exact (pr12 φ₁ @ !(pr12 φ₂))).
    - refine (rinvunitor _ • δp • runitor _ ,, _ ,, _).
      + apply identity_help.
      + abstract
          (rewrite !vassocl ;
           etrans ;
           [ do 2 apply maponpaths ;
             rewrite !vassocr ;
             rewrite <- vcomp_runitor ;
             rewrite !vassocl ;
             rewrite <- vcomp_runitor ;
             rewrite !vassocr ;
             rewrite rwhisker_vcomp ;
             apply idpath
           | ] ;
           etrans ;
           [ apply maponpaths ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             exact (!q)
           | ] ;
           rewrite vcomp_runitor ;
           rewrite !vassocr ;
           rewrite rinvunitor_runitor ;
           apply id2_left).
  Defined.

  Definition identity_internal_cleaving
    : internal_sfib_cleaving (id₁ b).
  Proof.
    intros x f g α.
    refine (f
            ,,
            α • runitor _
            ,,
            runitor_invertible_2cell _
            ,,
            _
            ,,
            _) ; cbn.
    - apply identity_lift.
    - abstract
        (rewrite <- vcomp_runitor ;
         rewrite <- rwhisker_vcomp ;
         apply maponpaths ;
         rewrite <- runitor_triangle ;
         use vcomp_move_L_pM ; [ is_iso | ] ;
         cbn ;
         rewrite runitor_rwhisker ;
         rewrite lunitor_runitor_identity ;
         apply idpath).
  Defined.

  Definition identity_lwhisker_cartesian
    : lwhisker_is_cartesian (id₁ b).
  Proof.
    intros x y h f g γ Hγ k α δp q.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ;
         [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use id1_faithful ;
         exact (pr12 φ₁ @ !(pr12 φ₂))).
    - refine (rinvunitor _ • δp • runitor _ ,, _ ,, _).
      + apply identity_help.
      + abstract
          (rewrite !vassocl ;
           rewrite <- vcomp_runitor ;
           etrans ;
           [ apply maponpaths ;
             rewrite !vassocr ;
             rewrite <- q ;
             apply vcomp_runitor
           | ] ;
           rewrite !vassocr ;
           rewrite rinvunitor_runitor ;
           apply id2_left).
  Defined.

  Definition identity_internal_sfib
    : internal_sfib (id₁ b).
  Proof.
    split.
    - exact identity_internal_cleaving.
    - exact identity_lwhisker_cartesian.
  Defined.
End IdentityInternalSFib.

(**
 6. The identity Street opfibration
 *)
Definition identity_internal_sopfib
           {B : bicat}
           (b : B)
  : internal_sopfib (id₁ b).
Proof.
  apply internal_sfib_is_internal_sopfib.
  exact (@identity_internal_sfib (op2_bicat B) b).
Defined.

(**
 7. Adjoint equivalences are faithful
 *)
Definition adj_equiv_faithful
           {B : bicat}
           {a b : B}
           {l : a --> b}
           (Hl : left_adjoint_equivalence l)
  : faithful_1cell l.
Proof.
  intros z g₁ g₂ α₁ α₂ p.
  pose (η := left_adjoint_unit Hl).
  apply id1_faithful.
  use (vcomp_rcancel (_ ◃ η)).
  {
    is_iso.
    apply (left_equivalence_unit_iso Hl).
  }
  rewrite !vcomp_whisker.
  apply maponpaths.
  use (vcomp_lcancel (rassociator _ _ _)).
  {
    is_iso.
  }
  rewrite <- !rwhisker_rwhisker_alt.
  rewrite p.
  apply idpath.
Qed.

(**
 8. Adjoint equivalences are fully faithful
 *)
Section AdjEquivFullyFaithful.
  Context {B : bicat}
          {a b : B}
          {l : a --> b}
          (Hl : left_adjoint_equivalence l)
          (r := left_adjoint_right_adjoint Hl)
          (η := left_equivalence_unit_iso Hl : invertible_2cell _ (l · r))
          (ε := left_equivalence_counit_iso Hl : invertible_2cell (r · l) _).

  Definition adj_equiv_fully_faithful_inv_cell
             {z : B}
             {g₁ g₂ : z --> a}
             (αf : g₁ · l ==> g₂ · l)
    : g₁ ==> g₂
    := rinvunitor _
       • (g₁ ◃ η)
       • lassociator g₁ l r
       • (αf ▹ r)
       • rassociator g₂ l r
       • (g₂ ◃ η^-1)
       • runitor _.

  Definition adj_equiv_fully_faithful_inv_cell_is_inv_cell
             {z : B}
             {g₁ g₂ : z --> a}
             (αf : g₁ · l ==> g₂ · l)
    : adj_equiv_fully_faithful_inv_cell αf ▹ l = αf.
  Proof.
    unfold adj_equiv_fully_faithful_inv_cell.
    cbn -[η r].
    rewrite <- !rwhisker_vcomp.
    use vcomp_move_R_Mp ; [ is_iso | ].
    use vcomp_move_R_Mp ; [ is_iso | ].
    use vcomp_move_R_Mp ; [ is_iso | ].
    cbn -[η r].
    rewrite !vassocl.
    rewrite !rwhisker_vcomp.
    rewrite !vassocr.
    refine (!(rwhisker_vcomp _ _ _) @ _).
    use (vcomp_rcancel (rassociator _ _ _)) ; [ is_iso | ].
    rewrite !vassocl.
    rewrite rwhisker_rwhisker_alt.
    use (vcomp_rcancel (rassociator _ _ _)) ; [ is_iso | ].
    cbn.
    rewrite !vassocl.
    assert ((rinvunitor g₂ • (g₂ ◃ η) • lassociator g₂ l r) ▹ l
            • rassociator _ _ _
            • rassociator _ _ _
            =
            g₂ ◃ (rinvunitor _ • (l ◃ ε^-1)))
      as H.
    {
      refine (_ @ id2_left _).
      use vcomp_move_L_Mp ; [ is_iso | ].
      cbn -[η r ε].
      refine (_ @ lwhisker_id2 _ _).
      pose (pr112 Hl : linvunitor l
                       • (η ▹ l)
                       • rassociator l r l
                       • (l ◃ ε)
                       • runitor l
                       =
                       id₂ _).
      cbn -[η ε r] in p.
      rewrite <- p ; clear p.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- rassociator_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- !rwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        apply id2_left.
      }
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_hcomp, lwhisker_hcomp.
      rewrite triangle_r_inv.
      apply idpath.
    }
    rewrite !vassocl in H.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact H.
    }
    clear H.
    assert ((rinvunitor g₁ • (g₁ ◃ η • lassociator g₁ l r)) ▹ l
            • rassociator (g₁ · l) r l
            =
            rinvunitor _ • (_ ◃ ε^-1))
      as H.
    {
      use vcomp_move_L_Mp ; [ is_iso | ].
      refine (_ @ id2_left _).
      use vcomp_move_L_Mp ; [ is_iso | ].
      cbn -[η r ε].
      refine (_ @ lwhisker_id2 _ _).
      pose (pr112 Hl : linvunitor l
                       • (η ▹ l)
                       • rassociator l r l
                       • (l ◃ ε)
                       • runitor _
                       =
                       id₂ _) as p.
      cbn -[η ε r] in p.
      rewrite <- p ; clear p.
      rewrite <- runitor_triangle.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_vcomp.
      rewrite !vassocl.
      rewrite <- rassociator_rassociator.
      rewrite !vassocr.
      etrans.
      {
        do 2 apply maponpaths_2.
        rewrite rwhisker_vcomp.
        rewrite !vassocl.
        rewrite lassociator_rassociator.
        rewrite id2_right.
        apply idpath.
      }
      apply maponpaths_2.
      rewrite <- rwhisker_vcomp.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_hcomp, lwhisker_hcomp.
      rewrite triangle_r_inv.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite !vassocr.
      do 2 apply maponpaths_2.
      rewrite !vassocr in H.
      exact H.
    }
    rewrite !vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- vcomp_whisker.
      apply idpath.
    }
    rewrite !vassocr.
    rewrite rwhisker_hcomp.
    rewrite <- rinvunitor_natural.
    rewrite !vassocl.
    apply maponpaths.
    rewrite <- lwhisker_vcomp.
    rewrite <- lwhisker_lwhisker_rassociator.
    rewrite !vassocr.
    apply maponpaths_2.
    rewrite left_unit_inv_assoc.
    apply idpath.
  Qed.

  Definition adj_equiv_fully_faithful
    : fully_faithful_1cell l.
  Proof.
    use make_fully_faithful.
    - exact (adj_equiv_faithful Hl).
    - intros z g₁ g₂ αf.
      simple refine (_ ,, _).
      + exact (adj_equiv_fully_faithful_inv_cell αf).
      + exact (adj_equiv_fully_faithful_inv_cell_is_inv_cell αf).
  Defined.
End AdjEquivFullyFaithful.

(**
 9. Adjoint equivalences are conservative
 *)
Definition adj_equiv_conservative
           {B : bicat}
           {a b : B}
           {l : a --> b}
           (Hl : left_adjoint_equivalence l)
  : conservative_1cell l.
Proof.
  apply fully_faithful_to_conservative.
  apply adj_equiv_fully_faithful.
  exact Hl.
Defined.

(**
 10. Adjoint equivalences are discrete
 *)
Definition adj_equiv_discrete
           {B : bicat}
           {a b : B}
           {l : a --> b}
           (Hl : left_adjoint_equivalence l)
  : discrete_1cell l.
Proof.
  apply fully_faithful_is_discrete.
  apply adj_equiv_fully_faithful.
  exact Hl.
Defined.

(**
 11. Adjoint equivalences preserve cartesian cells
 *)
Definition equivalence_preserves_cartesian
           {B : bicat}
           {b e₁ e₂ : B}
           (p₁ : e₁ --> b)
           (p₂ : e₂ --> b)
           (L : e₁ --> e₂)
           (com : invertible_2cell p₁ (L · p₂))
           (HL : left_adjoint_equivalence L)
           (HB_2_0 : is_univalent_2_0 B)
           (HB_2_1 : is_univalent_2_1 B)
  : mor_preserves_cartesian p₁ p₂ L.
Proof.
  refine (J_2_0
            HB_2_0
            (λ (x₁ x₂ : B) (L : adjoint_equivalence x₁ x₂),
             ∏ (p₁ : x₁ --> b)
               (p₂ : x₂ --> b)
               (c : invertible_2cell p₁ (L · p₂)),
             mor_preserves_cartesian p₁ p₂ L)
            _
            (L ,, HL)
            p₁
            p₂
            com).
  clear e₁ e₂ L HL p₁ p₂ com HB_2_0.
  cbn ; intros e p₁ p₂ com.
  pose (c := comp_of_invertible_2cell com (lunitor_invertible_2cell _)).
  refine (J_2_1
            HB_2_1
            (λ (x₁ x₂ : B)
               (f g : x₁ --> x₂)
               _,
             mor_preserves_cartesian f g (id₁ _))
            _
            c).
  intros.
  apply id_mor_preserves_cartesian.
Defined.

(**
 12. Adjoint equivalences preserve cartesian cells
 *)
Definition equivalence_preserves_opcartesian
           {B : bicat}
           {b e₁ e₂ : B}
           (p₁ : e₁ --> b)
           (p₂ : e₂ --> b)
           (L : e₁ --> e₂)
           (com : invertible_2cell p₁ (L · p₂))
           (HL : left_adjoint_equivalence L)
           (HB_2_0 : is_univalent_2_0 B)
           (HB_2_1 : is_univalent_2_1 B)
  : mor_preserves_opcartesian p₁ p₂ L.
Proof.
  refine (J_2_0
            HB_2_0
            (λ (x₁ x₂ : B) (L : adjoint_equivalence x₁ x₂),
             ∏ (p₁ : x₁ --> b)
               (p₂ : x₂ --> b)
               (c : invertible_2cell p₁ (L · p₂)),
             mor_preserves_opcartesian p₁ p₂ L)
            _
            (L ,, HL)
            p₁
            p₂
            com).
  clear e₁ e₂ L HL p₁ p₂ com HB_2_0.
  cbn ; intros e p₁ p₂ com.
  pose (c := comp_of_invertible_2cell com (lunitor_invertible_2cell _)).
  refine (J_2_1
            HB_2_1
            (λ (x₁ x₂ : B)
               (f g : x₁ --> x₂)
               _,
             mor_preserves_opcartesian f g (id₁ _))
            _
            c).
  intros.
  apply id_mor_preserves_opcartesian.
Defined.
