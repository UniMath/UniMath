(**
 Faithful and fully faithful 1-cells in bicategories

 In this file, we define
 - Faithful 1-cells
 - Fully faithful 1-cells
 - Identities, composition, and adjoint equivalences are (fully) faithful
 - We characterize these notions in 1-types and categories
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.Bicategories.Core.Bicat. Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Local Open Scope cat.

(**
Faithful 1-cells

Faithful 1-cells are those 1-cells for which postcomposition is a faithful functor.
More concretely, whiskering by this 1-cell is injective.
 *)
Definition faithful_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : UU
  := ∏ (z : B)
       (g₁ g₂ : z --> a)
       (α₁ α₂ : g₁ ==> g₂),
     α₁ ▹ f = α₂ ▹ f
     →
     α₁ = α₂.

Definition faithful_1cell_eq_cell
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : faithful_1cell f)
           {z : B}
           {g₁ g₂ : z --> a}
           {α₁ α₂ : g₁ ==> g₂}
           (p : α₁ ▹ f = α₂ ▹ f)
  : α₁ = α₂
  := Hf _ _ _ _ _ p.

Definition isaprop_faithful_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : isaprop (faithful_1cell f).
Proof.
  repeat (use impred ; intro).
  apply cellset_property.
Qed.

Definition faithful_1cell_to_faithful
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : faithful_1cell f → ∏ (z : B), faithful (post_comp z f).
Proof.
  intros Hf z g₁ g₂ α ; cbn in *.
  use invproofirrelevance.
  intros φ₁ φ₂ ; cbn in *.
  use subtypePath.
  {
    intro ; apply cellset_property.
  }
  apply (faithful_1cell_eq_cell Hf).
  exact (pr2 φ₁ @ !(pr2 φ₂)).
Qed.

Definition faithful_to_faithful_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : (∏ (z : B), faithful (post_comp z f)) → faithful_1cell f.
Proof.
  intros Hf z g₁ g₂ α₁ α₂ p.
  pose (proofirrelevance _ (Hf z g₁ g₂ (α₂ ▹ f)) (α₁ ,, p) (α₂ ,, idpath _)) as q.
  exact (maponpaths pr1 q).
Qed.

Definition faithful_1cell_weq_faithful
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : (faithful_1cell f) ≃ (∏ (z : B), faithful (post_comp z f)).
Proof.
  use weqimplimpl.
  - exact (faithful_1cell_to_faithful f).
  - exact (faithful_to_faithful_1cell f).
  - exact (isaprop_faithful_1cell f).
  - use impred ; intro.
    apply isaprop_faithful.
Defined.

(** Examples of faithful 1-cells *)
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

Definition comp_faithful
           {B : bicat}
           {a b c : B}
           {f : a --> b}
           {g : b --> c}
           (Hf : faithful_1cell f)
           (Hg : faithful_1cell g)
  : faithful_1cell (f · g).
Proof.
  intros z g₁ g₂ α₁ α₂ p.
  apply (faithful_1cell_eq_cell Hf).
  apply (faithful_1cell_eq_cell Hg).
  use (vcomp_rcancel (rassociator _ _ _)).
  {
    is_iso.
  }
  rewrite !rwhisker_rwhisker_alt.
  rewrite p.
  apply idpath.
Qed.

Definition faithful_invertible
           {B : bicat}
           {a b : B}
           {f₁ f₂ : a --> b}
           (β : f₁ ==> f₂)
           (Hβ : is_invertible_2cell β)
  : faithful_1cell f₁ → faithful_1cell f₂.
Proof.
  intros Hf₁ z g₁ g₂ α₁ α₂ p.
  apply (faithful_1cell_eq_cell Hf₁).
  use (vcomp_rcancel (_ ◃ β)).
  {
    is_iso.
  }
  rewrite !vcomp_whisker.
  rewrite p.
  apply idpath.
Qed.

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

(** Faithful 1-cells in standard bicategories *)

(** Faithful 1-cells in 1-types are functions for which `maponpaths` is an inclusion *)
Definition one_types_is_incl_faithful_1cell
           {X Y : one_types}
           (f : X --> Y)
           (Hf : ∏ (x y : (X : one_type)), isincl (@maponpaths _ _ f x y))
  : faithful_1cell f.
Proof.
  intros z g₁ g₂ α₁ α₂ p.
  use funextsec.
  intro x.
  cbn in * ; unfold homotfun in *.
  pose (Hf (g₁ x) (g₂ x) (maponpaths f (α₂ x))) as i.
  pose (proofirrelevance _ i (α₁ x ,, eqtohomot p x) (α₂ x ,, idpath _)) as k.
  exact (maponpaths pr1 k).
Qed.

Definition one_types_faithful_1cell_is_incl
           {X Y : one_types}
           (f : X --> Y)
           (Hf : faithful_1cell f)
  : ∏ (x y : (X : one_type)), isincl (@maponpaths _ _ f x y).
Proof.
  intros x y ; cbn in *.
  use isinclweqonpaths.
  intros p q.
  use isweqimplimpl.
  - intros α.
    pose (eqtohomot
            (Hf X (λ _, x) (λ _, y)
                (λ _, p) (λ _, q)
                (funextsec _ _ _ (λ _, α)))
            x)
      as fp.
    exact fp.
  - use invproofirrelevance.
    intros ? ?.
    apply X.
  - use invproofirrelevance.
    intros ? ?.
    apply Y.
Qed.

Definition one_types_is_incl_weq_faithful_1cell
           {X Y : one_types}
           (f : X --> Y)
  : (∏ (x y : (X : one_type)), isincl (@maponpaths _ _ f x y))
    ≃
    faithful_1cell f.
Proof.
  use weqimplimpl.
  - exact (one_types_is_incl_faithful_1cell f).
  - exact (one_types_faithful_1cell_is_incl f).
  - do 2 (use impred ; intro).
    apply isapropisincl.
  - apply isaprop_faithful_1cell.
Qed.

(** Faithful 1-cells in the bicategory of categories are faithful functors *)
Definition cat_faithful_is_faithful_1cell
           {C₁ C₂ : bicat_of_cats}
           (F : C₁ --> C₂)
           (HF : faithful F)
  : faithful_1cell F.
Proof.
  intros C₃ G₁ G₂ α₁ α₂ p.
  cbn in *.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intro x.
  use (invmaponpathsincl _ (HF (G₁ x) (G₂ x))).
  exact (nat_trans_eq_pointwise p x).
Qed.

Definition cat_faithful_1cell_is_faithful
           {C₁ C₂ : bicat_of_cats}
           (F : C₁ --> C₂)
           (HF : faithful_1cell F)
  : faithful F.
Proof.
  intros x y ; cbn in *.
  use isinclweqonpaths.
  intros f g.
  use isweqimplimpl.
  - intro p.
    assert (post_whisker (constant_nat_trans C₁ f) F
            =
            post_whisker (constant_nat_trans C₁ g) F)
      as X.
    {
      use nat_trans_eq ; [ apply homset_property | ].
      intro.
      exact p.
    }
    use (nat_trans_eq_pointwise (faithful_1cell_eq_cell HF X) x).
  - apply homset_property.
  - apply homset_property.
Qed.

Definition cat_faithful_weq_faithful_1cell
           {C₁ C₂ : bicat_of_cats}
           (F : C₁ --> C₂)
  : faithful F ≃ faithful_1cell F.
Proof.
  use weqimplimpl.
  - exact (cat_faithful_is_faithful_1cell F).
  - exact (cat_faithful_1cell_is_faithful F).
  - apply isaprop_faithful.
  - apply isaprop_faithful_1cell.
Qed.

(**
 Fully faithful 1-cells

 Fully faithful 1-cells satisfiy two properties:
 - Whiskering with that 1-cell is injective
 - Precomposition with that 1-cell is 'injective' up to a 2-cell
 *)
Definition fully_faithful_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : UU
  := (∏ (z : B)
        (g₁ g₂ : z --> a)
        (α₁ α₂ : g₁ ==> g₂),
      α₁ ▹ f = α₂ ▹ f
      →
      α₁ = α₂)
     ×
     (∏ (z : B)
        (g₁ g₂ : z --> a)
        (αf : g₁ · f ==> g₂ · f),
      ∑ (α : g₁ ==> g₂), α ▹ f = αf).

Definition fully_faithful_1cell_faithful
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : fully_faithful_1cell f)
  : faithful_1cell f
  := pr1 Hf.

Definition fully_faithful_1cell_eq
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : fully_faithful_1cell f)
           {z : B}
           {g₁ g₂ : z --> a}
           {α₁ α₂ : g₁ ==> g₂}
           (p : α₁ ▹ f = α₂ ▹ f)
  : α₁ = α₂
  := pr1 Hf _ _ _ _ _ p.

Definition fully_faithful_1cell_inv_map
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : fully_faithful_1cell f)
           {z : B}
           {g₁ g₂ : z --> a}
           (αf : g₁ · f ==> g₂ · f)
  : g₁ ==> g₂
  := pr1 (pr2 Hf _ _ _ αf).

Definition fully_faithful_1cell_inv_map_eq
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf : fully_faithful_1cell f)
           {z : B}
           {g₁ g₂ : z --> a}
           (αf : g₁ · f ==> g₂ · f)
  : fully_faithful_1cell_inv_map Hf αf ▹ f = αf
  := pr2 (pr2 Hf _ _ _ αf).

Definition make_fully_faithful
           {B : bicat}
           {a b : B}
           {f : a --> b}
           (Hf₁ : faithful_1cell f)
           (Hf₂ : ∏ (z : B)
                    (g₁ g₂ : z --> a)
                    (αf : g₁ · f ==> g₂ · f),
                  ∑ (α : g₁ ==> g₂), α ▹ f = αf)
  : fully_faithful_1cell f
  := (Hf₁ ,, Hf₂).

Definition isaprop_fully_faithful_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : isaprop (fully_faithful_1cell f).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use pathsdirprod.
  - apply isaprop_faithful_1cell.
  - use funextsec ; intro z.
    use funextsec ; intro g₁.
    use funextsec ; intro g₂.
    use funextsec ; intro αf.
    use subtypePath.
    {
      intro ; apply cellset_property.
    }
    pose (ψ₁ := pr2 φ₁ z g₁ g₂ αf).
    pose (ψ₂ := pr2 φ₂ z g₁ g₂ αf).
    enough (pr1 ψ₁ = pr1 ψ₂) as X.
    {
      exact X.
    }
    use (fully_faithful_1cell_eq φ₁).
    exact (pr2 ψ₁ @ !(pr2 ψ₂)).
Qed.

Definition fully_faithful_1cell_to_fully_faithful
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : fully_faithful_1cell f → ∏ (z : B), fully_faithful (post_comp z f).
Proof.
  intros Hf z g₁ g₂ α ; cbn in *.
  use iscontraprop1.
  - use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath ; [ intro ; apply cellset_property | ].
    cbn in *.
    apply (pr1 Hf).
    exact (pr2 φ₁ @ !(pr2 φ₂)).
  - exact (pr2 Hf z _ _ α).
Qed.

Definition fully_faithful_to_fully_faithful_1cell
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : (∏ (z : B), fully_faithful (post_comp z f)) → fully_faithful_1cell f.
Proof.
  intros Hf.
  use make_fully_faithful.
  - use faithful_to_faithful_1cell.
    intro z.
    apply fully_faithful_implies_full_and_faithful.
    apply Hf.
  - intros z g₁ g₂ αf.
    simple refine (_ ,, _).
    + exact (invmap (make_weq _ (Hf z g₁ g₂)) αf).
    + apply (homotweqinvweq (make_weq _ (Hf z g₁ g₂))).
Qed.

Definition fully_faithful_1cell_weq_fully_faithful
           {B : bicat}
           {a b : B}
           (f : a --> b)
  : (fully_faithful_1cell f)
    ≃
    (∏ (z : B), fully_faithful (post_comp z f)).
Proof.
  use weqimplimpl.
  - exact (fully_faithful_1cell_to_fully_faithful f).
  - exact (fully_faithful_to_fully_faithful_1cell f).
  - exact (isaprop_fully_faithful_1cell f).
  - use impred ; intro.
    apply isaprop_fully_faithful.
Defined.

(** Examples of fully faithful 1-cells *)
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

Definition comp_fully_faithful
           {B : bicat}
           {a b c : B}
           {f : a --> b}
           {g : b --> c}
           (Hf : fully_faithful_1cell f)
           (Hg : fully_faithful_1cell g)
  : fully_faithful_1cell (f · g).
Proof.
  use make_fully_faithful.
  - exact (comp_faithful
             (fully_faithful_1cell_faithful Hf)
             (fully_faithful_1cell_faithful Hg)).
  - intros z g₁ g₂ αf.
    simple refine (_ ,, _).
    + apply (fully_faithful_1cell_inv_map Hf).
      apply (fully_faithful_1cell_inv_map Hg).
      exact (rassociator _ _ _ • αf • lassociator _ _ _).
    + abstract
        (cbn ;
         use (vcomp_rcancel (lassociator _ _ _)) ; [ is_iso | ] ;
         rewrite !vassocl ;
         rewrite <- rwhisker_rwhisker ;
         rewrite !fully_faithful_1cell_inv_map_eq ;
         rewrite !vassocr ;
         rewrite lassociator_rassociator ;
         rewrite id2_left ;
         apply idpath).
Defined.

Definition fully_faithful_invertible
           {B : bicat}
           {a b : B}
           {f₁ f₂ : a --> b}
           (β : f₁ ==> f₂)
           (Hβ : is_invertible_2cell β)
           (Hf₁ : fully_faithful_1cell f₁)
  : fully_faithful_1cell f₂.
Proof.
  use make_fully_faithful.
  - exact (faithful_invertible β Hβ (fully_faithful_1cell_faithful Hf₁)).
  - intros z g₁ g₂ αf.
    simple refine (_ ,, _).
    + apply (fully_faithful_1cell_inv_map Hf₁).
      exact ((g₁ ◃ β) • αf • (g₂ ◃ Hβ^-1)).
    + abstract
        (cbn ;
         use (vcomp_rcancel (_ ◃ Hβ^-1)) ; [ is_iso | ] ;
         rewrite vcomp_whisker ;
         rewrite fully_faithful_1cell_inv_map_eq ;
         rewrite !vassocr ;
         rewrite lwhisker_vcomp ;
         rewrite vcomp_linv ;
         rewrite lwhisker_id2 ;
         rewrite id2_left ;
         apply idpath).
Qed.

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

(** Fully faithful 1-cells in standard bicategories *)

(** Fully faithful 1-cells in 1-types are injective maps *)
Definition one_types_isInjective_fully_faithful_1cell
           {X Y : one_types}
           (f : X --> Y)
           (Hf : isInjective f)
  : fully_faithful_1cell f.
Proof.
  use make_fully_faithful.
  - apply one_types_is_incl_faithful_1cell.
    intros x y.
    apply isinclweq.
    apply Hf.
  - intros Z g₁ g₂ αf ; cbn in * ; unfold homotfun in *.
    simple refine (_ ,, _).
    + intro x.
      apply (invmap (make_weq _ (Hf (g₁ x) (g₂ x)))).
      exact (αf x).
    + use funextsec.
      intro x.
      apply (homotweqinvweq (make_weq _ (Hf (g₁ x) (g₂ x)))).
Qed.

Definition one_types_fully_faithful_isInjective
           {X Y : one_types}
           (f : X --> Y)
           (Hf : fully_faithful_1cell f)
  : isInjective f.
Proof.
  intros x y ; cbn in *.
  use gradth.
  - intro p.
    exact (pr1 (pr2 Hf X (λ _, x) (λ _, y) (λ _, p)) x).
  - intro p ; simpl.
    pose (pr1 Hf
               _ _ _
               (pr1 (pr2 Hf X (λ _ : X, x) (λ _ : X, y) (λ _ : X, maponpaths f p)))
               (λ _, p))
      as q.
    cbn in q.
    refine (eqtohomot (q _) x).
    unfold homotfun.
    use funextsec.
    intro ; cbn.
    exact (eqtohomot (pr2 (pr2 Hf X (λ _, x) (λ _, y) (λ _, maponpaths f p))) _).
  - intros p.
    exact (eqtohomot (pr2 (pr2 Hf X (λ _, x) (λ _, y) (λ _, p))) x).
Qed.

Definition one_types_isInjective_weq_fully_faithful
           {X Y : one_types}
           (f : X --> Y)
  : isInjective f ≃ fully_faithful_1cell f.
Proof.
  use weqimplimpl.
  - exact (one_types_isInjective_fully_faithful_1cell f).
  - exact (one_types_fully_faithful_isInjective f).
  - apply isaprop_isInjective.
  - apply isaprop_fully_faithful_1cell.
Qed.

(** Fully faithful 1-cells in the bicategory of categories are fully faithful functors *)
Definition fully_faithful_inv_nat_trans_data
           {C₁ C₂ C₃ : category}
           {F : C₂ ⟶ C₃}
           (HF : fully_faithful F)
           {G₁ G₂ : C₁ ⟶ C₂}
           (α : G₁ ∙ F ⟹ G₂ ∙ F)
  : nat_trans_data G₁ G₂
  := λ x, invmap (make_weq _ (HF (G₁ x) (G₂ x))) (α x).

Definition fully_faithful_inv_is_nat_trans
           {C₁ C₂ C₃ : category}
           {F : C₂ ⟶ C₃}
           (HF : fully_faithful F)
           {G₁ G₂ : C₁ ⟶ C₂}
           (α : G₁ ∙ F ⟹ G₂ ∙ F)
  : is_nat_trans _ _ (fully_faithful_inv_nat_trans_data HF α).
Proof.
  intros x y f ; cbn ; unfold fully_faithful_inv_nat_trans_data.
  unfold fully_faithful in HF.
  pose (w := make_weq _ (HF (G₁ x) (G₂ y))).
  refine (!(homotinvweqweq w _) @ _ @ homotinvweqweq w _).
  apply maponpaths.
  cbn.
  rewrite !functor_comp.
  etrans.
  {
    apply maponpaths.
    apply (homotweqinvweq (make_weq _ (HF (G₁ _) (G₂ _)))).
  }
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply (homotweqinvweq (make_weq _ (HF (G₁ _) (G₂ _)))).
  }
  refine (!_).
  exact (nat_trans_ax α _ _ f).
Qed.

Definition fully_faithful_inv_nat_trans
           {C₁ C₂ C₃ : category}
           {F : C₂ ⟶ C₃}
           (HF : fully_faithful F)
           {G₁ G₂ : C₁ ⟶ C₂}
           (α : G₁ ∙ F ⟹ G₂ ∙ F)
  : G₁ ⟹ G₂.
Proof.
  use make_nat_trans.
  - exact (fully_faithful_inv_nat_trans_data HF α).
  - exact (fully_faithful_inv_is_nat_trans HF α).
Defined.

Definition cat_fully_faithful_is_fully_faithful_1cell
           {C₁ C₂ : bicat_of_cats}
           (F : C₁ --> C₂)
           (HF : fully_faithful F)
  : fully_faithful_1cell F.
Proof.
  use make_fully_faithful.
  - apply cat_faithful_is_faithful_1cell.
    apply fully_faithful_implies_full_and_faithful.
    exact HF.
  - intros C₃ G₁ G₂ αF ; cbn in *.
    simple refine (_ ,, _).
    + exact (fully_faithful_inv_nat_trans HF αF).
    + use nat_trans_eq ; [ apply homset_property | ].
      intro x.
      cbn ; unfold fully_faithful_inv_nat_trans_data.
      apply (homotweqinvweq (make_weq # F (HF (G₁ x) (G₂ x)))).
Qed.

Definition cat_fully_faithful_1cell_is_fully_faithful
           {C₁ C₂ : bicat_of_cats}
           (F : C₁ --> C₂)
           (HF : fully_faithful_1cell F)
  : fully_faithful F.
Proof.
  use full_and_faithful_implies_fully_faithful.
  cbn in *.
  split.
  - intros x y f.
    apply hinhpr.

    assert (is_nat_trans
              (constant_functor C₁ C₁ x ∙ F)
              (constant_functor C₁ C₁ y ∙ F)
              (λ _, f))
      as n_is_nat_trans.
    {
      intro ; intros.
      cbn.
      rewrite !functor_id.
      rewrite id_left, id_right.
      apply idpath.
    }
    pose (make_nat_trans
            (constant_functor C₁ C₁ x ∙ F)
            (constant_functor C₁ C₁ y ∙ F)
            (λ _, f)
            n_is_nat_trans)
      as n.

    pose (pr2 HF C₁ (constant_functor _ _ x) (constant_functor _ _ y) n) as inv.
    cbn in inv.
    simple refine (_ ,, _) ; cbn.
    + exact (pr1 inv x).
    + exact (nat_trans_eq_pointwise (pr2 inv) x).
  - apply cat_faithful_1cell_is_faithful.
    apply fully_faithful_1cell_faithful.
    exact HF.
Qed.

Definition cat_fully_faithful_weq_fully_faithful_1cell
           {C₁ C₂ : bicat_of_cats}
           (F : C₁ --> C₂)
  : fully_faithful F ≃ fully_faithful_1cell F.
Proof.
  use weqimplimpl.
  - exact (cat_fully_faithful_is_fully_faithful_1cell F).
  - exact (cat_fully_faithful_1cell_is_fully_faithful F).
  - apply isaprop_fully_faithful.
  - apply isaprop_fully_faithful_1cell.
Qed.
