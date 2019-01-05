(**
Internal equivalences in bicategories can be refined to adjoint equivalences.

Authors: Dan Frumin, Niels van der Weide

Ported from: https://github.com/nmvdw/groupoids
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Local Open Scope bicategory_scope.

Definition representable_faithful
           {C : bicat}
           {X Y Z : C}
           {f : C⟦X,Y⟧} {g : C⟦Y,X⟧}
           (η : id₁ X ==> g ∘ f)
           (k₁ k₂ : C⟦Z,X⟧)
           (α β : k₁ ==> k₂)
           (Hη : is_invertible_2cell η)
  : f ◅ α = f ◅ β -> α = β.
Proof.
  intros Hαβ.
  rewrite (whisker_l_iso_id₁ η _ _ α Hη).
  rewrite (whisker_l_iso_id₁ η _ _ β Hη).
  rewrite (whisker_l_eq k₁ k₂ α β Hαβ).
  reflexivity.
Qed.

Definition representable_full
           {C : bicat}
           {X Y Z : C}
           {f : C⟦X,Y⟧} {g : C⟦Y,X⟧}
           (η : id₁ X ==> g ∘ f)
           (θ : f ∘ g ==> id₁ Y)
           (Hη : is_invertible_2cell η)
           (k₁ k₂ : C⟦Z,X⟧)
           (α : f ∘ k₁ ==> f ∘ k₂)
  : k₁ ==> k₂.
Proof.
  refine (_ o rinvunitor _).
  refine (_ o η ▻ _).
  refine (_ o lassociator _ _ _).
  refine (_ o g ◅ α).
  refine (_ o rassociator _ _ _).
  refine (_ o Hη^-1 ▻ k₂).
  apply runitor.
Defined.

Definition full_spec
           {C : bicat}
           {X Y Z : C}
           {f : C⟦X,Y⟧} {g : C⟦Y,X⟧}
           (η : id₁ X ==> g ∘ f)
           (θ : f ∘ g ==> id₁ Y)
           (Hη : is_invertible_2cell η)
           (Hθ : is_invertible_2cell θ)
           (k₁ k₂ : C⟦Z,X⟧)
           (α : f ∘ k₁ ==> f ∘ k₂)
  : f ◅ (representable_full η θ Hη k₁ k₂ α) = α.
Proof.
  refine (representable_faithful (Hθ^-1) (f ∘ k₁) (f ∘ k₂) _ α _ _).
  { is_iso. }
  apply (vcomp_lcancel (lassociator _ _ _)).
  { is_iso. }
  rewrite <- whisker_l_hcomp.
  apply (vcomp_rcancel (rassociator _ _ _)).
  { is_iso. }
  rewrite <- !vassocr.
  rewrite lassociator_rassociator, id2_right.
  apply (vcomp_rcancel (Hη^-1 ▻ k₂)).
  { is_iso. }
  apply (vcomp_rcancel (runitor k₂)).
  { is_iso. }
  apply (vcomp_lcancel (η ▻ k₁)).
  { is_iso. }
  apply (vcomp_lcancel (rinvunitor k₁)).
  { is_iso. }
  rewrite <- !vassocr.
  rewrite <- (whisker_l_iso_id₁ η k₁ k₂ (representable_full η θ Hη k₁ k₂ α) Hη).
  reflexivity.
Qed.

Section EquivToAdjEquiv.
  Context {C : bicat}
          {X Y : C}.
  Variable (f : C⟦X,Y⟧)
           (Hf : left_equivalence f).

  Local Definition g : C⟦Y,X⟧ := left_adjoint_right_adjoint Hf.
  Local Definition η : id₁ X ==> g ∘ f := left_adjoint_unit Hf.
  Local Definition θ : f ∘ g ==> id₁ Y := left_adjoint_counit Hf.
  Local Definition ηiso := left_equivalence_unit_iso Hf.
  Local Definition θiso := left_equivalence_counit_iso Hf.

  Local Definition ε : f ∘ g ==> id₁ Y.
  Proof.
    refine (representable_full (θiso^-1) (ηiso^-1) _ (f ∘ g) (id₁ Y) _).
    { is_iso. }
    exact ((linvunitor g)
             o runitor g
             o ηiso^-1 ▻ g
             o rassociator _ _ _).
  Defined.

  Definition εiso : is_invertible_2cell ε.
  Proof.
    unfold ε, representable_full.
    is_iso.
  Defined.

  Definition equiv_to_adjequiv_d : left_adjoint_data f.
  Proof.
    refine (g ,, _).
    split.
    - exact η.
    - exact ε.
  Defined.

  Local Definition first_triangle_law
    : (lunitor g)
        o g ◅ ε
        o lassociator g f g
        o η ▻ g
        o rinvunitor _
      = id₂ g.
  Proof.
    rewrite !vassocr.
    unfold ε.
    rewrite (full_spec (θiso^-1) (ηiso^-1) _ (is_invertible_2cell_inv _) (f ∘ g) (id₁ Y) _).
    rewrite <- !vassocr.
    rewrite linvunitor_lunitor, id2_right.
    rewrite !vassocr.
    rewrite !(maponpaths (fun z => _ o (_ o z)) (!(vassocr _ _ _))).
    rewrite lassociator_rassociator, id2_right.
    rewrite !(maponpaths (fun z => _ o z) (!(vassocr _ _ _))).
    rewrite lwhisker_vcomp.
    rewrite vcomp_rinv.
    rewrite lwhisker_id2.
    rewrite id2_right.
    rewrite rinvunitor_runitor.
    reflexivity.
  Qed.

  Local Definition whisker_ηg_type
    : Type.
  Proof.
    refine (η ▻ g = inv_cell (η := (lunitor g o g ◅ ε o lassociator g f g)) _ o runitor g).
    unfold ε, representable_full.
    is_iso.
  Defined.

  Local Definition whisker_ηg
    : whisker_ηg_type.
  Proof.
    use vcomp_move_L_Mp.
    { cbn.
      is_iso.
      - apply Hf.
      - apply Hf.
    }
    cbn.
    refine (_ @ id2_right _).
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    apply first_triangle_law.
  Qed.

  Local Definition η_natural
    : η ▻ (g ∘ f) o rinvunitor (g ∘ f) o η
      =
      (g ∘ f) ◅ η o linvunitor (g ∘ f) o η.
  Proof.
    rewrite !vassocr.
    rewrite rinvunitor_natural.
    rewrite linvunitor_natural.
    rewrite <- !vassocr.
    rewrite lwhisker_hcomp, rwhisker_hcomp.
    rewrite <- !interchange.
    rewrite !id2_left, !id2_right.
    rewrite lunitor_V_id_is_left_unit_V_id.
    reflexivity.
  Qed.

  Local Definition η_natural_help
    : η ▻ (g ∘ f) o rinvunitor (g ∘ f)
      =
      (g ∘ f) ◅ η o linvunitor (g ∘ f)
    := vcomp_lcancel η ηiso η_natural.

  Local Definition η_whisker_l_hcomp
    : (g ∘ f) ◅ η = rassociator (g ∘ f) f g o g ◅ (f ◅ η) o lassociator (id₁ X) f g.
  Proof.
    rewrite !vassocr.
    use vcomp_move_L_Mp.
    { is_iso. }
    cbn.
    rewrite rwhisker_rwhisker.
    reflexivity.
  Qed.

  Local Definition η_whisker_r_hcomp
    : η ▻ (g ∘ f) = lassociator f g(g ∘ f) o η ▻ g ▻ f o rassociator f g (id₁ X).
  Proof.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite lwhisker_lwhisker.
    reflexivity.
  Qed.

  Local Definition help1
    : lassociator f g (g ∘ f) o (η ▻ g o rinvunitor _) ▻ f
      =
      (rassociator (g ∘ f) f g)
        o g ◅ (f ◅ η)
        o lassociator (id₁ X) f g
        o linvunitor (g ∘ f).
  Proof.
    rewrite <- η_whisker_l_hcomp.
    rewrite <- lwhisker_vcomp.
    rewrite left_unit_inv_assoc.
    rewrite <- !vassocr.
    rewrite lwhisker_lwhisker.
    rewrite !vassocr.
    rewrite !(maponpaths (fun z => _ o z) (!(vassocr _ _ _))).
    rewrite rassociator_lassociator, id2_right.
    exact η_natural_help.
  Qed.

  Local Definition help2
    : g ◅ (lassociator f g f o εiso^-1 ▻ f o rinvunitor _)
      =
      g ◅ (f ◅ η o linvunitor f).
  Proof.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    rewrite lwhisker_hcomp, rwhisker_hcomp.
    rewrite <- triangle_l_inv.
    rewrite !(maponpaths (fun z => _ o z) (!(vassocr _ _ _))).
    unfold assoc.
    rewrite <- !lwhisker_hcomp.
    rewrite <- rwhisker_lwhisker.
    pose help1 as p.
    rewrite whisker_ηg in p.
    cbn in p.
    rewrite !vassocr in p.
    rewrite rinvunitor_runitor, id2_left in p.
    rewrite <- !lwhisker_vcomp in p.
    rewrite linvunitor_assoc in p.
    rewrite <- !vassocr in p.
    rewrite !vassocr in p.
    rewrite !(maponpaths (fun z => _ o (_ o z)) (!(vassocr _ _ _))) in p.
    rewrite rassociator_lassociator, id2_right in p.
    rewrite <- bc_whisker_l_compose in p.
    rewrite <- !vassocr in p.
    pose @inverse_pentagon_5 as q.
    rewrite !lwhisker_hcomp in p.
    rewrite q in p ; clear q.
    rewrite !vassocr in p.
    use vcomp_rcancel. 2: exact (rassociator (f · g) f g).
    { is_iso. }
    rewrite rwhisker_vcomp.
    refine (_ @ p) ; clear p.
    cbn.
    rewrite !vassocr, !lwhisker_hcomp, !rwhisker_hcomp.
    reflexivity.
  Qed.

  Local Definition help3
    : lassociator f g f o εiso^-1 ▻ f o rinvunitor f
      =
      f ◅ η o linvunitor f.
  Proof.
    use (representable_faithful _ _ _ _ _ _ help2).
    - exact f.
    - exact (εiso^-1).
    - is_iso.
  Qed.

  Definition equiv_to_adjequiv_isadj : left_adjoint_axioms equiv_to_adjequiv_d.
  Proof.
    split ; cbn.
    - refine (maponpaths (fun z => ((z • _) • _) • _) (!help3) @ _).
      rewrite !vassocr.
      rewrite !(maponpaths (fun z => _ o (_ o z)) (!(vassocr _ _ _))).
      rewrite lassociator_rassociator, id2_right.
      rewrite !(maponpaths (fun z => _ o z) (!(vassocr _ _ _))).
      rewrite lwhisker_vcomp.
      rewrite vcomp_lid.
      rewrite lwhisker_id2.
      rewrite id2_right.
      rewrite rinvunitor_runitor.
      reflexivity.
    - rewrite <- !vassocr.
      exact first_triangle_law.
  Defined.

  Definition equiv_to_isadjequiv : left_adjoint_equivalence f.
  Proof.
    use tpair.
    - exact equiv_to_adjequiv_d.
    - cbn.
      split.
      + exact equiv_to_adjequiv_isadj.
      + split.
        * exact ηiso.
        * exact εiso.
  Defined.

  Definition equiv_to_adjequiv : adjoint_equivalence X Y
    := (f ,, equiv_to_isadjequiv).
End EquivToAdjEquiv.

Section CompositionEquivalence.
  Context {C : bicat}
          {X Y Z : C}.
  Variable (f : C⟦X,Y⟧)
           (g : C⟦Y,Z⟧)
           (A₁ : left_equivalence f)
           (A₂ : left_equivalence g).

  Local Notation finv := (left_adjoint_right_adjoint A₁).
  Local Notation ginv := (left_adjoint_right_adjoint A₂).

  Local Definition comp_unit
    : id₁ X ==> (finv ∘ ginv) ∘ (g ∘ f).
  Proof.
    refine (rassociator (g ∘ f) _ _ o _).
    refine ((_ ◅ _) o (left_adjoint_unit A₁)).
    refine (lassociator f g _ o _).
    exact (((left_adjoint_unit A₂) ▻ f) o rinvunitor f).
  Defined.

  Local Definition comp_unit_isiso
    : is_invertible_2cell comp_unit.
  Proof.
    unfold comp_unit.
    is_iso.
    - exact (left_equivalence_unit_iso A₁).
    - exact (left_equivalence_unit_iso A₂).
  Defined.

  Local Definition comp_counit
    : (g ∘ f) ∘ (finv ∘ ginv) ==> (id₁ Z).
  Proof.
    refine (_ o lassociator _ f g).
    refine (left_adjoint_counit A₂ o (g ◅ _)).
    refine (_ o rassociator _ _ _).
    refine (runitor _ o _).
    exact (left_adjoint_counit A₁ ▻ _).
  Defined.

  Local Definition comp_counit_isiso
    : is_invertible_2cell comp_counit.
  Proof.
    unfold comp_counit.
    is_iso.
    - exact (left_equivalence_counit_iso A₁).
    - exact (left_equivalence_counit_iso A₂).
  Defined.

  Definition comp_equiv
    : left_equivalence (f · g).
  Proof.
    use tpair.
    - repeat (use tpair).
      * exact (finv ∘ ginv).
      * exact comp_unit.
      * exact comp_counit.
    - split.
      * exact comp_unit_isiso.
      * exact comp_counit_isiso.
  Defined.
End CompositionEquivalence.

Definition comp_adjequiv
           {C : bicat}
           {X Y Z : C}
           (f : adjoint_equivalence X Y)
           (g : adjoint_equivalence Y Z)
  : adjoint_equivalence X Z.
Proof.
  use (equiv_to_adjequiv (f · g)).
  use comp_equiv.
  - exact f.
  - exact g.
Defined.
