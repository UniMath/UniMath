(* ----------------------------------------------------------------------------------- *)
(** ** Trivial display.

   Every bicategory is, in a trivial way, a displayed bicategory over any other
   bicategory.                                                                         *)
(* ----------------------------------------------------------------------------------- *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.Initial.
Require Import UniMath.Bicategories.Core.Examples.Final.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.AdjointUnique.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(* ----------------------------------------------------------------------------------- *)
(* Handy lemma about transport over a constant fibration.
   NB: This is similar to [transportf_const], but eta-expanded.                        *)
(* ----------------------------------------------------------------------------------- *)

Definition transportf_trivial (A B : UU) (a b : A) (p : a = b) (x : B) :
  x = transportf (λ x : A, B) p x.
Proof.
  induction p. apply idpath.
Defined.

Section Trivial_Displayed.
  (* ----------------------------------------------------------------------------------- *)
  (** [B] is the the base bicategory and [C] is the bicategory that we trivially
    display over [B].                                                                  *)
  (* ----------------------------------------------------------------------------------- *)
  Variable (B C : bicat).

  Definition trivial_disp_cat_ob_mor : disp_cat_ob_mor B
    := make_disp_cat_ob_mor
         B
         (λ _ : B, C)
         (λ (_ _ : B) (a b : C) _, C⟦a,b⟧).

  Definition trivial_disp_cat_id_comp
    : disp_cat_id_comp B trivial_disp_cat_ob_mor
    := (λ (_ : B) (a : C), identity a),,
                                      (λ (_ _ _ : B) _ _ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧), f · g).

  Definition trivial_disp_cat_data : disp_cat_data B
    := trivial_disp_cat_ob_mor,, trivial_disp_cat_id_comp.

  Definition trivial_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells B
    := tpair (λ C:disp_cat_data B, disp_2cell_struct C)
             trivial_disp_cat_data
             (λ _ _ _ _ _ a b f g, f ==> g).

  Definition trivial_displayed_data : disp_prebicat_data B.
    use (trivial_disp_prebicat_1_id_comp_cells,, _).
    repeat apply make_dirprod; cbn.
    - intros _ _ _. exact (λ a b f, id2 f).
    - intros _ _ _. exact (λ a b f, lunitor f).
    - intros _ _ _. exact (λ a b f, runitor f).
    - intros _ _ _. exact (λ a b f, linvunitor f).
    - intros _ _ _. exact (λ a b f, rinvunitor f).
    - intros _ _ _ _ _ _ _. exact (λ a b c d f g h, rassociator f g h).
    - intros _ _ _ _ _ _ _. exact (λ a b c d f g h, lassociator f g h).
    - intros _ _ _ _ _ _ _. exact (λ a b f g h x y, vcomp2 x y).
    - intros _ _ _ _ _ _ _. exact (λ a b c f g1 g2 x, lwhisker f x).
    - intros _ _ _ _ _ _ _. exact (λ a b c f1 f2 g x, rwhisker g x).
  Defined.

  Lemma trivial_disp_prebicat_laws : disp_prebicat_laws trivial_displayed_data.
  Proof.
    repeat apply make_dirprod; red; cbn; intros.
    - etrans. apply id2_left. apply transportf_trivial.
    - etrans. apply id2_right. apply transportf_trivial.
    - etrans. apply vassocr. apply transportf_trivial.
    - etrans. apply lwhisker_id2. apply transportf_trivial.
    - etrans. apply id2_rwhisker. apply transportf_trivial.
    - etrans. apply lwhisker_vcomp. apply transportf_trivial.
    - etrans. apply rwhisker_vcomp. apply transportf_trivial.
    - etrans. apply vcomp_lunitor. apply transportf_trivial.
    - etrans. apply vcomp_runitor. apply transportf_trivial.
    - etrans. apply lwhisker_lwhisker. apply transportf_trivial.
    - etrans. apply rwhisker_lwhisker. apply transportf_trivial.
    - etrans. apply rwhisker_rwhisker. apply transportf_trivial.
    - etrans. apply vcomp_whisker. apply transportf_trivial.
    - etrans. apply lunitor_linvunitor. apply transportf_trivial.
    - etrans. apply linvunitor_lunitor. apply transportf_trivial.
    - etrans. apply runitor_rinvunitor. apply transportf_trivial.
    - etrans. apply rinvunitor_runitor. apply transportf_trivial.
    - etrans. apply lassociator_rassociator. apply transportf_trivial.
    - etrans. apply rassociator_lassociator. apply transportf_trivial.
    - etrans. apply runitor_rwhisker. apply transportf_trivial.
    - etrans. apply lassociator_lassociator. apply transportf_trivial.
  Qed.

  Definition trivial_displayed_prebicat : disp_prebicat B
    := trivial_displayed_data,, trivial_disp_prebicat_laws.

  Definition trivial_displayed_bicat : disp_bicat B.
  Proof.
    refine (trivial_displayed_prebicat ,, _).
    repeat intro; apply C.
  Defined.
End Trivial_Displayed.

Definition prod_bicat
           (B C : bicat)
  : bicat
  := total_bicat (trivial_displayed_bicat B C).

Definition pairobj
           {B C : bicat}
           (X : B) (Y : C)
  : prod_bicat B C
  := X ,, Y.

Definition pairmor
           {B C : bicat}
           {X₁ X₂ : B} {Y₁ Y₂ : C}
           (f : X₁ --> X₂) (g : Y₁ --> Y₂)
  : pairobj X₁ Y₁ --> pairobj X₂ Y₂
  := f ,, g.

Definition paircell
           {B C : bicat}
           {X₁ X₂ : B} {Y₁ Y₂ : C}
           {f₁ f₂ : X₁ --> X₂} {g₁ g₂ : Y₁ --> Y₂}
           (α : f₁ ==> f₂) (β : g₁ ==> g₂)
  : pairmor f₁ g₁ ==> pairmor f₂ g₂
  := α ,, β.

Definition trivial_is_invertible_2cell_to_is_disp_invertible
           {B C : bicat}
           {b₁ b₂ : B}
           {f g : B ⟦ b₁, b₂ ⟧}
           {α : f ==> g}
           (Hα : is_invertible_2cell α)
           {c₁ : trivial_displayed_bicat B C b₁}
           {c₂ : trivial_displayed_bicat B C b₂}
           {ff : c₁ -->[ f ] c₂}
           {gg : c₁ -->[ g ] c₂}
           (β : ff ==> gg)
           (Hβ : is_invertible_2cell β)
  : is_disp_invertible_2cell Hα β.
Proof.
  simple refine (_ ,, (_ ,, _)).
  - exact (Hβ^-1).
  - abstract
      (unfold transportb ; cbn ;
       rewrite transportf_const ;
       apply vcomp_rinv).
  - abstract
      (unfold transportb ; cbn ;
       rewrite transportf_const ;
       apply vcomp_linv).
Defined.

Definition trivial_invertible_2cell_to_disp_invertible
           {B C : bicat}
           {b₁ b₂ : B}
           {f : B ⟦ b₁, b₂ ⟧}
           {c₁ : trivial_displayed_bicat B C b₁}
           {c₂ : trivial_displayed_bicat B C b₂}
           {ff gg : c₁ -->[ f] c₂}
  : invertible_2cell ff gg → disp_invertible_2cell (id2_invertible_2cell f) ff gg.
Proof.
  intros α.
  simple refine (_ ,, _).
  - exact (pr1 α).
  - apply trivial_is_invertible_2cell_to_is_disp_invertible.
    exact (pr2 α).
Defined.

Definition trivial_is_disp_invertible_to_is_invertible_2cell
           {B C : bicat}
           {b₁ b₂ : B}
           {f g : B ⟦ b₁, b₂ ⟧}
           {α : f ==> g}
           (Hα : is_invertible_2cell α)
           {c₁ : trivial_displayed_bicat B C b₁}
           {c₂ : trivial_displayed_bicat B C b₂}
           {ff gg : c₁ -->[ f] c₂}
           (β : ff ==> gg)
           (Hβ : is_disp_invertible_2cell Hα β)
  : is_invertible_2cell β.
Proof.
  use make_is_invertible_2cell.
  - exact (pr1 Hβ).
  - abstract
      (pose (pr12 Hβ) as p ;
       cbn in p ; unfold transportb in p ;
       rewrite transportf_const in p ;
       exact p).
  - abstract
      (pose (pr22 Hβ) as p ;
       cbn in p ; unfold transportb in p ;
       rewrite transportf_const in p ;
       exact p).
Defined.

Definition trivial_disp_invertible_to_invertible_2cell
           {B C : bicat}
           {b₁ b₂ : B}
           {f : B ⟦ b₁, b₂ ⟧}
           {c₁ : trivial_displayed_bicat B C b₁}
           {c₂ : trivial_displayed_bicat B C b₂}
           {ff gg : c₁ -->[ f] c₂}
  : disp_invertible_2cell (id2_invertible_2cell f) ff gg → invertible_2cell ff gg.
Proof.
  intros α.
  use make_invertible_2cell.
  - exact (pr1 α).
  - use (trivial_is_disp_invertible_to_is_invertible_2cell
           (is_invertible_2cell_id₂ f)).
    apply α.
Defined.

Definition trivial_invertible_to_disp_invertible_to_invertible
           {B C : bicat}
           {b₁ b₂ : B}
           {f : B ⟦ b₁, b₂ ⟧}
           {c₁ : trivial_displayed_bicat B C b₁}
           {c₂ : trivial_displayed_bicat B C b₂}
           {ff gg : c₁ -->[ f] c₂}
           (α : invertible_2cell ff gg)
  :  trivial_disp_invertible_to_invertible_2cell
       (trivial_invertible_2cell_to_disp_invertible α)
     =
     α.
Proof.
  use subtypePath.
  {
    intro ; apply isaprop_is_invertible_2cell.
  }
  apply idpath.
Qed.

Definition trivial_disp_invertible_to_invertible_to_disp_invertible
           {B C : bicat}
           {b₁ b₂ : B}
           {f : B ⟦ b₁, b₂ ⟧}
           {c₁ : trivial_displayed_bicat B C b₁}
           {c₂ : trivial_displayed_bicat B C b₂}
           {ff gg : c₁ -->[ f] c₂}
           (α : disp_invertible_2cell (id2_invertible_2cell f) ff gg)
  : trivial_invertible_2cell_to_disp_invertible
      (trivial_disp_invertible_to_invertible_2cell α)
    =
    α.
Proof.
  use subtypePath.
  {
    intro ; apply isaprop_is_disp_invertible_2cell.
  }
  apply idpath.
Qed.

Definition trivial_invertible_2cell_weq_disp_invertible
           {B C : bicat}
           {b₁ b₂ : B}
           {f : B ⟦ b₁, b₂ ⟧}
           {c₁ : trivial_displayed_bicat B C b₁}
           {c₂ : trivial_displayed_bicat B C b₂}
           (ff gg : c₁ -->[ f] c₂)
  : invertible_2cell ff gg ≃ disp_invertible_2cell (id2_invertible_2cell f) ff gg.
Proof.
  use make_weq.
  - exact trivial_invertible_2cell_to_disp_invertible.
  - use isweq_iso.
    + exact trivial_disp_invertible_to_invertible_2cell.
    + exact trivial_invertible_to_disp_invertible_to_invertible.
    + exact trivial_disp_invertible_to_invertible_to_disp_invertible.
Defined.

Definition trivial_is_univalent_2_1
           {B C : bicat}
           (HC : is_univalent_2_1 C)
  : disp_univalent_2_1 (trivial_displayed_bicat B C).
Proof.
  use fiberwise_local_univalent_is_univalent_2_1.
  intros b₁ b₂ f c₁ c₂ ff gg.
  use weqhomot.
  - exact (trivial_invertible_2cell_weq_disp_invertible ff gg
           ∘ make_weq (idtoiso_2_1 ff gg) (HC _ _ ff gg))%weq.
  - intro p ; cbn in p.
    induction p.
    use subtypePath.
    {
      intro ; apply isaprop_is_disp_invertible_2cell.
    }
    apply idpath.
Defined.

Definition trivial_adj_equiv_to_disp_adj_equiv
           {B C : bicat}
           {b : B}
           {c₁ c₂ : trivial_displayed_bicat B C b}
  : adjoint_equivalence c₁ c₂
    →
    disp_adjoint_equivalence (internal_adjoint_equivalence_identity b) c₁ c₂.
Proof.
  intros e.
  simple refine (_ ,, ((_ ,, (_ ,, _)) ,, ((_ ,, _) ,, (_ ,, _)))).
  - exact (pr1 e).
  - exact (left_adjoint_right_adjoint e).
  - exact (left_adjoint_unit e).
  - exact (left_adjoint_counit e).
  - abstract
      (unfold transportb ;
       cbn ;
       rewrite transportf_const ; cbn ;
       exact (pr1 (pr122 e))).
  - abstract
      (unfold transportb ;
       cbn ;
       rewrite transportf_const ; cbn ;
       exact (pr2 (pr122 e))).
  - abstract
      (apply trivial_is_invertible_2cell_to_is_disp_invertible ;
       apply (pr2 e)).
  - abstract
      (apply trivial_is_invertible_2cell_to_is_disp_invertible ;
       apply (pr2 e)).
Defined.

Definition trivial_disp_adj_equiv_to_adj_equiv
           {B C : bicat}
           {b : B}
           {c₁ c₂ : trivial_displayed_bicat B C b}
  : disp_adjoint_equivalence (internal_adjoint_equivalence_identity b) c₁ c₂
    →
    adjoint_equivalence c₁ c₂.
Proof.
  intros e.
  simple refine (_ ,, ((_ ,, (_ ,, _)) ,, ((_ ,, _) ,, (_ ,, _)))).
  - exact (pr1 e).
  - exact (pr112 e).
  - exact (pr1 (pr212 e)).
  - exact (pr2 (pr212 e)).
  - abstract
      (pose (pr1 (pr122 e)) as p ;
       cbn in p ;
       unfold transportb in p ;
       rewrite transportf_const in p ;
       exact p).
  - abstract
      (pose (pr2 (pr122 e)) as p ;
       cbn in p ;
       unfold transportb in p ;
       rewrite transportf_const in p ;
       exact p).
  - abstract
      (apply (trivial_is_disp_invertible_to_is_invertible_2cell _ _ (pr1 (pr222 e)))).
  - abstract
      (apply (trivial_is_disp_invertible_to_is_invertible_2cell _ _ (pr2 (pr222 e)))).
Defined.

Definition trivial_adj_equiv_to_disp_to_adj
           {B C : bicat}
           (HC_2_1 : is_univalent_2_1 C)
           {b : B}
           {c₁ c₂ : trivial_displayed_bicat B C b}
           (e : adjoint_equivalence c₁ c₂)
  : trivial_disp_adj_equiv_to_adj_equiv
      (trivial_adj_equiv_to_disp_adj_equiv e)
    =
    e.
Proof.
  use subtypePath.
  {
    intro.
    use isaprop_left_adjoint_equivalence.
    exact HC_2_1.
  }
  apply idpath.
Qed.

Definition trivial_disp_adj_equiv_to_adj_to_disp
           {B C : bicat}
           (HB_2_1 : is_univalent_2_1 B)
           (HC_2_1 : is_univalent_2_1 C)
           {b : B}
           {c₁ c₂ : trivial_displayed_bicat B C b}
           (e : disp_adjoint_equivalence (internal_adjoint_equivalence_identity b) c₁ c₂)
  : trivial_adj_equiv_to_disp_adj_equiv
      (trivial_disp_adj_equiv_to_adj_equiv e)
    =
    e.
Proof.
  use subtypePath.
  {
    intro.
    use isaprop_disp_left_adjoint_equivalence.
    - exact HB_2_1.
    - apply trivial_is_univalent_2_1.
      exact HC_2_1.
  }
  apply idpath.
Qed.

Definition trivial_adj_equiv_weq_disp_adj_equiv
           {B C : bicat}
           (HB_2_1 : is_univalent_2_1 B)
           (HC_2_1 : is_univalent_2_1 C)
           {b : B}
           (c₁ c₂ : trivial_displayed_bicat B C b)
  : adjoint_equivalence c₁ c₂
    ≃
    disp_adjoint_equivalence (internal_adjoint_equivalence_identity b) c₁ c₂.
Proof.
  use make_weq.
  - exact trivial_adj_equiv_to_disp_adj_equiv.
  - use isweq_iso.
    + exact trivial_disp_adj_equiv_to_adj_equiv.
    + exact (trivial_adj_equiv_to_disp_to_adj HC_2_1).
    + exact (trivial_disp_adj_equiv_to_adj_to_disp HB_2_1 HC_2_1).
Defined.

Definition trivial_is_univalent_2_0
           {B C : bicat}
           (HB_2_1 : is_univalent_2_1 B)
           (HC_2_0 : is_univalent_2_0 C)
           (HC_2_1 : is_univalent_2_1 C)
  : disp_univalent_2_0 (trivial_displayed_bicat B C).
Proof.
  use fiberwise_univalent_2_0_to_disp_univalent_2_0.
  intros b c₁ c₂.
  use weqhomot.
  - exact (trivial_adj_equiv_weq_disp_adj_equiv HB_2_1 HC_2_1 c₁ c₂
           ∘ make_weq (idtoiso_2_0 c₁ c₂) (HC_2_0 c₁ c₂))%weq.
  - intros p.
    cbn in p.
    induction p.
    use subtypePath.
    {
      intro.
      use isaprop_disp_left_adjoint_equivalence.
      - exact HB_2_1.
      - apply trivial_is_univalent_2_1.
        exact HC_2_1.
    }
    apply idpath.
Defined.
