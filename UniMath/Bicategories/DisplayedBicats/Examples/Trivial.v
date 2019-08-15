(* ----------------------------------------------------------------------------------- *)
(** ** Trivial display.

   Every bicategory is, in a trivial way, a displayed bicategory over any other
   bicategory.                                                                         *)
(* ----------------------------------------------------------------------------------- *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.Initial.
Require Import UniMath.Bicategories.Core.Examples.Final.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.

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
