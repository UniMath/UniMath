(** * Bicategory of Display Map Categories
    Contents:
    - Displayed Bicategory of Display Map Categories [disp_bicat_display_map_cat]
      - Useful coercions
      - Univalence
    - Displayed Bicategory of Display Map Categories with Terminal Object [disp_bicat_terminal_display_map_cat]
      - Useful coercions
      - Univalence
    - Pseudofunctor into the Bicategory of Full Comprehension Categories [psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat]
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.DisplayMapCat.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.PrecompEquivalence.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.Core.Examples.StructuredCategories.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Prod.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sub1Cell.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.

(* Notations: *)
Import Bicat.Notations.
Import DispBicat.Notations.
Local Open Scope cat.

(** ** Displayed Bicategory of Display Map Categories *)
Definition disp_prebicat_1_id_comp_cells_display_map_cat
  : disp_prebicat_1_id_comp_cells bicat_of_univ_cats.
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * exact (λ C, display_map_class (pr1 C)).
      * exact (λ _ _ D₁ D₂ F, is_display_map_class_functor D₁ D₂ F).
    + use tpair.
      * exact (λ _ _, is_display_map_class_functor_identity _).
      * exact (λ _ _ _ _ _ _ _ _ HF HG, is_display_map_class_functor_composite HF HG).
  - exact (λ _ _ _ _ _ _ _ _ _, unit).
Defined.

Definition disp_prebicat_ops_display_map_cat
  : disp_prebicat_ops disp_prebicat_1_id_comp_cells_display_map_cat.
Proof.
  repeat split; apply tt.
Defined.

Definition disp_prebicat_data_display_map_cat
  : disp_prebicat_data bicat_of_univ_cats.
Proof.
  use tpair.
  - exact disp_prebicat_1_id_comp_cells_display_map_cat.
  - exact disp_prebicat_ops_display_map_cat.
Defined.

Definition disp_prebicat_laws_display_map_cat
  : disp_prebicat_laws disp_prebicat_data_display_map_cat.
Proof.
  repeat split; intro; intros; apply isProofIrrelevantUnit.
Qed.

Definition disp_prebicat_display_map_cat
  : disp_prebicat bicat_of_univ_cats.
Proof.
  use tpair.
  - exact disp_prebicat_data_display_map_cat.
  - exact disp_prebicat_laws_display_map_cat.
Defined.

Definition has_disp_cellset_display_map_cat
  : has_disp_cellset disp_prebicat_display_map_cat.
Proof.
  intro; intros; cbn.
  exact isasetunit.
Qed.

Definition disp_bicat_display_map_cat
  : disp_bicat bicat_of_univ_cats.
Proof.
  use tpair.
  - exact disp_prebicat_display_map_cat.
  - exact has_disp_cellset_display_map_cat.
Defined.

Definition bicat_display_map_cat := total_bicat disp_bicat_display_map_cat.

(** *** Coercions *)
Definition display_map_cat := bicat_display_map_cat.
Coercion bicat_display_map_cat_ob_to_display_map_cat (D : bicat_display_map_cat) : display_map_cat := D.
Coercion display_map_cat_to_base_cat (D : display_map_cat) : univalent_category := pr1 D.

(** *** Univalence *)
Proposition disp_univalent_2_1_disp_bicat_display_map_cat
  : disp_univalent_2_1 disp_bicat_display_map_cat.
Proof.
  use fiberwise_local_univalent_is_univalent_2_1.
  intros C₁ C₂ F D₁ D₂ HF HF'.
  use isweqcontrcontr.
  - apply isPredicate_is_display_map_class_functor.
  - unfold disp_invertible_2cell, id2_invertible_2cell, is_invertible_2cell_id₂, make_invertible_2cell, make_is_invertible_2cell, is_disp_invertible_2cell, id2_left, nat_trans_id; cbn.
    apply iscontr_prod; [exact iscontrunit | apply iscontr_prod; [exact iscontrunit | apply iscontr_prod]].
    all: apply isapropunit.
Defined.

Definition display_map_class_adj_to_disp_adjoint_equiv
  {C : bicat_of_univ_cats} (D D' : disp_bicat_display_map_cat C)
  : is_display_map_class_functor D D' (functor_identity (univalent_category_to_category C))
    × is_display_map_class_functor D' D (functor_identity (univalent_category_to_category C))
  -> disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) D D'.
Proof.
  intros [HF HG].
  exists HF. use tpair.
  - exists HG. exact (tt ,, tt).
  - abstract (split; use tpair;
      [ apply isapropunit
      | apply isapropunit
      | exists tt; split; apply isapropunit
      | exists tt; split; apply isapropunit
    ]).
Defined.

Definition disp_adjoint_equiv_to_display_map_class_adj
  {C : bicat_of_univ_cats} (D D' : disp_bicat_display_map_cat C)
  : disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) D D'
  -> is_display_map_class_functor D D' (functor_identity (univalent_category_to_category C))
    × is_display_map_class_functor D' D (functor_identity (univalent_category_to_category C)).
Proof.
  intros [HF [[HG ?] ?]]. exact (HF ,, HG).
Defined.

Lemma display_map_class_adj_to_disp_adj_to_adj
  {C : bicat_of_univ_cats} (D D' : disp_bicat_display_map_cat C)
  : ∏ adj : is_display_map_class_functor D D' (functor_identity (univalent_category_to_category C)) × is_display_map_class_functor D' D (functor_identity (univalent_category_to_category C)),
    disp_adjoint_equiv_to_display_map_class_adj D D'
      (display_map_class_adj_to_disp_adjoint_equiv D D' adj) = adj.
Proof.
  intros [HF HG]. apply dirprod_paths; apply isPredicate_is_display_map_class_functor.
Qed.

Lemma disp_adjoint_equivalence_to_adj_to_disp_adj
  {C : bicat_of_univ_cats} (D D' : disp_bicat_display_map_cat C)
  : ∏ adj : disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) D D',
    display_map_class_adj_to_disp_adjoint_equiv D D'
      (disp_adjoint_equiv_to_display_map_class_adj D D' adj) = adj.
Proof.
  intros adj. apply subtypePath.
  {
    intro. apply isaprop_disp_left_adjoint_equivalence.
    - apply univalent_cat_is_univalent_2_1.
    - apply disp_univalent_2_1_disp_bicat_display_map_cat.
  }
  apply idpath.
Qed.

Definition display_map_class_adjoint_weq_disp_adjoint_equivalence
  {C : bicat_of_univ_cats} (D D' : disp_bicat_display_map_cat C)
  : is_display_map_class_functor D D' (functor_identity (univalent_category_to_category C))
    × is_display_map_class_functor D' D (functor_identity (univalent_category_to_category C))
  ≃ disp_adjoint_equivalence (idtoiso_2_0 C C (idpath C)) D D'.
Proof.
  use make_weq.
  - apply display_map_class_adj_to_disp_adjoint_equiv.
  - use isweq_iso.
    + apply disp_adjoint_equiv_to_display_map_class_adj.
    + apply display_map_class_adj_to_disp_adj_to_adj.
    + apply disp_adjoint_equivalence_to_adj_to_disp_adj.
Qed.

Proposition disp_univalent_2_0_disp_bicat_display_map_cat
  : disp_univalent_2_0 disp_bicat_display_map_cat.
Proof.
  use fiberwise_univalent_2_0_to_disp_univalent_2_0.
  intros C D D'.
  use weqhomot.
  - refine (display_map_class_adjoint_weq_disp_adjoint_equivalence D D'
           ∘ display_map_class_data_equiv_weq_display_map_class_adjoint D D' 
           ∘ display_map_class_equiv_weq_data_equiv D D')%weq.
  - intros p; cbn in p. induction p.
    use subtypePath.
    {
      intro. apply isaprop_disp_left_adjoint_equivalence.
      - apply univalent_cat_is_univalent_2_1.
      - apply disp_univalent_2_1_disp_bicat_display_map_cat.
    }
    apply isPredicate_is_display_map_class_functor.
Qed.

Definition disp_univalent_2_disp_bicat_display_map_cat
  : disp_univalent_2 disp_bicat_display_map_cat.
Proof.
  split.
  - exact disp_univalent_2_0_disp_bicat_display_map_cat.
  - exact disp_univalent_2_1_disp_bicat_display_map_cat.
Qed.

Definition univalent_2_bicat_display_map_cat
  : is_univalent_2 bicat_display_map_cat.
Proof.
  use total_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_display_map_cat.
  - exact univalent_cat_is_univalent_2.
Qed.

(** ** Displayed Bicategory of Display Map Categories with Terminal object in base *)
Definition disp_bicat_terminal_display_map_cat :
  disp_bicat bicat_of_univ_cats.
Proof.
  use disp_dirprod_bicat.
  - exact disp_bicat_terminal_obj.
  - exact disp_bicat_display_map_cat.
Defined.

Definition bicat_terminal_display_map_cat := total_bicat disp_bicat_terminal_display_map_cat.

(** *** Coercions *)
Definition terminal_display_map_cat : UU := bicat_terminal_display_map_cat.

Coercion terminal_display_map_cat_to_univ_base (D : terminal_display_map_cat) : univalent_category := pr1 D.

Coercion terminal_display_map_cat_to_terminal (D : terminal_display_map_cat) : Terminal D := pr112 D.

Coercion terminal_display_map_cat_to_display_map_class (D : terminal_display_map_cat) : display_map_class D := pr22 D.

Definition terminal_display_map_functor (D₁ D₂ : bicat_terminal_display_map_cat) : UU := bicat_terminal_display_map_cat ⟦ D₁, D₂ ⟧.

Coercion bicat_terminal_display_map_cat_1cell_to_terminal_display_map_functor {D₁ D₂ : bicat_terminal_display_map_cat} (F : bicat_terminal_display_map_cat ⟦ D₁, D₂ ⟧) : terminal_display_map_functor _ _ := F.

Coercion terminal_display_map_functor_to_display_map_class_functor {D₁ D₂ : terminal_display_map_cat} (F : terminal_display_map_functor D₁ D₂) : display_map_class_functor D₁ D₂ := (pr1 F ,, pr22 F).
Coercion terminal_display_map_functor_preserves_terminal {D₁ D₂ : terminal_display_map_cat} (F : terminal_display_map_functor D₁ D₂) : preserves_terminal F := pr212 F.

Definition terminal_display_map_nat_trans {D₁ D₂ : bicat_terminal_display_map_cat} (F G : bicat_terminal_display_map_cat ⟦ D₁, D₂ ⟧) : UU := prebicat_cells bicat_terminal_display_map_cat F G.
Coercion bicat_terminal_display_map_cat_2cell_to_nat_trans {D₁ D₂ : bicat_terminal_display_map_cat} {F G : bicat_terminal_display_map_cat ⟦ D₁, D₂ ⟧} (θ : prebicat_cells bicat_terminal_display_map_cat F G) : terminal_display_map_nat_trans F G := θ.
Coercion terminal_display_map_nat_trans_to_base_nat_trans {D₁ D₂ : bicat_terminal_display_map_cat} {F G : bicat_terminal_display_map_cat ⟦ D₁, D₂ ⟧} (θ : terminal_display_map_nat_trans F G) : nat_trans _ _ := pr1 θ.

(** *** Univalence of [disp_bicat_terminal_display_map_cat]. *)
Definition is_univalent_2_1_disp_bicat_terminal_display_map_cat
  : disp_univalent_2_1 disp_bicat_terminal_display_map_cat.
Proof.
  use is_univalent_2_1_dirprod_bicat.
  - exact disp_univalent_2_1_disp_bicat_terminal_obj.
  - exact disp_univalent_2_1_disp_bicat_display_map_cat.
Qed.

Definition is_univalent_2_0_disp_bicat_terminal_display_map_cat
  : disp_univalent_2_0 disp_bicat_terminal_display_map_cat.
Proof.
  use is_univalent_2_0_dirprod_bicat.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_disp_bicat_terminal_obj.
  - exact disp_univalent_2_disp_bicat_display_map_cat.
Qed.

Definition is_univalent_2_disp_bicat_terminal_display_map_cat
  : disp_univalent_2 disp_bicat_terminal_display_map_cat.
Proof.
  use is_univalent_2_dirprod_bicat.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_disp_bicat_terminal_obj.
  - exact disp_univalent_2_disp_bicat_display_map_cat.
Qed.

Definition is_univalent_2_1_bicat_terminal_display_map_cat
  : is_univalent_2_1 bicat_terminal_display_map_cat.
Proof.
  use is_univalent_2_1_total_dirprod.
  - exact univalent_cat_is_univalent_2_1.
  - exact disp_univalent_2_1_disp_bicat_terminal_obj.
  - exact disp_univalent_2_1_disp_bicat_display_map_cat.
Qed.

Definition is_univalent_2_0_bicat_terminal_display_map_cat
  : is_univalent_2_0 bicat_terminal_display_map_cat.
Proof.
  use is_univalent_2_0_total_dirprod.
  - exact univalent_cat_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_terminal_obj.
  - exact disp_univalent_2_disp_bicat_display_map_cat.
Qed.

Definition is_univalent_2_bicat_terminal_display_map_cat
  : is_univalent_2 bicat_terminal_display_map_cat.
Proof.
  use is_univalent_2_total_dirprod.
  - exact univalent_cat_is_univalent_2.
  - exact disp_univalent_2_disp_bicat_terminal_obj.
  - exact disp_univalent_2_disp_bicat_display_map_cat.
Qed.

(** ** Pseudofunctor from the bicategory of display map categories with terminal objects into the bicategory of full comprehension categories. *)

(** *** Pseudofunctor Data *)
Definition bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : bicat_terminal_display_map_cat → bicat_full_comp_cat.
Proof.
  (* intros D. use make_full_comp_cat. *)
  refine (λ D : terminal_display_map_cat, _).
  use make_full_comp_cat.
  - use make_comp_cat.
    + use make_cat_with_terminal_cleaving.
      * use make_cat_with_terminal_disp_cat.
        -- exact D. (* NOTE: I do not know why the coercion [terminal_display_map_cat_to_base_cat] does not work here. *)
        -- exact D.
        -- exact (univalent_display_map_cat D).
      * exact display_map_cleaving.
    + exact (cartesian_ι _).
  - exact (ι_ff _).
Defined.

Definition terminal_display_map_functor_to_full_comp_cat_functor
  : ∏ D₁ D₂ : bicat_terminal_display_map_cat,
      bicat_terminal_display_map_cat ⟦ D₁, D₂ ⟧
      → bicat_full_comp_cat ⟦ bicat_terminal_display_map_cat_to_bicat_full_comp_cat D₁, bicat_terminal_display_map_cat_to_bicat_full_comp_cat D₂ ⟧.
Proof.
  intros D₁ D₂ F; use make_full_comp_cat_functor.
  - use make_comp_cat_functor.
    + use make_functor_with_terminal_cleaving.
      * use make_functor_with_terminal_disp_cat.
        -- exact F.
        -- exact F.
        -- exact (display_map_functor F).
      * exact (is_cartesian_display_map_functor (_ ,, _)).
    + exact (pr1 (map_ι_is_ι_map F)).
  - abstract (intros x dx; exists (pr1 ((pr11 (map_ι_is_ι_map F)) x dx)); exists (id_left _); apply id_right).
Defined.

Definition terminal_display_map_transformation_to_full_comp_cat_transformation
  : ∏ (D₁ D₂ : bicat_terminal_display_map_cat) (F G : bicat_terminal_display_map_cat ⟦ D₁, D₂ ⟧),
    prebicat_cells bicat_terminal_display_map_cat F G
    → prebicat_cells bicat_full_comp_cat (terminal_display_map_functor_to_full_comp_cat_functor D₁ D₂ F)
        (terminal_display_map_functor_to_full_comp_cat_functor D₁ D₂ G).
Proof.
  intros D₁ D₂ F G θ.
  use make_full_comp_cat_nat_trans; use make_comp_cat_nat_trans.
  - use make_nat_trans_with_terminal_cleaving. use make_nat_trans_with_terminal_disp_cat.
    + exact θ.
    + use (display_map_nat_trans _).
  - abstract (
        intros x dx; simpl in x,dx; cbn;
        rewrite id_left, id_right;
        exact (idpath _)).
Defined.

Definition bicat_terminal_display_map_to_bicat_full_comp_cat_id_1cell
  : ∏ D : bicat_terminal_display_map_cat,
      prebicat_cells bicat_full_comp_cat (identity (bicat_terminal_display_map_cat_to_bicat_full_comp_cat D))
        (terminal_display_map_functor_to_full_comp_cat_functor D D (identity D)).
Proof.
  intros D. use make_full_comp_cat_nat_trans. use make_comp_cat_nat_trans.
  - use make_nat_trans_with_terminal_cleaving. use make_nat_trans_with_terminal_disp_cat.
    + exact (nat_trans_id _).
    + cbn. use (_ ,, _).
      * intros x dx; simpl in *. exists (identity _). abstract (exact (id_left _ @ !id_right _)).
      * abstract (intros x₁ x₂ f dx₁ dx₂ df;
        use eq_display_map_cat_mor; rewrite (transportb_display_map _ (identity (pr1 dx₁) · pr1 df ,, _));
        exact (id_right _ @ !id_left _)).
  - abstract (intros x dx; exact (id_right _ @ !id_left _)).
Defined.

Definition bicat_terminal_display_map_to_bicat_full_comp_cat_comp_1cell
  : ∏ (D₁ D₂ D₃ : bicat_terminal_display_map_cat) (F : bicat_terminal_display_map_cat ⟦ D₁, D₂ ⟧) (G : bicat_terminal_display_map_cat ⟦ D₂, D₃ ⟧),
    prebicat_cells bicat_full_comp_cat
      (terminal_display_map_functor_to_full_comp_cat_functor D₁ D₂ F · terminal_display_map_functor_to_full_comp_cat_functor D₂ D₃ G)
      (terminal_display_map_functor_to_full_comp_cat_functor D₁ D₃ (F · G)).
Proof.
  intros D₁ D₂ D₃ F G. use make_full_comp_cat_nat_trans. use make_comp_cat_nat_trans.
  - use make_nat_trans_with_terminal_cleaving. use make_nat_trans_with_terminal_disp_cat.
    + exact (nat_trans_id _).
    + exact display_map_functor_composite_to_composite_display_map_functor.
  - abstract (intros x dx; cbn; rewrite ? (pr121 G); exact (!assoc _ _ _ @ id_left _ @ id_left _ @ !id_right _)).
Defined.

Definition psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : psfunctor_data bicat_terminal_display_map_cat bicat_full_comp_cat.
Proof.
  use make_psfunctor_data.
  - exact bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
  - exact terminal_display_map_functor_to_full_comp_cat_functor.
  - exact terminal_display_map_transformation_to_full_comp_cat_transformation.
  - exact bicat_terminal_display_map_to_bicat_full_comp_cat_id_1cell.
  - exact bicat_terminal_display_map_to_bicat_full_comp_cat_comp_1cell.
Defined.

(** *** Pseudofunctor Laws *)
Lemma psfunctor_id2_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : psfunctor_id2_law psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
Proof.
  intros D₁ D₂ F.
  use full_comp_nat_trans_eq.
  - intros x. apply idpath.
  - intros x dx. use eq_display_map_cat_mor. etrans.
    + apply transportf_display_map_mor.
    + apply idpath.
Qed.

Lemma psfunctor_vcomp2_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : psfunctor_vcomp2_law psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
Proof.
  intros D₁ D₂ F G H η ϕ.
  use full_comp_nat_trans_eq.
  - intros x. apply idpath.
  - intros x dx. use eq_display_map_cat_mor. etrans.
    + apply transportf_display_map_mor.
    + apply idpath.
Qed.

Lemma psfunctor_lunitor_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : psfunctor_lunitor_law psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
Proof.
  intros D₁ D₂ F.
  use full_comp_nat_trans_eq.
  - intros x. simpl. rewrite (pr121 F), id_left, id_left. apply idpath.
  - intros x dx. use eq_display_map_cat_mor. etrans.
    + apply transportf_display_map_mor.
    + simpl. rewrite (pr121 F), id_left, id_left. apply idpath.
Qed.

Lemma psfunctor_runitor_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : psfunctor_runitor_law psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
Proof.
  intros D₁ D₂ F.
  use full_comp_nat_trans_eq.
  - intros x. simpl. rewrite id_left, id_left. apply idpath.
  - intros x dx. use eq_display_map_cat_mor. etrans.
    + apply transportf_display_map_mor.
    + simpl. rewrite id_left, id_left. apply idpath.
Qed.

Lemma psfunctor_lassociator_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : psfunctor_lassociator_law psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
Proof.
  intros D₁ D₂ D₃ D₄ F G H.
  use full_comp_nat_trans_eq.
  - intros x. simpl. rewrite (pr121 H), id_left, id_left, id_left. apply (!id_left _).
  - intros x dx. use eq_display_map_cat_mor. etrans.
    + apply transportf_display_map_mor.
    + simpl. rewrite (pr121 H), id_left, id_left, id_left. apply (!id_left _).
Qed.

Lemma psfunctor_lwhisker_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : psfunctor_lwhisker_law psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
Proof.
  intros D₁ D₂ D₃ F G H η.
  use full_comp_nat_trans_eq.
  - intros x. simpl. rewrite id_right. apply (id_left _).
  - intros x dx. use eq_display_map_cat_mor. etrans.
    + apply transportf_display_map_mor.
    + simpl. rewrite id_right. apply (id_left _).
Qed.

Lemma psfunctor_rwhisker_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : psfunctor_rwhisker_law psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
Proof.
  intros D₁ D₂ D₃ F G H η.
  use full_comp_nat_trans_eq.
  - intros x. simpl. rewrite id_right. apply (id_left _).
  - intros x dx. use eq_display_map_cat_mor. etrans.
    + apply transportf_display_map_mor.
    + simpl. rewrite id_right. apply (id_left _).
Qed.

Definition psfunctor_laws_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : psfunctor_laws psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
Proof.
  split7.
  - exact psfunctor_id2_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
  - exact psfunctor_vcomp2_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
  - exact psfunctor_lunitor_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
  - exact psfunctor_runitor_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
  - exact psfunctor_lassociator_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
  - exact psfunctor_lwhisker_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
  - exact psfunctor_rwhisker_law_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
Qed.

Lemma helper_id2_cell_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  (D : bicat_terminal_display_map_cat)
  : disp_nat_trans
      (nat_trans_id
        (functor_data_from_functor
            (full_comp_cat_to_comp_cat (psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat D))
            (full_comp_cat_to_comp_cat (psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat D))
            (full_comp_cat_functor_to_comp_cat_functor (# psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat (id₁ D)))))
      (comp_cat_type_functor (full_comp_cat_functor_to_comp_cat_functor (# psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat (id₁ D))))
      (comp_cat_type_functor (full_comp_cat_functor_to_comp_cat_functor (id₁ (psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat D)))). 
Proof.
    use tpair.
    - intros x dx; cbn in *. exists (identity _). abstract (exact (id_left _ @ !id_right _)).
    - abstract (intros x₁ x₂ f dx₁ dx₂ [df Hsq];
      (* symmetry; etrans; use eq_display_map_cat_mor. *)
      use eq_display_map_cat_mor; symmetry; etrans;
      (* the following did not work: *)
      (* + apply transportb_display_map_mor. *)
      (* we'll unfold it instead: *)
      [ refine (pr1_transportf (A := (pr11 D)⟦_, _⟧) _ _ @ _); rewrite transportf_const; simpl; apply id_left | simpl; exact (!id_right _)]).
Defined.

Lemma psfunctor_id_is_invertible_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : ∏ D : bicat_terminal_display_map_cat,
      is_invertible_2cell (psfunctor_id psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat D).
Proof.
  intros D. use tpair.
  - use make_full_comp_cat_nat_trans. use make_comp_cat_nat_trans.
    + use make_nat_trans_with_terminal_cleaving. use make_nat_trans_with_terminal_disp_cat.
      * exact (nat_trans_id _).
      * exact (helper_id2_cell_bicat_terminal_display_map_cat_to_bicat_full_comp_cat _).
    + intros x dx; cbn in *. exact (idpath _).
  - abstract (use tpair; use full_comp_nat_trans_eq;
    [ intros x; exact (id_left _)
    | intros x dx; use eq_display_map_cat_mor; etrans;
      [ apply transportf_display_map_mor | exact (id_left _)]
    | intros x; exact (id_left _)
    | intros x dx; use eq_display_map_cat_mor; etrans;
      [ apply transportf_display_map_mor | exact (id_left _)]]).
Defined.

Lemma helper_comp2_cell_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  (D₁ D₂ D₃ : bicat_terminal_display_map_cat) (F : bicat_terminal_display_map_cat ⟦ D₁, D₂ ⟧) (G : bicat_terminal_display_map_cat ⟦ D₂, D₃ ⟧)
  : disp_nat_trans
  (nat_trans_id
     (functor_data_from_functor
        (full_comp_cat_to_comp_cat (psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat D₁))
        (full_comp_cat_to_comp_cat (psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat D₃))
        (full_comp_cat_functor_to_comp_cat_functor (# psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat (F · G)))))
  (comp_cat_type_functor (full_comp_cat_functor_to_comp_cat_functor (# psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat (F · G))))
  (comp_cat_type_functor (full_comp_cat_functor_to_comp_cat_functor (# psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat F · # psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat G))).
Proof.
  use tpair.
  - intros x dx. exists (identity _). abstract (exact (id_left _ @ !id_right _)).
  - abstract (intros x₁ x₂ f dx₁ dx₂ [df Hsq];
    use eq_display_map_cat_mor; symmetry; etrans;
    [ refine (pr1_transportf (A := _⟦_, _⟧) _ _ @ _); rewrite transportf_const; simpl; apply id_left | simpl; exact (!id_right _)]).
Defined.

Lemma psfunctor_comp_is_invertible_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : ∏ (D₁ D₂ D₃ : bicat_terminal_display_map_cat) (F : bicat_terminal_display_map_cat ⟦ D₁, D₂ ⟧) (G : bicat_terminal_display_map_cat ⟦ D₂, D₃ ⟧),
    is_invertible_2cell (psfunctor_comp psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat F G).
Proof.
  intros D₁ D₂ D₃ F G.
  use tpair.
  - use make_full_comp_cat_nat_trans. use make_comp_cat_nat_trans.
    + use make_nat_trans_with_terminal_cleaving. use make_nat_trans_with_terminal_disp_cat.
      * apply nat_trans_id.
      * apply helper_comp2_cell_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
    + abstract (intros x dx; cbn; rewrite functor_id; rewrite ? id_left; apply idpath).
  - abstract (split; use full_comp_nat_trans_eq;
      [ intros x; exact (id_left _)
      | intros x dx; use subtypePath; try (exact (λ _, homset_property _ _ _ _ _)); etrans;
        [ refine (pr1_transportf (A := _⟦_, _⟧) _ _ @ _); rewrite transportf_const;
          apply id_left | exact (idpath _) ]
      | intros x; exact (id_left _)
      | intros x dx; use subtypePath; try (exact (λ _, homset_property _ _ _ _ _)); etrans;
        [ refine (pr1_transportf (A := _⟦_, _⟧) _ _ @ _); rewrite transportf_const;
          apply id_left | exact (idpath _) ]]).
Defined.

Definition invertible_cells_psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : invertible_cells psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
Proof.
  split.
  - exact psfunctor_id_is_invertible_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
  - exact psfunctor_comp_is_invertible_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
Qed.

Definition psfunctor_bicat_terminal_display_map_cat_to_bicat_full_comp_cat
  : psfunctor bicat_terminal_display_map_cat bicat_full_comp_cat.
Proof.
  use make_psfunctor.
  - exact psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
  - exact psfunctor_laws_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
  - exact invertible_cells_psfunctor_data_bicat_terminal_display_map_cat_to_bicat_full_comp_cat.
Defined.

