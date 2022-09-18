(*******************************************************************

 The trivial comprehension bicategory

 If we have a bicategory with products, then we obtain a
 comprehension bicategory. The fibration comes from the trivial
 displayed bicategory and for the comprehension pseudofunctor, we
 use that the bicategory has products.

 Contents
 1. The comprehension pseudofunctor
 2. Preservation of cartesian 1-cells
 3. Preservation of (op)cartesian 2-cells
 4. The comprehension bicategory

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Properties.
Require Import UniMath.Bicategories.Morphisms.Properties.Projections.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.CartesianPseudoFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Trivial.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.TrivialCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.CodomainCleaving.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.Logic.ComprehensionBicat.

Local Open Scope cat.

Section TrivialCompBicat.
  Context (B : bicat_with_binprod).

  (**
   1. The comprehension pseudofunctor
   *)
  Definition trivial_comprehension_data
    : disp_psfunctor_data
        (trivial_displayed_bicat B B)
        (cod_disp_bicat B)
        (id_psfunctor B).
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - intros x y.
      use make_ar.
      + exact (x ⊗ y).
      + exact π₁.
    - intros x₁ x₂ f y₁ y₂ g.
      use make_disp_1cell_cod.
      + exact (f ⊗₁ g).
      + apply inv_of_invertible_2cell.
        apply pair_1cell_pr1.
    - intros x₁ x₂ f₁ f₂ α y₁ y₂ g₁ g₂ β.
      use make_disp_2cell_cod.
      + exact (α ⊗₂ β).
      + abstract
          (unfold coherent_homot ;
           cbn ;
           use vcomp_move_R_pM ; [ is_iso | ] ;
           cbn ;
           rewrite !vassocr ;
           use vcomp_move_L_Mp ; [ is_iso | ] ;
           cbn ;
           apply prod_2cell_pr1_alt).
    - intro ; intros ; simpl.
      simple refine (_ ,, _).
      + use make_disp_2cell_cod.
        * exact ((pair_1cell_id_id_invertible _ _ _)^-1).
        * abstract
            (unfold coherent_homot ;
             cbn ;
             refine (maponpaths _ (binprod_ump_2cell_pr1 _ _ _) @ _) ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite lwhisker_id2 ;
             rewrite !vassocl ;
             rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)) ;
             rewrite linvunitor_lunitor ;
             rewrite id2_left ;
             apply runitor_rinvunitor).
      + use is_disp_invertible_2cell_cod.
        cbn.
        apply binprod_ump_2cell_invertible ; is_iso.
    - intro ; intros ; simpl.
      simple refine (_ ,, _).
      + use make_disp_2cell_cod.
        * apply pair_1cell_comp.
        * abstract
            (unfold coherent_homot ;
             cbn ;
             rewrite !vassocl ;
             etrans ; [ do 5 apply maponpaths ; apply binprod_ump_2cell_pr1 | ] ;
             rewrite !vassocr ;
             apply maponpaths_2 ;
             rewrite !vassocl ;
             etrans ;
             [ do 4 apply maponpaths ;
               rewrite !vassocr ;
               rewrite lassociator_rassociator ;
               rewrite id2_left ;
               apply idpath
             | ] ;
             etrans ;
             [ do 3 apply maponpaths ;
               rewrite !vassocr ;
               rewrite lwhisker_vcomp ;
               rewrite vcomp_linv ;
               rewrite lwhisker_id2 ;
               rewrite id2_left ;
               apply idpath
             | ] ;
             etrans ;
             [ do 2 apply maponpaths ;
               rewrite !vassocr ;
               rewrite rassociator_lassociator ;
               rewrite id2_left ;
               apply idpath
             | ] ;
             etrans ;
             [ apply maponpaths ;
               rewrite !vassocr ;
               rewrite rwhisker_vcomp ;
               rewrite vcomp_linv ;
               rewrite id2_rwhisker ;
               rewrite id2_left ;
               apply idpath
             | ] ;
             rewrite lassociator_rassociator ;
             rewrite lwhisker_id2 ;
             apply idpath).
      + use is_disp_invertible_2cell_cod.
        cbn.
        apply pair_1cell_comp_invertible.
  Defined.

  Definition trivial_comprehension_is_disp_psfunctor
    : is_disp_psfunctor
        (trivial_displayed_bicat B B)
        (cod_disp_bicat B)
        (id_psfunctor B)
        trivial_comprehension_data.
  Proof.
  repeat split ; intro ; intros ;
    (use subtypePath ; [ intro ; apply cellset_property | ]).
  - refine (_ @ !(transportb_cell_of_cod_over _ _)).
    apply pair_2cell_id_id.
  - refine (_ @ !(transportb_cell_of_cod_over _ _)).
    apply pair_2cell_comp.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lunitor _ _) _)).
    apply binprod_lunitor.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_runitor _ _) _)).
    apply binprod_runitor.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lassociator _ _ _ _) _)).
    apply binprod_lassociator.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lwhisker _ _ _) _)).
    apply binprod_lwhisker.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_rwhisker _ _ _) _)).
    apply binprod_rwhisker.
  Qed.

  Definition trivial_comprehension
    : disp_psfunctor
        (trivial_displayed_bicat B B)
        (cod_disp_bicat B)
        (id_psfunctor B).
  Proof.
    simple refine (_ ,, _).
    - exact trivial_comprehension_data.
    - exact trivial_comprehension_is_disp_psfunctor.
  Defined.

  (**
   2. Preservation of cartesian 1-cells
   *)
  Section GlobalCartesian.
    Context {b₁ b₂ : B}
            (f : b₁ --> b₂)
            {c₁ c₂ : B}
            (l : c₁ --> c₂)
            (Hl : left_adjoint_equivalence l).

    Let cone : pb_cone f π₁
      := make_pb_cone
           (b₁ ⊗ c₁)
           π₁
           (f ⊗₁ l)
           (inv_of_invertible_2cell (pair_1cell_pr1 B f l)).

    Let r : c₂ --> c₁
      := left_adjoint_right_adjoint Hl.
    Let η : invertible_2cell (id₁ c₁) (l · left_adjoint_right_adjoint Hl)
      := left_equivalence_unit_iso Hl.
    Let ε : invertible_2cell (left_adjoint_right_adjoint Hl · l) (id₁ c₂)
      := left_equivalence_counit_iso Hl.

    Section AdjEquivToUMP1.
      Context (q : pb_cone f (π₁ : b₂ ⊗ c₂ --> b₂)).

      Local Definition adj_equiv_to_pb_ump_1_pb_1cell_map
        : q --> b₁ ⊗ c₁
        := ⟨ pb_cone_pr1 q , pb_cone_pr2 q · π₂ · r ⟩.

      Local Notation "'φ'" := adj_equiv_to_pb_ump_1_pb_1cell_map.

      Local Definition adj_equiv_to_pb_ump_1_pb_1cell_π₁
        : invertible_2cell (φ · π₁) (pb_cone_pr1 q)
        := prod_1cell_pr1 _ _ _.

      Local Notation "'φπ₁'" := adj_equiv_to_pb_ump_1_pb_1cell_π₁.

      Local Definition adj_equiv_to_pb_ump_1_pb_1cell_cell_π₁
        : φ · (f ⊗₁ l) · π₁ ==> pb_cone_pr2 q · π₁
        := rassociator _ _ _
           • (_ ◃ pair_1cell_pr1 _ _ _)
           • lassociator _ _ _
           • (prod_1cell_pr1 _ _ _ ▹ _)
           • pb_cone_cell _.

      Local Notation "'φπ₂_cell_π₁'" := adj_equiv_to_pb_ump_1_pb_1cell_cell_π₁.

      Local Definition adj_equiv_to_pb_ump_1_pb_1cell_cell_π₂
        : φ · (f ⊗₁ l) · π₂ ==> pb_cone_pr2 q · π₂
        := rassociator _ _ _
           • (_ ◃ pair_1cell_pr2 _ _ _)
           • lassociator _ _ _
           • (prod_1cell_pr2 _ _ _ ▹ _)
           • rassociator _ _ _
           • (_ ◃ ε)
           • runitor _.

      Local Notation "'φπ₂_cell_π₂'" := adj_equiv_to_pb_ump_1_pb_1cell_cell_π₂.

      Local Definition adj_equiv_to_pb_ump_1_pb_1cell_cell
        : φ · (f ⊗₁ l) ==> pb_cone_pr2 q.
      Proof.
        use binprod_ump_2cell.
        - exact (pr2 (binprod_of B b₂ c₂)).
        - exact φπ₂_cell_π₁.
        - exact φπ₂_cell_π₂.
      Defined.

      Local Notation "'φπ₂_cell'" := adj_equiv_to_pb_ump_1_pb_1cell_cell.

      Local Definition adj_equiv_to_pb_ump_1_pb_1cell_invcell
        : invertible_2cell (φ · (f ⊗₁ l)) (pb_cone_pr2 q).
      Proof.
        use make_invertible_2cell.
        - exact φπ₂_cell.
        - use binprod_ump_2cell_invertible ;
          unfold adj_equiv_to_pb_ump_1_pb_1cell_cell_π₁ ;
          unfold adj_equiv_to_pb_ump_1_pb_1cell_cell_π₂.
          + is_iso.
            * apply pair_1cell_pr1.
            * apply prod_1cell_pr1.
            * apply pb_cone_cell.
          + is_iso.
            * apply pair_1cell_pr2.
            * apply prod_1cell_pr2.
            * apply ε.
      Defined.

      Local Notation "'φπ₂'" := adj_equiv_to_pb_ump_1_pb_1cell_invcell.

      Local Definition adj_equiv_to_pb_ump_1_pb_1cell_eq
        : φ ◃ pb_cone_cell cone
          =
          lassociator φ (pb_cone_pr1 cone) f
          • (φπ₁ ▹ f)
          • pb_cone_cell q
          • (φπ₂ ^-1 ▹ π₁)
          • rassociator φ (pb_cone_pr2 cone) π₁.
      Proof.
        cbn.
        rewrite !vassocl.
        refine (!_).
        etrans.
        {
          do 3 apply maponpaths.
          apply maponpaths_2.
          apply binprod_ump_2cell_pr1.
        }
        rewrite !vassocl.
        rewrite lassociator_rassociator.
        rewrite id2_right.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !vassocr.
          rewrite vcomp_rinv.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite rwhisker_vcomp.
          rewrite vcomp_rinv.
          rewrite id2_rwhisker.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite lassociator_rassociator.
        rewrite id2_left.
        apply idpath.
      Qed.

      Definition adj_equiv_to_pb_ump_1_pb_1cell
        : pb_1cell q cone.
      Proof.
        use make_pb_1cell.
        - exact φ.
        - exact φπ₁.
        - exact φπ₂.
        - exact adj_equiv_to_pb_ump_1_pb_1cell_eq.
      Defined.
    End AdjEquivToUMP1.

    Definition adj_equiv_to_pb_ump_1
      : pb_ump_1 cone.
    Proof.
      intro q.
      exact (adj_equiv_to_pb_ump_1_pb_1cell q).
    Defined.

    Section AdjEquivToUMP2.
      Context {q : B}
              {φ ψ : q --> cone}
              (α : φ · pb_cone_pr1 cone ==> ψ · pb_cone_pr1 cone)
              (β : φ · pb_cone_pr2 cone ==> ψ · pb_cone_pr2 cone)
              (p : (φ ◃ pb_cone_cell cone)
                   • lassociator φ (pb_cone_pr2 cone) π₁
                   • (β ▹ π₁)
                   • rassociator ψ (pb_cone_pr2 cone) π₁
                   =
                   lassociator φ (pb_cone_pr1 cone) f
                   • (α ▹ f)
                   • rassociator ψ (pb_cone_pr1 cone) f
                   • (ψ ◃ pb_cone_cell cone)).

      Let φπ₂ : φ · π₂ ==> ψ · π₂
        := fully_faithful_1cell_inv_map
             (adj_equiv_fully_faithful Hl)
             (rassociator φ π₂ l
              • (φ ◃ (pair_1cell_pr2 B f l) ^-1)
              • lassociator φ (f ⊗₁ l) π₂
              • (β ▹ π₂)
              • rassociator ψ (f ⊗₁ l) π₂
              • (ψ ◃ pair_1cell_pr2 B f l)
              • lassociator ψ π₂ l).

      Definition adj_equiv_to_pb_ump_2_unique
        : isaprop (∑ (γ : φ ==> ψ),
                   γ ▹ pb_cone_pr1 cone = α
                   ×
                   γ ▹ pb_cone_pr2 cone = β).
      Proof.
        use invproofirrelevance.
        intros ζ₁ ζ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply cellset_property.
        }
        use binprod_ump_2cell_unique.
        - exact (pr2 (binprod_of B b₁ c₁)).
        - exact α.
        - exact φπ₂.
        - exact (pr12 ζ₁).
        - use (fully_faithful_1cell_eq (adj_equiv_fully_faithful Hl)).
          refine (!_).
          etrans.
          {
            apply fully_faithful_1cell_inv_map_eq.
          }
          cbn -[η].
          rewrite !vassocl.
          use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
          rewrite rwhisker_rwhisker.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite !vassocl.
          use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
          rewrite <- vcomp_whisker.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite !vassocl.
          use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
          rewrite <- rwhisker_rwhisker_alt.
          apply maponpaths_2.
          apply maponpaths.
          exact (!(pr22 ζ₁)).
        - exact (pr12 ζ₂).
        - use (fully_faithful_1cell_eq (adj_equiv_fully_faithful Hl)).
          refine (!_).
          etrans.
          {
            apply fully_faithful_1cell_inv_map_eq.
          }
          cbn -[η].
          rewrite !vassocl.
          use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
          rewrite rwhisker_rwhisker.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite !vassocl.
          use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
          rewrite <- vcomp_whisker.
          rewrite !vassocr.
          apply maponpaths_2.
          rewrite !vassocl.
          use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
          rewrite <- rwhisker_rwhisker_alt.
          apply maponpaths_2.
          apply maponpaths.
          exact (!(pr22 ζ₂)).
      Qed.

      Definition adj_equiv_to_pb_ump_2_cell
        : φ ==> ψ.
      Proof.
        use binprod_ump_2cell.
        - exact (pr2 (binprod_of B b₁ c₁)).
        - exact α.
        - exact φπ₂.
      Defined.

      Definition adj_equiv_to_pb_ump_2_cell_pr1
        : adj_equiv_to_pb_ump_2_cell ▹ pb_cone_pr1 cone = α.
      Proof.
        apply binprod_ump_2cell_pr1.
      Qed.

      Definition adj_equiv_to_pb_ump_2_cell_pr2
        : adj_equiv_to_pb_ump_2_cell ▹ pb_cone_pr2 cone = β.
      Proof.
        use binprod_ump_2cell_unique.
        - exact (pr2 (binprod_of B b₂ c₂)).
        - exact (rassociator _ _ _
                 • (_ ◃ pair_1cell_pr1 _ _ _)
                 • lassociator _ _ _
                 • (α ▹ f)
                 • rassociator _ _ _
                 • (_ ◃ (pair_1cell_pr1 _ _ _)^-1)
                 • lassociator _ _ _).
        - exact (β ▹ _).
        - cbn ; cbn in p.
          rewrite !vassocl.
          use vcomp_move_L_pM ; [ is_iso | ].
          cbn.
          rewrite rwhisker_rwhisker.
          rewrite !vassocr.
          apply maponpaths_2.
          use vcomp_move_L_Mp ; [ is_iso | ].
          cbn.
          rewrite vcomp_whisker.
          rewrite !vassocl.
          apply maponpaths.
          rewrite !vassocr.
          use vcomp_move_L_Mp ; [ is_iso | ].
          cbn.
          rewrite <- rwhisker_rwhisker.
          do 2 apply maponpaths.
          apply binprod_ump_2cell_pr1.
        - cbn.
          use (vcomp_lcancel (lassociator _ _ _)) ; [ is_iso | ].
          rewrite rwhisker_rwhisker.
          use (vcomp_lcancel (_ ◃ (pair_1cell_pr2 B f l)^-1)) ; [ is_iso | ].
          rewrite !vassocr.
          rewrite <- vcomp_whisker.
          use (vcomp_lcancel (rassociator _ _ _)) ; [ is_iso | ].
          rewrite !vassocr.
          rewrite <- rwhisker_rwhisker_alt.
          etrans.
          {
            do 3 apply maponpaths_2.
            apply maponpaths.
            apply binprod_ump_2cell_pr2.
          }
          do 3 (use vcomp_move_R_Mp ; [ is_iso | ]).
          apply fully_faithful_1cell_inv_map_eq.
        - rewrite !vassocl.
          use vcomp_move_L_pM ; [ is_iso | ].
          cbn.
          use vcomp_move_L_pM ; [ is_iso ; apply pair_1cell_pr1 | ].
          cbn.
          rewrite !vassocr.
          use vcomp_move_L_Mp ; [ is_iso | ].
          cbn.
          exact p.
        - apply idpath.
      Qed.
    End AdjEquivToUMP2.

    Definition adj_equiv_to_pb_ump_2
      : pb_ump_2 cone.
    Proof.
      intros q φ ψ α β p.
      use iscontraprop1.
      - exact (adj_equiv_to_pb_ump_2_unique α β).
      - exact (adj_equiv_to_pb_ump_2_cell α β
               ,,
               adj_equiv_to_pb_ump_2_cell_pr1 α β
               ,,
               adj_equiv_to_pb_ump_2_cell_pr2 α β p).
    Defined.

    Definition adj_equiv_to_pb
      : has_pb_ump cone.
    Proof.
      split.
      - exact adj_equiv_to_pb_ump_1.
      - exact adj_equiv_to_pb_ump_2.
    Defined.
  End GlobalCartesian.

  Definition global_cartesian_trivial_comprehension
    : global_cartesian_disp_psfunctor trivial_comprehension.
  Proof.
    intros b₁ b₂ f c₁ c₂ g Hg ; cbn in *.
    apply is_pb_to_cartesian_1cell.
    pose (g_equiv := trivial_cartesian_1cell_is_adj_equiv _ _ _ _ Hg).
    apply (adj_equiv_to_pb f g g_equiv).
  Defined.

  (**
   3. Preservation of (op)cartesian 2-cells
   *)
  Definition local_cartesian_trivial_comprehension
    : local_cartesian_disp_psfunctor trivial_comprehension.
  Proof.
    intros b₁ b₂ f₁ f₂ α c₁ c₂ g₁ g₂ β Hβ ; cbn in *.
    apply is_cartesian_2cell_sfib_to_is_cartesian_2cell ; cbn.
    apply invertible_to_cartesian.
    refine (transportb
              is_invertible_2cell
              (pair_2cell_pr2 _ _ _)
              _).
    is_iso.
    - apply prod_1cell_pr2.
    - exact (trivial_cartesian_2cell_is_invertible _ _ _ _ Hβ).
  Defined.

  Definition local_opcartesian_trivial_comprehension
    : local_opcartesian_disp_psfunctor trivial_comprehension.
  Proof.
    intros b₁ b₂ f₁ f₂ α c₁ c₂ g₁ g₂ β Hβ ; cbn in *.
    apply is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell ; cbn.
    apply invertible_to_opcartesian.
    refine (transportb
              is_invertible_2cell
              (pair_2cell_pr2 _ _ _)
              _).
    is_iso.
    - apply prod_1cell_pr2.
    - exact (trivial_opcartesian_2cell_is_invertible _ _ _ _ Hβ).
  Defined.

  (**
   4. The comprehension bicategory
   *)
  Definition trivial_comprehension_bicat_structure
    : comprehension_bicat_structure B.
  Proof.
    use make_comprehension_bicat_structure.
    - exact (trivial_displayed_bicat B B).
    - exact trivial_comprehension.
    - exact (trivial_global_cleaving B B).
    - exact global_cartesian_trivial_comprehension.
  Defined.

  Definition trivial_comprehension_is_covariant
    : is_covariant trivial_comprehension_bicat_structure.
  Proof.
    repeat split.
    - exact (trivial_local_opcleaving B B).
    - exact (trivial_lwhisker_opcartesian B B).
    - exact (trivial_rwhisker_opcartesian B B).
    - exact local_opcartesian_trivial_comprehension.
  Defined.

  Definition trivial_comprehension_is_contravariant
    : is_contravariant trivial_comprehension_bicat_structure.
  Proof.
    repeat split.
    - exact (trivial_local_cleaving B B).
    - exact (trivial_lwhisker_cartesian B B).
    - exact (trivial_rwhisker_cartesian B B).
    - exact local_cartesian_trivial_comprehension.
  Defined.

  Definition trivial_comprehension_bicat
    : comprehension_bicat
    := _ ,, _ ,, trivial_comprehension_is_covariant.

  Definition trivial_contravariant_comprehension_bicat
    : contravariant_comprehension_bicat
    := _ ,, _ ,, trivial_comprehension_is_contravariant.
End TrivialCompBicat.
