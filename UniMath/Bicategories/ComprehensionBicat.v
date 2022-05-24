(*******************************************************************

 Comprehension bicategories

 In this file we define comprehension bicategories and we
 construct examples of them.

 1. Comprehension bicategories
 2. The trivial comprehension bicategory
 3. Locally groupoidal bicategories with pullbacks
 4. The comprehension bicategory of fibrations
 5. The comprehension bicategory of opfibrations
 6. The comprehension bicategory of a display map bicategory
 7. Internal Street fibrations and opfibrations

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Morphisms.FullyFaithful.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Morphisms.InternalStreetFibration.
Require Import UniMath.Bicategories.Morphisms.InternalStreetOpFibration.
Require Import UniMath.Bicategories.Morphisms.Properties.
Require Import UniMath.Bicategories.Morphisms.Properties.Projections.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayMapBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.CartesianPseudoFunctor.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Trivial.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayMapBicatToDispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.TrivialCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.CodomainCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.FibrationCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.OpFibrationCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.DisplayMapBicatCleaving.
Require Import UniMath.Bicategories.Limits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.Examples.BicatOfUnivCatsLimits.
Require Import UniMath.Bicategories.Limits.Examples.OpCellBicatLimits.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.

Local Open Scope cat.

(**
 1. Comprehension bicategories
 *)
Definition comprehension_bicat_structure
           (B : bicat)
  : UU
  := ∑ (D : disp_bicat B)
       (χ : disp_psfunctor D (cod_disp_bicat B) (id_psfunctor B)),
     global_cleaving D × global_cartesian_disp_psfunctor χ.

Definition make_comprehension_bicat_structure
           (B : bicat)
           (D : disp_bicat B)
           (χ : disp_psfunctor D (cod_disp_bicat B) (id_psfunctor B))
           (HD : global_cleaving D)
           (Hχ : global_cartesian_disp_psfunctor χ)
  : comprehension_bicat_structure B
  := D ,, χ ,, HD ,, Hχ.

(** Projections of a comprehension bicategory *)
Definition ty_of
           {B : bicat}
           (comp_B : comprehension_bicat_structure B)
  : disp_bicat B
  := pr1 comp_B.

Definition comp_of
           {B : bicat}
           (comp_B : comprehension_bicat_structure B)
  : disp_psfunctor (ty_of comp_B) (cod_disp_bicat B) (id_psfunctor B)
  := pr12 comp_B.

Definition ty_of_global_cleaving
           {B : bicat}
           (comp_B : comprehension_bicat_structure B)
  : global_cleaving (ty_of comp_B)
  := pr122 comp_B.

Definition comp_of_global_cartesian
           {B : bicat}
           (comp_B : comprehension_bicat_structure B)
  : global_cartesian_disp_psfunctor (comp_of comp_B)
  := pr222 comp_B.

(** Variances of comprehension bicategories *)
Definition is_covariant
           {B : bicat}
           (comp_B : comprehension_bicat_structure B)
  : UU
  := let D := ty_of comp_B in
     let χ := comp_of comp_B in
     local_opcleaving D
     × lwhisker_opcartesian D
     × rwhisker_opcartesian D
     × local_opcartesian_disp_psfunctor χ.

Definition is_contravariant
           {B : bicat}
           (comp_B : comprehension_bicat_structure B)
  : UU
  := let D := ty_of comp_B in
     let χ := comp_of comp_B in
     local_cleaving D
     × lwhisker_cartesian D
     × rwhisker_cartesian D
     × local_cartesian_disp_psfunctor χ.

Definition comprehension_bicat
  : UU
  := ∑ (B : bicat)
       (comp_B : comprehension_bicat_structure B),
     is_covariant comp_B.

Definition contravariant_comprehension_bicat
  : UU
  := ∑ (B : bicat)
       (comp_B : comprehension_bicat_structure B),
     is_contravariant comp_B.
(**
 2. The trivial comprehension bicategory
 *)
Section TrivialCompBicat.
  Context (B : bicat_with_binprod).

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

(**
 3. Locally groupoidal bicategories with pullbacks
 *)
Section PullbackComprehension.
  Context (B : bicat)
          (B_pb : has_pb B).

  Definition pb_comprehension
    : comprehension_bicat_structure B.
  Proof.
    use make_comprehension_bicat_structure.
    - exact (cod_disp_bicat B).
    - exact (disp_pseudo_id (cod_disp_bicat B)).
    - exact (cod_global_cleaving B B_pb).
    - exact (global_cartesian_id_psfunctor (cod_disp_bicat B)).
  Defined.

  Context (HB : locally_groupoid B).

  Definition locally_grpd_pb_comprehension_is_covariant
    : is_covariant pb_comprehension.
  Proof.
    repeat split.
    - exact (cod_local_opcleaving _ HB).
    - exact (cod_cleaving_lwhisker_opcartesian _ HB).
    - exact (cod_cleaving_rwhisker_opcartesian _ HB).
    - exact (local_opcartesian_id_psfunctor (cod_disp_bicat B)).
  Defined.

  Definition locally_grpd_pb_comprehension_is_contravariant
    : is_contravariant pb_comprehension.
  Proof.
    repeat split.
    - exact (cod_local_cleaving _ HB).
    - exact (cod_cleaving_lwhisker_cartesian _ HB).
    - exact (cod_cleaving_rwhisker_cartesian _ HB).
    - exact (local_cartesian_id_psfunctor (cod_disp_bicat B)).
  Defined.

  Definition locally_grpd_comprehension_bicat
    : comprehension_bicat
    := _ ,, _ ,, locally_grpd_pb_comprehension_is_covariant.

  Definition locally_grpd_contravariant_comprehension_bicat
    : contravariant_comprehension_bicat
    := _ ,, _ ,, locally_grpd_pb_comprehension_is_contravariant.
End PullbackComprehension.

(**
 4. The comprehension bicategory of fibrations
 *)
Definition cleaving_comprehension_data
  : disp_psfunctor_data
      disp_bicat_of_cleaving
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact (λ C D, total_univalent_category (pr1 D) ,, pr1_category _).
  - intros C₁ C₂ F D₁ D₂ FF.
    use make_disp_1cell_cod.
    + exact (total_functor (pr1 FF)).
    + use nat_iso_to_invertible_2cell.
      exact (total_functor_commute_iso (pr1 FF)).
  - intros C₁ C₂ F G α D₁ D₂ FF GG αα.
    use make_disp_2cell_cod.
    + exact (total_nat_trans (pr1 αα)).
    + abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  - intros C D.
    simple refine (_ ,, _).
    + use make_disp_2cell_cod.
      * exact (total_functor_identity (pr11 D)).
      * abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intros x ;
           cbn ;
           rewrite !id_left ;
           apply idpath).
    + use is_disp_invertible_2cell_cod.
      use is_nat_iso_to_is_invertible_2cell.
      intro x.
      apply identity_is_iso.
  - intros C₁ C₂ C₃ F G D₁ D₂ D₃ FF GG.
    simple refine (_ ,, _).
    + use make_disp_2cell_cod.
      * exact (total_functor_comp (pr1 FF) (pr1 GG)).
      * abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intros x ;
           cbn ;
           rewrite !id_left, !id_right ;
           apply functor_id).
    + use is_disp_invertible_2cell_cod.
      use is_nat_iso_to_is_invertible_2cell.
      intro x.
      apply identity_is_iso.
Defined.

Definition cleaving_comprehension_is_disp_psfunctor
  : is_disp_psfunctor
      disp_bicat_of_cleaving
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats)
      cleaving_comprehension_data.
Proof.
  repeat split ; intro ; intros ;
    (use subtypePath ; [ intro ; apply cellset_property | ]).
  - refine (_ @ !(transportb_cell_of_cod_over _ _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    apply idpath.
  - refine (_ @ !(transportb_cell_of_cod_over _ _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    apply idpath.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lunitor _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite functor_id, !id_right ;
         apply idpath).
    + rewrite !id_right_disp.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_runitor _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite !id_right ;
         apply idpath).
    + rewrite !id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - refine (_ @ !(transportb_cell_of_cod_over
                    (psfunctor_lassociator _ _ _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite functor_id, !id_right ;
         apply idpath).
    + rewrite !id_right_disp, !id_left_disp.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - refine (_ @ !(transportb_cell_of_cod_over
                    (psfunctor_lwhisker _ _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite !id_right, !id_left ;
         apply idpath).
    + rewrite !id_right_disp, !id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - refine (_ @ !(transportb_cell_of_cod_over
                    (psfunctor_rwhisker _ _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite !id_right, !id_left ;
         apply idpath).
    + rewrite !id_right_disp, !id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
Qed.

Definition cleaving_comprehension
  : disp_psfunctor
      disp_bicat_of_cleaving
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _).
  - exact cleaving_comprehension_data.
  - exact cleaving_comprehension_is_disp_psfunctor.
Defined.

Definition global_cartesian_cleaving_comprehension
  : global_cartesian_disp_psfunctor cleaving_comprehension.
Proof.
  use preserves_global_lifts_to_cartesian.
  - exact univalent_cat_is_univalent_2.
  - exact (cod_disp_univalent_2 _ univalent_cat_is_univalent_2).
  - exact cleaving_of_cleaving_global_cleaving.
  - intros C₁ C₂ F D₁.
    use is_pb_to_cartesian_1cell.
    apply reindexing_has_pb_ump.
    apply is_isofibration_from_is_fibration.
    exact (pr2 D₁).
Defined.

Section LocalCartesianFibration.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F₁ F₂ : C₁ --> C₂}
          (α : F₁ ==> F₂)
          {D₁ : disp_bicat_of_cleaving C₁}
          {D₂ : disp_bicat_of_cleaving C₂}
          {FF₁ : D₁ -->[ F₁ ] D₂}
          {FF₂ : D₁ -->[ F₂ ] D₂}
          (αα : disp_2cells α FF₁ FF₂)
          (Hαα : ∏ (x : C₁ : univalent_category)
                   (xx : (pr1 D₁ : disp_univalent_category _) x),
                 is_cartesian ((pr11 αα) x xx))
          (G : bicat_of_univ_cats
                 ⟦ total_univalent_category (pr1 D₁)
                   ,
                   total_univalent_category (pr1 D₂) ⟧)
          (γ : G ==> total_functor (pr1 FF₂))
          (δp : (G ∙ pr1_category (pr11 D₂) : bicat_of_univ_cats ⟦ _ , _ ⟧)
                ==>
                total_functor (pr1 FF₁) ∙ pr1_category (pr11 D₂))
          (q : post_whisker γ (pr1_category (pr11 D₂))
               =
               nat_trans_comp
                 _ _ _
                 δp
                 (post_whisker (total_nat_trans (pr1 αα)) (pr1_category _))).

  Definition local_cartesian_cleaving_lift_data
    : nat_trans_data
        (pr1 G)
        (total_functor (pr1 FF₁)).
  Proof.
    refine (λ x, pr1 δp x ,, _) ; cbn.
    refine (cartesian_factorisation (Hαα (pr1 x) (pr2 x)) _ _).
    exact (transportf
             (λ z, _ -->[ z ] _)
             (nat_trans_eq_pointwise q x)
             (pr2 (pr1 γ x))).
  Defined.

  Definition local_cartesian_cleaving_lift_is_nat_trans
    : is_nat_trans _ _ local_cartesian_cleaving_lift_data.
  Proof.
    intros x y f ; cbn.
    use total2_paths_f.
    - exact (nat_trans_ax δp x y f).
    - use (cartesian_factorisation_unique (Hαα (pr1 y) (pr2 y))).
      cbn.
      rewrite assoc_disp_var.
      rewrite mor_disp_transportf_postwhisker.
      rewrite assoc_disp_var.
      rewrite transport_f_f.
      rewrite cartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpaths.
        apply disp_nat_trans_ax.
      }
      unfold transportb.
      rewrite mor_disp_transportf_prewhisker.
      rewrite transport_f_f.
      rewrite assoc_disp.
      rewrite cartesian_factorisation_commutes.
      unfold transportb.
      rewrite mor_disp_transportf_postwhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        exact (fiber_paths (nat_trans_ax γ _ _ f)).
      }
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition local_cartesian_cleaving_lift
    : G ==> total_functor (pr1 FF₁).
  Proof.
    use make_nat_trans.
    - exact local_cartesian_cleaving_lift_data.
    - exact local_cartesian_cleaving_lift_is_nat_trans.
  Defined.

  Definition local_cartesian_cleaving_lift_over
    : local_cartesian_cleaving_lift ▹ _ = δp.
  Proof.
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    apply idpath.
  Qed.

  Definition local_cartesian_cleaving_lift_comm
    : local_cartesian_cleaving_lift • total_nat_trans (pr1 αα)
      =
      γ.
  Proof.
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    cbn.
    use total2_paths_f.
    - exact (!(nat_trans_eq_pointwise q x)).
    - cbn.
      rewrite cartesian_factorisation_commutes.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
  Qed.

  Definition local_cartesian_cleaving_lift_unique
    : isaprop
        (∑ δ,
         δ ▹ _ = δp
         ×
         δ • total_nat_trans (pr1 αα) = γ).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply cellset_property.
    }
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use total2_paths_f.
    - exact (nat_trans_eq_pointwise (pr12 φ₁) x
             @ !(nat_trans_eq_pointwise (pr12 φ₂) x)).
    - use (cartesian_factorisation_unique (Hαα (pr1 x) (pr2 x))).
      rewrite mor_disp_transportf_postwhisker.
      etrans.
      {
        apply maponpaths.
        exact (transportb_transpose_right
                 (fiber_paths (nat_trans_eq_pointwise (pr22 φ₁) x))).
      }
      refine (!_).
      etrans.
      {
        exact (transportb_transpose_right
                 (fiber_paths (nat_trans_eq_pointwise (pr22 φ₂) x))).
      }
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.
End LocalCartesianFibration.

Definition local_cartesian_cleaving_comprehension
  : local_cartesian_disp_psfunctor cleaving_comprehension.
Proof.
  intros C₁ C₂ F₁ F₂ α D₁ D₂ FF₁ FF₂ αα Hαα.
  apply is_cartesian_2cell_sfib_to_is_cartesian_2cell ; cbn.
  pose (cleaving_of_cleaving_cartesian_2cell_is_pointwise_cartesian _ Hαα) as p.
  intros G γ δp q.
  use iscontraprop1.
  - exact (local_cartesian_cleaving_lift_unique α αα p G γ δp).
  - simple refine (_ ,, _ ,, _).
    + exact (local_cartesian_cleaving_lift α αα p G γ δp q).
    + exact (local_cartesian_cleaving_lift_over α αα p G γ δp q).
    + exact (local_cartesian_cleaving_lift_comm α αα p G γ δp q).
Defined.

Definition cleaving_comprehension_bicat_structure
  : comprehension_bicat_structure bicat_of_univ_cats.
Proof.
  use make_comprehension_bicat_structure.
  - exact disp_bicat_of_cleaving.
  - exact cleaving_comprehension.
  - exact cleaving_of_cleaving_global_cleaving.
  - exact global_cartesian_cleaving_comprehension.
Defined.

Definition cleaving_comprehension_is_contravariant
  : is_contravariant cleaving_comprehension_bicat_structure.
Proof.
  repeat split.
  - exact cleaving_of_cleaving_local_cleaving.
  - exact cleaving_of_cleaving_lwhisker_cartesian.
  - exact cleaving_of_cleaving_rwhisker_cartesian.
  - exact local_cartesian_cleaving_comprehension.
Defined.

Definition cleaving_contravariant_comprehension_bicat
  : contravariant_comprehension_bicat
  := _ ,, _ ,, cleaving_comprehension_is_contravariant.

(**
 4. The comprehension bicategory of opfibrations
 *)
Definition opcleaving_comprehension_data
  : disp_psfunctor_data
      disp_bicat_of_opcleaving
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _).
  - exact (λ C D, total_univalent_category (pr1 D) ,, pr1_category _).
  - intros C₁ C₂ F D₁ D₂ FF.
    use make_disp_1cell_cod.
    + exact (total_functor (pr1 FF)).
    + use nat_iso_to_invertible_2cell.
      exact (total_functor_commute_iso (pr1 FF)).
  - intros C₁ C₂ F G α D₁ D₂ FF GG αα.
    use make_disp_2cell_cod.
    + exact (total_nat_trans (pr1 αα)).
    + abstract
        (use nat_trans_eq ; [ apply homset_property | ] ;
         intro x ; cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  - intros C D.
    simple refine (_ ,, _).
    + use make_disp_2cell_cod.
      * exact (total_functor_identity (pr11 D)).
      * abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intros x ;
           cbn ;
           rewrite !id_left ;
           apply idpath).
    + use is_disp_invertible_2cell_cod.
      use is_nat_iso_to_is_invertible_2cell.
      intro x.
      apply identity_is_iso.
  - intros C₁ C₂ C₃ F G D₁ D₂ D₃ FF GG.
    simple refine (_ ,, _).
    + use make_disp_2cell_cod.
      * exact (total_functor_comp (pr1 FF) (pr1 GG)).
      * abstract
          (use nat_trans_eq ; [ apply homset_property | ] ;
           intros x ;
           cbn ;
           rewrite !id_left, !id_right ;
           apply functor_id).
    + use is_disp_invertible_2cell_cod.
      use is_nat_iso_to_is_invertible_2cell.
      intro x.
      apply identity_is_iso.
Defined.

Definition opcleaving_comprehension_is_disp_psfunctor
  : is_disp_psfunctor
      disp_bicat_of_opcleaving
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats)
      opcleaving_comprehension_data.
Proof.
  repeat split ; intro ; intros ;
    (use subtypePath ; [ intro ; apply cellset_property | ]).
  - refine (_ @ !(transportb_cell_of_cod_over _ _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    apply idpath.
  - refine (_ @ !(transportb_cell_of_cod_over _ _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    apply idpath.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lunitor _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite functor_id, !id_right ;
         apply idpath).
    + rewrite !id_right_disp.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_runitor _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite !id_right ;
         apply idpath).
    + rewrite !id_right_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - refine (_ @ !(transportb_cell_of_cod_over
                    (psfunctor_lassociator _ _ _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite functor_id, !id_right ;
         apply idpath).
    + rewrite !id_right_disp, !id_left_disp.
      rewrite disp_functor_id.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - refine (_ @ !(transportb_cell_of_cod_over
                    (psfunctor_lwhisker _ _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite !id_right, !id_left ;
         apply idpath).
    + rewrite !id_right_disp, !id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  - refine (_ @ !(transportb_cell_of_cod_over
                    (psfunctor_rwhisker _ _ _) _)).
    apply nat_trans_eq ; [ intro ; apply homset_property | ].
    intro x ; cbn.
    use total2_paths_f ; cbn.
    + abstract
        (rewrite !id_right, !id_left ;
         apply idpath).
    + rewrite !id_right_disp, !id_left_disp.
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
Qed.

Definition opcleaving_comprehension
  : disp_psfunctor
      disp_bicat_of_opcleaving
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _).
  - exact opcleaving_comprehension_data.
  - exact opcleaving_comprehension_is_disp_psfunctor.
Defined.

Definition global_cartesian_opcleaving_comprehension
  : global_cartesian_disp_psfunctor opcleaving_comprehension.
Proof.
  use preserves_global_lifts_to_cartesian.
  - exact univalent_cat_is_univalent_2.
  - exact (cod_disp_univalent_2 _ univalent_cat_is_univalent_2).
  - exact opcleaving_global_cleaving.
  - intros C₁ C₂ F D₁.
    use is_pb_to_cartesian_1cell.
    apply reindexing_has_pb_ump.
    apply iso_cleaving_from_opcleaving.
    exact (pr2 D₁).
Defined.

Section LocalOpCartesianOpFibration.
  Context {C₁ C₂ : bicat_of_univ_cats}
          {F₁ F₂ : C₁ --> C₂}
          (α : F₁ ==> F₂)
          {D₁ : disp_bicat_of_opcleaving C₁}
          {D₂ : disp_bicat_of_opcleaving C₂}
          {FF₁ : D₁ -->[ F₁ ] D₂}
          {FF₂ : D₁ -->[ F₂ ] D₂}
          (αα : disp_2cells α FF₁ FF₂)
          (Hαα : ∏ (x : C₁ : univalent_category)
                   (xx : (pr1 D₁ : disp_univalent_category _) x),
                 is_opcartesian ((pr11 αα) x xx))
          (G : bicat_of_univ_cats
                 ⟦ total_univalent_category (pr1 D₁)
                   ,
                   total_univalent_category (pr1 D₂) ⟧)
          (tot_FF₁ := (total_functor (pr1 FF₁)
                       : bicat_of_univ_cats
                           ⟦ total_univalent_category (pr1 D₁)
                             ,
                             total_univalent_category (pr1 D₂) ⟧))
          (tot_FF₂ := (total_functor (pr1 FF₂)
                       : bicat_of_univ_cats
                           ⟦ total_univalent_category (pr1 D₁)
                             ,
                             total_univalent_category (pr1 D₂) ⟧))
          (tot_αα := total_nat_trans (pr1 αα) : tot_FF₁ ==> tot_FF₂)
          (γ : tot_FF₁ ==> G)
          (δp : tot_FF₂ · pr1_category _ ==> G · pr1_category _)
          (q : post_whisker γ (pr1_category (pr11 D₂))
               =
               nat_trans_comp
                 _ _ _
                 (post_whisker (total_nat_trans (pr1 αα)) (pr1_category _))
                 δp).

  Definition local_opcartesian_opcleaving_lift_data
    : nat_trans_data (pr1 tot_FF₂) (pr1 G).
  Proof.
    refine (λ x, pr1 δp x ,, _) ; cbn.
    refine (opcartesian_factorisation (Hαα (pr1 x) (pr2 x)) _ _).
    exact (transportf
             (λ z, _ -->[ z ] _)
             (nat_trans_eq_pointwise q x)
             (pr2 (pr1 γ x))).
  Defined.

  Definition local_opcartesian_opcleaving_lift_is_nat_trans
    : is_nat_trans _ _ local_opcartesian_opcleaving_lift_data.
  Proof.
    intros x y f ; cbn.
    use total2_paths_f.
    - exact (nat_trans_ax δp x y f).
    - use (opcartesian_factorisation_unique (Hαα (pr1 x) (pr2 x))).
      cbn.
      rewrite assoc_disp.
      rewrite mor_disp_transportf_prewhisker.
      rewrite assoc_disp.
      unfold transportb.
      rewrite transport_f_f.
      rewrite opcartesian_factorisation_commutes.
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        refine (!_).
        exact (transportf_transpose_left (disp_nat_trans_ax (pr1 αα) (pr2 f))).
      }
      rewrite mor_disp_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite assoc_disp_var.
      rewrite opcartesian_factorisation_commutes.
      rewrite mor_disp_transportf_prewhisker.
      rewrite !transport_f_f.
      etrans.
      {
        apply maponpaths.
        exact (transportb_transpose_right (fiber_paths (nat_trans_ax γ _ _ f))).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.

  Definition local_opcartesian_opcleaving_lift
    : tot_FF₂ ==> G.
  Proof.
    use make_nat_trans.
    - exact local_opcartesian_opcleaving_lift_data.
    - exact local_opcartesian_opcleaving_lift_is_nat_trans.
  Defined.

  Definition local_opcartesian_opcleaving_lift_over
    : local_opcartesian_opcleaving_lift ▹ _ = δp.
  Proof.
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    apply idpath.
  Qed.

  Definition local_opcartesian_opcleaving_lift_comm
    : tot_αα • local_opcartesian_opcleaving_lift
      =
      γ.
  Proof.
    use nat_trans_eq ; [ apply homset_property | ].
    intro x.
    cbn.
    use total2_paths_f.
    - exact (!(nat_trans_eq_pointwise q x)).
    - cbn.
      rewrite opcartesian_factorisation_commutes.
      rewrite transport_f_f.
      apply transportf_set.
      apply homset_property.
  Qed.

  Definition local_opcartesian_opcleaving_lift_unique
    : isaprop
        (∑ δ,
         δ ▹ _ = δp
         ×
         tot_αα • δ = γ).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply cellset_property.
    }
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro x.
    use total2_paths_f.
    - exact (nat_trans_eq_pointwise (pr12 φ₁) x
             @ !(nat_trans_eq_pointwise (pr12 φ₂) x)).
    - use (opcartesian_factorisation_unique (Hαα (pr1 x) (pr2 x))).
      rewrite mor_disp_transportf_prewhisker.
      etrans.
      {
        apply maponpaths.
        exact (transportb_transpose_right
                 (fiber_paths (nat_trans_eq_pointwise (pr22 φ₁) x))).
      }
      refine (!_).
      etrans.
      {
        exact (transportb_transpose_right
                 (fiber_paths (nat_trans_eq_pointwise (pr22 φ₂) x))).
      }
      unfold transportb.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply homset_property.
  Qed.
End LocalOpCartesianOpFibration.

Definition local_opcartesian_opcleaving_comprehension
  : local_opcartesian_disp_psfunctor opcleaving_comprehension.
Proof.
  intros C₁ C₂ F₁ F₂ α D₁ D₂ FF₁ FF₂ αα Hαα.
  apply is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell ; cbn.
  pose (opcleaving_of_opcleaving_opcartesian_2cell_is_pointwise_opcartesian _ Hαα) as p.
  intros G γ δp q.
  use iscontraprop1.
  - exact (local_opcartesian_opcleaving_lift_unique α αα p G γ δp).
  - simple refine (_ ,, _ ,, _).
    + exact (local_opcartesian_opcleaving_lift α αα p G γ δp q).
    + exact (local_opcartesian_opcleaving_lift_over α αα p G γ δp q).
    + exact (local_opcartesian_opcleaving_lift_comm α αα p G γ δp q).
Defined.

Definition opcleaving_comprehension_bicat_structure
  : comprehension_bicat_structure bicat_of_univ_cats.
Proof.
  use make_comprehension_bicat_structure.
  - exact disp_bicat_of_opcleaving.
  - exact opcleaving_comprehension.
  - exact opcleaving_global_cleaving.
  - exact global_cartesian_opcleaving_comprehension.
Defined.

Definition opcleaving_comprehension_is_covariant
  : is_covariant opcleaving_comprehension_bicat_structure.
Proof.
  repeat split.
  - exact cleaving_of_opcleaving_local_opcleaving.
  - exact cleaving_of_opcleaving_lwhisker_opcartesian.
  - exact cleaving_of_opcleaving_rwhisker_opcartesian.
  - exact local_opcartesian_opcleaving_comprehension.
Defined.

Definition cleaving_comprehension_bicat
  : comprehension_bicat
  := _ ,, _ ,, opcleaving_comprehension_is_covariant.

(**
 6. The comprehension bicategory of a display map bicategory
 *)
Section DispMapBicatToCompBicat.
  Context {B : bicat}
          (D : disp_map_bicat B)
          (HB : is_univalent_2 B).

  Let DD : disp_bicat B := disp_map_bicat_to_disp_bicat D.

  Definition disp_map_bicat_comprehension_data
    : disp_psfunctor_data DD (cod_disp_bicat B) (id_psfunctor B).
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _).
    - exact (λ x hx, pr1 hx ,, pr12 hx).
    - exact (λ x y f hx hy hf, pr1 hf ,, pr22 hf).
    - exact (λ x y f g α hx hy hf hg hα, hα).
    - simple refine (λ x hx, _ ,, _).
      + use make_disp_2cell_cod.
        * exact (id₂ _).
        * abstract
            (unfold coherent_homot ; cbn ;
             rewrite id2_rwhisker, id2_right ;
             rewrite lwhisker_id2, id2_left ;
             apply idpath).
      + use is_disp_invertible_2cell_cod ; simpl.
        is_iso.
    - simple refine (λ x y z f g hx hy hz hf hg, _ ,, _).
      + use make_disp_2cell_cod.
        * exact (id₂ _).
        * abstract
            (unfold coherent_homot ; cbn ;
             rewrite id2_rwhisker, id2_right ;
             rewrite lwhisker_id2, id2_left ;
             rewrite !vassocl ;
             apply idpath).
      + use is_disp_invertible_2cell_cod ; simpl.
        is_iso.
  Defined.

  Definition disp_map_bicat_comprehension_is_disp_psfunctor
    : is_disp_psfunctor _ _ _ disp_map_bicat_comprehension_data.
  Proof.
    repeat split ; intro ; intros ;
      (use subtypePath ; [ intro ; apply cellset_property | ]).
    - refine (_ @ !(transportb_cell_of_cod_over _ _)) ; cbn.
      apply idpath.
    - refine (_ @ !(transportb_cell_of_cod_over _ _)) ; cbn.
      apply idpath.
    - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lunitor _ _) _)) ; cbn.
      rewrite id2_rwhisker, !id2_left.
      apply idpath.
    - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_runitor _ _) _)) ; cbn.
      rewrite lwhisker_id2, !id2_left.
      apply idpath.
    - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lassociator _ _ _ _) _)) ; cbn.
      rewrite id2_rwhisker, lwhisker_id2.
      rewrite !id2_left, !id2_right.
      apply idpath.
    - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lwhisker _ _ _) _)) ; cbn.
      rewrite !id2_left, id2_right.
      apply idpath.
    - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_rwhisker _ _ _) _)) ; cbn.
      rewrite !id2_left, id2_right.
      apply idpath.
  Qed.

  Definition disp_map_bicat_comprehension
    : disp_psfunctor DD (cod_disp_bicat B) (id_psfunctor B)
    := disp_map_bicat_comprehension_data
       ,,
       disp_map_bicat_comprehension_is_disp_psfunctor.

  Definition global_cartesian_disp_map_bicat_comprehension
    : global_cartesian_disp_psfunctor disp_map_bicat_comprehension.
  Proof.
    use preserves_global_lifts_to_cartesian.
    - exact HB.
    - exact (cod_disp_univalent_2 _ HB).
    - exact (global_cleaving_of_disp_map_bicat D).
    - intros x y f hy.
      use is_pb_to_cartesian_1cell.
      exact (mirror_has_pb_ump
               (pb_of_pred_ob_has_pb_ump D (pr12 hy) f (pr22 hy))).
  Defined.

  Definition disp_map_bicat_to_comp_bicat
    : comprehension_bicat_structure B.
  Proof.
    use make_comprehension_bicat_structure.
    - exact DD.
    - exact disp_map_bicat_comprehension.
    - exact (global_cleaving_of_disp_map_bicat D).
    - exact global_cartesian_disp_map_bicat_comprehension.
  Defined.

  Definition disp_map_bicat_to_comp_bicat_local_opcartesian
             (HD : is_covariant_disp_map_bicat D)
    : local_opcartesian_disp_psfunctor
        (comp_of disp_map_bicat_to_comp_bicat).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? H.
    apply is_opcartesian_2cell_sopfib_to_is_opcartesian_2cell.
    cbn.
    apply (disp_map_is_opcartesian_2cell_to_is_opcartesian_2cell_sopfib _ HD).
    exact H.
  Defined.

  Definition is_covariant_disp_map_bicat_to_comp_bicat
             (HD : is_covariant_disp_map_bicat D)
    : is_covariant disp_map_bicat_to_comp_bicat.
  Proof.
    repeat split.
    - exact (local_opcleaving_of_disp_map_bicat _ HD).
    - exact (lwhisker_opcartesian_disp_map_bicat _ HD).
    - exact (rwhisker_opcartesian_disp_map_bicat _ HD).
    - exact (disp_map_bicat_to_comp_bicat_local_opcartesian HD).
  Defined.

  Definition disp_map_bicat_to_comp_bicat_local_cartesian
             (HD : is_contravariant_disp_map_bicat D)
    : local_cartesian_disp_psfunctor
        (comp_of disp_map_bicat_to_comp_bicat).
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? H.
    apply is_cartesian_2cell_sfib_to_is_cartesian_2cell.
    cbn.
    apply (disp_map_is_cartesian_2cell_to_is_cartesian_2cell_sfib _ HD).
    exact H.
  Defined.

  Definition is_contravariant_disp_map_bicat_to_comp_bicat
             (HD : is_contravariant_disp_map_bicat D)
    : is_contravariant disp_map_bicat_to_comp_bicat.
  Proof.
    repeat split.
    - exact (local_cleaving_of_disp_map_bicat _ HD).
    - exact (lwhisker_cartesian_disp_map_bicat _ HD).
    - exact (rwhisker_cartesian_disp_map_bicat _ HD).
    - exact (disp_map_bicat_to_comp_bicat_local_cartesian HD).
  Defined.

  Definition disp_map_bicat_comprehension_bicat
             (HD : is_covariant_disp_map_bicat D)
    : comprehension_bicat
    := _ ,, _ ,, is_covariant_disp_map_bicat_to_comp_bicat HD.

  Definition disp_map_bicat_contravariant_comprehension_bicat
             (HD : is_contravariant_disp_map_bicat D)
    : contravariant_comprehension_bicat
    := _ ,, _ ,, is_contravariant_disp_map_bicat_to_comp_bicat HD.
End DispMapBicatToCompBicat.

(**
 7. Internal Street fibrations and opfibrations
 *)
Definition internal_sfib_comprehension_bicat_structure
           (B : bicat_with_pb)
           (HB : is_univalent_2 B)
  : comprehension_bicat_structure B
  := disp_map_bicat_to_comp_bicat (sfib_disp_map_bicat B) HB.

Definition is_contravariant_internal_sfib_comprehension_bicat_structure
           (B : bicat_with_pb)
           (HB : is_univalent_2 B)
  : is_contravariant (internal_sfib_comprehension_bicat_structure B HB).
Proof.
  use is_contravariant_disp_map_bicat_to_comp_bicat.
  apply sfib_disp_map_bicat_is_contravariant.
Defined.

Definition internal_sfib_contravariant_comprehension_bicat
           (B : bicat_with_pb)
           (HB : is_univalent_2 B)
  : contravariant_comprehension_bicat
  := _ ,, _ ,, is_contravariant_internal_sfib_comprehension_bicat_structure B HB.

Definition internal_sopfib_comprehension_bicat_structure
           (B : bicat_with_pb)
           (HB : is_univalent_2 B)
  : comprehension_bicat_structure B
  := disp_map_bicat_to_comp_bicat (sopfib_disp_map_bicat B) HB.

Definition is_covariant_internal_sopfib_comprehension_bicat_structure
           (B : bicat_with_pb)
           (HB : is_univalent_2 B)
  : is_covariant (internal_sopfib_comprehension_bicat_structure B HB).
Proof.
  use is_covariant_disp_map_bicat_to_comp_bicat.
  apply sopfib_disp_map_bicat_is_covariant.
Defined.

Definition internal_sopfib_comprehension_bicat
           (B : bicat_with_pb)
           (HB : is_univalent_2 B)
  : comprehension_bicat
  := _ ,, _ ,, is_covariant_internal_sopfib_comprehension_bicat_structure B HB.
