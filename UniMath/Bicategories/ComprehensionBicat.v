(*******************************************************************

 Comprehension bicategories

 In this file we define comprehension bicategories and we
 construct examples of them.

 1. Comprehension bicategories
 2. The trivial comprehension bicategory
 3. Locally groupoidal bicategories with pullbacks
 4. The comprehension bicategory of fibrations
 5. The comprehension bicategory of opfibrations

 *******************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.StreetFibration.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.FullyFaithful.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.CleavingOfBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Trivial.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispBicatOfDispCats.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Codomain.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Sigma.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.TrivialCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.CodomainCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.FibrationCleaving.
Require Import UniMath.Bicategories.DisplayedBicats.ExamplesOfCleavings.OpFibrationCleaving.
Require Import UniMath.Bicategories.Colimits.Products.
Import Products.Notations.
Require Import UniMath.Bicategories.Colimits.Pullback.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.

Local Open Scope cat.

(**
 1. Comprehension bicategories
 *)
Definition comprehension_bicat
           (B : bicat)
  : UU
  := ∑ (D : disp_bicat B)
       (χ : disp_psfunctor D (cod_disp_bicat B) (id_psfunctor B)),
     global_cleaving D × global_cartesian_disp_psfunctor χ.

Definition make_comprehension_bicat
           (B : bicat)
           (D : disp_bicat B)
           (χ : disp_psfunctor D (cod_disp_bicat B) (id_psfunctor B))
           (HD : global_cleaving D)
           (Hχ : global_cartesian_disp_psfunctor χ)
  : comprehension_bicat B
  := D ,, χ ,, HD ,, Hχ.

(** Projections of a comprehension bicategory *)
Definition ty_of
           {B : bicat}
           (comp_B : comprehension_bicat B)
  : disp_bicat B
  := pr1 comp_B.

Definition comp_of
           {B : bicat}
           (comp_B : comprehension_bicat B)
  : disp_psfunctor (ty_of comp_B) (cod_disp_bicat B) (id_psfunctor B)
  := pr12 comp_B.

Definition ty_of_global_cleaving
           {B : bicat}
           (comp_B : comprehension_bicat B)
  : global_cleaving (ty_of comp_B)
  := pr122 comp_B.

Definition comp_of_global_cartesian
           {B : bicat}
           (comp_B : comprehension_bicat B)
  : global_cartesian_disp_psfunctor (comp_of comp_B)
  := pr222 comp_B.

(** Variances of comprehension bicategories *)
Definition is_covariant
           {B : bicat}
           (comp_B : comprehension_bicat B)
  : UU
  := let D := ty_of comp_B in
     let χ := comp_of comp_B in
     local_opcleaving D
     × lwhisker_opcartesian D
     × rwhisker_opcartesian D
     × local_opcartesian_disp_psfunctor χ.

Definition is_contravariant
           {B : bicat}
           (comp_B : comprehension_bicat B)
  : UU
  := let D := ty_of comp_B in
     let χ := comp_of comp_B in
     local_cleaving D
     × lwhisker_cartesian D
     × rwhisker_cartesian D
     × local_cartesian_disp_psfunctor χ.

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
  - refine (_ @ !(transportb_cell_of_cod_over _ _)) ; cbn.
    apply pair_2cell_id_id.
  - refine (_ @ !(transportb_cell_of_cod_over _ _)) ; cbn.
    apply pair_2cell_comp.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lunitor _ _) _)) ; cbn.
    (*use binprod_ump_2cell_unique_alt.
    + apply (pr2 B).
    + refine (!_).
      rewrite <- !rwhisker_vcomp.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply binprod_ump_2cell_pr1.
      }
      rewrite !vassocl.
      Locate "⊗₂".
      Search pair_2cell.
        apply maponpaths_2.
        apply binprod_ump_2cell_pr1.
      cbn.
      rewrite binprod_ump_2cell_pr1.
      cbn.*)
    admit.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_runitor _ _) _)) ; cbn.
    admit.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lassociator _ _ _ _) _)) ; cbn.
    admit.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_lwhisker _ _ _) _)) ; cbn.
    admit.
  - refine (_ @ !(transportb_cell_of_cod_over (psfunctor_rwhisker _ _ _) _)) ; cbn.
    admit.
  Admitted.

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

      Definition adj_equiv_to_pb_ump_1_pb_1cell
        : pb_1cell q cone.
      Proof.
        use make_pb_1cell.
        - exact ⟨ pb_cone_pr1 q , pb_cone_pr2 q · π₂ · r ⟩.
        - apply prod_1cell_pr1.
        - use make_invertible_2cell.
          + use binprod_ump_2cell.
            * exact (pr2 (binprod_of B b₂ c₂)).
            * exact (rassociator _ _ _
                     • (_ ◃ pair_1cell_pr1 _ _ _)
                     • lassociator _ _ _
                     • (prod_1cell_pr1 _ _ _ ▹ _)
                     • pb_cone_cell _).
            * exact (rassociator _ _ _
                     • (_ ◃ pair_1cell_pr2 _ _ _)
                     • lassociator _ _ _
                     • (prod_1cell_pr2 _ _ _ ▹ _)
                     • rassociator _ _ _
                     • (_ ◃ ε)
                     • runitor _).
          + use binprod_ump_2cell_invertible.
            * is_iso.
              ** apply pair_1cell_pr1.
              ** apply prod_1cell_pr1.
              ** apply pb_cone_cell.
            * is_iso.
              ** apply pair_1cell_pr2.
              ** apply prod_1cell_pr2.
              ** apply ε.
        - cbn.
          admit.
      Admitted.
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
        := rinvunitor _
           • (_ ◃ η)
           • rassociator _ _ _
           • (_ ◃ (lassociator _ _ _
                   • ((pair_1cell_pr2 B f l)^-1 ▹ _)))
           • lassociator _ _ _
           • (lassociator _ _ _ • (β ▹ _) ▹ _)
           • rassociator _ _ _
           • rassociator _ _ _
           • (_ ◃ (lassociator _ _ _
                   • (pair_1cell_pr2 B f l ▹ r)
                   • rassociator _ _ _
                   • (_ ◃ η^-1)
                   • runitor _)).

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
        - unfold φπ₂.
          rewrite !vassocl.
          admit.
        - exact (pr12 ζ₂).
        - admit.
      Admitted.

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
          admit.
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
      Admitted.
    End AdjEquivToUMP2.

    Definition adj_equiv_to_pb_ump_2
      : pb_ump_2 cone.
    Proof.
      intros q φ ψ α β p.
      use iscontraprop1.
      - exact (adj_equiv_to_pb_ump_2_unique α β p).
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
  Admitted.

  Definition local_opcartesian_trivial_comprehension
    : local_opcartesian_disp_psfunctor trivial_comprehension.
  Proof.
    intros b₁ b₂ f₁ f₂ α c₁ c₂ g₁ g₂ β Hβ ; cbn in *.
  Admitted.

  Definition trivial_comprehension_bicat
    : comprehension_bicat B.
  Proof.
    use make_comprehension_bicat.
    - exact (trivial_displayed_bicat B B).
    - exact trivial_comprehension.
    - exact (trivial_cleaving_of_bicats B B).
    - exact global_cartesian_trivial_comprehension.
  Defined.

  Definition trivial_comprehension_is_covariant
    : is_covariant trivial_comprehension_bicat.
  Proof.
    repeat split.
    - exact (trivial_local_opcleaving B B).
    - exact (trivial_lwhisker_opcartesian B B).
    - exact (trivial_rwhisker_opcartesian B B).
    - exact local_opcartesian_trivial_comprehension.
  Defined.

  Definition trivial_comprehension_is_contravariant
    : is_contravariant trivial_comprehension_bicat.
  Proof.
    repeat split.
    - exact (trivial_local_cleaving B B).
    - exact (trivial_lwhisker_cartesian B B).
    - exact (trivial_rwhisker_cartesian B B).
    - exact local_cartesian_trivial_comprehension.
  Defined.
End TrivialCompBicat.

(**
 3. Locally groupoidal bicategories with pullbacks
 *)
Section PullbackComprehension.
  Context (B : bicat)
          (B_pb : has_pb B).

  Definition pb_comprehension
    : comprehension_bicat B.
  Proof.
    use make_comprehension_bicat.
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
End PullbackComprehension.

(**
 4. The comprehension bicategory of fibrations
 *)

(**********************************************************
 **********************************************************
 MOVE
 **********************************************************
 **********************************************************)
Definition total_functor_commute
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           (FF : disp_functor F D₁ D₂)
  : pr1_category D₁ ∙ F ⟹ total_functor FF ∙ pr1_category D₂.
Proof.
  use make_nat_trans.
  - exact (λ _, identity _).
  - abstract
      (intros ? ? ? ;
       cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition total_functor_commute_iso
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           (FF : disp_functor F D₁ D₂)
  : nat_iso
      (pr1_category D₁ ∙ F)
      (total_functor FF ∙ pr1_category D₂).
Proof.
  use make_nat_iso.
  * exact (total_functor_commute FF).
  * intro.
    apply identity_is_iso.
Defined.

Definition total_nat_trans
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           {τ : F ⟹ G}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           {FF : disp_functor F D₁ D₂}
           {GG : disp_functor G D₁ D₂}
           (ττ : disp_nat_trans τ FF GG)
  : nat_trans (total_functor FF) (total_functor GG).
Proof.
  use make_nat_trans.
  - exact (λ x, τ (pr1 x) ,, ττ (pr1 x) (pr2 x)).
  - abstract
      (intros x y f ; cbn ;
       use total2_paths_b ;
       [ exact (nat_trans_ax τ _ _ (pr1 f))
       | exact (disp_nat_trans_ax ττ (pr2 f))]).
Defined.

Definition total_functor_identity
           {C : category}
           (D : disp_cat C)
  : functor_identity (total_category D)
    ⟹
    total_functor (disp_functor_identity D).
Proof.
  use make_nat_trans.
  - exact (λ _, identity _).
  - abstract
      (intros ? ? ? ; simpl ;
       refine (@id_right (total_category _) _ _ _ @ _) ;
       exact (!(@id_left (total_category _) _ _ _))).
Defined.

Definition total_functor_comp
           {C₁ C₂ C₃ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {D₁ : disp_cat C₁}
           {D₂ : disp_cat C₂}
           {D₃ : disp_cat C₃}
           (FF : disp_functor F D₁ D₂)
           (GG : disp_functor G D₂ D₃)
  : total_functor FF ∙ total_functor GG
    ⟹
    total_functor (disp_functor_composite FF GG).
Proof.
  use make_nat_trans.
  - exact (λ _, identity _).
  - abstract
      (intros x y f ;
       refine (@id_right (total_category _) _ _ _ @ _) ;
       exact (!(@id_left (total_category _) _ _ _))).
Defined.

(**********************************************************
 **********************************************************
 END MOVE
 **********************************************************
 **********************************************************)

Definition fibration_comprehension_data
  : disp_psfunctor_data
      disp_bicat_of_fibs
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

Definition fibration_comprehension_is_disp_psfunctor
  : is_disp_psfunctor
      disp_bicat_of_fibs
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats)
      fibration_comprehension_data.
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

Definition fibration_comprehension
  : disp_psfunctor
      disp_bicat_of_fibs
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _).
  - exact fibration_comprehension_data.
  - exact fibration_comprehension_is_disp_psfunctor.
Defined.

Definition global_cartesian_fibration_comprehension
  : global_cartesian_disp_psfunctor fibration_comprehension.
Proof.
Admitted.

Definition local_cartesian_fibration_comprehension
  : local_cartesian_disp_psfunctor fibration_comprehension.
Proof.
Admitted.

Definition fibration_comprehension_bicat
  : comprehension_bicat bicat_of_univ_cats.
Proof.
  use make_comprehension_bicat.
  - exact disp_bicat_of_fibs.
  - exact fibration_comprehension.
  - exact cleaving_of_fibs.
  - exact global_cartesian_fibration_comprehension.
Defined.

Definition fibration_comprehension_is_contravariant
  : is_contravariant fibration_comprehension_bicat.
Proof.
  repeat split.
  - exact cleaving_of_fibs_local_cleaving.
  - exact cleaving_of_fibs_lwhisker_cartesian.
  - exact cleaving_of_fibs_rwhisker_cartesian.
  - exact local_cartesian_fibration_comprehension.
Defined.

(**
 4. The comprehension bicategory of opfibrations
 *)
Definition opfibration_comprehension_data
  : disp_psfunctor_data
      disp_bicat_of_opfibs
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

Definition opfibration_comprehension_is_disp_psfunctor
  : is_disp_psfunctor
      disp_bicat_of_opfibs
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats)
      opfibration_comprehension_data.
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

Definition opfibration_comprehension
  : disp_psfunctor
      disp_bicat_of_opfibs
      (cod_disp_bicat bicat_of_univ_cats)
      (id_psfunctor bicat_of_univ_cats).
Proof.
  simple refine (_ ,, _).
  - exact opfibration_comprehension_data.
  - exact opfibration_comprehension_is_disp_psfunctor.
Defined.

Definition global_cartesian_opfibration_comprehension
  : global_cartesian_disp_psfunctor opfibration_comprehension.
Proof.
Admitted.

Definition local_opcartesian_opfibration_comprehension
  : local_opcartesian_disp_psfunctor opfibration_comprehension.
Proof.
Admitted.

Definition opfibration_comprehension_bicat
  : comprehension_bicat bicat_of_univ_cats.
Proof.
  use make_comprehension_bicat.
  - exact disp_bicat_of_opfibs.
  - exact opfibration_comprehension.
  - exact opfibs_global_cleaving.
  - exact global_cartesian_opfibration_comprehension.
Defined.

Definition opfibration_comprehension_is_contravariant
  : is_covariant opfibration_comprehension_bicat.
Proof.
  repeat split.
  - exact cleaving_of_opfibs_local_opcleaving.
  - exact cleaving_of_opfibs_lwhisker_opcartesian.
  - exact cleaving_of_opfibs_rwhisker_opcartesian.
  - exact local_opcartesian_opfibration_comprehension.
Defined.
