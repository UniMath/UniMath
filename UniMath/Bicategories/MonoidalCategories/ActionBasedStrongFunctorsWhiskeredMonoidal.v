(** shows that action-based strong functors can be perceived as strong monoidal functors from the monoidal category that is acting on the underlying categories to a suitable monoidal category

This means that the requirement on strength is that it behaves as a ``homomorphism'' w.r.t. the
monoidal structures. More precisely, we construct transformations in both directions between parameterized distributivity (in a slightly massaged form to accommodate reasoning through bicategories) and displayed sections that are a formalization-friendly form of strong monoidal functors that are right inverses of the projection from the target displayed category. The result makes use of displayed monoidal categories.

The non-monoidal basic situation is developed before.

Author: Ralph Matthes 2021, 2022

 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalSectionsWhiskered.
Require Import UniMath.Bicategories.MonoidalCategories.EndofunctorsWhiskeredMonoidal.
Require Import UniMath.Bicategories.MonoidalCategories.Actions.
Require Import UniMath.Bicategories.MonoidalCategories.ActionBasedStrength.
Require Import UniMath.Bicategories.MonoidalCategories.WhiskeredMonoidalFromBicategory.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Import Bicat.Notations.
Import BifunctorNotations.
Import DisplayedBifunctorNotations.

Local Open Scope cat.

Section Upstream.
  (** this section has nothing to do with monoidal categories but is dictated by the aims of this file *)

  Context {C A A' : category}.

  Context (H H' : C ⟶ [A, A']).

  Definition trafotarget_disp_cat_ob_mor: disp_cat_ob_mor C.
  Proof.
    use make_disp_cat_ob_mor.
    - intro c. exact ([A, A']⟦(H c : A ⟶ A'), (H' c : A ⟶ A')⟧).
    - intros c c' α β f.
      exact (α · (# H' f) = (# H f) · β).
  Defined.

  Lemma trafotarget_disp_cat_id_comp: disp_cat_id_comp C trafotarget_disp_cat_ob_mor.
  Proof.
    split.
    - intros c α.
      red. unfold trafotarget_disp_cat_ob_mor, make_disp_cat_ob_mor. hnf.
      do 2 rewrite functor_id.
      rewrite id_left. apply id_right.
    - intros c1 c2 c3 f g α1 α2 α3 Hypf Hypg.
      red. red in Hypf, Hypg.
      unfold trafotarget_disp_cat_ob_mor, make_disp_cat_ob_mor in Hypf, Hypg |- *.
      hnf in Hypf, Hypg |- *.
      do 2 rewrite functor_comp.
      rewrite assoc.
      rewrite Hypf.
      rewrite <- assoc.
      rewrite Hypg.
      apply assoc.
   Qed.

  Definition trafotarget_disp_cat_data: disp_cat_data C :=
    trafotarget_disp_cat_ob_mor ,, trafotarget_disp_cat_id_comp.

  Lemma trafotarget_disp_cells_isaprop (x y : C) (f : C ⟦ x, y ⟧)
        (xx : trafotarget_disp_cat_data x) (yy : trafotarget_disp_cat_data y):
    isaprop (xx -->[ f] yy).
  Proof.
    intros Hyp Hyp'.
    apply (functor_category_has_homsets _ _).
  Qed.

  Lemma trafotarget_disp_cat_axioms: disp_cat_axioms C trafotarget_disp_cat_data.
  Proof.
    repeat split; intros; try apply trafotarget_disp_cells_isaprop.
    apply isasetaprop.
    apply trafotarget_disp_cells_isaprop.
  Qed.

  Definition trafotarget_disp: disp_cat C := trafotarget_disp_cat_data ,, trafotarget_disp_cat_axioms.

  Definition trafotarget_cat: category := total_category trafotarget_disp.

  Definition forget_from_trafotarget: trafotarget_cat ⟶ C := pr1_category trafotarget_disp.

  Section TheEquivalence.

    (** a naive specification of the target of the bijection - we need to limit the equality to [functor_data] for the elementary definition *)
    Definition trafotarget_with_eq: UU := ∑ N: C ⟶ trafotarget_cat,
      functor_data_from_functor _ _ (functor_composite N forget_from_trafotarget) =
        functor_data_from_functor _ _ (functor_identity C).

    (** a "pedestrian" definition *)
    Definition nat_trafo_to_functor (η: H ⟹ H'): C ⟶ trafotarget_cat.
    Proof.
      use make_functor.
      - use make_functor_data.
        + intro c.
          exact (c ,, η c).
        + intros c c' f.
          exists f.
          red. unfold trafotarget_disp. hnf.
          apply pathsinv0, nat_trans_ax.
      - split; red.
        + intro c.
          use total2_paths_f.
          * cbn. apply idpath.
          * apply (functor_category_has_homsets _ _).
        + intros c1 c2 c3 f f'.
          use total2_paths_f.
          * cbn. apply idpath.
          * apply (functor_category_has_homsets _ _).
    Defined.

    (** an immediate consequence *)
    Definition nat_trafo_to_functor_with_eq (η: H ⟹ H'): trafotarget_with_eq.
    Proof.
      exists (nat_trafo_to_functor η).
      apply idpath.
    Defined.

    (** we can also use the infrastructure of displayed categories *)
    Definition nat_trafo_to_section (η: H ⟹ H'):
      @section_disp C trafotarget_disp.
    Proof.
      use tpair.
      - use tpair.
        + intro c. exact (η c).
        + intros c c' f.
          red. unfold trafotarget_disp. hnf.
          apply pathsinv0, nat_trans_ax.
      - split.
        + intro c.
          apply (functor_category_has_homsets _ _).
        + intros c1 c2 c3 f f'.
          apply (functor_category_has_homsets _ _).
    Defined.

    Definition nat_trafo_to_functor_through_section (η: H ⟹ H'): C ⟶ trafotarget_cat :=
      @section_functor C trafotarget_disp (nat_trafo_to_section η).

    Definition nat_trafo_to_functor_through_section_cor (η: H ⟹ H'):
      functor_composite (nat_trafo_to_functor_through_section η) forget_from_trafotarget = functor_identity C.
    Proof.
      apply from_section_functor.
    Defined.

    (** the immediate consequence needs to weaken this strong information *)
    Definition nat_trafo_to_functor_through_section_with_eq (η: H ⟹ H'): trafotarget_with_eq.
    Proof.
      exists (nat_trafo_to_functor_through_section η).
      (* show_id_type. *)
      apply (maponpaths pr1 (nat_trafo_to_functor_through_section_cor η)).
    Defined.

    (** the backwards direction essentially uses the sections - already for the statements *)
    Definition section_to_nat_trafo:
      @section_disp C trafotarget_disp -> H ⟹ H'.
    Proof.
      intro sd.
      induction sd as [[sdob sdmor] [sdid sdcomp]].
      use make_nat_trans.
      - intro c. exact (sdob c).
      - intros c c' f.
        apply pathsinv0. exact (sdmor c c' f).
    Defined.

    Local Lemma roundtrip1_with_sections (η: H ⟹ H'):
      section_to_nat_trafo (nat_trafo_to_section η) = η.
    Proof.
      apply nat_trans_eq; [ apply (functor_category_has_homsets _ _) |].
      intro c.
      apply idpath.
    Qed.

    Local Lemma roundtrip2_with_sections (sd: @section_disp C trafotarget_disp):
      nat_trafo_to_section (section_to_nat_trafo sd) = sd.
    Proof.
      induction sd as [[sdob sdmor] [sdid sdcomp]].
      unfold nat_trafo_to_section, section_to_nat_trafo.
      cbn.
      use total2_paths_f; simpl.
      - use total2_paths_f; simpl.
        + apply idpath.
        + (* a bit of an overkill: a real proof of equality *)
          cbn.
          do 3 (apply funextsec; intro).
          (* show_id_type. *)
          apply pathsinv0inv0.
      - match goal with |- @paths ?ID _ _ => set (goaltype := ID); simpl in goaltype end.
        assert (Hprop: isaprop goaltype).
        2: { apply Hprop. }
        apply isapropdirprod.
        + apply impred. intro c.
          (* assert (aux := sdmor c c (id c)).
          cbn in aux.
          match goal with [H: @paths ?ID _ _ |- _ ] => set (auxtype := ID); simpl in auxtype end. *)
          apply hlevelntosn.
          apply (functor_category_has_homsets _ _).
        + do 5 (apply impred; intro).
          apply hlevelntosn.
          apply (functor_category_has_homsets _ _).
    Qed.

  End TheEquivalence.

End Upstream.

(** the previous development can be generalized to a bicategory for the items in the target

    this paves the way for an efficient treatment of the construction of a monoidal target category *)

Section UpstreamInBicat.

  Context {C0 : category}. (** an "ordinary" category for the source *)
  Context {C : bicat}.
  Context (a a' : ob C).

  Context (H H' : C0 ⟶ hom a a').

  Definition trafotargetbicat_disp_cat_ob_mor: disp_cat_ob_mor C0.
  Proof.
    use make_disp_cat_ob_mor.
    - intro c. exact (H c ==> H' c).
    - intros c c' α β f.
      exact (α · (# H' f) = (# H f) · β).
  Defined.

  Lemma trafotargetbicat_disp_cat_id_comp: disp_cat_id_comp C0 trafotargetbicat_disp_cat_ob_mor.
  Proof.
    split.
    - intros c α.
      red. unfold trafotargetbicat_disp_cat_ob_mor, make_disp_cat_ob_mor. hnf.
      do 2 rewrite functor_id.
      rewrite id_left. apply id_right.
    - intros c1 c2 c3 f g α1 α2 α3 Hypf Hypg.
      red in Hypf, Hypg |- *.
      unfold trafotargetbicat_disp_cat_ob_mor, make_disp_cat_ob_mor in Hypf, Hypg |- *.
      hnf in Hypf, Hypg |- *.
      do 2 rewrite functor_comp.
      rewrite assoc.
      rewrite Hypf.
      rewrite <- assoc.
      rewrite Hypg.
      apply assoc.
  Qed.

  Definition trafotargetbicat_disp_cat_data: disp_cat_data C0 :=
    trafotargetbicat_disp_cat_ob_mor ,, trafotargetbicat_disp_cat_id_comp.

  Lemma trafotargetbicat_disp_cells_isaprop (x y : C0) (f : C0 ⟦ x, y ⟧)
        (xx : trafotargetbicat_disp_cat_data x) (yy : trafotargetbicat_disp_cat_data y):
    isaprop (xx -->[ f] yy).
  Proof.
    intros Hyp Hyp'.
    apply (hom a a').
  Qed.

  Lemma trafotargetbicat_disp_cat_axioms: disp_cat_axioms C0 trafotargetbicat_disp_cat_data.
  Proof.
    repeat split; intros; try apply trafotargetbicat_disp_cells_isaprop.
    apply isasetaprop.
    apply trafotargetbicat_disp_cells_isaprop.
  Qed.

  Definition trafotargetbicat_disp: disp_cat C0 := trafotargetbicat_disp_cat_data ,, trafotargetbicat_disp_cat_axioms.

  Definition trafotargetbicat_cat: category := total_category trafotargetbicat_disp.

  Definition forget_from_trafotargetbicat: trafotargetbicat_cat ⟶ C0 := pr1_category trafotargetbicat_disp.

  Section EquivalenceInBicat.

    (** a "pedestrian" definition *)
    Definition nat_trafo_to_functor_bicat_elementary (η: H ⟹ H'): C0 ⟶ trafotargetbicat_cat.
    Proof.
      use make_functor.
      - use make_functor_data.
        + intro c.
          exact (c ,, η c).
        + intros c c' f.
          exists f.
          red. unfold trafotargetbicat_disp. hnf.
          apply pathsinv0, nat_trans_ax.
      - split; red.
        + intro c.
          use total2_paths_f.
          * cbn. apply idpath.
          * apply trafotargetbicat_disp_cells_isaprop.
        + intros c1 c2 c3 f f'.
          use total2_paths_f.
          * cbn. apply idpath.
          * apply trafotargetbicat_disp_cells_isaprop.
    Defined.

    (** using sections *)
    Definition nat_trafo_to_section_bicat (η: H ⟹ H'):
      @section_disp C0 trafotargetbicat_disp.
    Proof.
      use tpair.
      - use tpair.
        + intro c. exact (η c).
        + intros c c' f.
          red. unfold trafotargetbicat_disp. hnf.
          apply pathsinv0, nat_trans_ax.
      - split.
        + intro c.
          apply trafotargetbicat_disp_cells_isaprop.
        + intros c1 c2 c3 f f'.
          apply trafotargetbicat_disp_cells_isaprop.
    Defined.

    Definition nat_trafo_to_functor_bicat (η: H ⟹ H'): C0 ⟶ trafotargetbicat_cat :=
      @section_functor C0 trafotargetbicat_disp (nat_trafo_to_section_bicat η).

    Definition nat_trafo_to_functor_bicat_cor (η: H ⟹ H'):
      functor_composite (nat_trafo_to_functor_bicat η) forget_from_trafotargetbicat = functor_identity C0.
    Proof.
      apply from_section_functor.
    Defined.

    (** the other direction, essentially dependent on sections *)
    Definition section_to_nat_trafo_bicat:
      @section_disp C0 trafotargetbicat_disp -> H ⟹ H'.
    Proof.
      intro sd.
      use make_nat_trans.
      - intro c. exact (pr1 (pr1 sd) c).
      - intros c c' f.
        assert (aux := pr2 (pr1 sd) c c' f). apply pathsinv0. exact aux.
    Defined.

    Local Lemma roundtrip1_with_sections_bicat (η: H ⟹ H'):
      section_to_nat_trafo_bicat (nat_trafo_to_section_bicat η) = η.
    Proof.
      apply nat_trans_eq; [ apply (hom a a') |].
      intro c.
      apply idpath.
    Qed.

    Local Lemma roundtrip2_with_sections_bicat (sd: @section_disp C0 trafotargetbicat_disp):
      nat_trafo_to_section_bicat (section_to_nat_trafo_bicat sd) = sd.
    Proof.
      unfold nat_trafo_to_section_bicat, section_to_nat_trafo_bicat.
      cbn.
      use total2_paths_f; simpl.
      - use total2_paths_f; simpl.
        + apply idpath.
        + (* a bit of an overkill: a real proof of equality *)
          cbn.
          do 3 (apply funextsec; intro).
          (* show_id_type. *)
          apply pathsinv0inv0.
      - match goal with |- @paths ?ID _ _ => set (goaltype := ID); simpl in goaltype end.
        assert (Hprop: isaprop goaltype).
        2: { apply Hprop. }
        apply isapropdirprod.
        + apply impred. intro c.
          (* assert (aux := pr2 (pr1 sd) c c (id₁ c)).
          cbn in aux.
          match goal with [H: @paths ?ID _ _ |- _ ] => set (auxtype := ID); simpl in auxtype end. *)
          apply hlevelntosn.
          apply (hom a a').
        + do 5 (apply impred; intro).
          apply hlevelntosn.
          apply (hom a a').
    Qed.

  End EquivalenceInBicat.

End UpstreamInBicat.

Section Main.

  Context {V : category}.
  Context (Mon_V : monoidal V).

  Notation "X ⊗ Y" := (X ⊗_{ Mon_V } Y).

  Section ActionViaBicat.

    Context {C : bicat}.
    Context (a0 : ob C).

    Context {FA: functor V (category_from_bicat_and_ob a0)}.
    Context (FAm: fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA).

    (** currently no development on the abstract level *)

  End ActionViaBicat.

  Section FunctorViaBicat.

    Context {C : bicat}.
    Context {a0 a0' : ob C}.

    Context {FA: functor V (category_from_bicat_and_ob a0)}.
    Context {FA': functor V (category_from_bicat_and_ob a0')}.

    Context (FAm: fmonoidal Mon_V (monoidal_from_bicat_and_ob a0) FA).
    Context (FA'm: fmonoidal Mon_V (monoidal_from_bicat_and_ob a0') FA').

    Context (G : hom a0 a0').

    Definition H : functor V (hom a0 a0') :=
       functor_compose FA' (functor_fix_fst_arg _ _ _ hcomp_functor G).

    Definition H' : functor V (hom a0 a0') :=
      functor_compose FA (functor_fix_snd_arg _ _ _ hcomp_functor G).

    Lemma Hok (v: V) : H v = G · FA' v.
    Proof.
      apply idpath.
    Defined.

    Lemma Hmorok (v v': V) (f: v --> v'): # H f = G ◃ # FA' f.
    Proof.
      cbn. apply hcomp_identity_left.
    Qed.

    Lemma H'ok (v: V) : H' v = FA v · G.
    Proof.
      apply idpath.
    Defined.

    Lemma H'morok (v v': V) (f: v --> v'): # H' f = # FA f ▹ G.
    Proof.
      cbn. apply hcomp_identity_right.
    Qed.

    Definition montrafotargetbicat_disp: disp_cat V := trafotargetbicat_disp a0 a0' H H'.
    Definition montrafotargetbicat_cat: category := trafotargetbicat_cat a0 a0' H H'.

    Definition param_distr_bicat_triangle_eq_variant0_RHS : trafotargetbicat_disp a0 a0' H H' I_{Mon_V}.
    Proof.
      set (t1 := lwhisker G (pr1 (fmonoidal_preservesunitstrongly FA'm))).
      set (t2 := rwhisker G (fmonoidal_preservesunit FAm)).
      refine (vcomp2 t1 _).
      refine (vcomp2 _ t2).
      apply (vcomp2(g:=G)).
      - cbn. apply runitor.
      - cbn. apply linvunitor.
    Defined.

    Definition montrafotargetbicat_disp_unit: montrafotargetbicat_disp I_{Mon_V} :=
      param_distr_bicat_triangle_eq_variant0_RHS.

    Definition montrafotargetbicat_unit: montrafotargetbicat_cat := I_{Mon_V},, montrafotargetbicat_disp_unit.

    Definition param_distr_bicat_pentagon_eq_body_RHS (v w : V)
               (dv: montrafotargetbicat_disp v) (dw: montrafotargetbicat_disp w) : H v · FA' w ==> FA (v ⊗ w) · G.
    Proof.
      set (aux1 := rwhisker (FA' w) dv).
      set (aux2 := lwhisker (FA v) dw).
      transparent assert (auxr : (H v · FA' w ==> FA v · H' w)).
      { refine (vcomp2 aux1 _).
        refine (vcomp2 _ aux2).
        cbn.
        apply rassociator.
      }
      set (aux3 := rwhisker G (fmonoidal_preservestensordata FAm v w)).
      refine (vcomp2 auxr _).
      refine (vcomp2 _ aux3).
      cbn.
      apply lassociator.
    Defined.

    Definition param_distr_bicat_pentagon_eq_body_variant_RHS (v w : V)
               (dv: montrafotargetbicat_disp v) (dw: montrafotargetbicat_disp w) : montrafotargetbicat_disp (v ⊗ w).
    Proof.
      set (aux1inv := lwhisker G (pr1 (fmonoidal_preservestensorstrongly FA'm v w))).
      refine (vcomp2 aux1inv _).
      refine (vcomp2 _ (param_distr_bicat_pentagon_eq_body_RHS v w dv dw)).
      cbn.
      apply lassociator.
    Defined.


    (** a number of auxiliary isomorphisms to ease the lemmas on arrow reversion *)
    Definition lwhisker_with_μ_inv_inv2cell (v w : V): invertible_2cell (G · FA' (v ⊗ w)) (G · (FA' v · FA' w)).
    Proof.
      use make_invertible_2cell.
      - exact (lwhisker G (pr1 (fmonoidal_preservestensorstrongly FA'm v w))).
      - apply is_invertible_2cell_lwhisker.
        change (is_z_isomorphism (pr1 (fmonoidal_preservestensorstrongly FA'm v w))).
        apply is_z_isomorphism_inv.
    Defined.

    Definition rwhisker_lwhisker_with_μ_inv_inv2cell (v1 v2 v3 : V):
      invertible_2cell (G · (FA' (v1 ⊗ v2) · FA' v3)) (G · (FA' v1 · FA' v2 · FA' v3)).
    Proof.
      use make_invertible_2cell.
      - exact (G ◃ (pr1 (fmonoidal_preservestensorstrongly FA'm v1 v2) ▹ FA' v3)).
      - apply is_invertible_2cell_lwhisker.
        apply is_invertible_2cell_rwhisker.
        change (is_z_isomorphism  (pr1 (fmonoidal_preservestensorstrongly FA'm v1 v2))).
        apply is_z_isomorphism_inv.
    Defined.

    Definition lwhisker_rwhisker_with_ϵ_inv_inv2cell (v : V):
      invertible_2cell (G · FA' I_{Mon_V} · FA' v) (G · id₁ a0' · FA' v).
    Proof.
      use make_invertible_2cell.
      - exact ((G ◃ pr1 (fmonoidal_preservesunitstrongly FA'm)) ▹ FA' v).
      - apply is_invertible_2cell_rwhisker.
        apply is_invertible_2cell_lwhisker.
        change (is_z_isomorphism (pr1 (fmonoidal_preservesunitstrongly FA'm))).
        apply is_z_isomorphism_inv.
    Defined.

    Definition rwhisker_with_linvunitor_inv2cell (v : V): invertible_2cell (G · FA' v) (id₁ a0 · G · FA' v).
    Proof.
      use make_invertible_2cell.
      - exact (linvunitor G ▹ FA' v).
      - apply is_invertible_2cell_rwhisker.
        apply is_invertible_2cell_linvunitor.
    Defined.

    Definition lwhisker_with_linvunitor_inv2cell (v : V):
      invertible_2cell (FA v · G) (FA v · (id₁ a0 · G)).
    Proof.
      use make_invertible_2cell.
      - exact (FA v ◃ linvunitor G).
      - apply is_invertible_2cell_lwhisker.
        apply is_invertible_2cell_linvunitor.
    Defined.

    Definition lwhisker_with_invlunitor_inv2cell (v : V):
      invertible_2cell (G · (pr11 FA') v) (G · (pr11 FA') (I_{Mon_V} ⊗ v)).
    Proof.
      use make_invertible_2cell.
      - exact (G ◃ # FA' (pr1 (pr2 (leftunitor_nat_z_iso Mon_V) v))).
      - apply is_invertible_2cell_lwhisker.
        change (is_z_isomorphism (# FA' (pr1 (pr2 (leftunitor_nat_z_iso Mon_V) v)))).
        apply functor_on_is_z_isomorphism.
        apply (is_z_iso_inv_from_z_iso (nat_z_iso_pointwise_z_iso (leftunitor_nat_z_iso Mon_V) v)).
    Defined.

    Definition rwhisker_with_invlunitor_inv2cell (v : V):
      invertible_2cell (FA v · G) (FA (I_{Mon_V} ⊗ v) · G).
    Proof.
      use make_invertible_2cell.
      - exact (# FA (pr1 (pr2 (leftunitor_nat_z_iso Mon_V) v)) ▹ G).
      - apply is_invertible_2cell_rwhisker.
        change (is_z_isomorphism (# FA (pr1 (pr2 (leftunitor_nat_z_iso Mon_V) v)))).
        apply functor_on_is_z_isomorphism.
        apply (is_z_iso_inv_from_z_iso (nat_z_iso_pointwise_z_iso (leftunitor_nat_z_iso Mon_V) v)).
    Defined.

    Definition lwhisker_with_invrunitor_inv2cell (v : V):
      invertible_2cell (G · FA' v) (G · FA'(v ⊗ I_{Mon_V})).
    Proof.
      use make_invertible_2cell.
      - exact (G ◃ # FA' (pr1 (pr2 (rightunitor_nat_z_iso Mon_V) v))).
      - apply is_invertible_2cell_lwhisker.
        change (is_z_isomorphism (# FA' (pr1 (pr2 (rightunitor_nat_z_iso Mon_V) v)))).
        apply functor_on_is_z_isomorphism.
        apply (is_z_iso_inv_from_z_iso (nat_z_iso_pointwise_z_iso (rightunitor_nat_z_iso Mon_V) v)).
    Defined.

    Definition rwhisker_with_invrunitor_inv2cell (v : V):
      invertible_2cell (FA v · G) (FA (v ⊗ I_{Mon_V}) · G).
    Proof.
      use make_invertible_2cell.
      - exact (# FA (pr1 (pr2 (rightunitor_nat_z_iso Mon_V) v)) ▹ G).
      - apply is_invertible_2cell_rwhisker.
        change (is_z_isomorphism (# FA (pr1 (pr2 (rightunitor_nat_z_iso Mon_V) v)))).
        apply functor_on_is_z_isomorphism.
        apply (is_z_iso_inv_from_z_iso (nat_z_iso_pointwise_z_iso (rightunitor_nat_z_iso Mon_V) v)).
    Defined.

    Definition lwhisker_with_ϵ_inv2cell (v : V):
      invertible_2cell (FA' v · id₁ a0') (FA' v · FA' I_{Mon_V}).
    Proof.
      use make_invertible_2cell.
      - exact (FA' v ◃ fmonoidal_preservesunit FA'm).
      - apply is_invertible_2cell_lwhisker.
        change (is_z_isomorphism (fmonoidal_preservesunit FA'm)).
        apply fmonoidal_preservesunitstrongly.
    Defined.

    Definition rwhisker_with_invassociator_inv2cell (v1 v2 v3 : V):
      invertible_2cell (FA (v1 ⊗ (v2 ⊗ v3)) · G) (FA ((v1 ⊗ v2) ⊗ v3) · G).
    Proof.
      use make_invertible_2cell.
      - exact (# FA (αinv_{Mon_V} v1 v2 v3) ▹ G).
      - apply is_invertible_2cell_rwhisker.
        change (is_z_isomorphism (# FA (αinv_{Mon_V} v1 v2 v3))).
        apply functor_on_is_z_isomorphism.
        exists (α_{Mon_V} v1 v2 v3).
        destruct (monoidal_associatorisolaw Mon_V v1 v2 v3).
        split; assumption.
    Defined.
    (** end of auxiliary definitions of isomorphisms *)

    (** the main lemma for the construction of the tensor - for reasons of exploiting legacy code, this is the general lemma and not its two instances that come right afterwards *)
    Lemma montrafotargetbicat_tensor_comp_aux (v w v' w': V) (f: V⟦v,v'⟧) (g: V⟦w,w'⟧)
          (η : montrafotargetbicat_disp v) (π : montrafotargetbicat_disp w)
          (η' : montrafotargetbicat_disp v') (π' : montrafotargetbicat_disp w')
          (Hyp: η  -->[ f] η') (Hyp': π -->[ g] π'):
      param_distr_bicat_pentagon_eq_body_variant_RHS v w η π
      -->[ f ⊗^{Mon_V} g]
      param_distr_bicat_pentagon_eq_body_variant_RHS v' w' η' π'.
    Proof.
      hnf in Hyp, Hyp' |- *.
      unfold param_distr_bicat_pentagon_eq_body_variant_RHS, param_distr_bicat_pentagon_eq_body_RHS.
      match goal with | [ |- (?Hαinv • (?Hassoc1 • ((?Hγ • (?Hassoc2 • ?Hδ)) • (?Hassoc3 • ?Hβ)))) · ?Hε = _ ] =>
                          set (αinv := Hαinv); set (γ := Hγ); set (δ:= Hδ); set (β := Hβ); set (ε1 := Hε) end.
      cbn in αinv, β.
      match goal with | [ |- _ = ?Hε · (?Hαinv • (?Hassoc4 • ((?Hγ • (?Hassoc5 • ?Hδ) • (?Hassoc6 • ?Hβ))))) ] =>
                          set (αinv' := Hαinv); set (γ' := Hγ); set (δ':= Hδ); set (β' := Hβ); set (ε2 := Hε) end.
      cbn in αinv', β'.
      set (αinviso := lwhisker_with_μ_inv_inv2cell v w).
      cbn in αinviso.
      etrans.
      { apply pathsinv0. apply vassocr. }
      apply (lhs_left_invert_cell _ _ _ αinviso).
      apply pathsinv0.
      unfold inv_cell.
      set (α := lwhisker G (fmonoidal_preservestensordata FA'm v w)).
      cbn in α.
      match goal with | [ |- ?Hαcand • _ = _ ] => set (αcand := Hαcand) end.
      change αcand with α.
      clear αcand.
      assert (μFA'natinst := full_naturality_condition (pr2 (preservestensor_is_nattrans (fmonoidal_preservestensornatleft FA'm) (fmonoidal_preservestensornatright FA'm))) f g).
      cbn in μFA'natinst.
      unfold make_binat_trans_data in μFA'natinst.
      assert (μFAnatinst := full_naturality_condition (pr2 (preservestensor_is_nattrans (fmonoidal_preservestensornatleft FAm) (fmonoidal_preservestensornatright FAm))) f g).
      cbn in μFAnatinst.
      unfold make_binat_trans_data in μFAnatinst.
      set (ε2better := lwhisker G (# FA' (f ⊗^{Mon_V} g))).
      transparent assert (ε2betterok : (ε2 = ε2better)).
      { cbn. apply hcomp_identity_left. }
      rewrite ε2betterok.
      etrans.
      { apply vassocr. }
      apply (maponpaths (lwhisker G)) in μFA'natinst.
      apply pathsinv0 in μFA'natinst.
      etrans.
      { apply maponpaths_2.
        apply lwhisker_vcomp. }
      etrans.
      { apply maponpaths_2.
        unfold functoronmorphisms1. rewrite functor_comp.
        exact μFA'natinst. }
      clear ε2 μFA'natinst ε2better ε2betterok.
      etrans.
      { apply maponpaths_2.
        apply pathsinv0.
        apply lwhisker_vcomp. }
      etrans.
      { apply pathsinv0. apply vassocr. }
      etrans.
      { apply maponpaths.
        rewrite vassocr.
        apply maponpaths_2.
        unfold αinv'.
        apply lwhisker_vcomp.
      }
      etrans.
      { apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        apply (pr12 (fmonoidal_preservestensorstrongly FA'm v' w')). }
      clear αinv αinv' αinviso α.
      set (ε1better := rwhisker G (# FA (f ⊗^{Mon_V} g))).
      transparent assert (ε1betterok : (ε1 = ε1better)).
      { cbn. apply hcomp_identity_right. }
      rewrite ε1betterok.
      cbn.
      rewrite lwhisker_id2.
      rewrite id2_left.
      match goal with | [ |- ?Hσ • _ = _ ] => set (σ' := Hσ) end.
      etrans.
      2: { repeat rewrite <- vassocr. apply idpath. }
      apply (maponpaths (rwhisker G)) in μFAnatinst.
      etrans.
      2: { do 5 apply maponpaths.
           apply pathsinv0. apply rwhisker_vcomp. }
      etrans.
      2: { do 5 apply maponpaths.
           unfold functoronmorphisms1. rewrite functor_comp.
           exact μFAnatinst. }
      clear β μFAnatinst ε1 ε1better ε1betterok.
      etrans.
      2: { do 5 apply maponpaths.
           apply rwhisker_vcomp. }
      match goal with | [ |- _ =  _ • (_ • (_ • (_ • (_ • (_ • ?Hβ'twin))))) ] => set (β'twin := Hβ'twin) end.
      change β'twin with β'.
      clear β'twin.
      repeat rewrite vassocr.
      apply maponpaths_2.
      clear β'.
      unfold σ'.
      assert (hcomp_aux:= hcomp_hcomp' (# FA' f) (# FA' g)).
      unfold hcomp, hcomp' in hcomp_aux.
      etrans.
      { do 5 apply maponpaths_2. apply maponpaths. apply hcomp_aux. }
      clear hcomp_aux σ'.
      rewrite <- lwhisker_vcomp.
      match goal with | [ |- (((((?Hσ'1 • ?Hσ'2) • _) • _) • _) • _) • _  = _ • ?Hσ ]
                        => set (σ'1 := Hσ'1); set (σ'2 := Hσ'2); set (σ := Hσ) end.
      change (η • # H' f = # H f • η') in Hyp.
      apply (maponpaths (rwhisker (FA' w'))) in Hyp.
      do 2 rewrite <- rwhisker_vcomp in Hyp.
      apply pathsinv0 in Hyp.
      assert (Hypvariant: σ'2 • lassociator G (FA' v') (FA' w') • γ' =
        lassociator G (FA' v) (FA' w') • (rwhisker (FA' w') η • rwhisker (FA' w') (# H' f))).
      { apply (maponpaths (vcomp2 (lassociator G (FA' v) (FA' w')))) in Hyp.
        etrans.
        2: { exact Hyp. }
        rewrite vassocr.
        apply maponpaths_2.
        rewrite Hmorok.
        apply rwhisker_lwhisker.
      }
      clear Hyp.
      intermediate_path (σ'1 • ((σ'2 • lassociator G (FA' v') (FA' w')) • γ') •
                             rassociator (FA v') G (FA' w') • δ' • lassociator (FA v') (FA w') G).
      { repeat rewrite <- vassocr.
        apply idpath. }
      rewrite Hypvariant.
      clear σ'2 γ' Hypvariant. (* until here mostly in parallel with earlier proof in CAT *)
      assert (σ'1ok : σ'1 • lassociator G (FA' v) (FA' w') =
                        lassociator G (FA' v) (FA' w) • (H v ◃ # FA' g)).
      (* associators needed in addition to devel. in CAT *)
      { apply lwhisker_lwhisker. }
      etrans.
      { repeat rewrite vassocr. rewrite σ'1ok. apply idpath. }
      clear σ'1 σ'1ok.
      repeat rewrite <- vassocr.
      apply maponpaths.
      etrans.
      { repeat rewrite vassocr.
        do 4 apply maponpaths_2.
        apply pathsinv0.
        apply hcomp_hcomp'. }
      unfold hcomp.
      repeat rewrite <- vassocr.
      apply maponpaths.
      clear γ.
      change (π • # H' g = # H g • π') in Hyp'.
      apply (maponpaths (lwhisker (FA v))) in Hyp'.
      do 2 rewrite <- lwhisker_vcomp in Hyp'.
      rewrite H'morok in Hyp'.
      assert (Hyp'variant: δ • lassociator (FA v) (FA w) G • ((FA v ◃ # FA g) ▹ G) =
                             ((FA v ◃ # H g) • (FA v ◃ π')) • lassociator (FA v) (FA w') G).
      (* close to what was called Hypvariant in the devel. in CAT *)
      { apply (maponpaths (fun x => x • lassociator (FA v) (FA w') G)) in Hyp'.
        etrans.
        { rewrite <- vassocr. apply maponpaths. apply pathsinv0. apply rwhisker_lwhisker. }
        rewrite vassocr. exact Hyp'.
      }
      clear Hyp'.
      set (σbetter := hcomp' (# FA f) (# FA g) ▹ G).
      assert (σbetterok : σ = σbetter).
      { apply maponpaths. apply hcomp_hcomp'. }
      rewrite σbetterok.
      clear σ σbetterok.
      unfold hcomp' in σbetter.
      set (σbetter' := ((FA v ◃ # FA g) ▹ G ) • ((# FA f ▹ FA w') ▹ G)).
      assert (σbetter'ok : σbetter = σbetter').
      { apply pathsinv0, rwhisker_vcomp. }
      rewrite σbetter'ok. clear σbetter σbetter'ok.
      etrans.
      2: { apply maponpaths. unfold σbetter'. repeat rewrite vassocr. apply maponpaths_2.
           apply pathsinv0. exact Hyp'variant. }
      clear Hyp'variant σbetter' δ. (* now very close to the situation in the CAT development where δ was cleared *)
      etrans.
      2: { repeat rewrite vassocr. apply idpath. }
      match goal with | [ |- _ = (((_ • ?Hν'variant) • ?Hδ'π') • _) • _]
                        => set (ν'variant := Hν'variant); set (δ'π' := Hδ'π') end.
      assert (ν'variantok: ν'variant • lassociator (FA v) G (FA' w') =
                             lassociator (FA v) G (FA' w) • (H' v ◃ # FA' g)).
      { unfold ν'variant. rewrite Hmorok. apply lwhisker_lwhisker. }
      etrans.
      2: { repeat rewrite <- vassocr. apply idpath. }
      apply pathsinv0.
      use lhs_left_invert_cell.
      { apply is_invertible_2cell_rassociator. }
      etrans.
      2: { repeat rewrite vassocr.
           do 4 apply maponpaths_2.
           exact ν'variantok. }
      repeat rewrite <- vassocr.
      apply maponpaths.
      clear ν'variant ν'variantok.
      etrans.
      { apply maponpaths.
        apply rwhisker_rwhisker. }
      repeat rewrite vassocr.
      apply maponpaths_2.
      rewrite H'morok.
      etrans.
      { apply pathsinv0. apply hcomp_hcomp'. }
      clear δ'π'.
      unfold hcomp.
      apply maponpaths_2.
      clear δ'.
      cbn.
      rewrite rwhisker_rwhisker.
      rewrite <- vassocr.
      etrans.
      { apply pathsinv0, id2_right. }
      apply maponpaths.
      apply pathsinv0.
      apply (vcomp_rinv (is_invertible_2cell_lassociator _ _ _)).
    Qed.

    (** the first dependently-typed ingredient of the displayed bifunctor for the tensor construction *)
    Lemma montrafotargetbicat_tensor_comp_aux_inst1 (v w w' : V) (g : V ⟦ w, w' ⟧)
          (η : G · FA' v ==> FA v · G) (π : G · FA' w ==> FA w · G) (π' : G · FA' w' ==> FA w' · G):
      π • (# FA g ▹ G) = (G ◃ # FA' g) • π'
      → param_distr_bicat_pentagon_eq_body_variant_RHS v w η π • (# FA (v ⊗^{ Mon_V}_{l} g) ▹ G) =
          (G ◃ # FA' (v ⊗^{ Mon_V}_{l} g)) • param_distr_bicat_pentagon_eq_body_variant_RHS v w' η π'.
    Proof.
      intro Hyp'.
      rewrite <- hcomp_identity_right in Hyp' |- *.
      rewrite <- hcomp_identity_left in Hyp' |- *.
      rewrite <- when_bifunctor_becomes_leftwhiskering.
      apply montrafotargetbicat_tensor_comp_aux; [| assumption].
      hnf. do 2 rewrite functor_id. rewrite id_left. apply id_right.
    Qed.

    (** the second dependently-typed ingredient of the displayed bifunctor for the tensor construction *)
    Lemma montrafotargetbicat_tensor_comp_aux_inst2 (v v' w : V) (f : V ⟦ v, v' ⟧)
          (η : G · FA' v ==> FA v · G) (η' : G · FA' v' ==> FA v' · G) (π : G · FA' w ==> FA w · G):
      η • (# FA f ▹ G) = (G ◃ # FA' f) • η'
      → param_distr_bicat_pentagon_eq_body_variant_RHS v w η π • (# FA (f ⊗^{ Mon_V}_{r} w) ▹ G) =
          (G ◃ # FA' (f ⊗^{ Mon_V}_{r} w)) • param_distr_bicat_pentagon_eq_body_variant_RHS v' w η' π.
    Proof.
      intro Hyp.
      rewrite <- hcomp_identity_right in Hyp |- *.
      rewrite <- hcomp_identity_left in Hyp |- *.
      rewrite <- when_bifunctor_becomes_rightwhiskering.
      apply montrafotargetbicat_tensor_comp_aux; [assumption |].
      hnf. do 2 rewrite functor_id. rewrite id_left. apply id_right.
    Qed.

    Definition montrafotargetbicat_disp_tensor: disp_tensor montrafotargetbicat_disp Mon_V.
    Proof.
      use make_disp_bifunctor.
      - use make_disp_bifunctor_data.
        + intros v w η π.
          exact (param_distr_bicat_pentagon_eq_body_variant_RHS v w η π).
        + cbn.
          intros v w w' g η π π' Hyp'.
          rewrite hcomp_identity_right in Hyp' |- *.
          rewrite hcomp_identity_left in Hyp' |- *.
          apply montrafotargetbicat_tensor_comp_aux_inst1; assumption.
        + cbn.
          intros v v' w f η η' π Hyp.
          rewrite hcomp_identity_right in Hyp |- *.
          rewrite hcomp_identity_left in Hyp |- *.
          apply montrafotargetbicat_tensor_comp_aux_inst2; assumption.
      - red. repeat split; red; intros; apply trafotargetbicat_disp_cells_isaprop.
    Defined.

    (** the following are called data elements, but they have no computational content *)
    Lemma montrafotargetbicat_disp_leftunitor_data: disp_leftunitor_data montrafotargetbicat_disp_tensor montrafotargetbicat_disp_unit.
    Proof.
      hnf.
      intros v η.
      cbn.
      (** now comes an adaptation of the code of [montrafotargetbicat_left_unitor_aux1] from the former approach to monoidal categories *)
      unfold param_distr_bicat_pentagon_eq_body_variant_RHS, montrafotargetbicat_disp_unit,
        param_distr_bicat_triangle_eq_variant0_RHS, param_distr_bicat_pentagon_eq_body_RHS.
      rewrite hcomp_identity_left. rewrite hcomp_identity_right.
      do 3 rewrite <- rwhisker_vcomp.
      repeat rewrite <- vassocr.
      match goal with | [ |- ?Hl1 • (_ • (?Hl2 • (_ • (_ • (?Hl3 • (_ • (?Hl4 • (_ • (?Hl5 • ?Hl6))))))))) = ?Hr1 • _]
                        => set (l1 := Hl1); set (l2 := Hl2); set (l3 := Hl3); set (l4 := Hl4);
                          set (l5 := Hl5); set (l6 := Hl6); set (r1 := Hr1) end.
      change (H v ==> H' v) in η.
      set (l1iso := lwhisker_with_μ_inv_inv2cell I_{Mon_V} v).
      apply (lhs_left_invert_cell _ _ _ l1iso).
      cbn.
      apply (lhs_left_invert_cell _ _ _ (is_invertible_2cell_lassociator _ _ _)).
      cbn.
      set (l2iso := lwhisker_rwhisker_with_ϵ_inv_inv2cell v).
      apply (lhs_left_invert_cell _ _ _ l2iso).
      cbn.
      etrans.
      2: { repeat rewrite vassocr.
           rewrite <- rwhisker_lwhisker_rassociator.
           apply maponpaths_2.
           repeat rewrite <- vassocr.
           apply maponpaths.
           unfold r1.
           do 2 rewrite lwhisker_vcomp.
           apply maponpaths.
           rewrite vassocr.
           assert (lax_monoidal_functor_unital_inst := fmonoidal_preservesleftunitality FA'm v).
           cbn in lax_monoidal_functor_unital_inst.
           apply pathsinv0.
           exact lax_monoidal_functor_unital_inst.
      }
      clear l1 l2 l1iso l2iso r1.
      etrans.
      { do 2 apply maponpaths.
        rewrite vassocr.
        apply maponpaths_2.
        apply rwhisker_rwhisker_alt. }
      clear l3.
      cbn.
      etrans.
      { do 2 apply maponpaths.
        repeat rewrite vassocr.
        do 3 apply maponpaths_2.
        rewrite <- vassocr.
        apply maponpaths.
        apply hcomp_hcomp'. }
      clear l4.
      unfold hcomp'.
      etrans.
      { repeat rewrite <- vassocr.
        do 4 apply maponpaths.
        rewrite vassocr.
        rewrite <- rwhisker_rwhisker.
        repeat rewrite <- vassocr.
        apply maponpaths.
        unfold l5, l6.
        do 2 rewrite rwhisker_vcomp.
        apply maponpaths.
        apply pathsinv0.
        rewrite vassocr.
        assert (lax_monoidal_functor_unital_inst := fmonoidal_preservesleftunitality FAm v).
        cbn in lax_monoidal_functor_unital_inst.
        apply pathsinv0.
        exact lax_monoidal_functor_unital_inst.
      }
      clear l5 l6. (* now only admin tasks in bicategory *)
      rewrite lunitor_lwhisker.
      apply maponpaths.
      apply (lhs_left_invert_cell _ _ _ (rwhisker_with_linvunitor_inv2cell v)).
      cbn.
      rewrite lunitor_triangle.
      rewrite vcomp_lunitor.
      rewrite vassocr.
      apply maponpaths_2.
      apply (lhs_left_invert_cell _ _ _ (is_invertible_2cell_rassociator _ _ _)).
      cbn.
      apply pathsinv0, lunitor_triangle.
    Qed.

    Lemma montrafotargetbicat_disp_rightunitor_data: disp_rightunitor_data montrafotargetbicat_disp_tensor montrafotargetbicat_disp_unit.
    Proof.
      hnf.
      intros v η.
      cbn.
      (** now comes an adaptation of the code of [montrafotargetbicat_right_unitor_aux1] from the former approach to monoidal categories *)
      unfold param_distr_bicat_pentagon_eq_body_variant_RHS, montrafotargetbicat_disp_unit,
        param_distr_bicat_triangle_eq_variant0_RHS, param_distr_bicat_pentagon_eq_body_RHS.
      rewrite hcomp_identity_left. rewrite hcomp_identity_right.
      do 3 rewrite <- lwhisker_vcomp.
      repeat rewrite <- vassocr.
      match goal with | [ |- ?Hl1 • (_ • (?Hl2 • (_ • (?Hl3 • (_ • (_ • (?Hl4 • (_ • (?Hl5 • ?Hl6))))))))) = ?Hr1 • _]
                        => set (l1 := Hl1); set (l2 := Hl2); set (l3 := Hl3); set (l4 := Hl4);
                          set (l5 := Hl5); set (l6 := Hl6); set (r1 := Hr1) end.
      change (H v ==> H' v) in η.
      set (l1iso := lwhisker_with_μ_inv_inv2cell v I_{Mon_V}).
      apply (lhs_left_invert_cell _ _ _ l1iso).
      cbn.
      clear l1 l1iso.
      apply (lhs_left_invert_cell _ _ _ (is_invertible_2cell_lassociator _ _ _)).
      cbn.
      etrans.
      2: { apply maponpaths.
           rewrite vassocr.
           apply maponpaths_2.
           unfold r1.
           rewrite lwhisker_vcomp.
           apply maponpaths.
           assert (lax_monoidal_functor_unital_inst := fmonoidal_preservesrightunitality FA'm v).
           cbn in lax_monoidal_functor_unital_inst.
           apply pathsinv0 in lax_monoidal_functor_unital_inst.
           set (aux1iso := lwhisker_with_ϵ_inv2cell v).
           rewrite <- vassocr in lax_monoidal_functor_unital_inst.
           apply pathsinv0 in lax_monoidal_functor_unital_inst.
           apply (rhs_left_inv_cell _ _ _ aux1iso) in lax_monoidal_functor_unital_inst.
           unfold inv_cell in lax_monoidal_functor_unital_inst.
           apply pathsinv0.
           exact lax_monoidal_functor_unital_inst.
      }
      cbn.
      clear r1.
      etrans.
      2: { rewrite vassocr.
           apply maponpaths_2.
           rewrite <- lwhisker_vcomp.
           rewrite vassocr.
           apply maponpaths_2.
           apply pathsinv0.
           apply lwhisker_lwhisker_rassociator. }
      etrans.
      2: { repeat rewrite <- vassocr.
           apply maponpaths.
           rewrite vassocr.
           apply maponpaths_2.
           apply pathsinv0, runitor_triangle. }
      rewrite <- vcomp_runitor.
      etrans.
      2: { rewrite vassocr.
           apply maponpaths_2.
           apply hcomp_hcomp'. }
      unfold hcomp.
      etrans.
      2: { repeat rewrite <- vassocr. apply idpath. }
      apply maponpaths.
      clear l2.
      etrans.
      { repeat rewrite vassocr.
        do 6 apply maponpaths_2.
        apply lwhisker_lwhisker_rassociator. }
      repeat rewrite <- vassocr.
      apply maponpaths.
      clear l3.
      cbn.
      etrans.
      { repeat rewrite vassocr.
        do 5 apply maponpaths_2.
        apply runitor_triangle. }
      etrans.
      2: { apply id2_right. }
      repeat rewrite <- vassocr.
      apply maponpaths.
      etrans.
      { apply maponpaths.
        rewrite vassocr.
        apply maponpaths_2.
        apply rwhisker_lwhisker. }
      cbn.
      clear l4.
      etrans.
      { apply maponpaths.
        rewrite <- vassocr.
        apply maponpaths.
        unfold l5, l6.
        do 2 rewrite rwhisker_vcomp.
        apply maponpaths.
        assert (lax_monoidal_functor_unital_inst := fmonoidal_preservesrightunitality FAm v).
        cbn in lax_monoidal_functor_unital_inst.
        apply pathsinv0.
        rewrite vassocr.
        apply pathsinv0.
        exact lax_monoidal_functor_unital_inst.
      }
      clear l5 l6. (* now only pure bicategory reasoning *)
      set (auxiso := lwhisker_with_linvunitor_inv2cell v).
      apply (lhs_left_invert_cell _ _ _ auxiso).
      cbn.
      rewrite id2_right.
      clear auxiso.
      apply runitor_rwhisker.
    Qed.

    Definition montrafotargetbicat_disp_associator_data: disp_associator_data montrafotargetbicat_disp_tensor.
    Proof.
      intros v1 v2 v3 η1 η2 η3.
      cbn. (** now comes an adaptation of the code of [montrafotargetbicat_associator_aux1] from the former approach to monoidal categories *)
      unfold param_distr_bicat_pentagon_eq_body_variant_RHS, montrafotargetbicat_disp_unit,
        param_distr_bicat_triangle_eq_variant0_RHS, param_distr_bicat_pentagon_eq_body_RHS.
      rewrite hcomp_identity_left. rewrite hcomp_identity_right.
      do 6 rewrite <- lwhisker_vcomp.
      do 6 rewrite <- rwhisker_vcomp.
      repeat rewrite <- vassocr.
      match goal with | [ |- ?Hl1 • (_ • (?Hl2 • (_ • (?Hl3 • (_ • (?Hl4 • (_ • (?Hl5 • (_ • (?Hl6 • (_ • (?Hl7 • ?Hl8)))))))))))) = _]
                        => set (l1 := Hl1); set (l2 := Hl2); set (l3 := Hl3); set (l4 := Hl4);
                          set (l5 := Hl5); set (l6 := Hl6); set (l7 := Hl7); set (l8 := Hl8) end.
      match goal with | [ |- _ = ?Hr1 • (?Hr2 • (_ • (?Hr3 • (_ • (?Hr4 • (_ • (?Hr5 • (_ • (?Hr6 • (_ • (?Hr7 • (_ • ?Hr8))))))))))))]
                        => set (r1 := Hr1); set (r2 := Hr2); set (r3 := Hr3); set (r4 := Hr4);
                          set (r5 := Hr5); set (r6 := Hr6); set (r7 := Hr7); set (r8 := Hr8) end.
      change (H v1 ==> H' v1) in η1; change (H v2 ==> H' v2) in η2; change (H v3 ==> H' v3) in η3.
      set (l1iso := lwhisker_with_μ_inv_inv2cell (v1 ⊗ v2) v3).
      apply (lhs_left_invert_cell _ _ _ l1iso).
      cbn.
      clear l1 l1iso.
      match goal with | [ |- _ = ?Hl1inv • _] => set (l1inv := Hl1inv) end.
      etrans.
      { rewrite vassocr.
        apply maponpaths_2.
        apply pathsinv0.
        apply rwhisker_lwhisker. }
      clear l2.
      etrans.
      { repeat rewrite <- vassocr. apply idpath. }
      match goal with | [ |- ?Hl2' • _ = _] => set (l2' := Hl2') end.
      cbn in l2'.
      set (l2'iso := rwhisker_lwhisker_with_μ_inv_inv2cell v1 v2 v3).
      apply (lhs_left_invert_cell _ _ _ l2'iso).
      cbn.
      clear l2' l2'iso.
      etrans.
      2: { repeat rewrite vassocr.
           do 13 apply maponpaths_2.
           unfold l1inv, r1.
           do 2 rewrite lwhisker_vcomp.
           apply maponpaths.
           assert (lax_monoidal_functor_assoc_inst := fmonoidal_preservesassociativity FA'm v1 v2 v3).
           cbn in lax_monoidal_functor_assoc_inst.
           apply pathsinv0.
           exact lax_monoidal_functor_assoc_inst.
      }
      clear l1inv r1.
      etrans.
      2: { do 13 apply maponpaths_2.
           do 2 rewrite <- lwhisker_vcomp.
           apply idpath. }
      etrans.
      2: { do 12 apply maponpaths_2.
           repeat rewrite <- vassocr.
           do 2 apply maponpaths.
           unfold r2.
           rewrite lwhisker_vcomp.
           apply maponpaths.
           set (auxbeinginverse := pr12 (fmonoidal_preservestensorstrongly FA'm v1 (v2 ⊗_{ Mon_V} v3))).
           cbn in auxbeinginverse.
           apply pathsinv0, auxbeinginverse. }
      cbn.
      clear r2.
      rewrite lwhisker_id2.
      rewrite id2_right.
      etrans.
      2: { do 10 apply maponpaths_2.
           repeat rewrite <- vassocr.
           apply maponpaths.
           rewrite vassocr.
           rewrite lwhisker_lwhisker.
           rewrite <- vassocr.
           apply maponpaths.
           apply hcomp_hcomp'. }
      unfold hcomp.
      clear r3.
      etrans.
      2: { repeat rewrite <- vassocr. apply idpath. }
      match goal with | [ |- _ = _ • (_ • (?Hr1'' • (?Hr3' • _)))]
                        => set (r1'' := Hr1''); set (r3' := Hr3') end.
      cbn in l5.
      (*

         lassociator (FA v1) (FA v2) G ▹ FA' v3 starts with FA v1 · (FA v2 · G) · FA' v3
         l5 starts with FA v1 · FA v2 · G · FA' v3

         FA v1 ◃ rassociator (FA v2) G (FA' v3) starts with FA v1 · (FA v2 · G · FA' v3)
         r6 starts with FA v1 · (FA v2 · H v3)

       *)
      match goal with | [ |- _ • (  _ • ( _ • ( _ • ( _ • ?Hltail))))  =
                              _ • (  _ • ( _ • ( _ • (  _ • ( _ • ( _ • ( _ • ?Hrtail)))))))]
                        => set (ltail := Hltail); set (rtail := Hrtail) end.
      assert (tailseq: lassociator (FA v1) (FA v2 · G) (FA' v3) • ltail = rtail).
      2: { rewrite <- tailseq.
           repeat rewrite vassocr.
           apply maponpaths_2.
           clear l5 l6 l7 l8 r6 r7 r8 ltail rtail tailseq η3.
           (* l3 is close to r1'', l4 is close to r5, and r3' is close
              to the inverse of r4 - we first treat the latter *)
           etrans.
           2: { repeat rewrite <- vassocr.
                do 3 apply maponpaths.
                repeat rewrite vassocr.
                do 3 apply maponpaths_2.
                rewrite <- vassocr.
                unfold r4.
                rewrite lwhisker_lwhisker_rassociator.
                rewrite vassocr.
                apply maponpaths_2.
                unfold r3'.
                rewrite lwhisker_vcomp.
                apply maponpaths.
                set (auxbeinginverse := pr12 (fmonoidal_preservestensorstrongly FA'm v2 v3)).
                cbn in auxbeinginverse.
                apply pathsinv0, auxbeinginverse. }
           cbn.
           clear r3' r4.
           rewrite lwhisker_id2.
           rewrite id2_left.
           (* now plain reasoning in one bicategory *)
           etrans.
           2: { repeat rewrite <- vassocr.
                do 5 apply maponpaths.
                apply pathsinv0, rwhisker_lwhisker. }
           clear r5.
           etrans.
           2: { repeat rewrite vassocr. apply idpath. }
           apply maponpaths_2.
           clear l4.
           assert (l3ok := rwhisker_rwhisker (FA' v2) (FA' v3) η1).
           apply (rhs_left_inv_cell _ _ _ (is_invertible_2cell_lassociator _ _ _)) in l3ok.
           cbn in l3ok.
           assert (l3okbetter: l3 = rassociator (G · FA' v1) (FA' v2) (FA' v3)
                                                • (r1'' • lassociator (FA v1 · G) (FA' v2) (FA' v3))).
           { apply l3ok. }
           rewrite l3okbetter.
           clear l3 l3ok l3okbetter.
           repeat rewrite <- vassocr.
           match goal with | [ |- _ • ( _ • ( _ • ( _ • ?Hltail2)))  = _ • ( _ • ( _ • ?Hrtail2))]
                             => set (ltail2 := Hltail2); set (rtail2 := Hrtail2) end.
           assert (tails2eq: ltail2 = rtail2).
           2: { rewrite tails2eq.
                repeat rewrite vassocr.
                do 2 apply maponpaths_2.
                clear r1'' ltail2 rtail2 tails2eq.
                rewrite <- hcomp_identity_left.
                rewrite <- hcomp_identity_right.
                apply pathsinv0.
                assert (pentagon_inst := inverse_pentagon_5 (FA' v3) (FA' v2) (FA' v1) G).
                cbn in pentagon_inst.
                etrans.
                { exact pentagon_inst. }
                repeat rewrite vassocr.
                apply idpath.
                (* to find the right pentagon law - there are: associativity_pentagon, pentagon, pentagon_2,
                   inverse_pentagon, inverse_pentagon_2, inverse_pentagon_3, inverse_pentagon_4,
                   inverse_pentagon_5, inverse_pentagon_6 *)
           }
           unfold ltail2, rtail2.
           clear ltail2 rtail2 η1 η2 r1''.
           assert (pentagon_inst := inverse_pentagon_4 (FA' v3) (FA' v2) G (FA v1)).
           apply pathsinv0 in pentagon_inst.
           rewrite vassocr in pentagon_inst.
           apply (rhs_right_inv_cell _ _ _ (is_invertible_2cell_rassociator _ _ _)) in pentagon_inst.
           cbn in pentagon_inst.
           rewrite <- vassocr in pentagon_inst.
           rewrite hcomp_identity_left in pentagon_inst.
           rewrite hcomp_identity_right in pentagon_inst.
           exact pentagon_inst.
      }
      (* now the second half of the proof - however with no need for inversion of "monoidal" arrows *)
      clear l3 l4 r4 r5 r1'' r3' η1 η2.
      unfold ltail; clear ltail.
      etrans.
      { do 2 apply maponpaths.
        repeat rewrite vassocr.
        do 3 apply maponpaths_2.
        unfold l5.
        rewrite rwhisker_rwhisker_alt.
        rewrite <- vassocr.
        apply maponpaths.
        apply hcomp_hcomp'. }
      clear l5 l6.
      unfold hcomp'.
      etrans.
      { do 2 apply maponpaths.
        repeat rewrite <- vassocr.
        do 2 apply maponpaths.
        repeat rewrite vassocr.
        do 2 apply maponpaths_2.
        apply pathsinv0, rwhisker_rwhisker. }
      etrans.
      { repeat rewrite <- vassocr.
        do 5 apply maponpaths.
        unfold l7, l8.
        do 2 rewrite rwhisker_vcomp.
        apply maponpaths.
        assert (lax_monoidal_functor_assoc_inst := fmonoidal_preservesassociativity FAm v1 v2 v3).
        cbn in lax_monoidal_functor_assoc_inst.
        apply pathsinv0.
        rewrite <- vassocr in lax_monoidal_functor_assoc_inst.
        apply pathsinv0.
        exact lax_monoidal_functor_assoc_inst.
      }
      clear l7 l8.
      unfold rtail; clear rtail.
      do 2 rewrite <- rwhisker_vcomp.
      repeat rewrite vassocr.
      apply maponpaths_2.
      clear r8.
      etrans.
      2: { repeat rewrite <- vassocr.
           do 3 apply maponpaths.
           apply pathsinv0, rwhisker_lwhisker. }
      clear r7.
      etrans.
      2: { repeat rewrite vassocr. apply idpath. }
      apply maponpaths_2.
      cbn.
      (* now plain reasoning in one bicategory *)
      assert (r6ok := lwhisker_lwhisker (FA v1) (FA v2) η3).
      apply (rhs_right_inv_cell _ _ _ (is_invertible_2cell_lassociator _ _ _)) in r6ok.
      cbn in r6ok.
      assert (r6okbetter: r6 = (lassociator (FA v1) (FA v2) (G · FA' v3)
                                            • (FA v1 · FA v2 ◃ η3))
                                 • rassociator (FA v1) (FA v2) (FA v3 · G)).
      { apply r6ok. }
      rewrite r6okbetter.
      clear r6 r6ok r6okbetter.
      repeat rewrite <- vassocr.
      match goal with | [ |- _ • ( _ • ( _ • ( _ • ?Hltail2)))  = _ • ( _ • ( _ • ?Hrtail2))]
                        => set (ltail2 := Hltail2); set (rtail2 := Hrtail2) end.
      assert (tails2eq: ltail2 = rtail2).
      2: { rewrite tails2eq.
           repeat rewrite vassocr.
           do 2 apply maponpaths_2.
           clear ltail2 rtail2 tails2eq.
           rewrite <- hcomp_identity_left.
           rewrite <- hcomp_identity_right.
           apply pathsinv0.
           assert (pentagon_inst := inverse_pentagon_5 (FA' v3) G (FA v2) (FA v1)).
           etrans.
           { exact pentagon_inst. }
           repeat rewrite vassocr.
           apply idpath.
      }
      unfold ltail2, rtail2.
      rewrite <- hcomp_identity_left.
      rewrite <- hcomp_identity_right.
      clear ltail2 rtail2 η3.
      assert (pentagon_inst := inverse_pentagon_4 G (FA v3) (FA v2) (FA v1)).
      apply pathsinv0 in pentagon_inst.
      rewrite vassocr in pentagon_inst.
      apply (rhs_right_inv_cell _ _ _ (is_invertible_2cell_rassociator _ _ _)) in pentagon_inst.
      cbn in pentagon_inst.
      rewrite <- vassocr in pentagon_inst.
      exact pentagon_inst.
    Qed.


    Lemma montrafotargetbicat_disp_associatorinv_data: disp_associatorinv_data montrafotargetbicat_disp_tensor.
    Proof.
      intros v1 v2 v3 η1 η2 η3.
      cbn. (** now comes an adaptation of the code of [montrafotargetbicat_associator_aux2] from the former approach to monoidal categories *)
      unfold param_distr_bicat_pentagon_eq_body_variant_RHS, montrafotargetbicat_disp_unit,
        param_distr_bicat_triangle_eq_variant0_RHS, param_distr_bicat_pentagon_eq_body_RHS.
      rewrite hcomp_identity_left. rewrite hcomp_identity_right.
      do 6 rewrite <- lwhisker_vcomp.
      do 6 rewrite <- rwhisker_vcomp.
      repeat rewrite <- vassocr.
      match goal with | [ |- ?Hl1 • (_ • (?Hl2 • (_ • (?Hl3 • (_ • (?Hl4 • (_ • (?Hl5 • (_ • (?Hl6 • (_ • (?Hl7 • ?Hl8)))))))))))) = _]
                        => set (l1 := Hl1); set (l2 := Hl2); set (l3 := Hl3); set (l4 := Hl4);
                          set (l5 := Hl5); set (l6 := Hl6); set (l7 := Hl7); set (l8 := Hl8) end.
      match goal with | [ |- _ = ?Hr1 • (?Hr2 • (_ • (?Hr3 • (_ • (?Hr4 • (_ • (?Hr5 • (_ • (?Hr6 • (_ • (?Hr7 • (_ • ?Hr8))))))))))))]
                        => set (r1 := Hr1); set (r2 := Hr2); set (r3 := Hr3); set (r4 := Hr4);
                          set (r5 := Hr5); set (r6 := Hr6); set (r7 := Hr7); set (r8 := Hr8) end.
      change (H v1 ==> H' v1) in η1; change (H v2 ==> H' v2) in η2; change (H v3 ==> H' v3) in η3.
      (* cbn in * |- *. *)
      set (l8iso := rwhisker_with_invassociator_inv2cell v1 v2 v3).
      etrans.
      { repeat rewrite vassocr. apply idpath. }
      apply (lhs_right_invert_cell _ _ _ l8iso).
      cbn.
      match goal with | [ |-  _ = _ • ?Hl8inv ] => set (l8inv := Hl8inv) end.
      clear l8 l8iso.
      etrans.
      2: { repeat rewrite vassocr.
           do 3 apply maponpaths_2.
           repeat rewrite <- vassocr.
           do 9 apply maponpaths.
           rewrite vassocr.
           etrans.
           2: { apply maponpaths_2.
                apply pathsinv0, rwhisker_rwhisker_alt. }
           cbn.
           repeat rewrite <- vassocr.
           apply maponpaths.
           apply pathsinv0, hcomp_hcomp'. }
      unfold hcomp'.
      clear r6 r7.
      etrans.
      2: { repeat rewrite <- vassocr.
           do 11 apply maponpaths.
           rewrite vassocr.
           rewrite <- rwhisker_rwhisker.
           rewrite <- vassocr.
           apply maponpaths.
           unfold r8, l8inv.
           do 2 rewrite rwhisker_vcomp.
           apply maponpaths.
           assert (lax_monoidal_functor_assoc_inst := fmonoidal_preservesassociativity FAm v1 v2 v3).
           cbn in lax_monoidal_functor_assoc_inst.
           apply pathsinv0.
           rewrite <- vassocr in lax_monoidal_functor_assoc_inst.
           exact lax_monoidal_functor_assoc_inst.
      }
      clear r8 l8inv.
      do 2 rewrite <- rwhisker_vcomp.
      etrans.
      2: { repeat rewrite vassocr. apply idpath. }
      apply maponpaths_2.
      clear l7.
      etrans.
      { rewrite <- vassocr.
        apply maponpaths.
        apply rwhisker_lwhisker. }
      clear l6.
      repeat rewrite vassocr.
      apply maponpaths_2.
      cbn.
      match goal with | [ |- ((((?Hlhead • _) • _) • _) • _) • _  =
                              (((((?Hrhead  • _) • _) • _) • _) • _) • _ ]
                        => set (lhead := Hlhead); set (rhead := Hrhead) end.
      assert (headsok: lhead  = rhead • rassociator (FA v1) (G · FA' v2) (FA' v3)).
      2: { (* first deal with the reasoning confined to the bicategory *)
        rewrite headsok.
        repeat rewrite <- vassocr.
        apply maponpaths.
        clear η1 l1 l2 l3 r1 r2 r3 r4 lhead rhead headsok.
        etrans.
        { rewrite vassocr.
          apply maponpaths_2.
          apply rwhisker_lwhisker_rassociator. }
        etrans.
        { repeat rewrite <- vassocr. apply idpath. }
        apply maponpaths.
        clear η2 l4 r5.
        (* now as for r6 in the proof of [montrafotargetbicat_associator_aux1] *)
        assert (l5ok := lwhisker_lwhisker (FA v1) (FA v2) η3).
        apply (rhs_right_inv_cell _ _ _ (is_invertible_2cell_lassociator _ _ _)) in l5ok.
        cbn in l5ok.
        assert (l5okbetter: l5 = (lassociator (FA v1) (FA v2) (G · FA' v3)
                                              • (FA v1 · FA v2 ◃ η3))
                                   • rassociator (FA v1) (FA v2) (FA v3 · G)).
        { apply l5ok. }
        rewrite l5okbetter.
        clear l5 l5ok l5okbetter.
        repeat rewrite <- vassocr.
        match goal with | [ |- _ • ( _ • ( _ • ( _ • ?Hltail2)))  =
                                _ • ( _ • ( _ • ?Hrtail2))]
                          => set (ltail2 := Hltail2); set (rtail2 := Hrtail2) end.
        assert (tails2eq: ltail2 = rtail2).
        2: { rewrite tails2eq.
             repeat rewrite vassocr.
             do 2 apply maponpaths_2.
             clear ltail2 rtail2 tails2eq.
             rewrite <- hcomp_identity_left.
             rewrite <- hcomp_identity_right.
             assert (pentagon_inst := inverse_pentagon_5 (FA' v3) G (FA v2) (FA v1)).
             apply pathsinv0, (rhs_left_inv_cell _ _ _ (is_invertible_2cell_lassociator _ _ _)) in pentagon_inst.
             apply pathsinv0 in pentagon_inst.
             cbn in pentagon_inst.
             rewrite vassocr in pentagon_inst.
             exact pentagon_inst.
        }
        unfold ltail2, rtail2.
        rewrite <- hcomp_identity_left.
        rewrite <- hcomp_identity_right.
        clear ltail2 rtail2 η3.
        assert (pentagon_inst := inverse_pentagon_4 G (FA v3) (FA v2) (FA v1)).
        apply pathsinv0 in pentagon_inst.
        rewrite vassocr in pentagon_inst.
        apply (rhs_right_inv_cell _ _ _ (is_invertible_2cell_rassociator _ _ _)) in pentagon_inst.
        cbn in pentagon_inst.
        rewrite <- vassocr in pentagon_inst.
        apply pathsinv0 in pentagon_inst.
        exact pentagon_inst.
      }
      clear η2 η3 l4 l5 r5.
      (* now the second half of the proof - however with even more need for inversion of "monoidal" arrows *)
      unfold lhead. clear lhead.
      etrans.
      { apply maponpaths_2.
        repeat rewrite <- vassocr.
        do 2 apply maponpaths.
        unfold l3.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite vassocr.
        apply maponpaths_2.
        apply hcomp_hcomp'. }
      unfold hcomp'.
      clear l2 l3.
      cbn.
      unfold rhead. clear rhead.
      (* now as for l5 *)
      assert (r4ok := rwhisker_rwhisker (FA' v2) (FA' v3) η1).
      apply (rhs_left_inv_cell _ _ _ (is_invertible_2cell_lassociator _ _ _)) in r4ok.
      cbn in r4ok.
      assert (r4okbetter: r4 = rassociator (G · FA' v1) (FA' v2) (FA' v3)
        • ((η1 ▹ FA' v2 · FA' v3) • lassociator (FA v1 · G) (FA' v2) (FA' v3))).
      { apply r4ok. }
      rewrite r4okbetter.
      clear r4 r4ok r4okbetter.
      repeat rewrite <- vassocr.
      match goal with | [ |- _ • ( _ • ( _ • ( _ • ?Hltail3)))  =
                              _ • ( _ • ( _ • ( _ • (_ • ( _ • ( _ • ?Hrtail3))))))]
                        => set (ltail3 := Hltail3); set (rtail3 := Hrtail3) end.
      assert (tails3eq: ltail3 = rtail3).
      { (* first deal with the reasoning confined to the bicategory *)
        unfold ltail3, rtail3.
        rewrite <- hcomp_identity_left.
        rewrite <- hcomp_identity_right.
        apply inverse_pentagon_4.
      }
      rewrite tails3eq.
      repeat rewrite vassocr.
      do 2 apply maponpaths_2.
      clear η1 ltail3 rtail3 tails3eq.
      etrans.
      2: { do 2 apply maponpaths_2.
           rewrite <- vassocr.
           apply maponpaths.
           apply rwhisker_lwhisker. }
      clear r3.
      etrans.
      { rewrite <- vassocr.
        apply maponpaths.
        apply pathsinv0, lwhisker_lwhisker. }
      repeat rewrite vassocr.
      unfold l1, r1, r2.
      do 3 rewrite lwhisker_vcomp.
      clear l1 r1 r2.
      match goal with | [ |- ?Hlhead2 • _  = ((?Hrhead2  • _) • _) • _ ]
                        => set (lhead2 := Hlhead2); set (rhead2 := Hrhead2) end.
      assert (heads2ok: lhead2 = rhead2 • (G ◃ rassociator (FA' v1) (FA' v2) (FA' v3))).
      2: { (* first deal with the reasoning confined to the bicategory *)
        rewrite heads2ok.
        repeat rewrite <- vassocr.
        apply maponpaths.
        clear lhead2 rhead2 heads2ok.
        cbn.
        rewrite <- hcomp_identity_left.
        rewrite <- hcomp_identity_right.
        apply inverse_pentagon_5.
      }
      unfold rhead2.
      rewrite lwhisker_vcomp.
      apply maponpaths.
      clear lhead2 rhead2.
      assert (lax_monoidal_functor_assoc_inst := fmonoidal_preservesassociativity FA'm v1 v2 v3).
      cbn in lax_monoidal_functor_assoc_inst.
      transparent assert (aux1iso : (invertible_2cell (FA' (v1 ⊗ (v2 ⊗ v3)))
                                                      (FA' v1 · FA' (v2 ⊗ v3)))).
      { use make_invertible_2cell.
        - exact (pr1 (fmonoidal_preservestensorstrongly FA'm v1 (v2 ⊗ v3))).
        - change (is_z_isomorphism (pr1 (fmonoidal_preservestensorstrongly FA'm v1 (v2 ⊗ v3)))).
          apply is_z_isomorphism_inv.
      }
      apply (lhs_left_invert_cell _ _ _ aux1iso).
      cbn.
      etrans.
      2: { repeat rewrite vassocr. apply idpath. }
      apply pathsinv0, lassociator_to_rassociator_post.
      transparent assert (aux2iso : (invertible_2cell (FA' (v1 ⊗ v2) · FA' v3)
                                                      ((FA' v1 · FA' v2) · FA' v3))).
      { use make_invertible_2cell.
        - exact ((pr1 (fmonoidal_preservestensorstrongly FA'm v1 v2)) ▹ FA' v3).
        - apply is_invertible_2cell_rwhisker.
          change (is_z_isomorphism  (pr1 (fmonoidal_preservestensorstrongly FA'm v1 v2))).
          apply is_z_isomorphism_inv.
      }
      apply (lhs_right_invert_cell _ _ _ aux2iso).
      cbn.
      transparent assert (aux3iso : (invertible_2cell (FA' ((v1 ⊗ v2) ⊗ v3))
                                                      (FA' (v1 ⊗ v2) · FA' v3))).
      { use make_invertible_2cell.
        - exact (pr1 (fmonoidal_preservestensorstrongly FA'm (v1 ⊗ v2) v3)).
        - change (is_z_isomorphism (pr1 (fmonoidal_preservestensorstrongly FA'm (v1 ⊗_{ Mon_V} v2) v3))).
          apply is_z_isomorphism_inv.
      }
      apply (lhs_right_invert_cell _ _ _ aux3iso).
      cbn.
      transparent assert (aux4iso : (invertible_2cell (FA' (v1 ⊗ (v2 ⊗ v3)))
                                                      (FA' ((v1 ⊗ v2) ⊗ v3)))).
      { use make_invertible_2cell.
        - exact (# FA' (αinv_{ Mon_V} v1 v2 v3)).
        - change (is_z_isomorphism (# FA' (αinv_{ Mon_V} v1 v2 v3))).
          apply functor_on_is_z_isomorphism.
          exists (α_{ Mon_V} v1 v2 v3).
          destruct (monoidal_associatorisolaw Mon_V v1 v2 v3); split; assumption.
      }
      apply (lhs_right_invert_cell _ _ _ aux4iso).
      cbn.
      repeat rewrite <- vassocr.
      transparent assert (aux5iso : (invertible_2cell (FA' v1 · FA' (v2 ⊗ v3))
                                                      (FA' v1 · (FA' v2 · FA' v3)))).
      { use make_invertible_2cell.
        - exact (FA' v1 ◃ (pr1 (fmonoidal_preservestensorstrongly FA'm v2 v3))).
        - apply is_invertible_2cell_lwhisker.
          change (is_z_isomorphism (pr1 (fmonoidal_preservestensorstrongly FA'm v2 v3))).
          apply is_z_isomorphism_inv.
      }
      apply pathsinv0, (lhs_left_invert_cell _ _ _ aux5iso).
      cbn.
      clear aux1iso aux2iso aux3iso aux4iso aux5iso.
      apply pathsinv0, rassociator_to_lassociator_pre.
      apply pathsinv0.
      repeat rewrite vassocr.
      exact lax_monoidal_functor_assoc_inst.
    Qed.

    Lemma montrafotargetbicat_disp_associator_iso: disp_associator_iso montrafotargetbicat_disp_associator_data montrafotargetbicat_disp_associatorinv_data.
    Proof.
      intros v1 v2 v3 η1 η2 η3.
      (** now we benefit from working in a displayed monoidal category *)
      split; apply trafotargetbicat_disp_cells_isaprop.
    Qed.

    Lemma montrafotargetbicat_disp_associator_law: disp_associator_law montrafotargetbicat_disp_associator_data montrafotargetbicat_disp_associatorinv_data.
    Proof.
      (** now we benefit from working in a displayed monoidal category *)
      repeat (split; try (red; intros; apply trafotargetbicat_disp_cells_isaprop)); try apply trafotargetbicat_disp_cells_isaprop.
    Qed.

    Lemma montrafotargetbicat_disp_leftunitorinv_data: disp_leftunitorinv_data montrafotargetbicat_disp_tensor montrafotargetbicat_disp_unit.
    Proof.
      intros v η.
      cbn. (** now comes an adaptation of the code of [montrafotargetbicat_left_unitor_aux2] from the former approach to monoidal categories *)
      unfold param_distr_bicat_pentagon_eq_body_variant_RHS, montrafotargetbicat_disp_unit,
        param_distr_bicat_triangle_eq_variant0_RHS, param_distr_bicat_pentagon_eq_body_RHS.
      rewrite hcomp_identity_left. rewrite hcomp_identity_right.
      do 3 rewrite <- rwhisker_vcomp.
      repeat rewrite <- vassocr.
      apply pathsinv0.
      match goal with | [ |- ?Hl1 • (?Hl2 • (_ • (?Hl3 • (_ • (_ • (?Hl4 • (_ • (?Hl5 • (_ • ?Hl6))))))))) = _ • ?Hr2]
                        => set (l1 := Hl1); set (l2 := Hl2); set (l3 := Hl3); set (l4 := Hl4);
                          set (l5 := Hl5); set (l6 := Hl6); set (r2 := Hr2) end.
      change (H v ==> H' v) in η.
      set (l1iso := lwhisker_with_invlunitor_inv2cell v).
      apply (lhs_left_invert_cell _ _ _ l1iso).
      cbn.
      set (l2iso := lwhisker_with_μ_inv_inv2cell I_{Mon_V} v).
      apply (lhs_left_invert_cell _ _ _ l2iso).
      cbn.
      apply (lhs_left_invert_cell _ _ _ (is_invertible_2cell_lassociator _ _ _)).
      cbn.
      set (l3iso := lwhisker_rwhisker_with_ϵ_inv_inv2cell v).
      apply (lhs_left_invert_cell _ _ _ l3iso).
      cbn.
      match goal with | [ |- _ = ?Hl3inv • (_ • (?Hl2inv • (?Hl1inv • _)))]
                        => set (l1inv := Hl1inv); set (l2inv := Hl2inv); set (l3inv := Hl3inv) end.
      clear l1 l2 l3 l1iso l2iso l3iso.
      etrans.
      2: { repeat rewrite vassocr.
           do 4 apply maponpaths_2.
           unfold l3inv.
           apply rwhisker_lwhisker_rassociator. }
      etrans.
      2: { do 2 apply maponpaths_2.
           repeat rewrite <- vassocr.
           apply maponpaths.
           unfold l2inv, l1inv.
           do 2 rewrite lwhisker_vcomp.
           apply maponpaths.
           rewrite vassocr.
           assert (lax_monoidal_functor_unital_inst := fmonoidal_preservesleftunitality FA'm v).
           cbn in lax_monoidal_functor_unital_inst.
           apply pathsinv0.
           exact lax_monoidal_functor_unital_inst.
      }
      clear l1inv l2inv l3inv.
      etrans.
      { do 2 apply maponpaths.
        repeat rewrite vassocr.
        do 3 apply maponpaths_2.
        apply rwhisker_rwhisker_alt. }
      cbn.
      etrans.
      { do 2 apply maponpaths.
        do 2 apply maponpaths_2.
        rewrite <- vassocr.
        apply maponpaths.
        apply hcomp_hcomp'. }
      clear l4 l5.
      unfold hcomp'.
      set (r2iso := rwhisker_with_invlunitor_inv2cell v).
      apply pathsinv0.
      apply (lhs_right_invert_cell _ _ _ r2iso).
      apply pathsinv0.
      cbn.
      clear r2 r2iso.
      etrans.
      { repeat rewrite <- vassocr.
        do 4 apply maponpaths.
        rewrite vassocr.
        rewrite <- rwhisker_rwhisker.
        repeat rewrite <- vassocr.
        apply maponpaths.
        unfold l6.
        do 2 rewrite rwhisker_vcomp.
        apply maponpaths.
        apply pathsinv0.
        rewrite vassocr.
        assert (lax_monoidal_functor_unital_inst := fmonoidal_preservesleftunitality FAm v).
        cbn in lax_monoidal_functor_unital_inst.
        apply pathsinv0.
        exact lax_monoidal_functor_unital_inst.
      }
      clear l6. (* now only admin tasks in bicategory: the goal is the same as at that
                   position in [montrafotargetbicat_left_unitor_aux1] *)
      rewrite lunitor_lwhisker.
      apply maponpaths.
      apply (lhs_left_invert_cell _ _ _ (rwhisker_with_linvunitor_inv2cell v)).
      cbn.
      rewrite lunitor_triangle.
      rewrite vcomp_lunitor.
      rewrite vassocr.
      apply maponpaths_2.
      apply (lhs_left_invert_cell _ _ _ (is_invertible_2cell_rassociator _ _ _)).
      cbn.
      apply pathsinv0, lunitor_triangle.
    Qed.

    Lemma montrafotargetbicat_disp_leftunitor_iso: disp_leftunitor_iso montrafotargetbicat_disp_leftunitor_data montrafotargetbicat_disp_leftunitorinv_data.
    Proof.
      intros v η.
      (** now we benefit from working in a displayed monoidal category *) split; apply trafotargetbicat_disp_cells_isaprop.
    Qed.

    Lemma montrafotargetbicat_disp_leftunitor_law: disp_leftunitor_law montrafotargetbicat_disp_leftunitor_data montrafotargetbicat_disp_leftunitorinv_data.
    Proof.
      split.
      - red. intros. apply trafotargetbicat_disp_cells_isaprop.
      - exact montrafotargetbicat_disp_leftunitor_iso.
    Qed.

    Lemma montrafotargetbicat_disp_rightunitorinv_data: disp_rightunitorinv_data montrafotargetbicat_disp_tensor montrafotargetbicat_disp_unit.
    Proof.
      intros v η.
      apply pathsinv0. cbn. (** now comes an adaptation of the code of [montrafotargetbicat_right_unitor_aux2] from the former approach to monoidal categories *)
      unfold param_distr_bicat_pentagon_eq_body_variant_RHS, montrafotargetbicat_disp_unit,
        param_distr_bicat_triangle_eq_variant0_RHS, param_distr_bicat_pentagon_eq_body_RHS.
      rewrite hcomp_identity_left. rewrite hcomp_identity_right.
      do 3 rewrite <- lwhisker_vcomp.
      repeat rewrite <- vassocr.
      match goal with | [ |- ?Hl1 • (?Hl2 • (_ • (?Hl3 • (_ • (?Hl4 • (_ • (_ • (?Hl5 • (_ • ?Hl6))))))))) = _ • ?Hr2]
                        => set (l1 := Hl1); set (l2 := Hl2); set (l3 := Hl3); set (l4 := Hl4);
                          set (l5 := Hl5); set (l6 := Hl6); set (r2 := Hr2) end.
      change (H v ==> H' v) in η.
      set (l1iso := lwhisker_with_invrunitor_inv2cell v).
      apply (lhs_left_invert_cell _ _ _ l1iso).
      cbn.
      clear l1 l1iso.
      set (l2iso := lwhisker_with_μ_inv_inv2cell v I_{Mon_V}).
      apply (lhs_left_invert_cell _ _ _ l2iso).
      cbn.
      clear l2 l2iso.
      apply (lhs_left_invert_cell _ _ _ (is_invertible_2cell_lassociator _ _ _)).
      cbn.
      etrans.
      2: { repeat rewrite <- vassocr.
           apply maponpaths.
           rewrite vassocr.
           apply maponpaths_2.
           rewrite lwhisker_vcomp.
           apply maponpaths.
           assert (lax_monoidal_functor_unital_inst := fmonoidal_preservesrightunitality FA'm v).
           cbn in lax_monoidal_functor_unital_inst.
           apply pathsinv0 in lax_monoidal_functor_unital_inst.
           set (aux1iso := lwhisker_with_ϵ_inv2cell v).
           rewrite <- vassocr in lax_monoidal_functor_unital_inst.
           apply pathsinv0 in lax_monoidal_functor_unital_inst.
           apply (rhs_left_inv_cell _ _ _ aux1iso) in lax_monoidal_functor_unital_inst.
           unfold inv_cell in lax_monoidal_functor_unital_inst.
           apply pathsinv0.
           exact lax_monoidal_functor_unital_inst.
      }
      cbn. (* same goal as in [montrafotargetbicat_right_unitor_aux1],
              except l_i -> l_{i+1} for i=2,3,4,5, and l6 becomes r2 on the other side *)
      etrans.
      2: { rewrite vassocr.
           apply maponpaths_2.
           rewrite <- lwhisker_vcomp.
           rewrite vassocr.
           apply maponpaths_2.
           apply pathsinv0.
           apply lwhisker_lwhisker_rassociator. }
      etrans.
      2: { repeat rewrite <- vassocr.
           apply maponpaths.
           rewrite vassocr.
           apply maponpaths_2.
           apply pathsinv0, runitor_triangle. }
      etrans.
      2: { apply maponpaths.
           rewrite vassocr.
           rewrite <- vcomp_runitor.
           apply idpath. }
      etrans.
      2: { rewrite vassocr.
           apply maponpaths_2.
           rewrite vassocr.
           apply maponpaths_2.
           apply hcomp_hcomp'. }
      unfold hcomp.
      etrans.
      2: { repeat rewrite <- vassocr. apply idpath. }
      apply maponpaths.
      clear l3.
      etrans.
      { repeat rewrite vassocr.
        do 5 apply maponpaths_2.
        apply lwhisker_lwhisker_rassociator. }
      repeat rewrite <- vassocr.
      apply maponpaths.
      clear l4.
      cbn.
      etrans.
      { repeat rewrite vassocr.
        do 4 apply maponpaths_2.
        apply runitor_triangle. }
      (* now we put an end to the diversion from the goal in [montrafotargetbicat_right_unitor_aux1] *)
      set (r2iso := rwhisker_with_invrunitor_inv2cell v).
      apply pathsinv0, (lhs_right_invert_cell _ _ _ r2iso), pathsinv0.
      cbn.
      clear r2 r2iso.
      (* resume analogous proof *)
      etrans.
      2: { apply id2_right. }
      repeat rewrite <- vassocr.
      apply maponpaths.
      etrans.
      { apply maponpaths.
        rewrite vassocr.
        apply maponpaths_2.
        apply rwhisker_lwhisker. }
      cbn.
      clear l5.
      etrans.
      { apply maponpaths.
        rewrite <- vassocr.
        apply maponpaths.
        unfold l6.
        do 2 rewrite rwhisker_vcomp.
        apply maponpaths.
        assert (lax_monoidal_functor_unital_inst := fmonoidal_preservesrightunitality FAm v).
        cbn in lax_monoidal_functor_unital_inst.
        apply pathsinv0 in lax_monoidal_functor_unital_inst.
        rewrite vassocr.
        apply pathsinv0.
        exact lax_monoidal_functor_unital_inst.
      }
      clear l6. (* now only pure bicategory reasoning *)
      set (auxiso := lwhisker_with_linvunitor_inv2cell v).
      apply (lhs_left_invert_cell _ _ _ auxiso).
      cbn.
      rewrite id2_right.
      clear auxiso.
      apply runitor_rwhisker.
    Qed.

    Lemma montrafotargetbicat_disp_rightunitor_iso: disp_rightunitor_iso montrafotargetbicat_disp_rightunitor_data montrafotargetbicat_disp_rightunitorinv_data.
    Proof.
      intros v η.
      (** now we benefit from working in a displayed monoidal category *) split; apply trafotargetbicat_disp_cells_isaprop.
    Qed.

    Lemma montrafotargetbicat_disp_rightunitor_law: disp_rightunitor_law montrafotargetbicat_disp_rightunitor_data montrafotargetbicat_disp_rightunitorinv_data.
    Proof.
      split.
      - red. intros. apply trafotargetbicat_disp_cells_isaprop.
      - exact montrafotargetbicat_disp_rightunitor_iso.
    Qed.

    Definition montrafotargetbicat_disp_monoidal_data: disp_monoidal_data montrafotargetbicat_disp Mon_V.
    Proof.
      exists montrafotargetbicat_disp_tensor.
      exists montrafotargetbicat_disp_unit.
      exists montrafotargetbicat_disp_leftunitor_data.
      exists montrafotargetbicat_disp_leftunitorinv_data.
      exists montrafotargetbicat_disp_rightunitor_data.
      exists montrafotargetbicat_disp_rightunitorinv_data.
      exists montrafotargetbicat_disp_associator_data.
      exact montrafotargetbicat_disp_associatorinv_data.
    Defined.

    Definition montrafotargetbicat_disp_monoidal: disp_monoidal montrafotargetbicat_disp Mon_V.
    Proof.
      exists montrafotargetbicat_disp_monoidal_data.
      split.
      exact montrafotargetbicat_disp_leftunitor_law.
      split; [ exact montrafotargetbicat_disp_rightunitor_law |].
      split; [ exact montrafotargetbicat_disp_associator_law |].
      (** now we benefit from working in a displayed monoidal category *)
      split; red; intros; apply trafotargetbicat_disp_cells_isaprop.
    Defined.

    Definition parameterized_distributivity_bicat_nat : UU := H ⟹ H'.
    Definition parameterized_distributivity_bicat_nat_funclass (δ : parameterized_distributivity_bicat_nat):
      ∏ v : V, H v --> H' v := pr1 δ.
    Coercion parameterized_distributivity_bicat_nat_funclass : parameterized_distributivity_bicat_nat >-> Funclass.

    Definition param_distr_bicat_triangle_eq_variant0 (δ : parameterized_distributivity_bicat_nat): UU :=
      δ I_{Mon_V} = param_distr_bicat_triangle_eq_variant0_RHS.

    Definition param_distr_bicat_pentagon_eq_variant (δ : parameterized_distributivity_bicat_nat): UU := ∏ (v w : V),
        δ (v ⊗ w) = param_distr_bicat_pentagon_eq_body_variant_RHS v w (δ v) (δ w).

    Section IntoMonoidalSectionBicat.

      Context (δ: parameterized_distributivity_bicat_nat).
      Context (δtr_eq: param_distr_bicat_triangle_eq_variant0 δ)
              (δpe_eq: param_distr_bicat_pentagon_eq_variant δ).

      (** using sections already for this direction *)
      Lemma param_distr_bicat_to_monoidal_section_data:
        smonoidal_data Mon_V montrafotargetbicat_disp_monoidal
                       (nat_trafo_to_section_bicat a0 a0' H H' δ).
      Proof.
        split.
        - intros v w. cbn.
          rewrite hcomp_identity_left, hcomp_identity_right.
          rewrite (functor_id FA), (functor_id FA').
          cbn.
          rewrite lwhisker_id2, id2_rwhisker.
          rewrite id2_left, id2_right.
          apply pathsinv0, δpe_eq.
        - cbn.
          rewrite hcomp_identity_left, hcomp_identity_right.
          rewrite (functor_id FA), (functor_id FA').
          cbn.
          rewrite lwhisker_id2, id2_rwhisker.
          rewrite id2_left, id2_right.
          apply pathsinv0, δtr_eq.
      Qed.
      (** the two equations were thus exactly the ingredients for the data of a monoidal section *)

      Lemma param_distr_bicat_to_monoidal_section_laws: smonoidal_laxlaws Mon_V montrafotargetbicat_disp_monoidal param_distr_bicat_to_monoidal_section_data.
      Proof.
        repeat split; red; intros; apply trafotargetbicat_disp_cells_isaprop.
      Qed.

      Lemma param_distr_bicat_to_monoidal_section_strongtensor:
        smonoidal_strongtensor Mon_V montrafotargetbicat_disp_monoidal
                               (smonoidal_preserves_tensor Mon_V montrafotargetbicat_disp_monoidal
                                                           param_distr_bicat_to_monoidal_section_data).
      Proof.
        intros v w.
        use tpair.
        - cbn. (** now as for [param_distr_bicat_to_monoidal_section_data] *)
          rewrite hcomp_identity_left, hcomp_identity_right.
          rewrite (functor_id FA), (functor_id FA').
          cbn.
          rewrite lwhisker_id2, id2_rwhisker.
          rewrite id2_left, id2_right.
          apply δpe_eq.
        - split; apply trafotargetbicat_disp_cells_isaprop.
      Qed.

      Lemma param_distr_bicat_to_monoidal_section_strongunit:
        smonoidal_strongunit Mon_V montrafotargetbicat_disp_monoidal
                             (smonoidal_preserves_unit Mon_V montrafotargetbicat_disp_monoidal
                                                       param_distr_bicat_to_monoidal_section_data).
      Proof.
        use tpair.
        - cbn.
          rewrite hcomp_identity_left, hcomp_identity_right.
          rewrite (functor_id FA), (functor_id FA').
          cbn.
          rewrite lwhisker_id2, id2_rwhisker.
          rewrite id2_left, id2_right.
          apply δtr_eq.
        - split; apply trafotargetbicat_disp_cells_isaprop.
      Qed.

    End IntoMonoidalSectionBicat.

(* not migrated, and also parameterized_distributivity_bicat not yet defined (taking into account the variants!)
Definition smf_from_param_distr_bicat:
  parameterized_distributivity_bicat -> strong_monoidal_functor Mon_V montrafotargetbicat_moncat.
Proof.
  intro δs.
  induction δs as [δ [δtr_eq δpe_eq]].
  exact (smf_from_param_distr_parts_bicat δ δtr_eq δpe_eq).
Defined.
 *)

    (** the other direction, essentially dependent on sections *)
    Section FromMonoidalSectionBicat.

      Context (sd: section_disp montrafotargetbicat_disp).
      Context (ms: smonoidal_data Mon_V montrafotargetbicat_disp_monoidal sd).
      (** since the laws were anyway trivial to establish, we do not need more than [smonoidal_data] *)

      Definition δ_from_ms: H ⟹ H' := section_to_nat_trafo_bicat _ _ _ _ sd.

      Lemma δtr_eq_from_ms: param_distr_bicat_triangle_eq_variant0 δ_from_ms.
      Proof.
        red.
        assert (aux := smonoidal_preserves_unit _ _ ms).
        cbn in aux.
        rewrite hcomp_identity_left, hcomp_identity_right in aux.
        rewrite (functor_id FA), (functor_id FA') in aux.
        cbn in aux.
        rewrite lwhisker_id2, id2_rwhisker in aux.
        rewrite id2_left, id2_right in aux.
        apply pathsinv0. exact aux.
      Qed.

      Lemma δpe_eq_from_ms: param_distr_bicat_pentagon_eq_variant δ_from_ms.
      Proof.
        intros v w.
        assert (aux := smonoidal_preserves_tensor _ _ ms v w).
        cbn in aux.
        rewrite hcomp_identity_left, hcomp_identity_right in aux.
        rewrite (functor_id FA), (functor_id FA') in aux.
        cbn in aux.
        rewrite lwhisker_id2, id2_rwhisker in aux.
        rewrite id2_left, id2_right in aux.
        apply pathsinv0. exact aux.
      Qed.

      (* TODO: roundtrip lemmas *)


    End FromMonoidalSectionBicat.

    Section RoundtripForSDData.

      Local Definition source_type: UU := ∑ δ: parameterized_distributivity_bicat_nat,
            param_distr_bicat_triangle_eq_variant0 δ ×
              param_distr_bicat_pentagon_eq_variant δ.
      Local Definition target_type: UU := ∑ sd: section_disp montrafotargetbicat_disp,
            smonoidal_data Mon_V montrafotargetbicat_disp_monoidal sd.

      Local Definition source_to_target : source_type -> target_type.
      Proof.
        intro ass. destruct ass as [δ [δtr_eq δpe_eq]].
        exists (nat_trafo_to_section_bicat a0 a0' H H' δ).
        apply param_distr_bicat_to_monoidal_section_data; [exact δtr_eq | exact δpe_eq].
      Defined.

      Local Definition target_to_source : target_type -> source_type.
      Proof.
        intro ass. destruct ass as [sd ms].
        exists (δ_from_ms sd).
        split; [apply δtr_eq_from_ms | apply δpe_eq_from_ms]; exact ms.
      Defined.

      Local Lemma roundtrip1 (ass: source_type): target_to_source (source_to_target ass) = ass.
      Proof.
        destruct ass as [δ [δtr_eq δpe_eq]].
        use total2_paths_f.
        - cbn.
          unfold δ_from_ms.
          apply roundtrip1_with_sections_bicat.
        - cbn.
          match goal with |- @paths ?ID _ _ => set (goaltype := ID); simpl in goaltype end.
          assert (Hprop: isaprop goaltype).
          2: { apply Hprop. }
          apply isapropdirprod.
          + unfold param_distr_bicat_triangle_eq_variant0.
            apply C.
          + unfold param_distr_bicat_pentagon_eq_variant.
            apply impred. intro v.
            apply impred. intro w.
            apply C.
      Qed.

      Local Lemma roundtrip2 (ass: target_type): source_to_target (target_to_source ass) = ass.
      Proof.
        destruct ass as [sd ms].
        use total2_paths_f.
        - cbn.
          unfold δ_from_ms.
          apply roundtrip2_with_sections_bicat.
        - cbn.
          match goal with |- @paths ?ID _ _ => set (goaltype := ID); simpl in goaltype end.
          assert (Hprop: isaprop goaltype).
          2: { apply Hprop. }
          apply isapropdirprod.
          + unfold section_preserves_tensor_data.
            apply impred. intro v.
            apply impred. intro w.
            apply trafotargetbicat_disp_cells_isaprop.
          + unfold section_preserves_unit.
            apply trafotargetbicat_disp_cells_isaprop.
      Qed.

    End RoundtripForSDData.


  End FunctorViaBicat.

  Section Functor.

    Context {A A': category}.

    Context {FA: functor V (cat_of_endofunctors A)}.
    Context {FA': functor V (cat_of_endofunctors A')}.

    Context (FAm: fmonoidal Mon_V (monoidal_of_endofunctors A) FA).
    Context (FA'm: fmonoidal Mon_V (monoidal_of_endofunctors A') FA').

    Context (G : A ⟶ A').

    Let H := param_distributivity'_dom(FA':=FA') A A' G.
    Let H' := param_distributivity'_codom(FA:=FA) A A' G.

    Goal H = Main.H(C:=bicat_of_cats)(FA':=FA') G.
    Proof.
      apply idpath.
    Qed.

    Goal H' = Main.H'(C:=bicat_of_cats)(FA:=FA) G.
    Proof.
      apply idpath.
    Qed.

    Definition parameterized_distributivity'_nat_as_instance
               (δtr: parameterized_distributivity'_nat(FA:=FA)(FA':=FA') A A' G):
      parameterized_distributivity_bicat_nat(FA:=FA)(FA':=FA') G := δtr.

    Definition montrafotarget_disp: disp_cat V :=
      montrafotargetbicat_disp(C:=bicat_of_cats)(FA:=FA)(FA':=FA') G.

    Definition montrafotarget_totalcat: category :=
      total_category montrafotarget_disp.

    Goal montrafotarget_disp = trafotargetbicat_disp(C:=bicat_of_cats) A A' H H'.
    Proof.
      apply idpath.
    Qed.

   Definition montrafotarget_disp_monoidal: disp_monoidal montrafotarget_disp Mon_V
     := montrafotargetbicat_disp_monoidal(C:=bicat_of_cats)(a0:=A)(a0':=A') FAm FA'm G.

   Definition montrafotarget_monoidal: monoidal montrafotarget_totalcat :=
     total_monoidal montrafotarget_disp_monoidal.

    Section IntoMonoidalSection.

      Context (δs : parameterized_distributivity' Mon_V A A' FAm FA'm G).
      Let δ := pr1 δs.
      Let δtr_eq := pr12 δs.
      Let δpe_eq := pr22 δs.

      Definition montrafotarget_section_disp : section_disp montrafotarget_disp
        := nat_trafo_to_section_bicat(C0:=V)(C:=bicat_of_cats) A A' H H' δ.

      Lemma δtr_eq': param_distr_bicat_triangle_eq_variant0 FAm FA'm G δ.
      Proof.
        apply param_distr'_triangle_eq_variant0_follows in δtr_eq.
        red in δtr_eq |- *.
        unfold param_distr'_triangle_eq_variant0_RHS in δtr_eq.
        unfold param_distr_bicat_triangle_eq_variant0_RHS.
        cbn in δtr_eq |- *.
        etrans.
        { exact δtr_eq. }
        rewrite (nat_trans_comp_id_right A' (functor_composite G (functor_identity A')) G).
        (* show_id_type. *)
        apply (nat_trans_eq A').
        intro a.
        cbn.
        rewrite id_right, id_left.
        rewrite (functor_id (FA' I_{ Mon_V})), id_left.
        apply idpath.
      Qed.

      Lemma δpe_eq': param_distr_bicat_pentagon_eq_variant FAm FA'm G δ.
      Proof.
        intros v w.
        set (δpe_eq_inst := δpe_eq v w).
        apply param_distr'_pentagon_eq_body_variant_follows in δpe_eq_inst.
        unfold param_distr_bicat_pentagon_eq_body_variant_RHS, param_distr_bicat_pentagon_eq_body_RHS.
        unfold param_distr'_pentagon_eq_body_variant, param_distr'_pentagon_eq_body_variant_RHS in δpe_eq_inst.
        cbn in δpe_eq_inst |- *.
        etrans.
        { exact δpe_eq_inst. }
        clear δpe_eq_inst.
        apply (nat_trans_eq A').
        intro a.
        cbn.
        do 3 rewrite id_left. rewrite id_right.
        rewrite (functor_id (FA' (v ⊗_{ Mon_V} w))), id_left.
        apply idpath.
      Qed.

      Definition param_distr'_to_monoidal_section_data:
        smonoidal_data Mon_V montrafotarget_disp_monoidal montrafotarget_section_disp :=
        param_distr_bicat_to_monoidal_section_data(C:=bicat_of_cats) FAm FA'm G
                             (parameterized_distributivity'_nat_as_instance δ) δtr_eq' δpe_eq'.

      Definition param_distr'_to_monoidal_section_laws:
        smonoidal_laxlaws Mon_V montrafotarget_disp_monoidal
                          param_distr'_to_monoidal_section_data :=
        param_distr_bicat_to_monoidal_section_laws FAm FA'm G δ δtr_eq' δpe_eq'.

      Definition param_distr'_to_monoidal_section_strongtensor:
        smonoidal_strongtensor Mon_V montrafotarget_disp_monoidal
                               (smonoidal_preserves_tensor Mon_V
                                                           montrafotarget_disp_monoidal
                                                           param_distr'_to_monoidal_section_data) :=
        param_distr_bicat_to_monoidal_section_strongtensor FAm FA'm G δ δtr_eq' δpe_eq'.

      Definition param_distr'_to_monoidal_section_strongunit:
        smonoidal_strongunit Mon_V montrafotarget_disp_monoidal
                             (smonoidal_preserves_unit Mon_V
                                                       montrafotarget_disp_monoidal
                                                       param_distr'_to_monoidal_section_data) :=
        param_distr_bicat_to_monoidal_section_strongunit FAm FA'm G δ δtr_eq' δpe_eq'.

      Definition param_distr'_to_functor: V ⟶ montrafotarget_totalcat :=
        section_functor montrafotarget_section_disp.

      Definition param_distr'_to_smf: fmonoidal Mon_V montrafotarget_monoidal param_distr'_to_functor.
      Proof.
        apply sectionfunctor_fmonoidal.
        use tpair.
        - use tpair.
          + apply param_distr'_to_monoidal_section_data.
          + apply param_distr'_to_monoidal_section_laws.
        - split.
          + apply param_distr'_to_monoidal_section_strongtensor.
          + apply param_distr'_to_monoidal_section_strongunit.
      Defined.

End IntoMonoidalSection.

Section FromMonoidalSection.

      Context {sd: section_disp montrafotarget_disp}.
      Context (ms: smonoidal_data Mon_V montrafotarget_disp_monoidal sd).
      (** since the laws were anyway trivial to establish, we do not need more than [smonoidal_data] *)

      Definition δ'_from_ms: H ⟹ H' := section_to_nat_trafo_bicat _ _ _ _ sd.

      Lemma δtr'_eq_from_ms: param_distr'_triangle_eq Mon_V A A' FAm FA'm G δ'_from_ms.
      Proof.
        apply param_distr'_triangle_eq_variant0_implies.
        assert (aux := δtr_eq_from_ms(C:=bicat_of_cats) FAm FA'm G sd ms).
        unfold param_distr'_triangle_eq_variant0.
        unfold param_distr'_triangle_eq_variant0_RHS.
        red in aux.
        unfold param_distr_bicat_triangle_eq_variant0_RHS in aux.
        etrans.
        { exact aux. }
        cbn.
        rewrite (nat_trans_comp_id_right A' (functor_composite G (functor_identity A')) G).
        apply (nat_trans_eq A').
        intro a.
        cbn.
        rewrite id_right, id_left.
        rewrite (functor_id (FA' I_{ Mon_V})), id_left.
        apply idpath.
      Qed.

      Lemma δpe'_eq_from_ms: param_distr'_pentagon_eq Mon_V A A' FAm FA'm G δ'_from_ms.
      Proof.
        intros v w.
        apply param_distr'_pentagon_eq_body_variant_implies.
        assert (aux := δpe_eq_from_ms(C:=bicat_of_cats) FAm FA'm G sd ms v w).
        red.
        etrans.
        { exact aux. }
        clear aux.
        unfold param_distr_bicat_pentagon_eq_body_variant_RHS, param_distr_bicat_pentagon_eq_body_RHS.
        unfold param_distr'_pentagon_eq_body_variant_RHS.
        apply (nat_trans_eq A').
        intro a.
        cbn.
        do 3 rewrite id_left. rewrite id_right.
        rewrite (functor_id (FA' (v ⊗_{ Mon_V} w))), id_left.
        apply idpath.
      Qed.


End FromMonoidalSection.

End Functor.

End Main.
