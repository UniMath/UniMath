(*
In this file we construct the category whose objects are pairs, consisting of a set and a subset of that set, as a displayed category.
Furthermore, we show that this displayed category is monoidal
and we construct a monoidal section which maps a set X to (X,X) (where the second X is considered to be maximal subset of X).
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalSectionsWhiskered.


Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Monoidal.CartesianMonoidalCategoriesWhiskered.

Section Subsets.

  Definition subset (X : hSet) : UU := X -> hProp.

  Definition subset_to_elements' {X : hSet} (U : subset X)
    : UU := ∑ x : X, U x.

  Definition subset_to_elements {X : hSet} (U : subset X) : hSet.
  Proof.
    exists (subset_to_elements' U).
    apply isaset_total2.
    - apply X.
    - intro.
      apply isasetaprop.
      apply U.
  Defined.

  Definition subset_to_elements_in_entireset
             {X : hSet} {U : subset X}
             (x : subset_to_elements U)
    : X := pr1 x.

  Definition subset_in_product {X Y : hSet}
             (U : subset X) (V : subset Y)
    : subset (setdirprod X Y).
  Proof.
    intro xy.
    exists (U (pr1 xy) × V (pr2 xy)).
    apply isapropdirprod. apply U. apply V.
  Defined.

  Definition subset_in_product' {X Y : hSet} (UV : subset (setdirprod X Y))
    : subset X × subset Y.
  Proof.
    split.
    - intro x.
      exists (∃ y : Y, UV (x,,y)).
      apply ishinh.
    - intro y.
      exists (∃ x : X, UV (x,,y)).
      apply ishinh.
  Defined.

  Definition singleton {X : hSet} (x : X) : subset X.
  Proof.
    intro x'.
    exists (x'=x).
    apply X.
  Defined.

  Definition intersection {X : hSet} (U V : subset X) : subset X
    := λ x, U x ∧ V x.

  Lemma intersection_commutative {X : hSet} (U V : subset X)
    : ∏ x : X, (intersection U V) x -> (intersection V U) x.
  Proof.
    intros ? p.
    exact (transportf _ (iscomm_hconj (U x) (V x)) p).
  Qed.

  Definition union_data {X I : hSet} (U : I -> subset X) :  X -> UU
    := λ x, ∃ i:I, U i x.

  Definition union {X I : hSet} (U : I -> subset X) : subset X.
  Proof.
    intro x.
    exists (union_data U x).
    apply impred_isaprop ; intro i.
    apply isapropimpl.
    apply i.
  Defined.

  Definition emptysubset (X : hSet) : subset X
    := λ x, hfalse.

  Definition entiresubset (X : hSet) : subset X
    := λ x, htrue.

  Definition contained {X : hSet} (U V : subset X) : UU
    := ∏ x : X, U x -> V x.

  Lemma contained_reflexive {X : hSet} (U : subset X)
    : contained U U.
  Proof.
    intro ; intro;  assumption.
  Qed.

  Definition contained_trans {X : hSet} {U V W : subset X} (uv : contained U V) (vw : contained V W)
    : contained U W.
  Proof.
    intros x p.
    apply vw.
    apply uv.
    assumption.
  Qed.

  Definition intersection_contained_l {X : hSet} (U V : subset X)
    : contained (intersection U V) U.
  Proof.
    intros ? xinUV.
    apply xinUV.
  Qed.

  Definition intersection_contained_r {X : hSet} (U V : subset X)
    : contained (intersection U V) V.
  Proof.
    intros ? xinUV.
    apply xinUV.
  Qed.

  Definition intersection_contained {X : hSet} {U U' V V' : subset X} (uu : contained U U') (vv : contained V V')
    : contained (intersection U V) (intersection V' U').
  Proof.
    intros x p.
    cbn.
    split.
    - apply vv.
      exact ((intersection_contained_r U V) x p).
    - apply uu.
      exact ((intersection_contained_l U V) x p).
  Qed.

  Lemma isaprop_contained {X : hSet} (U V : subset X)
    : isaprop (contained U V).
  Proof.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    apply V.
  Qed.

  Definition id (X : hSet) : X -> X := idfun X.
  Definition comp {X Y Z : hSet} (f : X -> Y) (g : Y -> Z)
    : X -> Z := funcomp f g.

  Definition image_subset {X Y : hSet} (U : subset X) (f : X → Y)
    : subset Y := λ y : Y, (∃ x : X, f x = y × U x).

  Lemma image_subset_emptysubset {X Y : hSet} (f : X → Y)
    : image_subset (emptysubset X) f = emptysubset Y.
  Proof.
    apply funextsec ; intro y.
    apply hPropUnivalence.
    - intro yinfEmpty.
      use (factor_through_squash _ _ yinfEmpty).
      { apply emptysubset. }
      intro x.
      apply (pr22 x).
    - intro yinEmpty.
      apply fromempty.
      exact (yinEmpty).
  Qed.

  Definition image_subset_id {X : hSet} (U : subset X)
    : image_subset U (id X) = U.
  Proof.
    apply funextsec ; intro x.
    apply hPropUnivalence.
    - intro xinIdU.
      use (factor_through_squash _ _ xinIdU).
      { apply U. }
      intro u0.
      assert (p0 : U (pr1 u0) = U x).
      {
        apply maponpaths.
        apply (pr12 u0).
      }
      induction p0.
      apply (pr22 u0).
    - intro xinU.
      apply hinhpr.
      exact (x,, idpath x,, xinU).
  Qed.

  Definition image_subset_comp {X Y Z : hSet} (U : subset X)
             (f : X → Y) (g : Y → Z)
    : image_subset U (comp f g) = image_subset (image_subset U f) g.
  Proof.
    apply funextsec ; intro z.
    apply hPropUnivalence.
    - intro zinCompU.
      use (factor_through_squash _ _ zinCompU).
      { apply ishinh. }
      intro x.
      apply hinhpr.
      exists (f (pr1 x)).
      exists (pr12 x).
      apply hinhpr.
      exact (pr1 x,, maponpaths f (idpath (pr1 x)),, pr22 x).
    - intro zinCompU.
      use (factor_through_squash _ _ zinCompU).
      { apply ishinh. }
      intro y.
      use (factor_through_squash _ _ (pr22 y)).
      { apply ishinh. }
      intro x.
      apply hinhpr.
      exists (pr1 x).
      split.
      + refine (_ @ (pr12 y)).
        unfold comp.
        unfold funcomp.
        apply maponpaths.
        exact (pr12 x).
      + exact (pr22 x).
  Qed.

  Definition subset_preserving {X Y : hSet} (U : subset X) (V : subset Y) (f : X → Y)
    : UU := contained (image_subset U f) V.

  Lemma isaprop_subset_preserving {X Y : hSet} (U : subset X) (V : subset Y) (f : X → Y)
    : isaprop (subset_preserving U V f).
  Proof.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    apply V.
  Qed.

  Lemma id_subset_preserving {X : hSet} (U : subset X) : subset_preserving U U (id X).
  Proof.
    intros x xinU.
    rewrite image_subset_id in xinU.
    exact xinU.
  Qed.

  Lemma comp_subset_preserving {X Y Z : hSet}
             {U : subset X} {V : subset Y} {W : subset Z}
             {f : X → Y} {g : Y → Z}
             (fsp : subset_preserving U V f) (gsp : subset_preserving V W g)
    : subset_preserving U W (comp f g).
  Proof.
    intros z zinU.
    rewrite image_subset_comp in zinU.
    apply gsp.
    unfold image_subset.
    use (factor_through_squash _ _ zinU).
    { apply ishinh. }
    intro y.
    apply hinhpr.
    exists (pr1 y).
    exists (pr12 y).
    apply fsp.
    exact (pr22 y).
  Qed.

  Lemma empty_subset_preserving {X Y : hSet} (f : X → Y)
    : subset_preserving (emptysubset X) (emptysubset Y) f.
  Proof.
    unfold subset_preserving.
    rewrite image_subset_emptysubset.
    apply contained_reflexive.
  Qed.

  Lemma entire_subset_preserving {X Y : hSet} (f : X → Y)
    : subset_preserving (entiresubset X) (entiresubset Y) f.
  Proof.
    exact (λ _ _, tt).
  Qed.

End Subsets.

Section SetWithSubset.

  Definition SS_disp_cat_ob_mor : disp_cat_ob_mor hset_category.
  Proof.
    use tpair.
    - exact (λ X, subset X).
    - exact (λ _ _ U V f, subset_preserving U V f).
  Defined.

  Definition SS_disp_cat_data : disp_cat_data hset_category.
  Proof.
    exists SS_disp_cat_ob_mor.
    use tpair.
    - intro ; intro.
      apply id_subset_preserving.
    - intros ? ? ? ? ? ? ? ? fsp gsp.
      apply (comp_subset_preserving fsp gsp).
  Defined.

  Definition SS_disp_cat_axioms : disp_cat_axioms hset_category SS_disp_cat_data.
  Proof.
    repeat split; cbn; intros; try (apply proofirrelevance, isaprop_subset_preserving).
    apply isasetaprop. apply isaprop_subset_preserving.
  Defined.

  Definition SS_disp_cat : disp_cat hset_category
    := SS_disp_cat_data ,, SS_disp_cat_axioms.

  (* We construct two sections, the empty and entire sections.
     However, we only have that the entire section is monoidal *)
  Definition empty_section_data : section_disp_data SS_disp_cat.
  Proof.
    exists (λ X, emptysubset X).
    intro ; intros.
    apply empty_subset_preserving.
  Defined.

  Definition empty_section_axioms : section_disp_axioms empty_section_data.
  Proof.
    use tpair.
    - intro ; repeat (apply funextsec ; intro) ; apply isapropempty.
    - intro ; intros.
      repeat (apply funextsec ; intro).
      apply isapropempty.
  Qed.

  Definition empty_section : section_disp SS_disp_cat
    := empty_section_data ,, empty_section_axioms.

  Definition entire_section_data : section_disp_data SS_disp_cat.
  Proof.
    exists (λ X, entiresubset X).
    intro ; intros.
    apply entire_subset_preserving.
  Defined.

  Definition entire_section_axioms : section_disp_axioms entire_section_data.
  Proof.
    use tpair.
    - intro ; repeat (apply funextsec ; intro) ; apply entiresubset.
    - intro ; intros ; repeat (apply funextsec ; intro) ; apply entiresubset.
  Qed.

  Definition entire_section : section_disp SS_disp_cat
    := entire_section_data ,, entire_section_axioms.

End SetWithSubset.

Section SetWithSubsetMonoidal.

  Definition SS_disp_cat_tensor_data
    : disp_bifunctor_data SET_cartesian_monoidal SS_disp_cat SS_disp_cat SS_disp_cat.
  Proof.
    exists (λ _ _ U V, subset_in_product U V).
    repeat (use tpair).
    - intros X Y1 Y2 g Ux U1 U2 gsp.
      intros xy2 xy1_prop.
      use (factor_through_squash _ _ xy1_prop).
      { apply subset_in_product. }
      intro xy1.
      repeat split.
      + rewrite (! pr12 xy1).
        exact (pr122 xy1).
      + simpl in *.
        apply gsp.
        apply hinhpr.
        exists (pr21 xy1).
        split.
        * rewrite (! pr12 xy1).
          apply idpath.
        * exact (pr222 xy1).
    - intros X1 X2 Y f U1 U2 Uy fsp.
      intros x2y x1y_prop.
      use (factor_through_squash _ _ x1y_prop).
      { apply subset_in_product. }
      intro x1y.
      repeat split.
      + simpl in *.
        apply fsp.
        apply hinhpr.
        exists (pr11 x1y).
        split.
        * rewrite (! pr12 x1y).
          apply idpath.
        * exact (pr122 x1y).
      + rewrite (! pr12 x1y).
        exact (pr222 x1y).
  Defined.

  Lemma SS_disp_cat_tensor_laws : is_disp_bifunctor SS_disp_cat_tensor_data.
  Proof.
    repeat split; red; intros; apply isaprop_subset_preserving.
  Qed.

  Definition SS_disp_cat_tensor : disp_tensor SS_disp_cat SET_cartesian_monoidal
    := SS_disp_cat_tensor_data,, SS_disp_cat_tensor_laws.

  Definition SS_disp_monoidal_data : disp_monoidal_data SS_disp_cat SET_cartesian_monoidal.
  Proof.
    exists (SS_disp_cat_tensor).
    exists (entiresubset unitHSET).
    repeat (use tpair).
    - intros X U x xinU_prop.
      use (factor_through_squash _ _ xinU_prop).
      { apply U. }
      intro xinU.
      rewrite (! pr12 xinU).
      exact (pr222 xinU).
    - intros X U x xinU_prop.
      exists tt.
      use (factor_through_squash _ _ xinU_prop).
      { apply U. }
      intro xinU.
      rewrite (! pr12 xinU).
      exact (pr22 xinU).
    - intros X U x xinU_prop.
      use (factor_through_squash _ _ xinU_prop).
      { apply U. }
      intro xinU.
      rewrite (! pr12 xinU).
      exact (pr122 xinU).
    - intros X U x xinU_prop.
      refine (_ ,, tt).
      use (factor_through_squash _ _ xinU_prop).
      { apply U. }
      intro xinU.
      rewrite (! pr12 xinU).
      exact (pr22 xinU).
    - intros X Y Z U V W xyz xyzinUVW_prop.
      use (factor_through_squash _ _ xyzinUVW_prop).
      {
        repeat (apply isapropdirprod).
        apply U. apply V. apply W.
      }
      intro xyzinUVW.
      rewrite (! pr12 xyzinUVW).
      repeat split ; apply (pr22 xyzinUVW).
    - intros X Y Z U V W xyz xyzinUVW_prop.
      use (factor_through_squash _ _ xyzinUVW_prop).
      {
        repeat (apply isapropdirprod).
        apply U. apply V. apply W.
      }
      intro xyzinUVW.
      rewrite (! pr12 xyzinUVW).
      repeat split ; apply (pr22 xyzinUVW).
  Defined.

  Definition SS_disp_monoidal_laws : disp_monoidal_laws (SS_disp_monoidal_data).
  Proof.
    repeat split ; try (intro ; intros) ; apply isaprop_subset_preserving.
  Qed.

  Definition SS_disp_monoidal : disp_monoidal SS_disp_cat SET_cartesian_monoidal
    := SS_disp_monoidal_data,, SS_disp_monoidal_laws.

  Definition entire_section_monoidal_data : smonoidal_data SET_cartesian_monoidal SS_disp_monoidal entire_section .
  Proof.
    use tpair.
    - exact (λ _ _ _ _, tt).
    - exact (λ _ _, tt).
  Defined.

  Definition entire_section_monoidal_ax : smonoidal_laxlaws _ _ entire_section_monoidal_data.
  Proof.
    repeat split ; repeat (intro ; intros ; apply isaprop_subset_preserving).
  Qed.

  Definition entire_section_monoidal_lax : smonoidal_lax SET_cartesian_monoidal SS_disp_monoidal entire_section
    := entire_section_monoidal_data,, entire_section_monoidal_ax.

  Definition entire_section_monoidal : smonoidal SET_cartesian_monoidal SS_disp_monoidal entire_section.
  Proof.
    exists (entire_section_monoidal_lax).
    use tpair.
    - intros X Y.
      repeat (use tpair) ; repeat (apply isaprop_subset_preserving).
      exists tt.
      exact tt.
    - repeat (use tpair) ; repeat (apply isaprop_subset_preserving).
      exact (λ _ _, tt).
  Defined.

End SetWithSubsetMonoidal.
