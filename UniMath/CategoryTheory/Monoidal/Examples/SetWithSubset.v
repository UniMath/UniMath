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

Section Subtype_AUX.

  (* We could define the intersection as follows but this makes it more complicated than it should be *)
  Definition binary_intersection' {X : UU} (U V : hsubtype X) : hsubtype X
    := subtype_intersection (λ b,  bool_rect (λ _ : bool, hsubtype X) U V b).

  Definition binary_intersection {X : UU} (U V : hsubtype X) : hsubtype X
    := λ x, U x ∧ V x.

  Lemma binary_intersection_commutative {X : UU} (U V : hsubtype X)
    : ∏ x : X, (binary_intersection U V) x -> (binary_intersection V U) x.
  Proof.
    intros ? p.
    exact (transportf _ (iscomm_hconj (U x) (V x)) p).
  Qed.

  Definition emptysubtype (X : UU) : hsubtype X
    := λ x, hfalse.

  Definition intersection_contained_l {X : UU} (U V : hsubtype X)
    : subtype_containedIn (binary_intersection U V) U.
  Proof.
    intros ? xinUV.
    apply xinUV.
  Qed.

  Definition intersection_contained_r {X : UU} (U V : hsubtype X)
    : subtype_containedIn (binary_intersection U V) V.
  Proof.
    intros ? xinUV.
    apply xinUV.
  Qed.

  Definition intersection_contained {X : UU} {U U' V V' : hsubtype X}
             (uu : subtype_containedIn U U')
             (vv : subtype_containedIn V V')
    : subtype_containedIn (binary_intersection U V) (binary_intersection V' U').
  Proof.
    intros x p.
    cbn.
    split.
    - apply (vv x).
      exact ((intersection_contained_r U V) x p).
    - apply (uu x).
      exact ((intersection_contained_l U V) x p).
  Qed.

  Lemma isaprop_subtype_containedIn {X : UU} (U V : hsubtype X)
    : isaprop (subtype_containedIn U V).
  Proof.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    apply V.
  Qed.

  Definition image_hsubtype {X Y : UU} (U : hsubtype X) (f : X → Y)
    : hsubtype Y := λ y : Y, (∃ x : X, f x = y × U x).

  Lemma image_hsubtype_emptyhsubtype {X Y : UU} (f : X → Y)
    : image_hsubtype (emptysubtype X) f = emptysubtype Y.
  Proof.
    apply funextsec ; intro y.
    apply hPropUnivalence.
    - intro yinfEmpty.
      use (factor_through_squash _ _ yinfEmpty).
      { apply emptysubtype. }
      intro x.
      apply (pr22 x).
    - intro yinEmpty.
      apply fromempty.
      exact (yinEmpty).
  Qed.

  Definition image_hsubtype_id {X : UU} (U : hsubtype X)
    : image_hsubtype U (idfun X) = U.
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

  Definition image_hsubtype_comp {X Y Z : UU} (U : hsubtype X)
             (f : X → Y) (g : Y → Z)
    : image_hsubtype U (funcomp f g) = image_hsubtype (image_hsubtype U f) g.
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
        unfold funcomp.
        unfold funcomp.
        apply maponpaths.
        exact (pr12 x).
      + exact (pr22 x).
  Qed.

  Definition hsubtype_preserving {X Y : UU} (U : hsubtype X) (V : hsubtype Y) (f : X → Y)
    : UU := subtype_containedIn (image_hsubtype U f) V.

  Lemma isaprop_hsubtype_preserving {X Y : UU} (U : hsubtype X) (V : hsubtype Y) (f : X → Y)
    : isaprop (hsubtype_preserving U V f).
  Proof.
    apply impred_isaprop ; intro.
    apply isapropimpl.
    apply V.
  Qed.

  Lemma id_hsubtype_preserving {X : UU} (U : hsubtype X) : hsubtype_preserving U U (idfun X).
  Proof.
    intros x xinU.
    rewrite image_hsubtype_id in xinU.
    exact xinU.
  Qed.

  Lemma comp_hsubtype_preserving {X Y Z : UU}
             {U : hsubtype X} {V : hsubtype Y} {W : hsubtype Z}
             {f : X → Y} {g : Y → Z}
             (fsp : hsubtype_preserving U V f) (gsp : hsubtype_preserving V W g)
    : hsubtype_preserving U W (funcomp f g).
  Proof.
    intros z zinU.
    rewrite image_hsubtype_comp in zinU.
    apply (gsp _).
    unfold image_hsubtype.
    use (factor_through_squash _ _ zinU).
    { apply ishinh. }
    intro y.
    apply hinhpr.
    exists (pr1 y).
    exists (pr12 y).
    apply (fsp _).
    exact (pr22 y).
  Qed.

  Lemma empty_hsubtype_preserving {X Y : UU} (f : X → Y)
    : hsubtype_preserving (emptysubtype X) (emptysubtype Y) f.
  Proof.
    unfold hsubtype_preserving.
    rewrite image_hsubtype_emptyhsubtype.
    apply subtype_containment_isrefl.
  Qed.

  Lemma total_hsubtype_preserving {X Y : UU} (f : X → Y)
    : hsubtype_preserving (totalsubtype X) (totalsubtype Y) f.
  Proof.
    exact (λ _ _, tt).
  Qed.

End Subtype_AUX.

Section SetSubtype.

  Definition setsubtype (X : hSet) : UU := hsubtype X.
  Identity Coercion setsubtype_to_subtype : setsubtype >-> hsubtype.

  Definition singletonsetsubtype {X : hSet} (x : X) : setsubtype X.
  Proof.
    intro x'.
    exists (x'=x).
    apply X.
  Defined.

  Definition emptysetsubtype {X : hSet} : setsubtype X := emptysubtype X.

  Definition setsubtype_in_product {X Y : hSet}
             (U : hsubtype X) (V : hsubtype Y)
    : setsubtype (setdirprod X Y) := subtypesdirprod U V.

  Definition union {X I : hSet} (U : I -> setsubtype X) :  setsubtype X := subtype_union U.

  Definition totalsetsubtype (X : hSet) : setsubtype X := totalsubtype X.

  Definition contained {X : hSet} (U V : setsubtype X) : UU := subtype_containedIn U V.

End SetSubtype.

Section SetWithSubset.

  Definition SS_disp_cat_ob_mor : disp_cat_ob_mor hset_category.
  Proof.
    use tpair.
    - exact (λ X, setsubtype X).
    - exact (λ _ _ U V f, hsubtype_preserving U V f).
  Defined.

  Definition SS_disp_cat_data : disp_cat_data hset_category.
  Proof.
    exists SS_disp_cat_ob_mor.
    use tpair.
    - intro ; intro.
      apply id_hsubtype_preserving.
    - intros ? ? ? ? ? ? ? ? fsp gsp.
      apply (comp_hsubtype_preserving fsp gsp).
  Defined.

  Definition SS_disp_cat_axioms : disp_cat_axioms hset_category SS_disp_cat_data.
  Proof.
    repeat split; cbn; intros; try (apply proofirrelevance, isaprop_hsubtype_preserving).
    apply isasetaprop. apply isaprop_hsubtype_preserving.
  Defined.

  Definition SS_disp_cat : disp_cat hset_category
    := SS_disp_cat_data ,, SS_disp_cat_axioms.

  Definition total_section_data : section_disp_data SS_disp_cat.
  Proof.
    exists (λ X, totalsetsubtype X).
    intro ; intros.
    apply total_hsubtype_preserving.
  Defined.

  Definition total_section_axioms : section_disp_axioms total_section_data.
  Proof.
    use tpair.
    - intro ; repeat (apply funextsec ; intro) ; apply totalsubtype.
    - intro ; intros ; repeat (apply funextsec ; intro) ; apply totalsubtype.
  Qed.

  Definition total_section : section_disp SS_disp_cat
    := total_section_data ,, total_section_axioms.

End SetWithSubset.

Section SetWithSubsetMonoidal.

  Definition SS_disp_cat_tensor_data
    : disp_bifunctor_data SET_cartesian_monoidal SS_disp_cat SS_disp_cat SS_disp_cat.
  Proof.
    exists (λ _ _ U V, setsubtype_in_product U V).
    repeat (use tpair).
    - intros X Y1 Y2 g Ux U1 U2 gsp.
      intros xy2 xy1_prop.
      use (factor_through_squash _ _ xy1_prop).
      { apply setsubtype_in_product. }
      intro xy1.
      repeat split.
      + rewrite (! pr12 xy1).
        exact (pr122 xy1).
      + simpl in *.
        apply (gsp _).
        apply hinhpr.
        exists (pr21 xy1).
        split.
        * rewrite (! pr12 xy1).
          apply idpath.
        * exact (pr222 xy1).
    - intros X1 X2 Y f U1 U2 Uy fsp.
      intros x2y x1y_prop.
      use (factor_through_squash _ _ x1y_prop).
      { apply setsubtype_in_product. }
      intro x1y.
      repeat split.
      + simpl in *.
        apply (fsp _).
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
    repeat split; red; intros; apply isaprop_hsubtype_preserving.
  Qed.

  Definition SS_disp_cat_tensor : disp_tensor SS_disp_cat SET_cartesian_monoidal
    := SS_disp_cat_tensor_data,, SS_disp_cat_tensor_laws.

  Definition SS_disp_monoidal_data : disp_monoidal_data SS_disp_cat SET_cartesian_monoidal.
  Proof.
    exists (SS_disp_cat_tensor).
    exists (totalsetsubtype unitHSET).
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
    repeat split ; try (intro ; intros) ; apply isaprop_hsubtype_preserving.
  Qed.

  Definition SS_disp_monoidal : disp_monoidal SS_disp_cat SET_cartesian_monoidal
    := SS_disp_monoidal_data,, SS_disp_monoidal_laws.

  Definition entire_section_monoidal_data : smonoidal_data SET_cartesian_monoidal SS_disp_monoidal total_section .
  Proof.
    use tpair.
    - exact (λ _ _ _ _, tt).
    - exact (λ _ _, tt).
  Defined.

  Definition entire_section_monoidal_ax : smonoidal_laxlaws _ _ entire_section_monoidal_data.
  Proof.
    repeat split ; repeat (intro ; intros ; apply isaprop_hsubtype_preserving).
  Qed.

  Definition entire_section_monoidal_lax : smonoidal_lax SET_cartesian_monoidal SS_disp_monoidal total_section
    := entire_section_monoidal_data,, entire_section_monoidal_ax.

  Definition entire_section_monoidal : smonoidal SET_cartesian_monoidal SS_disp_monoidal total_section.
  Proof.
    exists (entire_section_monoidal_lax).
    use tpair.
    - intros X Y.
      repeat (use tpair) ; repeat (apply isaprop_hsubtype_preserving).
      exists tt.
      exact tt.
    - repeat (use tpair) ; repeat (apply isaprop_hsubtype_preserving).
      exact (λ _ _, tt).
  Defined.

End SetWithSubsetMonoidal.
