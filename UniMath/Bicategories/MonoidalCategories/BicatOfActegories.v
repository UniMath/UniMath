(** **********************************************************

Ralph Matthes

August 2022
*)

(** **********************************************************

constructs the bicategory of (elementarily defined) actegories
with lax morphisms as 1-cells

 ************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.BicatOfCats.

Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.

Require Import UniMath.CategoryTheory.Actegories.Actegories.
Require Import UniMath.CategoryTheory.Actegories.MorphismsOfActegories.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Import BifunctorNotations.

Section A.

  Context {V : category} (Mon_V : monoidal V).

Section TheConstruction.

  Definition disp_actbicat_disp_ob_mor : disp_cat_ob_mor bicat_of_cats.
  Proof.
    exists (actegory Mon_V).
    exact (λ C D ActC ActD F, lineator_lax Mon_V ActC ActD F).
  Defined.

  Definition disp_actbicat_disp_id_comp : disp_cat_id_comp bicat_of_cats disp_actbicat_disp_ob_mor.
  Proof.
    split.
    - intros C F. apply identity_lineator_lax.
    - intros C D E ActC ActD ActE N O.
      apply comp_lineator_lax.
  Defined.

  Definition disp_actbicat_disp_catdata : disp_cat_data bicat_of_cats
    := (disp_actbicat_disp_ob_mor,,disp_actbicat_disp_id_comp).

  Definition bidisp_actbicat_disp_2cell_struct : disp_2cell_struct disp_actbicat_disp_ob_mor.
  Proof.
    intros C D F G ξ ActC ActD.
    exact (λ Fl Gl, is_linear_nat_trans (Fl : lineator_lax Mon_V ActC ActD F) (Gl : lineator_lax Mon_V ActC ActD G) ξ).
  Defined.

  Lemma isaprop_bidisp_actbicat_disp_2cell_struct
        {C D : bicat_of_cats}
        {F G : bicat_of_cats ⟦C,D⟧ }
        {ξ : prebicat_cells bicat_of_cats F G}
        {ActC : disp_actbicat_disp_catdata C}
        {ActD : disp_actbicat_disp_catdata D}
        (Fl : ActC -->[F] ActD)
        (Gl : ActC -->[G] ActD)
    : isaprop (bidisp_actbicat_disp_2cell_struct C D F G ξ ActC ActD Fl Gl).
  Proof.
    apply isaprop_is_linear_nat_trans.
  Qed.

  Definition bidisp_actbicat_disp_prebicat_1_id_comp_cells
    :  disp_prebicat_1_id_comp_cells bicat_of_cats
    := (disp_actbicat_disp_catdata,, bidisp_actbicat_disp_2cell_struct).

  Lemma bidisp_actbicat_disp_prebicat_ops :
    disp_prebicat_ops bidisp_actbicat_disp_prebicat_1_id_comp_cells.
  Proof.
    repeat split; cbn; unfold bidisp_actbicat_disp_2cell_struct, comp_lineator, identity_lineator.
    (** first 5 quantified equations for identity, then 5 quantified equations for composition *)
    - intros. apply is_linear_nat_trans_identity.
    - intros C D F ActC ActD lin v c.
      cbn.
      unfold comp_lineator_data, identity_lineator_lax.
      cbn.
      unfold identity_lineator_data.
      rewrite functor_id.
      do 2 rewrite id_right.
      etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, (bifunctor_leftid ActD). }
      apply pathsinv0, id_left.
    - intros C D F ActC ActD lin v c.
      cbn.
      unfold comp_lineator_data, identity_lineator_lax.
      cbn.
      unfold identity_lineator_data.
      etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, (bifunctor_leftid ActD). }
      apply id_right.
    - intros C D F ActC ActD lin v c.
      cbn.
      unfold comp_lineator_data, identity_lineator_lax.
      cbn.
      unfold identity_lineator_data.
      etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, (bifunctor_leftid ActD). }
      rewrite functor_id.
      apply pathsinv0, id_left.
    - intros C D F ActC ActD lin v c.
      cbn.
      unfold comp_lineator_data, identity_lineator_lax.
      cbn.
      unfold identity_lineator_data.
      etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, (bifunctor_leftid ActD). }
      do 2 rewrite id_left.
      apply id_right.
      (** now towards composition *)
    - intros C1 C2 C3 C4 F G H ActC1 ActC2 ActC3 ActC4 Fl Gl Hl v x.
      cbn.
      unfold comp_lineator_data, identity_lineator_lax.
      cbn.
      unfold comp_lineator_data.
      etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, (bifunctor_leftid ActC4). }
      rewrite id_right.
      rewrite id_left.
      repeat rewrite assoc'.
      apply maponpaths.
      apply functor_comp.
    - intros C1 C2 C3 C4 F G H ActC1 ActC2 ActC3 ActC4 Fl Gl Hl v x.
      cbn.
      unfold comp_lineator_data, identity_lineator_lax.
      cbn.
      unfold comp_lineator_data.
      etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, (bifunctor_leftid ActC4). }
      rewrite id_right.
      rewrite id_left.
      repeat rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, functor_comp.
    - intros C D F G H α β ActC ActD Fl Gl Hl linα linβ v x.
      cbn.
      etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, (bifunctor_leftcomp ActD). }
      rewrite assoc.
      etrans.
      { apply cancel_postcomposition.
        apply (linα v x). }
      repeat rewrite assoc'.
      apply maponpaths.
      apply linβ.
    - intros C D E F G1 G2 β ActC ActD ActE Fl G1l G2l linβ v x.
      cbn.
      unfold comp_lineator_data.
      assert (aux := linβ v (F x)).
      etrans.
      2: { rewrite assoc.
           apply cancel_postcomposition.
           exact aux. }
      clear aux.
      repeat rewrite assoc'.
      apply maponpaths.
      apply nat_trans_ax.
    - intros C D E F1 F2 G α ActC ActD ActE F1l F2l Gl linα v x.
      cbn.
      unfold comp_lineator_data.
      etrans.
      { rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, functor_comp. }
      etrans.
      { do 2 apply maponpaths.
        apply linα. }
      rewrite functor_comp.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0, lineator_linnatleft.
   Qed.

  Definition bidisp_actbicat_disp_prebicat_data : disp_prebicat_data bicat_of_cats
    := (bidisp_actbicat_disp_prebicat_1_id_comp_cells,, bidisp_actbicat_disp_prebicat_ops).

  Definition bidisp_actbicat_disp_prebicat_laws : disp_prebicat_laws bidisp_actbicat_disp_prebicat_data.
  Proof.
    repeat split; intro; intros; apply isaprop_bidisp_actbicat_disp_2cell_struct.
  Qed.

  Definition bidisp_actbicat_disp_prebicat : disp_prebicat bicat_of_cats
    := (bidisp_actbicat_disp_prebicat_data,,bidisp_actbicat_disp_prebicat_laws).

  Definition bidisp_actbicat_disp_bicat : disp_bicat bicat_of_cats.
  Proof.
    refine (bidisp_actbicat_disp_prebicat,, _).
    red; intros ? ? ? ? ? ? ? ? ?.
    apply isasetaprop.
    apply isaprop_bidisp_actbicat_disp_2cell_struct.
  Defined.

  Lemma actbicat_disp_2cells_isaprop : disp_2cells_isaprop bidisp_actbicat_disp_bicat.
  Proof.
    red.
    intros.
    apply isaprop_bidisp_actbicat_disp_2cell_struct.
  Qed.

  Definition actbicat : bicat := total_bicat bidisp_actbicat_disp_bicat.


End TheConstruction.

Definition actbicat_disp_locally_groupoid : disp_locally_groupoid bidisp_actbicat_disp_bicat.
Proof.
  red. intros C D F G αiso ActC ActD Fl Gl islin.
  use tpair.
  - transparent assert (isnziα : (is_nat_z_iso (pr11 αiso))).
    { apply (nat_trafo_pointwise_z_iso_if_z_iso (pr2 D)). exact (pr2 αiso). }
    exact (is_linear_nat_trans_pointwise_inverse (Fl : lineator_lax _ _ _ _) (Gl : lineator_lax _ _ _ _) (pr1 αiso) isnziα islin).
  - split; apply isaprop_bidisp_actbicat_disp_2cell_struct.
Defined.

End A.
