(*
In this file, we construct a displayed monoidal structure on the sigma construction (of displayed categories), given both displayed categories have a displayed monoidal structure.
For simplicity, we assume that the upper-most displayed category is locally propositional (this assumption is satisfied for the instantiations).

Contents:
        1. SigmaConstruction: Constructs the monoidal structure [sigma_disp_cat_monoidal];
        2. SigmaConstructionSymmetric: Constructs a symmetric monoidal structure [sigma_disp_cat_monoidal_symmetric];
        3. Dirprodconstruction: Explicit construction of the product of displayed monoidal categories [dirprod_disp_cat_monoidal, dirprod_disp_cat_symmetric_monoidal].
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.

Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Import BifunctorNotations.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Fullsub.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Local Open Scope cat.
Open Scope mor_disp_scope.

Import MonoidalNotations.
Import DisplayedBifunctorNotations.

Section SigmaConstruction.

  Context {C : category} {M : monoidal C}
    {D : disp_cat C} {DM : disp_monoidal D M}
    {E : disp_cat (total_category D)}
    (EM : disp_monoidal E (total_monoidal DM)).

  Context (E_prop : locally_propositional E).

  Definition sigma_disp_cat_tensor_data
    : disp_bifunctor_data M (sigma_disp_cat E) (sigma_disp_cat E) (sigma_disp_cat E).
  Proof.
    simple refine (_ ,, (_ ,, _)).
    - intros x y [xx xxx] [yy yyy].
      exists (xx ⊗⊗_{DM} yy).
      exact (xxx ⊗⊗_{EM} yyy).
    - intros x y1 y2 g [xx xxx] [yy1 yyy1] [yy2 yyy2] [gg ggg].
      exists (xx ⊗⊗^{DM}_{l} gg).
      exact (xxx ⊗⊗^{EM}_{l} ggg).
    - intros y1 y2 x g [yy1 yyy1] [yy2 yyy2] [xx xxx] [gg ggg].
      exists (gg ⊗⊗^{DM}_{r} xx).
      exact (ggg ⊗⊗^{EM}_{r} xxx).
  Defined.

  Lemma sigma_disp_is_tensor
    : is_disp_bifunctor M sigma_disp_cat_tensor_data.
  Proof.
    repeat split.
    - intros x y [xx xxx] [yy yyy].
      use total2_paths_f.
      + refine (disp_bifunctor_leftid DM x y xx yy @ _).
        apply pathsinv0, pr1_transportf.
      + apply E_prop.
    - intros x y [xx xxx] [yy yyy].
      use total2_paths_f.
      + refine (disp_bifunctor_rightid DM x y xx yy @ _).
        apply pathsinv0, pr1_transportf.
      + apply E_prop.
    - intro ; intros.
      use total2_paths_f.
      + refine (disp_bifunctor_leftcomp DM _ _ _ _ _ _ _ _ _ _ _ _ @ _).
        apply pathsinv0, pr1_transportf.
      + apply E_prop.
    - intro ; intros.
      use total2_paths_f.
      + refine (disp_bifunctor_rightcomp DM _ _ _ _ _ _ _ _ _ _ _ _ @ _).
        apply pathsinv0, pr1_transportf.
      + apply E_prop.
    - intro ; intros.
      use total2_paths_f.
      + etrans. {
          apply disp_bifunctor_equalwhiskers.
        }
        apply pathsinv0, pr1_transportf.
      + apply E_prop.
  Qed.

  Definition sigma_disp_cat_tensor
    : disp_tensor (sigma_disp_cat E) M.
  Proof.
    exists sigma_disp_cat_tensor_data.
    apply sigma_disp_is_tensor.
  Defined.

  Definition sigma_disp_cat_unit :
    sigma_disp_cat E I_{M}
    := (disp_monoidal_unit DM,, disp_monoidal_unit EM).

  Definition sigma_disp_cat_lunitor
    : disp_leftunitor_data sigma_disp_cat_tensor sigma_disp_cat_unit.
  Proof.
    intros x [xx xxx].
    exists (disp_monoidal_leftunitor DM _ xx).
    exact (disp_monoidal_leftunitor EM _ xxx).
  Defined.

  Definition sigma_disp_cat_lunitorinv
    : disp_leftunitorinv_data sigma_disp_cat_tensor sigma_disp_cat_unit.
  Proof.
    intros x [xx xxx].
    exists (disp_monoidal_leftunitorinv DM _ xx).
    exact (disp_monoidal_leftunitorinv EM _ xxx).
  Defined.

  Definition sigma_disp_cat_runitor
    : disp_rightunitor_data sigma_disp_cat_tensor sigma_disp_cat_unit.
  Proof.
    intros x [xx xxx].
    exists (disp_monoidal_rightunitor DM _ xx).
    exact (disp_monoidal_rightunitor EM _ xxx).
  Defined.

  Definition sigma_disp_cat_runitorinv
    : disp_rightunitorinv_data sigma_disp_cat_tensor sigma_disp_cat_unit.
  Proof.
    intros x [xx xxx].
    exists (disp_monoidal_rightunitorinv DM _ xx).
    exact (disp_monoidal_rightunitorinv EM _ xxx).
  Defined.

  Definition sigma_disp_cat_associator
    : disp_associator_data sigma_disp_cat_tensor.
  Proof.
    intros x y z [xx xxx] [yy yyy] [zz zzz].
    exists (disp_monoidal_associator DM _ _ _ xx yy zz).
    exact (disp_monoidal_associator EM _ _ _ xxx yyy zzz).
  Defined.

  Definition sigma_disp_cat_associatorinv
    : disp_associatorinv_data sigma_disp_cat_tensor.
  Proof.
    intros x y z [xx xxx] [yy yyy] [zz zzz].
    exists (disp_monoidal_associatorinv DM _ _ _ xx yy zz).
    exact (disp_monoidal_associatorinv EM _ _ _ xxx yyy zzz).
  Defined.

  Definition sigma_disp_cat_monoidal_data
    : disp_monoidal_data (sigma_disp_cat E) M.
  Proof.
    exists sigma_disp_cat_tensor.
    exists (disp_monoidal_unit DM ,, disp_monoidal_unit EM).
    exists sigma_disp_cat_lunitor.
    exists sigma_disp_cat_lunitorinv.
    exists sigma_disp_cat_runitor.
    exists sigma_disp_cat_runitorinv.
    exists sigma_disp_cat_associator.
    exact sigma_disp_cat_associatorinv.
  Defined.

  Lemma sigma_disp_cat_monoidal_laws
    : disp_monoidal_laws sigma_disp_cat_monoidal_data.
  Proof.
    repeat split ; try (intro ; intros) ; use total2_paths_f ; try (apply E_prop).
    - etrans. {
        apply (disp_monoidal_leftunitornat DM).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_monoidal_leftunitoriso DM).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_monoidal_leftunitoriso DM).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_monoidal_rightunitornat DM).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_monoidal_rightunitoriso DM).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_monoidal_rightunitoriso DM).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_monoidal_associatornatleft DM).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_monoidal_associatornatright DM).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_monoidal_associatornatleftright DM).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_monoidal_associatoriso DM).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_monoidal_associatoriso DM).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_monoidal_triangleidentity DM).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_monoidal_pentagonidentity DM).
      }
      apply pathsinv0, pr1_transportf.
  Qed.

  Definition sigma_disp_cat_monoidal
    : disp_monoidal (sigma_disp_cat E) M.
  Proof.
    exists sigma_disp_cat_monoidal_data.
    exact sigma_disp_cat_monoidal_laws.
  Defined.

End SigmaConstruction.

Section SigmaConstructionSymmetric.

  Context {C : category} {M : monoidal C} {S : symmetric M}
    {D : disp_cat C} {DM : disp_monoidal D M} {DS : disp_symmetric DM S}
    {E : disp_cat (total_category D)}
    {EM : disp_monoidal E (total_monoidal DM)}
    (ES : disp_symmetric EM (total_symmetric DM DS)).

  Context (E_prop : locally_propositional E).

  Definition sigma_disp_cat_monoidal_braiding_data
    : disp_braiding_data (sigma_disp_cat_monoidal EM E_prop) S.
  Proof.
    intros x y [xx xxx] [yy yyy].
    use tpair.
    - apply DS.
    - exact (pr1 ES _ _ xxx yyy).
  Defined.

  Lemma sigma_disp_cat_monoidal_braiding_laws
    : disp_braiding_laws (sigma_disp_cat_monoidal EM E_prop) sigma_disp_cat_monoidal_braiding_data
        sigma_disp_cat_monoidal_braiding_data.
  Proof.
    repeat split ; try (intro ; intros) ; use total2_paths_f ; try (apply E_prop).
    - etrans. {
        apply pr1_transportf.
      }
      apply (disp_braiding_to_naturality_left DM DS).
    - etrans. {
        apply pr1_transportf.
      }
      apply (disp_braiding_to_naturality_right DM DS).
    - etrans. {
        apply (disp_braiding_to_inverses DM DS).
      }
      apply pathsinv0, pr1_transportf.
    - etrans. {
        apply (disp_braiding_to_inverses DM DS).
      }
      etrans.
      2: { apply pathsinv0, pr1_transportf. }
      unfold transportb.
      apply maponpaths_2.
      apply homset_property.
    - etrans.
      2: { apply (disp_braiding_to_hexagon1 _ DS). }
      apply pr1_transportf.
    - etrans.
      2: { apply (disp_braiding_to_hexagon2 _ DS). }
      apply pr1_transportf.
  Qed.

  Definition sigma_disp_cat_monoidal_symmetric
    : disp_symmetric (sigma_disp_cat_monoidal EM E_prop) S.
  Proof.
    exists sigma_disp_cat_monoidal_braiding_data.
    exact sigma_disp_cat_monoidal_braiding_laws.
  Defined.

End SigmaConstructionSymmetric.

Section DirprodConstruction.

  Import DisplayedMonoidalNotations.

  Context {C : category} {M : monoidal C}
    {D : disp_cat C} (DM : disp_monoidal D M)
    {D' : disp_cat C} (D'M : disp_monoidal D' M).

  Context (D_prop : locally_propositional D)
    (D'_prop : locally_propositional D').

  Definition dirprod_disp_tensor
    : disp_bifunctor M (D × D') (D × D') (D × D').
  Proof.
    simple refine ((_ ,, (_,,_)) ,, _).
    - intros x y xx yy.
      exact (pr1 xx ⊗⊗_{DM} pr1 yy ,, pr2 xx ⊗⊗_{D'M} pr2 yy).
    - intros x y1 y2 g xx yy1 yy2 gg.
      exact (pr1 xx ⊗⊗^{DM}_{l} pr1 gg ,, pr2 xx ⊗⊗^{D'M}_{l} pr2 gg).
    - intros y1 y2 x f yy1 yy2 xx ff.
      exact (pr1 ff ⊗⊗^{DM}_{r} pr1 xx ,, pr2 ff ⊗⊗^{D'M}_{r} pr2 xx).
    - abstract (repeat split ;
                (try (intro ; intros) ; use total2_paths_f ; [apply D_prop | apply D'_prop])).
  Defined.

  Definition dirprod_disp_cat_monoidal_data
    : disp_monoidal_data (dirprod_disp_cat D D') M.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _).
    - exact dirprod_disp_tensor.
    - exact (dI_{DM} ,, dI_{D'M}).
    - intros x [x1 x2].
      exact (dlu^{DM} _ x1 ,, dlu^{D'M} _ x2).
    - intros x [x1 x2].
      exact (dluinv^{DM} _ x1 ,, dluinv^{D'M} _ x2).
    - intros x [x1 x2].
      exact (dru^{DM} _ x1 ,, dru^{D'M} _ x2).
    - intros x [x1 x2].
      exact (druinv^{DM} _ x1 ,, druinv^{D'M} _ x2).
    - intros x y z [x1 x2] [y1 y2] [z1 z2].
      exact (dα^{DM} _ _ _ x1 y1 z1 ,, dα^{D'M} _ _ _ x2 y2 z2).
    - intros x y z [x1 x2] [y1 y2] [z1 z2].
      exact (dαinv^{DM} _ _ _ x1 y1 z1 ,, dαinv^{D'M} _ _ _ x2 y2 z2).
  Defined.

  Definition dirprod_disp_cat_monoidal
    : disp_monoidal (dirprod_disp_cat D D') M.
  Proof.
    exists dirprod_disp_cat_monoidal_data.
    abstract (repeat split ;
              (try (intro ; intros) ; use total2_paths_f ; [apply D_prop | apply D'_prop])).
  Defined.

  Definition dirprod_disp_cat_symmetric_monoidal
    {S : symmetric M}
    (SM : disp_symmetric DM S)
    (S'M : disp_symmetric D'M S)
    : disp_symmetric dirprod_disp_cat_monoidal S.
  Proof.
    use tpair.
    - intros x y [x1 x2] [y1 y2].
      exact (pr1 SM _ _ x1 y1 ,, pr1 S'M _ _ x2 y2).
    - abstract (repeat split ;
              (try (intro ; intros) ; use total2_paths_f ; [apply D_prop | apply D'_prop])).
  Defined.

End DirprodConstruction.
