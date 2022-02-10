(**
The univalent bicategory of pointed 1-types.
*)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.
Local Open Scope bicategory_scope.

Definition p1types_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells one_types.
Proof.
  use tpair.
  - use tpair.
    + (** Objects and 1-cells *)
      use tpair.
      * (** Objects over a one type are points of X *)
        exact (λ X, pr1 X).
      * (** 1-cells over f are properties: f preserves points *)
        exact (λ _ _ x y f, f x = y).
    + (** Identity and composition of 1-cells: composition of properties *)
      use tpair.
      * exact (λ _ _, idpath _).
      * exact (λ _ _ _ f g x y z Hf Hg, maponpaths g Hf @ Hg).
  - exact (λ _ _ _ _ α x y ff gg, ff = α x @ gg).
Defined.

Definition p1types_disp_prebicat_ops
  : disp_prebicat_ops p1types_disp_prebicat_1_id_comp_cells.
Proof.
  repeat split; cbn.
  - intros X Y f x y ff.
    exact (pathscomp0rid _ @ maponpathsidfun _).
  - intros X Y f x y ff.
    exact (!(pathscomp0rid _ @ maponpathsidfun _)).
  - intros X Y Z W f g h x y z w ff gg hh.
    refine (_ @ !(path_assoc _ _ _)).
    refine (maponpaths (λ z, z @ hh) _).
    refine (maponpathscomp0 h (maponpaths g ff) gg @ _).
    refine (maponpaths (λ z, z @ _) _).
    apply maponpathscomp.
  - intros X Y Z W f g h x y z w ff gg hh.
    refine (!_).
    refine (_ @ !(path_assoc _ _ _)).
    refine (maponpaths (λ z, z @ hh) _).
    refine (maponpathscomp0 h (maponpaths g ff) gg @ _).
    refine (maponpaths (λ z, z @ _) _).
    apply maponpathscomp.
  - intros X Y f g h α β x y ff gg hh αα ββ.
    exact (αα @ maponpaths (λ z, _ @ z) ββ @ path_assoc _ _ _).
  - (* Whiskering *)
    intros X Y Z f g h α x y z ff gg hh αα.
    unfold funhomotsec.
    refine (maponpaths (λ z, _ @ z) αα @ _).
    refine (path_assoc _ _ _ @ _ @ !(path_assoc _ _ _)).
    refine (maponpaths (λ z, z @ _) _).
    apply homotsec_natural.
  - (* Whiskering *)
    intros X Y Z f g h α x y z ff gg hh αα.
    unfold homotfun.
    refine (_ @ !(path_assoc _ _ _)).
    refine (maponpaths (λ z, z @ hh) _).
    exact (maponpaths (maponpaths h) αα @ maponpathscomp0 h (α x) gg).
Defined.

Definition p1types_prebicat : disp_prebicat one_types.
Proof.
  use tpair.
  - exists p1types_disp_prebicat_1_id_comp_cells.
    apply p1types_disp_prebicat_ops.
  - repeat split; repeat intro; apply one_type_isofhlevel.
Defined.

Definition p1types_disp : disp_bicat one_types.
Proof.
  use tpair.
  - apply p1types_prebicat.
  - repeat intro.
    apply hlevelntosn.
    apply one_type_isofhlevel.
Defined.

Definition p1types : bicat := total_bicat p1types_disp.

Lemma p1types_disp_univalent_2_1 : disp_univalent_2_1 p1types_disp.
Proof.
  apply fiberwise_local_univalent_is_univalent_2_1.
  intros X Y f x y. cbn. intros p q.
  use gradth.
  - intro α. apply α.
  - intros α. apply Y.
  - intros α. cbn in  *.
    use subtypePath.
    {
      intro. apply (isaprop_is_disp_invertible_2cell (D:=p1types_disp)).
    }
    apply Y.
Defined.

Lemma p1types_disp_univalent_2_0 : disp_univalent_2_0 p1types_disp.
Proof.
  apply fiberwise_univalent_2_0_to_disp_univalent_2_0.
  intros X x x'. cbn in *.
  use gradth.
  - intros f. apply f.
  - intro p.
    induction p.
    apply idpath.
  - intros [f Hf].
    use subtypePath.
    { intros y y'.
      apply (isaprop_disp_left_adjoint_equivalence (D:=p1types_disp)).
      apply one_types_is_univalent_2.
      apply p1types_disp_univalent_2_1. }
    cbn ; cbn in f.
    induction f.
    apply idpath.
Defined.

Lemma p1types_disp_univalent_2 : disp_univalent_2 p1types_disp.
Proof.
  apply make_disp_univalent_2.
  - exact p1types_disp_univalent_2_0.
  - exact p1types_disp_univalent_2_1.
Defined.

Lemma p1types_univalent_2 : is_univalent_2 p1types.
Proof.
  apply total_is_univalent_2.
  - apply p1types_disp_univalent_2.
  - apply one_types_is_univalent_2.
Defined.
