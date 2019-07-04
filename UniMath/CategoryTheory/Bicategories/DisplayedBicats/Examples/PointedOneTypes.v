(**
The univalent bicategory of pointed 1-types.
*)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OneTypes.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.
Local Open Scope bicategory_scope.

Definition p1types_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells one_types.
Proof.
  use tpair.
  - use tpair.
    + (** Objects and 1-cells *)
      use tpair.
      * (** Objects over a one type are points of X *)
        intro X. apply X.
      * cbn. intros X Y x y f.
        (** 1-cells over f are properties: f preserves points *)
        exact (f x = y).
    + (** Identity and composition of 1-cells: composition of properties *)
      use tpair.
      * cbn. intros X x. reflexivity.
      * cbn. intros X Y Z f g x y z.
        intros Hf Hg.
        etrans. { apply maponpaths, Hf. }
        apply Hg.
  - cbn. hnf. intros X Y f g α. cbn in *.
    (** Two cells over α : f = g *)
    intros x y ff gg. cbn in *.
    (* homotopies are stable w.r.t to point preservation *)
    exact (transportf (λ h, h = y) (α x) ff = gg).
Defined.

Definition p1types_disp_prebicat_ops : disp_prebicat_ops p1types_disp_prebicat_1_id_comp_cells.
Proof.
  repeat split; cbn.
  - intros X Y f x y ff.
    induction ff. reflexivity.
  - intros X Y f x y ff.
    induction ff. reflexivity.
  - intros X Y Z W f g h x y z w ff gg hh.
    induction ff. induction gg. reflexivity.
  - intros X Y Z W f g h x y z w ff gg hh.
    induction ff. induction gg. reflexivity.
  - intros X Y f g h α β x y ff gg hh αα ββ.
    unfold homotcomp.
    etrans. {
      apply (!transport_f_f (λ h, h = y) _ _ _). }
    etrans. {
      apply maponpaths.
      apply αα. }
    apply ββ.
  - (* Whiskering *)
    intros X Y Z f g h α x y z ff gg hh αα.
    induction ff. cbn. apply αα.
  - (* Whiskering *)
    intros X Y Z f g h α x y z ff gg hh αα.
    unfold homotfun.
    etrans. {
      apply transportf_id2. }
    induction (α x). cbn in *. cbv[idfun] in *.
    apply map_on_two_paths; [|reflexivity].
    apply maponpaths. apply αα.
Defined.

Local Definition one_type_to_hlevel (X: one_type)
      : isofhlevel 3 X := pr2 X.


Definition p1types_prebicat : disp_prebicat one_types.
Proof.
  use tpair.
  - exists p1types_disp_prebicat_1_id_comp_cells.
    apply p1types_disp_prebicat_ops.
  - repeat split; repeat intro; apply one_type_to_hlevel.
Defined.

Definition p1types_disp : disp_bicat one_types.
Proof.
  use tpair.
  - apply p1types_prebicat.
  - repeat intro. apply hlevelntosn. apply one_type_to_hlevel.
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
    use subtypePath. {
      intro. apply (isaprop_is_disp_invertible_2cell (D:=p1types_disp)).
    }
    apply Y.
Defined.

Lemma p1types_disp_univalent_2_0 : disp_univalent_2_0 p1types_disp.
Proof.
  apply fiberwise_univalent_2_0_to_disp_univalent_2_0.
  intros X x x'. cbn in *.
  use gradth; unfold idfun.
  - intros f. apply f.
  - intro p.
    induction p. reflexivity.
  - intros [f Hf].
    use subtypePath.
    { intros y y'.
      apply (isaprop_disp_left_adjoint_equivalence (D:=p1types_disp)).
      apply one_types_is_univalent_2.
      apply p1types_disp_univalent_2_1. }
    { cbn; cbn in f. induction f. cbn. reflexivity. }
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
