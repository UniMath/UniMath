(**************************************************************************************************

  Direct products of displayed categories

  Given displayed categories D1 and D2 over the same base C, we construct the displayed category
  D1 × D2 over C with (D1 × D2) c = (D1 c) × (D2 c).
  The isomorphisms in this category are equivalent to pairs of isomorphisms in D1 and D2. We can
  use this to show that the category is displayed univalent if both D1 and D2 are.
  And lastly, we can construct the projection displayed functors, lying over the identity functor on
  C, which project on the data of D1 or D2 respectively.

  Contents
  1. The product displayed category [dirprod_disp_cat D1 D2] [D1 × D2]
  2. A characterization of displayed isomorphism [z_iso_disp_prod_weq]
  3. Univalence [dirprod_disp_cat_is_univalent]
  4. The projecton displayed functors [dirprodpr1_disp_functor] [dirprodpr2_disp_functor]

 **************************************************************************************************)
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(** * 1. The product displayed category *)

(** * Products of displayed (pre)categories

We directly define direct products of displayed categories over a base.

An alternative would be to define the direct product as the [sigma_disp_cat] of the pullback to either factor.  *)

Definition dirprod_disp_cat_ob_mor
           {C : precategory_ob_mor} (D1 D2 : disp_cat_ob_mor C)
  : disp_cat_ob_mor C.
Proof.
  exists (λ c, D1 c × D2 c).
  intros x y xx yy f.
  exact (pr1 xx -->[f] pr1 yy × pr2 xx -->[f] pr2 yy).
Defined.

Definition dirprod_disp_cat_id_comp
           {C : precategory_data}
           (D1 D2 : disp_cat_data C)
  : disp_cat_id_comp _ (dirprod_disp_cat_ob_mor D1 D2).
Proof.
  apply tpair.
  - intros x (x1, x2).
    exact (id_disp x1,, id_disp x2).
  - intros x y z f g xx yy zz ff gg.
    exact ((pr1 ff ;; pr1 gg),, (pr2 ff ;; pr2 gg)).
Defined.

Definition dirprod_disp_cat_data
           {C : precategory_data}
           (D1 D2 : disp_cat_data C)
  : disp_cat_data C
  := (_ ,, dirprod_disp_cat_id_comp D1 D2).

Section Dirprod.

Context {C : category} (D1 D2 : disp_cat C).

Definition dirprod_disp_cat_axioms
  : disp_cat_axioms _ (dirprod_disp_cat_data D1 D2).
Proof.
  repeat apply make_dirprod.
  - intros. apply dirprod_paths; use (id_left_disp _ @ !_).
    + use pr1_transportf.
    + apply pr2_transportf.
  - intros. apply dirprod_paths; use (id_right_disp _ @ !_).
    + use pr1_transportf.
    + apply pr2_transportf.
  - intros. apply dirprod_paths; use (assoc_disp _ _ _ @ !_).
    + use pr1_transportf.
    + apply pr2_transportf.
  - intros. apply isaset_dirprod; apply homsets_disp.
Qed.

Definition dirprod_disp_cat : disp_cat C
  := (_ ,, dirprod_disp_cat_axioms).

(** * 2. A characterization of displayed isomorphism *)
(** TODO: generalize over an aritrary base isomorphism *)
Definition z_iso_disp_prod1
      {x : C}
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x) :
  @z_iso_disp _ dirprod_disp_cat _ _ (identity_z_iso x) (xx1,, xx2) (xx1',, xx2') →
  (z_iso_disp (identity_z_iso x) xx1 xx1') × (z_iso_disp (identity_z_iso x) xx2 xx2').
Proof.
  unfold z_iso_disp. cbn.
  intros [[f1 f2] Hff].
  destruct Hff as [[g1 g2] Hfg].
  cbn in Hfg. destruct Hfg as [Hgf Hfg].
  use tpair.
  - exists f1, g1.
    split.
    + etrans. apply (maponpaths dirprod_pr1 Hgf).
      apply pr1_transportf.
    + etrans. apply (maponpaths dirprod_pr1 Hfg).
      apply pr1_transportf.
  - exists f2, g2.
    split.
    + etrans. apply (maponpaths dirprod_pr2 Hgf).
      apply pr2_transportf.
    + etrans. apply (maponpaths dirprod_pr2 Hfg).
      apply pr2_transportf.
Defined.

Definition z_iso_disp_prod2
      {x : C}
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x) :
  (z_iso_disp (identity_z_iso x) xx1 xx1') × (z_iso_disp (identity_z_iso x) xx2 xx2') →
  @z_iso_disp _ dirprod_disp_cat _ _ (identity_z_iso x) (xx1,, xx2) (xx1',, xx2').
Proof.
  unfold z_iso_disp. cbn.
  intros [[f1 Hf1] [f2 Hf2]].
  destruct Hf1 as [g1 [Hgf1 Hfg1]].
  destruct Hf2 as [g2 [Hgf2 Hfg2]].
  exists (f1,,f2), (g1,,g2).
  split.
  - apply dirprod_paths.
    + etrans. apply Hgf1.
      apply pathsinv0. apply pr1_transportf.
    + etrans. apply Hgf2.
      apply pathsinv0. apply pr2_transportf.
  - apply dirprod_paths.
    + etrans. apply Hfg1.
      apply pathsinv0. apply pr1_transportf.
    + etrans. apply Hfg2.
      apply pathsinv0. apply pr2_transportf.
Defined.

Lemma z_iso_disp_prod21
      {x : C}
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x)
      i
:
  z_iso_disp_prod2 xx1 xx1' xx2 xx2' (z_iso_disp_prod1 xx1 xx1' xx2 xx2' i) = i.
Proof.
  apply eq_z_iso_disp. cbn. reflexivity.
Qed.

Lemma z_iso_disp_prod12
      {x : C}
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x)
      (t : z_iso_disp (identity_z_iso x) xx1 xx1' × z_iso_disp (identity_z_iso x) xx2 xx2')
:
  z_iso_disp_prod1 xx1 xx1' xx2 xx2' (z_iso_disp_prod2 xx1 xx1' xx2 xx2' t) = t.
Proof.
  apply dirprod_paths.
  - apply eq_z_iso_disp. cbn. reflexivity.
  - apply eq_z_iso_disp. cbn. reflexivity.
Qed.

Lemma z_iso_disp_prod_weq
      (x : C)
      (xx1 xx1' : D1 x)
      (xx2 xx2' : D2 x) :
  @z_iso_disp _ dirprod_disp_cat _ _ (identity_z_iso x) (xx1,, xx2) (xx1',, xx2') ≃
  (z_iso_disp (identity_z_iso x) xx1 xx1') × (z_iso_disp (identity_z_iso x) xx2 xx2').
Proof.
  exists (z_iso_disp_prod1 xx1 xx1' xx2 xx2').
  use isweq_iso.
  - apply z_iso_disp_prod2.
  - apply z_iso_disp_prod21.
  - apply z_iso_disp_prod12.
Defined.

(** * 3. Univalence *)

Lemma z_iso_disp_aux_weq
      (U1 : is_univalent_in_fibers D1)
      (U2 : is_univalent_in_fibers D2)
      (x : C)
      (xx xx' : D1 x × D2 x)

:
  xx = xx'
    ≃ @z_iso_disp _ dirprod_disp_cat _ _ (identity_z_iso x) xx xx'.
Proof.
  eapply weqcomp. apply pathsdirprodweq.
  apply invweq. eapply weqcomp. apply z_iso_disp_prod_weq.
  apply invweq.
  apply weqdirprodf.
  - exists idtoiso_fiber_disp. apply U1.
  - exists idtoiso_fiber_disp. apply U2.
Defined.

Lemma dirprod_disp_cat_is_univalent :
  is_univalent_disp D1 →
  is_univalent_disp D2 →
  is_univalent_disp dirprod_disp_cat.
Proof.
  intros HD1 HD2.
  apply is_univalent_disp_from_fibers.
  intros x xx xx'.
  use isweqhomot.
  - apply z_iso_disp_aux_weq.
    + apply is_univalent_in_fibers_from_univalent_disp.
      apply HD1.
    + apply is_univalent_in_fibers_from_univalent_disp.
      apply HD2.
  - intros p. induction p. cbn.
    apply (@eq_z_iso_disp _ dirprod_disp_cat).
    reflexivity.
  - apply z_iso_disp_aux_weq.
Defined.

(** * 4. The projecton displayed functors *)

Definition dirprodpr1_disp_functor_data
  : disp_functor_data (functor_identity C) dirprod_disp_cat (D1).
Proof.
  use tpair.
  - intros x xx; exact (pr1 xx).
  - intros x y xx yy f ff; exact (pr1 ff).
Defined.

Definition dirprodpr1_disp_functor_axioms
  : disp_functor_axioms dirprodpr1_disp_functor_data.
Proof.
  split.
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition dirprodpr1_disp_functor
  : disp_functor (functor_identity C) dirprod_disp_cat (D1)
:= (dirprodpr1_disp_functor_data,, dirprodpr1_disp_functor_axioms).


Definition dirprodpr2_disp_functor_data
  : disp_functor_data (functor_identity C) dirprod_disp_cat (D2).
Proof.
  use tpair.
  - intros x xx; exact (pr2 xx).
  - intros x y xx yy f ff; exact (pr2 ff).
Defined.

Definition dirprodpr2_disp_functor_axioms
  : disp_functor_axioms dirprodpr2_disp_functor_data.
Proof.
  split.
  - intros; apply idpath.
  - intros; apply idpath.
Qed.

Definition dirprodpr2_disp_functor
  : disp_functor (functor_identity C) dirprod_disp_cat (D2)
:= (dirprodpr2_disp_functor_data,, dirprodpr2_disp_functor_axioms).

End Dirprod.

Declare Scope disp_cat_scope.
Notation "D1 × D2" := (dirprod_disp_cat D1 D2) : disp_cat_scope.
Delimit Scope disp_cat_scope with disp_cat.
Bind Scope disp_cat_scope with disp_cat.
