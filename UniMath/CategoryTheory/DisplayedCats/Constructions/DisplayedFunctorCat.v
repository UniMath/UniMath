(**************************************************************************************************

  The category of displayed functors

  This is a displayed version of functor_category: a displayed category of displayed functors and
  displayed natural transformation between two displayed categories, lying over the functor category
  between the base categories.
  The isomorphisms in the ordinary functor category are exactly the natural transformations that are
  isomorphisms on every point. In the same way, the displayed isomorphisms in the displayed functor
  category are the morphisms over an isomorphism, that are a displayed isomorphism at every point.

  Contents
  1. The displayed functor category [disp_functor_cat]
  2. The characterization of displayed isomorphisms [is_disp_functor_cat_z_iso_iff_pointwise_z_iso]

 **************************************************************************************************)
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section Functor.
  (** * 1. The displayed functor category *)

  (* TODO: clean up this section a bit. *)

  Variables C' C : category.
  Variable D' : disp_cat C'.
  Variable D : disp_cat C.

  Let FunctorsC'C := functor_category C' C.

  Definition disp_functor_cat_data :
    disp_cat_data (FunctorsC'C).
  Proof.
    use tpair.
    - use tpair.
      + intro F.
        apply (disp_functor F D' D).
      + simpl. intros F' F FF' FF a.
        apply (disp_nat_trans a FF' FF).
    - use tpair.
      + intros x xx.
        apply disp_nat_trans_id.
      + intros ? ? ? ? ? ? ? ? X X0. apply (disp_nat_trans_comp X X0 ).
  Defined.

  Lemma disp_functor_cat_is_disp_cat
    : disp_cat_axioms _ disp_functor_cat_data.
  Proof.
    repeat split.
    - apply disp_nat_trans_id_left.
    - apply disp_nat_trans_id_right.
    - apply disp_nat_trans_assoc.
    - intros. apply isaset_disp_nat_trans.
  Qed.

  Definition disp_functor_cat :
    disp_cat (FunctorsC'C)
    := disp_functor_cat_data ,, disp_functor_cat_is_disp_cat.

  (** * 2. The characterization of displayed isomorphisms *)

  Definition pointwise_z_iso_from_nat_z_iso {A : precategory} {X : category}
    {F G : [A, X]}
    (b : z_iso F G) (a : A) : z_iso (pr1 F a) (pr1 G a)
    :=
    functor_z_iso_pointwise_if_z_iso _ _ _ _ _ b (pr2 b)_ .

  Definition pointwise_inv_is_inv_on_z_iso {A : precategory} {X : category}
    {F G : [A, X]}
    (b : z_iso F G) (a : A) :

    inv_from_z_iso (pointwise_z_iso_from_nat_z_iso b a) =
                                        pr1 (inv_from_z_iso b) a.
  Proof.
    apply idpath.
  Defined.

  Definition is_pointwise_z_iso_if_is_disp_functor_cat_z_iso
    (x y : FunctorsC'C)
    (f : z_iso x y)
    (xx : disp_functor_cat x)
    (yy : disp_functor_cat y)
    (FF : xx -->[ f ] yy)
    (H : is_z_iso_disp f FF)
    :
    forall x' (xx' : D' x') , is_z_iso_disp (pointwise_z_iso_from_nat_z_iso f _ )
                            (pr1 FF _ xx' ).
  Proof.
    intros x' xx'.
    use tpair.
    - set (X:= pr1 H). simpl in X.
      apply (transportb _ (pointwise_inv_is_inv_on_z_iso f _ ) (X x' xx')).
    - simpl. repeat split.
      + etrans. apply mor_disp_transportf_postwhisker.
        apply pathsinv0.
        apply transportf_comp_lemma.
        assert (XR:= pr1 (pr2 H)).
        assert (XRT :=  (maponpaths pr1 XR)).
        assert (XRT' :=  toforallpaths _ _ _  (toforallpaths _ _ _ XRT x')).
        apply pathsinv0.
        etrans. apply XRT'.
        clear XRT' XRT XR.
        assert (XR := @disp_nat_trans_transportf C' C D' D).
        specialize (XR _ _ _ _ (! z_iso_after_z_iso_inv f)).
        etrans. apply XR.
        apply maponpaths_2, homset_property.
      + etrans. apply mor_disp_transportf_prewhisker.
        apply pathsinv0.
        apply transportf_comp_lemma.
        assert (XR:= inv_mor_after_z_iso_disp H).
        assert (XRT :=  (maponpaths pr1 XR)).
        assert (XRT' :=  toforallpaths _ _ _  (toforallpaths _ _ _ XRT x')).
        apply pathsinv0.
        etrans. apply XRT'.
        clear XRT' XRT XR.
        assert (XR := @disp_nat_trans_transportf C' C D' D).
        specialize (XR _ _ _ _ (! z_iso_inv_after_z_iso f)).
        etrans. apply XR.
        apply maponpaths_2, homset_property.
  Defined.

  Lemma is_disp_nat_trans_pointwise_inv
    (x y : FunctorsC'C)
    (f : z_iso x y)
    (xx : disp_functor_cat x)
    (yy : disp_functor_cat y)
    (FF : xx -->[ f] yy)
    (H : ∏ (x' : C') (xx' : D' x'),
        is_z_iso_disp (pointwise_z_iso_from_nat_z_iso f x') (pr1 FF x' xx'))
    : disp_nat_trans_axioms (λ x' xx', inv_mor_disp_from_z_iso (H x' xx')).
  Proof.
    intros x' x0 f0 xx' xx0 ff.
    apply (precomp_with_z_iso_disp_is_inj (make_z_iso_disp _ (H x' xx'))).
    refine (assoc_disp _ _ _ @ _).
    symmetry.
    refine (mor_disp_transportf_prewhisker _ _ _ @ _).
    refine (maponpaths (transportf _ _) (assoc_disp _ _ _) @ _).
    refine (transport_f_f _ _ _ _ @ _).
    refine (maponpaths (λ x, transportf _ _ (x ;; _)) (inv_mor_after_z_iso_disp (H _ _)) @ _).
    refine (maponpaths (transportf _ _) (mor_disp_transportf_postwhisker _ _ _) @ _).
    refine (maponpaths (λ x, transportf _ _ (transportf _ _ x)) (id_left_disp _) @ _).
    refine (maponpaths (transportf _ _) (transport_f_f _ _ _ _) @ _).
    refine (transport_f_f _ _ _ _ @ _).
    symmetry.
    apply transportf_transpose_left.
    refine (!maponpaths (λ x, x ;; _) (transportf_transpose_left (pr2 FF x' x0 f0 xx' xx0 ff)) @ _).
    refine (mor_disp_transportf_postwhisker _ _ _ @ _).
    refine (maponpaths (transportf _ _) (assoc_disp_var _ _ _) @ _).
    refine (transport_f_f _ _ _ _ @ _).
    refine (maponpaths (λ x, transportf _ _ (_ ;; x)) (inv_mor_after_z_iso_disp (H _ _)) @ _).
    refine (maponpaths (transportf _ _) (mor_disp_transportf_prewhisker _ _ _) @ _).
    refine (transport_f_f _ _ _ _ @ _).
    refine (maponpaths (λ x, transportf _ _ x) (id_right_disp _) @ _).
    refine (transport_f_f _ _ _ _ @ _).
    symmetry.
    refine (transport_f_f _ _ _ _ @ _).
    apply (maponpaths (λ x, transportf _ x _)).
    apply homset_property.
  Qed.

  Definition inv_disp_from_pointwise_z_iso
    (x y : FunctorsC'C)
    (f : z_iso x y)
    (xx : disp_functor_cat x)
    (yy : disp_functor_cat y)
    (FF : xx -->[ f ] yy)
    (H : forall x' (xx' : D' x') , is_z_iso_disp (pointwise_z_iso_from_nat_z_iso f _ )
                            (pr1 FF _ xx' ))
    :
        yy -->[ inv_from_z_iso f] xx.
  Proof.
    use tpair.
    + intros x' xx'.
      exact (inv_mor_disp_from_z_iso (H x' xx')).
    + intros x' x0 f0 xx' xx0 ff.
      apply is_disp_nat_trans_pointwise_inv.
  Defined.

  Definition is_disp_functor_cat_z_iso_if_pointwise_z_iso
    (x y : FunctorsC'C)
    (f : z_iso x y)
    (xx : disp_functor_cat x)
    (yy : disp_functor_cat y)
    (FF : xx -->[ f ] yy)
    (H : forall x' (xx' : D' x') , is_z_iso_disp (pointwise_z_iso_from_nat_z_iso f _ )
                            (pr1 FF _ xx' ))
    : is_z_iso_disp f FF.
  Proof.
    use tpair.
    - exact (inv_disp_from_pointwise_z_iso _ _ _ _ _ FF H).
    - abstract (
        split;
        apply disp_nat_trans_eq;
        intros c' xx';
        refine (_ @ !disp_nat_trans_transportf _ _ _ _ _ _ _ _ _ _);
        [ refine (z_iso_disp_after_inv_mor (H _ _) @ _)
        | refine (inv_mor_after_z_iso_disp (H _ _) @ _) ];
        apply (maponpaths (λ x, transportf _ x _));
        apply homset_property
      ).
  Defined.

  Definition is_disp_functor_cat_z_iso_iff_pointwise_z_iso
    (x y : FunctorsC'C)
    (f : z_iso x y)
    (xx : disp_functor_cat x)
    (yy : disp_functor_cat y)
    (FF : xx -->[ f ] yy)
    :
    (∏ x' (xx' : D' x') , is_z_iso_disp (pointwise_z_iso_from_nat_z_iso f _ )
                            (pr1 FF _ xx' ))
      <->
      is_z_iso_disp f FF.
  Proof.
    split.
    - apply is_disp_functor_cat_z_iso_if_pointwise_z_iso.
    - apply is_pointwise_z_iso_if_is_disp_functor_cat_z_iso.
  Defined.

End Functor.
