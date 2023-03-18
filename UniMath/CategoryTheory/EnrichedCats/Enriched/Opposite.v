Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enriched.Enriched.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Section Opposite.

Context {Mon_V : monoidal_cat}.

Definition opposite_enriched_precat (A : enriched_precat Mon_V) : enriched_precat (_ ,, monoidal_swapped Mon_V).
Proof.
  use make_enriched_precat.
  - use make_enriched_precat_data.
    + exact A.
    + intros x y.
      exact (enriched_cat_mor y x).
    + intro x.
      simpl.
      exact (enriched_cat_identity x).
    + intros x y z.
      exact (enriched_cat_comp z y x).
  - split; simpl in a, b; simpl.
    + refine (_ @ enriched_id_right b a).
      apply maponpaths_2.
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      cbn.
      rewrite whiskerscommutes ; [ apply idpath | ].
      apply (pr2 Mon_V).
    + refine (_ @ enriched_id_left b a).
      apply maponpaths_2.
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      cbn.
      rewrite whiskerscommutes ; [ apply idpath | ].
      apply (pr2 Mon_V).
  - intros a b c d ; cbn.
    refine (!(id_left _) @ _).
    etrans.
    {
      apply maponpaths_2.
      exact (!(mon_rassociator_lassociator _ _ _)).
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ !(enriched_assoc d c b a) @ _).
    + apply maponpaths.
      apply maponpaths_2.
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      cbn.
      rewrite whiskerscommutes ; [ apply idpath | ].
      apply (pr2 Mon_V).
    + apply maponpaths_2.
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      cbn.
      rewrite whiskerscommutes ; [ apply idpath | ].
      apply (pr2 Mon_V).
Defined.

Definition opposite_enriched_functor {A B : enriched_precat Mon_V} (F : enriched_functor A B) : enriched_functor (opposite_enriched_precat A) (opposite_enriched_precat B).
Proof.
  use make_enriched_functor.
  - use make_enriched_functor_data.
    + intro x.
      exact (F x).
    + intros x y.
      exact (enriched_functor_on_morphisms F y x).
  - intro x.
    cbn.
    apply enriched_functor_on_identity.
  - intros x y z.
    cbn.
    refine (enriched_functor_on_comp F z y x @ _).
    apply maponpaths_2.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    cbn.
    rewrite whiskerscommutes ; [ apply idpath | ].
    apply (pr2 Mon_V).
Defined.

(* note the direction *)
Definition opposite_enriched_nat_trans {A B : enriched_precat Mon_V} {F G : enriched_functor A B} (a : enriched_nat_trans F G) : enriched_nat_trans (opposite_enriched_functor G) (opposite_enriched_functor F).
Proof.
  use make_enriched_nat_trans.
  - intro x.
    exact (a x).
  - intros x y.
    cbn.
    apply pathsinv0.
    refine (_ @ enriched_nat_trans_ax a y x @ _).
    + apply maponpaths.
      unfold precompose_underlying_morphism, postcompose_underlying_morphism.
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      cbn.
      rewrite <- whiskerscommutes ; [ apply idpath | ].
      apply (pr2 Mon_V).
    + apply maponpaths.
      unfold precompose_underlying_morphism, postcompose_underlying_morphism.
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      cbn.
      rewrite <- whiskerscommutes ; [ apply idpath | ].
      apply (pr2 Mon_V).
Defined.

End Opposite.
