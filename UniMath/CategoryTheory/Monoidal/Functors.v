(***************************************************************************

 Monoidal functors

 In this file, we define the several notions of functors between monoidal
 categories. Again we use a displayed approach where we define notions such
 as lax monoidal structures on functors. We also provide examples, such as
 the identity and composition. In the end, we provide bundled versions of
 these defintions.

 Note that for the bundled versions we reformulate the laws to guarantee the
 notation is consistent with the bundled versions for monoidal categories.

 Contents
 1. Lax monoidal functors
 2. Strong monoidal functors
 3. Strict monoidal functors
 4. Symmetric monoidal functors
 5. The identity is strong monoidal
 6. Composition preserves lax/strongly monoidal functors
 7. Monoidal natural transformations
 8. Inverses of monoidal natural transformations
 9. Bundled versions
 10. Builders for the bundled versions

Note: after refactoring on March 10, 2023, the prior Git history of this development is found via
git log -- UniMath/CategoryTheory/Monoidal/MonoidalFunctorsWhiskered.v

 ***************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section local_helper_lemmas.
  Lemma iso_stable_under_equality
        {C : category}
        {x y : C}
        {f g : C⟦x,y⟧}
        (p : g = f)
        (Hf : is_z_isomorphism f)
    : is_z_isomorphism g.
  Proof.
    induction p.
    exact Hf.
  Qed.

  Lemma iso_stable_under_transportf
        {C : category}
        {x y z : C}
        {f : C⟦x,y⟧}
        (pf : y=z)
        (Hf : is_z_isomorphism f)
    : is_z_isomorphism (transportf _ pf f).
  Proof.
    induction pf.
    use Hf.
  Qed.

  Lemma iso_stable_under_equalitytransportf
        {C : category}
        {x y z : C}
        {f : C⟦x,y⟧} {g : C⟦x,z⟧}
        {pf : y = z}
        (qg : g = transportf _ pf f)
        (Hf : is_z_isomorphism f)
    : is_z_isomorphism g.
  Proof.
    use (iso_stable_under_equality qg).
    use (iso_stable_under_transportf).
    exact Hf.
  Qed.
End local_helper_lemmas.


Section MonoidalFunctors.
  (**
   1. Lax monoidal functors
   *)
  (** (Weak) Monoidal functors **)
  (* Monoidal functor data *)

  Definition preserves_tensordata
             {C D : category}
             (M : monoidal C)
             (N : monoidal D)
             (F : functor C D)
    : UU
    := ∏ (x y : C), D ⟦ F x ⊗_{ N} F y, F (x ⊗_{ M} y) ⟧.

  Definition preserves_unit
             {C D : category}
             (M : monoidal C)
             (N : monoidal D)
             (F : functor C D)
    : UU
    := D ⟦ I_{N} , F I_{M} ⟧.

  Definition fmonoidal_data
             {C D : category}
             (M : monoidal C)
             (N : monoidal D)
             (F : functor C D)
    : UU
    := preserves_tensordata M N F × preserves_unit M N F.

  Definition fmonoidal_preservestensordata
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fmd : fmonoidal_data M N F)
    : preserves_tensordata M N F
    := pr1 fmd.

  Definition fmonoidal_preservesunit
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fmd : fmonoidal_data M N F)
    : preserves_unit M N F
    := pr2 fmd.

  Lemma fmonoidal_data_eq
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fmd1 fmd2 : fmonoidal_data M N F)
    : (∏ x y : C,  fmonoidal_preservestensordata fmd1 x y = fmonoidal_preservestensordata fmd2 x y) ->
      fmonoidal_preservesunit fmd1 = fmonoidal_preservesunit fmd2 -> fmd1 = fmd2.
  Proof.
    intros pT pU.
    use total2_paths_f.
    - do 2 (apply funextsec ; intro) ; apply pT.
    - rewrite transportf_const.
      apply pU.
  Qed.

  (** Properties **)
  Definition preserves_tensor_nat_left
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (pt : preserves_tensordata M N F)
    : UU
    := ∏ (x y1 y2 : C) (g : C⟦y1,y2⟧),
       F x ⊗^{ N}_{l} # F g · pt x y2
       =
       pt x y1 · # F (x ⊗^{ M}_{l} g).

  Definition preserves_tensor_nat_right
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (pt : preserves_tensordata M N F)
    : UU
    := ∏ (x1 x2 y : C) (f : C⟦x1,x2⟧),
       # F f ⊗^{ N}_{r} F y · pt x2 y
       =
       pt x1 y · # F (f ⊗^{ M}_{r} y).

  Definition preserves_leftunitality
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (pt : preserves_tensordata M N F)
             (pu : preserves_unit M N F)
    : UU
    := ∏ (x : C),
       (pu ⊗^{ N}_{r} F x) · (pt I_{M} x) · (# F lu^{ M }_{ x})
       =
       lu^{ N }_{ F x}.

  Definition preserves_leftunitalityinv
         {C D : category}
         {M : monoidal C}
         {N : monoidal D}
         {F : functor C D}
         (pt : preserves_tensordata M N F)
         (pu : preserves_unit M N F)
    : UU
    := ∏ (x : C),
       luinv^{ N }_{ F x} · (pu ⊗^{ N}_{r} F x) · (pt I_{M} x)
       =
       # F luinv^{ M }_{ x}.

  Definition preserves_rightunitality
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (pt : preserves_tensordata M N F)
             (pu : preserves_unit M N F)
    : UU
    := ∏ (x : C),
       ((F x ⊗^{ N}_{l} pu) · (pt x I_{M}) · (# F ru^{ M }_{ x})
       =
       ru^{ N }_{ F x}).

  Definition preserves_rightunitalityinv
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (pt : preserves_tensordata M N F)
             (pu : preserves_unit M N F)
    : UU
    := ∏ (x : C),
       ruinv^{ N }_{ F x} · F x ⊗^{ N}_{l} pu · pt x I_{M}
       =
       # F ruinv^{ M }_{ x}.

  Definition preserves_associativity
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (pt : preserves_tensordata M N F)
    : UU
    := ∏ (x y z : C),
       ((pt x y) ⊗^{N}_{r} (F z)) · (pt (x ⊗_{M} y) z) · (#F (α^{M}_{x,y,z}))
       =
       α^{N}_{F x, F y, F z} · ((F x) ⊗^{N}_{l} (pt y z)) · (pt x (y ⊗_{M} z)).

  Definition preserves_associativityinv
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (pt : preserves_tensordata M N F)
    : UU
    := ∏ (x y z : C),
       αinv^{N}_{F x, F y, F z} · ((pt x y) ⊗^{N}_{r} (F z)) · (pt (x ⊗_{M} y) z)
       =
       ((F x) ⊗^{N}_{l} (pt y z)) · (pt x (y ⊗_{M} z)) · (#F (αinv^{M}_{x,y,z})).

  Definition fmonoidal_laxlaws
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fmd : fmonoidal_data M N F)
    : UU
    := (preserves_tensor_nat_left (fmonoidal_preservestensordata fmd)) ×
       (preserves_tensor_nat_right (fmonoidal_preservestensordata fmd)) ×
       (preserves_associativity (fmonoidal_preservestensordata fmd)) ×
       (preserves_leftunitality
          (fmonoidal_preservestensordata fmd)
          (fmonoidal_preservesunit fmd)) ×
       (preserves_rightunitality
          (fmonoidal_preservestensordata fmd)
          (fmonoidal_preservesunit fmd)).

  Lemma isaprop_fmonoidal_laxlaws
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fmd : fmonoidal_data M N F) : isaprop (fmonoidal_laxlaws fmd).
  Proof.
    repeat (apply isapropdirprod); repeat (apply impred; intro); apply D.
  Qed.

  Definition fmonoidal_lax
             {C D : category}
             (M : monoidal C)
             (N : monoidal D)
             (F : functor C D)
    : UU
    := ∑ (fmd : fmonoidal_data M N F), fmonoidal_laxlaws fmd.

  Definition fmonoidal_fdata
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fm : fmonoidal_lax M N F)
    : fmonoidal_data M N F
    := pr1 fm.
  Coercion fmonoidal_fdata : fmonoidal_lax >-> fmonoidal_data.

  Lemma fmonoidal_lax_eq
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fmd fmd' : fmonoidal_lax M N F) :
    pr1 fmd = pr1 fmd' -> fmd = fmd'.
  Proof.
    intro H.
    apply subtypePath.
    - intro; apply isaprop_fmonoidal_laxlaws.
    - exact H.
  Qed.

  Definition fmonoidal_flaws
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fm : fmonoidal_lax M N F)
    : fmonoidal_laxlaws fm
    := pr2 fm.

  Definition fmonoidal_preservestensornatleft
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fm : fmonoidal_lax M N F)
    : preserves_tensor_nat_left (fmonoidal_preservestensordata fm)
    := pr12 fm.

  Definition fmonoidal_preservestensornatright
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fm : fmonoidal_lax M N F)
    : preserves_tensor_nat_right (fmonoidal_preservestensordata fm)
    := pr122 fm.

  Definition fmonoidal_preservesassociativity
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fm : fmonoidal_lax M N F)
    : preserves_associativity (fmonoidal_preservestensordata fm)
    := pr1 (pr222 fm).

  Lemma fmonoidal_preservesassociativityinv
        {C D : category}
        {M : monoidal C}
        {N : monoidal D}
        {F : functor C D}
        (fm : fmonoidal_lax M N F)
    : preserves_associativityinv (fmonoidal_preservestensordata fm).
  Proof.
    intros x y z.
    rewrite assoc'.
    apply (z_iso_inv_on_right _ _ _ (_,,_,, monoidal_associatorisolaw N _ _ _)).
    cbn.
    etrans.
    2: { repeat rewrite assoc. apply cancel_postcomposition.
         apply fmonoidal_preservesassociativity. }
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    2: { apply maponpaths.
         rewrite <- functor_comp.
         apply maponpaths.
         apply pathsinv0, (monoidal_associatorisolaw M). }
    rewrite functor_id.
    apply pathsinv0, id_right.
  Qed.

  Definition fmonoidal_preservesleftunitality
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fm : fmonoidal_lax M N F)
    : preserves_leftunitality
        (fmonoidal_preservestensordata fm)
        (fmonoidal_preservesunit fm)
    := pr12 (pr222 fm).

  Lemma fmonoidal_preservesleftunitalityinv
        {C D : category}
        {M : monoidal C}
        {N : monoidal D}
        {F : functor C D}
        (fm : fmonoidal_lax M N F)
    : preserves_leftunitalityinv
        (fmonoidal_preservestensordata fm)
        (fmonoidal_preservesunit fm).
  Proof.
    intro x.
    rewrite assoc'.
    apply (z_iso_inv_on_right _ _ _ (_,,_,, monoidal_leftunitorisolaw N (F x))).
    cbn.
    rewrite <- (fmonoidal_preservesleftunitality fm).
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    2: { apply maponpaths.
         apply functor_comp. }
    etrans.
    2: { do 2 apply maponpaths.
         apply pathsinv0, (pr1(monoidal_leftunitorisolaw M x)). }
    rewrite functor_id.
    apply pathsinv0, id_right.
  Qed.

  Definition fmonoidal_preservesrightunitality
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fm : fmonoidal_lax M N F)
    : preserves_rightunitality
        (fmonoidal_preservestensordata fm)
        (fmonoidal_preservesunit fm)
    := pr22 (pr222 fm).

  Lemma fmonoidal_preservesrightunitalityinv
        {C D : category}
        {M : monoidal C}
        {N : monoidal D}
        {F : functor C D}
        (fm : fmonoidal_lax M N F)
    : preserves_rightunitalityinv
        (fmonoidal_preservestensordata fm)
        (fmonoidal_preservesunit fm).
  Proof.
    intro x.
    rewrite assoc'.
    apply (z_iso_inv_on_right _ _ _ (_,,_,, monoidal_rightunitorisolaw N (F x))).
    cbn.
    rewrite <- (fmonoidal_preservesrightunitality fm).
    repeat rewrite assoc'.
    apply maponpaths.
    etrans.
    2: { apply maponpaths.
         apply functor_comp. }
    etrans.
    2: { do 2 apply maponpaths.
         apply pathsinv0, (pr1(monoidal_rightunitorisolaw M x)). }
    rewrite functor_id.
    apply pathsinv0, id_right.
  Qed.

  Definition preserves_tensor_strongly
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             (pt : preserves_tensordata M N F)
    : UU
    := ∏ (x y : C), is_z_isomorphism (pt x y).

  Definition pointwise_z_iso_from_preserves_tensor_strongly
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             {pt : preserves_tensordata M N F}
             (pts : preserves_tensor_strongly pt) (x y : C)
    : z_iso (F x ⊗_{ N} F y) (F (x ⊗_{ M} y))
    := pt x y ,, pts x y.

  Lemma preserves_associativity_of_inverse_preserves_tensor
        {C D : category}
        {M : monoidal C} {N : monoidal D}
        {F : functor C D}
        {pt : preserves_tensordata M N F}
        (ptα : preserves_associativity pt)
        (pts : preserves_tensor_strongly pt) (x y z : C)
    : (is_z_isomorphism_mor (pts (x ⊗_{M} y) z))
      · ((is_z_isomorphism_mor (pts x y)) ⊗^{N}_{r} (F z))
      · α^{N}_{F x, F y, F z}
      =
      (#F (α^{M}_{x,y,z}))
      · (is_z_isomorphism_mor (pts x (y ⊗_{M} z)))
      · ((F x) ⊗^{N}_{l} (is_z_isomorphism_mor (pts y z))).
  Proof.
    set (ptsx_yz := pointwise_z_iso_from_preserves_tensor_strongly pts x (y ⊗_{M} z)).
    set (ptsxy_z := pointwise_z_iso_from_preserves_tensor_strongly pts (x ⊗_{M} y) z).
    set (ptsfx := functor_on_z_iso
          (leftwhiskering_functor N (F x))
          (pointwise_z_iso_from_preserves_tensor_strongly pts y z)).
    set (ptsfz := functor_on_z_iso
          (rightwhiskering_functor N (F z))
          (pointwise_z_iso_from_preserves_tensor_strongly pts x y)).

    apply (z_iso_inv_on_left _ _ _ _ ptsfx).
    apply pathsinv0.
    apply (z_iso_inv_on_left _ _ _ _ ptsx_yz).
    rewrite assoc'.
    rewrite assoc'.
    etrans.
    2: {
      apply maponpaths.
      rewrite assoc.
      exact (ptα x y z).
    }
    etrans.
    2: {
      rewrite assoc'.
      apply maponpaths.
      rewrite assoc.
      apply maponpaths_2.
      rewrite assoc.
      apply maponpaths_2.
      exact (! pr222 ptsfz).
    }
    rewrite id_left.
    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      exact (! pr222 ptsxy_z).
    }
    apply (! id_left _).
  Qed.

  Lemma preserves_tensorinv_nat_right
        {C D : category}
        {M : monoidal C} {N : monoidal D}
        {F : functor C D}
        {pt : preserves_tensordata M N F}
        (pts : preserves_tensor_strongly pt)
        (ptrn : preserves_tensor_nat_right pt)
        (x1 x2 y : C)
        (f : C⟦x1,x2⟧)
    : (is_z_isomorphism_mor (pts x1 y)) · # F f ⊗^{ N}_{r} F y
      =
      # F (f ⊗^{ M}_{r} y) · (is_z_isomorphism_mor (pts x2 y)).
  Proof.
    set (ptiso := pt x1 y ,, pts x1 y : z_iso _ _).
    apply (z_iso_inv_on_right _ _ _ ptiso).
    rewrite assoc.
    etrans.
    2: {
      apply maponpaths_2.
      apply ptrn.
    }
    rewrite assoc'.
    unfold is_z_isomorphism_mor.
    rewrite (pr12 (pts x2 y)).
    apply (! id_right _).
  Qed.

  Lemma preserves_tensorinv_nat_left
        {C D : category}
        {M : monoidal C} {N : monoidal D}
        {F : functor C D}
        {pt : preserves_tensordata M N F}
        (pts : preserves_tensor_strongly pt)
        (ptrn : preserves_tensor_nat_left pt)
        (x1 x2 y : C)
        (f : C⟦x1,x2⟧)
    : (is_z_isomorphism_mor (pts y x1)) · F y ⊗^{ N}_{l} # F f
      =
      # F (y ⊗^{ M}_{l} f) · (is_z_isomorphism_mor (pts y x2)).
  Proof.
    set (ptiso := pt y x1 ,, pts y x1 : z_iso _ _).
    apply (z_iso_inv_on_right _ _ _ ptiso).
    rewrite assoc.
    etrans.
    2: {
      apply maponpaths_2.
      apply ptrn.
    }
    rewrite assoc'.
    unfold is_z_isomorphism_mor.
    rewrite (pr12 (pts y x2)).
    apply (! id_right _).
  Qed.

  Definition preserves_unit_strongly
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             (pu : preserves_unit M N F)
    : UU
    := is_z_isomorphism pu.

  Definition fmonoidal_stronglaws
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             (pt : preserves_tensordata M N F)
             (pu : preserves_unit M N F)
    : UU
    := preserves_tensor_strongly pt × preserves_unit_strongly pu.

  Lemma isaprop_fmonoidal_stronglaws
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             (Fm : fmonoidal_data M N F)
    : isaprop (fmonoidal_stronglaws (pr1 Fm) (pr2 Fm)).
  Proof.
    apply isapropdirprod ; repeat (apply impred_isaprop ; intro) ; apply isaprop_is_z_isomorphism.
  Qed.

  (**
   2. Strong monoidal functors
   *)
  Definition fmonoidal
             {C D : category}
             (M : monoidal C)
             (N : monoidal D)
             (F : functor C D)
    : UU :=
    ∑ (Fm : fmonoidal_lax M N F),
      fmonoidal_stronglaws (fmonoidal_preservestensordata Fm) (fmonoidal_preservesunit Fm).

  Definition fmonoidal_fmonoidallax
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             (Fm : fmonoidal M N F)
    : fmonoidal_lax M N F
    := pr1 Fm.
  Coercion fmonoidal_fmonoidallax : fmonoidal >-> fmonoidal_lax.

  Definition fmonoidal_preservestensorstrongly
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             (Fm : fmonoidal M N F)
    : preserves_tensor_strongly (fmonoidal_preservestensordata Fm)
    := pr12 Fm.

  Definition fmonoidal_preservesunitstrongly
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             (Fm : fmonoidal M N F)
    : preserves_unit_strongly (fmonoidal_preservesunit Fm)
    := pr22 Fm.

  Lemma fmonoidal_eq
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             (fmd fmd' : fmonoidal M N F) :
    pr1 fmd = pr1 fmd' -> fmd = fmd'.
  Proof.
    intro H.
    apply subtypePath.
    - intro; apply isaprop_fmonoidal_stronglaws.
    - exact H.
  Qed.

  (** We now show that everything behaves as expected **)
  Definition functor_imageoftensor
             {C D : category}
             (M : monoidal C)
             (F : functor C D)
    : bifunctor C C D
    := compose_bifunctor_with_functor M F.

  Definition functor_tensorofimages
             {C D : category}
             (F : functor C D)
             (N : monoidal D)
    : bifunctor C C D
    := compose_functor_with_bifunctor F F N.

  Definition preserves_tensor_is_nattrans_type
             {C D : category}
             (M : monoidal C)
             (N : monoidal D)
             (F : functor C D)
    : UU
    := binat_trans (functor_tensorofimages F N) (functor_imageoftensor M F).

  (* I really don't know how to call the following lemma *)
  Definition preservestensor_is_nattrans
             {C D : category}
             {M : monoidal C}
             {N : monoidal D}
             {F : functor C D}
             {pt : preserves_tensordata M N F}
             (ptnl : preserves_tensor_nat_left pt)
             (ptnr : preserves_tensor_nat_right pt)
    : preserves_tensor_is_nattrans_type M N F.
  Proof.
    use make_binat_trans.
    - use make_binat_trans_data.
      intros x y.
      apply pt.
    - use tpair.
      + intros x y1 y2 g.
        apply ptnl.
      + intros x1 x2 y f.
        apply ptnr.
  Defined.

  Lemma preservestensor_is_nattrans_full
        {C D : category}
        {M : monoidal C}
        {N : monoidal D}
        {F : functor C D}
        {pt : preserves_tensordata M N F}
        (ptnl : preserves_tensor_nat_left pt)
        (ptnr : preserves_tensor_nat_right pt)
    : ∏ (x1 x2 y1 y2 : C) (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
      # F f ⊗^{ N} # F g · pt x2 y2 = pt x1 y1 · # F (f ⊗^{ M} g).
  Proof.
    intros.
    etrans.
    { unfold functoronmorphisms1.
      rewrite assoc'.
      rewrite ptnl.
      apply assoc. }
    rewrite ptnr.
    rewrite assoc'.
    apply maponpaths.
    apply pathsinv0, functor_comp.
  Qed.

  Definition preserves_tensor_inv_is_nattrans_type
             {C D : category}
             (M : monoidal C) (N : monoidal D)
             (F : functor C D)
    : UU
    := binat_trans (functor_imageoftensor M F) (functor_tensorofimages F N).

  (* name follows [preservestensor_is_nattrans], for lack of a better proposition *)
  Definition preservestensor_inv_is_nattrans
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             {pt : preserves_tensordata M N F}
             (ptnl : preserves_tensor_nat_left pt)
             (ptnr : preserves_tensor_nat_right pt)
             (ptstr: preserves_tensor_strongly pt)
    : preserves_tensor_inv_is_nattrans_type M N F
    := inv_binattrans_from_binatiso(α:=preservestensor_is_nattrans ptnl ptnr) ptstr.


  Definition preserves_leftunitality'
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             {pt : preserves_tensordata M N F}
             {pu : preserves_unit M N F}
             (plu : preserves_leftunitality pt pu)
    : ∏ (x : C),
      (pu ⊗^{N} (identity (F x))) · (pt I_{M} x) · (#F (lu^{M}_{x}))
      =
      lu^{N}_{F x}.
  Proof.
    intro x.
    unfold functoronmorphisms1.
    rewrite (bifunctor_leftid N).
    rewrite id_right.
    apply plu.
  Qed.

  Definition preserves_rightunitality'
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             {pt : preserves_tensordata M N F}
             {pu : preserves_unit M N F}
             (pru : preserves_rightunitality pt pu)
    : ∏ (x : C),
      ((identity (F x)) ⊗^{N} pu) · (pt x I_{M}) · (#F (ru^{M}_{x}))
      =
      ru^{N}_{F x}.
  Proof.
    intro x.
    unfold functoronmorphisms1.
    rewrite (bifunctor_rightid N).
    rewrite id_left.
    apply pru.
  Qed.

  Definition preserves_leftunitality''
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D} (Fm : fmonoidal M N F)
    : ∏ (x : C),
      (pr1 (fmonoidal_preservestensorstrongly Fm I_{M} x))
      · (pr1 (fmonoidal_preservesunitstrongly Fm) ⊗^{N} (identity (F x)))
      · lu^{N}_{F x}
      =
      #F (lu^{M}_{x}).
  Proof.
    intro x.
    set (plu := preserves_leftunitality' (fmonoidal_preservesleftunitality (pr1 Fm)) x).
    rewrite (! plu).
    rewrite ! assoc.

    etrans. {
      apply maponpaths_2.
      apply maponpaths_2.
      rewrite assoc'.
      apply maponpaths.
      unfold functoronmorphisms1.
      do 2 rewrite (bifunctor_leftid N).
      do 2 rewrite id_right.
      rewrite <- (bifunctor_rightcomp N).
      apply maponpaths.
      apply (fmonoidal_preservesunitstrongly Fm).
    }
    rewrite bifunctor_rightid.
    rewrite id_right.
    etrans. {
      apply maponpaths_2.
      apply (fmonoidal_preservestensorstrongly Fm).
    }
    apply id_left.
  Qed.

  Proposition strong_fmonoidal_preserves_associativity
              {C D : category}
              {M : monoidal C} {N : monoidal D}
              {F : functor C D}
              (Fm : fmonoidal M N F)
              (x y z : C)
    : # F (α^{M}_{x , y , z})
      =
      inv_from_z_iso (_ ,, fmonoidal_preservestensorstrongly Fm _ _)
      · (inv_from_z_iso (_ ,, fmonoidal_preservestensorstrongly Fm _ _) ⊗^{N}_{r} _)
      · (α^{N}_{ F x , F y , F z})
      · (F x ⊗^{ N}_{l} fmonoidal_preservestensordata Fm y z)
      · fmonoidal_preservestensordata Fm x (y ⊗_{ M} z).
  Proof.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      exact (!(fmonoidal_preservesassociativity Fm x y z)).
    }
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        refine (!_).
        apply (bifunctor_rightcomp N).
      }
      apply maponpaths.
      apply z_iso_after_z_iso_inv.
    }
    rewrite (bifunctor_rightid N).
    rewrite id_left.
    apply z_iso_after_z_iso_inv.
  Qed.

  (**
   3. Strict monoidal functors
   *)
  (* Strictly preserving monoidal functors *)
  Definition preserves_tensor_strictly
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             (pt : preserves_tensordata M N F)
    : UU
    := ∏ (x y : C), ∑ (pf : (F x) ⊗_{N} (F y) = F (x ⊗_{M} y)),
       pt x y = transportf _ pf (identity ((F x) ⊗_{N} (F y))).

  Lemma strictlytensorpreserving_is_strong
        {C D : category}
        {M : monoidal C} {N : monoidal D}
        {F : functor C D}
        {pt : preserves_tensordata M N F}
        (pst : preserves_tensor_strictly pt)
    : preserves_tensor_strongly pt.
  Proof.
    intros x y.
    use (iso_stable_under_equalitytransportf
           (pr2 (pst x y))
           (is_z_isomorphism_identity (F x ⊗_{N} F y))).
  Qed.

  Definition preserves_unit_strictly
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             (pu : preserves_unit M N F) : UU
    := ∑ (pf : I_{N} = (F I_{M})),
       pu = transportf _ pf (identity I_{N}).

  Definition strictlyunitpreserving_is_strong
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             {F : functor C D}
             {pu : preserves_unit M N F}
             (pus : preserves_unit_strictly pu)
    : preserves_unit_strongly pu.
  Proof.
    use (iso_stable_under_equalitytransportf (pr2 pus) (is_z_isomorphism_identity I_{N})).
  Defined.

  (**
   4. Symmetric monoidal functors
   *)
  Definition is_symmetric_monoidal_functor
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             (HM : symmetric M) (HN : symmetric N)
             {F : functor C D}
             (HF : fmonoidal_lax M N F)
    : UU
    := ∏ (x y : C),
       monoidal_braiding_data (symmetric_to_braiding HN) (F x) (F y)
       · fmonoidal_preservestensordata HF y x
       =
       fmonoidal_preservestensordata HF x y
       · #F(monoidal_braiding_data (symmetric_to_braiding HM) x y).

  Lemma isaprop_is_symmetric_monoidal_functor
             {C D : category}
             {M : monoidal C} {N : monoidal D}
             (HM : symmetric M) (HN : symmetric N)
             {F : functor C D}
             (HF : fmonoidal_lax M N F) :
    isaprop (is_symmetric_monoidal_functor HM HN HF).
  Proof.
    apply impred; intro c; apply impred; intro c'; apply D.
  Qed.

  (**
   5. The identity is strong monoidal
   *)
  (** towards a bicategory of monoidal categories *)
  Definition identity_fmonoidal_data
             {C : category}
             (M : monoidal C)
    : fmonoidal_data M M (functor_identity C).
  Proof.
    split.
    - intros x y. apply identity.
    - apply identity.
  Defined.

  Lemma identity_fmonoidal_laxlaws
        {C : category}
        (M : monoidal C)
    : fmonoidal_laxlaws (identity_fmonoidal_data M).
  Proof.
    repeat split; red; unfold fmonoidal_preservesunit, fmonoidal_preservestensordata; cbn; intros.
    - rewrite id_left. apply id_right.
    - rewrite id_left. apply id_right.
    - do 2 rewrite id_right.
      rewrite (bifunctor_rightid M).
      rewrite (bifunctor_leftid M).
      rewrite id_right.
      apply id_left.
    - rewrite id_right.
      rewrite (bifunctor_rightid M).
      apply id_left.
    - rewrite id_right.
      rewrite (bifunctor_leftid M).
      apply id_left.
  Qed.

  Definition identity_fmonoidal_lax
             {C : category}
             (M : monoidal C)
    : fmonoidal_lax M M (functor_identity C)
    := identity_fmonoidal_data M ,, identity_fmonoidal_laxlaws M.

  Definition identity_fmonoidal_stronglaws
             {C : category}
             (M : monoidal C)
    : fmonoidal_stronglaws
        (fmonoidal_preservestensordata (identity_fmonoidal_lax M))
        (fmonoidal_preservesunit (identity_fmonoidal_lax M)).
  Proof.
    split.
    - intros x y. apply is_z_isomorphism_identity.
    - apply is_z_isomorphism_identity.
  Defined.

  Definition identity_fmonoidal
             {C : category}
             (M : monoidal C)
    : fmonoidal M M (functor_identity C)
    := identity_fmonoidal_lax M ,, identity_fmonoidal_stronglaws M.

  Proposition is_symmetric_monoidal_identity
              {C : category}
              {M : monoidal C}
              (HM : symmetric M)
    : is_symmetric_monoidal_functor HM HM (identity_fmonoidal_lax M).
  Proof.
    intros x y.
    cbn.
    rewrite id_left, id_right.
    apply idpath.
  Qed.

  (**
   6. Composition preserves lax/strongly monoidal functors
   *)
  Definition comp_fmonoidal_data
             {C D E : category}
             {M : monoidal C} {N : monoidal D} {O : monoidal E}
             {F : C ⟶ D} {G : D ⟶ E}
             (Fm : fmonoidal_lax M N F) (Gm : fmonoidal_lax N O G)
    : fmonoidal_data M O (F ∙ G).
  Proof.
    split.
    - intros x y.
      exact (fmonoidal_preservestensordata Gm (F x) (F y)
             · #G (fmonoidal_preservestensordata Fm x y)).
    - exact (fmonoidal_preservesunit Gm
            · #G (fmonoidal_preservesunit Fm)).
  Defined.

  Lemma comp_fmonoidal_laxlaws
        {C D E : category}
        {M : monoidal C} {N : monoidal D} {O : monoidal E}
        {F : C ⟶ D} {G : D ⟶ E}
        (Fm : fmonoidal_lax M N F) (Gm : fmonoidal_lax N O G)
    : fmonoidal_laxlaws (comp_fmonoidal_data Fm Gm).
  Proof.
    repeat split; red; cbn; unfold fmonoidal_preservesunit, fmonoidal_preservestensordata; cbn; intros.
    - etrans.
      2: { rewrite assoc'. apply maponpaths. apply functor_comp. }
      etrans.
      2: { do 2 apply maponpaths. apply fmonoidal_preservestensornatleft. }
      rewrite functor_comp.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply fmonoidal_preservestensornatleft.
    - etrans.
      2: { rewrite assoc'. apply maponpaths. apply functor_comp. }
      etrans.
      2: { do 2 apply maponpaths. apply fmonoidal_preservestensornatright. }
      rewrite functor_comp.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply fmonoidal_preservestensornatright.
    - assert (auxF := fmonoidal_preservesassociativity Fm x y z).
      unfold fmonoidal_preservestensordata in auxF.
      assert (auxG := fmonoidal_preservesassociativity Gm (F x) (F y) (F z)).
      unfold fmonoidal_preservestensordata in auxG.
      rewrite (bifunctor_leftcomp O).
      rewrite (bifunctor_rightcomp O).
      etrans.
      2: { repeat rewrite assoc. apply cancel_postcomposition.
           repeat rewrite assoc'. do 2 apply maponpaths.
           apply pathsinv0, fmonoidal_preservestensornatleft. }
      etrans.
      2: { apply cancel_postcomposition.
           repeat rewrite assoc. apply cancel_postcomposition.
           exact auxG. }
      repeat rewrite assoc'. apply maponpaths.
      etrans.
      2: { apply maponpaths.
           rewrite <- functor_comp.
           apply functor_comp. }
      etrans.
      2: { do 2 apply maponpaths.
           rewrite assoc.
           exact auxF. }
      do 2 rewrite functor_comp.
      repeat rewrite assoc.
      do 2 apply cancel_postcomposition.
      apply fmonoidal_preservestensornatright.
    - assert (auxF := fmonoidal_preservesleftunitality Fm x).
      assert (auxG := fmonoidal_preservesleftunitality Gm (F x)).
      unfold fmonoidal_preservesunit, fmonoidal_preservestensordata in auxF, auxG.
      etrans; [| exact auxG].
      clear auxG.
      rewrite (bifunctor_rightcomp O).
      rewrite <- auxF.
      clear auxF.
      do 2 rewrite functor_comp.
      repeat rewrite assoc.
      do 2 apply cancel_postcomposition.
      repeat rewrite assoc'.
      apply maponpaths.
      apply fmonoidal_preservestensornatright.
    - assert (auxF := fmonoidal_preservesrightunitality Fm x).
      assert (auxG := fmonoidal_preservesrightunitality Gm (F x)).
      unfold fmonoidal_preservesunit, fmonoidal_preservestensordata in auxF, auxG.
      etrans; [| exact auxG].
      clear auxG.
      rewrite (bifunctor_leftcomp O).
      rewrite <- auxF.
      clear auxF.
      do 2 rewrite functor_comp.
      repeat rewrite assoc.
      do 2 apply cancel_postcomposition.
      repeat rewrite assoc'.
      apply maponpaths.
      apply fmonoidal_preservestensornatleft.
  Qed.

  Definition comp_fmonoidal_lax
             {C D E : category}
             {M : monoidal C} {N : monoidal D} {O : monoidal E}
             {F : C ⟶ D} {G : D ⟶ E}
             (Fm : fmonoidal_lax M N F) (Gm : fmonoidal_lax N O G)
    : fmonoidal_lax M O (F ∙ G)
    := comp_fmonoidal_data Fm Gm ,, comp_fmonoidal_laxlaws Fm Gm.

  Section CompStrongMonoidal.
    Context {C D E : category}
            {M : monoidal C} {N : monoidal D} {O : monoidal E}
            {F : C ⟶ D} {G : D ⟶ E}
            (Fm : fmonoidal M N F) (Gm : fmonoidal N O G).

    Let comp_fmnoidal_unit_inv
      : G (F I_{M}) --> I_{O}
      := #G (pr1 (fmonoidal_preservesunitstrongly Fm))
         · pr1 (fmonoidal_preservesunitstrongly Gm).

    Let comp_fmonoidal_tensor_inv
        (x y : C)
      : G (F (x ⊗_{ M } y)) --> G (F x) ⊗_{ O } G (F y)
      := #G (pr1 (fmonoidal_preservestensorstrongly Fm x y))
         · pr1 (fmonoidal_preservestensorstrongly Gm (F x) (F y)).

    Lemma comp_fmonoidal_tensor_inv_laws
          (x y : C)
      : is_inverse_in_precat
          (fmonoidal_preservestensordata (comp_fmonoidal_lax Fm Gm) x y)
          (comp_fmonoidal_tensor_inv x y).
    Proof.
      unfold comp_fmonoidal_tensor_inv.
      split.
      - cbn.
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite assoc.
          apply cancel_postcomposition.
          rewrite <- functor_comp.
          apply maponpaths.
          apply (pr12 (fmonoidal_preservestensorstrongly Fm x y)).
        }
        rewrite functor_id.
        rewrite id_left.
        apply (pr12 (fmonoidal_preservestensorstrongly Gm (F x) (F y))).
      - cbn.
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite assoc.
          apply cancel_postcomposition.
          apply (pr22 (fmonoidal_preservestensorstrongly Gm (F x) (F y))).
        }
        rewrite id_left.
        rewrite <- functor_comp.
        etrans.
        {
          apply maponpaths.
          apply (pr22 (fmonoidal_preservestensorstrongly Fm x y)).
        }
        apply functor_id.
    Qed.

    Lemma comp_fmonoidal_unit_inv_laws
      : is_inverse_in_precat
          (fmonoidal_preservesunit (comp_fmonoidal_lax Fm Gm))
          comp_fmnoidal_unit_inv.
    Proof.
      unfold comp_fmnoidal_unit_inv.
      split.
      - cbn.
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite assoc.
          apply cancel_postcomposition.
          rewrite <- functor_comp.
          apply maponpaths.
          apply (pr12 (fmonoidal_preservesunitstrongly Fm)).
        }
        rewrite functor_id.
        rewrite id_left.
        apply (pr12 (fmonoidal_preservesunitstrongly Gm)).
      - cbn.
        etrans.
        {
          rewrite !assoc'.
          apply maponpaths.
          rewrite assoc.
          apply cancel_postcomposition.
          apply (pr22 (fmonoidal_preservesunitstrongly Gm)).
        }
        rewrite id_left.
        rewrite <- functor_comp.
        etrans.
        {
          apply maponpaths.
          apply (pr22 (fmonoidal_preservesunitstrongly Fm)).
        }
        apply functor_id.
    Qed.

    Definition comp_fmonoidal_stronglaws
      : fmonoidal_stronglaws
          (fmonoidal_preservestensordata (comp_fmonoidal_lax Fm Gm))
          (fmonoidal_preservesunit (comp_fmonoidal_lax Fm Gm)).
    Proof.
      split.
      - intros x y.
        use make_is_z_isomorphism.
        + exact (comp_fmonoidal_tensor_inv x y).
        + exact (comp_fmonoidal_tensor_inv_laws x y).
      - use make_is_z_isomorphism.
        + exact comp_fmnoidal_unit_inv.
        + exact comp_fmonoidal_unit_inv_laws.
    Defined.

    Definition comp_fmonoidal
      : fmonoidal M O (F ∙ G)
      := comp_fmonoidal_lax Fm Gm ,, comp_fmonoidal_stronglaws.
  End CompStrongMonoidal.

  Proposition is_symmetric_monoidal_comp
              {C D E : category}
              {M : monoidal C}
              {N : monoidal D}
              {O : monoidal E}
              {HM : symmetric M}
              {HN : symmetric N}
              {HO : symmetric O}
              {F : C ⟶ D}
              {G : D ⟶ E}
              {HF : fmonoidal_lax M N F}
              {HG : fmonoidal_lax N O G}
              (HHF : is_symmetric_monoidal_functor HM HN HF)
              (HHG : is_symmetric_monoidal_functor HN HO HG)
    : is_symmetric_monoidal_functor HM HO (comp_fmonoidal_lax HF HG).
  Proof.
    intros x y.
    cbn.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply HHG.
    }
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite <- functor_comp.
      apply maponpaths.
      apply HHF.
    }
    rewrite functor_comp.
    apply idpath.
  Qed.
End MonoidalFunctors.

(**
 7. Monoidal natural transformations
 *)
Section MonoidalNaturalTransformations.

  Context {C D : category}
          {M : monoidal C} {N : monoidal D}
          {F G : functor C D}
          (Fm : fmonoidal_lax M N F) (Gm : fmonoidal_lax M N G)
          (α : F ⟹ G).

  Definition is_mon_nat_trans_tensorlaw
    : UU
    := ∏ (a a' : C),
       fmonoidal_preservestensordata Fm a a' · α (a ⊗_{M} a')
       =
       α a ⊗^{N} α a' · fmonoidal_preservestensordata Gm a a'.

  Definition is_mon_nat_trans_unitlaw : UU
    := fmonoidal_preservesunit Fm · α I_{M} = fmonoidal_preservesunit Gm.

  Definition is_mon_nat_trans : UU := is_mon_nat_trans_tensorlaw × is_mon_nat_trans_unitlaw.

  Lemma isaprop_is_mon_nat_trans : isaprop is_mon_nat_trans.
  Proof.
    apply isapropdirprod.
    - apply impred; intro a; apply impred; intro a'.
      apply D.
    - apply D.
  Qed.

End MonoidalNaturalTransformations.

Section SomeMonoidalNaturalTransformations.

  Lemma is_mon_nat_trans_identity {C D : category}
    {M : monoidal C} {N : monoidal D}
    {F : functor C D}
    (Fm : fmonoidal_lax M N F) :
    is_mon_nat_trans Fm Fm (nat_trans_id _).
  Proof.
    split; red; cbn; unfold fmonoidal_preservestensordata, fmonoidal_preservesunit; intros.
    - etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, bifunctor_distributes_over_id.
           - cbn in *.
             apply (bifunctor_leftid N).
           - cbn in *.
             apply (bifunctor_rightid N).
      }
      rewrite id_left.
      apply id_right.
    - apply id_right.
  Qed.

  Lemma is_mon_nat_trans_comp {C D : category}
    {M : monoidal C} {N : monoidal D}
    {F G H : functor C D}
    (Fm : fmonoidal_lax M N F)
    (Gm : fmonoidal_lax M N G)
    (Hm : fmonoidal_lax M N H)
    (α : F ⟹ G) (β : G ⟹ H)
    :
    is_mon_nat_trans Fm Gm α -> is_mon_nat_trans Gm Hm β ->
    is_mon_nat_trans Fm Hm (nat_trans_comp _ _ _ α β).
  Proof.
    intros Hα Hβ.
    split; red; cbn; unfold fmonoidal_preservestensordata, fmonoidal_preservesunit; intros.
    - etrans.
      2: { apply cancel_postcomposition.
           apply pathsinv0, bifunctor_distributes_over_comp.
           - cbn in *.
             apply (bifunctor_leftcomp N).
           - cbn in *.
             apply (bifunctor_rightcomp N).
           - cbn in *.
             apply (bifunctor_equalwhiskers N).
      }
      rewrite assoc.
      etrans.
      { apply cancel_postcomposition.
        apply (pr1 Hα a a'). }
      repeat rewrite assoc'.
      apply maponpaths.
      apply (pr1 Hβ).
    - rewrite assoc.
      etrans.
      { apply cancel_postcomposition.
        apply (pr2 Hα). }
      apply (pr2 Hβ).
  Qed.

End SomeMonoidalNaturalTransformations.

Proposition is_mon_nat_trans_prewhisker
            {C₁ C₂ C₃ : category}
            {M₁ : monoidal C₁}
            {M₂ : monoidal C₂}
            {M₃ : monoidal C₃}
            {F : C₁ ⟶ C₂}
            (HF : fmonoidal_lax M₁ M₂ F)
            {G₁ G₂ : C₂ ⟶ C₃}
            {HG₁ : fmonoidal_lax M₂ M₃ G₁}
            {HG₂ : fmonoidal_lax M₂ M₃ G₂}
            {τ : G₁ ⟹ G₂}
            (Hτ : is_mon_nat_trans HG₁ HG₂ τ)
  : is_mon_nat_trans
      (comp_fmonoidal_lax HF HG₁)
      (comp_fmonoidal_lax HF HG₂)
      (pre_whisker F τ).
Proof.
  split.
  - intros x y ; cbn.
    unfold fmonoidal_preservestensordata.
    assert (aux := pr1 Hτ (F x) (F y)).
    unfold fmonoidal_preservestensordata in aux.
    etrans.
    2: { rewrite assoc.
         apply cancel_postcomposition.
         exact aux. }
    clear aux.
    repeat rewrite assoc'.
    apply maponpaths.
    apply nat_trans_ax.
  - unfold is_mon_nat_trans_unitlaw ; cbn.
    unfold fmonoidal_preservesunit.
    assert (aux := pr2 Hτ).
    red in aux.
    unfold fmonoidal_preservesunit in aux.
    rewrite <- aux.
    repeat rewrite assoc'.
    apply maponpaths.
    apply nat_trans_ax.
Qed.

Proposition is_mon_nat_trans_postwhisker
            {C₁ C₂ C₃ : category}
            {M₁ : monoidal C₁}
            {M₂ : monoidal C₂}
            {M₃ : monoidal C₃}
            {F₁ F₂ : C₁ ⟶ C₂}
            {HF₁ : fmonoidal_lax M₁ M₂ F₁}
            {HF₂ : fmonoidal_lax M₁ M₂ F₂}
            {τ : F₁ ⟹ F₂}
            (Hτ : is_mon_nat_trans HF₁ HF₂ τ)
            {G : C₂ ⟶ C₃}
            (HG : fmonoidal_lax M₂ M₃ G)
  : is_mon_nat_trans
      (comp_fmonoidal_lax HF₁ HG)
      (comp_fmonoidal_lax HF₂ HG)
      (post_whisker τ G).
Proof.
  split.
  - intros x y ; cbn.
    unfold fmonoidal_preservestensordata.
    etrans.
      { rewrite assoc'.
        apply maponpaths.
        apply pathsinv0, functor_comp. }
      etrans.
      { do 2 apply maponpaths.
        apply (pr1 Hτ).
      }
      unfold fmonoidal_preservestensordata.
      rewrite functor_comp.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply pathsinv0, preservestensor_is_nattrans_full.
      + apply (fmonoidal_preservestensornatleft HG).
      + apply (fmonoidal_preservestensornatright HG).
  - unfold is_mon_nat_trans_unitlaw ; cbn.
    unfold fmonoidal_preservesunit.
    rewrite assoc'.
    apply maponpaths.
    etrans.
    { apply pathsinv0, functor_comp. }
    apply maponpaths.
    apply (pr2 Hτ).
Qed.

(**
 8. Inverses of monoidal natural transformations
 *)
Section InverseMonoidalNaturalTransformation.
  Context {C D : category}
          {M : monoidal C} {N : monoidal D}
          {F G : functor C D}
          (Fm : fmonoidal_lax M N F) (Gm : fmonoidal_lax M N G)
          (α : F ⟹ G).

  Lemma is_mon_nat_trans_pointwise_inverse
        (isnziα : is_nat_z_iso α)
    : is_mon_nat_trans Fm Gm α
      ->
      is_mon_nat_trans Gm Fm (nat_z_iso_inv (α,,isnziα)).
  Proof.
    intro ismnt. split.
    - intros x y.
      cbn.
      unfold fmonoidal_preservestensordata.
      set (aux := (_,, is_z_iso_bifunctor_z_iso N _ _ (isnziα x) (isnziα y)) : z_iso _ _).
      apply pathsinv0, (z_iso_inv_on_right _ _ _ aux).
      rewrite assoc.
      apply (z_iso_inv_on_left _ _ _ _ (_,,isnziα (x ⊗_{ M} y))).
      cbn.
      apply (!(pr1 ismnt x y)).
    - cbn.
      apply pathsinv0, (z_iso_inv_on_left _ _ _ _ (_,,isnziα I_{M})).
      apply (!(pr2 ismnt)).
  Qed.
End InverseMonoidalNaturalTransformation.

Local Open Scope moncat.

(**
 9. Bundled versions
 *)
Definition lax_monoidal_functor
           (V₁ V₂ : monoidal_cat)
  : UU
  := ∑ (F : V₁ ⟶ V₂), fmonoidal_lax V₁ V₂ F.

#[reversible=no] Coercion lax_monoidal_functor_to_functor
         {V₁ V₂ : monoidal_cat}
         (F : lax_monoidal_functor V₁ V₂)
  : V₁ ⟶ V₂
  := pr1 F.

#[reversible=no] Coercion lax_monoidal_functor_to_fmonoidal_lax
         {V₁ V₂ : monoidal_cat}
         (F : lax_monoidal_functor V₁ V₂)
  : fmonoidal_lax V₁ V₂ F
  := pr2 F.

Definition symmetric_lax_monoidal_functor
           (V₁ V₂ : sym_monoidal_cat)
  : UU
  := ∑ (F : lax_monoidal_functor V₁ V₂),
     is_symmetric_monoidal_functor (pr2 V₁) (pr2 V₂) (pr2 F).

#[reversible=no] Coercion symmetric_lax_monoidal_functor_to_lax_monoidal
         {V₁ V₂ : sym_monoidal_cat}
         (F : symmetric_lax_monoidal_functor V₁ V₂)
  : lax_monoidal_functor V₁ V₂
  := pr1 F.

Definition strong_monoidal_functor
           (V₁ V₂ : monoidal_cat)
  : UU
  := ∑ (F : V₁ ⟶ V₂), fmonoidal V₁ V₂ F.

#[reversible=no] Coercion strong_monoidal_functor_to_lax_monoidal_functor
         {V₁ V₂ : monoidal_cat}
         (F : strong_monoidal_functor V₁ V₂)
  : lax_monoidal_functor V₁ V₂
  := pr1 F ,, pr12 F.

Definition symmetric_strong_monoidal_functor
           (V₁ V₂ : sym_monoidal_cat)
  : UU
  := ∑ (F : strong_monoidal_functor V₁ V₂),
     is_symmetric_monoidal_functor (pr2 V₁) (pr2 V₂) (pr2 F).

#[reversible=no] Coercion symmetric_strong_monoidal_functor_to_strong_monoidal
         {V₁ V₂ : sym_monoidal_cat}
         (F : symmetric_strong_monoidal_functor V₁ V₂)
  : strong_monoidal_functor V₁ V₂
  := pr1 F.

#[reversible=no] Coercion symmetric_strong_monoidal_functor_to_lax_symmetric
         {V₁ V₂ : sym_monoidal_cat}
         (F : symmetric_strong_monoidal_functor V₁ V₂)
  : symmetric_lax_monoidal_functor V₁ V₂
  := (pr11 F ,, pr121 F) ,, pr2 F.

Definition mon_functor_unit
           {V₁ V₂ : monoidal_cat}
           (F : lax_monoidal_functor V₁ V₂)
  : I_{V₂} --> F (I_{V₁})
  := pr212 F.

Definition mon_functor_tensor
           {V₁ V₂ : monoidal_cat}
           (F : lax_monoidal_functor V₁ V₂)
           (x y : V₁)
  : F x ⊗ F y --> F(x ⊗ y)
  := pr112 F x y.

Section MonoidalFunctorAccessors.
  Context {V₁ V₂ : monoidal_cat}
          (F : lax_monoidal_functor V₁ V₂).

  Definition tensor_mon_functor_tensor
             {x₁ x₂ y₁ y₂ : V₁}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : #F f #⊗ #F g · mon_functor_tensor F x₂ y₂
      =
      mon_functor_tensor F x₁ y₁ · #F (f #⊗ g).
  Proof.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      apply (fmonoidal_preservestensornatleft (pr2 F)).
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply (fmonoidal_preservestensornatright (pr2 F)).
    }
    rewrite !assoc'.
    apply maponpaths.
    rewrite <- functor_comp.
    apply idpath.
  Qed.

  Definition mon_functor_lassociator
             (x y z : V₁)
    : mon_functor_tensor F x y #⊗ identity (F z)
      · mon_functor_tensor F (x ⊗ y) z
      · #F (mon_lassociator x y z)
      =
      mon_lassociator (F x) (F y) (F z)
      · identity (F x) #⊗ mon_functor_tensor F y z
      · mon_functor_tensor F x (y ⊗ z).
  Proof.
    refine (_ @ fmonoidal_preservesassociativity (pr2 F) x y z @ _).
    - apply maponpaths_2.
      apply maponpaths_2.
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      refine (_ @ id_right _).
      apply maponpaths.
      apply (bifunctor_leftid V₂).
    - apply maponpaths_2.
      apply maponpaths.
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      refine (!(id_left _) @ _).
      apply maponpaths_2.
      refine (!_).
      apply (bifunctor_rightid V₂).
  Qed.

  Definition mon_functor_rassociator
             (x y z : V₁)
    : mon_rassociator (F x) (F y) (F z)
      · mon_functor_tensor F x y #⊗ identity (F z)
      · mon_functor_tensor F (x ⊗ y) z
      =
      identity (F x) #⊗ mon_functor_tensor F y z
      · mon_functor_tensor F x (y ⊗ z)
      · #F (mon_rassociator x y z).
  Proof.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (!(id_left _) @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply mon_rassociator_lassociator.
      }
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      refine (!_).
      apply mon_functor_lassociator.
    }
    rewrite !assoc'.
    do 2 apply maponpaths.
    refine (_ @ id_right _).
    apply maponpaths.
    refine (!(functor_comp _ _ _) @ _ @ functor_id _ _).
    apply maponpaths.
    apply mon_lassociator_rassociator.
  Qed.

  Definition mon_functor_lunitor
             (x : V₁)
    : mon_lunitor (F x)
      =
      mon_functor_unit F #⊗ identity (F x)
      · mon_functor_tensor F (I_{V₁}) x
      · #F (mon_lunitor x).
  Proof.
    refine (!(fmonoidal_preservesleftunitality (pr2 F) x) @ _).
    do 2 apply maponpaths_2.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    refine (!(id_right _) @ _).
    apply maponpaths.
    refine (!_).
    apply (bifunctor_leftid V₂).
  Qed.

  Definition mon_functor_linvunitor
             (x : V₁)
    : #F (mon_linvunitor x)
      =
      mon_linvunitor (F x)
      · mon_functor_unit F #⊗ identity (F x)
      · mon_functor_tensor F (I_{V₁}) x.
  Proof.
    refine (!(id_left _) @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply mon_linvunitor_lunitor.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply mon_functor_lunitor.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ id_right _).
    apply maponpaths.
    refine (!(functor_comp _ _ _) @ _ @ functor_id _ _).
    apply maponpaths.
    apply mon_lunitor_linvunitor.
  Qed.

  Definition mon_functor_runitor
             (x : V₁)
    : mon_runitor (F x)
      =
      identity (F x) #⊗ mon_functor_unit F
      · mon_functor_tensor F x (I_{V₁})
      · #F (mon_runitor x).
  Proof.
    refine (!(fmonoidal_preservesrightunitality (pr2 F) x) @ _).
    do 2 apply maponpaths_2.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    refine (!(id_left _) @ _).
    apply maponpaths_2.
    refine (!_).
    apply (bifunctor_rightid V₂).
  Qed.

  Definition mon_functor_rinvunitor
             (x : V₁)
    : #F (mon_rinvunitor x)
      =
      mon_rinvunitor (F x)
      · identity (F x) #⊗ mon_functor_unit F
      · mon_functor_tensor F x (I_{V₁}).
  Proof.
    refine (!(id_left _) @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply mon_rinvunitor_runitor.
    }
    rewrite !assoc'.
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply mon_functor_runitor.
    }
    rewrite !assoc'.
    apply maponpaths.
    refine (_ @ id_right _).
    apply maponpaths.
    refine (!(functor_comp _ _ _) @ _ @ functor_id _ _).
    apply maponpaths.
    apply mon_runitor_rinvunitor.
  Qed.
End MonoidalFunctorAccessors.

Section StrongMonoidalFunctorAccessors.
  Context {V₁ V₂ : monoidal_cat}
          (F : strong_monoidal_functor V₁ V₂).

  Definition strong_functor_unit_inv
    : F (I_{V₁}) --> I_{V₂}.
  Proof.
    exact (inv_from_z_iso (_ ,, fmonoidal_preservesunitstrongly (pr2 F))).
  Defined.

  Definition strong_functor_unit_inv_unit
    : strong_functor_unit_inv · mon_functor_unit F = identity _.
  Proof.
    apply z_iso_after_z_iso_inv.
  Qed.

  Definition strong_functor_unit_unit_inv
    : mon_functor_unit F · strong_functor_unit_inv = identity _.
  Proof.
    apply (z_iso_inv_after_z_iso (_ ,, fmonoidal_preservesunitstrongly (pr2 F))).
  Qed.

  Definition strong_functor_tensor_inv
             (x y : V₁)
    : F(x ⊗ y) --> F x ⊗ F y.
  Proof.
    exact (inv_from_z_iso (_ ,, fmonoidal_preservestensorstrongly (pr2 F) x y)).
  Defined.

  Definition strong_functor_tensor_inv_tensor
             (x y : V₁)
    : strong_functor_tensor_inv x y · mon_functor_tensor F x y = identity _.
  Proof.
    apply z_iso_after_z_iso_inv.
  Qed.

  Definition strong_functor_tensor_tensor_inv
             (x y : V₁)
    : mon_functor_tensor F x y · strong_functor_tensor_inv x y = identity _.
  Proof.
    apply (z_iso_inv_after_z_iso (_ ,, fmonoidal_preservestensorstrongly (pr2 F) x y)).
  Qed.

  Definition tensor_strong_functor_tensor_inv
             {x₁ x₂ y₁ y₂ : V₁}
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : strong_functor_tensor_inv x₁ y₁ · #F f #⊗ #F g
      =
      #F (f #⊗ g) · strong_functor_tensor_inv x₂ y₂.
  Proof.
    use z_iso_inv_on_right ; cbn.
    rewrite !assoc.
    use z_iso_inv_on_left ; cbn.
    refine (!_).
    apply (tensor_mon_functor_tensor F).
  Qed.
End StrongMonoidalFunctorAccessors.

Proposition symmetric_lax_monoidal_sym_mon_braiding
            {V₁ V₂ : sym_monoidal_cat}
            (F : symmetric_lax_monoidal_functor V₁ V₂)
            (x y : V₁)
  : sym_mon_braiding V₂ (F x) (F y) · mon_functor_tensor F y x
    =
    mon_functor_tensor F x y · #F (sym_mon_braiding V₁ x y).
Proof.
  exact (pr2 F x y).
Qed.

(**
 10. Builders for the bundled versions
 *)
Definition lax_monoidal_functor_laws
           {V₁ V₂ : monoidal_cat}
           (F : V₁ ⟶ V₂)
           (μ : ∏ (x y : V₁), F x ⊗ F y --> F(x ⊗ y))
           (η : I_{V₂} --> F(I_{V₁}))
  : UU
  := (∏ (x₁ x₂ y₁ y₂ : V₁)
        (f : x₁ --> x₂)
        (g : y₁ --> y₂),
      #F f #⊗ #F g · μ x₂ y₂
      =
      μ x₁ y₁ · #F(f #⊗ g))
     ×
     (∏ (x : V₁),
      η #⊗ identity _ · μ (I_{V₁}) x · #F (mon_lunitor x)
      =
      mon_lunitor (F x))
     ×
     (∏ (x : V₁),
      identity _ #⊗ η · μ x (I_{V₁}) · #F (mon_runitor x)
      =
      mon_runitor (F x))
     ×
     (∏ (x y z : V₁),
      (μ x y #⊗ identity _) · μ (x ⊗ y) z · #F(mon_lassociator x y z)
      =
      mon_lassociator (F x) (F y) (F z) · (identity _ #⊗ μ y z) · μ x (y ⊗ z)).

Proposition lax_monoidal_functor_laws_to_monoidal_laws
            {V₁ V₂ : monoidal_cat}
            {F : V₁ ⟶ V₂}
            {μ : ∏ (x y : V₁), F x ⊗ F y --> F(x ⊗ y)}
            {η : I_{V₂} --> F(I_{V₁})}
            (HF : lax_monoidal_functor_laws F μ η)
  : fmonoidal_laxlaws (μ,, η).
Proof.
  repeat split.
  - intros x y₁ y₂ g ; cbn.
    refine (_ @ pr1 HF _ _ _ _ (identity _) g @ _).
    + apply maponpaths_2.
      unfold monoidal_cat_tensor_mor, functoronmorphisms1.
      refine (!(id_left _) @ _).
      apply maponpaths_2.
      rewrite functor_id.
      refine (!_).
      apply (bifunctor_rightid (pr2 V₂)).
    + do 2 apply maponpaths.
      unfold monoidal_cat_tensor_mor, functoronmorphisms1.
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply (bifunctor_rightid (pr2 V₁)).
  - intros x₁ x₂ y f ; cbn.
    refine (_ @ pr1 HF _ _ _ _ f (identity _) @ _).
    + apply maponpaths_2.
      unfold monoidal_cat_tensor_mor, functoronmorphisms1.
      refine (!(id_right _) @ _).
      apply maponpaths.
      rewrite functor_id.
      refine (!_).
      apply (bifunctor_leftid (pr2 V₂)).
    + do 2 apply maponpaths.
      unfold monoidal_cat_tensor_mor, functoronmorphisms1.
      refine (_ @ id_right _).
      apply maponpaths.
      apply (bifunctor_leftid (pr2 V₁)).
  - intros x y z ; cbn.
    refine (_ @ pr222 HF x y z @ _).
    + do 2 apply maponpaths_2.
      unfold monoidal_cat_tensor_mor, functoronmorphisms1.
      refine (!(id_right _) @ _).
      apply maponpaths.
      refine (!_).
      apply (bifunctor_leftid (pr2 V₂)).
    + apply maponpaths_2.
      apply maponpaths.
      unfold monoidal_cat_tensor_mor, functoronmorphisms1.
      refine (_ @ id_left _).
      apply maponpaths_2.
      apply (bifunctor_rightid (pr2 V₂)).
  - intros x ; cbn.
    refine (_ @ pr12 HF x).
    do 2 apply maponpaths_2.
    unfold monoidal_cat_tensor_mor, functoronmorphisms1.
    refine (!(id_right _) @ _).
    apply maponpaths.
    refine (!_).
    apply (bifunctor_leftid (pr2 V₂)).
  - intros x ; cbn.
    refine (_ @ pr122 HF x).
    do 2 apply maponpaths_2.
    unfold monoidal_cat_tensor_mor, functoronmorphisms1.
    refine (!(id_left _) @ _).
    apply maponpaths_2.
    refine (!_).
    apply (bifunctor_rightid (pr2 V₂)).
Qed.

Definition make_lax_monoidal_functor
           {V₁ V₂ : monoidal_cat}
           (F : V₁ ⟶ V₂)
           (μ : ∏ (x y : V₁), F x ⊗ F y --> F(x ⊗ y))
           (η : I_{V₂} --> F(I_{V₁}))
           (HF : lax_monoidal_functor_laws F μ η)
  : lax_monoidal_functor V₁ V₂
  := F ,, (μ ,, η) ,, lax_monoidal_functor_laws_to_monoidal_laws HF.

Definition make_strong_monoidal_functor
           {V₁ V₂ : monoidal_cat}
           (F : lax_monoidal_functor V₁ V₂)
           (Hμ : ∏ (x y : V₁), is_z_isomorphism (mon_functor_tensor F x y))
           (Hη : is_z_isomorphism (mon_functor_unit F))
  : strong_monoidal_functor V₁ V₂
  := pr1 F ,, pr2 F ,, Hμ ,, Hη.

Definition symmetric_monoidal_functor_laws
           {V₁ V₂ : sym_monoidal_cat}
           (F : lax_monoidal_functor V₁ V₂)
  : UU
  := ∏ (x y : V₁),
     sym_mon_braiding V₂ (F x) (F y) · mon_functor_tensor F y x
     =
     mon_functor_tensor F x y · #F(sym_mon_braiding V₁ x y).

Definition make_symmetric_lax_monoidal_functor
           {V₁ V₂ : sym_monoidal_cat}
           (F : lax_monoidal_functor V₁ V₂)
           (HF : symmetric_monoidal_functor_laws F)
  : symmetric_lax_monoidal_functor V₁ V₂
  := F ,, HF.

Definition make_symmetric_strong_monoidal_functor
           {V₁ V₂ : sym_monoidal_cat}
           (F : strong_monoidal_functor V₁ V₂)
           (HF : symmetric_monoidal_functor_laws F)
  : symmetric_strong_monoidal_functor V₁ V₂
  := F ,, HF.
