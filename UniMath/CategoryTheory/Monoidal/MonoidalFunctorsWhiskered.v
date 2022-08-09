Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.


Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section local_helper_lemmas.
  Lemma iso_stable_under_equality {C : category} {x y : C} {f g : C⟦x,y⟧} : (g = f) → is_z_isomorphism f → is_z_isomorphism g.
  Proof.
    intros pe pi.
    induction pe.
    exact pi.
  Qed.

  Lemma iso_stable_under_transportf {C : category} {x y z : C} {f : C⟦x,y⟧} {pf : y=z} : is_z_isomorphism f → is_z_isomorphism (transportf _ pf f).
  Proof.
    intro pfi.
    induction pf.
    use pfi.
  Qed.

  Lemma iso_stable_under_equalitytransportf {C : category} {x y z : C} {f : C⟦x,y⟧} {g : C⟦x,z⟧} {pf : y=z} :
    g = transportf _ pf f -> is_z_isomorphism f -> is_z_isomorphism g.
  Proof.
    intros p isof.
    use (iso_stable_under_equality p).
    use (iso_stable_under_transportf).
    exact isof.
  Qed.
End local_helper_lemmas.


Section MonoidalFunctors.

  (** (Weak) Monoidal functors **)
  (* Monoidal functor data *)

  Definition preserves_tensordata {C D : category} (M : monoidal C) (N : monoidal D) (F : functor C D) : UU :=
    ∏ (x y : C), D ⟦ F x ⊗_{ N} F y, F (x ⊗_{ M} y) ⟧.

  Definition preserves_unit {C D : category} (M : monoidal C) (N : monoidal D) (F : functor C D) : UU
    := D ⟦ I_{N} , F I_{M} ⟧.

  Definition fmonoidal_data {C D : category} (M : monoidal C) (N : monoidal D) (F : functor C D) :=
    preserves_tensordata M N F × preserves_unit M N F.

  Definition fmonoidal_preservestensordata {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
    (fmd : fmonoidal_data M N F) : (preserves_tensordata M N F) := pr1 fmd.

  Definition fmonoidal_preservesunit {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
    (fmd : fmonoidal_data M N F) : (preserves_unit M N F) := pr2 fmd.

  (** Properties **)
  Definition preserves_tensor_nat_left {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (pt : preserves_tensordata M N F)
    := ∏ (x y1 y2 : C) (g : C⟦y1,y2⟧),
      F x ⊗^{ N}_{l} # F g · pt x y2 = pt x y1 · # F (x ⊗^{ M}_{l} g).

  Definition preserves_tensor_nat_right {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (pt : preserves_tensordata M N F)
    := ∏ (x1 x2 y : C) (f : C⟦x1,x2⟧),
      # F f ⊗^{ N}_{r} F y · pt x2 y = pt x1 y · # F (f ⊗^{ M}_{r} y).

  Definition preserves_leftunitality {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
    (pt : preserves_tensordata M N F) (pu : preserves_unit M N F)
    := ∏ (x : C), (pu ⊗^{ N}_{r} F x) · (pt I_{ M} x) · (# F lu^{ M }_{ x}) = lu^{ N }_{ F x}.

  Definition preserves_leftunitalityinv {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
    (pt : preserves_tensordata M N F) (pu : preserves_unit M N F)
    := ∏ (x : C), luinv^{ N }_{ F x} · (pu ⊗^{ N}_{r} F x) · (pt I_{ M} x) = # F luinv^{ M }_{ x}.

  Definition preserves_rightunitality {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
    (pt : preserves_tensordata M N F) (pu : preserves_unit M N F)
    := ∏ (x : C), ((F x ⊗^{ N}_{l} pu) · (pt x I_{ M}) · (# F ru^{ M }_{ x}) = ru^{ N }_{ F x}).

  Definition preserves_rightunitalityinv {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
    (pt : preserves_tensordata M N F) (pu : preserves_unit M N F)
    := ∏ (x : C), ruinv^{ N }_{ F x} · F x ⊗^{ N}_{l} pu · pt x I_{ M} = # F ruinv^{ M }_{ x}.

  Definition preserves_associativity {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (pt : preserves_tensordata M N F) : UU :=
    ∏ (x y z : C), ((pt x y) ⊗^{N}_{r} (F z)) · (pt (x ⊗_{M} y) z) · (#F (α^{M}_{x,y,z}))
                   = α^{N}_{F x, F y, F z} · ((F x) ⊗^{N}_{l} (pt y z)) · (pt x (y ⊗_{M} z)).

  Definition preserves_associativityinv {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (pt : preserves_tensordata M N F) : UU :=
    ∏ (x y z : C), αinv^{N}_{F x, F y, F z} · ((pt x y) ⊗^{N}_{r} (F z)) · (pt (x ⊗_{M} y) z)
                   = ((F x) ⊗^{N}_{l} (pt y z)) · (pt x (y ⊗_{M} z)) · (#F (αinv^{M}_{x,y,z})).

  Definition fmonoidal_laxlaws {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fmd : fmonoidal_data M N F) : UU :=
    (preserves_tensor_nat_left (fmonoidal_preservestensordata fmd)) ×
      (preserves_tensor_nat_right (fmonoidal_preservestensordata fmd)) ×
      (preserves_associativity (fmonoidal_preservestensordata fmd)) ×
      (preserves_leftunitality (fmonoidal_preservestensordata fmd) (fmonoidal_preservesunit fmd)) ×
      (preserves_rightunitality (fmonoidal_preservestensordata fmd) (fmonoidal_preservesunit fmd)).

  Definition fmonoidal_lax {C D : category} (M : monoidal C) (N : monoidal D) (F : functor C D)  : UU :=
    ∑ (fmd : fmonoidal_data M N F), fmonoidal_laxlaws fmd.

  Definition fmonoidal_fdata {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : fmonoidal_lax M N F) : fmonoidal_data M N F := pr1 fm.
  Coercion fmonoidal_fdata : fmonoidal_lax >-> fmonoidal_data.

  Definition fmonoidal_flaws {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : fmonoidal_lax M N F) : fmonoidal_laxlaws fm := pr2 fm.

  Definition fmonoidal_preservestensornatleft {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : fmonoidal_lax M N F) :
    preserves_tensor_nat_left (fmonoidal_preservestensordata fm) := pr12 fm.
  Definition fmonoidal_preservestensornatright {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : fmonoidal_lax M N F) :
    preserves_tensor_nat_right (fmonoidal_preservestensordata fm) := pr122 fm.
  Definition fmonoidal_preservesassociativity {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : fmonoidal_lax M N F) :
    preserves_associativity (fmonoidal_preservestensordata fm) := pr1 (pr222 fm).

  Lemma fmonoidal_preservesassociativityinv {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : fmonoidal_lax M N F) :
    preserves_associativityinv (fmonoidal_preservestensordata fm).
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

  Definition fmonoidal_preservesleftunitality {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : fmonoidal_lax M N F) :
    preserves_leftunitality (fmonoidal_preservestensordata fm) (fmonoidal_preservesunit fm) := pr12 (pr222 fm).

  Lemma fmonoidal_preservesleftunitalityinv {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : fmonoidal_lax M N F) :
    preserves_leftunitalityinv (fmonoidal_preservestensordata fm) (fmonoidal_preservesunit fm).
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

  Definition fmonoidal_preservesrightunitality {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : fmonoidal_lax M N F) :
    preserves_rightunitality (fmonoidal_preservestensordata fm) (fmonoidal_preservesunit fm) := pr22 (pr222 fm).

  Lemma fmonoidal_preservesrightunitalityinv {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : fmonoidal_lax M N F) :
    preserves_rightunitalityinv (fmonoidal_preservestensordata fm) (fmonoidal_preservesunit fm).
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

  Definition preserves_tensor_strongly {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (pt : preserves_tensordata M N F) : UU
    := ∏ (x y : C), is_z_isomorphism (pt x y).

  Definition preserves_unit_strongly {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (pu : preserves_unit M N F) : UU
    := is_z_isomorphism pu.

  Definition fmonoidal_stronglaws {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
    (pt : preserves_tensordata M N F) (pu : preserves_unit M N F) : UU
    := preserves_tensor_strongly pt × preserves_unit_strongly pu.

  Definition fmonoidal {C D : category} (M : monoidal C) (N : monoidal D) (F : functor C D)  : UU :=
    ∑ (Fm : fmonoidal_lax M N F),
      fmonoidal_stronglaws (fmonoidal_preservestensordata Fm) (fmonoidal_preservesunit Fm).

  Definition fmonoidal_fmonoidallax {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (Fm : fmonoidal M N F) :
    fmonoidal_lax M N F := pr1 Fm.
  Coercion fmonoidal_fmonoidallax : fmonoidal >-> fmonoidal_lax.

  Definition fmonoidal_preservestensorstrongly {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (Fm : fmonoidal M N F) :
    preserves_tensor_strongly (fmonoidal_preservestensordata Fm) := pr12 Fm.

  Definition fmonoidal_preservesunitstrongly {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (Fm : fmonoidal M N F) :
    preserves_unit_strongly (fmonoidal_preservesunit Fm) := pr22 Fm.


  (** We now show that everything behaves as expected **)
  Definition functor_imageoftensor {C D : category} (M : monoidal C) (F : functor C D) : bifunctor C C D
    := compose_bifunctor_with_functor M F.

  Definition functor_tensorofimages {C D : category} (F : functor C D) (N : monoidal D) : bifunctor C C D
    := compose_functor_with_bifunctor F F N.

  Definition preserves_tensor_is_nattrans_type {C D : category} (M : monoidal C) (N : monoidal D) (F : functor C D) : UU
    := binat_trans (functor_tensorofimages F N) (functor_imageoftensor M F).

  (* I really don't know how to call the following lemma *)
  Definition preservestensor_is_nattrans {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} {pt : preserves_tensordata M N F}
    (ptnl : preserves_tensor_nat_left pt) (ptnr : preserves_tensor_nat_right pt) : preserves_tensor_is_nattrans_type M N F.
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

  Lemma preservestensor_is_nattrans_full {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} {pt : preserves_tensordata M N F}
    (ptnl : preserves_tensor_nat_left pt) (ptnr : preserves_tensor_nat_right pt) :
 ∏ (x1 x2 y1 y2 : C) (f : C⟦x1,x2⟧) (g : C⟦y1,y2⟧),
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

  Definition preserves_tensor_inv_is_nattrans_type {C D : category} (M : monoidal C) (N : monoidal D) (F : functor C D) : UU
    := binat_trans (functor_imageoftensor M F) (functor_tensorofimages F N).

  (* name follows [preservestensor_is_nattrans], for lack of a better proposition *)
  Definition preservestensor_inv_is_nattrans {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
             {pt : preserves_tensordata M N F}
             (ptnl : preserves_tensor_nat_left pt)
             (ptnr : preserves_tensor_nat_right pt)
             (ptstr: preserves_tensor_strongly pt)
    : preserves_tensor_inv_is_nattrans_type M N F
    := inv_binattrans_from_binatiso(α:=preservestensor_is_nattrans ptnl ptnr) ptstr.


  Definition preserves_leftunitality' {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
    {pt : preserves_tensordata M N F} {pu : preserves_unit M N F} (plu : preserves_leftunitality pt pu) :
    ∏ (x : C), (pu ⊗^{N} (identity (F x))) · (pt I_{M} x) · (#F (lu^{M}_{x})) = lu^{N}_{F x}.
  Proof.
    intro x.
    unfold functoronmorphisms1.
    rewrite bifunctor_leftid.
    rewrite id_right.
    apply plu.
  Qed.

  Definition preserves_rightunitality' {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
    {pt : preserves_tensordata M N F} {pu : preserves_unit M N F} (pru : preserves_rightunitality pt pu) :
    ∏ (x : C), ((identity (F x)) ⊗^{N} pu) · (pt x I_{M}) · (#F (ru^{M}_{x})) = ru^{N}_{F x}.
  Proof.
    intro x.
    unfold functoronmorphisms1.
    rewrite bifunctor_rightid.
    rewrite id_left.
    apply pru.
  Qed.



  (* Strictly preserving monoidal functors *)
  Definition preserves_tensor_strictly {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (pt : preserves_tensordata M N F) : UU
    := ∏ (x y : C), ∑ (pf : (F x) ⊗_{N} (F y) = F (x ⊗_{M} y)), pt x y = transportf _ pf (identity ((F x) ⊗_{N} (F y))).

  Lemma strictlytensorpreserving_is_strong {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} {pt : preserves_tensordata M N F}
    (pst : preserves_tensor_strictly pt) : preserves_tensor_strongly pt.
  Proof.
    intros x y.
    use (iso_stable_under_equalitytransportf (pr2 (pst x y)) (is_z_isomorphism_identity (F x ⊗_{N} F y))).
  Qed.



  Definition preserves_unit_strictly {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (pu : preserves_unit M N F) : UU
    := ∑ (pf : I_{N} = (F I_{M})), pu = transportf _ pf (identity I_{N}).

  Definition strictlyunitpreserving_is_strong {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} {pu : preserves_unit M N F}
    (pus : preserves_unit_strictly pu) : preserves_unit_strongly pu.
  Proof.
    use (iso_stable_under_equalitytransportf (pr2 pus) (is_z_isomorphism_identity I_{N})).
  Defined.

(** towards a bicategory of monoidal categories *)
  Definition identity_fmonoidal_data {C : category} (M : monoidal C) :
    fmonoidal_data M M (functor_identity C).
  Proof.
    split.
    - intros x y. apply identity.
    - apply identity.
  Defined.

  Lemma identity_fmonoidal_laxlaws {C : category} (M : monoidal C) :
    fmonoidal_laxlaws (identity_fmonoidal_data M).
  Proof.
    repeat split; red; unfold fmonoidal_preservesunit, fmonoidal_preservestensordata; cbn; intros.
    - rewrite id_left. apply id_right.
    - rewrite id_left. apply id_right.
    - do 2 rewrite id_right.
      rewrite bifunctor_rightid.
      rewrite bifunctor_leftid.
      rewrite id_right.
      apply id_left.
    -  rewrite id_right.
       rewrite bifunctor_rightid.
       apply id_left.
    - rewrite id_right.
       rewrite bifunctor_leftid.
       apply id_left.
  Qed.

  Definition identity_fmonoidal_lax {C : category} (M : monoidal C) :
    fmonoidal_lax M M (functor_identity C)
    := identity_fmonoidal_data M ,, identity_fmonoidal_laxlaws M.

  Definition identity_fmonoidal_stronglaws {C : category} (M : monoidal C) :
    fmonoidal_stronglaws (fmonoidal_preservestensordata (identity_fmonoidal_lax M))
      (fmonoidal_preservesunit (identity_fmonoidal_lax M)).
  Proof.
    split.
    - intros x y. apply is_z_isomorphism_identity.
    - apply is_z_isomorphism_identity.
  Defined.

  Definition identity_fmonoidal {C : category} (M : monoidal C) : fmonoidal M M (functor_identity C)
    := identity_fmonoidal_lax M ,, identity_fmonoidal_stronglaws M.

  Definition comp_fmonoidal_data {C D E : category} {M : monoidal C} {N : monoidal D} {O : monoidal E}
    {F : C ⟶ D} {G : D ⟶ E} (Fm : fmonoidal_lax M N F) (Gm : fmonoidal_lax N O G) :
    fmonoidal_data M O (F ∙ G).
  Proof.
    split.
    - intros x y.
      exact (fmonoidal_preservestensordata Gm (F x) (F y) · #G (fmonoidal_preservestensordata Fm x y)).
    - exact (fmonoidal_preservesunit Gm · #G (fmonoidal_preservesunit Fm)).
  Defined.

  Lemma comp_fmonoidal_laxlaws {C D E : category} {M : monoidal C} {N : monoidal D} {O : monoidal E}
    {F : C ⟶ D} {G : D ⟶ E} (Fm : fmonoidal_lax M N F) (Gm : fmonoidal_lax N O G) :
    fmonoidal_laxlaws (comp_fmonoidal_data Fm Gm).
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
      rewrite bifunctor_leftcomp.
      rewrite bifunctor_rightcomp.
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
      rewrite bifunctor_rightcomp.
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
      rewrite bifunctor_leftcomp.
      rewrite <- auxF.
      clear auxF.
      do 2 rewrite functor_comp.
      repeat rewrite assoc.
      do 2 apply cancel_postcomposition.
      repeat rewrite assoc'.
      apply maponpaths.
      apply fmonoidal_preservestensornatleft.
  Qed.

  Definition comp_fmonoidal_lax {C D E : category} {M : monoidal C} {N : monoidal D} {O : monoidal E}
    {F : C ⟶ D} {G : D ⟶ E} (Fm : fmonoidal_lax M N F) (Gm : fmonoidal_lax N O G) :
    fmonoidal_lax M O (F ∙ G)
    := comp_fmonoidal_data Fm Gm ,, comp_fmonoidal_laxlaws Fm Gm.

  Definition comp_fmonoidal_stronglaws {C D E : category} {M : monoidal C} {N : monoidal D} {O : monoidal E}
    {F : C ⟶ D} {G : D ⟶ E} (Fm : fmonoidal M N F) (Gm : fmonoidal N O G) :
  fmonoidal_stronglaws (fmonoidal_preservestensordata (comp_fmonoidal_lax Fm Gm))
    (fmonoidal_preservesunit (comp_fmonoidal_lax Fm Gm)).
  Proof.
    split.
    - intros x y.
      use tpair.
      + exact (#G (pr1 (fmonoidal_preservestensorstrongly Fm x y)) · pr1 (fmonoidal_preservestensorstrongly Gm (F x) (F y))).
      + split.
        * cbn.
          etrans.
          { repeat rewrite assoc'.
            apply maponpaths.
            rewrite assoc.
            apply cancel_postcomposition.
            rewrite <- functor_comp.
            apply maponpaths.
            apply (pr12 (fmonoidal_preservestensorstrongly Fm x y)). }
          rewrite functor_id.
          rewrite id_left.
          apply (pr12 (fmonoidal_preservestensorstrongly Gm (F x) (F y))).
        * cbn.
          etrans.
          { repeat rewrite assoc'.
            apply maponpaths.
            rewrite assoc.
            apply cancel_postcomposition.
            apply (pr22 (fmonoidal_preservestensorstrongly Gm (F x) (F y))). }
          rewrite id_left.
          rewrite <- functor_comp.
          etrans.
          { apply maponpaths.
            apply (pr22 (fmonoidal_preservestensorstrongly Fm x y)). }
          apply functor_id.
    - use tpair.
      + exact (#G (pr1 (fmonoidal_preservesunitstrongly Fm)) · pr1 (fmonoidal_preservesunitstrongly Gm)).
      + split.
        * cbn.
          etrans.
          { repeat rewrite assoc'.
            apply maponpaths.
            rewrite assoc.
            apply cancel_postcomposition.
            rewrite <- functor_comp.
            apply maponpaths.
            apply (pr12 (fmonoidal_preservesunitstrongly Fm)). }
          rewrite functor_id.
          rewrite id_left.
          apply (pr12 (fmonoidal_preservesunitstrongly Gm)).
        * cbn.
          etrans.
          { repeat rewrite assoc'.
            apply maponpaths.
            rewrite assoc.
            apply cancel_postcomposition.
            apply (pr22 (fmonoidal_preservesunitstrongly Gm)). }
          rewrite id_left.
          rewrite <- functor_comp.
          etrans.
          { apply maponpaths.
            apply (pr22 (fmonoidal_preservesunitstrongly Fm)). }
          apply functor_id.
  Qed.

  Definition comp_fmonoidal {C D E : category} {M : monoidal C} {N : monoidal D} {O : monoidal E}
    {F : C ⟶ D} {G : D ⟶ E} (Fm : fmonoidal M N F) (Gm : fmonoidal N O G) : fmonoidal M O (F ∙ G)
    := comp_fmonoidal_lax Fm Gm ,, comp_fmonoidal_stronglaws Fm Gm.


End MonoidalFunctors.

Section MonoidalNaturalTransformations.

  Context {C D : category} {M : monoidal C} {N : monoidal D}
    {F G : functor C D} (Fm : fmonoidal_lax M N F) (Gm : fmonoidal_lax M N G)
    (α : F ⟹ G).

  Definition is_mon_nat_trans : UU :=
    (∏ (a a' : C), fmonoidal_preservestensordata Fm a a' · α (a ⊗_{M} a') = α a ⊗^{N} α a' · fmonoidal_preservestensordata Gm a a') × fmonoidal_preservesunit Fm · α I_{M} = fmonoidal_preservesunit Gm.

  Lemma isaprop_is_mon_nat_trans : isaprop is_mon_nat_trans.
  Proof.
    apply isapropdirprod.
    - apply impred; intro a; apply impred; intro a'.
      apply D.
    - apply D.
  Qed.

End MonoidalNaturalTransformations.

Section InverseMonoidalNaturalTransformation.

  Context {C D : category} {M : monoidal C} {N : monoidal D}
    {F G : functor C D} (Fm : fmonoidal_lax M N F) (Gm : fmonoidal_lax M N G)
    (α : F ⟹ G).

  Lemma is_mon_nat_trans_pointwise_inverse (isnziα : is_nat_z_iso α) :
    is_mon_nat_trans Fm Gm α -> is_mon_nat_trans Gm Fm (nat_z_iso_inv (α,,isnziα)).
  Proof.
    intro ismnt. split.
    - intros x y.
      cbn.
      unfold fmonoidal_preservestensordata.
      set (aux := (_,, is_z_iso_bifunctor_z_iso (monoidal_tensor N) _ _ (isnziα x) (isnziα y)) : z_iso _ _).
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
