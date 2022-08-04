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

End MonoidalFunctors.
