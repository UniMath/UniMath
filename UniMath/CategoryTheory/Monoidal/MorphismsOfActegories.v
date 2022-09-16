(** the concept of morphism between actegories that is a functor between the
    categories acted upon that is compatible with the action structures

written by Ralph Matthes in close correspondence with the code in [UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered]

naming is inspired from Actegories for the Working Amthematician by Matteo Capucci and Bruno Gavranović,
available at https://arxiv.org/abs/2203.16351

in particular: the morphisms of V-actegories are called V-linear functors (the lax variant is also singled out), the crucial natural isomorphism asked for is called the lineator

2022
*)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.Actegories.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.
Import ActegoryNotations.

Section LinearFunctors.

  Context {V : category} (Mon_V : monoidal V). (** given the monoidal category that acts upon categories *)

Section TheDefinitions.

  Context {C D : category} (ActC : actegory Mon_V C) (ActD : actegory Mon_V D) (F: functor C D).


  (** (Weak) Linear functors **)
  (* Linear functor data *)

  Definition lineator_data : UU := ∏ (v : V) (x : C), D ⟦ v ⊗_{ActD} F x, F (v ⊗_{ActC} x) ⟧.

  (** Properties **)
  Definition lineator_nat_left (ld : lineator_data)
    := ∏ (v : V) (x1 x2 : C) (g : C⟦x1,x2⟧),
      v ⊗^{ActD}_{l} # F g · ld v x2 = ld v x1 · # F (v ⊗^{ActC}_{l} g).

  Definition lineator_nat_right (ld : lineator_data)
    := ∏ (v1 v2 : V) (x : C) (f : V⟦v1,v2⟧),
      f ⊗^{ActD}_{r} F x · ld v2 x = ld v1 x · # F (f ⊗^{ActC}_{r} x).

  Definition preserves_unitor (ld : lineator_data)
    := ∏ (x : C), ld I_{Mon_V} x · # F au^{ActC}_{x} = au^{ActD}_{F x}.

  Definition preserves_unitorinv (ld : lineator_data)
    := ∏ (x : C), auinv^{ActD}_{F x} · ld I_{Mon_V} x = # F auinv^{ActC}_{x}.

  Definition preserves_actor (ld : lineator_data) : UU :=
    ∏ (v w : V) (x : C),  ld (v ⊗_{Mon_V} w) x · #F (aα^{ActC}_{v,w,x}) =
                            aα^{ActD}_{v,w,F x} · v ⊗^{ActD}_{l} (ld w x) · ld v (w ⊗_{ActC} x).

  Definition preserves_actorinv  (ld : lineator_data) : UU :=
    ∏ (v w : V) (x : C), aαinv^{ActD}_{v,w,F x} · ld (v ⊗_{Mon_V} w) x =
                           v ⊗^{ActD}_{l} (ld w x) · ld v (w ⊗_{ActC} x) · #F (aαinv^{ActC}_{v,w,x}).

  (* the order of the entries follws that of [fmonoidal_laxlaws] *)
  Definition lineator_laxlaws (ld : lineator_data) : UU :=
    lineator_nat_left ld × lineator_nat_right ld × preserves_actor ld × preserves_unitor ld.

  Definition lineator_lax : UU := ∑ (ld : lineator_data), lineator_laxlaws ld.

  Definition lineator_lindata (ll : lineator_lax) : lineator_data := pr1 ll.
  Coercion lineator_lindata : lineator_lax >-> lineator_data.

  Definition lineator_linlaws (ll : lineator_lax) : lineator_laxlaws ll := pr2 ll.

  Definition lineator_linnatleft (ll : lineator_lax) : lineator_nat_left ll := pr12 ll.
  Definition lineator_linnatright (ll : lineator_lax) : lineator_nat_right ll := pr122 ll.

  Definition lineator_preservesactor (ll : lineator_lax) : preserves_actor ll := pr1 (pr222 ll).

  Lemma lineator_preservesactorinv (ll : lineator_lax) : preserves_actorinv ll.
  Proof.
    intros v w x.
    rewrite assoc'.
    apply (z_iso_inv_on_right _ _ _ (z_iso_from_actor_iso Mon_V ActD _ _ _)).
    cbn.
    etrans.
    2: { repeat rewrite assoc. apply cancel_postcomposition.
         apply lineator_preservesactor. }
    repeat rewrite assoc'.
    etrans.
    { apply pathsinv0, id_right. }
    apply maponpaths.
    etrans.
    2: { rewrite <- functor_comp.
         apply maponpaths.
         apply pathsinv0, (actegory_actorisolaw Mon_V ActC). }
    apply pathsinv0, functor_id.
  Qed.

  (*
  Definition lineator_preservesleftunitality {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : lineator_lax M N F) :
    preserves_leftunitality (lineator_preservestensordata fm) (lineator_preservesunit fm) := pr12 (pr222 fm).

  Lemma lineator_preservesleftunitalityinv {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : lineator_lax M N F) :
    preserves_leftunitalityinv (lineator_preservestensordata fm) (lineator_preservesunit fm).
  Proof.
    intro x.
    rewrite assoc'.
    apply (z_iso_inv_on_right _ _ _ (_,,_,, monoidal_leftunitorisolaw N (F x))).
    cbn.
    rewrite <- (lineator_preservesleftunitality fm).
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

  Definition lineator_preservesrightunitality {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : lineator_lax M N F) :
    preserves_rightunitality (lineator_preservestensordata fm) (lineator_preservesunit fm) := pr22 (pr222 fm).

  Lemma lineator_preservesrightunitalityinv {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (fm : lineator_lax M N F) :
    preserves_rightunitalityinv (lineator_preservestensordata fm) (lineator_preservesunit fm).
  Proof.
    intro x.
    rewrite assoc'.
    apply (z_iso_inv_on_right _ _ _ (_,,_,, monoidal_rightunitorisolaw N (F x))).
    cbn.
    rewrite <- (lineator_preservesrightunitality fm).
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
             {C D : category} {M : monoidal C} {N : monoidal D}
             {F : functor C D} (pt : preserves_tensordata M N F) : UU
    := ∏ (x y : C), is_z_isomorphism (pt x y).

  Definition pointwise_z_iso_from_preserves_tensor_strongly
             {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
             {pt : preserves_tensordata M N F} (pts : preserves_tensor_strongly pt) (x y : C) :
    z_iso (F x ⊗_{ N} F y) (F (x ⊗_{ M} y)) := pt x y ,, pts x y.

  Lemma preserves_actor_of_inverse_preserves_tensor
        {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
        {pt : preserves_tensordata M N F}
        (ptα : preserves_actor pt)
        (pts : preserves_tensor_strongly pt) (x y z : C) :
    (is_z_isomorphism_mor (pts (x ⊗_{M} y) z))
      · ((is_z_isomorphism_mor (pts x y)) ⊗^{N}_{r} (F z))
      · α^{N}_{F x, F y, F z} =
    (#F (α^{M}_{x,y,z}))
      · (is_z_isomorphism_mor (pts x (y ⊗_{M} z)))
      · ((F x) ⊗^{N}_{l} (is_z_isomorphism_mor (pts y z))).
  Proof.
    set (ptsx_yz := pointwise_z_iso_from_preserves_tensor_strongly pts x (y ⊗_{M} z)).
    set (ptsxy_z := pointwise_z_iso_from_preserves_tensor_strongly pts (x ⊗_{M} y) z).
    set (ptsfx := functor_on_z_iso
          (leftwhiskering_functor N (bifunctor_leftid N) (bifunctor_leftcomp N) (F x))
          (pointwise_z_iso_from_preserves_tensor_strongly pts y z)).
    set (ptsfz := functor_on_z_iso
          (rightwhiskering_functor N (bifunctor_rightid N) (bifunctor_rightcomp N) (F z))
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

  Lemma preserves_tensorinv_nat_right {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
    {pt : preserves_tensordata M N F} (pts : preserves_tensor_strongly pt) (ptrn : preserves_tensor_nat_right pt)
    (x1 x2 y : C) (f : C⟦x1,x2⟧) :
       (is_z_isomorphism_mor (pts x1 y)) · # F f ⊗^{ N}_{r} F y = # F (f ⊗^{ M}_{r} y) · (is_z_isomorphism_mor (pts x2 y)).
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

  Lemma preserves_tensorinv_nat_left {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
    {pt : preserves_tensordata M N F} (pts : preserves_tensor_strongly pt) (ptrn : preserves_tensor_nat_left pt)
    (x1 x2 y : C) (f : C⟦x1,x2⟧) :
      (is_z_isomorphism_mor (pts y x1)) · F y ⊗^{ N}_{l} # F f = # F (y ⊗^{ M}_{l} f) · (is_z_isomorphism_mor (pts y x2)).
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

  Definition preserves_unit_strongly {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (pu : preserves_unit M N F) : UU
    := is_z_isomorphism pu.

  Definition lineator_stronglaws {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D}
    (pt : preserves_tensordata M N F) (pu : preserves_unit M N F) : UU
    := preserves_tensor_strongly pt × preserves_unit_strongly pu.

  Definition lineator {C D : category} (M : monoidal C) (N : monoidal D) (F : functor C D)  : UU :=
    ∑ (Fm : lineator_lax M N F),
      lineator_stronglaws (lineator_preservestensordata Fm) (lineator_preservesunit Fm).

  Definition lineator_lineatorlax {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (Fm : lineator M N F) :
    lineator_lax M N F := pr1 Fm.
  Coercion lineator_lineatorlax : lineator >-> lineator_lax.

  Definition lineator_preservestensorstrongly {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (Fm : lineator M N F) :
    preserves_tensor_strongly (lineator_preservestensordata Fm) := pr12 Fm.

  Definition lineator_preservesunitstrongly {C D : category} {M : monoidal C} {N : monoidal D} {F : functor C D} (Fm : lineator M N F) :
    preserves_unit_strongly (lineator_preservesunit Fm) := pr22 Fm.


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
*)
End TheDefinitions.
(*

(** towards a bicategory of monoidal categories *)
  Definition identity_lineator_data {C : category} (M : monoidal C) :
    lineator_data M M (functor_identity C).
  Proof.
    split.
    - intros x y. apply identity.
    - apply identity.
  Defined.

  Lemma identity_lineator_laxlaws {C : category} (M : monoidal C) :
    lineator_laxlaws (identity_lineator_data M).
  Proof.
    repeat split; red; unfold lineator_preservesunit, lineator_preservestensordata; cbn; intros.
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

  Definition identity_lineator_lax {C : category} (M : monoidal C) :
    lineator_lax M M (functor_identity C)
    := identity_lineator_data M ,, identity_lineator_laxlaws M.

  Definition identity_lineator_stronglaws {C : category} (M : monoidal C) :
    lineator_stronglaws (lineator_preservestensordata (identity_lineator_lax M))
      (lineator_preservesunit (identity_lineator_lax M)).
  Proof.
    split.
    - intros x y. apply is_z_isomorphism_identity.
    - apply is_z_isomorphism_identity.
  Defined.

  Definition identity_lineator {C : category} (M : monoidal C) : lineator M M (functor_identity C)
    := identity_lineator_lax M ,, identity_lineator_stronglaws M.

  Definition comp_lineator_data {C D E : category} {M : monoidal C} {N : monoidal D} {O : monoidal E}
    {F : C ⟶ D} {G : D ⟶ E} (Fm : lineator_lax M N F) (Gm : lineator_lax N O G) :
    lineator_data M O (F ∙ G).
  Proof.
    split.
    - intros x y.
      exact (lineator_preservestensordata Gm (F x) (F y) · #G (lineator_preservestensordata Fm x y)).
    - exact (lineator_preservesunit Gm · #G (lineator_preservesunit Fm)).
  Defined.

  Lemma comp_lineator_laxlaws {C D E : category} {M : monoidal C} {N : monoidal D} {O : monoidal E}
    {F : C ⟶ D} {G : D ⟶ E} (Fm : lineator_lax M N F) (Gm : lineator_lax N O G) :
    lineator_laxlaws (comp_lineator_data Fm Gm).
  Proof.
    repeat split; red; cbn; unfold lineator_preservesunit, lineator_preservestensordata; cbn; intros.
    - etrans.
      2: { rewrite assoc'. apply maponpaths. apply functor_comp. }
      etrans.
      2: { do 2 apply maponpaths. apply lineator_linnatleft. }
      rewrite functor_comp.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply lineator_linnatleft.
    - etrans.
      2: { rewrite assoc'. apply maponpaths. apply functor_comp. }
      etrans.
      2: { do 2 apply maponpaths. apply lineator_linnatright. }
      rewrite functor_comp.
      repeat rewrite assoc.
      apply cancel_postcomposition.
      apply lineator_linnatright.
    - assert (auxF := lineator_preservesactor Fm x y z).
      unfold lineator_preservestensordata in auxF.
      assert (auxG := lineator_preservesactor Gm (F x) (F y) (F z)).
      unfold lineator_preservestensordata in auxG.
      rewrite bifunctor_leftcomp.
      rewrite bifunctor_rightcomp.
      etrans.
      2: { repeat rewrite assoc. apply cancel_postcomposition.
           repeat rewrite assoc'. do 2 apply maponpaths.
           apply pathsinv0, lineator_linnatleft. }
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
      apply lineator_linnatright.
    - assert (auxF := lineator_preservesleftunitality Fm x).
      assert (auxG := lineator_preservesleftunitality Gm (F x)).
      unfold lineator_preservesunit, lineator_preservestensordata in auxF, auxG.
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
      apply lineator_linnatright.
    - assert (auxF := lineator_preservesrightunitality Fm x).
      assert (auxG := lineator_preservesrightunitality Gm (F x)).
      unfold lineator_preservesunit, lineator_preservestensordata in auxF, auxG.
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
      apply lineator_linnatleft.
  Qed.

  Definition comp_lineator_lax {C D E : category} {M : monoidal C} {N : monoidal D} {O : monoidal E}
    {F : C ⟶ D} {G : D ⟶ E} (Fm : lineator_lax M N F) (Gm : lineator_lax N O G) :
    lineator_lax M O (F ∙ G)
    := comp_lineator_data Fm Gm ,, comp_lineator_laxlaws Fm Gm.

  Definition comp_lineator_stronglaws {C D E : category} {M : monoidal C} {N : monoidal D} {O : monoidal E}
    {F : C ⟶ D} {G : D ⟶ E} (Fm : lineator M N F) (Gm : lineator N O G) :
  lineator_stronglaws (lineator_preservestensordata (comp_lineator_lax Fm Gm))
    (lineator_preservesunit (comp_lineator_lax Fm Gm)).
  Proof.
    split.
    - intros x y.
      use tpair.
      + exact (#G (pr1 (lineator_preservestensorstrongly Fm x y)) · pr1 (lineator_preservestensorstrongly Gm (F x) (F y))).
      + split.
        * cbn.
          etrans.
          { repeat rewrite assoc'.
            apply maponpaths.
            rewrite assoc.
            apply cancel_postcomposition.
            rewrite <- functor_comp.
            apply maponpaths.
            apply (pr12 (lineator_preservestensorstrongly Fm x y)). }
          rewrite functor_id.
          rewrite id_left.
          apply (pr12 (lineator_preservestensorstrongly Gm (F x) (F y))).
        * cbn.
          etrans.
          { repeat rewrite assoc'.
            apply maponpaths.
            rewrite assoc.
            apply cancel_postcomposition.
            apply (pr22 (lineator_preservestensorstrongly Gm (F x) (F y))). }
          rewrite id_left.
          rewrite <- functor_comp.
          etrans.
          { apply maponpaths.
            apply (pr22 (lineator_preservestensorstrongly Fm x y)). }
          apply functor_id.
    - use tpair.
      + exact (#G (pr1 (lineator_preservesunitstrongly Fm)) · pr1 (lineator_preservesunitstrongly Gm)).
      + split.
        * cbn.
          etrans.
          { repeat rewrite assoc'.
            apply maponpaths.
            rewrite assoc.
            apply cancel_postcomposition.
            rewrite <- functor_comp.
            apply maponpaths.
            apply (pr12 (lineator_preservesunitstrongly Fm)). }
          rewrite functor_id.
          rewrite id_left.
          apply (pr12 (lineator_preservesunitstrongly Gm)).
        * cbn.
          etrans.
          { repeat rewrite assoc'.
            apply maponpaths.
            rewrite assoc.
            apply cancel_postcomposition.
            apply (pr22 (lineator_preservesunitstrongly Gm)). }
          rewrite id_left.
          rewrite <- functor_comp.
          etrans.
          { apply maponpaths.
            apply (pr22 (lineator_preservesunitstrongly Fm)). }
          apply functor_id.
  Qed.

  Definition comp_lineator {C D E : category} {M : monoidal C} {N : monoidal D} {O : monoidal E}
    {F : C ⟶ D} {G : D ⟶ E} (Fm : lineator M N F) (Gm : lineator N O G) : lineator M O (F ∙ G)
    := comp_lineator_lax Fm Gm ,, comp_lineator_stronglaws Fm Gm.

*)
End LinearFunctors.

(*
Section MonoidalNaturalTransformations.

  Context {C D : category} {M : monoidal C} {N : monoidal D}
    {F G : functor C D} (Fm : lineator_lax M N F) (Gm : lineator_lax M N G)
    (α : F ⟹ G).

  Definition is_mon_nat_trans : UU :=
    (∏ (a a' : C), lineator_preservestensordata Fm a a' · α (a ⊗_{M} a') = α a ⊗^{N} α a' · lineator_preservestensordata Gm a a') × lineator_preservesunit Fm · α I_{M} = lineator_preservesunit Gm.

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
    {F G : functor C D} (Fm : lineator_lax M N F) (Gm : lineator_lax M N G)
    (α : F ⟹ G).

  Lemma is_mon_nat_trans_pointwise_inverse (isnziα : is_nat_z_iso α) :
    is_mon_nat_trans Fm Gm α -> is_mon_nat_trans Gm Fm (nat_z_iso_inv (α,,isnziα)).
  Proof.
    intro ismnt. split.
    - intros x y.
      cbn.
      unfold lineator_preservestensordata.
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
*)
