(** the concept of morphism between actegories that is a functor between the
    categories acted upon that is compatible with the action structures

Written by Ralph Matthes in close correspondence with the code in [UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered]

Naming is inspired from Actegories for the Working Amthematician by Matteo Capucci and Bruno Gavranović,
available at https://arxiv.org/abs/2203.16351

There are lax and non-lax versions of morphisms: the lax morphisms of V-actegories are called lax V-linear functors, and the non-lax version the V-linear functors, where the difference is that in the latter the crucial natural transformation called the lineator is required to be an isomorphism.

The non-lax version is not called strong so as to avoid confusion with the usual denomination of the lineator as the strength of the underlying functor. [lineator_lax] is that notion of strength together with the laws governing it.

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
Require Import UniMath.CategoryTheory.Monoidal.ConstructionOfActegories.
Require Import UniMath.CategoryTheory.coslicecat.
Require Import UniMath.CategoryTheory.Monoidal.Examples.MonoidalPointedObjects.

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
  Identity Coercion lineator_data_funclass : lineator_data >-> Funclass.

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

  Lemma isaprop_lineator_laxlaws (ld : lineator_data) : isaprop (lineator_laxlaws ld).
  Proof.
    apply isapropdirprod; [| apply isapropdirprod ; [| apply isapropdirprod]];
      repeat (apply impred; intro); apply D.
  Qed.

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

  Definition lineator_preservesunitor (ll : lineator_lax) : preserves_unitor ll := pr2 (pr222 ll).

  Lemma lineator_preservesunitorinv (ll : lineator_lax) : preserves_unitorinv ll.
  Proof.
    intro x.
    apply (z_iso_inv_on_right _ _ _ (_,,_,, actegory_unitorisolaw Mon_V ActD (F x))).
    cbn.
    rewrite <- (lineator_preservesunitor ll).
    repeat rewrite assoc'.
    etrans.
    { apply pathsinv0, id_right. }
    apply maponpaths.
    etrans.
    2: { rewrite <- functor_comp.
         apply maponpaths.
         apply pathsinv0, (actegory_unitorisolaw Mon_V ActC x). }
    apply pathsinv0, functor_id.
  Qed.

  Definition lineator_strongly (ld : lineator_data) : UU
    := ∏ (v : V) (x : C), is_z_isomorphism (ld v x).

  Definition pointwise_z_iso_from_lineator_strongly {ld : lineator_data}
    (pas : lineator_strongly ld) (v : V) (x : C) :
    z_iso (v ⊗_{ActD} F x) (F (v ⊗_{ActC} x)) := ld v x ,, pas v x.

  Lemma preserves_actor_of_inverse_lineator_strongly
        {ld : lineator_data}
        (pα : preserves_actor ld)
        (ls : lineator_strongly ld) (v w : V) (x : C) :
    (is_z_isomorphism_mor (ls (v ⊗_{Mon_V} w) x))
       · aα^{ActD}_{v, w, F x} =
    (#F (aα^{ActC}_{v,w,x}))
      · (is_z_isomorphism_mor (ls v (w ⊗_{ActC} x)))
      · (v ⊗^{ActD}_{l} (is_z_isomorphism_mor (ls w x))).
  Proof.
    set (lsv_wx := pointwise_z_iso_from_lineator_strongly ls v (w ⊗_{ActC} x)).
    set (lsvw_x := pointwise_z_iso_from_lineator_strongly ls (v ⊗_{Mon_V} w) x).
    set (lsfv := functor_on_z_iso
          (leftwhiskering_functor ActD v)
          (pointwise_z_iso_from_lineator_strongly ls w x)).
    apply (z_iso_inv_on_left _ _ _ _ lsfv).
    apply pathsinv0.
    apply (z_iso_inv_on_left _ _ _ _ lsv_wx).
    rewrite assoc'.
    rewrite assoc'.
    etrans.
    2: {
      apply maponpaths.
      rewrite assoc.
      exact (pα v w x).
    }
    etrans.
    2: {
      rewrite assoc.
      apply maponpaths_2.
      exact (! pr222 lsvw_x).
    }
    apply (! id_left _).
  Qed.

  Lemma lineatorinv_nat_right {ld : lineator_data} (ls : lineator_strongly ld) (lrn : lineator_nat_right ld)
    (v1 v2 : V) (x : C) (f : V⟦v1,v2⟧) :
    (is_z_isomorphism_mor (ls v1 x)) · f ⊗^{ActD}_{r} F x =  #F (f ⊗^{ActC}_{r} x) · (is_z_isomorphism_mor (ls v2 x)).
  Proof.
    set (ldiso := ld v1 x ,, ls v1 x : z_iso _ _).
    apply (z_iso_inv_on_right _ _ _ ldiso).
    rewrite assoc.
    etrans.
    2: {
      apply maponpaths_2.
      apply lrn.
    }
    rewrite assoc'.
    unfold is_z_isomorphism_mor.
    rewrite (pr12 (ls v2 x)).
    apply (! id_right _).
  Qed.

  Lemma lineatorinv_nat_left {ld : lineator_data} (ls : lineator_strongly ld) (lln : lineator_nat_left ld)
    (v : V) (x1 x2 : C) (f : C⟦x1,x2⟧) :
      (is_z_isomorphism_mor (ls v x1)) · v ⊗^{ActD}_{l} # F f = # F (v ⊗^{ActC}_{l} f) · (is_z_isomorphism_mor (ls v x2)).
  Proof.
    set (ldiso := ld v x1 ,, ls v x1 : z_iso _ _).
    apply (z_iso_inv_on_right _ _ _ ldiso).
    rewrite assoc.
    etrans.
    2: {
      apply maponpaths_2.
      apply lln.
    }
    rewrite assoc'.
    unfold is_z_isomorphism_mor.
    rewrite (pr12 (ls v x2)).
    apply (! id_right _).
  Qed.

  Definition lineator : UU := ∑ (ll : lineator_lax), lineator_strongly ll.

  Definition lineator_lineatorlax (lin : lineator) : lineator_lax := pr1 lin.
  Coercion lineator_lineatorlax : lineator >-> lineator_lax.

  Definition lineator_linstrongly (lin : lineator) : lineator_strongly lin := pr2 lin.

  (** We now show that everything behaves as expected **)
  Definition functor_imageofaction : bifunctor V C D
    := compose_bifunctor_with_functor ActC F.

  Definition functor_actionofrightimage : bifunctor V C D
    := compose_functor_with_bifunctor (functor_identity _) F ActD.

  Definition lineator_is_nattrans_type : UU
    := binat_trans functor_actionofrightimage functor_imageofaction.

  (* I really don't know how to call the following lemma *)
  Definition lineator_is_nattrans {ld : lineator_data}
    (lnl : lineator_nat_left ld) (lnr : lineator_nat_right ld) : lineator_is_nattrans_type.
  Proof.
    use make_binat_trans.
    - use make_binat_trans_data.
      intros v x.
      apply ld.
    - use tpair.
      + intros v x1 x2 g.
        apply lnl.
      + intros v1 v2 x f.
        apply lnr.
  Defined.

  Lemma lineator_is_nattrans_full {ld : lineator_data}
    (lnl : lineator_nat_left ld) (lnr : lineator_nat_right ld) :
    ∏ (v1 v2 : V) (x1 x2 : C) (f : V⟦v1,v2⟧) (g : C⟦x1,x2⟧),
      f ⊗^{ActD} # F g · ld v2 x2 = ld v1 x1 · # F (f ⊗^{ActC} g).
  Proof.
    intros.
    etrans.
    { unfold functoronmorphisms1.
      rewrite assoc'.
      rewrite lnl.
      apply assoc. }
    rewrite lnr.
    rewrite assoc'.
    apply maponpaths.
    apply pathsinv0, functor_comp.
  Qed.

  Definition lineator_inv_is_nattrans_type : UU
    := binat_trans functor_imageofaction functor_actionofrightimage.

  (* name follows [lineator_is_nattrans], for lack of a better proposition *)
  Definition lineator_inv_is_nattrans
    {ld : lineator_data}
    (lnl : lineator_nat_left ld) (lnr : lineator_nat_right ld) (ls : lineator_strongly ld)
    : lineator_inv_is_nattrans_type
    := inv_binattrans_from_binatiso(α:=lineator_is_nattrans lnl lnr) ls.

  (* Strictly linear functors *)
  Definition lineator_strictly (ld : lineator_data) : UU
    := ∏ (v : V) (x : C), ∑ (pf : v ⊗_{ActD} (F x) = F (v ⊗_{ActC} x)), ld v x = transportf _ pf (identity (v ⊗_{ActD} (F x))).

  Lemma lineator_strictly_is_strongly  {ld : lineator_data} (lst : lineator_strictly ld) : lineator_strongly ld.
  Proof.
    intros v x.
    use (iso_stable_under_equalitytransportf (pr2 (lst v x)) (is_z_isomorphism_identity (v ⊗_{ActD} F x))).
  Qed.

End TheDefinitions.

Arguments lineator_lindata {_ _ _ _ _} _ _ _.
Arguments lineator_laxlaws {_ _ _ _ _} _.
Arguments lineator_strongly {_ _ _ _ _} _.
Arguments lineator_preservesactor {_ _ _ _ _} _ _ _ _.
Arguments lineator_preservesunitor {_ _ _ _ _} _ _.
Arguments lineator_linstrongly {_ _ _ _ _} _ _ _.

(** towards a bicategory of actegories *)
  Definition identity_lineator_data {C : category} (Act : actegory Mon_V C) :
    lineator_data Act Act (functor_identity C).
  Proof.
    - intros v x. apply identity.
  Defined.

  Lemma identity_lineator_laxlaws {C : category} (Act : actegory Mon_V C) :
    lineator_laxlaws (identity_lineator_data Act).
  Proof.
    repeat split; red; unfold identity_lineator_data; cbn; intros.
    - rewrite id_left. apply id_right.
    - rewrite id_left. apply id_right.
    - rewrite id_right.
      rewrite bifunctor_leftid.
      rewrite id_right.
      apply id_left.
    - apply id_left.
  Qed.

  Definition identity_lineator_lax {C : category} (Act : actegory Mon_V C) :
    lineator_lax Act Act (functor_identity C)
    := identity_lineator_data Act ,, identity_lineator_laxlaws Act.

  Definition identity_lineator_strongly {C : category} (Act : actegory Mon_V C) :
    lineator_strongly (identity_lineator_lax Act).
  Proof.
    - intros v x. apply is_z_isomorphism_identity.
  Defined.

  Definition identity_lineator {C : category} (Act : actegory Mon_V C) : lineator Act Act (functor_identity C)
    := identity_lineator_lax Act ,, identity_lineator_strongly Act.

  Definition comp_lineator_data {C D E : category} {ActC : actegory Mon_V C} {ActD : actegory Mon_V D} {ActE : actegory Mon_V E}
    {F : C ⟶ D} {G : D ⟶ E} (Fl : lineator_lax ActC ActD F) (Gl : lineator_lax ActD ActE G) :
    lineator_data ActC ActE (F ∙ G).
  Proof.
    intros v x.
    exact (lineator_lindata Gl v (F x) · #G (lineator_lindata Fl v x)).
  Defined.

  Lemma comp_lineator_laxlaws {C D E : category} {ActC : actegory Mon_V C} {ActD : actegory Mon_V D} {ActE : actegory Mon_V E}
    {F : C ⟶ D} {G : D ⟶ E} (Fl : lineator_lax ActC ActD F) (Gl : lineator_lax ActD ActE G) :
    lineator_laxlaws (comp_lineator_data Fl Gl).
  Proof.
    repeat split; red; cbn; unfold comp_lineator_data; cbn; intros.
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
    - assert (auxF := lineator_preservesactor Fl v w x).
      assert (auxG := lineator_preservesactor Gl v w (F x)).
      rewrite bifunctor_leftcomp.
      etrans.
      2: { repeat rewrite assoc. apply cancel_postcomposition.
           repeat rewrite assoc'. do 2 apply maponpaths.
           apply pathsinv0, lineator_linnatleft. }
      etrans.
      2: { apply cancel_postcomposition.
           repeat rewrite assoc. apply cancel_postcomposition.
           exact auxG. }
      repeat rewrite assoc'. apply maponpaths.
      repeat rewrite <- functor_comp.
      apply maponpaths.
      etrans; [ exact auxF |].
      apply assoc'.
    - assert (auxF := lineator_preservesunitor Fl x).
      assert (auxG := lineator_preservesunitor Gl (F x)).
      etrans; [| exact auxG].
      clear auxG.
      rewrite <- auxF.
      clear auxF.
      repeat rewrite assoc'.
      apply maponpaths.
      apply pathsinv0, functor_comp.
  Qed.

  Definition comp_lineator_lax {C D E : category} {ActC : actegory Mon_V C} {ActD : actegory Mon_V D} {ActE : actegory Mon_V E}
    {F : C ⟶ D} {G : D ⟶ E} (Fl : lineator_lax ActC ActD F) (Gl : lineator_lax ActD ActE G) :
    lineator_lax ActC ActE (F ∙ G) := comp_lineator_data Fl Gl ,, comp_lineator_laxlaws Fl Gl.

  Definition comp_lineator_strongly {C D E : category} {ActC : actegory Mon_V C} {ActD : actegory Mon_V D} {ActE : actegory Mon_V E}
    {F : C ⟶ D} {G : D ⟶ E} (Fl : lineator ActC ActD F) (Gl : lineator ActD ActE G) :
    lineator_strongly (comp_lineator_lax Fl Gl).
  Proof.
    intros v x.
    exists (#G (pr1 (lineator_linstrongly Fl v x)) · pr1 (lineator_linstrongly Gl v (F x))).
    split; cbn; unfold comp_lineator_data.
    - etrans.
      { repeat rewrite assoc'.
        apply maponpaths.
        rewrite assoc.
        apply cancel_postcomposition.
        rewrite <- functor_comp.
        apply maponpaths.
        apply (pr12 (lineator_linstrongly Fl v x)). }
      rewrite functor_id.
      rewrite id_left.
      apply (pr12 (lineator_linstrongly Gl v (F x))).
    - etrans.
      { repeat rewrite assoc'.
        apply maponpaths.
        rewrite assoc.
        apply cancel_postcomposition.
        apply (pr22 (lineator_linstrongly Gl v (F x))). }
      rewrite id_left.
      rewrite <- functor_comp.
      etrans.
      { apply maponpaths.
        apply (pr22 (lineator_linstrongly Fl v x)). }
      apply functor_id.
  Defined.

  Definition comp_lineator {C D E : category} {ActC : actegory Mon_V C} {ActD : actegory Mon_V D} {ActE : actegory Mon_V E}
    {F : C ⟶ D} {G : D ⟶ E} (Fl : lineator ActC ActD F) (Gl : lineator ActD ActE G) : lineator ActC ActE (F ∙ G)
    := comp_lineator_lax Fl Gl ,, comp_lineator_strongly Fl Gl.

End LinearFunctors.

Section TransformationsOfActegories.

  Context {V : category} {Mon_V : monoidal V} {C D : category} {ActC : actegory Mon_V C} {ActD : actegory Mon_V D}.

  Definition is_linear_nat_trans {F G : functor C D}
    (Fl : lineator_lax Mon_V ActC ActD F) (Gl : lineator_lax Mon_V ActC ActD G)(ξ : F ⟹ G) : UU :=
    ∏ (v : V) (x : C), lineator_lindata Mon_V ActC ActD F Fl v x · ξ (v ⊗_{ActC} x) =
                         v ⊗^{ActD}_{l} ξ x · lineator_lindata Mon_V ActC ActD G Gl v x.

  Lemma isaprop_is_linear_nat_trans {F G : functor C D}
    (Fl : lineator_lax Mon_V ActC ActD F) (Gl : lineator_lax Mon_V ActC ActD G)
    (ξ : F ⟹ G) : isaprop (is_linear_nat_trans Fl Gl ξ).
  Proof.
    apply impred; intro v; apply impred; intro x. apply D.
  Qed.

  Lemma is_linear_nat_trans_pointwise_inverse {F G : functor C D}
    (Fl : lineator_lax Mon_V ActC ActD F) (Gl : lineator_lax Mon_V ActC ActD G)
    (ξ : F ⟹ G) (isnziξ : is_nat_z_iso ξ) :
    is_linear_nat_trans Fl Gl ξ -> is_linear_nat_trans Gl Fl (nat_z_iso_inv (ξ,,isnziξ)).
  Proof.
    intros islnt v x.
    cbn.
    set (aux := (_,,is_z_iso_leftwhiskering_z_iso (actegory_action Mon_V ActD) v (ξ x) (isnziξ x)  : z_iso _ _)).
    apply pathsinv0, (z_iso_inv_on_right _ _ _ aux).
    rewrite assoc.
    apply (z_iso_inv_on_left _ _ _ _ (_,,isnziξ (v ⊗_{ActC} x))).
    cbn.
    apply (!(islnt v x)).
  Qed.


  Lemma is_linear_nat_trans_identity {F : functor C D} (Fl : lineator_lax Mon_V ActC ActD F) :
    is_linear_nat_trans Fl Fl (nat_trans_id F).
  Proof.
    intros v c.
    rewrite id_right.
    etrans.
    2: { apply cancel_postcomposition. apply pathsinv0, bifunctor_leftid. }
    apply pathsinv0, id_left.
  Qed.

  Lemma is_linear_nat_trans_comp {F G H : functor C D}
    (Fl : lineator_lax Mon_V ActC ActD F)
    (Gl : lineator_lax Mon_V ActC ActD G)
    (Hl : lineator_lax Mon_V ActC ActD H) {ξ1 : F ⟹ G} {ξ2 : G ⟹ H}
    (islnt1 : is_linear_nat_trans Fl Gl ξ1)
    (islnt2 : is_linear_nat_trans Gl Hl ξ2) : is_linear_nat_trans Fl Hl (nat_trans_comp _ _ _ ξ1 ξ2).
  Proof.
    intros v x.
    cbn.
    rewrite bifunctor_leftcomp.
    rewrite assoc.
    etrans.
    { apply cancel_postcomposition.
      apply islnt1. }
    do 2 rewrite assoc'.
    apply maponpaths.
    apply islnt2.
  Qed.

End TransformationsOfActegories.

Section StrongFunctors.

  Definition tensorialstrength {C : category} (M : monoidal C) (F : functor C C) : UU :=
    lineator_lax M (actegory_with_canonical_self_action M)
      (actegory_with_canonical_self_action M) F.

  Identity Coercion id_tensorialstrength : tensorialstrength >-> lineator_lax.

  Lemma tensorialstrength_lineator_nat_left {C : category} (M : monoidal C)
    {F : functor C C} (ts : tensorialstrength M F) :
    lineator_nat_left _ _ _ _ ts =
      ∏ (v x1 x2 : C) (g : C ⟦ x1, x2 ⟧),
      v ⊗^{ M}_{l} # F g · ts v x2 = ts v x1 · # F (v ⊗^{ M}_{l} g).
  Proof.
    apply idpath.
  Qed.

  Lemma tensorialstrength_lineator_nat_right {C : category} (M : monoidal C)
    {F : functor C C} (ts : tensorialstrength M F) :
    lineator_nat_right _ _ _ _ ts =
      ∏ (v1 v2 x : C) (f : C ⟦ v1, v2 ⟧),
      f ⊗^{ M}_{r} F x · ts v2 x = ts v1 x · # F (f ⊗^{ M}_{r} x).
  Proof.
    apply idpath.
  Qed.

  Lemma tensorialstrength_preserves_unitor {C : category} (M : monoidal C)
    {F : functor C C} (ts : tensorialstrength M F) :
    preserves_unitor _ _ _ _ ts = ∏ c : C, ts I_{M} c · # F lu^{M}_{c} = lu^{M}_{F c}.
  Proof.
    apply idpath.
  Qed.

  Lemma tensorialstrength_preserves_actor {C : category} (M : monoidal C)
    {F : functor C C} (ts : tensorialstrength M F) :
    preserves_actor _ _ _ _ ts = ∏ v w x : C,
        ts (v ⊗_{M} w) x · # F α^{M}_{v, w, x} =
          α^{M}_{v, w, F x} · v ⊗^{M}_{l} ts w x · ts v (w ⊗_{M} x).
  Proof.
    apply idpath.
  Qed.

  Definition pointedtensorialstrength {C : category} (M : monoidal C) (F : functor C C) : UU :=
    lineator_lax (monoidal_pointed_objects M) (actegory_with_canonical_pointed_action M)
                                              (actegory_with_canonical_pointed_action M) F.

  Identity Coercion id_pointedtensorialstrength : pointedtensorialstrength >-> lineator_lax.

  Lemma pointedtensorialstrength_lineator_nat_left {C : category} (M : monoidal C)
    {F : functor C C} (pts : pointedtensorialstrength M F):
    lineator_nat_left _ _ _ _ pts =
      ∏ (v : coslice_cat_total C I_{M}) (x1 x2 : C) (g : C⟦x1,x2⟧),
      pr1 v ⊗^{ M}_{l} # F g · pts v x2 = pts v x1 · # F (pr1 v ⊗^{ M}_{l} g).
  Proof.
    apply idpath.
  Qed.

  Lemma pointedtensorialstrength_lineator_nat_right {C : category} (M : monoidal C)
    {F : functor C C} (pts : pointedtensorialstrength M F):
    lineator_nat_right _ _ _ _ pts =
      ∏ (v1 v2 : coslice_cat_total C I_{M}) (x : C) (f : coslice_cat_total C I_{M} ⟦v1,v2⟧),
      pr1 f ⊗^{ M}_{r} F x · pts v2 x = pts v1 x · # F (pr1 f ⊗^{ M}_{r} x).
  Proof.
    apply idpath.
  Qed.

  Lemma pointedtensorialstrength_preserves_unitor {C : category} (M : monoidal C)
    {F : functor C C} (pts : pointedtensorialstrength M F):
    preserves_unitor _ _ _ _ pts ≃
      ∏ c : C, pts I_{ monoidal_pointed_objects M} c · # F lu^{M}_{c} = lu^{M}_{F c}.
  Proof.
    use weqimplimpl.
    - intros H c.
      assert (Hc := H c). clear H.
      cbn in Hc.
      unfold TotalDisplayedMonoidalWhiskered.total_unit, lifted_action_unitor_data in Hc. cbn in Hc.
      do 2 rewrite bifunctor_rightid in Hc. do 2 rewrite id_left in Hc.
      exact Hc.
    - intros H c.
      cbn.
      unfold TotalDisplayedMonoidalWhiskered.total_unit, lifted_action_unitor_data. cbn.
      do 2 rewrite bifunctor_rightid. do 2 rewrite id_left.
      apply H.
    - apply impred; intro c. apply C.
    - apply impred; intro c. apply C.
  Qed.

  Lemma pointedtensorialstrength_preserves_actor {C : category} (M : monoidal C)
    {F : functor C C} (pts : pointedtensorialstrength M F) :
    preserves_actor _ _ _ _ pts ≃
      ∏ (v w : coslice_cat_total C I_{M}) (x : C),
      pts (v ⊗_{monoidal_pointed_objects M} w) x · # F α^{M}_{pr1 v, pr1 w, x} =
          α^{M}_{pr1 v, pr1 w, F x} · pr1 v ⊗^{M}_{l} pts w x · pts v (pr1 w ⊗_{M} x).
  Proof.
    use weqimplimpl.
    - intros H v w x.
      assert (Hinst := H v w x). clear H.
      cbn in Hinst.
      unfold lifted_actor_data in Hinst. cbn in Hinst.
      do 2 rewrite bifunctor_rightid in Hinst. do 2 rewrite id_left in Hinst.
      exact Hinst.
    - intros H v w x.
      cbn.
      unfold lifted_actor_data. cbn.
      do 2 rewrite bifunctor_rightid. do 2 rewrite id_left.
      apply H.
    - do 3 (apply impred; intro). apply C.
    - do 3 (apply impred; intro). apply C.
  Qed.


End StrongFunctors.
