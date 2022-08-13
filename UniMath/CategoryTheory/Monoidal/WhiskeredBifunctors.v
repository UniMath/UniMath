
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.

(* This import is included because in the end we want to show that
   bifunctors are equivalent to functors coming out of a product category
*)
Require Import  UniMath.CategoryTheory.PrecategoryBinProduct.

Open Scope cat.

Section Bifunctor.

    Context {A B C : category}.

  Definition bifunctor_data : UU :=
    ∑ (F : A -> B -> C),
      (∏ (a : A) (b1 b2 : B), B⟦b1, b2⟧ → C⟦F a b1, F a b2⟧) × (* left whiskering *)
      (∏ (b : B) (a1 a2 : A), A⟦a1, a2⟧ → C⟦F a1 b, F a2 b⟧). (* right whiskering *)

  Definition make_bifunctor_data
             (F : A -> B -> C)
             (lw : ∏ (a : A) (b1 b2 : B), B⟦b1, b2⟧ → C⟦F a b1, F a b2⟧)
             (rw : ∏ (b : B) (a1 a2 : A), A⟦a1, a2⟧ → C⟦F a1 b, F a2 b⟧)
             : bifunctor_data := (F,,lw,,rw).

  Definition bifunctor_on_objects (F : bifunctor_data) : A → B → C := pr1 F.
  Local Notation "a ⊗_{ F } b" := (bifunctor_on_objects F a b) (at level 31).

  Definition leftwhiskering_on_morphisms (F : bifunctor_data) :
     ∏ (a : A) (b1 b2 : B), B⟦b1, b2⟧ → C⟦a ⊗_{F} b1, a ⊗_{F} b2⟧ := pr1 (pr2 F).
  Local Notation "a ⊗^{ F }_{l} g" := (leftwhiskering_on_morphisms F a _ _ g) (at level 31).

  Definition rightwhiskering_on_morphisms (F : bifunctor_data) :
     ∏ (b : B) (a1 a2 : A), A⟦a1, a2⟧ → C⟦a1 ⊗_{F} b, a2 ⊗_{F} b⟧ := pr2 (pr2 F).
  Local Notation "f ⊗^{ F }_{r} b" := (rightwhiskering_on_morphisms F b _ _ f) (at level 31).

  Definition bifunctor_leftidax (F : bifunctor_data) :=
    ∏ (a : A) (b : B), a ⊗^{F}_{l} (identity b) = identity (a ⊗_{F} b).

  Definition bifunctor_rightidax (F : bifunctor_data) :=
    ∏ (b : B) (a : A), (identity a) ⊗^{F}_{r} b = identity (a ⊗_{F} b).

  Definition bifunctor_leftcompax (F : bifunctor_data) :=
    ∏ (a : A) (b1 b2 b3 : B) (g1 : B⟦b1,b2⟧) (g2 : B⟦b2,b3⟧), a ⊗^{F}_{l} (g1 · g2) = (a ⊗^{F}_{l} g1) · (a ⊗^{F}_{l} g2).

  Definition bifunctor_rightcompax (F : bifunctor_data) :=
    ∏ (b : B) (a1 a2 a3 : A) (f1 : A⟦a1,a2⟧) (f2 : A⟦a2,a3⟧), (f1 · f2) ⊗^{F}_{r} b = (f1 ⊗^{F}_{r} b) · (f2 ⊗^{F}_{r} b).

  Lemma leftwhiskering_functor (F : bifunctor_data) (bli : bifunctor_leftidax F) (blc : bifunctor_leftcompax F) (a : A): functor B C.
  Proof.
    use make_functor.
    - use tpair.
      + intro b.
        exact (a ⊗_{F} b).
      + intros b1 b2 g.
        exact (a ⊗^{F}_{l} g).
    - use tpair.
      + intros b.
        exact (bli a b).
      + intros b1 b2 b3 g2 g3.
        cbn.
        exact (blc a b1 b2 b3 g2 g3).
  Defined.

  Lemma rightwhiskering_functor (F : bifunctor_data) (bri : bifunctor_rightidax F) (brc : bifunctor_rightcompax F) (b : B) : functor A C.
  Proof.
    use make_functor.
    - use tpair.
      + intro a.
        exact (a ⊗_{F} b).
      + intros a1 a2 f.
        exact (f ⊗^{F}_{r} b).
    - use tpair.
      + intros a.
        exact (bri b a).
      + intros a1 a2 a3 f2 f3.
        cbn.
        exact (brc b a1 a2 a3 f2 f3).
  Defined.

  Definition functoronmorphisms1 (F : bifunctor_data) {a1 a2 : A} {b1 b2 : B} (f : A⟦a1,a2⟧) (g : B⟦b1,b2⟧)
             : C⟦a1 ⊗_{F} b1, a2 ⊗_{F} b2⟧ := (f ⊗^{F}_{r} b1) · (a2 ⊗^{F}_{l} g).
  Local Notation "f ⊗^{ F } g" := (functoronmorphisms1 F f g) (at level 31).

  Definition functoronmorphisms2 (F : bifunctor_data) {a1 a2 : A} {b1 b2 : B} (f : A⟦a1,a2⟧) (g : B⟦b1,b2⟧)
    : C⟦a1 ⊗_{F} b1, a2 ⊗_{F} b2⟧ := (a1 ⊗^{F}_{l} g) · (f ⊗^{F}_{r} b2).
  Local Notation "f ⊗^{ F }_{2} g" := (functoronmorphisms2 F f g) (at level 31).

  Definition functoronmorphisms_are_equal (F : bifunctor_data) :=
    ∏ (a1 a2 : A) (b1 b2 : B) (f : A⟦a1,a2⟧) (g : B⟦b1,b2⟧),
      f ⊗^{F} g = f ⊗^{F}_{2} g.

  Lemma whiskerscommutes (F : bifunctor_data) (fmae : functoronmorphisms_are_equal F) {a1 a2 : A} {b1 b2 : B} (f : A⟦a1,a2⟧) (g : B⟦b1,b2⟧) : (f ⊗^{F}_{r} b1)·(a2 ⊗^{F}_{l} g) = (a1 ⊗^{F}_{l} g)·(f ⊗^{F}_{r} b2).
  Proof.
    exact (fmae _ _ _ _ f g).
  Qed.

  Definition is_bifunctor (F : bifunctor_data) : UU :=
    (bifunctor_leftidax F) ×
    (bifunctor_rightidax F) ×
    (bifunctor_leftcompax F) ×
    (bifunctor_rightcompax F) ×
    (functoronmorphisms_are_equal F).

  Lemma isaprop_is_bifunctor (F : bifunctor_data)
    : isaprop (is_bifunctor F).
  Proof.
    repeat (apply isapropdirprod) ; try (repeat (apply impred_isaprop ; intro) ; apply homset_property).
  Qed.

  Lemma bifunctor_distributes_over_id {F : bifunctor_data} (bli : bifunctor_leftidax F) (bri : bifunctor_rightidax F) (a : A) (b : B) : (identity a) ⊗^{F} (identity b) = identity (a ⊗_{F} b).
  Proof.
    unfold functoronmorphisms1.
    rewrite bri.
    rewrite bli.
    apply id_left.
  Qed.

  Lemma bifunctor_distributes_over_comp {F : bifunctor_data} (blc : bifunctor_leftcompax F) (brc : bifunctor_rightcompax F) (fmae : functoronmorphisms_are_equal F) {a1 a2 a3 : A} {b1 b2 b3 : B} (f1 : A⟦a1,a2⟧) (f2 : A⟦a2,a3⟧) (g1 : B⟦b1,b2⟧) (g2 : B⟦b2,b3⟧) : (f1 · f2) ⊗^{F} (g1 · g2) = (f1 ⊗^{F} g1) · (f2 ⊗^{F} g2).
  Proof.
    unfold functoronmorphisms1.
    rewrite brc.
    rewrite blc.
    rewrite assoc.
    rewrite assoc.
    apply cancel_postcomposition.
    rewrite assoc'.
    rewrite (whiskerscommutes _ fmae f2 g1).
    apply assoc.
  Qed.

  Definition bifunctor : UU :=
    ∑ (F : bifunctor_data), is_bifunctor F.

  Definition make_bifunctor (F : bifunctor_data) (H : is_bifunctor F)
    : bifunctor := (F,,H).

  Definition bifunctordata_from_bifunctor (F : bifunctor) : bifunctor_data := pr1 F.
  Coercion bifunctordata_from_bifunctor : bifunctor >-> bifunctor_data.

  Definition isbifunctor_from_bifunctor (F : bifunctor) : is_bifunctor F := pr2 F.

  Definition bifunctor_leftid (F : bifunctor) : bifunctor_leftidax F := pr1 (isbifunctor_from_bifunctor F).

  Definition bifunctor_rightid (F : bifunctor) : bifunctor_rightidax F := pr1 (pr2 (isbifunctor_from_bifunctor F)).

  Definition bifunctor_leftcomp (F : bifunctor) : bifunctor_leftcompax F := pr1 (pr2 (pr2 ((isbifunctor_from_bifunctor F)))).

  Definition bifunctor_rightcomp (F : bifunctor) : bifunctor_rightcompax F := pr1 (pr2 (pr2 (pr2 (isbifunctor_from_bifunctor F)))).

  Definition bifunctor_equalwhiskers (F : bifunctor) : functoronmorphisms_are_equal F := pr2 (pr2 (pr2 (pr2 (isbifunctor_from_bifunctor F)))).

  Lemma when_bifunctor_becomes_leftwhiskering (F : bifunctor) (a : A) {b1 b2 : B} (g: B⟦b1, b2⟧):
    identity a ⊗^{ F } g = a ⊗^{F}_{l} g.
  Proof.
    unfold functoronmorphisms1. rewrite bifunctor_rightid.
    apply id_left.
  Qed.

  Lemma when_bifunctor_becomes_rightwhiskering (F : bifunctor) {a1 a2 : A} (b : B) (f: A⟦a1, a2⟧):
    f ⊗^{ F } identity b = f ⊗^{F}_{r} b.
  Proof.
    unfold functoronmorphisms1. rewrite bifunctor_leftid.
    apply id_right.
  Qed.

End Bifunctor.

  Arguments bifunctor_data : clear implicits.
  Arguments bifunctor : clear implicits.

  Module BifunctorNotations.
  Notation "a ⊗_{ F } b" := (bifunctor_on_objects F a b) (at level 31).
  Notation "a ⊗^{ F }_{l} g" := (leftwhiskering_on_morphisms F a _ _ g) (at level 31).
  Notation "f ⊗^{ F }_{r} b" := (rightwhiskering_on_morphisms F b _ _ f) (at level 31).
  Notation "f ⊗^{ F } g" := (functoronmorphisms1 F f g) (at level 31).
  End BifunctorNotations.

Section Bifunctors.

    Import BifunctorNotations.

  Lemma compose_bifunctor_with_functor_data {A B C D : category} (F : bifunctor A B C) (G : functor C D) : bifunctor_data A B D.
  Proof.
    use make_bifunctor_data.
    - intros a b.
      exact (G (a ⊗_{F} b)).
    - intros a b1 b2 g.
      exact (#G (a ⊗^{F}_{l} g)).
    - intros a b1 b2 f.
      exact (#G (f ⊗^{F}_{r} a)).
  Defined.

  Lemma composition_bifunctor_with_functor_isbifunctor {A B C D : category} (F : bifunctor A B C) (G : functor C D) : is_bifunctor (compose_bifunctor_with_functor_data F G).
  Proof.
    repeat split.
    - intros a b.
      cbn.
      rewrite bifunctor_leftid.
      exact (functor_id G (a ⊗_{F} b)).
    - intros a b.
      cbn.
      rewrite bifunctor_rightid.
      apply functor_id.
    - intros a b1 b2 b3 g1 g2.
      cbn.
      rewrite bifunctor_leftcomp.
      apply functor_comp.
    - intros  b a1 a2 a3 f1 f2.
      cbn.
      rewrite bifunctor_rightcomp.
      apply functor_comp.
    - intros a1 a2 b1 b2 f g.
      unfold compose_bifunctor_with_functor_data.
      etrans.
      { apply pathsinv0, functor_comp. }
      rewrite whiskerscommutes.
      apply functor_comp.
      apply bifunctor_equalwhiskers.
  Qed.

  Definition compose_bifunctor_with_functor {A B C D : category} (F : bifunctor A B C) (G : functor C D)
    : bifunctor A B D := (compose_bifunctor_with_functor_data F G ,, composition_bifunctor_with_functor_isbifunctor F G).

  Lemma compose_functor_with_bifunctor_data {A B A' B' C : category} (F : functor A A') (G : functor B B') (H : bifunctor A' B' C) : bifunctor_data A B C.
  Proof.
    use make_bifunctor_data.
    - intros a b.
      exact ((F a) ⊗_{H} (G b)).
    - intros a b1 b2 g.
      exact ((F a) ⊗^{H}_{l} (#G g)).
    - intros b a1 a2 f.
      exact ((#F f) ⊗^{H}_{r} (G b)).
  Defined.

  Lemma composition_functor_with_bifunctor_isbifunctor {A B A' B' C : category} (F : functor A A') (G : functor B B') (H : bifunctor A' B' C) : is_bifunctor (compose_functor_with_bifunctor_data F G H).
  Proof.
    repeat split.
    - intros a b.
      cbn.
      rewrite functor_id.
      apply bifunctor_leftid.
    - intros a b.
      cbn.
      rewrite functor_id.
      apply bifunctor_rightid.
    - intros a b1 b2 b3 g1 g2.
      cbn.
      rewrite functor_comp.
      apply bifunctor_leftcomp.
    - intros  b a1 a2 a3 f1 f2.
      cbn.
      rewrite functor_comp.
      apply bifunctor_rightcomp.
    - intros a1 a2 b1 b2 f g.
      apply (whiskerscommutes H (bifunctor_equalwhiskers H)).
  Qed.

  Definition compose_functor_with_bifunctor {A B A' B' C : category} (F : functor A A') (G : functor B B') (H : bifunctor A' B' C)
    : bifunctor A B C := (compose_functor_with_bifunctor_data F G H ,, composition_functor_with_bifunctor_isbifunctor F G H).

End Bifunctors.

Section WhiskeredBinaturaltransformation.

  Import BifunctorNotations.

  Context {A B C : category}.

  Definition binat_trans_data (F G : bifunctor A B C) : UU :=
    ∏ (a : A) (b : B), C⟦a ⊗_{F} b, a ⊗_{G} b⟧.

  Definition make_binat_trans_data {F G : bifunctor A B C} (α : ∏ (a : A) (b : B), C⟦a ⊗_{F} b, a ⊗_{G} b⟧) : binat_trans_data F G := α.

  Definition is_binat_trans {F G : bifunctor A B C} (α : binat_trans_data F G) :=
    (∏ (a : A) (b1 b2 : B) (g : B⟦b1,b2⟧),
       (a ⊗^{ F}_{l} g) · (α a b2) = (α a b1) · (a ⊗^{ G}_{l} g))
                                           ×
       (∏ (a1 a2 : A) (b : B) (f : A⟦a1,a2⟧),
       (f ⊗^{ F}_{r} b) · (α a2 b) = (α a1 b) · (f ⊗^{ G}_{r} b)).

  Lemma full_naturality_condition {F G : bifunctor A B C} {α : binat_trans_data F G} (αn : is_binat_trans α) {a1 a2 : A} {b1 b2 : B} (f : A⟦a1,a2⟧) (g : B⟦b1,b2⟧) : (f ⊗^{F} g)·(α a2 b2) = (α a1 b1)·(f ⊗^{G} g).
  Proof.
    unfold functoronmorphisms1.
    rewrite assoc'.
    rewrite (pr1 αn a2 _ _ g).
    rewrite assoc.
    rewrite (pr2 αn a1 a2 b1 f).
    apply assoc'.
  Qed.

  Definition binat_trans (F G : bifunctor A B C) : UU :=
    ∑ (α : binat_trans_data F G), is_binat_trans α.

  Definition binattransdata_from_binattrans {F G : bifunctor A B C} (α : binat_trans F G) : binat_trans_data F G := pr1 α.

  (* Something like this is done in Core.NaturalTransformation, but I don't really know what this funclass is,
     I inserted this to use (α x y) without having to project, it would be good to have some explanation,
     also I don't understand why making a coercion for binattransdata_from_binattrans is not sufficient
     since I already have a identity coercion for binat_trans_data. *)
  Definition binattransdata_from_binattrans_funclass {F G : bifunctor A B C} (α : binat_trans F G)
    : ∏ (a : A) (b : B), C⟦a ⊗_{F} b, a ⊗_{G} b⟧ := pr1 α.
  Coercion binattransdata_from_binattrans_funclass : binat_trans >-> Funclass.

  Definition make_binat_trans {F G : bifunctor A B C} (α : binat_trans_data F G) (H : is_binat_trans α)
    : binat_trans F G := (α,,H).

  Definition is_binatiso {F G : bifunctor A B C} (α : binat_trans F G)
    := ∏ (a : A) (b : B), is_z_isomorphism (pr1 α a b).

  Definition inv_from_binatiso {F G : bifunctor A B C} {α : binat_trans F G} (isiso: is_binatiso α) : binat_trans_data G F := fun a b => pr1 (isiso a b).

  Lemma is_binat_trans_inv_from_binatiso {F G : bifunctor A B C} {α : binat_trans F G} (isiso: is_binatiso α) : is_binat_trans (inv_from_binatiso isiso).
  Proof.
    split.
    - intros ? ? ? ?.
      apply pathsinv0.
      apply (z_iso_inv_on_right _ _ _ (α a b1 ,, isiso a b1)).
      rewrite assoc.
      apply (z_iso_inv_on_left _ _ _ _ (α a b2 ,, isiso a b2)).
      apply pathsinv0, (pr12 α).
    - intros ? ? ? ?.
      apply pathsinv0.
      apply (z_iso_inv_on_right _ _ _ (α a1 b ,, isiso a1 b)).
      rewrite assoc.
      apply (z_iso_inv_on_left _ _ _ _ (α a2 b ,, isiso a2 b)).
      apply pathsinv0, (pr22 α).
  Qed.

  Definition inv_binattrans_from_binatiso {F G : bifunctor A B C} {α : binat_trans F G} (isiso: is_binatiso α) : binat_trans G F := inv_from_binatiso isiso,, is_binat_trans_inv_from_binatiso isiso.

End WhiskeredBinaturaltransformation.

Section FunctorsFromProductCategory.

  Import BifunctorNotations.

  (* This notation comes from Precategorybinproduct. *)
  Local Notation "C × D" := (category_binproduct C D) (at level 75, right associativity).

  Definition bifunctor_to_functorfromproductcat_data {C D E : category}
             (F : bifunctor C D E) : functor_data (C × D) E.
  Proof.
    exists (λ cd, (pr1 cd) ⊗_{F} (pr2 cd)).
    exact (λ _ _ fg, (pr1 fg) ⊗^{F} (pr2 fg)).
  Defined.

  Definition bifunctor_to_functorfromproductcat_laws
             {C D E : category} (F : bifunctor C D E)
    : is_functor (bifunctor_to_functorfromproductcat_data F).
  Proof.
    split.
    - intro ; apply bifunctor_distributes_over_id.
      exact (bifunctor_leftid F).
      exact (bifunctor_rightid F).
    - intro ; intros ; apply bifunctor_distributes_over_comp.
      exact (bifunctor_leftcomp F).
      exact (bifunctor_rightcomp F).
      exact (bifunctor_equalwhiskers F).
  Qed.

  Definition bifunctor_to_functorfromproductcat {C D E : category}
             (F : bifunctor C D E) : functor (C × D) E
    := bifunctor_to_functorfromproductcat_data F ,, bifunctor_to_functorfromproductcat_laws F.

  Definition bifunctor_from_functorfromproductcat_data {C D E : category}
             (F : functor (C × D) E) : bifunctor_data C D E.
  Proof.
    exists (λ c d, F (c,,d)).
    exists (λ c _ _ g, #F (catbinprodmor (identity c) g)).
    exact (λ d _ _ f, #F (catbinprodmor f (identity d))).
  Defined.

  Definition bifunctor_from_functorfromproductcat_laws
             {C D E : category} (F : functor (C × D) E)
    : is_bifunctor (bifunctor_from_functorfromproductcat_data F).
  Proof.
    repeat split.
    - exact (λ c d, functor_id F (c ,, d)).
    - exact (λ c d, functor_id F (d ,, c)).
    - intros c d1 d2 d3 g1 g2.
      refine (_ @ functor_comp F (catbinprodmor (identity c) g1) (catbinprodmor (identity c) g2)).
      cbn.
      etrans. {
        apply maponpaths.
        apply maponpaths_2.
        apply (! id_left _).
      }
      apply maponpaths.
      apply binprod_comp.
    - intros d c1 c2 c3 f1 f2.
      refine (_ @ functor_comp F (catbinprodmor f1 (identity d)) (catbinprodmor f2 (identity d))).
      cbn.
      etrans. {
        do 2 apply maponpaths.
        apply (! id_left _).
      }
      apply maponpaths.
      apply binprod_comp.
    - intro ; intros.
      unfold functoronmorphisms1.
      unfold functoronmorphisms2.
      cbn.
      etrans. { apply (! functor_comp _ _ _). }
      etrans. { apply maponpaths ; apply (binprod_comp). }
      etrans.
      2: { apply functor_comp. }
      etrans.
      2: { apply maponpaths ; apply binprod_comp. }
      apply maponpaths.
      etrans. { apply (! binprod_comp _ _ _ _ _ _ f (identity a2) (identity b1) g). }
      etrans. { apply maponpaths_2 ; apply id_right. }
      etrans.
      2: { apply maponpaths_2 ; apply (! id_left _). }
      apply maponpaths.
      exact (id_left _ @ ! id_right _).
  Qed.

  Definition bifunctor_from_functorfromproductcat {C D E : category}
             (F : functor (C × D) E) : bifunctor C D E
    := bifunctor_from_functorfromproductcat_data F ,, bifunctor_from_functorfromproductcat_laws F.

  Lemma bifunctor_to_functor_to_bifunctor_data
        {C D E : category} (F : bifunctor C D E)
    : pr1 (bifunctor_from_functorfromproductcat (bifunctor_to_functorfromproductcat F)) = pr1 F.
  Proof.
    repeat (use total2_paths_f).
    - apply idpath.
    - repeat (apply funextsec ; intro).
      apply when_bifunctor_becomes_leftwhiskering.
    - repeat (apply funextsec ; intro).
      etrans. {
        rewrite transportf_const.
        apply when_bifunctor_becomes_rightwhiskering.
      }
      apply idpath.
  Qed.

  Lemma bifunctor_to_functor_to_bifunctor
        {C D E : category} (F : bifunctor C D E)
    : bifunctor_from_functorfromproductcat (bifunctor_to_functorfromproductcat F) = F.
  Proof.
    use total2_paths_f.
    { apply bifunctor_to_functor_to_bifunctor_data. }
    apply isaprop_is_bifunctor.
  Qed.

  Lemma functor_to_bifunctor_to_functor
        {C D E : category} (F : functor (C × D) E)
    : bifunctor_to_functorfromproductcat (bifunctor_from_functorfromproductcat F) = F.
  Proof.
    apply (functor_eq _ _ (homset_property _)).
    use total2_paths_f.
    - apply idpath.
    - etrans. { rewrite idpath_transportf.
                apply idpath. }
      repeat (apply funextsec ; intro).
      etrans. { apply (! functor_comp _ _ _). }
      apply maponpaths.
      etrans. { apply binprod_comp. }
      cbn.
      etrans. { apply maponpaths ; apply id_left. }
      etrans. { apply maponpaths_2 ; apply id_right. }
      apply idpath.
  Qed.

  Lemma bifunctor_equiv_functorfromproductcat (C D E : category)
    : bifunctor C D E ≃ functor (category_binproduct C D) E.
  Proof.
    use weq_iso.
    { apply bifunctor_to_functorfromproductcat. }
    { apply bifunctor_from_functorfromproductcat. }
    { intro ; apply bifunctor_to_functor_to_bifunctor. }
    intro ; apply functor_to_bifunctor_to_functor.
  Defined.

End FunctorsFromProductCategory.
