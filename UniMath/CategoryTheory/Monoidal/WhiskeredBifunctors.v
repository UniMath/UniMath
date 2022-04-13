
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.

Open Scope cat.

Section Bifunctor.

  Definition bifunctor_data (A B C : category) : UU :=
    ∑ (F : A -> B -> C),
      (∏ (a : A) (b1 b2 : B), B⟦b1, b2⟧ → C⟦F a b1, F a b2⟧) × (* left whiskering *)
      (∏ (b : B) (a1 a2 : A), A⟦a1, a2⟧ → C⟦F a1 b, F a2 b⟧). (* right whiskering *)

  Definition make_bifunctor_data {A B C : category}
             (F : A -> B -> C)
             (lw : ∏ (a : A) (b1 b2 : B), B⟦b1, b2⟧ → C⟦F a b1, F a b2⟧)
             (rw : ∏ (b : B) (a1 a2 : A), A⟦a1, a2⟧ → C⟦F a1 b, F a2 b⟧)
             : bifunctor_data A B C := (F,,lw,,rw).

  Definition bifunctor_on_objects {A B C : category} (F : bifunctor_data A B C) : A → B → C := pr1 F.
  Local Notation "a ⊗_{ F } b" := (bifunctor_on_objects F a b) (at level 31).

  Definition leftwhiskering_on_morphisms {A B C : category} (F : bifunctor_data A B C) :
     ∏ (a : A) (b1 b2 : B), B⟦b1, b2⟧ → C⟦a ⊗_{F} b1, a ⊗_{F} b2⟧ := pr1 (pr2 F).
  Local Notation "a ⊗^{ F }_{l} g" := (leftwhiskering_on_morphisms F a _ _ g) (at level 31).

  Definition rightwhiskering_on_morphisms {A B C : category} (F : bifunctor_data A B C) :
     ∏ (b : B) (a1 a2 : A), A⟦a1, a2⟧ → C⟦a1 ⊗_{F} b, a2 ⊗_{F} b⟧ := pr2 (pr2 F).
  Local Notation "f ⊗^{ F }_{r} b" := (rightwhiskering_on_morphisms F b _ _ f) (at level 31).

  Definition bifunctor_leftidax {A B C : category} (F : bifunctor_data A B C) :=
    ∏ (a : A) (b : B), a ⊗^{F}_{l} (identity b) = identity (a ⊗_{F} b).

  Definition bifunctor_rightidax {A B C : category} (F : bifunctor_data A B C) :=
    ∏ (b : B) (a : A), (identity a) ⊗^{F}_{r} b = identity (a ⊗_{F} b).

  Definition bifunctor_leftcompax {A B C : category} (F : bifunctor_data A B C) :=
    ∏ (a : A) (b1 b2 b3 : B) (g1 : B⟦b1,b2⟧) (g2 : B⟦b2,b3⟧), a ⊗^{F}_{l} (g1 · g2) = (a ⊗^{F}_{l} g1) · (a ⊗^{F}_{l} g2).

  Definition bifunctor_rightcompax {A B C : category} (F : bifunctor_data A B C) :=
    ∏ (b : B) (a1 a2 a3 : A) (f1 : A⟦a1,a2⟧) (f2 : A⟦a2,a3⟧), (f1 · f2) ⊗^{F}_{r} b = (f1 ⊗^{F}_{r} b) · (f2 ⊗^{F}_{r} b).

  Lemma leftwhiskering_functor {A B C : category} (F : bifunctor_data A B C) (bli : bifunctor_leftidax F) (blc : bifunctor_leftcompax F) (a : A): functor B C.
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

  Lemma rightwhiskering_functor {A B C : category} (F : bifunctor_data A B C) (bri : bifunctor_rightidax F) (brc : bifunctor_rightcompax F) (b : B) : functor A C.
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

  Definition functoronmorphisms1 {A B C : category} (F : bifunctor_data A B C) {a1 a2 : A} {b1 b2 : B} (f : A⟦a1,a2⟧) (g : B⟦b1,b2⟧)
             : C⟦a1 ⊗_{F} b1, a2 ⊗_{F} b2⟧ := (f ⊗^{F}_{r} b1) · (a2 ⊗^{F}_{l} g).
  Local Notation "f ⊗^{ F } g" := (functoronmorphisms1 F f g) (at level 31).

  Definition functoronmorphisms2 {A B C : category} (F : bifunctor_data A B C) {a1 a2 : A} {b1 b2 : B} (f : A⟦a1,a2⟧) (g : B⟦b1,b2⟧)
    : C⟦a1 ⊗_{F} b1, a2 ⊗_{F} b2⟧ := (a1 ⊗^{F}_{l} g) · (f ⊗^{F}_{r} b2).
  Local Notation "f ⊗^{ F }_{2} g" := (functoronmorphisms2 F f g) (at level 31).

  Definition functoronmorphisms_are_equal {A B C : category} (F : bifunctor_data A B C) :=
    ∏ (a1 a2 : A) (b1 b2 : B) (f : A⟦a1,a2⟧) (g : B⟦b1,b2⟧),
      f ⊗^{F} g = f ⊗^{F}_{2} g.

  Lemma whiskerscommutes {A B C : category} (F : bifunctor_data A B C) (fmae : functoronmorphisms_are_equal F) {a1 a2 : A} {b1 b2 : B} (f : A⟦a1,a2⟧) (g : B⟦b1,b2⟧) : (f ⊗^{F}_{r} b1)·(a2 ⊗^{F}_{l} g) = (a1 ⊗^{F}_{l} g)·(f ⊗^{F}_{r} b2).
  Proof.
    exact (fmae _ _ _ _ f g).
  Qed.

  Definition is_bifunctor {A B C : category} (F : bifunctor_data A B C) : UU :=
    (bifunctor_leftidax F) ×
    (bifunctor_rightidax F) ×
    (bifunctor_leftcompax F) ×
    (bifunctor_rightcompax F) ×
    (functoronmorphisms_are_equal F).

  Lemma bifunctor_distributes_over_id {A B C : category} {F : bifunctor_data A B C} (bli : bifunctor_leftidax F) (bri : bifunctor_rightidax F) (a : A) (b : B) : (identity a) ⊗^{F} (identity b) = identity (a ⊗_{F} b).
  Proof.
    unfold functoronmorphisms1.
    rewrite bri.
    rewrite bli.
    apply id_left.
  Qed.

  Lemma bifunctor_distributes_over_comp {A B C : category} {F : bifunctor_data A B C} (blc : bifunctor_leftcompax F) (brc : bifunctor_rightcompax F) (fmae : functoronmorphisms_are_equal F) {a1 a2 a3 : A} {b1 b2 b3 : B} (f1 : A⟦a1,a2⟧) (f2 : A⟦a2,a3⟧) (g1 : B⟦b1,b2⟧) (g2 : B⟦b2,b3⟧) : (f1 · f2) ⊗^{F} (g1 · g2) = (f1 ⊗^{F} g1) · (f2 ⊗^{F} g2).
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

  Definition bifunctor (A B C : category) : UU :=
    ∑ (F : bifunctor_data A B C), is_bifunctor F.

  Definition make_bifunctor {A B C : category} (F : bifunctor_data A B C) (H : is_bifunctor F)
    : bifunctor A B C := (F,,H).

  Definition bifunctordata_from_bifunctor {A B C : category} (F : bifunctor A B C) : bifunctor_data A B C := pr1 F.
  Coercion bifunctordata_from_bifunctor : bifunctor >-> bifunctor_data.

  Definition isbifunctor_from_bifunctor {A B C : category} (F : bifunctor A B C) : is_bifunctor F := pr2 F.

  Definition bifunctor_leftid {A B C : category} (F : bifunctor A B C) : bifunctor_leftidax F := pr1 (isbifunctor_from_bifunctor F).

  Definition bifunctor_rightid {A B C : category} (F : bifunctor A B C) : bifunctor_rightidax F := pr1 (pr2 (isbifunctor_from_bifunctor F)).

  Definition bifunctor_leftcomp {A B C : category} (F : bifunctor A B C) : bifunctor_leftcompax F := pr1 (pr2 (pr2 ((isbifunctor_from_bifunctor F)))).

  Definition bifunctor_rightcomp {A B C : category} (F : bifunctor A B C) : bifunctor_rightcompax F := pr1 (pr2 (pr2 (pr2 (isbifunctor_from_bifunctor F)))).

  Definition bifunctor_equalwhiskers {A B C : category} (F : bifunctor A B C) : functoronmorphisms_are_equal F := pr2 (pr2 (pr2 (pr2 (isbifunctor_from_bifunctor F)))).

  Lemma when_bifunctor_becomes_leftwhiskering {A B C : category} (F : bifunctor A B C) (a : A) {b1 b2 : B} (g: B⟦b1, b2⟧):
    identity a ⊗^{ F } g = a ⊗^{F}_{l} g.
  Proof.
    unfold functoronmorphisms1. rewrite bifunctor_rightid.
    apply id_left.
  Qed.

  Lemma when_bifunctor_becomes_rightwhiskering {A B C : category} (F : bifunctor A B C) {a1 a2 : A} (b : B) (f: A⟦a1, a2⟧):
    f ⊗^{ F } identity b = f ⊗^{F}_{r} b.
  Proof.
    unfold functoronmorphisms1. rewrite bifunctor_leftid.
    apply id_right.
  Qed.


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

End Bifunctor.

Module BifunctorNotations.
  Notation "a ⊗_{ F } b" := (bifunctor_on_objects F a b) (at level 31).
  Notation "a ⊗^{ F }_{l} g" := (leftwhiskering_on_morphisms F a _ _ g) (at level 31).
  Notation "f ⊗^{ F }_{r} b" := (rightwhiskering_on_morphisms F b _ _ f) (at level 31).
  Notation "f ⊗^{ F } g" := (functoronmorphisms1 F f g) (at level 31).
End BifunctorNotations.


Section WhiskeredBinaturaltransformation.

  Import BifunctorNotations.

  Definition binat_trans_data {A B C : category} (F G : bifunctor A B C) : UU :=
    ∏ (a : A) (b : B), C⟦a ⊗_{F} b, a ⊗_{G} b⟧.

  Definition make_binat_trans_data {A B C : category} {F G : bifunctor A B C} (α : ∏ (a : A) (b : B), C⟦a ⊗_{F} b, a ⊗_{G} b⟧) : binat_trans_data F G := α.

  Definition is_binat_trans {A B C : category} {F G : bifunctor A B C} (α : binat_trans_data F G) :=
    (∏ (a : A) (b1 b2 : B) (g : B⟦b1,b2⟧),
       (a ⊗^{ F}_{l} g) · (α a b2) = (α a b1) · (a ⊗^{ G}_{l} g))
                                           ×
       (∏ (a1 a2 : A) (b : B) (f : A⟦a1,a2⟧),
       (f ⊗^{ F}_{r} b) · (α a2 b) = (α a1 b) · (f ⊗^{ G}_{r} b)).

  Lemma full_naturality_condition {A B C : category} {F G : bifunctor A B C} {α : binat_trans_data F G} (αn : is_binat_trans α) {a1 a2 : A} {b1 b2 : B} (f : A⟦a1,a2⟧) (g : B⟦b1,b2⟧) : (f ⊗^{F} g) · (α a2 b2) = (α a1 b1) · (f ⊗^{G} g).
  Proof.
    unfold functoronmorphisms1.
    rewrite assoc'.
    rewrite (pr1 αn a2 _ _ g).
    rewrite assoc.
    rewrite (pr2 αn a1 a2 b1 f).
    apply assoc'.
  Qed.

  Definition binat_trans {A B C : category} (F G : bifunctor A B C) : UU :=
    ∑ (α : binat_trans_data F G), is_binat_trans α.

  Definition binattransdata_from_binattrans {A B C : category} {F G : bifunctor A B C} (α : binat_trans F G) : binat_trans_data F G := pr1 α.
  (* Something like this is done in Core.NaturalTransformation, but I don't really know what this funclass is,
     I inserted this to use (α x y) without having to project, it would be good to have some explanation,
     also I don't understand why making a coercion for binattransdata_from_binattrans is not sufficient
     since I already have a identity coercion for binat_trans_data. *)
  Definition binattransdata_from_binattrans_funclass {A B C : category} {F G : bifunctor A B C} (α : binat_trans F G)
    : ∏ (a : A) (b : B), C⟦a ⊗_{F} b, a ⊗_{G} b⟧ := pr1 α.
  Coercion binattransdata_from_binattrans_funclass : binat_trans >-> Funclass.

  Definition make_binat_trans {A B C : category} {F G : bifunctor A B C} (α : binat_trans_data F G) (H : is_binat_trans α)
    : binat_trans F G := (α,,H).

  Definition is_binatiso {A B C : category} {F G : bifunctor A B C} (α : binat_trans F G)
    := ∏ (a : A) (b : B), is_z_isomorphism (pr1 α a b).

End WhiskeredBinaturaltransformation.
