(** the concept of left action of a monoidal category on a category

written by Ralph Matthes in lockstep with the code in [UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered]

naming is inspired from https://ncatlab.org/nlab/show/actegory:
the whole structure is an [actegory], the binary operation is the [action], the extra data are the [action_unitor] and the [actor], together with their inverses

2022

*)

Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.

Local Open Scope cat.

Import BifunctorNotations.
Import MonoidalNotations.

Section A.

Context {V : category} (Mon_V : monoidal V). (** given the monoidal category that acts upon categories *)

(** Data **)
Definition action (C : category) : UU :=
  bifunctor V C C.
Identity Coercion actionintobifunctor : action >-> bifunctor.

(** the following widens the concept of left unitor of a monoidal category, a right unitor is not appropriate for actions *)
Definition action_unitor_data {C : category} (A : action C) : UU :=
  ∏ (x : C), C⟦I_{Mon_V} ⊗_{A} x, x⟧.

Definition action_unitorinv_data {C : category} (A : action C) : UU :=
  ∏ (x : C), C⟦x, I_{Mon_V} ⊗_{A} x⟧.

Definition actor_data {C : category} (A : action C) : UU :=
  ∏ (v w : V) (x : C), C ⟦(v ⊗_{Mon_V} w) ⊗_{A} x, v ⊗_{A} (w ⊗_{A} x)⟧.

Definition actorinv_data {C : category} (A : action C) : UU :=
  ∏ (v w : V) (x : C), C ⟦v ⊗_{A} (w ⊗_{A} x), (v ⊗_{Mon_V} w) ⊗_{A} x⟧.

Definition actegory_data (C : category) : UU :=
    ∑ A : action C,
        (action_unitor_data A) × (action_unitorinv_data A) ×
           (actor_data A) × (actorinv_data A).

Definition make_actegory_data {C : category} {A : action C}
  (au : action_unitor_data A) (auinv : action_unitorinv_data A)
  (aα : actor_data A) (aαinv : actorinv_data A) : actegory_data C
  := (A,,au,,auinv,,aα,,aαinv).

Definition actegory_action {C : category} (AD : actegory_data C) : action C := pr1 AD.
Coercion actegory_action : actegory_data >-> action.

Definition actegory_unitordata {C : category} (AD : actegory_data C) : action_unitor_data AD
  := pr1 (pr2 AD).
Notation "au_{ AD }" := (actegory_unitordata AD).

Definition actegory_unitorinvdata {C : category} (AD : actegory_data C) : action_unitorinv_data AD
  := pr12 (pr2 AD).
Notation "auinv_{ AD }" := (actegory_unitorinvdata AD).

Definition actegory_actordata {C : category} (AD : actegory_data C) : actor_data AD
  := pr12 (pr2 (pr2 AD)).
Notation "aα_{ AD }" := (actegory_actordata AD).

Definition actegory_actorinvdata {C : category} (AD : actegory_data C) : actorinv_data AD
  := pr22 (pr2 (pr2 AD)).
Notation "aαinv_{ AD }" := (actegory_actorinvdata AD).


(** Axioms **)
Definition action_unitor_nat {C : category} {A : action C} (au : action_unitor_data A) : UU :=
  ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  I_{Mon_V} ⊗^{A}_{l} f · au y = au x · f.

Definition action_unitorinv_nat {C : category} {A : action C} (auinv : action_unitorinv_data A) : UU :=
  ∏ (x y : C), ∏ (f : C ⟦x,y⟧),  auinv x · I_{Mon_V} ⊗^{A}_{l} f = f · auinv y.

Definition action_unitor_iso_law {C : category} {A : action C} (au : action_unitor_data A) (auinv : action_unitorinv_data A) : UU :=
  ∏ (x : C), is_inverse_in_precat (au x) (auinv x).

Definition action_unitor_law {C : category} {A : action C} (au : action_unitor_data A) (auinv : action_unitorinv_data A) : UU :=
  action_unitor_nat au × action_unitor_iso_law au auinv.

Definition action_unitorlaw_nat {C : category} {A : action C} {au : action_unitor_data A} {auinv : action_unitorinv_data A}
  (aul : action_unitor_law au auinv) : action_unitor_nat au := pr1 aul.

Definition action_unitorlaw_iso_law {C : category} {A : action C} {au : action_unitor_data A} {auinv : action_unitorinv_data A}
  (aul : action_unitor_law au auinv) : action_unitor_iso_law au auinv := pr2 aul.

Definition actor_nat_leftwhisker {C : category} {A : action C} (aα : actor_data A) : UU
  := ∏ (v w : V) (z z' : C) (h : C⟦z,z'⟧),
    (aα v w z) · (v ⊗^{A}_{l} (w ⊗^{A}_{l} h)) = ((v ⊗_{Mon_V} w) ⊗^{A}_{l} h) · (aα v w z').

Definition actor_nat_rightwhisker {C : category} {A : action C} (aα : actor_data A) : UU
  := ∏ (v v' w : V) (z : C) (f : V⟦v,v'⟧),
    (aα v w z) · (f ⊗^{A}_{r} (w ⊗_{A} z)) = ((f ⊗^{Mon_V}_{r} w) ⊗^{A}_{r} z) · (aα v' w z).

Definition actor_nat_leftrightwhisker {C : category} {A : action C} (aα : actor_data A) : UU
  := ∏ (v w w' : V) (z : C) (g : V⟦w,w'⟧),
    (aα v w z) · (v ⊗^{A}_{l} (g ⊗^{A}_{r} z)) = ((v ⊗^{Mon_V}_{l} g) ⊗^{A}_{r} z) · (aα v w' z).

Lemma actor_nat1 {C : category} {A : action C} {aα : actor_data A} (aαnl : actor_nat_leftwhisker aα)
  (aαnr : actor_nat_rightwhisker aα) (aαnlr : actor_nat_leftrightwhisker aα)
  {v v' w w' : V} {z z' : C} (f : V⟦v,v'⟧) (g : V⟦w,w'⟧) (h : C⟦z,z'⟧) :
  (aα v w z) · ((f ⊗^{A}_{r} (w ⊗_{A} z)) · (v' ⊗^{A}_{l} ((g ⊗^{A}_{r} z) · (w' ⊗^{A}_{l} h)))) =
    (((f ⊗^{Mon_V}_{r} w) · (v' ⊗^{Mon_V}_{l} g))  ⊗^{A}_{r} z) · ((v' ⊗_{Mon_V} w') ⊗^{A}_{l} h) · (aα v' w' z').
Proof.
  rewrite assoc.
  rewrite aαnr.
  rewrite assoc'.
  etrans. {
    apply cancel_precomposition.
    rewrite (bifunctor_leftcomp A).
    rewrite assoc.
    rewrite aαnlr.
    apply idpath.
  }

  etrans. {
    apply cancel_precomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply aαnl.
  }
  rewrite assoc.
  rewrite assoc.
  apply cancel_postcomposition.
  apply pathsinv0.
  rewrite (bifunctor_rightcomp A).
  apply idpath.
Qed.

Lemma actor_nat2 {C : category} {A : action C} {aα : actor_data A} (aαnl : actor_nat_leftwhisker aα)
  (aαnr : actor_nat_rightwhisker aα) (aαnlr : actor_nat_leftrightwhisker aα)
  {v v' w w' : V} {z z' : C} (f : V⟦v,v'⟧) (g : V⟦w,w'⟧) (h : C⟦z,z'⟧) :
  (aα v w z) · (f ⊗^{A} (g ⊗^{A} h)) = ((f ⊗^{Mon_V} g) ⊗^{A} h) · (aα v' w' z').
Proof.
  intros.
  unfold functoronmorphisms1.
  exact (actor_nat1 aαnl aαnr aαnlr f g h).
Qed.

Definition actor_iso_law {C : category} {A : action C} (aα : actor_data A) (aαinv : actorinv_data A) : UU
  := ∏ (v w : V) (z : C), is_inverse_in_precat (aα v w z) (aαinv v w z).

Definition actor_law {C : category} {A : action C} (aα : actor_data A) (aαinv : actorinv_data A) : UU :=
  (actor_nat_leftwhisker aα) × (actor_nat_rightwhisker aα) ×
    (actor_nat_leftrightwhisker aα) × (actor_iso_law aα aαinv).

Definition actorlaw_natleft {C : category} {A : action C} {aα : actor_data A} {aαinv : actorinv_data A}
  (aαl : actor_law aα aαinv) : actor_nat_leftwhisker aα := pr1 aαl.
Definition actorlaw_natright {C : category} {A : action C} {aα : actor_data A} {aαinv : actorinv_data A}
  (aαl : actor_law aα aαinv) : actor_nat_rightwhisker aα := pr1 (pr2 aαl).
Definition actorlaw_natleftright {C : category} {A : action C} {aα : actor_data A} {aαinv : actorinv_data A}
  (aαl : actor_law aα aαinv) : actor_nat_leftrightwhisker aα := pr1 (pr2 (pr2 aαl)).
Definition actorlaw_iso_law {C : category} {A : action C} {aα : actor_data A} {aαinv : actorinv_data A}
  (aαl : actor_law aα aαinv) : actor_iso_law aα aαinv := pr2 (pr2 (pr2 aαl)).

Definition actegory_triangle_identity {C : category}
           {A : action C}
           (au : action_unitor_data A)
           (aα : actor_data A)
    := ∏ (v : V) (y : C), (aα v I_{Mon_V} y) · (v ⊗^{A}_{l} (au y)) = (ru_{Mon_V} v) ⊗^{A}_{r} y.

Definition actegory_pentagon_identity {C : category} {A : action C} (aα : actor_data A) : UU :=
  ∏ (w v v' : V) (z : C),
    ((α_{Mon_V} w v v') ⊗^{A}_{r} z) · (aα w (v ⊗_{Mon_V} v') z) · (w ⊗^{A}_{l} (aα v v' z)) =
      (aα (w⊗_{Mon_V} v) v' z) · (aα w v (v' ⊗_{A} z)).

Definition actegory_laws {C : category} (AD : actegory_data C) : UU :=
  (action_unitor_law au_{AD} auinv_{AD}) × (actor_law aα_{AD} aαinv_{AD}) ×
    (actegory_triangle_identity au_{AD} aα_{AD}) × (actegory_pentagon_identity aα_{AD}).

Definition actegory (C : category) : UU :=
  ∑ (AD : actegory_data C), (actegory_laws AD).

Definition actegory_actdata {C : category} (Act : actegory C) : actegory_data C := pr1 Act.
Coercion actegory_actdata : actegory >-> actegory_data.

Definition actegory_actlaws {C : category} (Act : actegory C) : actegory_laws Act := pr2 Act.

Definition actegory_unitorlaw {C : category} (Act : actegory C) : action_unitor_law au_{Act} auinv_{Act} := pr1 (actegory_actlaws Act).
Definition actegory_unitornat {C : category} (Act : actegory C) : action_unitor_nat au_{Act} := action_unitorlaw_nat (actegory_unitorlaw Act).
Definition actegory_unitorisolaw {C : category} (Act : actegory C) : action_unitor_iso_law au_{Act} auinv_{Act} := action_unitorlaw_iso_law (actegory_unitorlaw Act).

Lemma actegory_unitorinvnat {C : category} (Act : actegory C) : action_unitorinv_nat auinv_{Act}.
Proof.
  intros x y f.
  apply (z_iso_inv_on_right _ _ _ (_,,_,,actegory_unitorisolaw Act x)).
  cbn.
  rewrite assoc.
  apply (z_iso_inv_on_left _ _ _ _ (_,,_,,actegory_unitorisolaw Act y)).
  apply pathsinv0, actegory_unitornat.
Qed.

Definition actegory_actorlaw {C : category} (Act : actegory C) : actor_law aα_{Act} aαinv_{Act} := pr12 (actegory_actlaws Act).
Definition actegory_actornatleft {C : category} (Act : actegory C) : actor_nat_leftwhisker aα_{Act} := actorlaw_natleft (actegory_actorlaw Act).
Definition actegory_actornatright {C : category} (Act : actegory C) : actor_nat_rightwhisker aα_{Act} := actorlaw_natright (actegory_actorlaw Act).
Definition actegory_actornatleftright {C : category} (Act : actegory C) : actor_nat_leftrightwhisker aα_{Act} := actorlaw_natleftright (actegory_actorlaw Act).
Definition actegory_actorisolaw {C : category} (Act : actegory C) : actor_iso_law aα_{Act} aαinv_{Act} := actorlaw_iso_law (actegory_actorlaw Act).

Definition actegory_triangleidentity {C : category} (Act : actegory C) : actegory_triangle_identity au_{Act} aα_{Act} := pr1 (pr22 (actegory_actlaws Act)).
Definition actegory_pentagonidentity {C : category} (Act : actegory C) : actegory_pentagon_identity aα_{Act} := pr2 (pr22 (actegory_actlaws Act)).

Lemma isaprop_actegory_laws {C : category} (AD : actegory_data C)
  : isaprop (actegory_laws AD).
Proof.
  repeat (apply isapropdirprod)
  ; repeat (apply impred ; intro)
  ; repeat (try apply C)
  ; repeat (apply isaprop_is_inverse_in_precat).
Qed.

(** Some additional data and properties which one deduces from actegories **)

Lemma action_unitor_nat_z_iso {C : category} (Act : actegory C):
  nat_z_iso (leftwhiskering_functor Act (bifunctor_leftid Act) (bifunctor_leftcomp Act) I_{Mon_V}) (functor_identity C).
Proof.
  use make_nat_z_iso.
  - use make_nat_trans.
    + exact (λ x, au_{Act} x).
    + exact (λ x y f, actegory_unitornat Act x y f).
  - intro x. exists (auinv_{Act} x).
    apply (actegory_unitorisolaw Act x).
Defined.

Definition z_iso_from_actor_iso
  {C : category} (Act : actegory C) (v w : V) (x : C)
  : z_iso ((v ⊗_{Mon_V} w) ⊗_{Act} x) (v ⊗_{Act} (w ⊗_{Act} x))
  := make_z_iso
       (aα_{Act} v w x)
       (aαinv_{Act} v w x)
       (actegory_actorisolaw Act v w x).

Definition actorinv_nat_leftwhisker {C : category} (Act : actegory C) :
  ∏ (v w : V) (z z' : C) (h : C⟦z,z'⟧),
    (v ⊗^{Act}_{l} (w ⊗^{Act}_{l} h)) · (aαinv_{Act} v w z') = (aαinv_{Act} v w z) · ((v ⊗_{Mon_V} w) ⊗^{Act}_{l} h) .
Proof.
  intros v w z z' h.
  apply (swap_nat_along_zisos (z_iso_from_actor_iso Act v w z) (z_iso_from_actor_iso Act v w z')).
  apply actegory_actornatleft.
Qed.

Definition actorinv_nat_rightwhisker {C : category} (Act : actegory C) :
  ∏ (v v' w : V) (z: C) (f : V⟦v,v'⟧),
    (f ⊗^{Act}_{r} (w ⊗_{Act} z)) · (aαinv_{Act} v' w z) = (aαinv_{Act} v w z) · ((f ⊗^{Mon_V}_{r} w) ⊗^{Act}_{r} z).
Proof.
  intros v v' w z f.
  apply (swap_nat_along_zisos (z_iso_from_actor_iso Act v w z) (z_iso_from_actor_iso Act v' w z)).
  apply actegory_actornatright.
Qed.

Definition actorinv_nat_leftrightwhisker {C : category} (Act : actegory C) :
  ∏ (v w w' : V) (z : C) (g : V⟦w,w'⟧),
    (v ⊗^{Act}_{l} (g ⊗^{Act}_{r} z)) · (aαinv_{Act} v w' z) = (aαinv_{Act} v w z) · ((v ⊗^{Mon_V}_{l} g) ⊗^{Act}_{r} z).
Proof.
  intros v w w' z g.
  apply (swap_nat_along_zisos (z_iso_from_actor_iso Act v w z) (z_iso_from_actor_iso Act v w' z)).
  apply actegory_actornatleftright.
Qed.

Definition actorinv_nat1 {C : category} (Act : actegory C)
  {v v' w w' : V} {z z' : C} (f : V⟦v,v'⟧) (g : V⟦w,w'⟧) (h : C⟦z,z'⟧) :
  ((f ⊗^{Act}_{r} (w ⊗_{Act} z)) · (v' ⊗^{Act}_{l} ((g ⊗^{Act}_{r} z) · (w' ⊗^{Act}_{l} h)))) · (aαinv_{Act} v' w' z') =
    (aαinv_{Act} v w z) · ((((f ⊗^{Mon_V}_{r} w) · (v' ⊗^{Mon_V}_{l} g)) ⊗^{Act}_{r} z) · ((v' ⊗_{Mon_V} w') ⊗^{ Act}_{l} h)).
Proof.
  apply (swap_nat_along_zisos
           (z_iso_from_actor_iso Act v w z)
           (z_iso_from_actor_iso Act v' w' z')
        ).
  unfold z_iso_from_actor_iso.
  unfold make_z_iso.
  unfold make_is_z_isomorphism.
  unfold pr1.
  apply actor_nat1.
  - exact (actegory_actornatleft Act).
  - exact (actegory_actornatright Act).
  - exact (actegory_actornatleftright Act).
Qed.

Lemma actorinv_nat2 {C : category} (Act : actegory C)
  {v v' w w' : V} {z z' : C} (f : V⟦v,v'⟧) (g : V⟦w,w'⟧) (h : C⟦z,z'⟧) :
  (f ⊗^{Act} (g ⊗^{Act} h)) · (aαinv_{Act} v' w' z') = (aαinv_{Act} v w z) · ((f ⊗^{Mon_V} g) ⊗^{Act} h).
Proof.
  intros.
  unfold functoronmorphisms1.
  apply actorinv_nat1.
Qed.

Lemma pentagon_identity_actorinv {C : category} (Act : actegory C) (w v u : V) (z : C):
  w ⊗^{ Act}_{l} (aαinv_{Act} v u z)
  · aαinv_{Act} w (v ⊗_{Mon_V} u) z
  · αinv_{Mon_V} w v u ⊗^{Act}_{r} z =
    aαinv_{Act} w v (u ⊗_{Act} z)
  · aαinv_{Act} (w ⊗_{Mon_V} v) u z.
Proof.
  apply pathsinv0.
  apply (z_iso_inv_on_right _ _ _ (z_iso_from_actor_iso Act _ _ _)).
  unfold z_iso_from_actor_iso.
  unfold make_z_iso.
  unfold make_is_z_isomorphism.
  etrans. { apply (pathsinv0 (id_right _)). }
  apply (z_iso_inv_on_right _ _ _ (z_iso_from_actor_iso Act _ _ _)).
  cbn.
  apply pathsinv0.
  etrans. {
   rewrite assoc.
   apply cancel_postcomposition.
   apply (pathsinv0 (actegory_pentagonidentity Act w v u z)).
  }
  etrans. {
    rewrite assoc.
    rewrite assoc.
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply (pathsinv0 (bifunctor_leftcomp Act _ _ _ _ _ _)).
  }
  etrans. {
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    apply cancel_precomposition.
    apply maponpaths.
    apply (pr2 (z_iso_from_actor_iso Act v u z)).
  }
  etrans. {
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    apply cancel_precomposition.
    apply bifunctor_leftid.
  }
  etrans. {
    apply cancel_postcomposition.
    apply cancel_postcomposition.
    apply id_right.
  }
  etrans. {
    apply cancel_postcomposition.
    rewrite assoc'.
    apply cancel_precomposition.
    apply (pr2 (z_iso_from_actor_iso Act w (v⊗_{Mon_V}u) z)).
  }
  etrans. {
    apply cancel_postcomposition.
    apply id_right.
  }
  etrans. {
    apply (pathsinv0 (bifunctor_rightcomp Act _ _ _ _ _ _)).
  }
  etrans. {
    apply maponpaths.
    apply (pr2 (pr2 (z_iso_from_associator_iso Mon_V w v u))).
  }
  apply bifunctor_rightid.
Qed.

End A.

Module ActegoryNotations.
  Notation "au_{ Mon_V , Act }" := (actegory_unitordata Mon_V Act).
  Notation "aα_{ Mon_V , Act }" := (actegory_actordata Mon_V Act).
  Notation "au_{ Mon_V , Act }_{ x }" := (actegory_unitordata Mon_V Act x ).
  Notation "aα_{ Mon_V , Act }_{ v , w , x }" := (actegory_actordata Mon_V Act v w x).
  Notation "au^{ Mon_V , Act }_{ x }" := (actegory_unitordata Mon_V Act x ).
  Notation "aα^{ Mon_V , Act }_{ v , w , x }" := (actegory_actordata Mon_V Act v w x).
  Notation "auinv^{ Mon_V , Act }_{ x }" := (actegory_unitorinvdata Mon_V Act x ).
  Notation "aαinv^{ Mon_V , Act }_{ v , w , x }" := (actegory_actorinvdata Mon_V Act v w x).
End ActegoryNotations.
