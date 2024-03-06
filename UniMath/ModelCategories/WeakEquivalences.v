Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.ModelCategories.MorphismClass.

Section weakeqv.

Local Open Scope cat.
Local Open Scope morcls.
Local Open Scope logic.

Definition weq_comp_ax {C : category} (W : morphism_class C) : UU :=
    ∀ x y z (f : x --> y) (g : y --> z),
      (W _ _) f ⇒ (W _ _) g ⇒ (W _ _) (f · g).
Definition weq_cancel_left_ax {C : category} (W : morphism_class C) : UU :=
    ∀ (x y z : C) (f : x --> y) (g : y --> z),
      (W _ _) f ⇒ (W _ _) (f · g) ⇒ (W _ _) g.
Definition weq_cancel_right_ax {C : category} (W : morphism_class C) : UU :=
    ∀ (x y z : C) (f : x --> y) (g : y --> z),
      (W _ _) g ⇒ (W _ _) (f · g) ⇒ (W _ _) f.

Definition is_weak_equivalences {C : category} (W : morphism_class C) : UU :=
    weq_comp_ax W × weq_cancel_left_ax W × weq_cancel_right_ax W.

Definition weak_equivalences (C : category) : UU :=
    ∑ (W : morphism_class C), is_weak_equivalences W.

Definition weq_class {C : category} (W : weak_equivalences C) := pr1 W.
Definition weq_is_weq {C : category} (W : weak_equivalences C) := (pr2 W).
Definition is_weq_comp {C : category} {W : morphism_class C} (weq : is_weak_equivalences W) := (pr1 (weq)).
Definition is_weq_cancel_left {C : category} {W : morphism_class C} (weq : is_weak_equivalences W) := pr12 weq.
Definition is_weq_cancel_right {C : category} {W : morphism_class C} (weq : is_weak_equivalences W) := pr22 weq.

Definition weq_comp {C : category} (W : weak_equivalences C) := is_weq_comp (weq_is_weq W).
Definition weq_cancel_left {C : category} (W : weak_equivalences C) := is_weq_cancel_left (weq_is_weq W).
Definition weq_cancel_right {C : category} (W : weak_equivalences C) := is_weq_cancel_right (weq_is_weq W).

Lemma isaprop_is_weak_equivalences {C : category} (W : morphism_class C) : isaprop (is_weak_equivalences W).
Proof.
  idtac;
    repeat apply isapropdirprod;
    do 3 (apply impred_isaprop; intro);
    apply propproperty.
Qed.

End weakeqv.