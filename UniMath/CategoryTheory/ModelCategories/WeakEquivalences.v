Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.ModelCategories.MorphismClass.

Section weakeqv.

Local Open Scope cat.
Local Open Scope morcls.
Local Open Scope logic.

Definition weq_of_iso_ax {M : category} (W : morphism_class M) :=
    ∀ x y (i : x --> y) (h : is_iso i), (W _ _) i.
Definition weq_comp_ax {M : category} (W : morphism_class M) :=
    ∀ x y z (f : x --> y) (g : y --> z), (W _ _) f ⇒ (W _ _) g ⇒ (W _ _) (g ∘ f).
Definition weq_cancel_left_ax {M : category} (W : morphism_class M) :=
    ∀ x y z (f : x --> y) (g : y --> z), (W _ _) f ⇒ (W _ _) (g ∘ f) ⇒ (W _ _) g.
Definition weq_cancel_right_ax {M : category} (W : morphism_class M) :=
    ∀ x y z (f : x --> y) (g : y --> z), (W _ _) g ⇒ (W _ _) (g ∘ f) ⇒ (W _ _) f.
    
Definition is_weak_equivalences {M : category} (W : morphism_class M) :=
    weq_of_iso_ax W × weq_comp_ax W × weq_cancel_left_ax W × weq_cancel_right_ax W.

Definition weak_equivalences (M : category) :=
    ∑ (W : morphism_class M), is_weak_equivalences W.

Definition weq_class {M : category} (W : weak_equivalences M) := pr1 W.
Definition weq_is_weq {M : category} (W : weak_equivalences M) := (pr2 W).
Definition is_weq_of_iso {M : category} {W : morphism_class M} (weq : is_weak_equivalences W) := pr1 (weq).
Definition is_weq_comp {M : category} {W : morphism_class M} (weq : is_weak_equivalences W) := pr1 (pr2 (weq)).
Definition is_weq_cancel_left {M : category} {W : morphism_class M} (weq : is_weak_equivalences W) := pr1 (pr2 (pr2 (weq))).
Definition is_weq_cancel_right {M : category} {W : morphism_class M} (weq : is_weak_equivalences W) := pr2 (pr2 (pr2 (weq))).

Definition weq_of_iso {M : category} (W : weak_equivalences M) := is_weq_of_iso (weq_is_weq W).
Definition weq_comp {M : category} (W : weak_equivalences M) := is_weq_comp (weq_is_weq W).
Definition weq_cancel_left {M : category} (W : weak_equivalences M) := is_weq_cancel_left (weq_is_weq W).
Definition weq_cancel_right {M : category} (W : weak_equivalences M) := is_weq_cancel_right (weq_is_weq W).

Lemma isaprop_is_weak_equivalences {M : category} (W : morphism_class M) : isaprop (is_weak_equivalences W).
Proof.
  idtac; 
    repeat apply isapropdirprod; 
    do 4 (apply impred_isaprop; intro);
    apply propproperty.
Qed.

End weakeqv.