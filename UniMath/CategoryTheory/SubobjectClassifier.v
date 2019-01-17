(** * Subobject classifiers *)

(** ** Contents

  - Definition
  - Accessors
*)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.PartB.
Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.Monics.

Local Open Scope cat.

(** ** Definition *)

Definition subobject_classifier {C : precategory} (T : Terminal C) : UU :=
  ∑ (O : ob C) (true : C⟦T, O⟧), ∏ (X Y : ob C) (m : Monic _ X Y),
    ∃! chi : C⟦Y, O⟧,
      ∑ (H : m · chi = TerminalArrow _ _ · true), isPullback _ _ _ _ H.

Definition make_subobject_classifier {C : precategory} {T : Terminal C}
           (O : ob C) (true : C⟦T, O⟧) :
  (∏ (X Y : ob C) (m : Monic _ X Y),
    iscontr (∑ (chi : C⟦Y, O⟧)
               (H : m · chi = TerminalArrow _ _ · true),
               isPullback _ _ _ _ H)) -> subobject_classifier T.
Proof.
  intros.
  use tpair; [exact O|].
  use tpair; [exact true|].
  assumption.
Qed.

(** ** Accessors *)

Section Accessors.
  Context {C : precategory} {T : Terminal C} (O : subobject_classifier T).

  Definition subobject_classifier_object : ob C :=  pr1 O.

  (** [true] is monic. We only export the accessor for it them as a [Monic]
      (rather than the a morphism), as it's strictly more useful. *)
  Definition true' : C⟦T, subobject_classifier_object⟧ := pr1 (pr2 O).

  Local Lemma true_is_monic : isMonic true'.
  Proof.
    apply from_terminal_isMonic.
  Qed.

  Definition true : Monic _ T subobject_classifier_object :=
    mk_Monic _ true' true_is_monic.

  Definition subobject_classifier_universal_property {X Y} (m : Monic _ X Y) :
    iscontr (∑ (chi : C⟦Y, subobject_classifier_object⟧)
               (H : m · chi = TerminalArrow _ _ · true'),
               isPullback _ _ _ _ H) := pr2 (pr2 O) X Y m.

  Local Definition characteristic_morphism' {X Y} (m : Monic _ X Y) :
    C⟦Y, subobject_classifier_object⟧ :=
    pr1 (iscontrpr1 (subobject_classifier_universal_property m)).

  Definition subobject_classifier_square_commutes {X Y} (m : Monic _ X Y) :
    m · characteristic_morphism' m = TerminalArrow _ _ · true :=
    pr1 (pr2 (iscontrpr1 (subobject_classifier_universal_property m))).

  Definition subobject_classifier_pullback {X Y} (m : Monic _ X Y) :
    Pullback (characteristic_morphism' m) true.
  Proof.
    use mk_Pullback.
    - exact X.
    - exact m.
    - apply TerminalArrow.
    - apply subobject_classifier_square_commutes.
    - apply (pr2 (pr2 (iscontrpr1 (subobject_classifier_universal_property m)))).
  Defined.

  Definition subobject_classifier_pullback_sym {hsC : has_homsets C} {X Y} (m : Monic _ X Y) :
    Pullback true (characteristic_morphism' m).
  Proof.
    refine (@switchPullback (C,, _) _ _ _ _ _ (subobject_classifier_pullback m)).
    assumption.
  Defined.

End Accessors.

Coercion subobject_classifier_object : subobject_classifier >-> ob.
Coercion true : subobject_classifier >-> Monic.
