Require Export UniMath.Foundations.PartA.


Notation "x .1" := (pr1 x) (at level 3, format "x '.1'").
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'").


Definition Fam (I : UU) :=
  I -> UU.

Definition Map__i {I : UU} (A B : Fam I) :=
  ∏ i, A i -> B i.
Infix "->__i" := Map__i (at level 99).

Definition idmap__i {I : UU} (A : Fam I) :=
  λ (i : I) (a : A i), a.

Definition comp__i {I : UU} {A B C : Fam I}
           (f : B ->__i C)
           (g : A ->__i B) :=
  λ i a, f i (g i a).
Infix "∘__i" := comp__i (at level 49).

Definition weq__i {I : UU} (A B : Fam I) : UU :=
  ∏ i, A i ≃ B i.
Infix "≃__i" := weq__i (at level 80).
Definition weqcomp__i {I : UU} {A B C : Fam I}
           (f : A ≃__i B) (g : B ≃__i C) :
  A ≃__i C :=
  λ i, weqcomp (f i) (g i).
Definition invweq__i {I : UU} {A B : Fam I} (f : A ≃__i B) : B ≃__i A :=
  λ i, invweq (f i).



Definition prefunctor (I J : UU) : UU :=
  ∑ F : Fam I -> Fam J,
        ∏ A B : Fam I, (A ->__i B) -> F A ->__i F B.

Definition on_objects {I J : UU} (F : prefunctor I J) : Fam I -> Fam J :=
  pr1 F.
Coercion on_objects : prefunctor >-> Funclass.


Definition on_maps {I J : UU} (F : prefunctor I J) {A B : Fam I} (f : A ->__i B) :
  on_objects F A ->__i on_objects F B :=
  pr2 F _ _ f.

Notation "F .map" := (on_maps F) (at level 3, format "F '.map'").


(* properties of functor *)
Definition id_to_id {I J : UU} (F : prefunctor I J) : UU :=
  ∏ A : Fam I,
        F.map (idmap__i A) = (idmap__i (F A)).


Definition comp_to_comp {I J : UU} (F : prefunctor I J) : UU :=
  ∏ A B C : Fam I,
  ∏ f : A ->__i B,
  ∏ g : B ->__i C,
        F.map (g ∘__i f) = (F.map g) ∘__i (F.map f).

Definition is_functor {I J : UU} (F : prefunctor I J) :=
  (id_to_id F) ×
  (comp_to_comp F).

Definition functor (I J : UU) : UU :=
  ∑ F : prefunctor I J,
        is_functor F.

Definition build_functor {I J : UU}
           (on_objects : Fam I -> Fam J)
           (on_maps : ∏ A B : Fam I, A ->__i B -> on_objects A ->__i on_objects B)
           (id_to_id : ∏ A, on_maps A A (idmap__i _) = idmap__i _)
           (comp_to_comp : ∏ A B C (f : A ->__i B) (g : B ->__i C),
                           on_maps _ _ (g ∘__i f) = on_maps _ _ g ∘__i on_maps _ _ f) :
  functor I J :=
  (on_objects,,
    on_maps),,
  id_to_id,,
  comp_to_comp.

Coercion functor_to_prefunctor {I J : UU} (F : functor I J) : prefunctor I J :=
  pr1 F.

(* projections of properties *)
Definition functor_id_to_id {I J : UU} (F : functor I J) :
  ∏ A : Fam I, F.map (idmap__i _) = (idmap__i _) :=
  pr1 (pr2 F).

Definition functor_comp_to_comp {I J : UU} (F : functor I J) :
  ∏ A B C : Fam I,
  ∏ f : A ->__i B,
  ∏ g : B ->__i C,
        F.map (g ∘__i f) = (F.map g) ∘__i (F.map f) :=
  pr2 (pr2 F).



Require Import UniMath.Foundations.Propositions.

Definition powerset : functor unit unit.
Proof.
  use build_functor.
  - exact (λ A _, A tt -> hProp).
  - intros A B f i A' b.
    exact (∃ a, A' a × f tt a = b).
  - intros A.
    cbn. unfold idmap__i.
    apply funextsec; intros _.
    apply funextfun; intros A'.
    apply funextfun; intros a.
    apply weqtopathshProp.
    use weq_iso.
    + apply hinhuniv.
      intros [a' [a'_is_in_A' a'_is_a]].
      induction a'_is_a.
      exact a'_is_in_A'.
    + intros a_is_in_A'.
      apply hinhpr.
      exists a. exists a_is_in_A'. reflexivity.
    + intros x.
      apply propproperty.
    + intros x.
      apply propproperty.
  - intros A B C.
    intros f g.
    unfold comp__i.
    apply funextsec; intros _.
    apply funextfun; intros A'.
    apply funextfun; intros c.
    apply weqtopathshProp.
    use weq_iso.
    + apply hinhfun.
      intros [a [a_is_in_A' g_f_a_is_c]].
      exists (f tt a).
      split.
      * apply hinhpr.
        exists a. exists a_is_in_A'. reflexivity.
      * exact g_f_a_is_c.
    + apply hinhuniv.
      intros [b [H g_a_is_c]]; revert H.
      apply hinhfun.
      intros [a [a_is_in_A' f_a_is_b]].
      exists a. exists a_is_in_A'. rewrite f_a_is_b. exact g_a_is_c.
    + intros x; apply propproperty.
    + intros x; apply propproperty.
Defined.

Goal ¬ ∑ A, A ≃ powerset (λ _, A) tt.
Proof.
  intros [A e].
  set (C a := hneg (make_hProp (e a a) (propproperty (e a a)))).
  assert (equivalence : C (invweq e C) <-> ¬ C (invweq e C)). {
    change (¬ e (invmap e C) (invweq e C) <-> ¬ C (invweq e C)).
    rewrite homotweqinvweq.
    apply isrefl_logeq.
  }
  assert (H1 : ¬ C (invweq e C)). {
    intros H.
    apply (dirprod_pr1 equivalence H).
    exact H.
  }
  apply H1.
  apply (dirprod_pr2 equivalence).
  exact H1.
Qed.
