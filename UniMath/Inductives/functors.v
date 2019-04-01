Require Export UniMath.Foundations.PartA.


Notation "x .1" := (pr1 x) (at level 3, format "x '.1'").
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'").


Definition Fam (I : UU) :=
  I -> UU.

Definition Mapⁱ {I : UU} (A B : Fam I) :=
  ∏ i, A i -> B i.
Infix "->ⁱ" := Mapⁱ (at level 99).

Definition idmapⁱ {I : UU} (A : Fam I) :=
  λ (i : I) (a : A i), a.

Definition compⁱ {I : UU} {A B C : Fam I}
           (f : B ->ⁱ C)
           (g : A ->ⁱ B) :=
  λ i a, f i (g i a).
Infix "∘ⁱ" := compⁱ (at level 50).

Definition weqⁱ {I : UU} (A B : Fam I) : UU :=
  ∏ i, A i ≃ B i.
Infix "≃ⁱ" := weqⁱ (at level 80).
Definition weqcompⁱ {I : UU} {A B C : Fam I}
           (f : A ≃ⁱ B) (g : B ≃ⁱ C) :
  A ≃ⁱ C :=
  λ i, weqcomp (f i) (g i).
Definition invweqⁱ {I : UU} {A B : Fam I} (f : A ≃ⁱ B) : B ≃ⁱ A :=
  λ i, invweq (f i).



Definition prefunctor (I J : UU) : UU :=
  ∑ F : Fam I -> Fam J,
        ∏ A B : Fam I, (A ->ⁱ B) -> F A ->ⁱ F B.

Definition on_objects {I J : UU} (F : prefunctor I J) : Fam I -> Fam J :=
  pr1 F.
Coercion on_objects : prefunctor >-> Funclass.


Definition on_maps {I J : UU} (F : prefunctor I J) {A B : Fam I} (f : A ->ⁱ B) :
  on_objects F A ->ⁱ on_objects F B :=
  pr2 F _ _ f.

Notation "F .map" := (on_maps F) (at level 3, format "F '.map'").


(* properties of functor *)
Definition id_to_id {I J : UU} (F : prefunctor I J) : UU :=
  ∏ A : Fam I,
        F.map (idmapⁱ A) = (idmapⁱ (F A)).


Definition comp_to_comp {I J : UU} (F : prefunctor I J) : UU :=
  ∏ A B C : Fam I,
  ∏ f : A ->ⁱ B,
  ∏ g : B ->ⁱ C,
        F.map (g ∘ⁱ f) = (F.map g) ∘ⁱ (F.map f).

Definition is_functor {I J : UU} (F : prefunctor I J) :=
  (id_to_id F) ×
  (comp_to_comp F).

Definition functor (I J : UU) : UU :=
  ∑ F : prefunctor I J,
        is_functor F.

Definition build_functor {I J : UU}
           (on_objects : Fam I -> Fam J)
           (on_maps : ∏ A B : Fam I, A ->ⁱ B -> on_objects A ->ⁱ on_objects B)
           (id_to_id : ∏ A, on_maps A A (idmapⁱ _) = idmapⁱ _)
           (comp_to_comp : ∏ A B C (f : A ->ⁱ B) (g : B ->ⁱ C),
                           on_maps _ _ (g ∘ⁱ f) = on_maps _ _ g ∘ⁱ on_maps _ _ f) :
  functor I J :=
  (on_objects,,
    on_maps),,
  id_to_id,,
  comp_to_comp.

Coercion functor_to_prefunctor {I J : UU} (F : functor I J) : prefunctor I J :=
  pr1 F.

(* projections of properties *)
Definition functor_id_to_id {I J : UU} (F : functor I J) :
  ∏ A : Fam I, F.map (idmapⁱ _) = (idmapⁱ _) :=
  pr1 (pr2 F).

Definition functor_comp_to_comp {I J : UU} (F : functor I J) :
  ∏ A B C : Fam I,
  ∏ f : A ->ⁱ B,
  ∏ g : B ->ⁱ C,
        F.map (g ∘ⁱ f) = (F.map g) ∘ⁱ (F.map f) :=
  pr2 (pr2 F).



Require Import UniMath.Foundations.Propositions.

Definition powerset : functor unit unit.
Proof.
  use build_functor.
  - exact (λ A _, A tt -> hProp).
  - intros A B f i A' b.
    exact (∃ a, A' a × f tt a = b).
  - intros A.
    cbn. unfold idmapⁱ.
    apply funextsec; intros _.
    apply funextfun; intros A'.
    apply funextfun; intros a.
    apply weqtopathshProp.
    use weqgradth.
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
    unfold compⁱ.
    apply funextsec; intros _.
    apply funextfun; intros A'.
    apply funextfun; intros c.
    apply weqtopathshProp.
    use weqgradth.
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
  set (C a := hneg (hProppair (e a a) (propproperty (e a a)))).
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