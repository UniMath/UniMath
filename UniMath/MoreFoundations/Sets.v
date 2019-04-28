(** ** More results on sets *)

Require Export UniMath.MoreFoundations.Propositions.
Require Export UniMath.Foundations.Sets.

(** ** Contents

  - (More entries need to be added here...)
  - Other universal properties for [setquot]
  - The equivalence relation of being in the same fiber
  - Subsets
 *)

Local Open Scope set.

Definition hProp_set : hSet := make_hSet _ isasethProp.

Definition isconst {X:UU} {Y:hSet} (f : X -> Y) : hProp := ∀ x x', f x = f x'.

Definition squash_to_hSet {X : UU} {Y : hSet} (f : X -> Y) : isconst f -> ∥ X ∥ -> Y.
Proof.
  apply squash_to_set, setproperty.
Defined.

Definition isconst_2 {X Y:UU} {Z:hSet} (f : X -> Y -> Z) : hProp :=
  (∀ x x' y y', f x y = f x' y')%set.

Definition squash_to_hSet_2 {X Y : UU} {Z : hSet} (f : X -> Y -> Z) :
  isconst_2 f -> ∥ X ∥ -> ∥ Y ∥ -> Z.
Proof.
  intros c. use squash_to_set.
  { apply isaset_forall_hSet. }
  { intros x. use squash_to_hSet. exact (f x). intros y y'. exact (c x x y y'). }
  { intros x x'. apply funextfun; intros yn.
    apply (squash_to_prop yn).
    { apply setproperty. }
    intros y. assert (e : hinhpr y = yn).
    { apply propproperty. }
    induction e. change ( f x y = f x' y ). exact (c x x' y y). }
Defined.

Definition isconst_2' {X Y:UU} {Z:hSet} (f : X -> Y -> Z) : hProp :=
  (
    (∀ x x' y, f x y = f x' y)
    ∧
    (∀ x y y', f x y = f x y')
  )%set.

Definition squash_to_hSet_2' {X Y : UU} {Z : hSet} (f : X -> Y -> Z) :
  isconst_2' f -> ∥ X ∥ -> ∥ Y ∥ -> Z.
Proof.
  intros [c d]. use squash_to_set.
  { apply isaset_forall_hSet. }
  { intros x. use squash_to_hSet. exact (f x). intros y y'. exact (d x y y'). }
  { intros x x'. apply funextfun; intros yn.
    apply (squash_to_prop yn).
    { apply setproperty. }
    intros y. assert (e : hinhpr y = yn).
    { apply propproperty. }
    induction e. change ( f x y = f x' y ). exact (c x x' y). }
Defined.

Definition eqset_to_path {X:hSet} (x y:X) : eqset x y -> x = y := λ e, e.

Lemma isapropiscomprelfun {X : UU} {Y : hSet} (R : hrel X) (f : X -> Y) : isaprop (iscomprelfun R f).
Proof.
  apply impred. intro x. apply impred. intro x'. apply impred. intro r. apply Y.
Defined.

Lemma iscomprelfun_funcomp {X Y Z : UU} {R : hrel X} {S : hrel Y}
           {f : X → Y} {g : Y → Z} (Hf : iscomprelrelfun R S f) (Hg : iscomprelfun S g) :
  iscomprelfun R (g ∘ f).
Proof.
  intros x x' r. exact (Hg _ _ (Hf x x' r)).
Defined.

(** ** Other universal properties for [setquot] *)

Theorem setquotunivprop' {X : UU} {R : eqrel X} (P : setquot (pr1 R) -> UU)
        (H : ∏ x, isaprop (P x)) (ps : ∏ x : X, P (setquotpr R x)) : ∏ c : setquot (pr1 R), P c.
Proof.
  exact (setquotunivprop R (λ x, make_hProp (P x) (H x)) ps).
Defined.

Theorem setquotuniv2prop' {X : UU} {R : eqrel X} (P : setquot (pr1 R) → setquot (pr1 R) → UU)
        (H : ∏ x1 x2, isaprop (P x1 x2))
        (ps : ∏ x1 x2, P (setquotpr R x1) (setquotpr R x2)) : ∏ c1 c2 : setquot (pr1 R), P c1 c2.
Proof.
  exact (setquotuniv2prop R (λ x1 x2, make_hProp (P x1 x2) (H x1 x2)) ps).
Defined.

Theorem setquotuniv3prop' {X : UU} {R : eqrel X}
        (P : setquot (pr1 R) → setquot (pr1 R) → setquot (pr1 R) → UU)
        (H : ∏ x1 x2 x3, isaprop (P x1 x2 x3))
        (ps : ∏ x1 x2 x3, P (setquotpr R x1) (setquotpr R x2) (setquotpr R x3)) :
  ∏ c1 c2 c3 : setquot (pr1 R), P c1 c2 c3.
Proof.
  exact (setquotuniv3prop R (λ x1 x2 x3, make_hProp (P x1 x2 x3) (H x1 x2 x3)) ps).
Defined.

Theorem setquotuniv4prop' {X : UU} {R : eqrel X}
        (P : setquot (pr1 R) → setquot (pr1 R) → setquot (pr1 R) → setquot (pr1 R) → UU)
        (H : ∏ x1 x2 x3 x4, isaprop (P x1 x2 x3 x4))
        (ps : ∏ x1 x2 x3 x4,
              P (setquotpr R x1) (setquotpr R x2) (setquotpr R x3) (setquotpr R x4)) :
  ∏ c1 c2 c3 c4 : setquot (pr1 R), P c1 c2 c3 c4.
Proof.
  exact (setquotuniv4prop R (λ x1 x2 x3 x4, make_hProp (P x1 x2 x3 x4) (H x1 x2 x3 x4)) ps).
Defined.

Definition setcoprod (X Y : hSet) : hSet :=
  make_hSet (X ⨿ Y) (isasetcoprod X Y (pr2 X) (pr2 Y)).


(** ** The equivalence relation of being in the same fiber *)

Definition same_fiber_eqrel {X Y : hSet} (f : X → Y) : eqrel X.
Proof.
  use make_eqrel.
  - intros x y.
    exact (eqset (f x) (f y)).
  - use iseqrelconstr.
    + intros ? ? ? xy yz; exact (xy @ yz).
    + intro; reflexivity.
    + intros ? ? eq; exact (!eq).
Defined.

(** ** Subsets *)

Definition subset {X : hSet} (Hsub : hsubtype X) : hSet :=
  make_hSet (carrier Hsub) (isaset_carrier_subset _ Hsub).

Definition makeSubset {X : hSet} {Hsub : hsubtype X} (x : X) (Hx : Hsub x) : subset Hsub :=
  x,, Hx.

Definition pi0 (X : UU) : hSet := setquotinset (pathseqrel X).

Section Pi0.
  Definition π₀ : Type -> hSet := pi0.
  Definition component {X:Type} : X -> π₀ X := setquotpr (pathseqrel X).
  Definition π₀_map {X Y:Type} : (X -> Y) -> (π₀ X -> π₀ Y)
    := λ f, setquotfun (pathseqrel X) (pathseqrel Y) f (λ x x', hinhfun (maponpaths f)).
  Definition π₀_universal_property {X:Type} {Y:hSet} : (π₀ X -> Y) ≃ (X -> Y).
  Proof.
    exists (λ h, h ∘ component). intros f. apply iscontraprop1.
    - apply isaproptotal2.
      + intros h. use (_ : isaset _). apply impred_isaset. intros x. apply setproperty.
      + intros h h' e e'. apply funextsec. intro w.
        { apply (surjectionisepitosets component).
          - apply issurjsetquotpr.
          - apply setproperty.
          - intros x. exact (maponpaths (λ k, k x) (e @ ! e')). }
    - now exists (setquotuniv _ _ f (λ x y e, squash_to_prop e (setproperty Y (f x) (f y)) (maponpaths f))).
  Defined.
  Definition π₀_universal_map {X:Type} {Y:hSet} : (X -> Y) -> (π₀ X -> Y) := invmap π₀_universal_property.
  Lemma π₀_universal_map_eqn {X:Type} {Y:hSet} (f : X -> Y) :
    ∏ (x:X), π₀_universal_map f (component x) = f x.
  Proof.
    reflexivity.
  Defined.
  Lemma π₀_universal_map_uniq {X:Type} {Y:hSet} (h h' : π₀ X -> Y) :
    (∏ x, h (component x) = h' (component x)) -> h ~ h'.
  Proof.
    intros e x. apply (surjectionisepitosets component).
    - apply issurjsetquotpr.
    - apply setproperty.
    - exact e.
  Defined.
End Pi0.


(** ** Minimal equivalence relations *)
(* Constructs the smallest eqrel containing a given relation *)
Section mineqrel.

  Close Scope set.

  Context {A : UU} (R0 : hrel A).

  Lemma isaprop_eqrel_from_hrel a b :
    isaprop (∏ R : eqrel A, (∏ x y, R0 x y -> R x y) -> R a b).
  Proof.
    apply impred; intro R; apply impred_prop.
  Qed.

  Definition eqrel_from_hrel : hrel A :=
    λ a b, make_hProp _ (isaprop_eqrel_from_hrel a b).

  Lemma iseqrel_eqrel_from_hrel : iseqrel eqrel_from_hrel.
  Proof.
    repeat split.
    - intros x y z H1 H2 R HR. exact (eqreltrans _ _ _ _ (H1 _ HR) (H2 _ HR)).
    - now intros x R _; apply (eqrelrefl R).
    - intros x y H R H'. exact (eqrelsymm _ _ _ (H _ H')).
  Qed.

  Lemma eqrel_impl a b : R0 a b -> eqrel_from_hrel a b.
  Proof.
    now intros H R HR; apply HR.
  Qed.

  (* eqrel_from_hrel is the *smallest* relation containing R0 *)
  Lemma minimal_eqrel_from_hrel (R : eqrel A) (H : ∏ a b, R0 a b -> R a b) :
    ∏ a b, eqrel_from_hrel a b -> R a b.
  Proof.
    now intros a b H'; apply (H' _ H).
  Qed.

End mineqrel.

Lemma eqreleq {A : UU} (R : eqrel A) (x y : A) : x = y → R x y.
Proof.
  intros e.
  induction e.
  apply eqrelrefl.
Defined.
