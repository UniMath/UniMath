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
  exact (setquotunivprop R (λ x, hProppair (P x) (H x)) ps).
Defined.

Theorem setquotuniv2prop' {X : UU} {R : eqrel X} (P : setquot (pr1 R) → setquot (pr1 R) → UU)
        (H : ∏ x1 x2, isaprop (P x1 x2))
        (ps : ∏ x1 x2, P (setquotpr R x1) (setquotpr R x2)) : ∏ c1 c2 : setquot (pr1 R), P c1 c2.
Proof.
  exact (setquotuniv2prop R (λ x1 x2, hProppair (P x1 x2) (H x1 x2)) ps).
Defined.

Theorem setquotuniv3prop' {X : UU} {R : eqrel X}
        (P : setquot (pr1 R) → setquot (pr1 R) → setquot (pr1 R) → UU)
        (H : ∏ x1 x2 x3, isaprop (P x1 x2 x3))
        (ps : ∏ x1 x2 x3, P (setquotpr R x1) (setquotpr R x2) (setquotpr R x3)) :
  ∏ c1 c2 c3 : setquot (pr1 R), P c1 c2 c3.
Proof.
  exact (setquotuniv3prop R (λ x1 x2 x3, hProppair (P x1 x2 x3) (H x1 x2 x3)) ps).
Defined.

Theorem setquotuniv4prop' {X : UU} {R : eqrel X}
        (P : setquot (pr1 R) → setquot (pr1 R) → setquot (pr1 R) → setquot (pr1 R) → UU)
        (H : ∏ x1 x2 x3 x4, isaprop (P x1 x2 x3 x4))
        (ps : ∏ x1 x2 x3 x4,
              P (setquotpr R x1) (setquotpr R x2) (setquotpr R x3) (setquotpr R x4)) :
  ∏ c1 c2 c3 c4 : setquot (pr1 R), P c1 c2 c3 c4.
Proof.
  exact (setquotuniv4prop R (λ x1 x2 x3 x4, hProppair (P x1 x2 x3 x4) (H x1 x2 x3 x4)) ps).
Defined.

Definition setcoprod (X Y : hSet) : hSet :=
  hSetpair (X ⨿ Y) (isasetcoprod X Y (pr2 X) (pr2 Y)).

(** ** The equivalence relation of being in the same fiber *)

Definition same_fiber_eqrel {X Y : hSet} (f : X → Y) : eqrel X.
Proof.
  use eqrelpair.
  - intros x y.
    exact (eqset (f x) (f y)).
  - use iseqrelconstr.
    + intros ? ? ? xy yz; exact (xy @ yz).
    + intro; reflexivity.
    + intros ? ? eq; exact (!eq).
Defined.

(** ** Subsets *)

Definition subset {X : hSet} (Hsub : hsubtype X) : hSet :=
  hSetpair (carrier Hsub) (isaset_carrier_subset _ Hsub).

Definition makeSubset {X : hSet} {Hsub : hsubtype X} (x : X) (Hx : Hsub x) : subset Hsub :=
  x,, Hx.