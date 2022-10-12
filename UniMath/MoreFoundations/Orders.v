(** ** More results on types of ordering *)

Require Import UniMath.MoreFoundations.Propositions.
Require Import UniMath.MoreFoundations.Sets.


(** * Strong orders *)
(** A _strong ordering_ is a transitive, irreflexive, and cotransitive relation.

The terminology is our own, and the definition is not very well-established.  Classically, this is nearly equivalent to the more established _strict total order_ (transitive, irreflexive, trichotomous).  Constructively/computationally, cotransitivity is generally better than trichotomy — in particular, it is constructively provable for the reals — so it is more used in such settings.   *)

Definition isStrongOrder {X : UU} (R : hrel X) : UU :=
  istrans R × iscotrans R × isirrefl R.

Lemma isapropisStrongOrder {X : hSet} (R : hrel X) :
  isaprop (isStrongOrder R).
Proof.
  apply isapropdirprod.
  - apply isaprop_istrans.
  - apply isapropdirprod.
    + apply isaprop_iscotrans.
    + apply isaprop_isirrefl.
Defined.

Section isso_pty.

Context {X : UU}.
Context {R : hrel X}
        (is : isStrongOrder R).

Definition istrans_isStrongOrder : istrans R :=
  pr1 is.
Definition iscotrans_isStrongOrder : iscotrans R :=
  pr1 (pr2 is).
Definition isirrefl_isStrongOrder : isirrefl R :=
  pr2 (pr2 is).
Definition isasymm_isStrongOrder : isasymm R :=
  istransandirrefltoasymm
    istrans_isStrongOrder
    isirrefl_isStrongOrder.

End isso_pty.

Lemma isStrongOrder_hnegispreorder :
  ∏ (X : hSet) (R : hrel X),
  isStrongOrder R → ispreorder (λ x y : X, (¬ R x y)%logic).
Proof.
  intros X R is.
  split.
  - intros x y z Hxy Hyz Hxz.
    generalize (iscotrans_isStrongOrder is _ y _ Hxz).
    apply toneghdisj.
    split.
    + exact Hxy.
    + exact Hyz.
  - exact (isirrefl_isStrongOrder is).
Defined.

Lemma isStrongOrder_bck {X Y : UU} (f : Y → X) (gt : hrel X) :
  isStrongOrder gt → isStrongOrder (fun_hrel_comp f gt).
Proof.
  intros is.
  split ; [ | split ].
  - intros x y z.
    apply (istrans_isStrongOrder is).
  - intros x y z.
    apply (iscotrans_isStrongOrder is).
  - intros x.
    apply (isirrefl_isStrongOrder is).
Qed.

Definition StrongOrder (X : UU) := ∑ R : hrel X, isStrongOrder R.
Definition make_StrongOrder {X : UU} (R : hrel X) (is : isStrongOrder R) : StrongOrder X :=
  R,,is.
Definition pr1StrongOrder {X : UU} : StrongOrder X → hrel X := pr1.
Coercion  pr1StrongOrder : StrongOrder >-> hrel.

Section so_pty.

Context {X : UU}.
Context (R : StrongOrder X).

Definition istrans_StrongOrder : istrans R :=
  istrans_isStrongOrder (pr2 R).
Definition iscotrans_StrongOrder : iscotrans R :=
  iscotrans_isStrongOrder (pr2 R).
Definition isirrefl_StrongOrder : isirrefl R :=
  isirrefl_isStrongOrder (pr2 R).
Definition isasymm_StrongOrder : isasymm R :=
  isasymm_isStrongOrder (pr2 R).

End so_pty.

Definition StrongOrder_bck {X Y : UU} (f : Y → X)
           (gt : StrongOrder X) : StrongOrder Y :=
  (fun_hrel_comp f gt) ,, isStrongOrder_bck f _ (pr2 gt).

Lemma isStrongOrder_setquot {X : UU} {R : eqrel X} {L : hrel X} (is : iscomprelrel R L) :
  isStrongOrder L → isStrongOrder (quotrel is).
Proof.
  intros H.
  split ; [ | split].
  - apply istransquotrel, (istrans_isStrongOrder H).
  - apply iscotransquotrel, (iscotrans_isStrongOrder H).
  - apply isirreflquotrel, (isirrefl_isStrongOrder H).
Qed.

Definition StrongOrder_setquot {X : UU} {R : eqrel X} {L : StrongOrder X}
           (is : iscomprelrel R L) : StrongOrder (setquot R) :=
  quotrel is,, isStrongOrder_setquot is (pr2 L).
