(** ** More results on types of ordering *)

Require Import UniMath.MoreFoundations.Propositions.
Require Import UniMath.MoreFoundations.Sets.


(** * Preorders *)
(** [po] is defined in [Foundations.Sets], but with some access functions missing *)

Section po_pty.

Context {X : UU}.
Context (R : po X).

Definition istrans_po : istrans R :=
  pr1 (pr2 R).
Definition isrefl_po : isrefl R :=
  pr2 (pr2 R).

End po_pty.



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
Definition pr2StrongOrder {X : UU} {R : StrongOrder X} : isStrongOrder R := pr2 R.
Coercion pr2StrongOrder : StrongOrder >-> isStrongOrder.

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


(** * Reverse orders *)
(** or how easily define ge x y := le x y *)

Definition hrel_reverse {X : UU} (l : hrel X) := λ x y, l y x.

Lemma istrans_reverse {X : UU} (l : hrel X) :
  istrans l → istrans (hrel_reverse l).
Proof.
  intros Hl x y z Hxy Hyz.
  now apply (Hl z y x).
Qed.

Lemma isrefl_reverse {X : UU} (l : hrel X) :
  isrefl l → isrefl (hrel_reverse l).
Proof.
  intros Hl x.
  now apply Hl.
Qed.

Lemma ispreorder_reverse {X : UU} (l : hrel X) :
  ispreorder l → ispreorder (hrel_reverse l).
Proof.
  intros H.
  split.
  now apply istrans_reverse, (pr1 H).
  now apply isrefl_reverse, (pr2 H).
Qed.
Definition po_reverse {X : UU} (l : po X) :=
  make_po (hrel_reverse l) (ispreorder_reverse l (pr2 l)).
Lemma po_reverse_correct {X : UU} (l : po X) :
  ∏ x y : X, po_reverse l x y = l y x.
Proof.
  intros x y.
  now apply paths_refl.
Qed.

Lemma issymm_reverse {X : UU} (l : hrel X) :
  issymm l → issymm (hrel_reverse l).
Proof.
  intros Hl x y.
  now apply Hl.
Qed.

Lemma iseqrel_reverse {X : UU} (l : hrel X) :
  iseqrel l → iseqrel (hrel_reverse l).
Proof.
  intros H.
  split.
  now apply ispreorder_reverse, (pr1 H).
  now apply issymm_reverse, (pr2 H).
Qed.
Definition eqrel_reverse {X : UU} (l : eqrel X) :=
  make_eqrel (hrel_reverse l) (iseqrel_reverse l (pr2 l)).
Lemma eqrel_reverse_correct {X : UU} (l : eqrel X) :
  ∏ x y : X, eqrel_reverse l x y = l y x.
Proof.
  intros x y.
  now apply paths_refl.
Qed.

Lemma isirrefl_reverse {X : UU} (l : hrel X) :
  isirrefl l → isirrefl (hrel_reverse l).
Proof.
  intros Hl x.
  now apply Hl.
Qed.
Lemma iscotrans_reverse {X : UU} (l : hrel X) :
  iscotrans l -> iscotrans (hrel_reverse l).
Proof.
  intros Hl x y z H.
  now apply islogeqcommhdisj, Hl.
Qed.

Lemma isStrongOrder_reverse {X : UU} (l : hrel X) :
  isStrongOrder l → isStrongOrder (hrel_reverse l).
Proof.
  intros H.
  repeat split.
  - apply istrans_reverse, (istrans_isStrongOrder H).
  - apply iscotrans_reverse,(iscotrans_isStrongOrder H).
  - apply isirrefl_reverse, (isirrefl_isStrongOrder H).
Qed.
Definition StrongOrder_reverse {X : UU} (l : StrongOrder X) :=
  make_StrongOrder (hrel_reverse l) (isStrongOrder_reverse l (pr2 l)).
Lemma StrongOrder_reverse_correct {X : UU} (l : StrongOrder X) :
  ∏ x y : X, StrongOrder_reverse l x y = l y x.
Proof.
  intros x y.
  now apply paths_refl.
Qed.

Lemma isasymm_reverse {X : UU} (l : hrel X) :
  isasymm l → isasymm (hrel_reverse l).
Proof.
  intros Hl x y.
  now apply Hl.
Qed.

Lemma iscoasymm_reverse {X : UU} (l : hrel X) :
  iscoasymm l → iscoasymm (hrel_reverse l).
Proof.
  intros Hl x y.
  now apply Hl.
Qed.

Lemma istotal_reverse {X : UU} (l : hrel X) :
  istotal l → istotal (hrel_reverse l).
Proof.
  intros Hl x y.
  now apply Hl.
Qed.
