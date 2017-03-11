Require Export UniMath.Foundations.PartB.
Require Export UniMath.Foundations.Resizing2.

(* this file is not compiled with type-in-type *)

Section A.

  Universe i j.
  Constraint Set < i.
  Constraint i < j.

  Lemma B (X:Type@{i}) : X = ( X : Type@{j} ).
  Proof.
    reflexivity.
  Defined.

  Definition raise_element : Type@{i} -> Type@{j}.
  Proof.
    intros T.
    exact T.
  Defined.

  Lemma change_universe_paths {X : Type@{i}} {x y : X} : weq@{j} (paths@{i} x y) (paths@{j} x y).
  Proof.
    simple refine (weqpair _ (gradth _ _ _ _)).
    - intros p. try exact p. now induction p.
    - intros p. try exact p. now induction p.
    - intros p. try exact p. now induction p.
    - intros p. try exact p. now induction p.
  Defined.

  Definition raise_paths {X : Type@{i}} {x y : X} : paths@{i} x y -> paths@{j} x y
    := pr1weq change_universe_paths.

  Definition lower_paths {X : Type@{i}} {x y : X} : paths@{j} x y -> paths@{i} x y
    := invmap change_universe_paths.

  Lemma raise_iscontr (X : Type@{i}) : iscontr@{i} X -> iscontr@{j} X.
  Proof.
    intros ic. induction ic as [c e]. exists c. intro x. now induction (e x).
  Defined.

  Lemma lower_iscontr (X : Type@{i}) : iscontr@{i} X <- iscontr@{j} X.
  Proof.
    intros ic. induction ic as [c e]. exists c. intro x. now induction (e x).
  Defined.

  Lemma change_universe_pairs (X:Type@{i}) (P:X -> Type@{i}) :
    weq@{j} (total2@{i} P) (total2@{j} P).
  Proof.
    simple refine (weqpair _ (gradth _ _ _ _)).
    - intro w. try exact w. induction w as [x p]. exists x. exact p.
    - intro w. try exact w. induction w as [x p]. exists x. exact p.
    - intro w. try reflexivity. induction w as [x p]. reflexivity.
    - intro w. try reflexivity. induction w as [x p]. reflexivity.
  Defined.

  Lemma lower_universe_isweq {X Y : Type@{i}} (f : X -> Y) : isweq@{j} f -> isweq@{i} f.
  Proof.
    intros iw. try exact iw. intro y. assert (q := iw y); clear iw.
    simple refine (iscontrweqf _ q); clear q. apply invweq.
    intermediate_weq (@total2@{j} X (fun x : X => @paths@{i} Y (f x) y)).
    - apply change_universe_pairs.
    - apply weqfibtototal; intro x. apply change_universe_paths.
  Defined.

  Lemma lower_universe_weq (X Y : Type@{i}) : weq@{j} X Y -> weq@{i} X Y.
  Proof.
    intro w. try exact w. exists (pr1 w). apply lower_universe_isweq. exact (pr2 w).
  Defined.

  Lemma raise_universe_isweq {X Y : Type@{i}} (f : X -> Y) : isweq@{i} f -> isweq@{j} f.
  Proof.
    intros iw. try exact iw. intro y. assert (q := iw y); clear iw.
    simple refine (iscontrweqf _ q); clear q. apply invweq.
    intermediate_weq (@total2@{j} X (fun x : X => @paths@{i} Y (f x) y)).
    - apply weqfibtototal; intro x. apply invweq, change_universe_paths.
    - unfold hfiber. apply invweq, change_universe_pairs.
  Defined.

  Lemma raise_universe_weq (X Y : Type@{i}) : weq@{i} X Y -> weq@{j} X Y.
  Proof.
    intro w. try exact w. exists (pr1 w). apply raise_universe_isweq. exact (pr2 w).
  Defined.

  Lemma raise_universe_isofhlevel n (X : Type@{i}) : isofhlevel@{i} n X -> isofhlevel@{j} n X.
  Proof.
    generalize X; clear X.
    induction n as [|n IH].
    - apply raise_iscontr.
    - intros X hl x y. assert (hl' := hl x y : isofhlevel@{i} n (x = y)); clear hl.
      simple refine (@isofhlevelweqf n _ _ _ hl').
      apply change_universe_paths.
  Defined.

  Lemma lower_universe_isofhlevel n (X : Type@{i}) : isofhlevel@{j} n X -> isofhlevel@{i} n X.
  Proof.
    generalize X; clear X.
    induction n as [|n IH].
    - apply lower_iscontr.
    - intros X hl x y. assert (hl' := hl x y : isofhlevel@{j} n (x = y)); clear hl.
      apply IH. simple refine (@isofhlevelweqf n _ _ _ hl').
      apply invweq, change_universe_paths.
  Defined.

  Lemma ResizeProp_weq {X:Type@{j}} (ip:isaprop@{j} X): weq@{j} X (ResizeProp@{i j} X ip).
  Proof.
    simple refine (weqpair _ (gradth _ _ _ _)).
    - intros x. exact x.
    - intros x. exact x.
    - reflexivity.
    - reflexivity.
  Defined.

  Lemma ResizeType_weq {S : Type@{i}} (T : Type@{j}) (w : weq@{j} S T) :
    weq@{j} T (ResizeType@{i j} T w).
  Proof.
    simple refine (weqpair _ (gradth _ _ _ _)).
    - intros x. exact x.
    - intros x. exact x.
    - reflexivity.
    - reflexivity.
  Defined.

  Lemma isofhlevel_resize@{i j} n (X:Type@{j}) (ip : isaprop@{j} X) :
    isofhlevel@{j} n X -> isofhlevel@{i} n (ResizeProp@{i j} X ip).
  Proof.
    intros hl.
    set (q := isofhlevelweqf@{j j} n (ResizeProp_weq ip) hl).
    apply lower_universe_isofhlevel.
    exact q.
  Defined.

End A.
