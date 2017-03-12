Require Export UniMath.Foundations.PartB.
Require Export UniMath.Foundations.Resizing2.

(* this file is not compiled with type-in-type *)

Monomorphic Universe uu0.       (* lowest universe, larger than Set, from which all the propositions come *)

Local Set Printing Universes.

Section A.

  Universe i j.
  Constraint Set < i.
  Constraint i < j.

  Lemma B (X:Type@{i}) : X = ( X : Type@{j} ).
  Proof.
    reflexivity.
  Defined.

  Definition raise_element@{} : Type@{i} -> Type@{j}.
  (* adding @{} prevents additional universe parameters from being added to this definition *)
  Proof.
    intros T.
    exact T.
  Defined.

  Definition raise_universe_paths@{} {X : Type@{i}} {x y : X} : paths@{i} x y -> paths@{j} x y.
  Proof.
    intros p. try exact p. now induction p.
  Defined.

  Definition lower_universe_paths@{} {X : Type@{i}} {x y : X} : paths@{j} x y -> paths@{i} x y.
  Proof.
    intros p. try exact p. now induction p.
  Defined.

  Lemma change_universe_paths@{k} {X : Type@{i}} {x y : X} : weq@{k} (paths@{i} x y) (paths@{j} x y).
  Proof.
    simple refine (weqpair _ (gradth _ _ _ _)).
    - apply raise_universe_paths.
    - apply lower_universe_paths.
    - intros p. try exact p. now induction p.
    - intros p. try exact p. now induction p.
  Defined.

  Lemma raise_iscontr@{} (X : Type@{i}) : iscontr@{i} X -> iscontr@{j} X.
  Proof.
    intros ic. induction ic as [c e]. exists c. intro x. now induction (e x).
  Defined.

  Lemma lower_iscontr@{} (X : Type@{i}) : iscontr@{i} X <- iscontr@{j} X.
  Proof.
    intros ic. induction ic as [c e]. exists c. intro x. now induction (e x).
  Defined.

  Definition raise_universe_pairs@{} (X:Type@{i}) (P:X -> Type@{i}) :
    total2@{i} P -> total2@{j} P.
  Proof.
    intro w. try exact w. induction w as [x p]. exists x. exact p.
  Defined.

  Definition lower_universe_pairs@{} (X:Type@{i}) (P:X -> Type@{i}) :
    total2@{i} P <- total2@{j} P.
  Proof.
    intro w. try exact w. induction w as [x p]. exists x. exact p.
  Defined.

  Lemma change_universe_pairs@{k} (X:Type@{i}) (P:X -> Type@{i}) :
    weq@{k} (total2@{i} P) (total2@{j} P).
  Proof.
    simple refine (weqpair _ (gradth _ _ _ _)).
    - exact (raise_universe_pairs X P).
    - exact (lower_universe_pairs X P).
    - intro w. try reflexivity. now induction w as [x p].
    - intro w. try reflexivity. now induction w as [x p].
  Defined.

  Lemma change_universe_pr1@{} (X:Type@{i}) (P:X -> Type@{i}) (w :total2@{i} P) :
    pr1@{i} w = pr1@{j} (raise_universe_pairs X P w).
  Proof.
    try reflexivity. now induction w.
  Defined.

  Lemma change_universe_hfiber@{k} (X Y : Type@{i}) (f : X -> Y) (y : Y) :
    weq@{k} (hfiber@{i} f y) (hfiber@{j} f y).
  Proof.
    Unset Printing Notations.
    unfold hfiber.
    intermediate_weq (@total2@{j} X (fun x : X => @paths@{i} Y (f x) y)).
    - apply change_universe_pairs.
    - apply weqfibtototal; intro x. apply change_universe_paths.
    Set Printing Notations.
  Defined.

  Lemma lower_universe_isweq@{} {X Y : Type@{i}} (f : X -> Y) : isweq@{j} f -> isweq@{i} f.
  Proof.
    Unset Printing Notations.
    intros iw. try exact iw. intro y. assert (q := iw y); clear iw.
    simple refine (iscontrweqf _ q); clear q. apply invweq. apply change_universe_hfiber.
    Set Printing Notations.
  Defined.

  Lemma lower_universe_weq@{} (X Y : Type@{i}) : weq@{j} X Y -> weq@{i} X Y.
  Proof.
    intro w. try exact w. exists (pr1 w). apply lower_universe_isweq. exact (pr2 w).
  Defined.

  Lemma raise_universe_isweq@{} {X Y : Type@{i}} (f : X -> Y) : isweq@{i} f -> isweq@{j} f.
  Proof.
    intros iw. try exact iw. intro y. assert (q := iw y); clear iw.
    simple refine (iscontrweqf _ q); clear q. apply invweq.
    intermediate_weq (@total2@{j} X (fun x : X => @paths@{i} Y (f x) y)).
    - apply weqfibtototal; intro x. apply invweq, change_universe_paths.
    - unfold hfiber. apply invweq, change_universe_pairs.
  Defined.

  Lemma raise_universe_weq@{} (X Y : Type@{i}) : weq@{i} X Y -> weq@{j} X Y.
  Proof.
    intro w. try exact w. exists (pr1 w). apply raise_universe_isweq. exact (pr2 w).
  Defined.

  Lemma raise_universe_isofhlevel@{} (n:nat) (X : Type@{i}) : isofhlevel@{i} n X -> isofhlevel@{j} n X.
  (* Declaring n in nat explicitly prevents errors like "Error: Universe {Top.205} is unbound." Coq bug? *)
  Proof.
    generalize X; clear X.
    induction n as [|n IH].
    - apply raise_iscontr.
    - intros X hl x y. assert (hl' := hl x y : isofhlevel@{i} n (x = y)); clear hl.
      simple refine (@isofhlevelweqf n _ _ _ hl').
      apply change_universe_paths.
  Defined.

  Lemma lower_universe_isofhlevel@{} (n:nat) (X : Type@{i}) : isofhlevel@{j} n X -> isofhlevel@{i} n X.
  Proof.
    generalize X; clear X.
    induction n as [|n IH].
    - apply lower_iscontr.
    - intros X hl x y. assert (hl' := hl x y : isofhlevel@{j} n (x = y)); clear hl.
      apply IH. simple refine (@isofhlevelweqf n _ _ _ hl').
      apply invweq, change_universe_paths.
  Defined.

  Goal ∏ (X:Type@{j}) (ip:isaprop@{j} X), ResizeProp@{i j} X ip = X.
  (* illustrate that [ResizeProp T ip] and [T] are judgmentally equal *)
  Proof.
    intros. reflexivity.
  Defined.

  Goal ∏ (S : Type@{i}) (T : Type@{j}) (w : weq@{j} S T), ResizeType@{i j} T w = T.
  (* illustrate that [ResizeType T w] and [T] are judgmentally equal *)
  Proof.
    intros. reflexivity.
  Defined.

  (* Lemma isofhlevel_resize@{} (n:nat) (X:Type@{j}) (ip : isaprop@{j} X) : *)
  (*   isofhlevel@{j} n X -> isofhlevel@{i} n (ResizeProp@{i j} X ip). *)
  (* Proof. *)
  (*   intros hl. apply lower_universe_isofhlevel. exact hl. *)
  (* Defined. *)

End A.

Section B.

  Universes i j k.
  Constraint i < j.
  Constraint j < k.

  Lemma A (X:Type@{i}) (P:X -> Type@{i}) : paths@{k} (total2@{i} P) (total2@{j} P).
  Proof.
    try reflexivity.          (* get Coq to do this? *)
  Abort.

End B.
