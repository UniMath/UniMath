Unset Automatic Introduction.
Require Import Foundations.hlevel2.hSet.
Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).
Notation "p @ q" := (pathscomp0 p q) (at level 60, right associativity).

Definition sections {T:UU} (P:T->UU) := forall t:T, P t.
Definition etaExpand {T:UU} (P:T->UU) (f:sections P) := fun t => f t.

Parameter  A : UU.
Parameter  B : A->UU.
Parameter  C : sections B -> UU.
Definition C' : sections B -> UU := fun g => C (etaExpand _ g).

Definition V  := total2 C.
Definition V' := total2 C'.

Goal (fun g => C' (etaExpand B g)) == C'.
  unfold C', etaExpand, sections. (* we see that it's actually a definitional equality *)
  apply idpath.
Defined.

Definition etaExpandE : V' -> V'.
  intros [g h].
  exists (fun x => g x).
  exact  h.
Defined.

Lemma pair_path {X:UU} {P:X->UU} {x x':X} {p: P x} {p' : P x'} 
      (e : x == x') (e' : transportf _ e p == p') : 
  tpair _ x p == tpair _ x' p'.
  (* compare with functtransportf in uu0.v *)
Proof. intros. destruct e. destruct e'. apply idpath. Defined.

Lemma pair_path_pr1 {X:UU} {P:X->UU} {xp xp' : total2 P} (h : xp == xp') : pr1 xp == pr1 xp'.
Proof. intros. apply (maponpaths pr1 h). Defined.

Lemma pair_path_pr2 {X:UU} {P:X->UU} {xp xp' : total2 P} (h : xp == xp') : transportf P (pair_path_pr1 h) (pr2 xp) == pr2 xp'.
Proof. intros. destruct h. apply idpath. Defined.

Module Attempt1.

  Lemma foo1 : forall v, etaExpandE v == v.
  Proof.
    intros [g h].    
    apply (pair_path (!etacorrection _ _ g)).
    (* now we're stuck with a transport over an eta correction path *)
  Abort.

End Attempt1.

Module Attempt2.

  Lemma foo1 : forall v, etaExpandE v == v.
  Proof.
    intros [g h].    
    unfold etaExpandE, etaExpand.
    destruct (!etacorrection _ _ g). (* the goal is unaffected *)
  Abort.

End Attempt2.

Module Attempt3.

  Definition fpmaphomotfun {X: UU} {P Q: X -> UU} : (homot P Q) -> total2 P -> total2 Q.
  Proof. intros ? ? ? h [x p]. exists x. destruct (h x). exact p. Defined.

  Definition homot2 {X Y:UU} {f g:X->Y} (p q:homot f g) := forall x, p x == q x.

  Definition fpmaphomothomot {X: UU} {P Q: X -> UU} (h1 h2: homot P Q) : 
    homot2 h1 h2 -> homot (fpmaphomotfun h1) (fpmaphomotfun h2).
  Proof. intros ? ? ? ? ? H [x p]. apply (maponpaths (tpair _ x)). destruct (H x). apply idpath. Defined.

  Definition h1 : homot C' (fun f => C' (etaExpand B f)).
    intro f.
    unfold C', etaExpand.         (* we see it's actually a definitional equality *)
    apply idpath.
  Defined.

  Definition h2 : homot C' (fun f => C' (etaExpand B f)).
    intro f.
    apply (maponpaths C' (etacorrection _ _ f)).
  Defined.

  Lemma H : homot2 h1 h2.
  Proof.
    intro f.
    unfold h1, h2, C'.
    (* we're stuck, because we need a computation rule for etaExpand *)
    admit.                      (* so we assume it *)
  Defined.

  (* let's see why the computation rule would have helped *)

  Lemma foo1 : forall v, etaExpandE v == v.
  Proof.
    set (z := fpmaphomothomot h1 h2 H).

  Abort.

End Attempt3.

Module Attempt4.

  Lemma foo1 : forall v, etaExpandE v == v.
  Proof.
    intros [g h].    
    unfold etaExpandE, etaExpand.
    revert h. destruct (!etacorrection _ _ g). (* this avoids transport *)
    intro h.
    apply idpath.
  Defined.                        (* success! *)

  Lemma asdf : forall v:V', etaExpand _ (pr1 v) == pr1 (etaExpandE v).
  Proof.                        (* not a definitional equality *)
    intros [g h]. apply idpath. 
  Defined.

  Lemma transport_along_eta (g:sections B) (h:C' g) : transportf C' (!etacorrection A B g) h == h.
  Proof.
    intros.
    set (v := tpair C' g h).
    set (p := etaExpandE v).
    unfold etaExpandE, v in p.
    set (q := pair_path_pr2 (!pair_path (!etacorrection A B g) (idpath (transportf C' (!etacorrection A B g) h))
            @
          (foo1 v)
          )).
    unfold v, pr2 in q; simpl.
    Check (q).
  (* it should be possible to complete this proof *)
  Abort.

End Attempt4.
