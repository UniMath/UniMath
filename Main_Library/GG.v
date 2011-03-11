Require Arith.
Require Export u0.


Set Print Universes.

Inductive pathsu (T:Type): T -> T -> UU := idpathu:  forall t:T, pathsu _ t t. 

Print pathsu.


(*Definition UU:=Type.*)

Definition UU := Type .

Variable T : UU .

Record T2 : UU := T2pair { p1 : T ; p2 : T }.

Print T2.

Definition UU' := Type .

Record UUBB : UU' := UUBBpair { TT : UU ; tt : TT } .

Print UUBB.

Variable b: pathsu _ UU UU.

Check pathsu.

Check (pathsu _ t t).

Check (idpathu _ UU).

Variable c: (f ( pathsu _ UU UU)).







Inductive reflect (P:Prop) : bool -> Type := | RT: P -> reflect P true | RF: ~P -> reflect P false.

Fixpoint rflt (P:Prop)(b:bool) : Type := match b with true => P | false => ~P end.

Lemma l2a (P:Prop)(b:bool): reflect P b -> rflt P b.
Proof. intros. case H.  simpl. trivial. simpl. trivial. Defined.

Lemma l2b (P:Prop)(b:bool): rflt P b -> reflect P b.
Proof. intros. destruct b.  simpl in X.  apply (RT P X). simpl in X. apply (RF P X). Defined. 


(*Inductive acc_nat (P: nat -> bool)(i:nat) : Prop := AccNat0:  (P i=true) -> acc_nat P i | AccNatS : acc_nat P (S i) -> acc_nat P i.

Check acc_nat.*)



Section about_exists.

Variable T:Type.
Variable P: T -> Prop.


Definition isinh (X:Type) := forall Q:Prop, ((X ->Q)->Q).
Definition isinhpr (X:Type) := (fun x:X => fun P:Prop => fun f:_ => f x) : X -> isinh X.

Check isinh.

Definition existspr: {t:T | P t} -> exists t:T, P t.
Proof. intro. destruct X. apply (ex_intro (fun y => P y) x p).  Defined. 


Theorem two_definitions_are_equivalent: (isinh {t:T | P t}) <-> exists t:T, P t.
Proof. intros. split.
assert (s1: isinh {t:T | P t} -> (exists t:T, P t)). intro.  apply (H (exists t:T, P t) existspr). assumption. 
intro.  destruct H. apply (isinhpr {t:T | P t} (existT (fun y:T => P y) x H)). Defined. 

End about_exists.




Section ExMinn.
 
Variable P : nat -> bool.
Hypothesis exP : exists n, P n = true.



 
Inductive acc_nat (i:nat) : Prop := AccNat0: (P i = true) -> acc_nat i | AccNatS: acc_nat (S i) -> acc_nat i.
 
Definition dec_le m n := m - n = 0.
 
Lemma lt_neq_and_le : forall m n, m <> n -> dec_le m n -> dec_le (S m) n.
Proof.
induction m; destruct n; intros m_neq_n m_le_n.
  case m_neq_n; split.
  split.
  discriminate.
apply IHm; [intros m_eq_n | assumption].
case m_neq_n; rewrite m_eq_n; split.
Qed.




Lemma find_ex_minn : {m | P m = true & forall n, P n = true -> dec_le m n}.
Proof.
pose (lb m := forall n, P n = true -> dec_le m n).
set (goal := {m : nat | P m = true & lb m}); change goal.
assert (lb_0 : lb 0) by split.
assert (acc0 : acc_nat 0).
 case exP; intros n; rewrite <- (Plus.plus_0_r n); generalize 0.
 induction n; [left; trivial | intros j].
 rewrite -> plus_Sn_m, plus_n_Sm; right; apply IHn; assumption.
assert (atPm : forall m, P m = true -> lb m -> goal).
 intros m Pm lb_m; exists m; assumption.
assert (not_Pm_and_notPm : forall m, P m = false -> P m <> true).
 intros m notPm; rewrite notPm; discriminate.
assert (notPm_lb_Sm : forall m, P m = false -> lb m -> lb (S m)).
 intros m notPm lb_m n Pn.
 apply lt_neq_and_le; [intro m_eq_n | exact (lb_m n Pn)].
 rewrite <- m_eq_n in Pn; exact (not_Pm_and_notPm m notPm Pn).
exact (
 let fix loop m lb_m acc_m {struct acc_m} :=
   match P m as b return P m = b -> goal with
   | true => fun Pm => atPm m Pm lb_m
   | false => fun notPm =>
       loop (S m) (notPm_lb_Sm m notPm lb_m)
         (match acc_m with
          | AccNat0 Pm => match not_Pm_and_notPm m notPm Pm with end
          | AccNatS acc_Sm => acc_Sm
          end)
   end (refl_equal (P m)) in
 loop 0 lb_0 acc0).
Qed.








Lemma find_ex_minn_2 : {m | P m = true & forall n, P n = true -> dec_le m n}.
Proof.
pose (lb m := forall n, P n = true -> dec_le m n).
set (goal := {m : nat | P m = true & lb m}); change goal.
assert (lb_0 : lb 0) by split.
assert (acc0 : acc_nat 0).
 case exP; intros n; rewrite <- (Plus.plus_0_r n); generalize 0.
 induction n; [left; trivial | intros j].
 rewrite -> plus_Sn_m, plus_n_Sm; right; apply IHn; assumption.
assert (atPm : forall m, P m = true -> lb m -> goal).
 intros m Pm lb_m; exists m; assumption.
assert (not_Pm_and_notPm : forall m, P m = false -> P m <> true).
 intros m notPm; rewrite notPm; discriminate.
assert (notPm_lb_Sm : forall m, P m = false -> lb m -> lb (S m)).
 intros m notPm lb_m n Pn.
 apply lt_neq_and_le; [intro m_eq_n | exact (lb_m n Pn)].
 rewrite <- m_eq_n in Pn; exact (not_Pm_and_notPm m notPm Pn).

Set Print All. 

set (main_fun:=
 (fix loop m lb_m acc_m {struct acc_m} :=
   match P m as b return P m = b -> goal with
   | true => fun Pm => atPm m Pm lb_m
   | false => fun notPm =>
       loop (S m) (notPm_lb_Sm m notPm lb_m)
         (match acc_m with
          | AccNat0 Pm => match not_Pm_and_notPm m notPm Pm with end
          | AccNatS acc_Sm => acc_Sm
          end)
   end (refl_equal (P m)))).

set (q1:= fun m:nat => refl_equal (P m)).

apply (main_fun    0 lb_0 acc0 ).

QED.






 
Lemma find_ex_minn : {m | P m = true & forall n, P n = true -> dec_le m n}.
Proof.
assert (min0 : forall n, P n = true -> dec_le 0 n). split. revert min0.

(* assert (acc0 : acc_nat 0); [ | revert acc0].
  case exP; intros n; rewrite <- (Plus.plus_0_r n); generalize 0.
  induction n; [left; trivial | intros j].
  rewrite -> plus_Sn_m, plus_n_Sm; right; apply IHn; assumption. *)

assert (s1: forall n:nat, acc_nat n -> nat). intro. intro.  case (P n).   intro.  induction H. 

assert (acc0 : acc_nat 0). induction exP.
assert (acc_nat x -> acc_nat 0). clear H. induction x. trivial. intro.  apply (IHx (AccNatS _ H)).
apply (H0 (AccNat0 _ H)). generalize acc0.

generalize 0. fix 2. intros m IHm m_lb.
case_eq (P m). intros Pm. exists m. assumption. assumption.  intro. 
apply (find_ex_minn (S m)). clear find_ex_minn. [|intros n Pn].
  case IHm. [rewrite Pm. intros. discriminate | trivial].
apply lt_neq_and_le. [intro m_eq_n | exact (m_lb n Pn)].
rewrite -> m_eq_n, Pn in Pm. discriminate.
Qed.
 Set Printing All.
Print find_ex_minn.


End ExMinn.
 
(*
Variable P : pred nat.
Hypothesis exP : exists n, P n.
 
Inductive acc_nat i : Prop := AccNat0 of P i | AccNatS of acc_nat i.+1.
 
Lemma find_ex_minn : {m | P m & forall n, P n -> m <= n}.
Proof.
have: forall n, P n -> n >= 0 by [].
have: acc_nat 0.
  case exP => n; rewrite -(addn0 n); elim: n 0 => [|n IHn] j; first by left.
  rewrite addSnnS; right; exact: IHn.
move: 0; fix 2 => m IHm m_lb; case Pm: (P m); first by exists m.
apply: find_ex_minn m.+1 _ _ => [|n Pn]; first by case: IHm; rewrite ?Pm.
by rewrite ltn_neqAle m_lb //; case: eqP Pm => // ->; case/idP.
Qed.
*)






Variable P:Prop. 
Variable Q:Prop.

Lemma l1: reflect P true -> P.
Proof.  intro.  change (if true then P else True).  case H. auto. auto.  Defined.