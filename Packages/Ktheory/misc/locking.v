(* from Jason Gross *)

Definition key : unit. exact tt. Qed.
Definition locked A (x:A) : A := match key with tt => x end.
Lemma unlock A x : x = locked A x.
  unfold locked. destruct key. reflexivity.
Defined.
Record total {T} ( P: T -> Type ) := tpair { pr1 : T; pr2 : P pr1 }.
Definition morfun (o:Type) := o -> o -> Type.
Definition category := total morfun.
Definition make_cat := tpair _ morfun.
Parameter o : Type.
Parameter m m' : o -> o -> Type.
Definition C := make_cat o m.
Definition C':= make_cat o m'.
Parameter x : o.
Definition ob (C:category) := pr1 _ C.
Check x : ob C.
Check x : ob C'.
Definition iso {C:category} (a b:ob C) := unit.
Definition funny (a:ob C) (b:ob C') := iso a b.
Definition ob' : category -> Type := 
  locked (category -> Type) (fun C : category => ob C).
Definition iso' {C:category} (a b:ob' C) := unit.
(* Definition funny' (a:ob' C) (b:ob' C') := iso' a b. (* <-- fails, good *) *)
Definition open {C} : ob' C -> ob C.
  unfold ob',locked. destruct key. exact (fun c => c).
Defined.
Definition close {C} : ob C -> ob' C.
  unfold ob',locked. destruct key. exact (fun c => c).
Defined.
Definition iso2' {C:category} (a b:ob' C) := iso (open a) (open b).
