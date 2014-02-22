Unset Automatic Introduction.

Inductive identity {X} (x:X) : X -> Type := 
  idpath : identity x x.

Notation "x == y" := (identity x y) (at level 70).

Definition iscontr X := { x:X & forall y, x == y }.

Definition fiber {X Y} (f:X->Y) (y:Y) := { x:X & f x == y }.

Definition isweq {X Y} (f:X->Y) := forall y, iscontr (fiber f y).

Definition isaprop X := forall (x y:X), iscontr (x == y). 

Definition isaset X := forall (x y:X), isaprop (x == y). 

Definition idfun X := fun (x:X) => x.

Lemma idfun_isweq X : isweq (idfun X).
Proof. intros.
       unfold isweq.
       intros.
       refine (existT _ _ _).
       - refine (existT _ y _).
         exact (idpath y).
       - intro p. 
         induction p as [x e]. 
         induction e. 
         exact (idpath _).
Qed.

Definition weq X Y := {f:X->Y & isweq f}.

Definition phi X Y : (X==Y) -> (weq X Y).
  intros X Y p.
  induction p.
  refine (existT _ (idfun X) _).
  exact (idfun_isweq X).
Defined.

Axiom univalence : forall X Y, isweq (phi X Y).
