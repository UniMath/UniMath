Unset Automatic Introduction.

Inductive identity {X} (x:X) : X -> Type := 
  idpath : identity x x.

Notation "x == y" := (identity x y) (at level 70).

Definition iscontr X := { x:X & forall y, x == y }.

Definition fiber {X Y} (f:X->Y) (y:Y) := { x:X & f x == y }.

Definition isweq {X Y} (f:X->Y) := forall y, iscontr (fiber f y).

Definition idfun X (x:X) := x.

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

Definition weq X Y := { f:X->Y & isweq f }.

Notation "X -~- Y" := (weq X Y) (at level 70).

Definition phi X Y : X==Y -> X-~-Y.
  intros X Y p.
  induction p.
  refine (existT _ _ _).
  - exact (idfun X).
  - exact (idfun_isweq X).
Defined.

Axiom univalence : forall X Y, isweq (phi X Y).
