Unset Automatic Introduction.

Inductive identity {X} (x:X) : X -> Type := 
  id : identity x x.

Notation "x == y" := (identity x y) (at level 70).

Definition iscontr X := { x:X & forall y, x == y }.

Definition fiber {X Y} (f:X->Y) (y:Y) := { x:X & f x == y }.

Definition isequiv {X Y} (f:X->Y) := forall y, iscontr (fiber f y).

Lemma idfun_isequiv X : isequiv (fun x:X => x).
Proof. intros.
       unfold isequiv.
       intros.
       unfold iscontr.
       refine (existT _ _ _).
       - unfold fiber.
         refine (existT _ _ _).
         + exact y.
         + exact (id y).
       - intro p. 
         induction p. 
         induction p. 
         exact (id _).
Qed.

Definition equiv X Y := { f:X->Y & isequiv f }.

Notation "X ~~ Y" := (equiv X Y) (at level 70).

Definition phi X Y : X==Y -> X~~Y.
  intros X Y p.
  induction p.
  refine (existT _ _ _).
  - exact (fun x:X => x).
  - exact (idfun_isequiv X).
Defined.

Axiom univalence : forall X Y, isequiv (phi X Y).
