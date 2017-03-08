
Print Grammar constr.


Notation "X ⨿ Y" := (X + Y) (at level 50, left associativity) : A.



Definition UU := Type.
Definition type_of (X:Type) (x:X) : Type := X.
Definition UU' := type_of _ UU.
Set Printing Universes.
Print UU.                       (* Top.1 *)
Print UU'.                      (* Top.4 *)
Print Universes.
Definition f (T:UU') := unit.
Definition a := f UU.
Print Universes.
