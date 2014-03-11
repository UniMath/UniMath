Class EqDec (A : Type) := 
  {
    eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, eqb x y = true -> x = y }.
Instance unit_EqDec : EqDec unit :=
  {
    eqb x y := true ;
    eqb_leibniz x y H :=
      match x, y return x = y with tt, tt => eq_refl tt end }.
Instance eq_bool : EqDec bool := { eqb x y := if x then y else negb y }.
Proof. intros x y H.
       destruct x ; destruct y ; (discriminate || reflexivity).
Defined.
Definition neqb {A} {eqa : EqDec A} (x y : A) := negb (eqb x y).

