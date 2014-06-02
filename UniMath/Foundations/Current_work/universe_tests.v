(* *)

Set Printing Universes.

Definition U1 := Type.
Definition U2 : U1 := Type.

Print U1.
Print U2.

Variable A : U2.

Definition test1 := A -> A . 
Print test1.
Definition test11 := ( A : U1 ) -> A . 
Print test11.

Definition test2 := identity_refl test11 : identity test1 test11.
Set Printing Implicit.  
Print test2.


(* End of the ile universe_tests.v *)