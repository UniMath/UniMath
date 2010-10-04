Definition dp := 
 fun (A B:Set)(x:A)(y:B)(f:forall C:Set, C->C) => (f A x, f B y).

Check dp.