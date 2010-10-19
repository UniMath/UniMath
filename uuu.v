
Definition UUU:=Type. 


Inductive empty:UUU := .
Inductive unit:UUU := tt:unit.
Inductive bool:UUU := true:bool | false:bool.
Inductive nat:UUU := O:nat | S: nat -> nat.


