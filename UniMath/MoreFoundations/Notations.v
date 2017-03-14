(** * Notations  *)

Require Export UniMath.MoreFoundations.Foundations.

Delimit Scope type_scope with type.

Reserved Notation "A ⇒ B" (at level 95, no associativity).
(* to input: type "\Rightarrow" or "\r=" or "\r" or "\Longrightarrow" or "\=>" with
             Agda input method *)

Notation "A ⇒ B" := (himpl A B) : logic.

Local Open Scope logic.

Definition hequiv (P Q:hProp) : hProp := (P ⇒ Q) ∧ (Q ⇒ P).

Notation "A ⇔ B" := (hequiv A B) (at level 95, no associativity) : logic.

Definition total2_hProp {X : hProp} (Y : X -> hProp) : hProp
  := hProppair (∑ x, Y x) (isaprop_total2 X Y).

Delimit Scope prop with prop.

Notation "'∑' x .. y , P" := (total2_hProp (fun x =>.. (total2_hProp (fun y => P))..))
  (at level 200, x binder, y binder, right associativity) : prop.
  (* type this in emacs in agda-input method with \sum *)

Notation "'pr11' x" := (pr1 (pr1 x)) (at level 8).
Notation "'pr12' x" := (pr1 (pr2 x)) (at level 8).
Notation "'pr21' x" := (pr2 (pr1 x)) (at level 8).
Notation "'pr22' x" := (pr2 (pr2 x)) (at level 8).

Notation "'pr111' x" := (pr1 (pr1 (pr1 x))) (at level 8).
Notation "'pr112' x" := (pr1 (pr1 (pr2 x))) (at level 8).
Notation "'pr121' x" := (pr1 (pr2 (pr1 x))) (at level 8).
Notation "'pr122' x" := (pr1 (pr2 (pr2 x))) (at level 8).
Notation "'pr211' x" := (pr2 (pr1 (pr1 x))) (at level 8).
Notation "'pr212' x" := (pr2 (pr1 (pr2 x))) (at level 8).
Notation "'pr221' x" := (pr2 (pr2 (pr1 x))) (at level 8).
Notation "'pr222' x" := (pr2 (pr2 (pr2 x))) (at level 8).

Notation "'pr1111' x" := (pr1 (pr1 (pr1 (pr1 x)))) (at level 8).
Notation "'pr1112' x" := (pr1 (pr1 (pr1 (pr2 x)))) (at level 8).
Notation "'pr1121' x" := (pr1 (pr1 (pr2 (pr1 x)))) (at level 8).
Notation "'pr1122' x" := (pr1 (pr1 (pr2 (pr2 x)))) (at level 8).
Notation "'pr1211' x" := (pr1 (pr2 (pr1 (pr1 x)))) (at level 8).
Notation "'pr1212' x" := (pr1 (pr2 (pr1 (pr2 x)))) (at level 8).
Notation "'pr1221' x" := (pr1 (pr2 (pr2 (pr1 x)))) (at level 8).
Notation "'pr1222' x" := (pr1 (pr2 (pr2 (pr2 x)))) (at level 8).
Notation "'pr2111' x" := (pr2 (pr1 (pr1 (pr1 x)))) (at level 8).
Notation "'pr2112' x" := (pr2 (pr1 (pr1 (pr2 x)))) (at level 8).
Notation "'pr2121' x" := (pr2 (pr1 (pr2 (pr1 x)))) (at level 8).
Notation "'pr2122' x" := (pr2 (pr1 (pr2 (pr2 x)))) (at level 8).
Notation "'pr2211' x" := (pr2 (pr2 (pr1 (pr1 x)))) (at level 8).
Notation "'pr2212' x" := (pr2 (pr2 (pr1 (pr2 x)))) (at level 8).
Notation "'pr2221' x" := (pr2 (pr2 (pr2 (pr1 x)))) (at level 8).
Notation "'pr2222' x" := (pr2 (pr2 (pr2 (pr2 x)))) (at level 8).

Notation "'pr11111' x" := (pr1 (pr1 (pr1 (pr1 (pr1 x))))) (at level 8).
Notation "'pr11112' x" := (pr1 (pr1 (pr1 (pr1 (pr2 x))))) (at level 8).
Notation "'pr11121' x" := (pr1 (pr1 (pr1 (pr2 (pr1 x))))) (at level 8).
Notation "'pr11122' x" := (pr1 (pr1 (pr1 (pr2 (pr2 x))))) (at level 8).
Notation "'pr11211' x" := (pr1 (pr1 (pr2 (pr1 (pr1 x))))) (at level 8).
Notation "'pr11212' x" := (pr1 (pr1 (pr2 (pr1 (pr2 x))))) (at level 8).
Notation "'pr11221' x" := (pr1 (pr1 (pr2 (pr2 (pr1 x))))) (at level 8).
Notation "'pr11222' x" := (pr1 (pr1 (pr2 (pr2 (pr2 x))))) (at level 8).
Notation "'pr12111' x" := (pr1 (pr2 (pr1 (pr1 (pr1 x))))) (at level 8).
Notation "'pr12112' x" := (pr1 (pr2 (pr1 (pr1 (pr2 x))))) (at level 8).
Notation "'pr12121' x" := (pr1 (pr2 (pr1 (pr2 (pr1 x))))) (at level 8).
Notation "'pr12122' x" := (pr1 (pr2 (pr1 (pr2 (pr2 x))))) (at level 8).
Notation "'pr12211' x" := (pr1 (pr2 (pr2 (pr1 (pr1 x))))) (at level 8).
Notation "'pr12212' x" := (pr1 (pr2 (pr2 (pr1 (pr2 x))))) (at level 8).
Notation "'pr12221' x" := (pr1 (pr2 (pr2 (pr2 (pr1 x))))) (at level 8).
Notation "'pr12222' x" := (pr1 (pr2 (pr2 (pr2 (pr2 x))))) (at level 8).
Notation "'pr21111' x" := (pr2 (pr1 (pr1 (pr1 (pr1 x))))) (at level 8).
Notation "'pr21112' x" := (pr2 (pr1 (pr1 (pr1 (pr2 x))))) (at level 8).
Notation "'pr21121' x" := (pr2 (pr1 (pr1 (pr2 (pr1 x))))) (at level 8).
Notation "'pr21122' x" := (pr2 (pr1 (pr1 (pr2 (pr2 x))))) (at level 8).
Notation "'pr21211' x" := (pr2 (pr1 (pr2 (pr1 (pr1 x))))) (at level 8).
Notation "'pr21212' x" := (pr2 (pr1 (pr2 (pr1 (pr2 x))))) (at level 8).
Notation "'pr21221' x" := (pr2 (pr1 (pr2 (pr2 (pr1 x))))) (at level 8).
Notation "'pr21222' x" := (pr2 (pr1 (pr2 (pr2 (pr2 x))))) (at level 8).
Notation "'pr22111' x" := (pr2 (pr2 (pr1 (pr1 (pr1 x))))) (at level 8).
Notation "'pr22112' x" := (pr2 (pr2 (pr1 (pr1 (pr2 x))))) (at level 8).
Notation "'pr22121' x" := (pr2 (pr2 (pr1 (pr2 (pr1 x))))) (at level 8).
Notation "'pr22122' x" := (pr2 (pr2 (pr1 (pr2 (pr2 x))))) (at level 8).
Notation "'pr22211' x" := (pr2 (pr2 (pr2 (pr1 (pr1 x))))) (at level 8).
Notation "'pr22212' x" := (pr2 (pr2 (pr2 (pr1 (pr2 x))))) (at level 8).
Notation "'pr22221' x" := (pr2 (pr2 (pr2 (pr2 (pr1 x))))) (at level 8).
Notation "'pr22222' x" := (pr2 (pr2 (pr2 (pr2 (pr2 x))))) (at level 8).

Notation "'pr111111' x" := (pr1 (pr1 (pr1 (pr1 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr111112' x" := (pr1 (pr1 (pr1 (pr1 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr111121' x" := (pr1 (pr1 (pr1 (pr1 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr111122' x" := (pr1 (pr1 (pr1 (pr1 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr111211' x" := (pr1 (pr1 (pr1 (pr2 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr111212' x" := (pr1 (pr1 (pr1 (pr2 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr111221' x" := (pr1 (pr1 (pr1 (pr2 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr111222' x" := (pr1 (pr1 (pr1 (pr2 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr112111' x" := (pr1 (pr1 (pr2 (pr1 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr112112' x" := (pr1 (pr1 (pr2 (pr1 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr112121' x" := (pr1 (pr1 (pr2 (pr1 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr112122' x" := (pr1 (pr1 (pr2 (pr1 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr112211' x" := (pr1 (pr1 (pr2 (pr2 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr112212' x" := (pr1 (pr1 (pr2 (pr2 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr112221' x" := (pr1 (pr1 (pr2 (pr2 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr112222' x" := (pr1 (pr1 (pr2 (pr2 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr121111' x" := (pr1 (pr2 (pr1 (pr1 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr121112' x" := (pr1 (pr2 (pr1 (pr1 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr121121' x" := (pr1 (pr2 (pr1 (pr1 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr121122' x" := (pr1 (pr2 (pr1 (pr1 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr121211' x" := (pr1 (pr2 (pr1 (pr2 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr121212' x" := (pr1 (pr2 (pr1 (pr2 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr121221' x" := (pr1 (pr2 (pr1 (pr2 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr121222' x" := (pr1 (pr2 (pr1 (pr2 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr122111' x" := (pr1 (pr2 (pr2 (pr1 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr122112' x" := (pr1 (pr2 (pr2 (pr1 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr122121' x" := (pr1 (pr2 (pr2 (pr1 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr122122' x" := (pr1 (pr2 (pr2 (pr1 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr122211' x" := (pr1 (pr2 (pr2 (pr2 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr122212' x" := (pr1 (pr2 (pr2 (pr2 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr122221' x" := (pr1 (pr2 (pr2 (pr2 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr122222' x" := (pr1 (pr2 (pr2 (pr2 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr211111' x" := (pr2 (pr1 (pr1 (pr1 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr211112' x" := (pr2 (pr1 (pr1 (pr1 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr211121' x" := (pr2 (pr1 (pr1 (pr1 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr211122' x" := (pr2 (pr1 (pr1 (pr1 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr211211' x" := (pr2 (pr1 (pr1 (pr2 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr211212' x" := (pr2 (pr1 (pr1 (pr2 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr211221' x" := (pr2 (pr1 (pr1 (pr2 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr211222' x" := (pr2 (pr1 (pr1 (pr2 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr212111' x" := (pr2 (pr1 (pr2 (pr1 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr212112' x" := (pr2 (pr1 (pr2 (pr1 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr212121' x" := (pr2 (pr1 (pr2 (pr1 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr212122' x" := (pr2 (pr1 (pr2 (pr1 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr212211' x" := (pr2 (pr1 (pr2 (pr2 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr212212' x" := (pr2 (pr1 (pr2 (pr2 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr212221' x" := (pr2 (pr1 (pr2 (pr2 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr212222' x" := (pr2 (pr1 (pr2 (pr2 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr221111' x" := (pr2 (pr2 (pr1 (pr1 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr221112' x" := (pr2 (pr2 (pr1 (pr1 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr221121' x" := (pr2 (pr2 (pr1 (pr1 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr221122' x" := (pr2 (pr2 (pr1 (pr1 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr221211' x" := (pr2 (pr2 (pr1 (pr2 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr221212' x" := (pr2 (pr2 (pr1 (pr2 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr221221' x" := (pr2 (pr2 (pr1 (pr2 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr221222' x" := (pr2 (pr2 (pr1 (pr2 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr222111' x" := (pr2 (pr2 (pr2 (pr1 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr222112' x" := (pr2 (pr2 (pr2 (pr1 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr222121' x" := (pr2 (pr2 (pr2 (pr1 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr222122' x" := (pr2 (pr2 (pr2 (pr1 (pr2 (pr2 x)))))) (at level 8).
Notation "'pr222211' x" := (pr2 (pr2 (pr2 (pr2 (pr1 (pr1 x)))))) (at level 8).
Notation "'pr222212' x" := (pr2 (pr2 (pr2 (pr2 (pr1 (pr2 x)))))) (at level 8).
Notation "'pr222221' x" := (pr2 (pr2 (pr2 (pr2 (pr2 (pr1 x)))))) (at level 8).
Notation "'pr222222' x" := (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 x)))))) (at level 8).
