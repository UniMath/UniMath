(** * use propositional truncation to construct an interval *)

Unset Automatic Introduction.
Require Import Foundations.hlevel1.hProp.
Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).

Definition bool_map {Y} := bool_rect (fun _ => Y).

Definition interval := ishinh bool.
Definition left := hinhpr _ true.
Definition right := hinhpr _ false.
Definition interval_path : left == right.
Proof. apply (pr2 (ishinh _)). Defined.

Definition interval_map Y (f : bool -> Y) (e:f true == f false) :
  interval -> Y.
Proof. intros ? ? ? h.
       apply (@pr1 _ (fun y => y == f true)).
       apply (h (hProppair _ (isapropifcontr (iscontrcoconustot _ _)))).
       intro v. apply (tpair _ (f v)). 
       { destruct v. { reflexivity. } { exact (!e). } } Defined.

(* verify some computations are definitional *)
Goal forall Y (f : bool -> Y) (e:f true == f false) (v:bool), 
       interval_map Y f e (hinhpr _ v) == f v.
  reflexivity. Qed.
Goal forall Y (y y':Y) (v:bool), bool_map y y' true == y.
  reflexivity. Qed.
Goal forall Y (y y':Y) (v:bool), bool_map y y' false == y'.
  reflexivity. Qed.

(** ** use the interval to prove functional extensionality for sections

       Notice that [interval_path] above depends on [funextfunax],
       so we don't get something for nothing. *)
Definition funextsec2 X (Y:X->Type) (f g:forall x,Y x) :
           (forall x, f x==g x) -> f == g.
Proof. intros ? ? ? ? e.
       exact (maponpaths
           (fun h x => interval_map (Y x) (bool_map (f x) (g x)) (e x) h)
           interval_path). Defined.
