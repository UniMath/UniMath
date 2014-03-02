(** * use propositional truncation to construct an interval *)

Unset Automatic Introduction.
Require Import Foundations.hlevel1.hProp.
Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).

Definition bool_map {Y} := bool_rect (fun _ => Y) : Y -> Y -> bool -> Y.

Definition interval := ishinh bool.
Definition left := hinhpr _ true.
Definition right := hinhpr _ false.
Definition interval_path : left == right.
Proof. apply (pr2 (ishinh _)). Defined.

Definition interval_map Y (f : bool -> Y) : f true == f false -> interval -> Y.
Proof. 
  intros ? ? e h.
  set (q := fun y => y == f false).
  exact (pr1 (h (hProppair (coconustot Y (f false))
                           (isapropifcontr (iscontrcoconustot _ _)))
                (fun v => 
                  tpair _ (f v)
                        (bool_rect (funcomp f q) e (idpath _) v)))).
Defined.

(* verify a computation is definitional *)
Goal forall Y (f : bool -> Y) (e:f true == f false) (v:bool), 
       interval_map Y f e (hinhpr _ v) == f v.
  reflexivity. Qed.

(** ** use the interval to prove functional extensionality for sections

       Notice that [ishinh] depends on [funextfunax],
       so we don't get something for nothing, but this is
       a quick way of deducing [funextsec] from [funextfunax]. *)

Definition funextsec2 X (Y:X->Type) (f g:forall x,Y x) :
           (forall x, f x==g x) -> f == g.
Proof. intros ? ? ? ? e.
       exact (maponpaths
           (fun h x => interval_map (Y x) (bool_map (f x) (g x)) (e x) h)
           interval_path). Defined.
