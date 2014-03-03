(** * Use propositional truncation to construct an interval

Martin Escardo's version in Agda is 
%\href{http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/hsetfunext.html#6060}{here}.%
#<a href="http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/hsetfunext.html##6060">here</a>.# *)

Unset Automatic Introduction.
Require Import Foundations.hlevel1.hProp.
Notation "a == b" := (paths a b) (at level 70, no associativity).
Notation "! p " := (pathsinv0 p) (at level 50).

Definition bool_map {Y} := bool_rect (fun _ => Y) : Y -> Y -> bool -> Y.

(** ** The definition of the interval 

We define the interval as the propositional truncation of [bool]. *)

Definition interval := ishinh bool.
Definition left := hinhpr _ true.
Definition right := hinhpr _ false.
Definition interval_path : left == right.
Proof. apply (pr2 (ishinh _)). Defined.
Definition interval_map {Y} {y y':Y} : y == y' -> interval -> Y.
Proof. 
  intros ? ? ? e h.
  set (f := bool_map y y').
  set (q := fun y => y == f false).
  exact (pr1 (h (hProppair (coconustot Y (f false))
                           (isapropifcontr (iscontrcoconustot _ _)))
                (fun v => 
                  tpair _ (f v)
                        (bool_rect (funcomp f q) e (idpath _) v)))).
Defined.

(** We verify some computations. *)

Goal forall Y (y y':Y) (e:y == y'), interval_map e left == y.
  reflexivity. Qed.

Goal forall Y (y y':Y) (e:y == y'), interval_map e right == y'.
  reflexivity. Qed.

Goal forall Y (y y':Y) (e:y == y'), 
       maponpaths (interval_map e) interval_path == e.
  intros.
  destruct e.
  admit.
Defined.

(** ** Functional extensionality for sections using the interval *)

Definition funextsec2 X (Y:X->Type) (f g:forall x,Y x) :
           (forall x, f x==g x) -> f == g.
Proof. 
  intros ? ? ? ? e.
  exact (maponpaths
           (fun h x => interval_map (e x) h)
           interval_path). Defined.

(**    Notice that [ishinh] depends on [funextfunax],
       so we don't get something for nothing, but this is
       a quick way of deducing [funextsec] from [funextfunax]. *)
