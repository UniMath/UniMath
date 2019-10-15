(** * Notations  *)

Require Export UniMath.Foundations.All.

Notation "A ⇒ B" := (himpl A B) : logic.

Local Open Scope logic.

Definition hequiv (P Q:hProp) : hProp := (P ⇒ Q) ∧ (Q ⇒ P).

Notation "A ⇔ B" := (hequiv A B) (at level 95, no associativity) : logic.

Definition total2_hProp {X : hProp} (Y : X -> hProp) : hProp
  := make_hProp (∑ x, Y x) (isaprop_total2 X Y).

Declare Scope prop.
Delimit Scope prop with prop.

Notation "'∑' x .. y , P" := (total2_hProp (λ x,.. (total2_hProp (λ y, P))..))
  (at level 200, x binder, y binder, right associativity) : prop.
  (* type this in emacs in agda-input method with \sum *)

Notation "'pr11' x" := (pr1 (pr1 x)) (at level 10, left associativity).
Notation "'pr12' x" := (pr1 (pr2 x)) (at level 10, left associativity).
Notation "'pr21' x" := (pr2 (pr1 x)) (at level 10, left associativity).
Notation "'pr22' x" := (pr2 (pr2 x)) (at level 10, left associativity).

Notation "'pr111' x" := (pr1 (pr1 (pr1 x))) (at level 10, left associativity).
Notation "'pr112' x" := (pr1 (pr1 (pr2 x))) (at level 10, left associativity).
Notation "'pr121' x" := (pr1 (pr2 (pr1 x))) (at level 10, left associativity).
Notation "'pr122' x" := (pr1 (pr2 (pr2 x))) (at level 10, left associativity).
Notation "'pr211' x" := (pr2 (pr1 (pr1 x))) (at level 10, left associativity).
Notation "'pr212' x" := (pr2 (pr1 (pr2 x))) (at level 10, left associativity).
Notation "'pr221' x" := (pr2 (pr2 (pr1 x))) (at level 10, left associativity).
Notation "'pr222' x" := (pr2 (pr2 (pr2 x))) (at level 10, left associativity).

(** ** Variants on paths and coconus *)

Definition paths_from {X} (x:X) := coconusfromt X x.
Definition point_to {X} {x:X} : paths_from x -> X := coconusfromtpr1 _ _.
Definition paths_from_path {X} {x:X} (w:paths_from x) := pr2 w.
Definition paths' {X} (x:X) := λ y, y = x.
Definition idpath' {X} (x:X) := idpath x : paths' x x.
Definition paths_to {X} (x:X) := coconustot X x.
Definition point_from {X} {x:X} : paths_to x -> X := coconustotpr1 _ _.
Definition paths_to_path {X} {x:X} (w:paths_to x) := pr2 w.

Lemma iscontr_paths_to {X} (x:X) : iscontr (paths_to x).
Proof. apply iscontrcoconustot. Defined.
Lemma iscontr_paths_from {X} (x:X) : iscontr (paths_from x).
Proof. apply iscontrcoconusfromt. Defined.
Definition paths_to_prop {X} (x:X) :=
  make_hProp (paths_to x) (isapropifcontr (iscontr_paths_to x)).
Definition paths_from_prop {X} (x:X) :=
  make_hProp (paths_from x) (isapropifcontr (iscontr_paths_from x)).

(** ** Squashing *)

Notation squash_fun := hinhfun (only parsing).
Notation squash_fun2 := hinhfun2 (only parsing).
Notation squash_element := hinhpr (only parsing).

Lemma squash_path {X} (x y:X) : squash_element x = squash_element y.
Proof. intros. apply propproperty. Defined.
