(** Anthony Bordg, June 2017 *)


(** ********************************************

Contents:

- Types with operators ([typewithoperators])
- Groups with operators ([grwithoperators]) and morphisms between them ([grwithoperatorsfun])
- Stable subgroups of a group with operators ([stable_subgr])

***********************************************)


Require Import UniMath.Algebra.Groups.

(** * Types with operators *)

(** Types with a binary operation *)

Definition typewithbinop : UU := ∑ X : UU, binop X.

Definition pr1typewithbinop (X : typewithbinop) : UU := pr1 X.

Coercion pr1typewithbinop : typewithbinop >-> UU.

Definition op {X : typewithbinop} : binop X := pr2 X.

Definition ishbinopfun {X Y : typewithbinop} (f : X -> Y) : UU :=
  ∏ x x' : X, f (op x x') = op (f x) (f x').

Definition typewithbinopfun (X Y : typewithbinop) : UU := ∑ f : X -> Y, ishbinopfun f.

Definition pr1typewithbinopfun {X Y : typewithbinop} (f : typewithbinopfun X Y) : X -> Y := pr1 f.

Coercion pr1typewithbinopfun : typewithbinopfun >-> Funclass.

(** Types with a (left) action *)
(** cf. section 1. Actions, §3, chapitre 1, Algèbre, N. Bourbaki *)

Definition action (Ω X : UU) : UU := Ω -> X -> X.

Definition typewithaction (Ω : UU) : UU := ∑ X : UU, action Ω X.

Definition typewithaction_pair {Ω : UU} (X : UU) (ω : action Ω X) : typewithaction Ω := tpair _ X ω.

Definition pr1typewithaction {Ω : UU} (X : typewithaction Ω) : UU := pr1 X.

Coercion pr1typewithaction : typewithaction >-> UU.

Definition pr2typewithaction {Ω : UU} (X : typewithaction Ω) : action Ω X := pr2 X.

Local Notation " α · x " := (pr2typewithaction _ α x) : typewithaction_scope.

Delimit Scope typewithaction_scope with typewithaction.

Local Open Scope typewithaction.

(** Types with a binary operation and a (left) action *)

Definition typewith_binop_action (Ω : UU) : UU := ∑ X : typewithbinop, action Ω X.

Definition pr1typewith_binop_action {Ω : UU} (X : typewith_binop_action Ω) : typewithbinop := pr1 X.

Coercion pr1typewith_binop_action : typewith_binop_action >-> typewithbinop.

Definition typewith_binop_action_to_binop {Ω : UU} (X : typewith_binop_action Ω) : binop X := pr2 (pr1 X).

Definition pr2typewith_binop_action {Ω : UU} (X : typewith_binop_action Ω) : action Ω X := pr2 X.

(** Types with operators *)

Definition ishdistr_action {Ω X : UU} (opp : binop X) (ω : action Ω X) : UU :=
  ∏ α : Ω, ∏ x y : X, ω α (opp x y) = opp (ω α x) (ω α y).

Definition typewithoperators (Ω : UU) : UU :=
  ∑ X : typewith_binop_action Ω, ishdistr_action (typewith_binop_action_to_binop X) (pr2typewith_binop_action X).

Definition pr1typewithoperators {Ω : UU} (X : typewithoperators Ω) : typewith_binop_action Ω := pr1 X.

Coercion pr1typewithoperators : typewithoperators >-> typewith_binop_action.

Definition typewithoperators_to_typewithbinop {Ω : UU} (X : typewithoperators Ω) : typewithbinop := pr1 X.

Coercion typewithoperators_to_typewithbinop : typewithoperators >-> typewithbinop.

Definition typewithoperators_to_action {Ω : UU} (X : typewithoperators Ω) : action Ω X := pr2 (pr1 X).

Definition typewithoperators_to_typewithaction {Ω : UU} (X : typewithoperators Ω) : typewithaction Ω :=
  typewithaction_pair X (typewithoperators_to_action X).

Coercion typewithoperators_to_typewithaction : typewithoperators >-> typewithaction.

Definition homothety {Ω : UU} (X : typewithoperators Ω) (α : Ω) : X -> X := typewithoperators_to_action X α.

Lemma ishbinopfun_homothety {Ω : UU} (X : typewithoperators Ω) (α : Ω) : ishbinopfun (homothety X α).
Proof.
  intros x y.
  apply (pr2 X).
Defined.

Definition iscomm_typewithoperators {Ω : UU} (X : typewithoperators Ω) : UU := iscomm (@op X).

Definition commtypewithoperators (Ω : UU) : UU := ∑ X : typewithoperators Ω, iscomm_typewithoperators X.

(** Morphisms between types with operators *)

Definition ishcompat_wrt_action {Ω : UU} (X Y : typewithaction Ω) (f : X -> Y) : UU := ∏ α : Ω, ∏ x : X, f (α · x) = α · (f x) .

Definition typewithoperatorsfun {Ω : UU} (X Y : typewithoperators Ω) : UU :=
  ∑ f : typewithbinopfun X Y, ishcompat_wrt_action X Y f.

(** ** Groups with operators *)
(** cf. section 2. Groupes à opérateurs, §4, chapitre 1, Algèbre, N. Bourbaki *)

(** Groups endowed with a (left) action *)

Definition grwithaction (Ω : UU) : UU := ∑ G : gr, action Ω G.

Definition grwithaction_pair {Ω : UU} (G : gr) (ω : action Ω G) : grwithaction Ω := tpair _ G ω.

Definition pr1grwithaction {Ω : UU} (G : grwithaction Ω) : gr := pr1 G.

Coercion pr1grwithaction : grwithaction >-> gr.

(** From groups to types with a binary operations *)

Definition gr_to_typewithbinop (G : gr) : typewithbinop.
Proof.
  split with G.
  exact (pr2 (pr1 G)).
Defined.

(** Groups with operators *)

Definition grwithoperators (Ω : UU) : UU := ∑ G : grwithaction Ω, ishdistr_action (@op (gr_to_typewithbinop G)) (pr2 G).

Definition grwithoperators_pair {Ω : UU} (G : grwithaction Ω) (is : ishdistr_action (@op (gr_to_typewithbinop G)) (pr2 G)) :
  grwithoperators Ω := tpair _ G is.

Definition pr1grwithoperators {Ω : UU} (G : grwithoperators Ω) : grwithaction Ω:= pr1 G.

Coercion pr1grwithoperators : grwithoperators >-> grwithaction.

(** A few access functions for groups endowed with a (left) action and groups with operators *)

Definition grwithaction_to_typewith_binop_action {Ω : UU} (G : grwithaction Ω) : typewith_binop_action Ω.
Proof.
  split with (gr_to_typewithbinop G).
  exact (pr2 G).
Defined.

Definition grwithoperators_to_typewithoperators {Ω : UU} (G : grwithoperators Ω) : typewithoperators Ω.
Proof.
  split with (grwithaction_to_typewith_binop_action G).
  exact (pr2 G).
Defined.

Coercion grwithoperators_to_typewithoperators : grwithoperators >-> typewithoperators.

Definition grwithoperators_to_typewithaction {Ω : UU} (G : grwithoperators Ω) : typewithaction Ω.
Proof.
  split with G.
  exact (pr2 (pr1grwithoperators G)).
Defined.

Coercion grwithoperators_to_typewithaction : grwithoperators >-> typewithaction.

(** Abelian groups with operators *)

Definition abgrwithoperators (Ω : UU) : UU := ∑ G : grwithoperators Ω, iscomm (@op (gr_to_typewithbinop G)).

Definition pr1abgrwithoperators {Ω : UU} (G : abgrwithoperators Ω) : grwithoperators Ω := pr1 G.

Coercion pr1abgrwithoperators : abgrwithoperators >-> grwithoperators.

Lemma ismonoidfun_homothety {Ω : UU} (G : grwithoperators Ω) (α : Ω) : ismonoidfun (homothety G α).
Proof.
  apply make_dirprod.
  - intros x y.
    apply (pr2 G).
  - assert (p : homothety G α (unel G) = homothety G α (@op G (unel G) (unel G))).
    + symmetry. apply maponpaths. apply lunax.
    + apply (grlcan G (homothety G α (unel G))).
      transitivity (homothety G α (@op G (unel G) (unel G))).
      * symmetry. apply (pr2 G).
      * symmetry.  rewrite runax. apply p.
Defined.

(** Morphisms between groups with operators *)

Definition grwithoperatorsfun {Ω : UU} (X Y : grwithoperators Ω) : UU :=
  ∑ f : monoidfun X Y, ishcompat_wrt_action X Y f.


(** *** Stable subgroups of a group with operators *)
(** cf. section 3. Sous-groupes, §4, Algèbre, N. Bourbaki *)

(** Subtypes of a type with a binary operation *)

Definition issubtypewithbinop {X : UU} (opp : binop X) (A : hsubtype X) : UU :=
  ∏ a a' : A, A (opp (pr1 a) (pr1 a')).

Lemma isapropissubtypewithbinop {X : UU} (opp : binop X) (A : hsubtype X) : isaprop (issubtypewithbinop opp A).
Proof.
  intros.
  apply impred. intro a.
  apply impred. intros a'.
  apply (pr2 (A (opp (pr1 a) (pr1 a')))).
Defined.

Definition subtypewithbinop (X : typewithbinop) : UU := ∑ A : hsubtype X, issubtypewithbinop (@op X) A.

Definition isstable_by_action {Ω X : UU} (ω : action Ω X) (A : hsubtype X) : UU :=
  ∏ α : Ω, ∏ x : X, A x -> A (ω α x).

Lemma isapropisstable_by_action {Ω X : UU} (ω : action Ω X) (A : hsubtype X) : isaprop (isstable_by_action ω A).
Proof.
  intros.
  apply impred. intro t.
  apply impred. intro x.
  apply impred. intro p.
  apply (pr2 (A (ω t x))).
Defined.

Definition isstable_subgr {Ω : UU} {G : grwithoperators Ω} (A : hsubtype G) : UU :=
  (issubgr A) × (isstable_by_action (typewithoperators_to_action G) A).

Lemma isapropisstable_subgr {Ω : UU} {G : grwithoperators Ω} (A : hsubtype G) : isaprop (isstable_subgr A).
Proof.
  intros. apply (isofhleveldirprod 1).
  - apply isapropissubgr.
  - apply isapropisstable_by_action.
Defined.

Definition stable_subgr {Ω : UU} (G : grwithoperators Ω) : UU := ∑ A : hsubtype G, isstable_subgr A.

(** A few access functions for stable subgroups *)

Definition stable_subgr_to_gr {Ω : UU} {G : grwithoperators Ω} (H : stable_subgr G) : gr :=
  carrierofasubgr (make_subgr (pr1 H)  (dirprod_pr1 (pr2 H))).

Definition stable_subgr_to_action {Ω : UU} {G : grwithoperators Ω} (H : stable_subgr G) : action Ω (stable_subgr_to_gr H).
Proof.
  intros α x.
  split with (pr2 (pr1 G) α (pr1 x)).
  apply (pr2 (pr2 H) α (pr1 x)).
  apply (pr2 x).
Defined.

Definition stable_subgr_to_grwithaction {Ω : UU} {G : grwithoperators Ω} (H : stable_subgr G) : grwithaction Ω :=
  grwithaction_pair (stable_subgr_to_gr H) (stable_subgr_to_action H).

Definition stable_subgr_to_ishdistr_action {Ω : UU} {G : grwithoperators Ω} (H : stable_subgr G) :
  ishdistr_action (@op (gr_to_typewithbinop (stable_subgr_to_gr H))) (stable_subgr_to_action H).
Proof.
  intros α x y.
  use total2_paths_f.
  apply (pr2 G α (pr1 x) (pr1 y)).
  apply propproperty.
Defined.

Definition stable_subgr_to_grwithoperators {Ω : UU} (G : grwithoperators Ω) (H : stable_subgr G) : grwithoperators Ω :=
  grwithoperators_pair (stable_subgr_to_grwithaction H) (stable_subgr_to_ishdistr_action H).

Coercion stable_subgr_to_grwithoperators : stable_subgr >-> grwithoperators.
