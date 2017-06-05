(** Anthony Bordg, June 2017 *)


Require Import UniMath.Algebra.Monoids_and_Groups.

(** * Types with operators *)

(** Types with a binary operation *)

Definition typewithbinop : UU := ∑ X : UU, binop X.

Definition pr1typewithbinop (X : typewithbinop) : UU := pr1 X.

Coercion pr1typewithbinop : typewithbinop >-> UU.

Definition op {X : typewithbinop} : binop X := pr2 X.

Definition ishbinopfun {X Y : typewithbinop} (f : X -> Y) : UU :=
  ∏ x x' : X, paths (f (op x x')) (op (f x) (f x')).

Definition typewithbinopfun (X Y : typewithbinop) : UU := ∑ f : X -> Y, ishbinopfun f.

Definition pr1typewithbinopfun {X Y : typewithbinop} (f : typewithbinopfun X Y) : X -> Y := pr1 f.

Coercion pr1typewithbinopfun : typewithbinopfun >-> Funclass.

(** Types with a left action *)

Definition laction (Ω X : UU) : UU := Ω -> X -> X.

Definition typewithlaction (Ω : UU) : UU := ∑ X : UU, laction Ω X.

Definition typewithlaction_pair {Ω : UU} (X : UU) (ω : laction Ω X) : typewithlaction Ω := tpair _ X ω.

Definition pr1typewithlaction {Ω : UU} (X : typewithlaction Ω) : UU := pr1 X.

Coercion pr1typewithlaction : typewithlaction >-> UU.

Definition pr2typewithlaction {Ω : UU} (X : typewithlaction Ω) : laction Ω X := pr2 X.

Local Notation " α · x " := (pr2typewithlaction _ α x) : typewithlaction_scope.

Delimit Scope typewithlaction_scope with typewithlaction.

Local Open Scope typewithlaction.

(** Types with a binary operation and a left action *)

Definition typewith_binop_laction (Ω : UU) : UU := ∑ X : typewithbinop, laction Ω X.

Definition pr1typewith_binop_laction {Ω : UU} (X : typewith_binop_laction Ω) : typewithbinop := pr1 X.

Coercion pr1typewith_binop_laction : typewith_binop_laction >-> typewithbinop.

Definition typewith_binop_laction_to_binop {Ω : UU} (X : typewith_binop_laction Ω) : binop X := pr2 (pr1 X).

Definition pr2typewith_binop_laction {Ω : UU} (X : typewith_binop_laction Ω) : laction Ω X := pr2 X.

(** Types with operators *)

Definition ishdistr_laction {Ω X : UU} (opp : binop X) (ω : laction Ω X) : UU :=
  ∏ α : Ω, ∏ x y : X, ω α (opp x y) = opp (ω α x) (ω α y).

Definition typewithoperators (Ω : UU) : UU :=
  ∑ X : typewith_binop_laction Ω, ishdistr_laction (typewith_binop_laction_to_binop X) (pr2typewith_binop_laction X).

Definition pr1typewithoperators {Ω : UU} (X : typewithoperators Ω) : typewith_binop_laction Ω := pr1 X.

Coercion pr1typewithoperators : typewithoperators >-> typewith_binop_laction.

Definition typewithoperators_to_typewithbinop {Ω : UU} (X : typewithoperators Ω) : typewithbinop := pr1 X.

Coercion typewithoperators_to_typewithbinop : typewithoperators >-> typewithbinop.

Definition typewithoperators_to_laction {Ω : UU} (X : typewithoperators Ω) : laction Ω X := pr2 (pr1 X).

Definition typewithoperators_to_typewithlaction {Ω : UU} (X : typewithoperators Ω) : typewithlaction Ω :=
  typewithlaction_pair X (typewithoperators_to_laction X).

Coercion typewithoperators_to_typewithlaction : typewithoperators >-> typewithlaction.

Definition homothety {Ω : UU} (X : typewithoperators Ω) (α : Ω) : X -> X := typewithoperators_to_laction X α.

Lemma ishbinopfun_homothety {Ω : UU} (X : typewithoperators Ω) (α : Ω) : ishbinopfun (homothety X α).
Proof.
  intros x y.
  apply (pr2 X).
Defined.

Definition iscomm_typewithoperators {Ω : UU} (X : typewithoperators Ω) : UU := iscomm (@op X).

Definition commtypewithoperators (Ω : UU) : UU := ∑ X : typewithoperators Ω, iscomm_typewithoperators X.

(** Morphisms between types with operators *)

Definition ishcompat_wrt_laction {Ω : UU} (X Y : typewithlaction Ω) (f : X -> Y) : UU := ∏ α : Ω, ∏ x : X, f (α · x) = α · (f x) .

Definition typewithoperatorsfun {Ω : UU} (X Y : typewithoperators Ω) : UU :=
  ∑ f : typewithbinopfun X Y, ishcompat_wrt_laction X Y f.

(** * Groups with operators *)

(** Groups endowed with a left action *)

Definition grwithlaction (Ω : UU) : UU := ∑ G : gr, laction Ω G.

Definition grwithlaction_pair {Ω : UU} (G : gr) (ω : laction Ω G) : grwithlaction Ω := tpair _ G ω.

Definition pr1grwithlaction {Ω : UU} (G : grwithlaction Ω) : gr := pr1 G.

Coercion pr1grwithlaction : grwithlaction >-> gr.

(** From groups to types with a binary operations *)

Definition gr_to_typewithbinop (G : gr) : typewithbinop.
Proof.
  split with G.
  exact (pr2 (pr1 G)).
Defined.

(** Groups with operators *)

Definition grwithoperators (Ω : UU) : UU := ∑ G : grwithlaction Ω, ishdistr_laction (@op (gr_to_typewithbinop G)) (pr2 G).

Definition grwithoperators_pair {Ω : UU} (G : grwithlaction Ω) (is : ishdistr_laction (@op (gr_to_typewithbinop G)) (pr2 G)) :
  grwithoperators Ω := tpair _ G is.

Definition pr1grwithoperators {Ω : UU} (G : grwithoperators Ω) : grwithlaction Ω:= pr1 G.

Coercion pr1grwithoperators : grwithoperators >-> grwithlaction.

(** A few access functions for groups endowed with a left action and groups with operators *)

Definition grwithlaction_to_typewith_binop_laction {Ω : UU} (G : grwithlaction Ω) : typewith_binop_laction Ω.
Proof.
  split with (gr_to_typewithbinop G).
  exact (pr2 G).
Defined.

Definition grwithoperators_to_typewithoperators {Ω : UU} (G : grwithoperators Ω) : typewithoperators Ω.
Proof.
  split with (grwithlaction_to_typewith_binop_laction G).
  exact (pr2 G).
Defined.

Coercion grwithoperators_to_typewithoperators : grwithoperators >-> typewithoperators.

Definition grwithoperators_to_typewithlaction {Ω : UU} (G : grwithoperators Ω) : typewithlaction Ω.
Proof.
  split with G.
  exact (pr2 (pr1grwithoperators G)).
Defined.

Coercion grwithoperators_to_typewithlaction : grwithoperators >-> typewithlaction.

(** Abelian groups with operators *)

Definition abgrwithoperators (Ω : UU) : UU := ∑ G : grwithoperators Ω, iscomm (@op (gr_to_typewithbinop G)).

Definition pr1abgrwithoperators {Ω : UU} (G : abgrwithoperators Ω) : grwithoperators Ω := pr1 G.

Coercion pr1abgrwithoperators : abgrwithoperators >-> grwithoperators.

Lemma ismonoidfun_homothety {Ω : UU} (G : grwithoperators Ω) (α : Ω) : ismonoidfun (homothety G α).
Proof.
  apply dirprodpair.
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
  ∑ f : monoidfun X Y, ishcompat_wrt_laction X Y f.

(** * Subtypes of a type with a binary operation *)

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

Definition isstable_by_laction {Ω X : UU} (ω : laction Ω X) (A : hsubtype X) : UU :=
  ∏ α : Ω, ∏ x : A, A (ω α (pr1 x)).

Lemma isapropisstable_by_laction {Ω X : UU} (ω : laction Ω X) (A : hsubtype X) : isaprop (isstable_by_laction ω A).
Proof.
  intros.
  apply impred. intro t.
  apply impred. intro x.
  apply (pr2 (A (ω t (pr1 x)))).
Defined.

(** * Stable subgroups of a group with operators *)

Definition isstable_subgr {Ω : UU} {G : grwithoperators Ω} (A : hsubtype G) : UU :=
  (issubgr A) × (isstable_by_laction (typewithoperators_to_laction G) A).

Lemma isapropisstable_subgr {Ω : UU} {G : grwithoperators Ω} (A : hsubtype G) : isaprop (isstable_subgr A).
Proof.
  intros. apply (isofhleveldirprod 1).
  - apply isapropissubgr.
  - apply isapropisstable_by_laction.
Defined.

Definition stable_subgr {Ω : UU} (G : grwithoperators Ω) : UU := ∑ A : hsubtype G, isstable_subgr A.

(** A few access functions for stable subgroups *)

Definition stable_subgr_to_gr {Ω : UU} {G : grwithoperators Ω} (H : stable_subgr G) : gr :=
  carrierofasubgr (subgrpair (pr1 H)  (dirprod_pr1 (pr2 H))).

Definition stable_subgr_to_laction {Ω : UU} {G : grwithoperators Ω} (H : stable_subgr G) : laction Ω (stable_subgr_to_gr H).
Proof.
  intros α x.
  split with (pr2 (pr1 G) α (pr1 x)).
  apply (pr2 (pr2 H) α x).
Defined.

Definition stable_subgr_to_grwithlaction {Ω : UU} {G : grwithoperators Ω} (H : stable_subgr G) : grwithlaction Ω :=
  grwithlaction_pair (stable_subgr_to_gr H) (stable_subgr_to_laction H).

Definition stable_subgr_to_ishdistr_laction {Ω : UU} {G : grwithoperators Ω} (H : stable_subgr G) :
  ishdistr_laction (@op (gr_to_typewithbinop (stable_subgr_to_gr H))) (stable_subgr_to_laction H).
Proof.
  intros α x y.
  use total2_paths_f.
  apply (pr2 G α (pr1 x) (pr1 y)).
  apply propproperty.
Defined.

Definition stable_subgr_to_grwithoperators {Ω : UU} (G : grwithoperators Ω) (H : stable_subgr G) : grwithoperators Ω :=
  grwithoperators_pair (stable_subgr_to_grwithlaction H) (stable_subgr_to_ishdistr_laction H).

Coercion stable_subgr_to_grwithoperators : stable_subgr >-> grwithoperators.
