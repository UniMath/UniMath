(** * Algebra 1. Part A. Generalities. Vladimir Voevodsky. Aug. 2011 -. *)
(** ** Contents
- Sets with one and two binary operations
 - Unary operations
 - Binary operations
  - General definitions
  - Standard conditions on one binary operation on a set
  - Standard conditions on a pair of binary operations on a set
 - Sets with one binary operation
  - General definitions
  - Functions compatible with a binary operation (homomorphism)
    and their properties
  - Transport of properties of a binary operation
  - Subobject
  - Relations compatible with a binary operation and quotient objects
  - Relations inversely compatible with a binary operation
  - Homomorphisms and relations
  - Quotient relations
  - Direct products
 - Sets with two binary operations
  - General definitions
  - Functions compatible with a pair of binary operation (homomorphisms)
    and their properties
  - Transport of properties of a pair of binary operations
  - Subobjects
  - Quotient objects
  - Direct products
*)


(** ** Preamble *)

(** Settings *)

(** The following line has to be removed for the file to compile with Coq8.2 *)
Unset Automatic Introduction.

(** Imports *)

Require Export UniMath.Foundations.Sets.

(** To upstream files *)


(** ** Sets with one and two binary operations *)

(** *** Unary operations *)

Definition unop (X : UU) : UU := X -> X.

(** *** Binary operations *)


(** **** General definitions *)

Definition islcancelable {X : UU} (opp : binop X) (x : X) : UU := isincl (λ x0 : X, opp x x0).

Definition isrcancelable {X : UU} (opp : binop X) (x : X) : UU := isincl (λ x0 : X, opp x0 x).

Definition iscancelable {X : UU} (opp : binop X) (x : X) : UU :=
  (islcancelable opp x) × (isrcancelable opp x).

Definition islinvertible {X : UU} (opp : binop X) (x : X) : UU := isweq (λ x0 : X, opp x x0).

Definition isrinvertible {X : UU} (opp : binop X) (x : X) : UU := isweq (λ x0 : X, opp x0 x).

Definition isinvertible {X : UU} (opp : binop X) (x : X) : UU :=
  (islinvertible opp x) × (isrinvertible opp x).

(** **** Transfer of binary operations relative to weak equivalences *)

Definition binop_weq_fwd {X Y : UU} (H : X ≃ Y) :
  binop X → binop Y :=
  λ (opp : binop X) (x y : Y), H (opp (invmap H x) (invmap H y)).

Definition binop_weq_bck {X Y : UU} (H : X ≃ Y) :
  binop Y → binop X :=
  λ (opp : binop Y) (x y : X), invmap H (opp (H x) (H y)).

(** **** Standard conditions on one binary operation on a set *)

(** *)

Definition isassoc {X : UU} (opp : binop X) : UU :=
  ∏ x x' x'', paths (opp (opp x x') x'') (opp x (opp x' x'')).

Lemma isapropisassoc {X : hSet} (opp : binop X) : isaprop (isassoc opp).
Proof.
  intros.
  apply impred. intro x.
  apply impred. intro x'.
  apply impred. intro x''.
  simpl. apply (setproperty X).
Defined.

(** *)

Definition islunit {X : UU} (opp : binop X) (un0 : X) : UU := ∏ x : X, (opp un0 x) = x.

Lemma isapropislunit {X : hSet} (opp : binop X) (un0 : X) : isaprop (islunit opp un0).
Proof.
  intros.
  apply impred. intro x.
  simpl. apply (setproperty X).
Defined.

Definition isrunit {X : UU} (opp : binop X) (un0 : X) : UU := ∏ x : X, (opp x un0) = x.

Lemma isapropisrunit {X : hSet} (opp : binop X) (un0 : X) : isaprop (isrunit opp un0).
Proof.
  intros.
  apply impred. intro x.
  simpl. apply (setproperty X).
Defined.

Definition isunit {X : UU} (opp : binop X) (un0 : X) : UU :=
  (islunit opp un0) × (isrunit opp un0).

Definition isunitpair {X : UU} {opp : binop X} {un0 : X} (H1 : islunit opp un0)
           (H2 : isrunit opp un0) : isunit opp un0 := dirprodpair H1 H2.

Definition isunital {X : UU} (opp : binop X) : UU := total2 (λ un0 : X, isunit opp un0).

Definition isunitalpair {X : UU} {opp : binop X} (un0 : X) (is : isunit opp un0) :
  isunital opp := tpair _ un0 is.

Lemma isapropisunital {X : hSet} (opp : binop X) : isaprop (isunital opp).
Proof.
  intros.
  apply (@isapropsubtype X (λ un0 : _, hconj (hProppair _ (isapropislunit opp un0))
                                              (hProppair _ (isapropisrunit opp un0)))).
  intros u1 u2. intros ua1 ua2.
  apply (pathscomp0 (pathsinv0 (pr2 ua2 u1)) (pr1 ua1 u2)).
Defined.

(** *)

Definition ismonoidop {X : UU} (opp : binop X) : UU := (isassoc opp) × (isunital opp).

Definition mk_ismonoidop {X : UU} {opp : binop X} (H1 : isassoc opp) (H2 : isunital opp) :
  ismonoidop opp := dirprodpair H1 H2.

Definition assocax_is {X : UU} {opp : binop X} : ismonoidop opp -> isassoc opp := @pr1 _ _.

Definition unel_is {X : UU} {opp : binop X} (is : ismonoidop opp) : X := pr1 (pr2 is).

Definition lunax_is {X : UU} {opp : binop X} (is : ismonoidop opp) :
  islunit opp (pr1 (pr2 is)) := pr1 (pr2 (pr2 is)).

Definition runax_is {X : UU} {opp : binop X} (is : ismonoidop opp) :
  isrunit opp (pr1 (pr2 is)) := pr2 (pr2 (pr2 is)).

Lemma isapropismonoidop {X : hSet} (opp : binop X) : isaprop (ismonoidop opp).
Proof.
  intros.
  apply (isofhleveldirprod 1).
  apply isapropisassoc.
  apply isapropisunital.
Defined.

(** *)

Definition islinv {X : UU} (opp : binop X) (un0 : X) (inv0 : X -> X) : UU :=
  ∏ x : X, paths (opp (inv0 x) x) un0.

Lemma isapropislinv {X : hSet} (opp : binop X) (un0 : X) (inv0 : X -> X) :
  isaprop (islinv opp un0 inv0).
Proof.
  intros.
  apply impred. intro x.
  apply (setproperty X (opp (inv0 x) x) un0).
Defined.

Definition isrinv {X : UU} (opp : binop X) (un0 : X) (inv0 : X -> X) : UU :=
  ∏ x : X, paths (opp x (inv0 x)) un0.

Lemma isapropisrinv {X : hSet} (opp : binop X) (un0 : X) (inv0 : X -> X) :
  isaprop (isrinv opp un0 inv0).
Proof.
  intros.
  apply impred. intro x.
  apply (setproperty X).
Defined.

Definition isinv {X : UU} (opp : binop X) (un0 : X) (inv0 : X -> X) : UU :=
  (islinv opp un0 inv0) × (isrinv opp un0 inv0).

Definition mk_isinv {X : UU} {opp : binop X} {un0 : X} {inv0 : X -> X} (H1 : islinv opp un0 inv0)
           (H2 : isrinv opp un0 inv0) : isinv opp un0 inv0 := dirprodpair H1 H2.

Lemma isapropisinv {X : hSet} (opp : binop X) (un0 : X) (inv0 : X -> X) :
  isaprop (isinv opp un0 inv0).
Proof.
  intros.
  apply (isofhleveldirprod 1).
  apply isapropislinv.
  apply isapropisrinv.
Defined.

Definition invstruct {X : UU} (opp : binop X) (is : ismonoidop opp) : UU :=
  total2 (fun inv0 : X -> X => isinv opp (unel_is is) inv0).

Definition mk_invstruct {X : UU} {opp : binop X} {is : ismonoidop opp} (inv0 : X -> X)
           (H : isinv opp (unel_is is) inv0) : invstruct opp is := tpair _ inv0 H.

Definition isgrop {X : UU} (opp : binop X) : UU :=
  total2 (λ is : ismonoidop opp, invstruct opp is).

Definition mk_isgrop {X : UU} {opp : binop X} (H1 : ismonoidop opp) (H2 : invstruct opp H1) :
  isgrop opp := tpair _ H1 H2.

Definition isgroppair {X : UU} {opp : binop X} (is1 : ismonoidop opp) (is2 : invstruct opp is1) :
  isgrop opp := tpair (λ is : ismonoidop opp, invstruct opp is) is1 is2.

Definition pr1isgrop (X : UU) (opp : binop X) : isgrop opp -> ismonoidop opp := @pr1 _ _.
Coercion pr1isgrop : isgrop >-> ismonoidop.

Definition grinv_is {X : UU} {opp : binop X} (is : isgrop opp) : X -> X := pr1 (pr2 is).

Definition grlinvax_is {X : UU} {opp : binop X} (is : isgrop opp) :
  islinv opp (unel_is (pr1 is)) (pr1 (pr2 is)) := pr1 (pr2 (pr2 is)).

Definition grrinvax_is {X : UU} {opp : binop X} (is : isgrop opp) :
  isrinv opp (unel_is (pr1 is)) (pr1 (pr2 is)) := pr2 (pr2 (pr2 is)).

Lemma isweqrmultingr_is {X : UU} {opp : binop X} (is : isgrop opp) (x0 : X) :
  isrinvertible opp x0.
Proof.
  intros. destruct is as [ is istr ].
  set (f := λ x : X, opp x x0).
  set (g := λ x : X, opp x ((pr1 istr) x0)).
  destruct is as [ assoc isun0 ].
  destruct istr as [ inv0 axs ].
  destruct isun0 as [ un0 unaxs ].
  simpl in * |-.
  assert (egf : ∏ x : _, paths (g (f x)) x).
  {
    intro x. unfold f. unfold g.
    destruct (pathsinv0 (assoc x x0 (inv0 x0))).
    set (e := pr2 axs x0). simpl in e. rewrite e.
    apply (pr2 unaxs x).
  }
  assert (efg : ∏ x : _, paths (f (g x)) x).
  {
    intro x. unfold f. unfold g.
    destruct (pathsinv0 (assoc x (inv0 x0) x0)).
    set (e := pr1 axs x0). simpl in e. rewrite e.
    apply (pr2 unaxs x).
  }
  apply (gradth _ _ egf efg).
Defined.

Lemma isweqlmultingr_is {X : UU} {opp : binop X} (is : isgrop opp) (x0 : X) :
  islinvertible opp x0.
Proof.
  intros. destruct is as [ is istr ].
  set (f := λ x : X, opp x0 x).
  set (g := λ x : X, opp ((pr1 istr) x0) x).
  destruct is as [ assoc isun0 ].
  destruct istr as [ inv0 axs ].
  destruct isun0 as [ un0 unaxs ].
  simpl in * |-.
  assert (egf : ∏ x : _, paths (g (f x)) x).
  {
    intro x. unfold f. unfold g.
    destruct (assoc (inv0 x0) x0 x).
    set (e := pr1 axs x0). simpl in e. rewrite e.
    apply (pr1 unaxs x).
  }
  assert (efg : ∏ x : _, paths (f (g x)) x).
  {
    intro x. unfold f. unfold g.
    destruct (assoc x0 (inv0 x0) x).
    set (e := pr2 axs x0). simpl in e. rewrite e.
    apply (pr1 unaxs x).
  }
  apply (gradth _ _ egf efg).
Defined.

Lemma isapropinvstruct {X : hSet} {opp : binop X} (is : ismonoidop opp) :
  isaprop (invstruct opp is).
Proof.
  intros. apply isofhlevelsn. intro is0.
  set (un0 := pr1 (pr2 is)).
  assert (int : ∏ (i : X -> X),
                isaprop (dirprod (∏ x : X, paths (opp (i x) x) un0)
                                 (∏ x : X, paths (opp x (i x)) un0))).
  {
    intro i. apply (isofhleveldirprod 1).
    - apply impred. intro x. simpl. apply (setproperty X).
    - apply impred. intro x. simpl. apply (setproperty X).
  }
  apply (isapropsubtype (λ i : _, hProppair _ (int i))).
  intros inv1 inv2. simpl. intro ax1. intro ax2. apply funextfun. intro x0.
  apply (invmaponpathsweq (weqpair _ (isweqrmultingr_is (tpair _ is is0) x0))).
  simpl. rewrite (pr1 ax1 x0). rewrite (pr1 ax2 x0). apply idpath.
Defined.

Lemma isapropisgrop {X : hSet} (opp : binop X) : isaprop (isgrop opp).
Proof.
  intros.
  apply (isofhleveltotal2 1).
  - apply isapropismonoidop.
  - apply isapropinvstruct.
Defined.

(* (** Unitary monoid where all elements are invertible is a group *)

Definition allinvvertibleinv {X : hSet} {opp : binop X} (is : ismonoidop opp)
  (allinv : ∏ x : X, islinvertible opp x) : X -> X
  := λ x : X, invmap (weqpair _ (allinv x)) (unel_is is).

*)

(** The following lemma is an analog of [Bourbaki, Alg. 1, ex. 2, p. 132] *)

Lemma isgropif {X : hSet} {opp : binop X} (is0 : ismonoidop opp)
      (is : ∏ x : X, hexists (λ x0 : X, (opp x x0) = (unel_is is0))) : isgrop opp.
Proof.
  intros. split with is0.
  destruct is0 as [ assoc isun0 ].
  destruct isun0 as [ un0 unaxs0 ].
  simpl in is.
  simpl in unaxs0. simpl in un0.
  simpl in assoc. simpl in unaxs0.
  assert (l1 : ∏ x' : X, isincl (λ x0 : X, opp x0 x')).
  {
    intro x'.
    apply (@hinhuniv (total2 (λ x0 : X, (opp x' x0) = un0))
                     (hProppair _ (isapropisincl (λ x0 : X, opp x0 x')))).
    - intro int1. simpl. apply isinclbetweensets.
      + apply (pr2 X).
      + apply (pr2 X).
      + intros a b. intro e.
        rewrite (pathsinv0 (pr2 unaxs0 a)). rewrite (pathsinv0 (pr2 unaxs0 b)).
        destruct int1 as [ invx' eq ].
        rewrite (pathsinv0 eq).
        destruct (assoc a x' invx').
        destruct (assoc b x' invx').
        rewrite e. apply idpath.
    -  apply (is x').
  }
  assert (is' : ∏ x : X, hexists (λ x0 : X, eqset (opp x0 x) un0)).
  {
    intro x. apply (λ f : _ , hinhuniv f (is x)). intro s1.
    destruct s1 as [ x' eq ]. apply hinhpr. split with x'. simpl.
    apply (invmaponpathsincl _ (l1 x')).
    rewrite (assoc x' x x'). rewrite eq. rewrite (pr1 unaxs0 x').
    unfold unel_is. simpl. rewrite (pr2 unaxs0 x'). apply idpath.
  }
  assert (l1' : ∏ x' : X, isincl (λ x0 : X, opp x' x0)).
  {
    intro x'.
    apply (@hinhuniv (total2 (λ x0 : X, (opp x0 x') = un0))
                     (hProppair _ (isapropisincl (λ x0 : X, opp x' x0)))).
    - intro int1. simpl. apply isinclbetweensets.
      + apply (pr2 X).
      + apply (pr2 X).
      + intros a b. intro e.
        rewrite (pathsinv0 (pr1 unaxs0 a)). rewrite (pathsinv0 (pr1 unaxs0 b)).
        destruct int1 as [ invx' eq ]. rewrite (pathsinv0 eq).
        destruct (pathsinv0 (assoc invx' x' a)).
        destruct (pathsinv0 (assoc invx' x' b)).
        rewrite e. apply idpath.
    - apply (is' x').
  }
  assert (int : ∏ x : X, isaprop (total2 (λ x0 : X, eqset (opp x0 x) un0))).
  {
    intro x. apply isapropsubtype. intros x1 x2. intros eq1 eq2.
    apply (invmaponpathsincl _ (l1 x)).
    rewrite eq1. rewrite eq2. apply idpath.
  }
  simpl.
  set (linv0 := λ x : X, hinhunivcor1 (hProppair _ (int x)) (is' x)).
  simpl in linv0.
  set (inv0 := λ x : X, pr1 (linv0 x)). split with inv0. simpl.
  split with (λ x : _, pr2 (linv0 x)). intro x.
  apply (invmaponpathsincl _ (l1 x)).
  rewrite (assoc x (inv0 x) x). change (inv0 x) with (pr1 (linv0 x)).
  rewrite (pr2 (linv0 x)). unfold unel_is. simpl.
  rewrite (pr1 unaxs0 x). rewrite (pr2 unaxs0 x). apply idpath.
Defined.

(** *)

Definition iscomm {X : UU} (opp : binop X) : UU := ∏ x x' : X, paths (opp x x') (opp x' x).

Lemma isapropiscomm {X : hSet} (opp : binop X) : isaprop (iscomm opp).
Proof.
  intros.
  apply impred. intros x.
  apply impred. intro x'.
  simpl.
  apply (setproperty X).
Defined.

Definition isabmonoidop {X : UU} (opp : binop X) : UU := (ismonoidop opp) × (iscomm opp).

Definition mk_isabmonoidop {X : UU} {opp : binop X} (H1 : ismonoidop opp) (H2 : iscomm opp) :
  isabmonoidop opp := dirprodpair H1 H2.

Definition pr1isabmonoidop (X : UU) (opp : binop X) : isabmonoidop opp -> ismonoidop opp :=
  @pr1 _ _.
Coercion pr1isabmonoidop : isabmonoidop >-> ismonoidop.

Definition commax_is {X : UU} {opp : binop X} (is : isabmonoidop opp) : iscomm opp := pr2 is.

Lemma isapropisabmonoidop {X : hSet} (opp : binop X) :
  isaprop (isabmonoidop opp).
Proof.
  intros.
  apply (isofhleveldirprod 1).
  apply isapropismonoidop.
  apply isapropiscomm.
Defined.

Lemma abmonoidoprer {X : UU} {opp : binop X} (is : isabmonoidop opp) (a b c d : X) :
  paths (opp (opp a b) (opp c d)) (opp (opp a c) (opp b d)).
Proof.
  intros.
  destruct is as [ is comm ]. destruct is as [ assoc unital0 ].
  simpl in *.
  destruct (assoc (opp a b) c d). destruct (assoc (opp a c) b d).
  destruct (pathsinv0 (assoc a b c)). destruct (pathsinv0 (assoc a c b)).
  destruct (comm b c). apply idpath.
Defined.

(** *)

Lemma weqlcancelablercancelable {X : UU} (opp : binop X) (is : iscomm opp) (x : X) :
  (islcancelable opp x) ≃ (isrcancelable opp x).
Proof.
  intros.
  assert (f : (islcancelable opp x) -> (isrcancelable opp x)).
  {
    unfold islcancelable. unfold isrcancelable.
    intro isl. apply (λ h : _, isinclhomot _ _ h isl).
    intro x0. apply is.
  }
  assert (g : (isrcancelable opp x) -> (islcancelable opp x)).
  {
    unfold islcancelable. unfold isrcancelable. intro isr.
    apply (λ h : _, isinclhomot _ _ h isr). intro x0. apply is.
  }
  split with f.
  apply (isweqimplimpl f g (isapropisincl (λ x0 : X, opp x x0))
                       (isapropisincl (λ x0 : X, opp x0 x))).
Defined.

Lemma weqlinvertiblerinvertible {X : UU} (opp : binop X) (is : iscomm opp) (x : X) :
  (islinvertible opp x) ≃ (isrinvertible opp x).
Proof.
  intros.
  assert (f : (islinvertible opp x) -> (isrinvertible opp x)).
  {
    unfold islinvertible. unfold isrinvertible. intro isl.
    apply (isweqhomot (λ y, opp x y)).
    - intro z. apply is.
    - apply isl.
  }
  assert (g : (isrinvertible opp x) -> (islinvertible opp x)).
  {
    unfold islinvertible. unfold isrinvertible. intro isr.
    apply (λ h : _, isweqhomot _ _ h isr).
    intro x0. apply is.
  }
  split with f.
  apply (isweqimplimpl f g (isapropisweq (λ x0 : X, opp x x0))
                       (isapropisweq (λ x0 : X, opp x0 x))).
Defined.

(* Lemma below currently requires X:hSet but should have a proof for X:UU *)

Lemma weqlunitrunit {X : hSet} (opp : binop X) (is : iscomm opp) (un0 : X) :
  (islunit opp un0) ≃ (isrunit opp un0).
Proof.
  intros.
  assert (f : (islunit opp un0) -> (isrunit opp un0)).
  {
    unfold islunit. unfold isrunit. intro isl. intro x.
    destruct (is un0 x). apply (isl x).
  }
  assert (g : (isrunit opp un0) -> (islunit opp un0)).
  {
    unfold islunit. unfold isrunit. intro isr. intro x.
    destruct (is x un0). apply (isr x).
  }
  split with f.
  apply (isweqimplimpl f g (isapropislunit opp un0) (isapropisrunit opp un0)).
Defined.

(* Same for the following lemma *)

Lemma weqlinvrinv {X : hSet} (opp : binop X) (is : iscomm opp) (un0 : X) (inv0 : X -> X) :
  (islinv opp un0 inv0) ≃ (isrinv opp un0 inv0).
Proof.
  intros.
  assert (f : (islinv opp un0 inv0) -> (isrinv opp un0 inv0)).
  {
    unfold islinv. unfold isrinv. intro isl. intro x.
    destruct (is (inv0 x) x). apply (isl x).
  }
  assert (g : (isrinv opp un0 inv0) -> (islinv opp un0 inv0)).
  {
    unfold islinv. unfold isrinv. intro isr. intro x.
    destruct (is x (inv0 x)). apply (isr x).
  }
  split with f.
  apply (isweqimplimpl f g (isapropislinv opp un0 inv0) (isapropisrinv opp un0 inv0)).
Defined.
Opaque abmonoidoprer.

(** *)

Definition isabgrop {X : UU} (opp : binop X) : UU := (isgrop opp) × (iscomm opp).

Definition mk_isabgrop {X : UU} {opp : binop X} (H1 : isgrop opp) (H2 : iscomm opp) :
  isabgrop opp := dirprodpair H1 H2.

Definition pr1isabgrop (X : UU) (opp : binop X) : isabgrop opp -> isgrop opp := @pr1 _ _.
Coercion pr1isabgrop : isabgrop >-> isgrop.

Definition isabgroptoisabmonoidop (X : UU) (opp : binop X) : isabgrop opp -> isabmonoidop opp :=
  λ is : _, dirprodpair (pr1 (pr1 is)) (pr2 is).
Coercion isabgroptoisabmonoidop : isabgrop >-> isabmonoidop.

Lemma isapropisabgrop {X : hSet} (opp : binop X) : isaprop (isabgrop opp).
Proof.
  intros.
  apply (isofhleveldirprod 1).
  apply isapropisgrop.
  apply isapropiscomm.
Defined.

(** **** Standard conditions on a pair of binary operations on a set *)

(** *)

Definition isldistr {X : UU} (opp1 opp2 : binop X) : UU :=
  ∏ x x' x'' : X, paths (opp2 x'' (opp1 x x')) (opp1 (opp2 x'' x) (opp2 x'' x')).

Lemma isapropisldistr {X : hSet} (opp1 opp2 : binop X) : isaprop (isldistr opp1 opp2).
Proof.
  intros.
  apply impred. intro x.
  apply impred. intro x'.
  apply impred. intro x''.
  simpl. apply (setproperty X).
Defined.

Definition isrdistr {X : UU} (opp1 opp2 : binop X) : UU :=
  ∏ x x' x'' : X, paths (opp2 (opp1 x x') x'') (opp1 (opp2 x x'') (opp2 x' x'')).

Lemma isapropisrdistr {X : hSet} (opp1 opp2 : binop X) : isaprop (isrdistr opp1 opp2).
Proof.
  intros.
  apply impred. intro x.
  apply impred. intro x'.
  apply impred. intro x''.
  simpl. apply (setproperty X).
Defined.

Definition isdistr {X : UU} (opp1 opp2 : binop X) : UU :=
  (isldistr opp1 opp2) × (isrdistr opp1 opp2).

Lemma isapropisdistr {X : hSet} (opp1 opp2 : binop X) : isaprop (isdistr opp1 opp2).
Proof.
  intros.
  apply (isofhleveldirprod 1 _ _ (isapropisldistr _ _) (isapropisrdistr _ _)).
Defined.

(** *)

Lemma weqldistrrdistr {X : hSet} (opp1 opp2 : binop X) (is : iscomm opp2) :
  (isldistr opp1 opp2) ≃ (isrdistr opp1 opp2).
Proof.
  intros.
  assert (f : (isldistr opp1 opp2) -> (isrdistr opp1 opp2)).
  {
    unfold isldistr. unfold isrdistr. intro isl. intros x x' x''.
    destruct (is x'' (opp1 x x')). destruct (is x'' x). destruct (is x'' x').
    apply (isl x x' x'').
  }
  assert (g : (isrdistr opp1 opp2) -> (isldistr opp1 opp2)).
  {
    unfold isldistr. unfold isrdistr. intro isr. intros x x' x''.
    destruct (is (opp1 x x') x''). destruct (is x x''). destruct (is x' x'').
    apply (isr x x' x'').
  }
  split with f.
  apply (isweqimplimpl f g (isapropisldistr opp1 opp2) (isapropisrdistr opp1 opp2)).
Defined.

(** *)

Definition isabsorb {X : UU} (opp1 opp2 : binop X) : UU :=
  ∏ x y : X, opp1 x (opp2 x y) = x.

Lemma isapropisabsorb {X : hSet} (opp1 opp2 : binop X) :
  isaprop (isabsorb opp1 opp2).
Proof.
  intros X opp1 opp2.
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply (setproperty X).
Defined.

(** *)

Definition isrigops {X : UU} (opp1 opp2 : binop X) : UU :=
  (∑ axs : (isabmonoidop opp1) × (ismonoidop opp2),
           (∏ x : X, (opp2 (unel_is (pr1 axs)) x) = (unel_is (pr1 axs)))
             × (∏ x : X, (opp2 x (unel_is (pr1 axs))) = (unel_is (pr1 axs))))
    × (isdistr opp1 opp2).

Definition mk_isrigops {X : hSet} {opp1 opp2 : binop X} (H1 : isabmonoidop opp1)
           (H2 : ismonoidop opp2) (H3 : ∏ x : X, (opp2 (unel_is H1) x) = (unel_is H1))
           (H4 : ∏ x : X, (opp2 x (unel_is H1)) = (unel_is H1))
           (H5 : isdistr opp1 opp2) : isrigops opp1 opp2 :=
  tpair _ (tpair _ (dirprodpair H1 H2) (dirprodpair H3 H4)) H5.

Definition rigop1axs_is {X : UU} {opp1 opp2 : binop X} :
  isrigops opp1 opp2 -> isabmonoidop opp1 := λ is : _, pr1 (pr1 (pr1 is)).

Definition rigop2axs_is {X : UU} {opp1 opp2 : binop X} : isrigops opp1 opp2 -> ismonoidop opp2 :=
  λ is : _, pr2 (pr1 (pr1 is)).

Definition rigdistraxs_is {X : UU} {opp1 opp2 : binop X} :
  isrigops opp1 opp2 -> isdistr opp1 opp2 := λ is : _,  pr2 is.

Definition rigldistrax_is {X : UU} {opp1 opp2 : binop X} :
  isrigops opp1 opp2 -> isldistr opp1 opp2 := λ is : _, pr1 (pr2 is).

Definition rigrdistrax_is {X : UU} {opp1 opp2 : binop X} :
  isrigops opp1 opp2 -> isrdistr opp1 opp2 := λ is : _, pr2 (pr2 is).

Definition rigunel1_is {X : UU} {opp1 opp2 : binop X} (is : isrigops opp1 opp2) : X :=
  pr1 (pr2 (pr1 (rigop1axs_is is))).

Definition rigunel2_is {X : UU} {opp1 opp2 : binop X} (is : isrigops opp1 opp2) : X :=
  (pr1 (pr2 (rigop2axs_is is))).

Definition rigmult0x_is {X : UU} {opp1 opp2 : binop X} (is : isrigops opp1 opp2) (x : X) :
  paths (opp2 (rigunel1_is is) x) (rigunel1_is is) := pr1 (pr2 (pr1 is)) x.

Definition rigmultx0_is {X : UU} {opp1 opp2 : binop X} (is : isrigops opp1 opp2) (x : X) :
  paths (opp2 x (rigunel1_is is)) (rigunel1_is is) := pr2 (pr2 (pr1 is)) x.

Lemma isapropisrigops {X : hSet} (opp1 opp2 : binop X) : isaprop (isrigops opp1 opp2).
Proof.
  intros.
  apply (isofhleveldirprod 1).
  - apply (isofhleveltotal2 1).
    + apply (isofhleveldirprod 1).
      * apply isapropisabmonoidop.
      * apply isapropismonoidop.
    + intro x. apply (isofhleveldirprod 1).
      * apply impred. intro x'.
        apply (setproperty X).
      * apply impred. intro x'.
        apply (setproperty X).
  - apply isapropisdistr.
Defined.

(** *)

Definition isrngops {X : UU} (opp1 opp2 : binop X) : UU :=
  dirprod ((isabgrop opp1) × (ismonoidop opp2)) (isdistr opp1 opp2).

Definition mk_isrngops {X : UU} {opp1 opp2 : binop X} (H1 : isabgrop opp1) (H2 : ismonoidop opp2)
           (H3 : isdistr opp1 opp2) : isrngops opp1 opp2 :=
  dirprodpair (dirprodpair H1 H2) H3.

Definition rngop1axs_is {X : UU} {opp1 opp2 : binop X} : isrngops opp1 opp2 -> isabgrop opp1 :=
  λ is : _, pr1 (pr1 is).

Definition rngop2axs_is {X : UU} {opp1 opp2 : binop X} : isrngops opp1 opp2 -> ismonoidop opp2 :=
  λ is : _, pr2 (pr1 is).

Definition rngdistraxs_is {X : UU} {opp1 opp2 : binop X} :
  isrngops opp1 opp2 -> isdistr opp1 opp2 := λ is : _, pr2 is.

Definition rngldistrax_is {X : UU} {opp1 opp2 : binop X} :
  isrngops opp1 opp2 -> isldistr opp1 opp2 := λ is : _, pr1 (pr2 is).

Definition rngrdistrax_is {X : UU} {opp1 opp2 : binop X} :
  isrngops opp1 opp2 -> isrdistr opp1 opp2 := λ is : _, pr2 (pr2 is).

Definition rngunel1_is {X : UU} {opp1 opp2 : binop X} (is : isrngops opp1 opp2) : X :=
  unel_is (pr1 (pr1 is)).

Definition rngunel2_is {X : UU} {opp1 opp2 : binop X} (is : isrngops opp1 opp2) : X :=
  unel_is (pr2 (pr1 is)).

Lemma isapropisrngops {X : hSet} (opp1 opp2 : binop X) : isaprop (isrngops opp1 opp2).
Proof.
  intros.
  apply (isofhleveldirprod 1).
  - apply (isofhleveldirprod 1).
    + apply isapropisabgrop.
    + apply isapropismonoidop.
  - apply isapropisdistr.
Defined.

Lemma multx0_is_l {X : UU} {opp1 opp2 : binop X} (is1 : isgrop opp1) (is2 : ismonoidop opp2)
      (is12 : isdistr opp1 opp2) : ∏ x : X, paths (opp2 x (unel_is (pr1 is1))) (unel_is (pr1 is1)).
Proof.
  intros.
  destruct is12 as [ ldistr0 rdistr0 ].
  destruct is2 as [ assoc2 [ un2 [ lun2 run2 ] ] ].
  simpl in *.
  apply (invmaponpathsweq (weqpair _ (isweqrmultingr_is is1 (opp2 x un2)))).
  simpl.
  destruct is1 as [ [ assoc1 [ un1 [ lun1 run1 ] ] ] [ inv0 [ linv0 rinv0 ] ] ].
  unfold unel_is. simpl in *.
  rewrite (lun1 (opp2 x un2)). destruct (ldistr0 un1 un2 x).
  rewrite (run2 x). rewrite (lun1 un2). rewrite (run2 x). apply idpath.
Defined.
Opaque multx0_is_l.

Lemma mult0x_is_l {X : UU} {opp1 opp2 : binop X} (is1 : isgrop opp1) (is2 : ismonoidop opp2)
      (is12 : isdistr opp1 opp2) : ∏ x : X, paths (opp2 (unel_is (pr1 is1)) x) (unel_is (pr1 is1)).
Proof.
  intros.
  destruct is12 as [ ldistr0 rdistr0 ].
  destruct is2 as [ assoc2 [ un2 [ lun2 run2 ] ] ]. simpl in *.
  apply (invmaponpathsweq (weqpair _ (isweqrmultingr_is is1 (opp2 un2 x)))).
  simpl.
  destruct is1 as [ [ assoc1 [ un1 [ lun1 run1 ] ] ] [ inv0 [ linv0 rinv0 ] ] ].
  unfold unel_is. simpl in *.
  rewrite (lun1 (opp2 un2 x)). destruct (rdistr0 un1 un2 x).
  rewrite (lun2 x). rewrite (lun1 un2). rewrite (lun2 x). apply idpath.
Defined.
Opaque mult0x_is_l.

Definition minus1_is_l {X : UU} {opp1 opp2 : binop X} (is1 : isgrop opp1)
           (is2 : ismonoidop opp2) := (grinv_is is1) (unel_is is2).

Lemma islinvmultwithminus1_is_l {X : UU} {opp1 opp2 : binop X}
      (is1 : isgrop opp1) (is2 : ismonoidop opp2) (is12 : isdistr opp1 opp2)
      (x : X) : paths (opp1 (opp2 (minus1_is_l is1 is2) x) x) (unel_is (pr1 is1)).
Proof.
  intros.
  set (xinv := opp2 (minus1_is_l is1 is2) x).
  rewrite (pathsinv0 (lunax_is is2 x)).
  unfold xinv.
  rewrite (pathsinv0 (pr2 is12 _ _ x)).
  unfold minus1_is_l. unfold grinv_is.
  rewrite (grlinvax_is is1 _). apply mult0x_is_l.
  - apply is2.
  - apply is12.
Defined.
Opaque islinvmultwithminus1_is_l.

Lemma isrinvmultwithminus1_is_l {X : UU} {opp1 opp2 : binop X} (is1 : isgrop opp1)
      (is2 : ismonoidop opp2) (is12 : isdistr opp1 opp2) (x : X) :
  paths (opp1 x (opp2 (minus1_is_l is1 is2) x)) (unel_is (pr1 is1)).
Proof.
  intros.
  set (xinv := opp2 (minus1_is_l is1 is2) x).
  rewrite (pathsinv0 (lunax_is is2 x)). unfold xinv.
  rewrite (pathsinv0 (pr2 is12 _ _ x)). unfold minus1_is_l. unfold grinv_is.
  rewrite (grrinvax_is is1 _).
  apply mult0x_is_l. apply is2. apply is12.
Defined.
Opaque isrinvmultwithminus1_is_l.

Lemma isminusmultwithminus1_is_l {X : UU} {opp1 opp2 : binop X} (is1 : isgrop opp1)
      (is2 : ismonoidop opp2) (is12 : isdistr opp1 opp2) (x : X) :
  paths (opp2 (minus1_is_l is1 is2) x) (grinv_is is1 x).
Proof.
  intros.
  apply (invmaponpathsweq (weqpair _ (isweqrmultingr_is is1 x))).
  simpl. rewrite (islinvmultwithminus1_is_l is1 is2 is12 x).
  unfold grinv_is. rewrite (grlinvax_is is1 x). apply idpath.
Defined.
Opaque isminusmultwithminus1_is_l.

Lemma isrngopsif {X : UU} {opp1 opp2 : binop X} (is1 : isgrop opp1) (is2 : ismonoidop opp2)
      (is12 : isdistr opp1 opp2) : isrngops opp1 opp2.
Proof.
  intros.
  set (assoc1 := pr1 (pr1 is1)).
  split.
  - split.
    + split with is1.
      intros x y.
      apply (invmaponpathsweq
               (weqpair _ (isweqrmultingr_is is1 (opp2 (minus1_is_l is1 is2) (opp1 x y))))).
      simpl. rewrite (isrinvmultwithminus1_is_l is1 is2 is12 (opp1 x y)).
      rewrite (pr1 is12 x y _).
      destruct (assoc1 (opp1 y x) (opp2 (minus1_is_l is1 is2) x) (opp2 (minus1_is_l is1 is2) y)).
      rewrite (assoc1 y x _).
      destruct (pathsinv0 (isrinvmultwithminus1_is_l is1 is2 is12 x)).
      unfold unel_is. rewrite (runax_is (pr1 is1) y).
      rewrite (isrinvmultwithminus1_is_l is1 is2 is12 y).
      apply idpath.
    + apply is2.
  - apply is12.
Defined.

Definition rngmultx0_is {X : UU} {opp1 opp2 : binop X} (is : isrngops opp1 opp2) :
  ∏ (x : X), opp2 x (unel_is (pr1 (rngop1axs_is is))) = unel_is (pr1 (rngop1axs_is is)) :=
  multx0_is_l (rngop1axs_is is) (rngop2axs_is is) (rngdistraxs_is is).

Definition rngmult0x_is {X : UU} {opp1 opp2 : binop X} (is : isrngops opp1 opp2) :
  ∏ (x : X), opp2 (unel_is (pr1 (rngop1axs_is is))) x = unel_is (pr1 (rngop1axs_is is)) :=
  mult0x_is_l (rngop1axs_is is) (rngop2axs_is is) (rngdistraxs_is is).

Definition rngminus1_is {X : UU} {opp1 opp2 : binop X} (is : isrngops opp1 opp2) : X :=
  minus1_is_l (rngop1axs_is is) (rngop2axs_is is).

Definition rngmultwithminus1_is {X : UU} {opp1 opp2 : binop X} (is : isrngops opp1 opp2) :
  ∏ (x : X),
  opp2 (minus1_is_l (rngop1axs_is is) (rngop2axs_is is)) x = grinv_is (rngop1axs_is is) x :=
  isminusmultwithminus1_is_l (rngop1axs_is is) (rngop2axs_is is) (rngdistraxs_is is).

Definition isrngopstoisrigops (X : UU) (opp1 opp2 : binop X) (is : isrngops opp1 opp2) :
  isrigops opp1 opp2.
Proof.
  intros. split.
  - split with (dirprodpair (isabgroptoisabmonoidop _ _ (rngop1axs_is is)) (rngop2axs_is is)).
    split.
    + simpl. apply (rngmult0x_is).
    + simpl. apply (rngmultx0_is).
  - apply (rngdistraxs_is is).
Defined.
Coercion isrngopstoisrigops : isrngops >-> isrigops.

(** *)

Definition iscommrigops {X : UU} (opp1 opp2 : binop X) : UU :=
  (isrigops opp1 opp2) × (iscomm opp2).

Definition pr1iscommrigops (X : UU) (opp1 opp2 : binop X) :
  iscommrigops opp1 opp2 -> isrigops opp1 opp2 := @pr1 _ _.
Coercion pr1iscommrigops : iscommrigops >-> isrigops.

Definition rigiscommop2_is {X : UU} {opp1 opp2 : binop X} (is : iscommrigops opp1 opp2) :
  iscomm opp2 := pr2 is.

Lemma isapropiscommrig {X : hSet} (opp1 opp2 : binop X) : isaprop (iscommrigops opp1 opp2).
Proof.
  intros.
  apply (isofhleveldirprod 1).
  - apply isapropisrigops.
  - apply isapropiscomm.
Defined.

(** *)

Definition iscommrngops {X : UU} (opp1 opp2 : binop X) : UU :=
  (isrngops opp1 opp2) × (iscomm opp2).

Definition pr1iscommrngops (X : UU) (opp1 opp2 : binop X) :
  iscommrngops opp1 opp2 -> isrngops opp1 opp2 := @pr1 _ _.
Coercion pr1iscommrngops : iscommrngops >-> isrngops.

Definition rngiscommop2_is {X : UU} {opp1 opp2 : binop X} (is : iscommrngops opp1 opp2) :
  iscomm opp2 := pr2 is.

Lemma isapropiscommrng {X : hSet} (opp1 opp2 : binop X) : isaprop (iscommrngops opp1 opp2).
Proof.
  intros.
  apply (isofhleveldirprod 1).
  - apply isapropisrngops.
  - apply isapropiscomm.
Defined.

Definition iscommrngopstoiscommrigops (X : UU) (opp1 opp2 : binop X)
           (is : iscommrngops opp1 opp2) : iscommrigops opp1 opp2 :=
  dirprodpair (isrngopstoisrigops _ _ _ (pr1 is)) (pr2 is).
Coercion iscommrngopstoiscommrigops : iscommrngops >-> iscommrigops.

(** **** Transfer properties of binary operations relative to weak equivalences *)

(** binop_weq_fwd *)

Lemma isassoc_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  isassoc opp → isassoc (binop_weq_fwd H opp).
Proof.
  intros X Y H opp is.
  intros x y z.
  apply (maponpaths H).
  refine (pathscomp0 _ (pathscomp0 (is _ _ _) _)).
  - apply (maponpaths (λ x, opp x _)).
    apply homotinvweqweq.
  - apply maponpaths.
    apply homotinvweqweq0.
Defined.

Lemma islunit_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (x0 : X) :
  islunit opp x0 → islunit (binop_weq_fwd H opp) (H x0).
Proof.
  intros X Y H opp x0 is.
  intros y.
  unfold binop_weq_fwd.
  refine (pathscomp0 (maponpaths _ _) _).
  - refine (pathscomp0 (maponpaths (λ x, opp x _) _) _).
    + apply homotinvweqweq.
    + apply is.
  - apply homotweqinvweq.
Defined.

Lemma isrunit_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (x0 : X) :
  isrunit opp x0 → isrunit (binop_weq_fwd H opp) (H x0).
Proof.
  intros X Y H opp x0 is.
  intros y.
  unfold binop_weq_fwd.
  refine (pathscomp0 (maponpaths _ _) _).
  - refine (pathscomp0 (maponpaths (opp _) _) _).
    + apply homotinvweqweq.
    + apply is.
  - apply homotweqinvweq.
Defined.

Lemma isunit_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (x0 : X) :
  isunit opp x0 → isunit (binop_weq_fwd H opp) (H x0).
Proof.
  intros X Y H opp x0 is.
  split.
  apply islunit_weq_fwd, (pr1 is).
  apply isrunit_weq_fwd, (pr2 is).
Defined.

Lemma isunital_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  isunital opp → isunital (binop_weq_fwd H opp).
Proof.
  intros X Y H opp is.
  exists (H (pr1 is)).
  apply isunit_weq_fwd, (pr2 is).
Defined.

Lemma ismonoidop_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  ismonoidop opp → ismonoidop (binop_weq_fwd H opp).
Proof.
  intros X Y H opp is.
  split.
  apply isassoc_weq_fwd, (pr1 is).
  apply isunital_weq_fwd, (pr2 is).
Defined.

Lemma islinv_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (x0 : X) (inv : X → X) :
  islinv opp x0 inv → islinv (binop_weq_fwd H opp) (H x0) (λ y : Y, H (inv (invmap H y))).
Proof.
  intros X Y H opp x0 inv is.
  intros y.
  unfold binop_weq_fwd.
  apply maponpaths.
  refine (pathscomp0 _ (is _)).
  apply (maponpaths (λ x, opp x _)).
  apply homotinvweqweq.
Defined.
Lemma isrinv_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (x0 : X) (inv : X → X) :
  isrinv opp x0 inv → isrinv (binop_weq_fwd H opp) (H x0) (λ y : Y, H (inv (invmap H y))).
Proof.
  intros X Y H opp x0 inv is.
  intros y.
  unfold binop_weq_fwd.
  apply maponpaths.
  refine (pathscomp0 _ (is _)).
  apply (maponpaths (opp _)).
  apply homotinvweqweq.
Defined.
Lemma isinv_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (x0 : X) (inv : X → X) :
  isinv opp x0 inv → isinv (binop_weq_fwd H opp) (H x0) (λ y : Y, H (inv (invmap H y))).
Proof.
  intros X Y H opp x0 inv is.
  split.
  apply islinv_weq_fwd, (pr1 is).
  apply isrinv_weq_fwd, (pr2 is).
Defined.
Lemma invstruct_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (is : ismonoidop opp) :
  invstruct opp is → invstruct (binop_weq_fwd H opp) (ismonoidop_weq_fwd H opp is).
Proof.
  intros X Y H opp is inv.
  exists (λ y : Y, H (pr1 inv (invmap H y))).
  apply isinv_weq_fwd, (pr2 inv).
Defined.

Lemma isgrop_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  isgrop opp → isgrop (binop_weq_fwd H opp).
Proof.
  intros X Y H opp is.
  mkpair.
  apply ismonoidop_weq_fwd, (pr1 is).
  apply invstruct_weq_fwd, (pr2 is).
Defined.

Lemma iscomm_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  iscomm opp → iscomm (binop_weq_fwd H opp).
Proof.
  intros X Y H opp is.
  intros x y.
  unfold binop_weq_fwd.
  apply maponpaths, is.
Defined.

Lemma isabmonoidop_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  isabmonoidop opp → isabmonoidop (binop_weq_fwd H opp).
Proof.
  intros X Y H opp is.
  split.
  apply ismonoidop_weq_fwd, (pr1 is).
  apply iscomm_weq_fwd, (pr2 is).
Defined.

Lemma isabgrop_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  isabgrop opp → isabgrop (binop_weq_fwd H opp).
Proof.
  intros X Y H opp is.
  split.
  apply isgrop_weq_fwd, (pr1 is).
  apply iscomm_weq_fwd, (pr2 is).
Defined.

Lemma isldistr_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  isldistr op1 op2 → isldistr (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intros X Y H op1 op2 is.
  intros x y z.
  unfold binop_weq_fwd.
  apply maponpaths.
  refine (pathscomp0 _ (pathscomp0 (is _ _ _) _)).
  - apply maponpaths.
    apply homotinvweqweq.
  - apply map_on_two_paths ; apply homotinvweqweq0.
Defined.
Lemma isrdistr_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  isrdistr op1 op2 → isrdistr (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intros X Y H op1 op2 is.
  intros x y z.
  unfold binop_weq_fwd.
  apply maponpaths.
  refine (pathscomp0 _ (pathscomp0 (is _ _ _) _)).
  - apply (maponpaths (λ x, op2 x _)).
    apply homotinvweqweq.
  - apply map_on_two_paths ; apply homotinvweqweq0.
Defined.

Lemma isdistr_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  isdistr op1 op2 → isdistr (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intros X Y H op1 op2 is.
  split.
  apply isldistr_weq_fwd, (pr1 is).
  apply isrdistr_weq_fwd, (pr2 is).
Defined.

Lemma isabsorb_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  isabsorb op1 op2 → isabsorb (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intros X Y H op1 op2 is.
  intros x y.
  unfold binop_weq_fwd.
  refine (pathscomp0 _ (homotweqinvweq H _)).
  apply maponpaths.
  refine (pathscomp0 _ (is _ _)).
  apply maponpaths.
  apply (homotinvweqweq H).
Defined.

Lemma isrigops_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  isrigops op1 op2 → isrigops (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intros X Y H op1 op2 is.
  split.
  - mkpair.
    + split.
      apply isabmonoidop_weq_fwd, (pr1 (pr1 (pr1 is))).
      apply ismonoidop_weq_fwd, (pr2 (pr1 (pr1 is))).
    + split ; simpl.
      * intros x.
        apply (maponpaths H).
        refine (pathscomp0 _ (pr1 (pr2 (pr1 is)) _)).
        apply (maponpaths (λ x, op2 x _)).
        apply homotinvweqweq.
      * intros x.
        apply (maponpaths H).
        refine (pathscomp0 _ (pr2 (pr2 (pr1 is)) _)).
        apply (maponpaths (op2 _)).
        apply homotinvweqweq.
  - apply isdistr_weq_fwd, (pr2 is).
Defined.

Lemma isrngops_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  isrngops op1 op2 → isrngops (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intros X Y H op1 op2 is.
  split.
  - split.
    + apply isabgrop_weq_fwd, (pr1 (pr1 is)).
    + apply ismonoidop_weq_fwd, (pr2 (pr1 is)).
  - apply isdistr_weq_fwd, (pr2 is).
Defined.

Lemma iscommrigops_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  iscommrigops op1 op2 → iscommrigops (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intros X Y H op1 op2 is.
  split.
  - apply isrigops_weq_fwd, (pr1 is).
  - apply iscomm_weq_fwd, (pr2 is).
Defined.

Lemma iscommrngops_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  iscommrngops op1 op2 → iscommrngops (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intros X Y H op1 op2 is.
  split.
  - apply isrngops_weq_fwd, (pr1 is).
  - apply iscomm_weq_fwd, (pr2 is).
Defined.

(** binop_weq_bck *)

Lemma isassoc_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  isassoc opp → isassoc (binop_weq_bck H opp).
Proof.
  intros X Y H opp is.
  intros x y z.
  apply (maponpaths (invmap H)).
  refine (pathscomp0 _ (pathscomp0 (is _ _ _) _)).
  - apply (maponpaths (λ x, opp x _)).
    apply homotweqinvweq.
  - apply maponpaths.
    apply pathsinv0, homotweqinvweq.
Defined.
Lemma islunit_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (x0 : Y) :
  islunit opp x0 → islunit (binop_weq_bck H opp) (invmap H x0).
Proof.
  intros X Y H opp x0 is.
  intros y.
  unfold binop_weq_bck.
  refine (pathscomp0 (maponpaths _ _) _).
  - refine (pathscomp0 (maponpaths (λ x, opp x _) _) _).
    + apply homotweqinvweq.
    + apply is.
  - apply homotinvweqweq.
Defined.
Lemma isrunit_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (x0 : Y) :
  isrunit opp x0 → isrunit (binop_weq_bck H opp) (invmap H x0).
Proof.
  intros X Y H opp x0 is.
  intros y.
  unfold binop_weq_bck.
  refine (pathscomp0 (maponpaths _ _) _).
  - refine (pathscomp0 (maponpaths (opp _) _) _).
    + apply homotweqinvweq.
    + apply is.
  - apply homotinvweqweq.
Defined.
Lemma isunit_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (x0 : Y) :
  isunit opp x0 → isunit (binop_weq_bck H opp) (invmap H x0).
Proof.
  intros X Y H opp x0 is.
  split.
  apply islunit_weq_bck, (pr1 is).
  apply isrunit_weq_bck, (pr2 is).
Defined.

Lemma isunital_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  isunital opp → isunital (binop_weq_bck H opp).
Proof.
  intros X Y H opp is.
  exists (invmap H (pr1 is)).
  apply isunit_weq_bck, (pr2 is).
Defined.

Lemma ismonoidop_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  ismonoidop opp → ismonoidop (binop_weq_bck H opp).
Proof.
  intros X Y H opp is.
  split.
  apply isassoc_weq_bck, (pr1 is).
  apply isunital_weq_bck, (pr2 is).
Defined.

Lemma islinv_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (x0 : Y) (inv : Y → Y) :
  islinv opp x0 inv → islinv (binop_weq_bck H opp) (invmap H x0) (λ y : X, invmap H (inv (H y))).
Proof.
  intros X Y H opp x0 inv is.
  intros y.
  unfold binop_weq_bck.
  apply maponpaths.
  refine (pathscomp0 _ (is _)).
  apply (maponpaths (λ x, opp x _)).
  apply homotweqinvweq.
Defined.
Lemma isrinv_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (x0 : Y) (inv : Y → Y) :
  isrinv opp x0 inv → isrinv (binop_weq_bck H opp) (invmap H x0) (λ y : X, invmap H (inv (H y))).
Proof.
  intros X Y H opp x0 inv is.
  intros y.
  unfold binop_weq_bck.
  apply maponpaths.
  refine (pathscomp0 _ (is _)).
  apply (maponpaths (opp _)).
  apply homotweqinvweq.
Defined.
Lemma isinv_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (x0 : Y) (inv : Y → Y) :
  isinv opp x0 inv → isinv (binop_weq_bck H opp) (invmap H x0) (λ y : X, invmap H (inv (H y))).
Proof.
  intros X Y H opp x0 inv is.
  split.
  apply islinv_weq_bck, (pr1 is).
  apply isrinv_weq_bck, (pr2 is).
Defined.
Lemma invstruct_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (is : ismonoidop opp) :
  invstruct opp is → invstruct (binop_weq_bck H opp) (ismonoidop_weq_bck H opp is).
Proof.
  intros X Y H opp is inv.
  exists (λ y : X, invmap H (pr1 inv (H y))).
  apply isinv_weq_bck, (pr2 inv).
Defined.

Lemma isgrop_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  isgrop opp → isgrop (binop_weq_bck H opp).
Proof.
  intros X Y H opp is.
  mkpair.
  apply ismonoidop_weq_bck, (pr1 is).
  apply invstruct_weq_bck, (pr2 is).
Defined.

Lemma iscomm_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  iscomm opp → iscomm (binop_weq_bck H opp).
Proof.
  intros X Y H opp is.
  intros x y.
  unfold binop_weq_bck.
  apply maponpaths, is.
Defined.

Lemma isabmonoidop_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  isabmonoidop opp → isabmonoidop (binop_weq_bck H opp).
Proof.
  intros X Y H opp is.
  split.
  apply ismonoidop_weq_bck, (pr1 is).
  apply iscomm_weq_bck, (pr2 is).
Defined.

Lemma isabgrop_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  isabgrop opp → isabgrop (binop_weq_bck H opp).
Proof.
  intros X Y H opp is.
  split.
  apply isgrop_weq_bck, (pr1 is).
  apply iscomm_weq_bck, (pr2 is).
Defined.

Lemma isldistr_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  isldistr op1 op2 → isldistr (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intros X Y H op1 op2 is.
  intros x y z.
  unfold binop_weq_bck.
  apply maponpaths.
  refine (pathscomp0 _ (pathscomp0 (is _ _ _) _)).
  - apply maponpaths.
    apply homotweqinvweq.
  - apply map_on_two_paths ; apply pathsinv0, homotweqinvweq.
Defined.
Lemma isrdistr_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  isrdistr op1 op2 → isrdistr (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intros X Y H op1 op2 is.
  intros x y z.
  unfold binop_weq_bck.
  apply maponpaths.
  refine (pathscomp0 _ (pathscomp0 (is _ _ _) _)).
  - apply (maponpaths (λ x, op2 x _)).
    apply homotweqinvweq.
  - apply map_on_two_paths ; apply pathsinv0, homotweqinvweq.
Defined.

Lemma isdistr_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  isdistr op1 op2 → isdistr (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intros X Y H op1 op2 is.
  split.
  apply isldistr_weq_bck, (pr1 is).
  apply isrdistr_weq_bck, (pr2 is).
Defined.

Lemma isabsorb_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  isabsorb op1 op2 → isabsorb (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intros X Y H op1 op2 is.
  intros x y.
  unfold binop_weq_bck.
  refine (pathscomp0 _ (homotinvweqweq H _)).
  apply maponpaths.
  refine (pathscomp0 _ (is _ _)).
  apply maponpaths.
  apply (homotweqinvweq H).
Defined.

Lemma isrigops_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  isrigops op1 op2 → isrigops (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intros X Y H op1 op2 is.
  split.
  - mkpair.
    + split.
      apply isabmonoidop_weq_bck, (pr1 (pr1 (pr1 is))).
      apply ismonoidop_weq_bck, (pr2 (pr1 (pr1 is))).
    + split ; simpl.
      * intros x.
        apply (maponpaths (invmap H)).
        refine (pathscomp0 _ (pr1 (pr2 (pr1 is)) _)).
        apply (maponpaths (λ x, op2 x _)).
        apply homotweqinvweq.
      * intros x.
        apply (maponpaths (invmap H)).
        refine (pathscomp0 _ (pr2 (pr2 (pr1 is)) _)).
        apply (maponpaths (op2 _)).
        apply homotweqinvweq.
  - apply isdistr_weq_bck, (pr2 is).
Defined.

Lemma isrngops_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  isrngops op1 op2 → isrngops (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intros X Y H op1 op2 is.
  split.
  - split.
    + apply isabgrop_weq_bck, (pr1 (pr1 is)).
    + apply ismonoidop_weq_bck, (pr2 (pr1 is)).
  - apply isdistr_weq_bck, (pr2 is).
Defined.

Lemma iscommrigops_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  iscommrigops op1 op2 → iscommrigops (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intros X Y H op1 op2 is.
  split.
  - apply isrigops_weq_bck, (pr1 is).
  - apply iscomm_weq_bck, (pr2 is).
Defined.

Lemma iscommrngops_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  iscommrngops op1 op2 → iscommrngops (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intros X Y H op1 op2 is.
  split.
  - apply isrngops_weq_bck, (pr1 is).
  - apply iscomm_weq_bck, (pr2 is).
Defined.


(** *** Sets with one binary operation *)

(** **** General definitions *)

Definition setwithbinop : UU := total2 (λ X : hSet, binop X).

Definition setwithbinoppair (X : hSet) (opp : binop X) : setwithbinop :=
  tpair (λ X : hSet, binop X) X opp.

Definition pr1setwithbinop : setwithbinop -> hSet := @pr1 _ (λ X : hSet, binop X).
Coercion pr1setwithbinop : setwithbinop >-> hSet.

Definition op {X : setwithbinop} : binop X := pr2 X.

Definition isasetbinoponhSet {X : hSet} : isaset (@binop X).
Proof.
  intros X.
  use impred_isaset. intros t1.
  use impred_isaset. intros t2.
  use setproperty.
Defined.
Opaque isasetbinoponhSet.

Notation "x + y" := (op x y) : addoperation_scope.
Notation "x * y" := (op x y) : multoperation_scope.


(** **** Functions compatible with a binary operation (homomorphisms) and their properties *)

Definition isbinopfun {X Y : setwithbinop} (f : X -> Y) : UU :=
  ∏ x x' : X, paths (f (op x x')) (op (f x) (f x')).

Definition mk_isbinopfun {X Y : setwithbinop} {f : X -> Y}
           (H : ∏ x x' : X, f (op x x') = op (f x) (f x')) : isbinopfun f := H.

Lemma isapropisbinopfun {X Y : setwithbinop} (f : X -> Y) : isaprop (isbinopfun f).
Proof.
  intros.
  apply impred. intro x.
  apply impred. intro x'.
  apply (setproperty Y).
Defined.

Definition isbinopfun_twooutof3b {A B C : setwithbinop} (f : A -> B) (g : B -> C)
           (H : issurjective f) : isbinopfun (g ∘ f)%functions -> isbinopfun f -> isbinopfun g.
Proof.
  intros A B C f g H H1 H2.
  use mk_isbinopfun.
  intros b1 b2.
  use (squash_to_prop (H b1) (@setproperty C _ _)). intros H1'.
  use (squash_to_prop (H b2) (@setproperty C _ _)). intros H2'.
  rewrite <- (hfiberpr2 _ _ H1'). rewrite <- (hfiberpr2 _ _ H2').
  use (pathscomp0
         (! (maponpaths (λ b : B, g b) (H2 (hfiberpr1 f b1 H1') (hfiberpr1 f b2 H2'))))).
  exact (H1 (hfiberpr1 f b1 H1') (hfiberpr1 f b2 H2')).
Qed.

Definition binopfun (X Y : setwithbinop) : UU := total2 (fun f : X -> Y => isbinopfun f).

Definition binopfunpair {X Y : setwithbinop} (f : X -> Y) (is : isbinopfun f) : binopfun X Y :=
  tpair _ f is.

Definition pr1binopfun (X Y : setwithbinop) : binopfun X Y -> (X -> Y) := @pr1 _ _.
Coercion pr1binopfun : binopfun >-> Funclass.

Definition binopfunisbinopfun {X Y : setwithbinop} (f : binopfun X Y) : isbinopfun f := pr2 f.

Lemma isasetbinopfun  (X Y : setwithbinop) : isaset (binopfun X Y).
Proof.
  intros.
  apply (isasetsubset (pr1binopfun X Y)).
  - change (isofhlevel 2 (X -> Y)).
    apply impred. intro.
    apply (setproperty Y).
  - refine (isinclpr1 _ _). intro.
    apply isapropisbinopfun.
Defined.

Lemma isbinopfuncomp {X Y Z : setwithbinop} (f : binopfun X Y) (g : binopfun Y Z) :
  isbinopfun (funcomp (pr1 f) (pr1 g)).
Proof.
  intros.
  set (axf := pr2 f). set (axg := pr2 g).
  intros a b. unfold funcomp.
  rewrite (axf a b). rewrite (axg (pr1 f a) (pr1 f b)).
  apply idpath.
Defined.
Opaque isbinopfuncomp.

Definition binopfuncomp {X Y Z : setwithbinop} (f : binopfun X Y) (g : binopfun Y Z) :
  binopfun X Z := binopfunpair (funcomp (pr1 f) (pr1 g)) (isbinopfuncomp f g).

Definition binopmono (X Y : setwithbinop) : UU := total2 (λ f : incl X Y, isbinopfun (pr1 f)).

Definition binopmonopair {X Y : setwithbinop} (f : incl X Y) (is : isbinopfun f) :
  binopmono X Y := tpair _  f is.

Definition pr1binopmono (X Y : setwithbinop) : binopmono X Y -> incl X Y := @pr1 _ _.
Coercion pr1binopmono : binopmono >-> incl.

Definition binopincltobinopfun (X Y : setwithbinop) :
  binopmono X Y -> binopfun X Y := λ f, binopfunpair (pr1 (pr1 f)) (pr2 f).
Coercion binopincltobinopfun : binopmono >-> binopfun.

Definition binopmonocomp {X Y Z : setwithbinop} (f : binopmono X Y) (g : binopmono Y Z) :
  binopmono X Z := binopmonopair (inclcomp (pr1 f) (pr1 g)) (isbinopfuncomp f g).

Definition binopiso (X Y : setwithbinop) : UU := total2 (λ f : X ≃ Y, isbinopfun f).

Definition binopisopair {X Y : setwithbinop} (f : X ≃ Y) (is : isbinopfun f) :
  binopiso X Y := tpair _  f is.

Definition pr1binopiso (X Y : setwithbinop) : binopiso X Y -> X ≃ Y := @pr1 _ _.
Coercion pr1binopiso : binopiso >-> weq.

Lemma isasetbinopiso (X Y : setwithbinop) : isaset (binopiso X Y).
Proof.
  intros X Y.
  use isaset_total2.
  - use isaset_total2.
    + use impred_isaset. intros t. use setproperty.
    + intros x. use isasetaprop. use isapropisweq.
  - intros w. use isasetaprop. use isapropisbinopfun.
Defined.
Opaque isasetbinopiso.

Definition binopisotobinopmono (X Y : setwithbinop) :
  binopiso X Y -> binopmono X Y := λ f, binopmonopair (pr1 f) (pr2 f).
Coercion binopisotobinopmono : binopiso >-> binopmono.

Definition binopisocomp {X Y Z : setwithbinop} (f : binopiso X Y) (g : binopiso Y Z) :
  binopiso X Z := binopisopair (weqcomp (pr1 f) (pr1 g)) (isbinopfuncomp f g).

Lemma isbinopfuninvmap {X Y : setwithbinop} (f : binopiso X Y) : isbinopfun (invmap (pr1 f)).
Proof.
  intros. set (axf := pr2 f). intros a b.
  apply (invmaponpathsweq (pr1 f)).
  rewrite (homotweqinvweq (pr1 f) (op a b)).
  rewrite (axf (invmap (pr1 f) a) (invmap (pr1 f) b)).
  rewrite (homotweqinvweq (pr1 f) a).
  rewrite (homotweqinvweq (pr1 f) b).
  apply idpath.
Defined.
Opaque isbinopfuninvmap.

Definition invbinopiso {X Y : setwithbinop} (f : binopiso X Y) :
  binopiso Y X := binopisopair (invweq (pr1 f)) (isbinopfuninvmap f).

Definition idbinopiso (X : setwithbinop) : binopiso X X.
Proof.
  intros X.
  use binopisopair.
  - exact (idweq X).
  - intros x1 x2. use idpath.
Defined.


(** **** (X = Y) ≃ (binopiso X Y)
   The idea is to use the composition (X = Y) ≃ (X ╝ Y) ≃ (binopiso X Y)
*)

Definition setwithbinop_univalence_weq1 (X Y : setwithbinop) : (X = Y) ≃ (X ╝ Y) :=
  total2_paths_equiv _ X Y.

Definition setwithbinop_univalence_weq2 (X Y : setwithbinop) : (X ╝ Y) ≃ (binopiso X Y).
Proof.
  intros X Y.
  use weqbandf.
  - use hSet_univalence.
  - intros e. use invweq. induction X as [X Xop]. induction Y as [Y Yop]. cbn in e.
    induction e. use weqimplimpl.
    + intros i.
      use funextfun. intros x1.
      use funextfun. intros x2.
      exact (i x1 x2).
    + intros e. change (Xop = Yop) in e. intros x1 x2. induction e. use idpath.
    + use isapropisbinopfun.
    + use isasetbinoponhSet.
Defined.

Definition setwithbinop_univalence_map (X Y : setwithbinop) : X = Y -> binopiso X Y.
Proof.
  intros X Y e. induction e. exact (idbinopiso X).
Defined.

Lemma setwithbinop_univalence_isweq (X Y : setwithbinop) :
  isweq (setwithbinop_univalence_map X Y).
Proof.
  intros X Y.
  use isweqhomot.
  - exact (weqcomp (setwithbinop_univalence_weq1 X Y) (setwithbinop_univalence_weq2 X Y)).
  - intros e. induction e. use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque setwithbinop_univalence_isweq.

Definition setwithbinop_univalence (X Y : setwithbinop) : (X = Y) ≃ (binopiso X Y).
Proof.
  intros X Y.
  use weqpair.
  - exact (setwithbinop_univalence_map X Y).
  - exact (setwithbinop_univalence_isweq X Y).
Defined.
Opaque setwithbinop_univalence.


(** **** hfiber and binop*)
Local Lemma hfiberbinop_path {A B : setwithbinop} (f : binopfun A B) (b1 b2 : B)
      (hf1 : hfiber (pr1 f) b1) (hf2 : hfiber (pr1 f) b2) :
  pr1 f (@op A (pr1 hf1) (pr1 hf2)) = (@op B b1 b2).
Proof.
  intros A B f b1 b2 hf1 hf2.
  use (pathscomp0 (binopfunisbinopfun f _ _)).
  rewrite <- (hfiberpr2 _ _ hf1). rewrite <- (hfiberpr2 _ _ hf2). use idpath.
Qed.

Definition hfiberbinop {A B : setwithbinop} (f : binopfun A B) (b1 b2 : B)
           (hf1 : hfiber (pr1 f) b1) (hf2 : hfiber (pr1 f) b2) :
  hfiber (pr1 f) (@op B b1 b2) :=
  hfiberpair (pr1 f) (@op A (pr1 hf1) (pr1 hf2)) (hfiberbinop_path f b1 b2 hf1 hf2).


(** **** Transport of properties of a binary operation  *)

Lemma islcancelablemonob {X Y : setwithbinop} (f : binopmono X Y) (x : X)
      (is : islcancelable (@op Y) (f x)) : islcancelable (@op X) x.
Proof.
  intros. unfold islcancelable.
  apply (isincltwooutof3a (λ x0 : X, op x x0) f (pr2 (pr1 f))).
  assert (h : homot (funcomp f (λ y0 : Y, op (f x) y0)) (funcomp (λ x0 : X, op x x0) f)).
  {
    intro x0. unfold funcomp. apply (pathsinv0 ((pr2 f) x x0)).
  }
  apply (isinclhomot _ _ h).
  apply (isinclcomp f (inclpair _ is)).
Defined.

Lemma isrcancelablemonob {X Y : setwithbinop} (f : binopmono X Y) (x : X)
      (is : isrcancelable (@op Y) (f x)) : isrcancelable (@op X) x.
Proof.
  intros. unfold islcancelable.
  apply (isincltwooutof3a (λ x0 : X, op x0 x) f (pr2 (pr1 f))).
  assert (h : homot (funcomp f (λ y0 : Y, op y0 (f x))) (funcomp (λ x0 : X, op x0 x) f)).
  {
    intro x0. unfold funcomp. apply (pathsinv0 ((pr2 f) x0 x)).
  }
  apply (isinclhomot _ _ h). apply (isinclcomp f (inclpair _ is)).
Defined.

Lemma iscancelablemonob {X Y : setwithbinop} (f : binopmono X Y) (x : X)
      (is : iscancelable (@op Y) (f x)) : iscancelable (@op X) x.
Proof.
  intros.
  apply (dirprodpair (islcancelablemonob f x (pr1 is)) (isrcancelablemonob f x (pr2 is))).
Defined.

Notation islcancelableisob := islcancelablemonob.
Notation isrcancelableisob := isrcancelablemonob.
Notation iscancelableisob := iscancelablemonob.

Lemma islinvertibleisob {X Y : setwithbinop} (f : binopiso X Y) (x : X)
      (is : islinvertible (@op Y) (f x)) : islinvertible (@op X) x.
Proof.
  intros. unfold islinvertible. apply (twooutof3a (λ x0 : X, op x x0) f).
  - assert (h : homot (funcomp f (λ y0 : Y, op (f x) y0)) (funcomp (λ x0 : X, op x x0) f)).
    {
      intro x0. unfold funcomp. apply (pathsinv0 ((pr2 f) x x0)).
    }
    apply (isweqhomot _ _ h). apply (pr2 (weqcomp f (weqpair _ is))).
  - apply (pr2 (pr1 f)).
Defined.

Lemma isrinvertibleisob {X Y : setwithbinop} (f : binopiso X Y) (x : X)
      (is : isrinvertible (@op Y) (f x)) : isrinvertible (@op X) x.
Proof.
  intros.
  unfold islinvertible. apply (twooutof3a (λ x0 : X, op x0 x) f).
  - assert (h : homot (funcomp f (λ y0 : Y, op y0 (f x))) (funcomp (λ x0 : X, op x0 x) f)).
    {
      intro x0. unfold funcomp. apply (pathsinv0 ((pr2 f) x0 x)).
    }
    apply (isweqhomot _ _ h). apply (pr2 (weqcomp f (weqpair _ is))).
  - apply (pr2 (pr1 f)).
Defined.

Lemma isinvertiblemonob {X Y : setwithbinop} (f : binopiso X Y) (x : X)
      (is : isinvertible (@op Y) (f x)) : isinvertible (@op X) x.
Proof.
  intros.
  apply (dirprodpair (islinvertibleisob f x (pr1 is)) (isrinvertibleisob f x (pr2 is))).
Defined.

Definition islinvertibleisof {X Y : setwithbinop} (f : binopiso X Y) (x : X)
           (is : islinvertible (@op X) x) : islinvertible (@op Y) (f x).
Proof.
  intros. unfold islinvertible. apply (twooutof3b f).
  - apply (pr2 (pr1 f)).
  - assert (h : homot (funcomp (λ x0 : X, op x x0) f) (λ x0 : X, op (f x) (f x0))).
    {
      intro x0. unfold funcomp. apply (pr2 f x x0).
    }
    apply (isweqhomot _ _ h). apply (pr2 (weqcomp (weqpair _ is) f)).
Defined.

Definition isrinvertibleisof {X Y : setwithbinop} (f : binopiso X Y) (x : X)
           (is : isrinvertible (@op X) x) : isrinvertible (@op Y) (f x).
Proof.
  intros. unfold isrinvertible. apply (twooutof3b f).
  - apply (pr2 (pr1 f)).
  - assert (h : homot (funcomp (λ x0 : X, op x0 x) f) (λ x0 : X, op (f x0) (f x))).
    {
      intro x0. unfold funcomp. apply (pr2 f x0 x).
    }
    apply (isweqhomot _ _ h). apply (pr2 (weqcomp (weqpair _ is) f)).
Defined.

Lemma isinvertiblemonof {X Y : setwithbinop} (f : binopiso X Y) (x : X)
      (is : isinvertible (@op X) x) : isinvertible (@op Y) (f x).
Proof.
  intros.
  apply (dirprodpair (islinvertibleisof f x (pr1 is)) (isrinvertibleisof f x (pr2 is))).
Defined.

Lemma isassocmonob {X Y : setwithbinop} (f : binopmono X Y) (is : isassoc (@op Y)) :
  isassoc (@op X).
Proof.
  intros.
  set (axf := pr2 f). simpl in axf. intros a b c.
  apply (invmaponpathsincl _ (pr2 (pr1 f))).
  rewrite (axf (op a b) c). rewrite (axf a b).
  rewrite (axf a (op b c)). rewrite (axf b c). apply is.
Defined.
Opaque isassocmonob.

Lemma iscommmonob {X Y : setwithbinop} (f : binopmono X Y) (is : iscomm (@op Y)) : iscomm (@op X).
Proof.
  intros. set (axf := pr2 f). simpl in axf. intros a b.
  apply (invmaponpathsincl _ (pr2 (pr1 f))).
  rewrite (axf a b). rewrite (axf b a). apply is.
Defined.
Opaque iscommmonob.

Notation isassocisob := isassocmonob.
Notation iscommisob := iscommmonob.

Lemma isassocisof {X Y : setwithbinop} (f : binopiso X Y) (is : isassoc (@op X)) : isassoc (@op Y).
Proof.
  intros. apply (isassocmonob (invbinopiso f) is).
Defined.
Opaque isassocisof.

Lemma iscommisof {X Y : setwithbinop} (f : binopiso X Y) (is : iscomm (@op X)) : iscomm (@op Y).
Proof.
  intros. apply (iscommmonob (invbinopiso f) is).
Defined.
Opaque iscommisof.

Lemma isunitisof {X Y : setwithbinop} (f : binopiso X Y) (unx : X) (is : isunit (@op X) unx) :
  isunit (@op Y) (f unx).
Proof.
  intros. set (axf := pr2 f). split.
  - intro a. change (f unx) with (pr1 f unx).
    apply (invmaponpathsweq (pr1 (invbinopiso f))).
    rewrite (pr2 (invbinopiso f) (pr1 f unx) a). simpl.
    rewrite (homotinvweqweq (pr1 f) unx). apply (pr1 is).
  - intro a. change (f unx) with (pr1 f unx).
    apply (invmaponpathsweq (pr1 (invbinopiso f))).
    rewrite (pr2 (invbinopiso f) a (pr1 f unx)). simpl.
    rewrite (homotinvweqweq (pr1 f) unx). apply (pr2 is).
Defined.
Opaque isunitisof.

Definition isunitalisof {X Y : setwithbinop} (f : binopiso X Y) (is : isunital (@op X)) :
  isunital (@op Y) := isunitalpair (f (pr1 is)) (isunitisof f (pr1 is) (pr2 is)).

Lemma isunitisob {X Y : setwithbinop} (f : binopiso X Y) (uny : Y) (is : isunit (@op Y) uny) :
  isunit (@op X) ((invmap f) uny).
Proof.
  intros. set (int := isunitisof (invbinopiso f)). simpl. simpl in int.
  apply int. apply is.
Defined.
Opaque isunitisob.

Definition isunitalisob {X Y : setwithbinop} (f : binopiso X Y) (is : isunital (@op Y)) :
  isunital (@op X) := isunitalpair ((invmap f) (pr1 is)) (isunitisob f (pr1 is) (pr2 is)).

Definition ismonoidopisof {X Y : setwithbinop} (f : binopiso X Y) (is : ismonoidop (@op X)) :
  ismonoidop (@op Y) := dirprodpair (isassocisof f (pr1 is)) (isunitalisof f (pr2 is)).

Definition ismonoidopisob {X Y : setwithbinop} (f : binopiso X Y) (is : ismonoidop (@op Y)) :
  ismonoidop (@op X) := dirprodpair (isassocisob f (pr1 is)) (isunitalisob f (pr2 is)).

Lemma isinvisof {X Y : setwithbinop} (f : binopiso X Y) (unx : X) (invx : X -> X)
      (is : isinv (@op X) unx invx) :
  isinv (@op Y) (pr1 f unx) (funcomp (invmap (pr1 f)) (funcomp invx (pr1 f))).
Proof.
  intros. set (axf := pr2 f). set (axinvf := pr2 (invbinopiso f)).
  simpl in axf. simpl in axinvf. unfold funcomp. split.
  - intro a. apply (invmaponpathsweq (pr1 (invbinopiso f))).
    simpl. rewrite (axinvf ((pr1 f) (invx (invmap (pr1 f) a))) a).
    rewrite (homotinvweqweq (pr1 f) unx).
    rewrite (homotinvweqweq (pr1 f) (invx (invmap (pr1 f) a))).
    apply (pr1 is).
  - intro a. apply (invmaponpathsweq (pr1 (invbinopiso f))).
    simpl. rewrite (axinvf a ((pr1 f) (invx (invmap (pr1 f) a)))).
    rewrite (homotinvweqweq (pr1 f) unx).
    rewrite (homotinvweqweq (pr1 f) (invx (invmap (pr1 f) a))).
    apply (pr2 is).
Defined.
Opaque isinvisof.

Definition isgropisof {X Y : setwithbinop} (f : binopiso X Y) (is : isgrop (@op X)) :
  isgrop (@op Y) := tpair _ (ismonoidopisof f is)
                          (tpair _ (funcomp (invmap (pr1 f)) (funcomp (grinv_is is) (pr1 f)))
                                 (isinvisof f (unel_is is) (grinv_is is) (pr2 (pr2 is)))).

Lemma isinvisob {X Y : setwithbinop} (f : binopiso X Y) (uny : Y) (invy : Y -> Y)
      (is : isinv (@op Y) uny invy) : isinv (@op X) (invmap (pr1 f) uny)
                                            (funcomp (pr1 f) (funcomp invy (invmap (pr1 f)))).
Proof.
  intros. apply (isinvisof (invbinopiso f) uny invy is).
Defined.
Opaque isinvisob.

Definition isgropisob {X Y : setwithbinop} (f : binopiso X Y) (is : isgrop (@op Y)) :
  isgrop (@op X) := tpair _ (ismonoidopisob f is)
                          (tpair _  (funcomp (pr1 f) (funcomp (grinv_is is) (invmap (pr1 f))))
                                 (isinvisob f (unel_is is) (grinv_is is) (pr2 (pr2 is)))).

Definition isabmonoidopisof {X Y : setwithbinop} (f : binopiso X Y) (is : isabmonoidop (@op X)) :
  isabmonoidop (@op Y) := tpair _ (ismonoidopisof f is) (iscommisof f (commax_is is)).

Definition isabmonoidopisob {X Y : setwithbinop} (f : binopiso X Y) (is : isabmonoidop (@op Y)) :
  isabmonoidop (@op X) := tpair _ (ismonoidopisob f is) (iscommisob f (commax_is is)).

Definition isabgropisof {X Y : setwithbinop} (f : binopiso X Y) (is : isabgrop (@op X)) :
  isabgrop (@op Y) := tpair _ (isgropisof f is) (iscommisof f (commax_is is)).

Definition isabgropisob {X Y : setwithbinop} (f : binopiso X Y) (is : isabgrop (@op Y)) :
  isabgrop (@op X) := tpair _ (isgropisob f is) (iscommisob f (commax_is is)).


(** **** Subobjects *)

Definition issubsetwithbinop {X : hSet} (opp : binop X) (A : hsubtype X) : UU :=
  ∏ a a' : A, A (opp (pr1 a) (pr1 a')).

Lemma isapropissubsetwithbinop {X : hSet} (opp : binop X) (A : hsubtype X) :
  isaprop (issubsetwithbinop opp A).
Proof.
  intros.
  apply impred. intro a.
  apply impred. intros a'.
  apply (pr2 (A (opp (pr1 a) (pr1 a')))).
Defined.

Definition subsetswithbinop {X : setwithbinop} : UU :=
  total2 (λ A : hsubtype X, issubsetwithbinop (@op X) A).

Definition subsetswithbinoppair {X : setwithbinop} :
  ∏ (t : hsubtype X), (λ A : hsubtype X, issubsetwithbinop op A) t →
                       ∑ A : hsubtype X, issubsetwithbinop op A :=
  tpair (λ A : hsubtype X, issubsetwithbinop (@op X) A).

Definition subsetswithbinopconstr {X : setwithbinop} :
  ∏ (t : hsubtype X), (λ A : hsubtype X, issubsetwithbinop op A) t →
                       ∑ A : hsubtype X, issubsetwithbinop op A := @subsetswithbinoppair X.

Definition pr1subsetswithbinop (X : setwithbinop) : @subsetswithbinop X -> hsubtype X :=
  @pr1 _ (λ A : hsubtype X, issubsetwithbinop (@op X) A).
Coercion pr1subsetswithbinop : subsetswithbinop >-> hsubtype.

Definition pr2subsetswithbinop {X : setwithbinop} (Y : @subsetswithbinop X) :
  issubsetwithbinop (@op X) (pr1subsetswithbinop X Y) := pr2 Y.

Definition totalsubsetwithbinop (X : setwithbinop) : @subsetswithbinop X.
Proof.
  intros. split with (λ x : X, htrue). intros x x'. apply tt.
Defined.

Definition carrierofasubsetwithbinop {X : setwithbinop} (A : @subsetswithbinop X) : setwithbinop.
Proof.
  intros.
  set (aset := (hSetpair (carrier A) (isasetsubset (pr1carrier A) (setproperty X)
                                                   (isinclpr1carrier A))) : hSet).
  split with aset.
  set (subopp := (λ a a' : A, carrierpair A (op (pr1carrier _ a) (pr1carrier _ a')) (pr2 A a a')) :
                   (A -> A -> A)).
  simpl. unfold binop. apply subopp.
Defined.
Coercion carrierofasubsetwithbinop : subsetswithbinop >-> setwithbinop.


(** **** Relations compatible with a binary operation and quotient objects *)

Definition isbinophrel {X : setwithbinop} (R : hrel X) : UU :=
  dirprod (∏ a b c : X, R a b -> R (op c a) (op c b)) (∏ a b c : X, R a b -> R (op a c) (op b c)).

Definition isbinophrellogeqf {X : setwithbinop} {L R : hrel X}
           (lg : hrellogeq L R) (isl : isbinophrel L) : isbinophrel R.
Proof.
  intros. split.
  - intros a b c rab.
    apply ((pr1 (lg _ _) ((pr1 isl) _ _ _ (pr2 (lg  _ _) rab)))).
  - intros a b c rab.
    apply ((pr1 (lg _ _) ((pr2 isl) _ _ _ (pr2 (lg  _ _) rab)))).
Defined.

Lemma isapropisbinophrel {X : setwithbinop} (R : hrel X) : isaprop (isbinophrel R).
Proof.
  intros. apply isapropdirprod.
  - apply impred. intro a.
    apply impred. intro b.
    apply impred. intro c.
    apply impred. intro r.
    apply (pr2 (R _ _)).
  - apply impred. intro a.
    apply impred. intro b.
    apply impred. intro c.
    apply impred. intro r.
    apply (pr2 (R _ _)).
Defined.

Lemma isbinophrelif {X : setwithbinop} (R : hrel X) (is : iscomm (@op X))
      (isl : ∏ a b c : X, R a b -> R (op c a) (op c b)) : isbinophrel R.
Proof.
  intros. split with isl. intros a b c rab.
  destruct (is c a). destruct (is c b). apply (isl _ _ _ rab).
Defined.

Lemma iscompbinoptransrel {X : setwithbinop} (R : hrel X) (ist : istrans R) (isb : isbinophrel R) :
  iscomprelrelfun2 R R (@op X).
Proof.
  intros. intros a b c d. intros rab rcd.
  set (racbc := pr2 isb a b c rab). set (rbcbd := pr1 isb c d b rcd).
  apply (ist _ _ _ racbc rbcbd).
Defined.

Lemma isbinopreflrel {X : setwithbinop} (R : hrel X) (isr : isrefl R)
      (isb : iscomprelrelfun2 R R (@op X)) : isbinophrel R.
Proof.
  intros. split.
  - intros a b c rab. apply (isb c c a b (isr c) rab).
  - intros a b c rab. apply (isb a b c c rab (isr c)).
Defined.

Definition binophrel {X : setwithbinop} : UU := total2 (λ R : hrel X, isbinophrel R).

Definition binophrelpair {X : setwithbinop} :
  ∏ (t : hrel X), (λ R : hrel X, isbinophrel R) t → ∑ R : hrel X, isbinophrel R :=
  tpair (λ R : hrel X, isbinophrel R).

Definition pr1binophrel (X : setwithbinop) : @binophrel X -> hrel X :=
  @pr1 _ (λ R : hrel X, isbinophrel R).
Coercion pr1binophrel : binophrel >-> hrel.

Definition binoppo {X : setwithbinop} : UU := total2 (λ R : po X, isbinophrel R).

Definition binoppopair {X : setwithbinop} :
  ∏ (t : po X), (λ R : po X, isbinophrel R) t → ∑ R : po X, isbinophrel R :=
  tpair (λ R : po X, isbinophrel R).

Definition pr1binoppo (X : setwithbinop) : @binoppo X -> po X := @pr1 _ (λ R : po X, isbinophrel R).
Coercion pr1binoppo : binoppo >-> po.

Definition binopeqrel {X : setwithbinop} : UU := total2 (λ R : eqrel X, isbinophrel R).

Definition binopeqrelpair {X : setwithbinop} :
  ∏ (t : eqrel X), (λ R : eqrel X, isbinophrel R) t → ∑ R : eqrel X, isbinophrel R :=
  tpair (λ R : eqrel X, isbinophrel R).

Definition pr1binopeqrel (X : setwithbinop) : @binopeqrel X -> eqrel X :=
  @pr1 _ (λ R : eqrel X, isbinophrel R).
Coercion pr1binopeqrel : binopeqrel >-> eqrel.

Definition setwithbinopquot {X : setwithbinop} (R : @binopeqrel X) : setwithbinop.
Proof.
  intros. split with (setquotinset R).
  set (qt  := setquot R). set (qtset := setquotinset R).
  assert (iscomp : iscomprelrelfun2 R R op) by apply (iscompbinoptransrel R (eqreltrans R) (pr2 R)).
  set (qtmlt := setquotfun2 R R op iscomp).
  simpl. unfold binop. apply qtmlt.
Defined.

Definition ispartbinophrel {X : setwithbinop} (S : hsubtype X) (R : hrel X) : UU :=
  dirprod (∏ a b c : X, S c -> R a b -> R (op c a) (op c b))
          (∏ a b c : X, S c -> R a b -> R (op a c) (op b c)).
Lemma isaprop_ispartbinophrel {X : setwithbinop} (S : hsubtype X) (R : hrel X) :
  isaprop (ispartbinophrel S R).
Proof.
  intros X S R.
  apply isapropdirprod ;
  apply impred_isaprop ; intros a ;
  apply impred_isaprop ; intros b ;
  apply impred_isaprop ; intros c ;
  apply isapropimpl, isapropimpl, propproperty.
Defined.

Definition isbinoptoispartbinop {X : setwithbinop} (S : hsubtype X) (L : hrel X)
           (is : isbinophrel L) : ispartbinophrel S L.
Proof.
  intros X S L.
  unfold isbinophrel. unfold ispartbinophrel. intro d2. split.
  - intros a b c is. apply (pr1 d2 a b c).
  - intros a b c is. apply (pr2 d2 a b c).
Defined.

Definition ispartbinophrellogeqf {X : setwithbinop} (S : hsubtype X) {L R : hrel X}
           (lg : hrellogeq L R) (isl : ispartbinophrel S L) : ispartbinophrel S R.
Proof.
  intros. split.
  - intros a b c is rab.
    apply ((pr1 (lg _ _) ((pr1 isl) _ _ _ is (pr2 (lg _ _) rab)))).
  - intros a b c is rab.
    apply ((pr1 (lg _ _) ((pr2 isl) _ _ _ is (pr2 (lg  _ _) rab)))).
Defined.

Lemma ispartbinophrelif {X : setwithbinop} (S : hsubtype X) (R : hrel X) (is : iscomm (@op X))
      (isl : ∏ a b c : X, S c -> R a b -> R (op c a) (op c b)) : ispartbinophrel S R.
Proof.
  intros. split with isl.
  intros a b c s rab. destruct (is c a). destruct (is c b).
  apply (isl _ _ _ s rab).
Defined.


(** **** Relations inversely compatible with a binary operation *)

Definition isinvbinophrel {X : setwithbinop} (R : hrel X) : UU :=
  dirprod (∏ a b c : X, R (op c a) (op c b) ->  R a b) (∏ a b c : X, R (op a c) (op b c) -> R a b).

Definition isinvbinophrellogeqf {X : setwithbinop} {L R : hrel X} (lg : hrellogeq L R)
           (isl : isinvbinophrel L) : isinvbinophrel R.
Proof.
  intros. split.
  - intros a b c rab.
    apply ((pr1 (lg _ _) ((pr1 isl) _ _ _ (pr2 (lg  _ _) rab)))).
  - intros a b c rab.
    apply ((pr1 (lg _ _) ((pr2 isl) _ _ _ (pr2 (lg  _ _) rab)))).
Defined.

Lemma isapropisinvbinophrel {X : setwithbinop} (R : hrel X) : isaprop (isinvbinophrel R).
Proof.
  intros. apply isapropdirprod.
  - apply impred. intro a.
    apply impred. intro b.
    apply impred. intro c.
    apply impred. intro r.
    apply (pr2 (R _ _)).
  - apply impred. intro a.
    apply impred. intro b.
    apply impred. intro c.
    apply impred. intro r.
    apply (pr2 (R _ _)).
Defined.

Lemma isinvbinophrelif {X : setwithbinop} (R : hrel X) (is : iscomm (@op X))
      (isl : ∏ a b c : X,  R (op c a) (op c b) -> R a b) : isinvbinophrel R.
Proof.
  intros. split with isl. intros a b c rab.
  destruct (is c a). destruct (is c b).
  apply (isl _ _ _ rab).
Defined.

Definition ispartinvbinophrel {X : setwithbinop} (S : hsubtype X) (R : hrel X) : UU :=
  dirprod (∏ a b c : X, S c -> R (op c a) (op c b) -> R a b)
          (∏ a b c : X, S c -> R (op a c) (op b c) -> R a b).

Definition isinvbinoptoispartinvbinop {X : setwithbinop} (S : hsubtype X) (L : hrel X)
           (is : isinvbinophrel L) : ispartinvbinophrel S L.
Proof.
  intros X S L.
  unfold isinvbinophrel. unfold ispartinvbinophrel. intro d2.
  split.
  - intros a b c s. apply (pr1 d2 a b c).
  - intros a b c s. apply (pr2 d2 a b c).
Defined.

Definition ispartinvbinophrellogeqf {X : setwithbinop} (S : hsubtype X) {L R : hrel X}
           (lg : hrellogeq L R) (isl : ispartinvbinophrel S L) : ispartinvbinophrel S R.
Proof.
  intros. split.
  - intros a b c s rab.
    apply ((pr1 (lg _ _) ((pr1 isl) _ _ _ s (pr2 (lg  _ _) rab)))).
  - intros a b c s rab.
    apply ((pr1 (lg _ _) ((pr2 isl) _ _ _ s (pr2 (lg  _ _) rab)))).
Defined.

Lemma ispartinvbinophrelif {X : setwithbinop} (S : hsubtype X) (R : hrel X) (is : iscomm (@op X))
      (isl : ∏ a b c : X, S c -> R (op c a) (op c b) -> R a b) : ispartinvbinophrel S R.
Proof.
  intros. split with isl. intros a b c s rab.
  destruct (is c a). destruct (is c b).
  apply (isl _ _ _ s rab).
Defined.


(** **** Homomorphisms and relations *)

Lemma binophrelandfun {X Y : setwithbinop} (f : binopfun X Y) (R : hrel Y) (is : @isbinophrel Y R) :
  @isbinophrel X (λ x x', R (f x) (f x')).
Proof.
  intros.
  set (ish := (pr2 f) : ∏ a0 b0, paths (f (op a0 b0)) (op (f a0) (f b0))).
  split.
  - intros a b c r. rewrite (ish _ _). rewrite (ish _ _).
    apply (pr1 is). apply r.
  - intros a b c r. rewrite (ish _ _). rewrite (ish _ _).
    apply (pr2 is). apply r.
Defined.

Lemma ispartbinophrelandfun {X Y : setwithbinop} (f : binopfun X Y) (SX : hsubtype X)
      (SY : hsubtype Y) (iss : ∏ x : X, (SX x) -> (SY (f x))) (R : hrel Y)
      (is : @ispartbinophrel Y SY R) : @ispartbinophrel X SX (λ x x', R (f x) (f x')).
Proof.
  intros.
  set (ish := (pr2 f) : ∏ a0 b0, paths (f (op a0 b0)) (op (f a0) (f b0))).
  split.
  - intros a b c s r. rewrite (ish _ _). rewrite (ish _ _).
    apply ((pr1 is) _ _ _ (iss _ s) r).
  - intros a b c s r. rewrite (ish _ _). rewrite (ish _ _).
    apply ((pr2 is) _ _ _ (iss _ s) r).
Defined.

Lemma invbinophrelandfun {X Y : setwithbinop} (f : binopfun X Y) (R : hrel Y)
      (is : @isinvbinophrel Y R) : @isinvbinophrel X (λ x x', R (f x) (f x')).
Proof.
  intros.
  set (ish := (pr2 f) : ∏ a0 b0, paths (f (op a0 b0)) (op (f a0) (f b0))).
  split.
  - intros a b c r. rewrite (ish _ _) in r. rewrite (ish _ _) in r.
    apply ((pr1 is) _ _ _ r).
  - intros a b c r. rewrite (ish _ _) in r. rewrite (ish _ _) in r.
    apply ((pr2 is) _ _ _ r).
Defined.

Lemma ispartinvbinophrelandfun {X Y : setwithbinop} (f : binopfun X Y) (SX : hsubtype X)
      (SY : hsubtype Y) (iss : ∏ x : X, (SX x) -> (SY (f x))) (R : hrel Y)
      (is : @ispartinvbinophrel Y SY R) : @ispartinvbinophrel X SX (λ x x', R (f x) (f x')).
Proof.
  intros.
  set (ish := (pr2 f) : ∏ a0 b0, paths (f (op a0 b0)) (op (f a0) (f b0))).
  split.
  - intros a b c s r. rewrite (ish _ _) in r. rewrite (ish _ _) in r.
    apply ((pr1 is) _ _ _ (iss _ s) r).
  - intros a b c s r. rewrite (ish _ _) in r. rewrite (ish _ _) in r.
    apply ((pr2 is) _ _ _ (iss _ s) r).
Defined.


(** **** Quotient relations *)

Lemma isbinopquotrel {X : setwithbinop} (R : @binopeqrel X) {L : hrel X} (is : iscomprelrel R L)
      (isl : isbinophrel L) : @isbinophrel (setwithbinopquot R) (quotrel is).
Proof.
  intros. unfold isbinophrel. split.
  - assert (int : ∏ (a b c : setwithbinopquot R),
                  isaprop (quotrel is a b -> quotrel is (op c a) (op c b))).
    {
      intros a b c. apply impred. intro. apply (pr2 (quotrel is _ _)).
    }
    apply (setquotuniv3prop R (λ a b c, hProppair _ (int a b c))).
    exact (pr1 isl).
  - assert (int : ∏ (a b c : setwithbinopquot R),
                  isaprop (quotrel is a b -> quotrel is (op a c) (op b c))).
    {
      intros a b c. apply impred. intro. apply (pr2 (quotrel is _ _)).
    }
    apply (setquotuniv3prop R (λ a b c, hProppair _ (int a b c))).
    exact (pr2 isl).
Defined.


(** **** Direct products *)

Definition setwithbinopdirprod (X Y : setwithbinop) : setwithbinop.
Proof.
  intros. split with (setdirprod X Y). unfold binop. simpl.
  (* ??? in 8.4-8.5-trunk the following apply generates an error message if the
     type of xy and xy' is left as _ despite the fact that the type of goal is
     dirprod X Y -> dirprod X Y ->.. *)
  apply (λ xy xy' : dirprod X Y, dirprodpair (op (pr1 xy) (pr1 xy')) (op (pr2 xy) (pr2 xy'))).
Defined.


(** *** Sets with two binary operations *)

(** **** General definitions *)

Definition setwith2binop : UU := total2 (λ X : hSet, (binop X) × (binop X)).

Definition setwith2binoppair (X : hSet) (opps : (binop X) × (binop X)) :
  setwith2binop := tpair (λ X : hSet, (binop X) × (binop X)) X opps.

Definition pr1setwith2binop : setwith2binop -> hSet :=
  @pr1 _ (λ X : hSet, (binop X) × (binop X)).
Coercion pr1setwith2binop : setwith2binop >-> hSet.

Definition op1 {X : setwith2binop} : binop X := pr1 (pr2 X).

Definition op2 {X : setwith2binop} : binop X := pr2 (pr2 X).

Definition setwithbinop1 (X : setwith2binop) : setwithbinop := setwithbinoppair (pr1 X) (@op1 X).

Definition setwithbinop2 (X : setwith2binop) : setwithbinop := setwithbinoppair (pr1 X) (@op2 X).

Notation "x + y" := (op1 x y) : twobinops_scope.
Notation "x * y" := (op2 x y) : twobinops_scope.

Definition isasettwobinoponhSet {X : hSet} : isaset ((binop X) × (binop X)).
Proof.
  intros X.
  use isasetdirprod.
  - use isasetbinoponhSet.
  - use isasetbinoponhSet.
Defined.
Opaque isasettwobinoponhSet.


(** **** Functions compatible with a pair of binary operation (homomorphisms) and their properties *)

Definition istwobinopfun {X Y : setwith2binop} (f : X -> Y) : UU :=
  dirprod (∏ x x' : X, paths (f (op1 x x')) (op1 (f x) (f x')))
          (∏ x x' : X, paths (f (op2 x x')) (op2 (f x) (f x'))).

Definition mk_istwobinopfun {X Y : setwith2binop} (f : X -> Y)
           (H1 : ∏ x x' : X, paths (f (op1 x x')) (op1 (f x) (f x')))
           (H2 : ∏ x x' : X, paths (f (op2 x x')) (op2 (f x) (f x'))) :
  istwobinopfun f := dirprodpair H1 H2.

Lemma isapropistwobinopfun {X Y : setwith2binop} (f : X -> Y) : isaprop (istwobinopfun f).
Proof.
  intros. apply isofhleveldirprod.
  - apply impred. intro x.
    apply impred. intro x'.
    apply (setproperty Y).
  - apply impred. intro x.
    apply impred. intro x'.
    apply (setproperty Y).
Defined.

Definition twobinopfun (X Y : setwith2binop) : UU := total2 (fun f : X -> Y => istwobinopfun f).

Definition twobinopfunpair {X Y : setwith2binop} (f : X -> Y) (is : istwobinopfun f) :
  twobinopfun X Y := tpair _ f is.

Definition pr1twobinopfun (X Y : setwith2binop) : twobinopfun X Y -> (X -> Y) := @pr1 _ _.
Coercion pr1twobinopfun : twobinopfun >-> Funclass.

Definition binop1fun {X Y : setwith2binop} (f : twobinopfun X Y) :
  binopfun (setwithbinop1 X) (setwithbinop1 Y) :=
  @binopfunpair (setwithbinop1 X) (setwithbinop1 Y) (pr1 f) (pr1 (pr2 f)).

Definition binop2fun {X Y : setwith2binop} (f : twobinopfun X Y) :
  binopfun (setwithbinop2 X) (setwithbinop2 Y) :=
  @binopfunpair (setwithbinop2 X) (setwithbinop2 Y) (pr1 f) (pr2 (pr2 f)).

Definition twobinopfun_paths {X Y : setwith2binop} (f g : twobinopfun X Y)
           (e : pr1 f = pr1 g) : f = g.
Proof.
  intros X Y f g e.
  use total2_paths_f.
  - exact e.
  - use proofirrelevance. use isapropistwobinopfun.
Defined.
Opaque twobinopfun_paths.

Lemma isasettwobinopfun  (X Y : setwith2binop) : isaset (twobinopfun X Y).
Proof.
  intros.
  apply (isasetsubset (pr1twobinopfun X Y)).
  - change (isofhlevel 2 (X -> Y)).
    apply impred. intro. apply (setproperty Y).
  - refine (isinclpr1 _ _). intro. apply isapropistwobinopfun.
Defined.
Opaque isasettwobinopfun.

Lemma istwobinopfuncomp {X Y Z : setwith2binop} (f : twobinopfun X Y) (g : twobinopfun Y Z) :
  istwobinopfun (funcomp (pr1 f) (pr1 g)).
Proof.
  intros.
  set (ax1f := pr1 (pr2 f)). set (ax2f := pr2 (pr2 f)).
  set (ax1g := pr1 (pr2 g)). set (ax2g := pr2 (pr2 g)).
  split.
  - intros a b. unfold funcomp.
    rewrite (ax1f a b). rewrite (ax1g (pr1 f a) (pr1 f b)).
    apply idpath.
  - intros a b. unfold funcomp.
    rewrite (ax2f a b). rewrite (ax2g (pr1 f a) (pr1 f b)).
    apply idpath.
Defined.
Opaque istwobinopfuncomp.

Definition twobinopfuncomp {X Y Z : setwith2binop} (f : twobinopfun X Y) (g : twobinopfun Y Z) :
  twobinopfun X Z := twobinopfunpair (funcomp (pr1 f) (pr1 g)) (istwobinopfuncomp f g).

Definition twobinopmono (X Y : setwith2binop) : UU := total2 (λ f : incl X Y, istwobinopfun f).

Definition twobinopmonopair {X Y : setwith2binop} (f : incl X Y) (is : istwobinopfun f) :
  twobinopmono X Y := tpair _  f is.

Definition pr1twobinopmono (X Y : setwith2binop) : twobinopmono X Y -> incl X Y := @pr1 _ _.
Coercion pr1twobinopmono : twobinopmono >-> incl.

Definition twobinopincltotwobinopfun (X Y : setwith2binop) :
  twobinopmono X Y -> twobinopfun X Y := λ f, twobinopfunpair (pr1 (pr1 f)) (pr2 f).
Coercion twobinopincltotwobinopfun : twobinopmono >-> twobinopfun.

Definition binop1mono {X Y : setwith2binop} (f : twobinopmono X Y) :
  binopmono (setwithbinop1 X) (setwithbinop1 Y) :=
  @binopmonopair (setwithbinop1 X) (setwithbinop1 Y) (pr1 f) (pr1 (pr2 f)).

Definition binop2mono {X Y : setwith2binop} (f : twobinopmono X Y) :
  binopmono (setwithbinop2 X) (setwithbinop2 Y) :=
  @binopmonopair (setwithbinop2 X) (setwithbinop2 Y) (pr1 f) (pr2 (pr2 f)).

Definition twobinopmonocomp {X Y Z : setwith2binop} (f : twobinopmono X Y) (g : twobinopmono Y Z) :
  twobinopmono X Z := twobinopmonopair (inclcomp (pr1 f) (pr1 g)) (istwobinopfuncomp f g).

Definition twobinopiso (X Y : setwith2binop) : UU := total2 (λ f : X ≃ Y, istwobinopfun f).

Definition twobinopisopair {X Y : setwith2binop} (f : X ≃ Y) (is : istwobinopfun f) :
  twobinopiso X Y := tpair _  f is.

Definition pr1twobinopiso (X Y : setwith2binop) : twobinopiso X Y -> X ≃ Y := @pr1 _ _.
Coercion pr1twobinopiso : twobinopiso >-> weq.

Definition twobinopisototwobinopmono (X Y : setwith2binop) :
  twobinopiso X Y -> twobinopmono X Y := λ f, twobinopmonopair (pr1 f) (pr2 f).
Coercion twobinopisototwobinopmono : twobinopiso >-> twobinopmono.

Definition twobinopisototwobinopfun {X Y : setwith2binop} (f : twobinopiso X Y) :
  twobinopfun X Y := twobinopfunpair f (pr2 f).

Lemma twobinopiso_paths {X Y : setwith2binop} (f g : twobinopiso X Y) (e : pr1 f = pr1 g) : f = g.
Proof.
  intros X Y f g e.
  use total2_paths_f.
  - exact e.
  - use proofirrelevance. use isapropistwobinopfun.
Defined.
Opaque twobinopiso_paths.

Definition binop1iso {X Y : setwith2binop} (f : twobinopiso X Y) :
  binopiso (setwithbinop1 X) (setwithbinop1 Y) :=
  @binopisopair (setwithbinop1 X) (setwithbinop1 Y) (pr1 f) (pr1 (pr2 f)).

Definition binop2iso {X Y : setwith2binop} (f : twobinopiso X Y) :
  binopiso (setwithbinop2 X) (setwithbinop2 Y) :=
  @binopisopair (setwithbinop2 X) (setwithbinop2 Y) (pr1 f) (pr2 (pr2 f)).

Definition twobinopisocomp {X Y Z : setwith2binop} (f : twobinopiso X Y) (g : twobinopiso Y Z) :
  twobinopiso X Z := twobinopisopair (weqcomp (pr1 f) (pr1 g)) (istwobinopfuncomp f g).

Lemma istwobinopfuninvmap {X Y : setwith2binop} (f : twobinopiso X Y) :
  istwobinopfun (invmap (pr1 f)).
Proof.
  intros.
  set (ax1f := pr1 (pr2 f)). set (ax2f := pr2 (pr2 f)).
  split.
  - intros a b. apply (invmaponpathsweq (pr1 f)).
    rewrite (homotweqinvweq (pr1 f) (op1 a b)).
    rewrite (ax1f (invmap (pr1 f) a) (invmap (pr1 f) b)).
    rewrite (homotweqinvweq (pr1 f) a).
    rewrite (homotweqinvweq (pr1 f) b).
    apply idpath.
  - intros a b. apply (invmaponpathsweq (pr1 f)).
    rewrite (homotweqinvweq (pr1 f) (op2 a b)).
    rewrite (ax2f (invmap (pr1 f) a) (invmap (pr1 f) b)).
    rewrite (homotweqinvweq (pr1 f) a).
    rewrite (homotweqinvweq (pr1 f) b).
    apply idpath.
Defined.
Opaque istwobinopfuninvmap.

Definition invtwobinopiso {X Y : setwith2binop} (f : twobinopiso X Y) :
  twobinopiso Y X := twobinopisopair (invweq (pr1 f)) (istwobinopfuninvmap f).

Definition idtwobinopiso (X : setwith2binop) : twobinopiso X X.
Proof.
  intros X.
  use twobinopisopair.
  - use (idweq X).
  - use mk_istwobinopfun.
    + intros x x'. use idpath.
    + intros x x'. use idpath.
Defined.


(** **** X = Y ≃ (X ≃ Y)
   The idea is to use the composition X = Y ≃ X ╝ Y ≃ (twobinopiso X Y)
*)

Definition setwith2binop_univalence_weq1 (X Y : setwith2binop) : (X = Y) ≃ (X ╝ Y) :=
  total2_paths_equiv _ X Y.

Definition setwith2binop_univalence_weq2 (X Y : setwith2binop) : (X ╝ Y) ≃ (twobinopiso X Y).
Proof.
  intros X Y.
  use weqbandf.
  - use hSet_univalence.
  - intros e. use invweq. induction X as [X Xop]. induction Y as [Y Yop]. cbn in e.
    induction e. use weqimplimpl.
    + intros i.
      use dirprod_paths.
      * use funextfun. intros x1.
        use funextfun. intros x2.
        exact ((dirprod_pr1 i) x1 x2).
      * use funextfun. intros x1.
        use funextfun. intros x2.
        exact ((dirprod_pr2 i) x1 x2).
    + intros e. change (Xop = Yop) in e.
      use mk_istwobinopfun.
      * intros x1 x2. induction e. use idpath.
      * intros x1 x2. induction e. use idpath.
    + use isapropistwobinopfun.
    + use isasettwobinoponhSet.
Defined.
Opaque setwith2binop_univalence_weq2.

Definition setwith2binop_univalence_map (X Y : setwith2binop) : X = Y -> twobinopiso X Y.
Proof.
  intros X Y e. induction e. exact (idtwobinopiso X).
Defined.

Lemma setwith2binop_univalence_isweq (X Y : setwith2binop) :
  isweq (setwith2binop_univalence_map X Y).
Proof.
  intros X Y.
  use isweqhomot.
  - exact (weqcomp (setwith2binop_univalence_weq1 X Y) (setwith2binop_univalence_weq2 X Y)).
  - intros e. induction e. use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque setwith2binop_univalence_isweq.

Definition setwith2binop_univalence (X Y : setwith2binop) : (X = Y) ≃ (twobinopiso X Y).
Proof.
  intros X Y.
  use weqpair.
  - exact (setwith2binop_univalence_map X Y).
  - exact (setwith2binop_univalence_isweq X Y).
Defined.
Opaque setwith2binop_univalence.


(** **** Transport of properties of a pair of binary operations *)

Lemma isldistrmonob {X Y : setwith2binop} (f : twobinopmono X Y) (is : isldistr (@op1 Y) (@op2 Y)) :
  isldistr (@op1 X) (@op2 X).
Proof.
  intros.
  set (ax1f := pr1 (pr2 f)). set (ax2f := pr2 (pr2 f)).
  intros a b c. apply (invmaponpathsincl _ (pr2 (pr1 f))).
  change (paths ((pr1 f) (op2 c (op1 a b))) ((pr1 f) (op1 (op2 c a) (op2 c b)))).
  rewrite (ax2f c (op1 a b)).
  rewrite (ax1f a b).
  rewrite (ax1f (op2 c a) (op2 c b)).
  rewrite (ax2f c a).
  rewrite (ax2f c b).
  apply is.
Defined.
Opaque isldistrmonob.

Lemma isrdistrmonob {X Y : setwith2binop} (f : twobinopmono X Y)
      (is : isrdistr (@op1 Y) (@op2 Y)) : isrdistr (@op1 X) (@op2 X).
Proof.
  intros.
  set (ax1f := pr1 (pr2 f)). set (ax2f := pr2 (pr2 f)).
  intros a b c.
  apply (invmaponpathsincl _ (pr2 (pr1 f))).
  change (paths ((pr1 f) (op2 (op1 a b) c)) ((pr1 f) (op1 (op2 a c) (op2 b c)))).
  rewrite (ax2f (op1 a b) c).
  rewrite (ax1f a b).
  rewrite (ax1f (op2 a c) (op2 b c)).
  rewrite (ax2f a c).
  rewrite (ax2f b c).
  apply is.
Defined.
Opaque isrdistrmonob.

Definition isdistrmonob {X Y : setwith2binop} (f : twobinopmono X Y)
           (is : isdistr (@op1 Y) (@op2 Y)) :
  isdistr (@op1 X) (@op2 X) := dirprodpair (isldistrmonob f (pr1 is)) (isrdistrmonob f (pr2 is)).

Notation isldistrisob := isldistrmonob.
Notation isrdistrisob := isrdistrmonob.
Notation isdistrisob := isdistrmonob.

Lemma isldistrisof {X Y : setwith2binop} (f : twobinopiso X Y) (is : isldistr (@op1 X) (@op2 X)) :
  isldistr (@op1 Y) (@op2 Y).
Proof.
  intros. apply (isldistrisob (invtwobinopiso f) is).
Defined.

Lemma isrdistrisof {X Y : setwith2binop} (f : twobinopiso X Y) (is : isrdistr (@op1 X) (@op2 X)) :
  isrdistr (@op1 Y) (@op2 Y).
Proof.
  intros. apply (isrdistrisob (invtwobinopiso f) is).
Defined.

Lemma isdistrisof {X Y : setwith2binop} (f : twobinopiso X Y) (is : isdistr (@op1 X) (@op2 X)) :
  isdistr (@op1 Y) (@op2 Y).
Proof.
  intros. apply (isdistrisob (invtwobinopiso f) is).
Defined.

Definition isrigopsisof {X Y : setwith2binop} (f : twobinopiso X Y)
           (is : isrigops (@op1 X) (@op2 X)) : isrigops (@op1 Y) (@op2 Y).
Proof.
  intros. split.
  - split with (dirprodpair (isabmonoidopisof (binop1iso f) (rigop1axs_is is))
                            (ismonoidopisof (binop2iso f) (rigop2axs_is is))).
    simpl.
    change (unel_is (ismonoidopisof (binop1iso f) (rigop1axs_is is)))
    with ((pr1 f) (rigunel1_is is)).
    split.
    + intro y.
      rewrite (pathsinv0 (homotweqinvweq f y)).
      rewrite (pathsinv0 ((pr2 (pr2 f)) _ _)).
      apply (maponpaths (pr1 f)). apply (rigmult0x_is is).
    + intro y.
      rewrite (pathsinv0 (homotweqinvweq f y)).
      rewrite (pathsinv0 ((pr2 (pr2 f)) _ _)).
      apply (maponpaths (pr1 f)).
      apply (rigmultx0_is is).
  - apply (isdistrisof f). apply (rigdistraxs_is is).
Defined.

Definition isrigopsisob {X Y : setwith2binop} (f : twobinopiso X Y)
           (is : isrigops (@op1 Y) (@op2 Y)) : isrigops (@op1 X) (@op2 X).
Proof.
  intros. apply (isrigopsisof (invtwobinopiso f) is).
Defined.

Definition isrngopsisof {X Y : setwith2binop} (f : twobinopiso X Y)
           (is : isrngops (@op1 X) (@op2 X)) : isrngops (@op1 Y) (@op2 Y) :=
  dirprodpair (dirprodpair (isabgropisof (binop1iso f) (rngop1axs_is is))
                           (ismonoidopisof (binop2iso f) (rngop2axs_is is)))
              (isdistrisof f (pr2 is)).

Definition isrngopsisob {X Y : setwith2binop} (f : twobinopiso X Y)
           (is : isrngops (@op1 Y) (@op2 Y)) : isrngops (@op1 X) (@op2 X) :=
  dirprodpair (dirprodpair (isabgropisob (binop1iso f) (rngop1axs_is is))
                           (ismonoidopisob (binop2iso f) (rngop2axs_is is)))
              (isdistrisob f (pr2 is)).

Definition iscommrngopsisof {X Y : setwith2binop} (f : twobinopiso X Y)
           (is : iscommrngops (@op1 X) (@op2 X)) : iscommrngops (@op1 Y) (@op2 Y) :=
  dirprodpair (isrngopsisof f is) (iscommisof (binop2iso f) (pr2 is)).

Definition iscommrngopsisob {X Y : setwith2binop} (f : twobinopiso X Y)
           (is : iscommrngops (@op1 Y) (@op2 Y)) : iscommrngops (@op1 X) (@op2 X) :=
  dirprodpair (isrngopsisob f is) (iscommisob (binop2iso f) (pr2 is)).


(** **** Subobjects *)

Definition issubsetwith2binop {X : setwith2binop} (A : hsubtype X) : UU :=
  dirprod (∏ a a' : A, A (op1 (pr1 a) (pr1 a'))) (∏ a a' : A, A (op2 (pr1 a) (pr1 a'))).

Lemma isapropissubsetwith2binop {X : setwith2binop} (A : hsubtype X) :
  isaprop (issubsetwith2binop A).
Proof.
  intros. apply (isofhleveldirprod 1).
  - apply impred. intro a.
    apply impred. intros a'.
    apply (pr2 (A (op1 (pr1 a) (pr1 a')))).
  - apply impred. intro a.
    apply impred. intros a'.
    apply (pr2 (A (op2 (pr1 a) (pr1 a')))).
Defined.

Definition subsetswith2binop {X : setwith2binop} : UU :=
  total2 (λ A : hsubtype X, issubsetwith2binop A).

Definition subsetswith2binoppair {X : setwith2binop} :
  ∏ (t : hsubtype X), (λ A : hsubtype X, issubsetwith2binop A) t →
                       ∑ A : hsubtype X, issubsetwith2binop A :=
  tpair (λ A : hsubtype X, issubsetwith2binop A).

Definition subsetswith2binopconstr {X : setwith2binop} :
  ∏ (t : hsubtype X), (λ A : hsubtype X, issubsetwith2binop A) t →
                       ∑ A : hsubtype X, issubsetwith2binop A :=
  @subsetswith2binoppair X.

Definition pr1subsetswith2binop (X : setwith2binop) : @subsetswith2binop X -> hsubtype X :=
  @pr1 _ (λ A : hsubtype X, issubsetwith2binop A).
Coercion pr1subsetswith2binop : subsetswith2binop >-> hsubtype.

Definition totalsubsetwith2binop (X : setwith2binop) : @subsetswith2binop X.
Proof.
  intros. split with (λ x : X, htrue). split.
  - intros x x'. apply tt.
  - intros. apply tt.
Defined.

Definition carrierofsubsetwith2binop {X : setwith2binop} (A : @subsetswith2binop X) : setwith2binop.
Proof.
  intros.
  set (aset := (hSetpair (carrier A) (isasetsubset (pr1carrier A) (setproperty X)
                                                   (isinclpr1carrier A))) : hSet).
  split with aset.
  set (subopp1 := (λ a a' : A, carrierpair A (op1 (pr1carrier _ a) (pr1carrier _ a'))
                                            (pr1 (pr2 A) a a')) : (A -> A -> A)).
  set (subopp2 := (λ a a' : A, carrierpair A (op2 (pr1carrier _ a) (pr1carrier _ a'))
                                            (pr2 (pr2 A) a a')) : (A -> A -> A)).
  simpl. apply (dirprodpair subopp1 subopp2).
Defined.
Coercion carrierofsubsetwith2binop : subsetswith2binop >-> setwith2binop.


(** **** Quotient objects *)

Definition is2binophrel {X : setwith2binop} (R : hrel X) : UU :=
  dirprod (@isbinophrel (setwithbinop1 X) R) (@isbinophrel (setwithbinop2 X) R).

Lemma isapropis2binophrel {X : setwith2binop} (R : hrel X) : isaprop (is2binophrel R).
Proof.
  intros. apply (isofhleveldirprod 1).
  - apply isapropisbinophrel.
  - apply isapropisbinophrel.
Defined.

Lemma iscomp2binoptransrel {X : setwith2binop} (R : hrel X) (is : istrans R)
      (isb : is2binophrel R) :
  dirprod (iscomprelrelfun2 R R (@op1 X)) (iscomprelrelfun2 R R (@op2 X)).
Proof.
  intros. split.
  - apply (@iscompbinoptransrel (setwithbinop1 X) R is (pr1 isb)).
  - apply (@iscompbinoptransrel (setwithbinop2 X) R is (pr2 isb)).
Defined.

Definition twobinophrel {X : setwith2binop} : UU := total2 (λ R : hrel X, is2binophrel R).

Definition twobinophrelpair {X : setwith2binop} :
  ∏ (t : hrel X), (λ R : hrel X, is2binophrel R) t → ∑ R : hrel X, is2binophrel R :=
  tpair (λ R : hrel X, is2binophrel R).

Definition pr1twobinophrel (X : setwith2binop) : @twobinophrel X -> hrel X :=
  @pr1 _ (λ R : hrel X, is2binophrel R).
Coercion pr1twobinophrel : twobinophrel >-> hrel.

Definition twobinoppo {X : setwith2binop} : UU := total2 (λ R : po X, is2binophrel R).

Definition twobinoppopair {X : setwith2binop} :
  ∏ (t : po X), (λ R : po X, is2binophrel R) t → ∑ R : po X, is2binophrel R :=
  tpair (λ R : po X, is2binophrel R).

Definition pr1twobinoppo (X : setwith2binop) : @twobinoppo X -> po X :=
  @pr1 _ (λ R : po X, is2binophrel R).
Coercion pr1twobinoppo : twobinoppo >-> po.

Definition twobinopeqrel {X : setwith2binop} : UU := total2 (λ R : eqrel X, is2binophrel R).

Definition twobinopeqrelpair {X : setwith2binop} :
  ∏ (t : eqrel X), (λ R : eqrel X, is2binophrel R) t → ∑ R : eqrel X, is2binophrel R :=
  tpair (λ R : eqrel X, is2binophrel R).

Definition pr1twobinopeqrel (X : setwith2binop) : @twobinopeqrel X -> eqrel X :=
  @pr1 _ (λ R : eqrel X, is2binophrel R).
Coercion pr1twobinopeqrel : twobinopeqrel >-> eqrel.

Definition setwith2binopquot {X : setwith2binop} (R : @twobinopeqrel X) : setwith2binop.
Proof.
  intros. split with (setquotinset R).
  set (qt := setquot R). set (qtset := setquotinset R).
  assert (iscomp1 : iscomprelrelfun2 R R (@op1 X))
    by apply (pr1 (iscomp2binoptransrel (pr1 R) (eqreltrans _) (pr2 R))).
  set (qtop1 := setquotfun2 R R (@op1 X) iscomp1).
  assert (iscomp2 : iscomprelrelfun2 R R (@op2 X))
    by apply (pr2 (iscomp2binoptransrel (pr1 R) (eqreltrans _) (pr2 R))).
  set (qtop2 := setquotfun2 R R (@op2 X) iscomp2).
  simpl. apply (dirprodpair qtop1 qtop2).
Defined.


(** **** Direct products *)

Definition setwith2binopdirprod (X Y : setwith2binop) : setwith2binop.
Proof.
  intros. split with (setdirprod X Y). simpl.
  (* ??? same issue as with setwithbinopdirpro above *)
  apply (dirprodpair
           (λ xy xy' : dirprod X Y, dirprodpair (op1 (pr1 xy) (pr1 xy')) (op1 (pr2 xy) (pr2 xy')))
           (λ xy xy' : dirprod X Y, dirprodpair (op2 (pr1 xy) (pr1 xy'))
                                                 (op2 (pr2 xy) (pr2 xy')))).
Defined.

(* End of file *)
