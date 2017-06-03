(* Anthony Bordg, February 2017 *)

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.Algebra.Monoids_and_Groups.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Algebra.Domains_and_Fields.



Local Open Scope addmonoid_scope.

(* The underlying set of the ring of endomorphisms of an abelian group *)

Definition setrngofend (G : abgr) : hSet :=
  hSetpair (monoidfun G G) (isasetmonoidfun G G).

(* Two binary operations on the underlying set of the ring of endomorphisms of an abelian group *)

Definition setrngofendop1 {G: abgr} : binop (setrngofend G).
Proof.
  intros f g.
  apply (@monoidfunconstr _ _ (λ x : G, pr1 f x + pr1 g x)).
  apply tpair. intros x x'. rewrite (pr1 (pr2 f)). rewrite (pr1 (pr2 g)). apply (abmonoidrer G).
  rewrite (pr2 (pr2 f)). rewrite (pr2 (pr2 g)). rewrite (lunax G). reflexivity.
Defined.

Definition setrngofendop2 {G : abgr} : binop (setrngofend G).
Proof.
  intros f g.
  apply (monoidfuncomp f g).
Defined.

Notation "f + g" := (setrngofendop1 f g) : abgr_scope.
Notation "g ∘ f" := (setrngofendop2 f g) : abgr_scope.

Definition setwith2binoprngofend (G : abgr) : setwith2binop :=
  setwith2binoppair (setrngofend G) (dirprodpair (setrngofendop1) (setrngofendop2)).


(* setrngofendop1 G and setrngofendop2 G are ring operations *)

  (** setrngofendop1 is a commutative group operation **)

    (*** Indeed, it is a group operation ***)

      (**** First, it is a monoid operation  ****)

Local Open Scope abgr_scope.

 Definition isassocsetrngofendop1 {G : abgr} : isassoc (@op1 (setwith2binoprngofend G)).
 Proof.
   intros f g h.
   assert (p : (pr1 ((f + g) + h)) =  (pr1 (f + (g + h)))).
   apply funextfun. intro. simpl. apply (pr2 G).
   assert (q : (transportf (λ x : G -> G, ismonoidfun x) p) (pr2 ((f + g) + h))  = pr2 (f + (g + h))).
   apply isapropismonoidfun. apply (total2_paths2_f p q).
 Defined.

 Definition setrngofendun0 {G: abgr} : setrngofend G.
 Proof.
   apply (@monoidfunconstr _ _ (λ x : G, 0)).  apply dirprodpair. intros x x'. rewrite (lunax G).
   reflexivity. reflexivity.
 Defined.

 Definition islunitsetrngofendun0 {G : abgr} : islunit (@op1 (setwith2binoprngofend G)) setrngofendun0.
 Proof.
   intro f. assert (p : pr1 (setrngofendun0 + f) = pr1 f). apply funextfun.
   intro x. simpl. apply (lunax G (pr1 f x)).
   assert (q : (transportf (λ x : G -> G, ismonoidfun x) p (pr2 (setrngofendun0 + f))) = pr2 f).
   apply isapropismonoidfun. replace f with (pr1 f,,pr2 f). apply (total2_paths2_f p q). induction f as [x y]. reflexivity.
 Defined.

Definition isrunitsetrngofendun0 {G : abgr} : isrunit (@op1 (setwith2binoprngofend G)) setrngofendun0.
 Proof.
   intros f. assert (p : pr1 (f + setrngofendun0) = pr1 f). apply funextfun.
   intro x. simpl. apply (runax G (pr1 f x)).
   assert (q : (transportf (λ x : G -> G, ismonoidfun x) p (pr2 (f + setrngofendun0))) = pr2 f).
   apply isapropismonoidfun. replace f with (pr1 f,,pr2 f). apply (total2_paths2_f p q). induction f as [x y]. reflexivity.
 Defined.

 Definition isunitsetrngofendun0 {G : abgr} : isunit (@op1 (setwith2binoprngofend G)) setrngofendun0.
 Proof.
   exact (dirprodpair islunitsetrngofendun0 isrunitsetrngofendun0).
 Defined.

 Definition isunitalsetrngofendop1 {G : abgr} : isunital (@op1 (setwith2binoprngofend G)).
 Proof.
   exact (isunitalpair setrngofendun0 isunitsetrngofendun0).
 Defined.

 Definition ismonoidopsetrngofendop1 {G : abgr} : ismonoidop (@op1 (setwith2binoprngofend G)) :=
   dirprodpair isassocsetrngofendop1 isunitalsetrngofendop1.

Local Close Scope abgr_scope.

(* The definition below should be moved to Monoids_and_Groups *)

 Definition ismonoidfunabgrinv {G : abgr} : ismonoidfun (grinv G).
 Proof.
   apply dirprodpair. intros x y. transitivity (grinv G y + grinv G x). exact (grinvop G x y). apply (commax G).
   apply (grinvunel G).
 Defined.

Definition setrngofendinv {G : abgr} : setrngofend G -> setrngofend G.
 Proof.
   intro f. apply (@monoidfunconstr G G (λ x : G, grinv G (pr1 f x))). apply dirprodpair. intros x x'.
   rewrite (dirprod_pr1 (pr2 f)). apply (dirprod_pr1 ismonoidfunabgrinv). rewrite (dirprod_pr2 (pr2 f)). apply (grinvunel G).
 Defined.

Local Open Scope abgr_scope.

 Definition islinvsetrngofendinv {G : abgr} : islinv (@op1 (setwith2binoprngofend G)) setrngofendun0 setrngofendinv.
 Proof.
   intro f. assert (p: pr1 ((setrngofendinv f) + f) = pr1 setrngofendun0). apply funextfun.
   intro x. simpl. apply (grlinvax G).
   assert (q : (transportf (λ x : G -> G, ismonoidfun x) p (pr2 (setrngofendinv f + f))) = pr2 setrngofendun0).
   apply isapropismonoidfun. apply (total2_paths2_f p q).
 Defined.

Definition isrinvsetrngofendinv {G : abgr} : isrinv (@op1 (setwith2binoprngofend G)) setrngofendun0 setrngofendinv.
 Proof.
   intro f. assert (p: pr1 (f + setrngofendinv f) = pr1 setrngofendun0). apply funextfun.
   intro x. simpl. apply (grrinvax G).
   assert (q : (transportf (λ x : G -> G, ismonoidfun x) p (pr2 (f + setrngofendinv f))) = pr2 setrngofendun0).
   apply isapropismonoidfun. apply (total2_paths2_f p q).
 Defined.

Definition isinvsetrngofendinv {G : abgr} : isinv (@op1 (setwith2binoprngofend G)) setrngofendun0 setrngofendinv.
 Proof.
   apply dirprodpair. exact islinvsetrngofendinv. exact isrinvsetrngofendinv.
 Defined.

 Definition isinvstructsetrngofendinv {G : abgr} : invstruct (@op1 (setwith2binoprngofend G)) ismonoidopsetrngofendop1 :=
   tpair (λ inv0 : (setrngofend G) -> (setrngofend G), isinv setrngofendop1 setrngofendun0 inv0)
         setrngofendinv isinvsetrngofendinv.

 Definition isgropsetrngofendop1 {G : abgr} : isgrop (@op1 (setwith2binoprngofend G)) :=
   tpair (λ is : ismonoidop setrngofendop1, invstruct setrngofendop1 is) ismonoidopsetrngofendop1 isinvstructsetrngofendinv.

 Definition iscommsetrngofendop1 {G : abgr} : iscomm (@op1 (setwith2binoprngofend G)).
 Proof.
   intros f g. assert (p : pr1 (f + g) = pr1 (g + f)). apply funextfun. intro x. simpl. apply (commax G).
   assert (q : (transportf (λ x : G -> G, ismonoidfun x) p (pr2 (f + g))) = pr2 (g + f)).
   apply (isapropismonoidfun). apply (total2_paths2_f p q).
 Defined.

Definition isabgropsetrngofendop1 {G : abgr} : isabgrop (@op1 (setwith2binoprngofend G)) :=
  dirprodpair isgropsetrngofendop1 iscommsetrngofendop1.

  (* setrngofendop2 is a monoid operation *)

Definition isassocsetrngofendop2 {G : abgr} : isassoc (@op2 (setwith2binoprngofend G)).
Proof.
  intros f g h. assert (p : pr1 (h ∘ (g ∘ f)) = pr1 ((h ∘ g) ∘ f)). simpl. apply funcomp_assoc.
  assert (q : (transportf (λ x : G -> G, ismonoidfun x) p (pr2 (h ∘ (g ∘ f)))) = pr2 ((h ∘ g) ∘ f)). apply isapropismonoidfun.
  apply (total2_paths2_f p q).
Defined.

Definition setrngofendun1 {G: abgr} : setrngofend G.
 Proof.
   apply (@monoidfunconstr _ _ (idfun G)).  apply dirprodpair. intros x x'. unfold idfun. reflexivity. unfold idfun. reflexivity.
 Defined.

 Definition islunitsetrngofendun1 {G : abgr} : islunit (@op2 (setwith2binoprngofend G)) setrngofendun1.
 Proof.
   intro f. assert (p : pr1 (f ∘ setrngofendun1) = pr1 f). apply funextfun.
   intro x. simpl. unfold funcomp. unfold idfun. reflexivity.
   assert (q : (transportf (λ x : G -> G, ismonoidfun x) p (pr2 (f ∘ setrngofendun1))) = pr2 f).
   apply isapropismonoidfun. replace f with (pr1 f,,pr2 f). apply (total2_paths2_f p q). induction f as [x y]. reflexivity.
 Defined.

Definition isrunitsetrngofendun1 {G : abgr} : isrunit (@op2 (setwith2binoprngofend G)) setrngofendun1.
 Proof.
   intros f. assert (p : pr1 (setrngofendun1 ∘ f) = pr1 f). apply funextfun.
   intro x. simpl. unfold funcomp. unfold idfun. reflexivity.
   assert (q : (transportf (λ x : G -> G, ismonoidfun x) p (pr2 (setrngofendun1 ∘ f))) = pr2 f).
   apply isapropismonoidfun. replace f with (pr1 f,,pr2 f). apply (total2_paths2_f p q). induction f as [x y]. reflexivity.
 Defined.

 Definition isunitsetrngofendun1 {G : abgr} : isunit (@op2 (setwith2binoprngofend G)) setrngofendun1.
 Proof.
   exact (dirprodpair islunitsetrngofendun1 isrunitsetrngofendun1).
 Defined.

 Definition isunitalsetrngofendop2 {G : abgr} : isunital (@op2 (setwith2binoprngofend G)).
 Proof.
   exact (isunitalpair setrngofendun1 isunitsetrngofendun1).
 Defined.

 Definition ismonoidopsetrngofendop2 {G : abgr} : ismonoidop (@op2 (setwith2binoprngofend G)) :=
   dirprodpair isassocsetrngofendop2 isunitalsetrngofendop2.

  (* setrngofendop2 is distributive over setrngofendop1 *)

 Definition isldistrsetrngofendop {G : abgr} : isldistr (@op1 (setwith2binoprngofend G)) op2.
 Proof.
   intros f g h. assert (p : pr1 ((f + g) ∘ h) = pr1 ((f ∘ h) + (g ∘ h))). apply funextfun. intro x. simpl. unfold funcomp. reflexivity.
   assert (q : (transportf (λ x : G -> G, ismonoidfun x) p (pr2 ((f + g) ∘ h))) = pr2 ((f ∘ h) + (g ∘ h))). apply isapropismonoidfun.
   apply (total2_paths2_f p q).
 Defined.

Definition isrdistrsetrngofendop {G : abgr} : isrdistr (@op1 (setwith2binoprngofend G)) op2.
 Proof.
   intros f g h. assert (p : pr1 (h ∘ (f + g)) = pr1 ((h ∘ f) + (h ∘ g))). apply funextfun. intro x. simpl. unfold funcomp.
   apply (pr1 (pr2 h)).
   assert (q : (transportf (λ x : G -> G, ismonoidfun x) p (pr2 (h ∘ (f + g)))) = pr2 ((h ∘ f) + (h ∘ g))). apply isapropismonoidfun.
   apply (total2_paths2_f p q).
 Defined.

 Definition isdistrsetrngofendop {G : abgr} : isdistr (@op1 (setwith2binoprngofend G)) op2 :=
   dirprodpair isldistrsetrngofendop isrdistrsetrngofendop.

 Definition isrngopssetrngofendop {G : abgr} : isrngops (@op1 (setwith2binoprngofend G)) op2 :=
   dirprodpair (dirprodpair isabgropsetrngofendop1 ismonoidopsetrngofendop2) isdistrsetrngofendop.

 (* The set of endomorphisms of an abelian group is a ring *)

 Definition isarngsetrngofend (G : abgr) : rng :=
   rngpair (@isrngopssetrngofendop G).

 (* The definition of the small type of modules over a commutative ring *)

 Definition module : UU := ∑ X Y, rngfun X (isarngsetrngofend Y).

 (* The definition of the small type of vector spaces over a field *)

 Definition VectSp : UU := ∑ X : fld, ∑ Y : abgr, rngfun X (isarngsetrngofend Y).
