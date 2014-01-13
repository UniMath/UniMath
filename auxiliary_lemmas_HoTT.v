Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.

Definition propproperty ( X : hProp ) := pr2 X . 

(** * Paths in total spaces are equivalent to pairs of paths *)

(** some of the lemmas are proved for similar fibrations twice:
    once we consider fibrations over a type in universe [UU], 
    once we consider fibrations over the universe [UU] itself *)


Lemma total2_paths {A : UU} {B : A -> UU} {s s' : total2 (fun x => B x)} 
    (p : pr1 s == pr1 s') 
    (q : transportf (fun x => B x) p (pr2 s) == pr2 s') : 
               s == s'.
Proof.
  destruct s as [a b]; destruct s' as [a' b'].
  simpl in p; destruct p.
  simpl in q; destruct q.
  apply idpath.
Defined.


Lemma total2_paths_hProp (A : UU) (B : A -> UU) (is : forall a, isaprop (B a))
    (s s' : total2 (fun x => B x)) : pr1 s == pr1 s' -> s == s'.
Proof.
  intro h.
  apply (total2_paths h).
  apply proofirrelevance.
  apply is.
Defined.

Lemma total2_paths_UU  {B : UU -> UU} {s s' : total2 (fun x => B x)} 
    (p : pr1 s == pr1 s') 
    (q : transportf (fun x => B x) p (pr2 s) == pr2 s') : 
               s == s'.
Proof.
  destruct s as [a b]; destruct s' as [a' b'].
  simpl in p; destruct p.
  simpl in q; destruct q.
  apply idpath.
Defined.


Lemma total2_paths2 {A : UU} {B : A -> UU} {a1 : A} {b1 : B a1} 
    {a2 : A} {b2 : B a2} (p : a1 == a2) 
    (q : transportf (fun x => B x) p b1 == b2) : 
    tpair (fun x => B x) a1 b1 == tpair (fun x => B x) a2 b2.
Proof.
  set (H := @total2_paths _ _  
    (tpair (fun x => B x) a1 b1)(tpair (fun x => B x) a2 b2)).
  simpl in H.
  apply (H p q).
Defined.

Lemma total2_paths2_UU {B : UU -> UU} {A A': UU} {b : B A} 
     {b' : B A'} (p : A == A') (q : transportf (fun x => B x) p b == b') : 
    tpair (fun x => B x) A b == tpair (fun x => B x) A' b'.
Proof.
  set (H := @total2_paths _ _  
     (tpair (fun x => B x) A b)(tpair (fun x => B x) A' b')).
  simpl in H.
  apply (H p q).
Defined.


Lemma base_paths {A : UU}{B : A -> UU}(a b : total2 B) :
  a == b -> pr1 a == pr1 b.
Proof.
  apply maponpaths.
Defined.

Lemma base_paths_UU {B : UU -> UU}(a b : total2 B) :
  a == b -> pr1 a == pr1 b.
Proof.
  intro H.
  apply (maponpaths  (@pr1 _ _) H).
Defined.


Definition fiber_path {A : UU} {B : A -> UU} {u v : total2 (fun x => B x)}
  (p : u == v) : transportf (fun x => B x) (base_paths _ _ p) (pr2 u) == pr2 v.
Proof.
  destruct p.
  apply idpath.
Defined.

Definition fiber_path_UU {B : UU -> UU} {u v : total2 (fun x => B x)}
  (p : u == v) : transportf (fun x => B x) (base_paths_UU _ _ p) (pr2 u) == pr2 v.
Proof.
  destruct p.
  apply idpath.
Defined.



Lemma total_path_reconstruction {A : UU} {B : A -> UU} {x y : total2 (fun x => B x)} 
 (p : x == y) : total2_paths  _ (fiber_path p) == p.
Proof.
  induction p.
  destruct x.
  apply idpath.
Defined.


Lemma total_path_reconstruction_UU {B : UU -> UU} {x y : total2 (fun x => B x)} 
 (p : x == y) : total2_paths_UU  _ (fiber_path_UU p) == p.
Proof.
  induction p.
  destruct x.
  apply idpath.
Defined.

Lemma base_total_path {A : UU} {B : A -> UU} {x y : total2 (fun x => B x)}
  {p : pr1 x == pr1 y} (q : transportf _ p (pr2 x) == pr2 y) :
  (base_paths _ _ (total2_paths _ q)) == p.
Proof.
  destruct x as [x H]. destruct y as [y K].
  simpl in p. induction p. simpl in q. induction q.
  apply idpath.
Defined.


Lemma base_total_path_UU {B : UU -> UU} {x y : total2 (fun x => B x)}
  {p : pr1 x == pr1 y} (q : transportf _ p (pr2 x) == pr2 y) :
  (base_paths_UU _ _ (total2_paths_UU _ q)) == p.
Proof.
  destruct x as [x H]. destruct y as [y K].
  simpl in p. induction p. simpl in q. induction q.
  apply idpath.
Defined.


Lemma fiber_total_path {A : UU} (B : A -> UU) (x y : total2 (fun x => B x))
  (p : pr1 x == pr1 y) (q : transportf _ p (pr2 x) == pr2 y) :
  transportf (fun p' : pr1 x == pr1 y => transportf _ p' (pr2 x) == pr2 y)
  (base_total_path q)  (fiber_path (total2_paths _ q))
  == q.
Proof.
  destruct x as [x H]. destruct y as [y K].
  simpl in p. induction p. simpl in q. induction q.
  apply idpath.
Defined.

Lemma fiber_total_path_UU (B : UU -> UU) (x y : total2 (fun x => B x))
  (p : pr1 x == pr1 y) (q : transportf _ p (pr2 x) == pr2 y) :
  transportf (fun p' : pr1 x == pr1 y => transportf _ p' (pr2 x) == pr2 y)
  (base_total_path_UU q)  (fiber_path_UU (total2_paths_UU _ q))
  == q.
Proof.
  destruct x as [x H]. destruct y as [y K].
  simpl in p. induction p. simpl in q. induction q.
  apply idpath.
Defined.




Theorem total_paths_equiv {A : UU} (B : A -> UU) (x y : total2 (fun x => B x)) :
  weq (x == y) (total2 (fun p : pr1 x == pr1 y => 
                            transportf _ p (pr2 x) == pr2 y )).
Proof.
  exists (  fun r : x == y =>  
               tpair (fun p : pr1 x == pr1 y => 
             transportf _ p (pr2 x) == pr2 y) (base_paths _ _ r) (fiber_path r)).
  apply (gradth _
  (fun pq : total2 (fun p : pr1 x == pr1 y => transportf _ p (pr2 x) == pr2 y)
          => total2_paths (pr1 pq) (pr2 pq))).
  intro p.
  simpl.
  apply total_path_reconstruction.
  intros [p q].
  simpl.
  set (H':= base_total_path q).
  apply ( total2_paths2 
    (B := fun p : pr1 x == pr1 y => transportf (fun x : A => B x) p (pr2 x) 
      == pr2 y) H').
  apply fiber_total_path.
Defined.


Theorem total_paths2_hProp_equiv {A : UU} (B : A -> hProp) 
   (x y : total2 (fun x => B x)): weq (x == y) (pr1 x == pr1 y).
Proof.
  set (t := total_paths_equiv B x y).
  simpl in *.
  set (t':= isweqpr1 
     (fun p : pr1 x == pr1 y => transportf (fun x : A => B x) p (pr2 x) == pr2 y)).

  simpl in *.
  assert (H : forall z : pr1 x == pr1 y, 
        iscontr (transportf (fun x : A => B x) z (pr2 x) == pr2 y)).
  intro p.
  set (H := pr2 (B (pr1 y))).
  simpl in H.
  apply (H _ (pr2 y)).
  simpl in *.
  set (Ht := t' H).
  set (ht := tpair _ _ Ht).
  
  set (HHH := weqcomp t ht).
  exact HHH.
Defined.


Theorem equal_transport_along_weq (A B : UU)  (f : weq A B) (a a' : A) :
      f a == f a' -> a == a'.
Proof.
  intro H.
  apply (!homotinvweqweq f a @ maponpaths (invmap f) H @ homotinvweqweq f a').
Defined.

Definition equal_equalities_between_pairs (A : UU)(B : A -> UU)(x y : total2 (fun x => B x))
   (p q : x == y) : 
  total_paths_equiv _ _ _ p == total_paths_equiv _ _ _ q -> p == q :=
      equal_transport_along_weq _ _ _ _ _ .


(** This helper lemma is an adaptation of an analogous lemma
    [isweqpr1] from Voevodsky's Foundations library.
    Here, we prove it for predicates on path spaces in [UU].
*)

Lemma isweqpr1_UU (X X' : UU) ( B : (X == X') -> UU ) 
   ( is1 : forall z , iscontr ( B z ) ) : isweq ( @pr1 _ B ) .
Proof. 
  intros. 
  unfold isweq. 
  intro y. 
  set (isy:= is1 y). 
  apply (iscontrweqf ( ezweqpr1 B y)) . 
  assumption. 
Defined.



Lemma pairofobuip (C C': hSet) (a b : C) (c d : C') 
        (p q : dirprod (a == b) (c == d)) : p == q.
Proof.
  assert (H : pr1 p == pr1 q).
  apply uip. exact (pr2 C).
  apply (total2_paths H).
  apply uip. exact (pr2 C').
Qed.










