(*

"iso" can be applied to objects in different precategories and that's
mathematically strange, or even incorrect, and can cause confusion.

However, it might be sort of convenient if it would check at least that the two
categories have the same morphisms, the same identity arrows, and the same
composition operations, but not check that the proofs of the identities are the
same. But even that might lead to confusion, so better not.

Here is the code that shows the problem.

*)

Require Import Foundations.hlevel2.hSet.
Require Import RezkCompletion.precategories.
        Import pathnotations.PathNotations.

(* make two precategories with the same objects *)
Parameter o : Type.
Parameter m m' : o -> o -> Type.
Parameter is : forall (c d:o), isaset (m c d).
Parameter is': forall (c d:o), isaset (m' c d).
Parameter id : forall c:o, m c c.
Parameter id': forall c:o, m' c c.
Parameter co : forall {c d e:o} (f:m c d) (g:m d e), m c e.
Parameter co': forall {c d e:o} (f:m' c d) (g:m' d e), m' c e.
Parameter rg: forall (c d:o) (f:m c d), co (id c) f == f.
Parameter lf: forall (c d:o) (f:m c d), co f (id d) == f.
Parameter rg': forall (c d:o) (f:m' c d), co' (id' c) f == f.
Parameter lf': forall (c d:o) (f:m' c d), co' f (id' d) == f.
Parameter ass: forall (a b c d : o)
                      (f : m a b) (g : m b c) (h : m c d),
                 co f (co g h) == co (co f g) h.
Parameter ass': forall (a b c d : o)
                      (f : m' a b) (g : m' b c) (h : m' c d),
                 co' f (co' g h) == co' (co' f g) h.

Definition precategory_pair (C:precategory_data) (i:is_precategory C)
  : precategory := tpair _ C i.

Definition makePrecategory 
    (obj : UU)
    (mor : obj -> obj -> UU)
    (imor : forall i j:obj, isaset (mor i j))
    (identity : forall i:obj, mor i i)
    (compose : forall (i j k:obj) (f:mor i j) (g:mor j k), mor i k)
    (right : forall (i j:obj) (f:mor i j), compose _ _ _ (identity i) f == f)
    (left  : forall (i j:obj) (f:mor i j), compose _ _ _ f (identity j) == f)
    (associativity : forall (a b c d:obj) (f:mor a b) (g:mor b c) (h:mor c d),
        compose _ _ _ f (compose _ _ _ g h) == compose _ _ _ (compose _ _ _ f g) h)
    : precategory.
  intros.
  set (C := precategory_data_pair
              (precategory_ob_mor_pair 
                 obj 
                 (fun i j:obj => hSetpair (mor i j) (imor i j))) identity compose).
  assert (iC : is_precategory C).
    split. split. exact right. exact left. exact associativity.
  exact (precategory_pair C iC).
Defined.    

Definition C := makePrecategory o m is id (@co) rg lf ass.
Definition C':= makePrecategory o m' is' id' (@co') rg' lf' ass'.

Definition funny (c:C) (c':C') := RezkCompletion.precategories.iso c c'. (* ! *)

Goal unit.
  Set Printing All.
  set (m := funny).
  unfold funny in m; simpl in m. (* see see that m includes nothing about C' *)
  exact tt.
Qed.  

Definition funny' (c:C) (c':o) := RezkCompletion.precategories.iso c c'. (* ! *)
