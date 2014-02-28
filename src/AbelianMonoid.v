(* -*- coding: utf-8 -*- *)

Unset Automatic Introduction.
Require Import Foundations.hlevel2.algebra1b
               Foundations.hlevel2.finitesets
               Ktheory.Utilities.
Import RezkCompletion.pathnotations.PathNotations Utilities.Notation.
Local Notation "x * y" := ( op x y ). 
Definition incl n : stn n -> stn (S n).
  intros n [i l]. exists i.
  apply (natlthlehtrans i n (S n)). { assumption. } { exact (natlehnsn n). }
Defined.
Definition finiteOperation0 (X:abmonoid) n (x:stn n->X) : X.
Proof. (* return (...((x0*x1)*x2)*...)  *)
  intros. induction n as [|n x'].
  { exact (unel _). } { exact ((x' (funcomp (incl n) x)) * x (lastelement n)). } Defined.
Goal forall (X:abmonoid) n (x:stn (S n)->X),
     finiteOperation0 X (S n) x 
  == finiteOperation0 X n (funcomp (incl n) x) * x (lastelement n).
Proof. reflexivity. Qed.
Lemma same_n {I m n} (f:nelstruct m I) (g:nelstruct n I) : m == n.
Proof. intros. apply weqtoeqstn. exact (weqcomp f (invweq g)). Qed.
Lemma fun_assoc {W X Y Z} (f:W->X) (g:X->Y) (h:Y->Z) :
  funcomp (funcomp f g) h == funcomp f (funcomp g h).
Proof. reflexivity. Defined.
Lemma uniqueness0 (X:abmonoid) n : forall I (f g:nelstruct n I) (x:I->X),
     finiteOperation0 X n (funcomp (pr1 f) x) 
  == finiteOperation0 X n (funcomp (pr1 g) x).
Proof. intros ? ?. induction n as [|n IH].
       { reflexivity. }
       { intros. simpl.
         assert (dec : decidable ( pr1 f (lastelement n) == pr1 g (lastelement n) )).
         { apply (isdeceqweqf f). apply isdeceqstn. }
         destruct dec as [e|b].
         { apply (aptwice (fun x y => x*y)).
           { rewrite <- 2 ! fun_assoc. 
             assert (f' := nelstructoncompl (pr1 f (lastelement n)) f).
             assert (g' := nelstructoncompl (pr1 g (lastelement n)) g).
             destruct e.
             Check IH _ f' g' (pr1compl _ _ _).

                                       admit. }
           { exact (ap x e). } }
         { admit. } } Qed.
Definition finiteOperation1 (X:abmonoid) I : finstruct I -> (I->X) -> X.
  intros ? ? [n f] x.
  apply (finiteOperation0 X n).
  intros i. exact (x (pr1 f i)).
Defined.
Definition finiteOperation {I} (is:isfinite I) (X:abmonoid) (x:I->X) : X.
  intros. refine (squash_to_set is _ _ _); clear is. 
  { apply setproperty. }
  { intros fs. apply (finiteOperation1 X I fs x). }
  { intros [m f] [n g]. assert (e := same_n f g). destruct e. apply uniqueness0. }
Defined.

