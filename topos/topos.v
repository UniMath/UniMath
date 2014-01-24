Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.

Require Import RezkCompletion.limits.terminal.
Require Import RezkCompletion.limits.pullbacks.

Require Import RezkCompletion.topos.epis_monos.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).


Section subobject_classifier.

Variable C : precategory.

(* it seems that in order to state the subobject classifier axiom
   i need to ask C to have a terminal object sigma-wise 
   the basic instances of toposes (Set, presheaves) are univalent, however,
   so it doesn't make a difference
*)

Variable T : Terminal C.

Definition isSubobjectClassifier (Omega : C) (TrueArrow : T --> Omega) :=
    forall (s b : C) (m : mono C s b), iscontr (
      total2 (fun phi : b --> Omega =>
      total2 (fun H : m ;; phi == TerminalArrow C T s ;; TrueArrow  => 
                    isPullback C TrueArrow phi m (TerminalArrow _ _ s) H))).


Definition SubobjectClassifier :=  
    total2 (fun Omega : C => 
    total2 (fun TrueArrow : T --> Omega =>
           isSubobjectClassifier Omega TrueArrow)).
Definition Omega (S : SubobjectClassifier) : C := pr1 S.

(* todo : prove unicity of subobject classifer *)

Section power_object.

Variable OMEGA : SubobjectClassifier.
Variable Pb : Pullbacks C.




Let Omega : C := pr1 OMEGA.

Definition is_power_object (b : C) (Pb : C)



End subobject_classifier.































