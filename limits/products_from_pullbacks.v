Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.

Require Import RezkCompletion.limits.aux_lemmas_HoTT.
Require Export RezkCompletion.limits.pullbacks.
Require Export RezkCompletion.limits.products.
Require Import RezkCompletion.limits.terminal.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).

Section product_from_pullback.

Variable C : precategory.
Variable Pb : Pullbacks C.
Variable T : Terminal C.


Definition UnivProductFromPullback (c d a : C) (f : a --> c) (g : a --> d):
total2
     (fun fg : a --> Pb T c d (TerminalArrow C T c) (TerminalArrow C T d) =>
      dirprod (fg;; PullbackPr1 C (Pb T c d (TerminalArrow C T c) (TerminalArrow C T d)) == f)
        (fg;; PullbackPr2 C (Pb T c d (TerminalArrow C T c) (TerminalArrow C T d)) == g)).
Proof.
 Check PullbackArrow.
  unfold Pullbacks in Pb.
  exists (PullbackArrow _ (Pb _ _ _ (TerminalArrow C T c)(TerminalArrow C T d)) _ f g
       (ArrowsToTerminal _ _ _ _ _)).
  split. 
  apply PullbackArrow_PullbackPr1 .
  apply PullbackArrow_PullbackPr2 .
Defined.
  


Lemma isProductCone_PullbackCone (c d : C):
   isProductCone C c d 
            (PullbackObject _ (Pb _ _ _ (TerminalArrow C T c)(TerminalArrow C T d)))
   (PullbackPr1 _ _  ) (PullbackPr2 _ _ ).
Proof.
  unfold isProductCone.
  intros a f g.
  exists (UnivProductFromPullback c d a f g).
  intro t.
  apply proofirrelevance.
  apply isapropifcontr.
  apply (isPullback_Pullback).
  apply ArrowsToTerminal.
Qed.

End product_from_pullback.













