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
     (fun fg : a --> Pb T c d (TerminalArrow c) (TerminalArrow d) =>
      dirprod (fg;; PullbackPr1 C (Pb T c d (TerminalArrow c) (TerminalArrow d)) == f)
        (fg;; PullbackPr2 C (Pb T c d (TerminalArrow c) (TerminalArrow d)) == g)).
Proof.
  unfold Pullbacks in Pb.
  exists (PullbackArrow _ (Pb _ _ _ (TerminalArrow c)(TerminalArrow d)) _ f g
       (ArrowsToTerminal _ _ _ _ _)).
  split. 
  apply PullbackArrow_PullbackPr1 .
  apply PullbackArrow_PullbackPr2 .
Defined.
  


Lemma isProductCone_PullbackCone (c d : C):
   isProductCone C c d 
            (PullbackObject _ (Pb _ _ _ (TerminalArrow c)(TerminalArrow (T:=T) d)))
   (PullbackPr1 _ _  ) (PullbackPr2 _ _ ).
Proof.
  intros a f g.
  exists (UnivProductFromPullback c d a f g).
  intro t.
  apply proofirrelevance,
        isapropifcontr,
        isPullback_Pullback,
        ArrowsToTerminal.
Qed.

Definition ProductCone_PullbackCone (c d : C) : ProductCone _ c d.
Proof.
  exists
  (tpair _ (PullbackObject _ (Pb _ _ _ (TerminalArrow c)(TerminalArrow (T:=T) d)))
               (dirprodpair  (PullbackPr1 _ _  ) (PullbackPr2 _ _ ))).
 exact (isProductCone_PullbackCone c d).
Defined.

Definition ProductsFromPullbacks : Products C := ProductCone_PullbackCone.


Arguments ProductObject [C] c d {_}.
Local Notation "c 'x' d" := (ProductObject  c d )(at level 5).
Check (fun c d : C => c x d).

End product_from_pullback.















