Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Export UniMath.Bicategories.WkCatEnrichment.prebicategory.


(* Local Notation "C  'c×'  D" := (precategory_binproduct C D) (at level 75, right associativity). *)
Notation "a  '-1->'  b" := (homcat a b) (at level 50, left associativity).
Notation "f  '-2->'  g" := (@precategory_morphisms (_ -1->_) f g) (at level 50, left associativity).
Notation "alpha  ';v;'  beta" := (@compose (_ -1-> _) _ _ _ alpha beta) (at level 50, left associativity).
Notation "f  ';1;'  g" := (compose1 f g) (at level 50, left associativity).
Notation "alpha  ';h;'  beta" := (compose2h alpha beta) (at level 50, left associativity).
Notation "alpha  ';hi;'  beta" := (compose2h_iso alpha beta) (at level 50, left associativity).
