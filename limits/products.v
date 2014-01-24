Require Import Foundations.Generalities.uuu.
Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.


Require Import RezkCompletion.pathnotations.
Import RezkCompletion.pathnotations.PathNotations.
Require Import RezkCompletion.auxiliary_lemmas_HoTT.
Require Import RezkCompletion.precategories.

Require Import RezkCompletion.limits.aux_lemmas_HoTT.
Require Import RezkCompletion.limits.terminal.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g)(at level 50).
