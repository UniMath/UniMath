Require Import UniMath.Foundations.Preamble.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.bicategories.prebicategory.

Notation "a -1-> b" := (homprecat a b)(at level 50).
Notation "f ;1; g" := (compose_1mor f g) (at level 50, format "f ;1; g", no associativity).
Notation "a -2-> b" := (precategory_morphisms a b)(at level 50).
Notation "alpha ;v; beta" := (compose alpha beta) (at level 50, format "alpha ;v; beta", no associativity).
Notation "alpha ;i; beta" := (iso_comp alpha beta) (at level 50, format "alpha ;i; beta", no associativity).
Notation "alpha ;h; beta" := (compose_2mor_horizontal alpha beta) (at level 50, format "alpha ;h; beta").
Notation "alpha ;hi; beta" := (compose_2mor_iso_horizontal alpha beta) (at level 50, format "alpha ;hi; beta").
