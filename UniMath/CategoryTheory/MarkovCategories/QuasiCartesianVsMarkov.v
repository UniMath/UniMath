(*********************************************
An Alternative Axiomatization of Markov Categories

Cartesian categories have an equational presentation using 
pairing and projections. We adapt this presentation to give an
alternative axiomatization of Markov categories. 
* The advantage is that reasoning about coherence 
  in the new axioms is much simpler and easy to automate.
* Our presentation becomes implicational instead of equational
  because some η-laws only hold for deterministic morphisms.

It also seems related to the equational presentation 
of the CD calculus, and centrality in Freyd categories

We call this presentation "quasicartesian".
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.


Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.
Require Import UniMath.CategoryTheory.MarkovCategories.QuasiCartesian.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section MarkovToQuasiCartesian.
  Context {C : markov_category}.


End MarkovToQuasiCartesian.

Section QuasiCartesianToMarkov.
  Context {C : quasicartesian_category}.


End QuasiCartesianToMarkov.
