Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.CategoryTheory.UnicodeNotations.

Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.coequalizers.

Require Import UniMath.CategoryTheory.Epis.


(** Definition of an effective epimorphism.
An effective epimorphism p: A -> B is a morphism wich as a kernel pair and which
is the coequalizer of its kernel pair.
*)
Section EffectiveEpi.
  Context {C:precategory} {A B:C}.
  Variable (f: C ⟦A,B⟧). 
  
  Definition kernel_pair := Pullback  f f.

  Definition isEffective :=
    Σ  g:kernel_pair,
         (isCoequalizer (PullbackPr1 g)
                        (PullbackPr2 g) f (PullbackSqrCommutes g)).
End EffectiveEpi.

Definition HasEffectiveEpis (C:precategory) :=
  Π (A B:C) (f:C⟦A,B⟧), isEpi f -> isEffective f.
