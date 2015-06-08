Require Import UniMath.Foundations.Generalities.uu0.
Require Import UniMath.Foundations.hlevel1.hProp.
Require Import UniMath.Foundations.hlevel2.hSet.

Require Import UniMath.RezkCompletion.precategories.
Require Import UniMath.RezkCompletion.functors_transformations.
Require Import SubstSystems.UnicodeNotations.
Require Import UniMath.RezkCompletion.whiskering.
Require Import UniMath.RezkCompletion.Monads.
Require Import UniMath.RezkCompletion.limits.products.
Require Import UniMath.RezkCompletion.limits.coproducts.
Require Import UniMath.RezkCompletion.limits.terminal.
Require Import SubstSystems.Auxiliary.
Require Import SubstSystems.PointedFunctors.
Require Import SubstSystems.ProductPrecategory.
Require Import SubstSystems.HorizontalComposition.
Require Import SubstSystems.PointedFunctorsComposition.
Require Import SubstSystems.SubstitutionSystems.
Require Import SubstSystems.FunctorsPointwiseCoproduct.

Local Notation "# F" := (functor_on_morphisms F)(at level 3).
Local Notation "F ⟶ G" := (nat_trans F G) (at level 39).
Arguments functor_composite {_ _ _} _ _ .
Arguments nat_trans_comp {_ _ _ _ _} _ _ .
Local Notation "G ∙ F" := (functor_composite F G : [ _ , _ , _ ]) (at level 35).
Local Notation "α ∙∙ β" := (hor_comp β α) (at level 20).
Ltac pathvia b := (apply (@pathscomp0 _ _ b _ )).

Local Notation "α 'ø' Z" := (pre_whisker Z α)  (at level 25).
Local Notation "Z ∘ α" := (post_whisker _ _ _ _ α Z) (at level 35).

Arguments θ_source {_ _} _ .
Arguments θ_target {_ _} _ .
Arguments θ_Strength1 {_ _ _} _ .
Arguments θ_Strength2 {_ _ _} _ .


Section Lambda.

Variable C : precategory.
Variable hs : has_homsets C.

Variable terminal : Terminal C.

Variable CC : Coproducts C.
Variable CP : Products C.

Let one : C :=  @TerminalObject C terminal.

Definition App_Sig : functor [C, C, hs] [C, C, hs].
(** 
   [App_Sig (X) (A) :=  X(A) × X(A)]
 
see FunctorsPointwiseCoproduct, do analogously for product 

*)

Definition Lam_Sig : functor [C, C, hs] [C, C, hs].
(** 
   [Lam_Sig (X) := X o option

   implement the functor (E + _) for fixed E

   needs terminal object

*)

Definition Flat_Sig : functor [C, C, hs] [C, C, hs].
(** 
   [Flat_Sig (X) := X o X]
   
   ingredients:
     - functor_composite in RezkCompletion.functors_transformations 
     - map given by horizontal composition in Substsystems.HorizontalComposition
     - functor laws for this thing : 
         functor_id, functor_comp
         id_left, id_right, assoc

 Alternatively : free in two arguments, then precomposed with diagonal
 
*)



(** here definition of suitable θ's  *)

(** finally, prove strength laws to yield the 3 signatures *)





