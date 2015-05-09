Require Import Foundations.Generalities.uu0.
Require Import Foundations.hlevel1.hProp.
Require Import Foundations.hlevel2.hSet.

Require Import RezkCompletion.precategories.
Require Import RezkCompletion.functors_transformations.
Require Import SubstSystems.UnicodeNotations.
Require Import RezkCompletion.whiskering.
Require Import RezkCompletion.Monads.
Require Import RezkCompletion.limits.products.
Require Import RezkCompletion.limits.coproducts.
Require Import RezkCompletion.limits.initial.
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

Local Notation "C ⟦ a , b ⟧" := (precategory_morphisms (C:=C) a b) (at level 50).

Arguments θ_source {_ _} _ .
Arguments θ_target {_ _} _ .
Arguments θ_Strength1 {_ _ _} _ .
Arguments θ_Strength2 {_ _ _} _ .

Section Example_Signatures.

(** Define some examples of signatures

    For this, we implement basic building blocks for 
    - abstraction (precomposition with +1, i.e. F mapsto F ∘ option)
    - application (sends a functor F to F × F)
    - explicit flattening (sends F to F ∘ F)

*)


Variable C : precategory.
Variable hs : has_homsets C.

 Local Notation "'EndC'":= ([C, C, hs]) .
Local Notation "'Ptd'" := (precategory_Ptd C hs).
Local Notation "'U'" := (functor_ptd_forget C hs).

End Example_Signatures.