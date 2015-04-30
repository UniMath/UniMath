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

Section sum_of_signatures.

Variable C : precategory.
Variable hs : has_homsets C.
Variable PP : Products C.
Variable CC : Coproducts C.

(* should be proved somewhere *)

Local Notation "'CCC'" := (Coproducts_functor_precat C C CC hs : Coproducts [C, C, hs]).


Variables H1 H2 : functor [C, C, hs] [C, C, hs].

Variable θ1 : θ_source H1 ⟶ θ_target H1.
Variable θ2 : θ_source H2 ⟶ θ_target H2.

Variable S11 : θ_Strength1 θ1.
Variable S12 : θ_Strength2 θ1.
Variable S21 : θ_Strength1 θ2.
Variable S22 : θ_Strength2 θ2.


Definition H : functor [C, C, hs] [C, C, hs] := coproduct_functor _ _ CCC H1 H2.


Definition bla1 (X : [C, C] hs) (Z : precategory_Ptd C hs) :
   ∀ c : C, 
    (functor_composite_data (pr1 Z)
     (coproduct_functor_data C C CC (H1 X) (H2 X))) c
   ⇒ (coproduct_functor_data C C CC (H1 (functor_composite (pr1 Z) X))
       (H2 (functor_composite (pr1 Z) X))) c.
Proof.
  intro c.
  apply CoproductOfArrows.
  - set (T1 := θ1 (prodcatpair _ _ X Z)).
    set (T2 := pr1 T1 c).
    simpl in T2.
    exact T2.
  - exact (pr1 (θ2 (prodcatpair _ _ X Z)) c).
Defined.

Lemma bar (X : [C, C] hs) (Z : precategory_Ptd C hs):
   is_nat_trans
     (functor_composite_data (pr1 Z)
        (coproduct_functor_data C C CC (H1 X) (H2 X)))
     (coproduct_functor_data C C CC (H1 (functor_composite (pr1 Z) X))
        (H2 (functor_composite (pr1 Z) X))) (bla1 X Z).
Proof.
  intros x x' f.
  simpl.
  unfold bla1.
  simpl.
  unfold coproduct_functor_mor.
  assert (T:= CoproductOfArrows_comp C CC).
  assert (T1 := T _ _ _ _ _ _ 
           (# (pr1 (H1 X)) (# (pr1 Z) f)) (# (pr1 (H2 X)) (# (pr1 Z) f))
         (pr1 (θ1 (prodcatpair C hs X Z)) x') 
         (pr1 (θ2 (prodcatpair C hs X Z)) x')
         ).
  simpl in *.
  match goal with |[H : _ = ?g |- _ ] => transitivity g end.
  - apply T1.
  - clear T1.
    assert (T2 := T _ _ _ _ _ _ 
                   (pr1 (θ1 (prodcatpair C hs X Z)) x) 
                   (pr1 (θ2 (prodcatpair C hs X Z)) x)
                   (# (pr1 (H1 (functor_composite (pr1 Z) X))) f)
                   (# (pr1 (H2 (functor_composite (pr1 Z) X))) f) ).
    match goal with |[H : _ = ?g |- _ ] => transitivity g end.
    + apply CoproductOfArrows_eq.
      * apply (nat_trans_ax (θ1 (prodcatpair _ _ X Z))).
      * apply (nat_trans_ax (θ2 (prodcatpair _ _ X Z))).
    + apply (!T2). 
Qed.

Definition bla (X : [C, C] hs) (Z : precategory_Ptd C hs) :
   functor_composite_data (pr1 Z)
     (coproduct_functor_data C C CC (H1 X) (H2 X))
   ⟶ coproduct_functor_data C C CC (H1 (functor_composite (pr1 Z) X))
       (H2 (functor_composite (pr1 Z) X)).
Proof.
  exists (bla1 X Z).
  apply bar.
Defined.  


Definition θ_ob : ∀ XF, θ_source H XF ⇒ θ_target H XF. 
Proof.
  intro XZ.
  destruct XZ as [X Z].
  apply bla.
Defined.
  
   
Definition θ : θ_source H ⟶ θ_target H.
Proof.
  exists θ_ob.
  intros [X Z] [X' Z'] [α β].  
  simpl in *.
  unfold θ_source_mor.
  simpl.
  unfold θ_target_mor.
  simpl.
  unfold coproduct_functor_mor.
  apply nat_trans_eq.
  - apply hs.
  - intro c.
    simpl.
    unfold coproduct_nat_trans_data.
    unfold bla1; simpl.
    unfold coproduct_functor_mor.
    simpl.
    unfold coproduct_nat_trans_in2_data.
    unfold coproduct_nat_trans_in1_data.
    simpl.
    rewrite <- assoc.
(*    rewrite CoproductOfArrows_comp. *)
  admit.
Defined.

End sum_of_signatures.