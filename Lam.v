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
Require Import SubstSystems.Signatures.
Require Import SubstSystems.SubstitutionSystems.
Require Import SubstSystems.FunctorsPointwiseCoproduct.
Require Import SubstSystems.FunctorsPointwiseProduct.
Require Import SubstSystems.EndofunctorsMonoidal.

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

Section Preparations.

Variable C : precategory.
Variable hs : has_homsets C.
Variable CP : Products C.
Variable CC : Coproducts C.
Variable terminal : Terminal C.
Let one : C :=  @TerminalObject C terminal.

Definition square_functor := product_functor C C CP (functor_identity C) (functor_identity C).

Section Constant_Functor.

Variable c: ob C.

Definition constant_functor_data: functor_data C C :=
   functor_data_constr C C (fun a => c) (fun (a b : ob C) f => identity _) .

Lemma is_functor_constant: is_functor constant_functor_data.
Proof.
  split; simpl.
  red; intros; apply idpath.
  red; intros; simpl.
  apply pathsinv0.
  apply id_left.
Qed.

Definition constant_functor: functor C C := tpair _ _ is_functor_constant.

End Constant_Functor.

Definition option_functor: functor C C := coproduct_functor _ _ CC (constant_functor one) (functor_identity C).

End Preparations.


Section Lambda.

Variable C : precategory.
Variable hs : has_homsets C.

(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C, hs]) .

Variable terminal : Terminal C.

Variable CC : Coproducts C.
Variable CP : Products C.

Let one : C :=  @TerminalObject C terminal.

(** 
   [App_H (X) (A) :=  X(A) × X(A)]
*)
Definition App_H : functor EndC EndC.
Proof.
  apply square_functor.
  apply Products_functor_precat.
  exact CP.
Defined.

(** 
   [Abs_H (X) := X o option]
*)  

Definition Abs_H_ob (X: EndC): functor C C := functor_composite (option_functor _ CC terminal) X.
Definition Abs_H_mor_nat_trans_data (X X': EndC)(α: X ⇒ X'): ∀ c, Abs_H_ob X c ⇒ Abs_H_ob X' c.
Proof.
  intro.
  unfold Abs_H_ob.
  red. simpl. apply α.
Defined.
  
Lemma is_nat_trans_Abs_H_mor_nat_trans_data  (X X': EndC)(α: X ⇒ X'): is_nat_trans _ _ (Abs_H_mor_nat_trans_data X X' α).
Proof.
  red.
  intros c c' f.
  destruct α as [α α_nat_trans].
  unfold Abs_H_mor_nat_trans_data, Abs_H_ob.
  simpl.
  apply α_nat_trans.
 Qed.
  
Definition Abs_H_mor (X X': EndC)(α: X ⇒ X'): (Abs_H_ob X: ob EndC) ⇒ Abs_H_ob X'.
Proof.
  exists (Abs_H_mor_nat_trans_data X X' α).
  exact (is_nat_trans_Abs_H_mor_nat_trans_data X X' α).
Defined.
  
Definition Abs_H_functor_data: functor_data EndC EndC.
Proof.
  exists Abs_H_ob.
  exact Abs_H_mor.
Defined.

Lemma is_functor_Abs_H_data: is_functor Abs_H_functor_data.
Proof.
  red.
  split; red.
  + intros X.
    unfold Abs_H_functor_data.
    simpl.
    apply nat_trans_eq; try assumption.
    intro c.
    unfold Abs_H_mor.
    simpl.
    apply idpath.
  + intros X X' X'' α β.
    unfold Abs_H_functor_data.
    simpl.
    apply nat_trans_eq; try assumption.
    intro c.
    unfold Abs_H_mor.
    simpl.
    apply idpath.
Qed.

Definition Abs_H : functor [C, C, hs] [C, C, hs] := tpair _ _ is_functor_Abs_H_data.


(** 
   [Flat_H (X) := X o X]
   
   ingredients:
     - functor_composite in RezkCompletion.functors_transformations 
     - map given by horizontal composition in Substsystems.HorizontalComposition
 
 Alternatively : free in two arguments, then precomposed with diagonal
 
*)
Definition Flat_H_ob (X: EndC): functor C C := functor_composite X X.
Definition Flat_H_mor (X X': EndC)(α: X ⇒ X'): (Flat_H_ob X: ob EndC) ⇒ Flat_H_ob X' := α ∙∙ α.
Definition Flat_H_functor_data: functor_data EndC EndC.
Proof.
  exists Flat_H_ob.
  exact Flat_H_mor.
Defined.

Lemma is_functor_Flat_H_data: is_functor Flat_H_functor_data.
Proof.
  red.
  split; red.
  + intros X.
    unfold Flat_H_functor_data.
    simpl.
    unfold Flat_H_mor.
    apply nat_trans_eq; try assumption.
    intro c.
    simpl.
    rewrite id_left.
    apply functor_id.
  + intros X X' X'' α β.
    unfold Flat_H_functor_data.
    simpl.
    unfold Flat_H_mor.
    apply nat_trans_eq; try assumption.
    intro c.
    simpl.
    destruct β as [β β_is_nat]; simpl.
    rewrite functor_comp.
    repeat rewrite <- assoc.
    apply maponpaths.
    repeat rewrite assoc.
    rewrite β_is_nat.
    apply idpath.
Qed.

Definition Flat_H : functor [C, C, hs] [C, C, hs] := tpair _ _ is_functor_Flat_H_data.



(** here definition of suitable θ's together with their strength laws  *)


Definition App_θ_data: ∀ XZ, (θ_source App_H)XZ ⇒ (θ_target App_H)XZ.
Proof.
  intro XZ.
  apply nat_trans_id.
Defined.

Lemma is_nat_trans_App_θ_data: is_nat_trans _ _ App_θ_data.
Proof.
  red.
  unfold App_θ_data.
  intros XZ XZ' αβ.
(* the following only for better readability: *)
  destruct XZ as [X Z];
  destruct XZ' as [X' Z'];
  destruct αβ as [α β];
  simpl in *.
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  rewrite id_left.
  rewrite id_right.
  unfold product_nat_trans_data, product_functor_mor.
  unfold ProductOfArrows.
  eapply pathscomp0.
  apply precompWithProductArrow.
  simpl.
  unfold product_nat_trans_pr1_data. unfold product_nat_trans_pr2_data.
  simpl.
  apply ProductArrowUnique.
  + rewrite ProductPr1Commutes.
    repeat rewrite assoc.
    rewrite ProductPr1Commutes.
    apply idpath.
  + rewrite ProductPr2Commutes.
    repeat rewrite assoc.
    rewrite ProductPr2Commutes.
    apply idpath.
Qed.

Definition App_θ: nat_trans (θ_source App_H) (θ_target App_H) :=
  tpair _ _ is_nat_trans_App_θ_data.

Lemma App_θ_strenght1_int: θ_Strength1_int _  _ _ App_θ.
Proof.
  red.
  intro.
  unfold App_θ, App_H.  
  simpl.
  unfold App_θ_data. 
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  rewrite id_left.
  unfold product_nat_trans_data.
  apply pathsinv0.
  apply ProductArrowUnique.
  + rewrite id_left.
    unfold EndofunctorsMonoidal.λ_functor.
    unfold EndofunctorsMonoidal.ρ_functor.
    simpl.    
    rewrite id_right.
    apply idpath.
  + rewrite id_left.
    unfold EndofunctorsMonoidal.λ_functor.
    unfold EndofunctorsMonoidal.ρ_functor.
    simpl.    
    rewrite id_right.
    apply idpath.
Qed.


Lemma App_θ_strenght2_int: θ_Strength2_int _  _ _ App_θ.
Proof.
  red.
  intros.
  unfold App_θ, App_H.  
  simpl.
  unfold App_θ_data. 
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  do 3 rewrite id_left.
  unfold product_nat_trans_data.
  apply pathsinv0.
  apply ProductArrowUnique.
  + rewrite id_left.
    unfold EndofunctorsMonoidal.α_functor.
    simpl.    
    rewrite id_right.
    apply idpath.
  + rewrite id_left.
    unfold EndofunctorsMonoidal.α_functor.
    simpl.    
    rewrite id_right.
    apply idpath.
Qed.


Definition Abs_θ_data_data: ∀ XZ A, ((θ_source Abs_H)XZ: functor C C) A ⇒ ((θ_target Abs_H)XZ: functor C C) A.
Proof.
  intro XZ.
  destruct XZ as [X Z].
  simpl.
  intro A.
  apply (functor_on_morphisms (functor_data_from_functor _ _ X)).
  unfold coproduct_functor_ob.
  unfold constant_functor.
  simpl.
  destruct Z as [Z e].
  simpl.
  apply CoproductArrow.
  + exact (CoproductIn1 _ _ ;; nat_trans_data e (CoproductObject C (CC terminal A))).
  + exact (functor_on_morphisms (functor_data_from_functor _ _ Z) (CoproductIn2 _ (CC terminal A))).
Defined.

Lemma is_nat_trans_Abs_θ_data_data: ∀ XZ, is_nat_trans _ _ (Abs_θ_data_data XZ).
Proof.
  intros [X [Z e]].
  red.
  intros c c' f.
  simpl.
  rewrite <- functor_comp.
  rewrite <- functor_comp.
  apply maponpaths.
  unfold coproduct_functor_mor.
  eapply pathscomp0.
  apply precompWithCoproductArrow.
  eapply pathscomp0.
Focus 2.
  apply (!(postcompWithCoproductArrow _ _ _ _ _)).
  simpl.
  rewrite id_left.
  rewrite <- assoc.
  rewrite <- functor_comp.
  rewrite <- functor_comp.
  destruct e as [e e_is_nat].
  simpl.
  apply CoproductArrow_eq.
  + assert (NN :=  e_is_nat _ _ (CoproductOfArrows C (CC terminal c) (CC terminal c')
         (identity terminal) f)).
    match goal with |[ H1: _ = ?f;;?g |- _ = ?h ;; _ ] => 
         transitivity (h;;(f;;g)) end.
    * rewrite <- NN.
      clear NN.
      unfold functor_identity.   
      simpl.
      rewrite assoc.
      rewrite CoproductOfArrowsIn1.
      rewrite id_left.
      apply idpath.
    * apply idpath. 
  + apply maponpaths.
    eapply pathscomp0.
Focus 2.
    apply (!(CoproductOfArrowsIn2 _ _ _ _ _ )).
    apply idpath.
Qed.       


Definition Abs_θ_data: ∀ XZ, (θ_source Abs_H)XZ ⇒ (θ_target Abs_H)XZ.
Proof.
  intro XZ.
  exact (tpair _ _ (is_nat_trans_Abs_θ_data_data XZ)).
Defined.

Lemma is_nat_trans_Abs_θ_data: is_nat_trans _ _ Abs_θ_data.
Proof.
  red.
  intros XZ XZ' αβ.
  destruct XZ as [X [Z e]].
  destruct XZ' as [X' [Z' e']].
  destruct αβ as [α β].
  simpl in *.
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  destruct α as [α α_is_nat].
  destruct β as [β β_is_pointed].
  simpl in *.
  unfold constant_functor.
  unfold coproduct_functor_ob.
  simpl.
  rewrite assoc.
  rewrite α_is_nat.
  do 2 rewrite <- assoc.
  apply maponpaths.
  do 2 rewrite <- functor_comp.
  apply maponpaths.
  unfold coproduct_functor_mor, constant_functor_data.
  simpl.  
  rewrite precompWithCoproductArrow.
  rewrite postcompWithCoproductArrow.
  apply CoproductArrow_eq.
  + rewrite id_left.
    rewrite <- assoc.
    rewrite β_is_pointed.
    apply idpath.
  + destruct β as [β β_is_nat].
    simpl in *.
    apply pathsinv0.
    apply β_is_nat.
Qed.

Definition Abs_θ: nat_trans (θ_source Abs_H) (θ_target Abs_H) :=
  tpair _ _ is_nat_trans_Abs_θ_data.
 
Lemma Abs_θ_strenght1_int: θ_Strength1_int _  _ _ Abs_θ.
Proof.
  red.
  intro.
  unfold Abs_θ, Abs_H.  
  simpl.
  unfold Abs_θ_data. 
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  rewrite id_right.
  apply functor_id_id.
  apply pathsinv0.
  apply CoproductArrowUnique.
  + apply idpath.
  + apply id_right.
Qed.

Lemma Abs_θ_strenght2_int: θ_Strength2_int _  _ _ Abs_θ.
Proof.
  red.
  intros.
  unfold Abs_θ, Abs_H.  
  simpl.
  unfold Abs_θ_data. 
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  rewrite id_left.
  rewrite id_right.
  rewrite <- functor_comp.
  apply maponpaths.
  clear X.
  destruct Z as [Z e];
  destruct Z' as [Z' e'];
  simpl.
  eapply pathscomp0.
Focus 2.
  eapply pathsinv0.
  apply postcompWithCoproductArrow.
(*  destruct e as [e e_is_nat]. *)
  destruct e' as [e' e'_is_nat];
  simpl in *.
  apply CoproductArrow_eq.
  + rewrite <- assoc.
    assert (NN := e'_is_nat _ _ (e (CoproductObject C (CC terminal c)))).
    simpl in NN. (* is important for success of the trick *)
    match goal with |[ H1: _ = ?f;;?g |- ?h ;; _ = _ ] => 
         transitivity (h;;(f;;g)) end.
    * apply idpath.
    * rewrite <- NN.    
      clear NN.
      assert (NNN := e'_is_nat _ _ (CoproductArrow C (CC terminal (Z c))
         (CoproductIn1 C (CC terminal c);;
          e (CoproductObject C (CC terminal c)))
         (# Z (CoproductIn2 C (CC terminal c))))). 
      simpl in NNN.
      match goal with |[ H1: _ = ?f;;?g |- _ = ?h ;; _] => 
         transitivity (h;;(f;;g)) end.
      - rewrite <- NNN.
        clear NNN.
        do 2 rewrite assoc.        
        rewrite CoproductIn1Commutes.
        apply idpath.
      - apply idpath.
  + rewrite <- functor_comp.
    apply maponpaths.
    eapply pathscomp0.
Focus 2.
    eapply pathsinv0.
    apply CoproductIn2Commutes.
    apply idpath.
Qed.


Definition Flat_θ_data: ∀ XZ, (θ_source Flat_H)XZ ⇒ (θ_target Flat_H)XZ.
Proof.
  intro XZ.
  destruct XZ as [X [Z e]].
  simpl.
  set (h:= nat_trans_comp (λ_functor_inv _ X) ((nat_trans_id _) ∙∙ e)).
  exact (nat_trans_comp (α_functor_inv _ Z X X) (h ∙∙ (nat_trans_id (functor_composite Z X)))).
Defined.

Lemma is_nat_trans_Flat_θ_data: is_nat_trans _ _ Flat_θ_data.
Proof.
  red.
  intros XZ XZ' αβ.
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  destruct XZ as [X [Z e]];
  destruct XZ' as [X' [Z' e']];
  destruct αβ as [α β];
  simpl in *.
  destruct α as [α α_is_nat];
  destruct β as [[β β_is_nat] β_is_pointed];
  simpl in *.
  repeat rewrite id_left.
  do 4 rewrite functor_id.
  do 2 rewrite id_right.
  repeat rewrite <- assoc.
  do 3 rewrite <- functor_comp.
  repeat rewrite assoc.
  rewrite α_is_nat.
  repeat rewrite <- assoc.
  apply maponpaths.
  rewrite <- functor_comp.
  apply maponpaths.
  repeat rewrite assoc.
  rewrite β_is_pointed.
  destruct e as [e e_is_nat];
  destruct e' as [e' e'_is_nat];
  simpl in *.
  eapply pathscomp0.
Focus 2.
  apply e'_is_nat.
  apply idpath.
Qed.

Definition Flat_θ: nat_trans (θ_source Flat_H) (θ_target Flat_H) :=
  tpair _ _ is_nat_trans_Flat_θ_data.

Lemma Flat_θ_strenght1_int: θ_Strength1_int _  _ _ Flat_θ.
Proof.
  red.
  intro.
  unfold Flat_θ, Flat_H.  
  simpl.
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  repeat rewrite id_left.
  repeat rewrite functor_id.
  repeat rewrite id_left.
  apply idpath.
Qed.

Lemma Flat_θ_strenght2_int: θ_Strength2_int _  _ _ Flat_θ.
Proof.
  red.
  intros.
  destruct Z as [Z e];
  destruct Z' as [Z' e'];
  simpl.
  apply nat_trans_eq; try assumption.
  intro c.
  simpl.
  repeat rewrite id_left.
  repeat rewrite <- functor_comp.
  apply maponpaths.
  repeat rewrite functor_id.
  repeat rewrite id_right.
  apply idpath.  
Qed.

(** finally, constitute the 3 signatures *)

Definition App_Sig: Signature C hs.
Proof.
  exists App_H.
  exists App_θ.
  split.
  + exact App_θ_strenght1_int.      
  + exact App_θ_strenght2_int.
Defined.

Definition Abs_Sig: Signature C hs.
Proof.
  exists Abs_H.
  exists Abs_θ.
  split.
  + exact Abs_θ_strenght1_int.      
  + exact Abs_θ_strenght2_int.
Defined.

Definition Flat_Sig: Signature C hs.
Proof.
  exists Flat_H.
  exists Flat_θ.
  split.
  + exact Flat_θ_strenght1_int.      
  + exact Flat_θ_strenght2_int.
Defined.

End Lambda.
