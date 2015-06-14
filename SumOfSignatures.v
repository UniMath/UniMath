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
Require Import SubstSystems.Auxiliary.
Require Import SubstSystems.PointedFunctors.
Require Import SubstSystems.ProductPrecategory.
Require Import SubstSystems.HorizontalComposition.
Require Import SubstSystems.PointedFunctorsComposition.
Require Import SubstSystems.Signatures.
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
  

Lemma is_nat_trans_θ_ob : 
 is_nat_trans (θ_source_functor_data C hs H) (θ_target_functor_data C hs H)
     θ_ob.
Proof.
    intros [X Z] [X' Z'] [α β].  
(*  simpl in *.
  unfold θ_source_mor.
  simpl.
  unfold θ_target_mor.
  simpl.
  unfold coproduct_functor_mor.
*)
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
    
    
    eapply pathscomp0; [ | eapply pathsinv0; apply CoproductOfArrows_comp]. (* replaces commented code below *)
    
    
(*    
    assert (T:=CoproductOfArrows_comp C CC).
    
    match goal with |[ |- _ = (CoproductOfArrows C (CC ?a ?b) (CC ?c ?d) ?f ?g) ;; _ ] =>
                       assert (T2 := T a b c d) end.
    clear T.
    assert (T3:= T2 (pr1 (H1 (functor_composite (pr1 Z') X')) c)
                 (pr1 (H2 (functor_composite (pr1 Z') X')) c)).
    clear T2.
    match goal with |[ |- _ = (CoproductOfArrows _ _ _  ?f ?g) ;; _ ] =>
            assert (T4 := T3 f g) end.
    clear T3.
    match goal with |[ |- _ = _ ;; CoproductArrow _ _ (?a ;; _ ) (?b ;; _ ) ] =>
          assert (T5 := T4 a b) end.
    clear T4.
    match goal with |[H : _ = ?g |- _ ] => transitivity g end.
     Focus 2.
     apply (!T5).

    clear T5.
*)
    eapply pathscomp0. apply cancel_postcomposition. apply CoproductOfArrows_comp.
(*
    assert (T:=CoproductOfArrows_comp C CC).
    assert (T':= T _ _ _ _ _ _ 
             (pr1 (# H1 α) ((pr1 Z) c))
             (pr1 (# H2 α) ((pr1 Z) c))
             (# (pr1 (H1 X')) ((pr1 β) c))
             (# (pr1 (H2 X')) ((pr1 β) c))).
    simpl in *. clear T.
    match goal with |[T' : _ = ?e |- _ ;; _ ;; ?h = _ ] =>
       transitivity (e ;; h) end.
    + apply cancel_postcomposition.
      apply T'.
*)
    eapply pathscomp0. apply CoproductOfArrows_comp.
    
    apply CoproductOfArrows_eq.
 (*
    + clear T'.
      assert (T := CoproductOfArrows_comp C CC 
                   _ _ _ _ _ _ 
                   (pr1 (# H1 α) ((pr1 Z) c);; # (pr1 (H1 X')) ((pr1 β) c))
                   (pr1 (# H2 α) ((pr1 Z) c);; # (pr1 (H2 X')) ((pr1 β) c))
                   (pr1 (θ1 (prodcatpair C hs X' Z')) c)
                   (pr1 (θ2 (prodcatpair C hs X' Z')) c)).
      match goal with | [T : _ = ?e |- _ ] => transitivity e end.
      * apply T.
      * clear T. 
        apply CoproductOfArrows_eq.
*)        
           assert (Ha:= nat_trans_ax θ1).
           assert (Hb:= Ha _ _ (prodcatmor _ _ α β)). clear Ha.
           simpl in *.
           unfold θ_source_mor, θ_target_mor in Hb.
           simpl in *.
           assert (HA := nat_trans_eq_pointwise _ _ _ _ _ _ Hb c).
           apply HA.
           
           assert (Ha:= nat_trans_ax θ2).
           assert (Hb:= Ha _ _ (prodcatmor _ _ α β)). clear Ha.
           simpl in *.
           unfold θ_source_mor, θ_target_mor in Hb.
           simpl in *.
           assert (HA := nat_trans_eq_pointwise _ _ _ _ _ _ Hb c).
           apply HA.
Qed.           
           


   
Definition θ : θ_source H ⟶ θ_target H.
Proof.
  exists θ_ob.
  apply is_nat_trans_θ_ob.
Defined.

Lemma SumStrength1 : θ_Strength1 θ.
Proof.
  unfold θ_Strength1.
  intro X.
  apply nat_trans_eq. 
  - apply hs.
  - intro x.
    simpl.
    unfold bla1.
    unfold coproduct_nat_trans_data.
    
    eapply pathscomp0. apply precompWithCoproductArrow.
    
(*    
    assert (H:=@precompWithCoproductArrow C).
    assert (Ha := H _ _ (CC ((pr1 (H1 X)) ((pr1 (id_Ptd C hs)) x)) ((pr1 (H2 X)) ((pr1 (id_Ptd C hs)) x)))).
    clear H.
    assert (Hb := Ha _ _  (CC ((pr1 (H1 (functor_composite (pr1 (id_Ptd C hs)) X))) x)
        ((pr1 (H2 (functor_composite (pr1 (id_Ptd C hs)) X))) x))).
      clear Ha.
     assert (Hc := Hb  (pr1 (θ1 (prodcatpair C hs X (id_Ptd C hs))) x)
                       (pr1 (θ2 (prodcatpair C hs X (id_Ptd C hs))) x)).
        clear Hb.
        rewrite Hc. clear Hc.
*)
  
    unfold coproduct_functor_ob.
      simpl.
     apply pathsinv0.
     apply Coproduct_endo_is_identity.
     + rewrite CoproductIn1Commutes.
       unfold θ_Strength1 in S11.
       assert (Ha := nat_trans_eq_pointwise _ _ _ _ _ _ (S11 X) x).
       rewrite assoc.
       match goal with |[H : _ = ?e |- _ ;; _ ;; ?f = _ ] => 
              transitivity (e ;; f) end.
       * apply cancel_postcomposition.
         apply Ha.
       * apply id_left.
    + rewrite CoproductIn2Commutes.
      assert (Ha := nat_trans_eq_pointwise _ _ _ _ _ _ (S21 X) x).
       rewrite assoc.
       match goal with |[H : _ = ?e |- _ ;; _ ;; ?f = _ ] => 
              transitivity (e ;; f) end.
       * apply cancel_postcomposition.
         apply Ha.
       * apply id_left.
Qed.

Lemma SumStrength2 : θ_Strength2 θ.
Proof.
  unfold θ_Strength2.
  intros X Z Z' Y α.
  apply nat_trans_eq; try assumption.
    intro x.
    simpl.
    unfold bla1.
    simpl.
    unfold coproduct_nat_trans_data.
    simpl.
    eapply pathscomp0. apply precompWithCoproductArrow.
(*
    assert (Ha := @precompWithCoproductArrow C).
    assert (Hb := Ha _ _ (CC ((pr1 (H1 X)) (pr1 Z' (pr1 Z x))) ((pr1 (H2 X)) (pr1 Z' (pr1 Z x))))).
    clear Ha.
    assert (Hc := Hb _ _ (CC ((pr1 (H1 (functor_composite (functor_composite (pr1 Z) (pr1 Z')) X))) x)
        ((pr1 (H2 (functor_composite (functor_composite (pr1 Z) (pr1 Z')) X))) x))
     (pr1 (θ1 (prodcatpair C hs X (ptd_composite C Z Z'))) x)
     (pr1 (θ2 (prodcatpair C hs X (ptd_composite C Z Z'))) x)  ).
      clear Hb.
     assert (Hd := Hc _ (pr1 (# H1 α) x;; coproduct_nat_trans_in1_data C C CC (H1 Y) (H2 Y) x)
     (pr1 (# H2 α) x;; coproduct_nat_trans_in2_data C C CC (H1 Y) (H2 Y) x)).
     clear Hc.
     match goal with |[ H : _ = ?e |- _ ] => transitivity e end.
     { apply Hd. }
     
     clear Hd.
*)
       apply pathsinv0.
       eapply pathscomp0. apply cancel_postcomposition. apply CoproductOfArrows_comp.
(*
       eapply pathscomp0. apply precompWithCoproductArrow.
       
       Search (CoproductArrow _ _ _ _ _ _ = CoproductArrow _ _ _ _ _ _ ).
       
       apply CoproductArrow_eq.
  *)     
       
(*
       match goal with |[|- CoproductOfArrows _ _ _ ?f ?g ;;
                            CoproductOfArrows _ _ _ ?f' ?g' ;; _ = _ ] =>
              
         assert (T:= CoproductOfArrows_comp _ CC _ _ _ _ _ _ f g f' g') end.
       match goal with |[T: _ = ?e |- _ ;; _ ;; ?f = _ ] =>
            transitivity (e ;; f) end.
       { apply cancel_postcomposition.
         apply T. }
       
       clear T.
*)
       apply precompWithCoproductArrow_eq.
       - assert (Ha:=S12 X Z Z' Y α).
         simpl in Ha.
         rewrite assoc.
         rewrite assoc.
         apply cancel_postcomposition.
         assert (Hb := nat_trans_eq_pointwise _ _ _ _ _ _ Ha).
         apply Hb.
       - assert (Ha:=S22 X Z Z' Y α).
         simpl in Ha.
         rewrite assoc.
         rewrite assoc.
         apply cancel_postcomposition.
         assert (Hb := nat_trans_eq_pointwise _ _ _ _ _ _ Ha).
         apply Hb.       
Qed.

End sum_of_signatures.