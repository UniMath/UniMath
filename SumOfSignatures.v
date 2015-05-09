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
Local Notation "α 'øø' Z" := (# (pre_composition_functor_data _ _ _ hs _ Z) α) (at level 25).

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
       apply pathsinv0.
       Check CoproductOfArrows_comp.
       match goal with |[|- CoproductOfArrows _ _ _ ?f ?g ;;
                            CoproductOfArrows _ _ _ ?f' ?g' ;; _ = _ ] =>
              
         assert (T:= CoproductOfArrows_comp _ CC _ _ _ _ _ _ f g f' g') end.
       match goal with |[T: _ = ?e |- _ ;; _ ;; ?f = _ ] =>
            transitivity (e ;; f) end.
       { apply cancel_postcomposition.
         apply T. }
       
       clear T.
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


Section sum_of_hss.


Local Notation "'U'" := (functor_ptd_forget C hs).
Local Notation "'Ptd'" := (precategory_Ptd C hs).
Local Notation "'EndC'":= ([C, C, hs]) .

Variable T : hss _ _ H1 θ1.

Definition eta := (ptd_pt _ (pr1 (pr1 T))).
Definition tau := τ _ _ _ T.

Variable ExtH : H2 (U T) ⇒ U T. 

Variable ExtH_compat : ∀ Z (f : Z ⇒ _ ), 
  ExtH øø (U Z) ;; fbracket C hs H1 θ1 T f =
                        θ2 (prodcatpair C hs (U T) Z) ;; # H2 (fbracket C hs H1 θ1 T f) ;; ExtH.

Definition extended_Alg : Alg C hs H.
Proof.
  exists (pr1 (pr1 T)).
  exact (CoproductArrow _ (Coproducts_functor_precat _ _  _ _ _ _ )
           tau ExtH).
Defined.

Definition extended_bracket : bracket C hs H θ extended_Alg.
Proof.
  unfold bracket.
  intros Z f.
  set (X:= fbracket _ _ _ _ T f).
  assert (X' : # U f =
      # (pre_composition_functor_data C C C hs hs (U Z))
        (ptd_pt C (pr1 extended_Alg));; X
      × θ (prodcatpair C hs (U extended_Alg) Z);; # H X;;
        τ C hs H extended_Alg =
        # (pre_composition_functor_data C C C hs hs (U Z))
          (τ C hs H extended_Alg);; X).
  { split.
    - apply fbracket_η.
    - unfold X.
      apply nat_trans_eq; try assumption.
      intro c; simpl.
      unfold bla1.
      unfold coproduct_nat_trans_data.
      simpl.
      assert (A:= @precompWithCoproductArrow C).
      assert (B:=A _ _  (CC (pr1 (H1 (pr1 (pr1 (pr1 T)))) ((pr1 Z) c))
        (pr1 (H2 (pr1 (pr1 (pr1 T)))) ((pr1 Z) c)))).
        clear A.
      assert (D:= B _ _  (CC (pr1 (H1 (functor_composite (pr1 Z) (pr1 (pr1 (pr1 T))))) c)
        (pr1 (H2 (functor_composite (pr1 Z) (pr1 (pr1 (pr1 T))))) c))
     (pr1 (θ1 (prodcatpair C hs (pr1 (pr1 (pr1 T))) Z)) c)
     (pr1 (θ2 (prodcatpair C hs (pr1 (pr1 (pr1 T))) Z)) c)).
        clear B.
          rewrite D. clear D.
      unfold coproduct_nat_trans_in1_data.
      unfold coproduct_nat_trans_in2_data.
      assert (A:=@precompWithCoproductArrow C).
      assert (B:= A _ _  (CC ((pr1 (H1 (pr1 (pr1 (pr1 T))))) ((pr1 Z) c))
        ((pr1 (H2 (pr1 (pr1 (pr1 T))))) ((pr1 Z) c)))).
       clear A.
      assert (D:= B _ _ (CC (pr1 (H1 (U T)) c) (pr1 (H2 (U T)) c))).
        clear B.
      assert (E:= D  (pr1 (θ1 (prodcatpair C hs (pr1 (pr1 (pr1 T))) Z)) c;;
                        (pr1 (# H1 (fbracket C hs H1 θ1 T f)) c))
                     (pr1 (θ2 (prodcatpair C hs (pr1 (pr1 (pr1 T))) Z)) c;;
                        (pr1 (# H2 (fbracket C hs H1 θ1 T f)) c))
                       _ 
                       (tau c) 
                       (pr1 ExtH c)).
        clear D.
      match goal with |[ E : _ = ?x |- _ ] => transitivity x end.
        repeat rewrite assoc.
        apply E.
      clear E. apply pathsinv0.
      apply CoproductArrowUnique.
      + assert (A:=CoproductIn1Commutes C). 
        rewrite assoc.
        assert (B:= A _ _ (CC ((pr1 (H1 (pr1 (pr1 (pr1 T))))) ((pr1 Z) c))
        ((pr1 (H2 (pr1 (pr1 (pr1 T))))) ((pr1 Z) c)))).
        clear A.
        assert (D:= B _  (tau (pr1 (pr1 (pr1 Z)) c))).
        simpl in *.
          assert (E:= D 
                         (pr1 ExtH (pr1 (pr1 (pr1 Z)) c))).
         clear B D.
       match goal with |[ E : _ = ?x |- _ ;; _ ;; ?z = _ ] => transitivity (x ;; z) end.
        * apply cancel_postcomposition. apply E.
        * clear E.
          assert (A:= fbracket_τ _ _ _ _ T f).
          assert (B:= nat_trans_eq_pointwise _ _ _ _ _ _ A).
         apply pathsinv0, B.
     + rewrite assoc.
        assert (A:=CoproductIn2Commutes C). 
        assert (B:= A _ _ (CC ((pr1 (H1 (pr1 (pr1 (pr1 T))))) ((pr1 Z) c))
        ((pr1 (H2 (pr1 (pr1 (pr1 T))))) ((pr1 Z) c)))).
        clear A.
        assert (D:= B _  (tau (pr1 (pr1 (pr1 Z)) c))).
          assert (E:= D 
                         (pr1 ExtH (pr1 (pr1 (pr1 Z)) c))).
          clear B D.
         match goal with |[ E : _ = ?x |- _ ;; _ ;; ?z = _ ] => transitivity (x ;; z) end.
          * apply cancel_postcomposition. apply E.
          * clear E.
            simpl.
            assert (X0 :  ExtH øø (U Z) ;; fbracket C hs H1 θ1 T f =
                        θ2 (prodcatpair C hs (U T) Z) ;; # H2 (fbracket C hs H1 θ1 T f) ;; ExtH). 
            { apply ExtH_compat. }            
            apply (nat_trans_eq_pointwise _ _ _ _ _ _ X0).
      }
  
    exists (tpair _ X X').
  
    intros [t tp].
    apply total2_paths_second_isaprop.
  - simpl.
    apply isapropdirprod.
    * apply isaset_nat_trans. apply hs.
    * apply isaset_nat_trans. apply hs.
  - simpl.
    unfold X.
    apply fbracket_unique.
    + apply (pr1 tp). 
    + apply nat_trans_eq; try assumption.
      intro c; simpl.
      assert (A := nat_trans_eq_pointwise _ _ _ _ _ _ (pr2 tp) c).
      simpl in A.
      unfold bla1 in A.
      unfold coproduct_nat_trans_data in A.
      
      admit. (* should follow from "left side" of A *)
Defined.      


Definition extended_hss : hss _ _ H θ.
Proof.
  exists extended_Alg.
  exact extended_bracket.
Defined.  

End sum_of_hss.



Section hss_of_sum.

(** Goal of this section was to show that a hss on a sum
    induces a hss on the components.
    But that is not true, because substitution on the
    components cannot proved to be unique
*)

Local Notation "'U'" := (functor_ptd_forget C hs).
Local Notation "'Ptd'" := (precategory_Ptd C hs).
Local Notation "'EndC'":= ([C, C, hs]) .

Variable T : hss _ _ H θ.

Definition eta' := (ptd_pt _ (pr1 (pr1 T))).

Definition tau' := τ _ _ _ T.

Definition inj : H1 (U T) ⇒ H (U T).
Proof.
  set (X := @CoproductIn1 _ (H1 (U T)) (H2 (U T))).
  set (X1 := X (Coproducts_functor_precat _ _ CC _ _ _ )).
  exact X1.
Defined.
  
Definition H1_Alg : Alg C hs H1.
Proof.
  exists (pr1 (pr1 T)).
  exact (inj ;; tau').
Defined.

Definition summand_bracket : bracket C hs H1 θ1 H1_Alg.
Proof.
  unfold bracket.
  intros Z f.
  simpl in f.
  set (X := fbracket _ hs H θ T f).
  assert ( X' :  
      # U f =
      # (pre_composition_functor_data C C C hs hs (U Z))
        (ptd_pt C (pr1 H1_Alg));; X
      × θ1 (prodcatpair C hs (U H1_Alg) Z);; # H1 X;; τ C hs H1 H1_Alg =
        # (pre_composition_functor_data C C C hs hs (U Z)) (τ C hs H1 H1_Alg);;
        X).
  { split.
    - simpl.
      set (H3 := fbracket_η C hs H θ T f).
      exact H3.
    - set (H3 := fbracket_τ C hs H θ T f).
      simpl.
      unfold tau.
      unfold inj.
      simpl.
      apply nat_trans_eq; try assumption.
      intro c; simpl.
      unfold coproduct_nat_trans_in1_data.
      simpl.
      assert (H3':= nat_trans_eq_weq _ _ hs _ _ _ _ H3 c).
      clear H3. simpl in H3'.
      unfold bla1 in H3'. unfold coproduct_nat_trans_data in H3'.
      simpl in H3'.
      unfold coproduct_nat_trans_in1_data in H3'.
      simpl in *.
      unfold X.
      
      match goal with |[H3' : ?z = _ |- _ = ?x ;; _ ;; _ ] =>
          transitivity (x ;; z) end.
      Focus 2.
        repeat rewrite <- assoc.
        apply maponpaths.
        repeat rewrite <- assoc in H3'.
        apply H3'.

      clear H3'.  
      repeat rewrite assoc.
      apply cancel_postcomposition.
      
      clear X.
      assert (X:= @CoproductOfArrowsIn1 C ).
      
      assert (X1 := X _ _ (CC (pr1 (H1 (U T)) (pr1 (pr1 (pr1 Z)) c))
                       (pr1 (H2 (U T)) (pr1 (pr1 (pr1 Z)) c)))).
      assert (X2 := X1 _ _  (CC (pr1 (H1 (functor_composite (pr1 Z) (U T))) c)
        (pr1 (H2 (functor_composite (pr1 Z) (U T))) c))).
         clear X X1.
      rewrite X2. clear X2.
      repeat rewrite <- assoc.
      apply maponpaths.
      rewrite CoproductIn1Commutes.
      apply idpath.
  }
  exists (tpair _ X X').
  intro t.
  destruct t as [t tp].
  apply total2_paths_second_isaprop.
  + simpl. 
    apply isapropdirprod.
    * apply isaset_nat_trans. apply hs.
    * apply isaset_nat_trans. apply hs.
  + simpl.
    unfold X.
    apply fbracket_unique.
    * apply (pr1 tp).
    * Abort. (* here we'd need to say something about H2, but we can't *)
       
Definition T' : hss _ _ H1 θ1.
Proof.
  exists H1_Alg.
  Abort.

End hss_of_sum.

End sum_of_signatures.