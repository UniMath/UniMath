Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.SubstitutionSystems.Auxiliary.
Require Import UniMath.SubstitutionSystems.PointedFunctors.
Require Import UniMath.SubstitutionSystems.ProductPrecategory.
Require Import UniMath.SubstitutionSystems.HorizontalComposition.
Require Import UniMath.SubstitutionSystems.PointedFunctorsComposition.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.FunctorsPointwiseCoproduct.

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
Arguments θ_Strength1_int {_ _ _} _ .
Arguments θ_Strength2_int {_ _ _} _ .

Section sum_of_signatures.

Variable C : precategory.
Variable hs : has_homsets C.
(* Variable PP : Products C. *)
Variable CC : Coproducts C.

Section construction.

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
  - exact (pr1 (θ1 (prodcatpair _ _ X Z)) c).
  - exact (pr1 (θ2 (prodcatpair _ _ X Z)) c).
Defined.

Lemma bar (X : [C, C] hs) (Z : precategory_Ptd C hs):
   is_nat_trans
     (functor_composite_data (pr1 Z)
        (coproduct_functor_data C C CC (H1 X) (H2 X)))
     (coproduct_functor_data C C CC (H1 (functor_composite (pr1 Z) X))
        (H2 (functor_composite (pr1 Z) X))) (bla1 X Z).
Proof.
  intros x x' f; simpl.
  unfold bla1; simpl.
  unfold coproduct_functor_mor.
  eapply pathscomp0; [ apply CoproductOfArrows_comp | ].
  eapply pathscomp0; [ | eapply pathsinv0; apply CoproductOfArrows_comp].
(*  
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
*)
    
  apply CoproductOfArrows_eq.
  * apply (nat_trans_ax (θ1 (prodcatpair _ _ X Z))).
  * apply (nat_trans_ax (θ2 (prodcatpair _ _ X Z))).
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
  intros [X Z] [X' Z'] [α β]. simpl in *.
  apply nat_trans_eq.
  - exact hs.
  - intro c; simpl.
    unfold coproduct_nat_trans_data;
    unfold bla1; simpl.
    unfold coproduct_functor_mor.
    unfold coproduct_nat_trans_in2_data.
    unfold coproduct_nat_trans_in1_data.
    (* on the right-hand side, there is a second but unfolded CoproductOfArrows in the row - likewise a first such on the left-hand side, to be treater further below *)
    
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
    + assert (Ha:= nat_trans_ax θ1 _ _ (prodcatmor _ _ α β)).
      apply (nat_trans_eq_pointwise _ _ _ _ _ _ Ha c).
    + assert (Ha:= nat_trans_ax θ2 _ _ (prodcatmor _ _ α β)).
      apply (nat_trans_eq_pointwise _ _ _ _ _ _ Ha).
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
    
    eapply pathscomp0. apply CoproductOfArrows_comp.
     apply pathsinv0.
     apply Coproduct_endo_is_identity.
     + rewrite CoproductOfArrowsIn1.
       unfold θ_Strength1 in S11.
       assert (Ha := nat_trans_eq_pointwise _ _ _ _ _ _ (S11 X) x).
       eapply pathscomp0; [ | apply id_left].
       apply cancel_postcomposition.
       apply Ha.
     + rewrite CoproductOfArrowsIn2.
       unfold θ_Strength1 in S21.
       assert (Ha := nat_trans_eq_pointwise _ _ _ _ _ _ (S21 X) x).
       eapply pathscomp0; [ | apply id_left].
       apply cancel_postcomposition.
       apply Ha.
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
    eapply pathscomp0. apply CoproductOfArrows_comp.
    apply pathsinv0.
    eapply pathscomp0. apply cancel_postcomposition. apply CoproductOfArrows_comp.
    unfold coproduct_nat_trans_in2_data.
    unfold coproduct_nat_trans_in1_data.
    eapply pathscomp0. apply CoproductOfArrows_comp.
    apply pathsinv0.
    apply CoproductOfArrows_eq.
       - assert (Ha:=S12 X Z Z' Y α).
         simpl in Ha.
         assert (Ha_x := nat_trans_eq_pointwise _ _ _ _ _ _ Ha x).
         apply Ha_x.
       - assert (Ha:=S22 X Z Z' Y α).
         simpl in Ha.
         assert (Ha_x := nat_trans_eq_pointwise _ _ _ _ _ _ Ha x).
         apply Ha_x.
Qed.

Variable S11' : θ_Strength1_int θ1.
Variable S12' : θ_Strength2_int θ1.
Variable S21' : θ_Strength1_int θ2.
Variable S22' : θ_Strength2_int θ2.

Lemma SumStrength1' : θ_Strength1_int θ.
Proof.
  clear S11 S12 S21 S22 S12' S22'.
  unfold θ_Strength1_int.
  intro X.
  apply nat_trans_eq. 
  - apply hs.
  - intro x.
    simpl.
    unfold bla1.
    unfold coproduct_nat_trans_data.
    
    eapply pathscomp0. apply CoproductOfArrows_comp.
     apply pathsinv0.
     apply Coproduct_endo_is_identity.
     + rewrite CoproductOfArrowsIn1.
       red in S11'.
       assert (Ha := nat_trans_eq_pointwise _ _ _ _ _ _ (S11' X) x).
       simpl in Ha.
       eapply pathscomp0; [ | apply id_left].
       apply cancel_postcomposition.
       apply Ha.
     + rewrite CoproductOfArrowsIn2.
       red in S21'.
       assert (Ha := nat_trans_eq_pointwise _ _ _ _ _ _ (S21' X) x).
       simpl in Ha.
       eapply pathscomp0; [ | apply id_left].
       apply cancel_postcomposition.
       apply Ha.
Qed.


Lemma SumStrength2' : θ_Strength2_int θ.
Proof.
  clear S11 S12 S21 S22 S11' S21'.
  unfold θ_Strength2_int.
  intros X Z Z'.
  apply nat_trans_eq; try assumption.
    intro x.
    simpl.
    rewrite id_left. 
    unfold bla1.
    simpl.
    unfold coproduct_nat_trans_data.
    simpl.
    eapply pathscomp0. apply CoproductOfArrows_comp.
    apply pathsinv0.
    eapply pathscomp0. apply CoproductOfArrows_comp.
    apply pathsinv0.
    apply CoproductOfArrows_eq.
       - assert (Ha:=S12' X Z Z').
         simpl in Ha.
         assert (Ha_x := nat_trans_eq_pointwise _ _ _ _ _ _ Ha x).
         simpl in Ha_x.
         rewrite id_left in Ha_x.
         apply Ha_x.
       - assert (Ha:=S22' X Z Z').
         simpl in Ha.
         assert (Ha_x := nat_trans_eq_pointwise _ _ _ _ _ _ Ha x).
         simpl in Ha_x.
         rewrite id_left in Ha_x.
         apply Ha_x.
Qed.

End construction.


Definition Sum_of_Signatures (S1 S2: Signature C hs): Signature C hs.
Proof.
  destruct S1 as [H1 [θ1 [S11' S12']]].
  destruct S2 as [H2 [θ2 [S21' S22']]].
  exists (H H1 H2).
  exists (θ H1 H2 θ1 θ2).
  split.
  + apply SumStrength1'; assumption.
  + apply SumStrength2'; assumption.
Defined.


End sum_of_signatures.
