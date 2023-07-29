(**********************************************************************************

 Natural transformations of two-sided displayed categories

 We define natural transformations between functors on two-sided diplayed
 categories. In addition, we prove an equality principle (if two such natural
 transformations are pointwise equal, then they are actually equal), and we give
 the necessary constructions.

 Contents
 1. Natural transformations of two-sided displayed categories
 2. Equality principle
 3. The total natural transformation
 4. The identity transformation
 5. Composition of transformations
 6. Prewhiskering
 7. Postwhiskering
 8. Displayed two-sided natural transformations versus one-sided ones

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.NaturalTransformations.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.

Local Open Scope cat.

(**
 1. Natural transformations of two-sided displayed categories
 *)
Section DisplayedNatTrans.
  Context {C₁ C₁' C₂ C₂' : category}
          {F F' : C₁ ⟶ C₁'}
          (τ : F ⟹ F')
          {G G' : C₂ ⟶ C₂'}
          (θ : G ⟹ G')
          {D : twosided_disp_cat C₁ C₂}
          {D' : twosided_disp_cat C₁' C₂'}
          (FG : twosided_disp_functor F G D D')
          (FG' : twosided_disp_functor F' G' D D').

  Definition twosided_disp_nat_trans_data
    : UU
    := ∏ (x : C₁) (y : C₂) (xy : D x y), FG _ _ xy -->[ τ x ][ θ y ] FG' _ _ xy.

  Definition twosided_disp_nat_trans_laws
             (τθ : twosided_disp_nat_trans_data)
    : UU
    := ∏ (x₁ x₂ : C₁)
         (y₁ y₂ : C₂)
         (f : x₁ --> x₂)
         (g : y₁ --> y₂)
         (xy₁ : D x₁ y₁)
         (xy₂ : D x₂ y₂)
         (fg : xy₁ -->[ f ][ g ] xy₂),
       #2 FG fg ;;2 τθ _ _ xy₂
       =
       transportb
         (λ z, _ -->[ z ][ _] _)
         (nat_trans_ax τ _ _ f)
         (transportb
            (λ z, _ -->[ _ ][ z ] _)
            (nat_trans_ax θ _ _ g)
            (τθ _ _ xy₁ ;;2 #2 FG' fg)).

  Definition twosided_disp_nat_trans
    : UU
    := ∑ (τθ : twosided_disp_nat_trans_data), twosided_disp_nat_trans_laws τθ.

  Definition twosided_disp_nat_trans_ob
             (τθ : twosided_disp_nat_trans)
             {x : C₁}
             {y : C₂}
             (xy : D x y)
    : FG _ _ xy -->[ τ x ][ θ y ] FG' _ _ xy
    := pr1 τθ x y xy.

  Coercion twosided_disp_nat_trans_ob : twosided_disp_nat_trans >-> Funclass.

  Proposition twosided_disp_nat_trans_ax
              (τθ : twosided_disp_nat_trans)
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {f : x₁ --> x₂}
              {g : y₁ --> y₂}
              {xy₁ : D x₁ y₁}
              {xy₂ : D x₂ y₂}
              (fg : xy₁ -->[ f ][ g ] xy₂)
    : #2 FG fg ;;2 τθ _ _ xy₂
      =
      transportb
        (λ z, _ -->[ z ][ _] _)
        (nat_trans_ax τ _ _ f)
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (nat_trans_ax θ _ _ g)
           (τθ _ _ xy₁ ;;2 #2 FG' fg)).
  Proof.
    apply (pr2 τθ).
  Qed.

  Proposition isaprop_twosided_disp_nat_trans_laws
              (τθ : twosided_disp_nat_trans_data)
    : isaprop (twosided_disp_nat_trans_laws τθ).
  Proof.
    repeat (use impred ; intro).
    apply D'.
  Qed.

  Proposition isaset_twosided_disp_nat_trans
    : isaset twosided_disp_nat_trans.
  Proof.
    use isaset_total2.
    - use impred_isaset ; intro x.
      use impred_isaset ; intro y.
      use impred_isaset ; intro xy.
      apply D'.
    - intro.
      apply isasetaprop.
      exact (isaprop_twosided_disp_nat_trans_laws _).
  Qed.
End DisplayedNatTrans.

(**
 2. Equality principle
 *)
Definition eq_twosided_disp_nat_trans
           {C₁ C₁' C₂ C₂' : category}
           {F F' : C₁ ⟶ C₁'}
           {τ : F ⟹ F'}
           {G G' : C₂ ⟶ C₂'}
           {θ : G ⟹ G'}
           {D : twosided_disp_cat C₁ C₂}
           {D' : twosided_disp_cat C₁' C₂'}
           {FG : twosided_disp_functor F G D D'}
           {FG' : twosided_disp_functor F' G' D D'}
           {τθ τθ' : twosided_disp_nat_trans τ θ FG FG'}
           (p : ∏ (x : C₁) (y : C₂) (xy : D x y), τθ x y xy = τθ' x y xy)
  : τθ = τθ'.
Proof.
  use subtypePath.
  {
    intro.
    repeat (use impred ; intro).
    apply isaset_disp_mor.
  }
  use funextsec ; intro x.
  use funextsec ; intro y.
  use funextsec ; intro xy.
  apply p.
Qed.

(**
 3. The total natural transformation
 *)
Section TotalNatTrans.
  Context {C₁ C₁' C₂ C₂' : category}
          {F F' : C₁ ⟶ C₁'}
          {τ : F ⟹ F'}
          {G G' : C₂ ⟶ C₂'}
          {θ : G ⟹ G'}
          {D : twosided_disp_cat C₁ C₂}
          {D' : twosided_disp_cat C₁' C₂'}
          {FG : twosided_disp_functor F G D D'}
          {FG' : twosided_disp_functor F' G' D D'}
          (τθ : twosided_disp_nat_trans τ θ FG FG').

  Definition total_twosided_disp_nat_trans_data
    : nat_trans_data
        (total_twosided_disp_functor FG)
        (total_twosided_disp_functor FG')
    := λ x, τ (pr1 x) ,, θ (pr12 x) ,, τθ _ _ (pr22 x).

  Definition total_twosided_disp_nat_trans_laws
    : is_nat_trans
        _ _
        total_twosided_disp_nat_trans_data.
  Proof.
    intros x y f.
    use total2_paths_2_b.
    - apply nat_trans_ax.
    - apply nat_trans_ax.
    - apply τθ.
  Qed.

  Definition total_twosided_disp_nat_trans
    : total_twosided_disp_functor FG ⟹ total_twosided_disp_functor FG'.
  Proof.
    use make_nat_trans.
    - exact total_twosided_disp_nat_trans_data.
    - exact total_twosided_disp_nat_trans_laws.
  Defined.
End TotalNatTrans.

(**
 4. The identity transformation
 *)
Section IdNatTrans.
  Context {C₁ C₁' C₂ C₂' : category}
          {F : C₁ ⟶ C₁'}
          {G : C₂ ⟶ C₂'}
          {D : twosided_disp_cat C₁ C₂}
          {D' : twosided_disp_cat C₁' C₂'}
          (FG : twosided_disp_functor F G D D').

  Definition id_twosided_disp_nat_trans_data
    : twosided_disp_nat_trans_data (nat_trans_id F) (nat_trans_id G) FG FG
    := λ x y xy, id_two_disp _.

  Definition id_twosided_disp_nat_trans_laws
    : twosided_disp_nat_trans_laws
        _ _ _ _
        id_twosided_disp_nat_trans_data.
  Proof.
    intros x₁ x₂ y₁ y₂ f g xy₁ xy₂ fg ; unfold id_twosided_disp_nat_trans_data.
    refine (id_two_disp_right _ @ _).
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply id_two_disp_left.
    }
    rewrite !twosided_prod_transportb.
    unfold transportb.
    rewrite transport_f_f.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  Qed.

  Definition id_twosided_disp_nat_trans
    : twosided_disp_nat_trans (nat_trans_id F) (nat_trans_id G) FG FG.
  Proof.
    simple refine (_ ,, _).
    - exact id_twosided_disp_nat_trans_data.
    - exact id_twosided_disp_nat_trans_laws.
  Defined.
End IdNatTrans.

Arguments id_twosided_disp_nat_trans_data {C₁ C₁' C₂ C₂' F G D D'} FG /.
Arguments id_twosided_disp_nat_trans {C₁ C₁' C₂ C₂' F G D D'} FG /.

(**
 5. Composition of transformations
 *)
Section CompNatTrans.
  Context {C₁ C₁' C₂ C₂' : category}
          {F F' F'' : C₁ ⟶ C₁'}
          {τ : F ⟹ F'}
          {τ' : F' ⟹ F''}
          {G G' G'' : C₂ ⟶ C₂'}
          {θ : G ⟹ G'}
          {θ' : G' ⟹ G''}
          {D : twosided_disp_cat C₁ C₂}
          {D' : twosided_disp_cat C₁' C₂'}
          {FG : twosided_disp_functor F G D D'}
          {FG' : twosided_disp_functor F' G' D D'}
          {FG'' : twosided_disp_functor F'' G'' D D'}
          (τθ : twosided_disp_nat_trans τ θ FG FG')
          (τθ' : twosided_disp_nat_trans τ' θ' FG' FG'').

  Definition comp_twosided_disp_nat_trans_data
    : twosided_disp_nat_trans_data
        (nat_trans_comp _ _ _ τ τ')
        (nat_trans_comp _ _ _ θ θ')
        FG FG''
    := λ x y xy, τθ _ _ xy ;;2 τθ' _ _ xy.

  Definition comp_twosided_disp_nat_trans_laws
    : twosided_disp_nat_trans_laws
        _ _ _ _
        comp_twosided_disp_nat_trans_data.
  Proof.
    intros x₁ x₂ y₁ y₂ f g xy₁ xy₂ fg ; unfold comp_twosided_disp_nat_trans_data.
    cbn.
    rewrite assoc_two_disp.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply (pr2 τθ).
    }
    unfold transportb.
    rewrite two_disp_pre_whisker_left.
    rewrite two_disp_pre_whisker_right.
    rewrite assoc_two_disp_alt.
    rewrite !twosided_prod_transport.
    rewrite !transport_f_f.
    etrans.
    {
      do 2 apply maponpaths.
      apply (pr2 τθ').
    }
    unfold transportb.
    rewrite two_disp_post_whisker_left.
    rewrite two_disp_post_whisker_right.
    rewrite assoc_two_disp.
    unfold transportb.
    rewrite !twosided_prod_transport.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  Qed.

  Definition comp_twosided_disp_nat_trans
    : twosided_disp_nat_trans
        (nat_trans_comp _ _ _ τ τ')
        (nat_trans_comp _ _ _ θ θ')
        FG FG''.
  Proof.
    simple refine (_ ,, _).
    - exact comp_twosided_disp_nat_trans_data.
    - exact comp_twosided_disp_nat_trans_laws.
  Defined.
End CompNatTrans.

Arguments comp_twosided_disp_nat_trans_data {C₁ C₁' C₂ C₂' F F' F'' τ τ' G G' G'' θ θ' D D' FG FG' FG''} _ _ /.
Arguments comp_twosided_disp_nat_trans {C₁ C₁' C₂ C₂' F F' F'' τ τ' G G' G'' θ θ' D D' FG FG' FG''} _ _ /.

(**
 6. Prewhiskering
 *)
Section Prewhisker.
  Context {C₁ C₁' C₁'' C₂ C₂' C₂'' : category}
          {F : C₁ ⟶ C₁'}
          {G : C₂ ⟶ C₂'}
          {H H' : C₁' ⟶ C₁''}
          {τ : H ⟹ H'}
          {K K' : C₂' ⟶ C₂''}
          {θ : K ⟹ K'}
          {D : twosided_disp_cat C₁ C₂}
          {D' : twosided_disp_cat C₁' C₂'}
          {D'' : twosided_disp_cat C₁'' C₂''}
          (FG : twosided_disp_functor F G D D')
          {HK : twosided_disp_functor H K D' D''}
          {HK' : twosided_disp_functor H' K' D' D''}
          (τθ : twosided_disp_nat_trans τ θ HK HK').

  Definition pre_whisker_twosided_disp_nat_trans_data
    : twosided_disp_nat_trans_data
        (pre_whisker F τ : F ∙ H ⟹ F ∙ H')
        (pre_whisker G θ : G ∙ K ⟹ G ∙ K')
        (comp_twosided_disp_functor FG HK)
        (comp_twosided_disp_functor FG HK')
    := λ x y xy, τθ _ _ (FG _ _ xy).

  Definition pre_whisker_twosided_disp_nat_trans_laws
    : twosided_disp_nat_trans_laws
        _ _ _ _
        pre_whisker_twosided_disp_nat_trans_data.
  Proof.
    intros x₁ x₂ y₁ y₂ f g xy₁ xy₂ fg ; unfold pre_whisker_twosided_disp_nat_trans_data.
    cbn.
    etrans.
    {
      apply (pr2 τθ).
    }
    rewrite !twosided_prod_transportb.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  Qed.

  Definition pre_whisker_twosided_disp_nat_trans
    : twosided_disp_nat_trans
        (pre_whisker F τ : F ∙ H ⟹ F ∙ H')
        (pre_whisker G θ : G ∙ K ⟹ G ∙ K')
        (comp_twosided_disp_functor FG HK)
        (comp_twosided_disp_functor FG HK').
  Proof.
    simple refine (_ ,, _).
    - exact pre_whisker_twosided_disp_nat_trans_data.
    - exact pre_whisker_twosided_disp_nat_trans_laws.
  Defined.
End Prewhisker.

Arguments pre_whisker_twosided_disp_nat_trans_data {C₁ C₁' C₁'' C₂ C₂' C₂'' F G H H' τ K K' θ D D' D''} FG {HK HK'} _ /.
Arguments pre_whisker_twosided_disp_nat_trans {C₁ C₁' C₁'' C₂ C₂' C₂'' F G H H' τ K K' θ D D' D''} FG {HK HK'} _ /.

(**
 7. Postwhiskering
 *)
Section Postwhisker.
  Context {C₁ C₁' C₁'' C₂ C₂' C₂'' : category}
          {F F' : C₁ ⟶ C₁'}
          {τ : F ⟹ F'}
          {G G' : C₂ ⟶ C₂'}
          {θ : G ⟹ G'}
          {H : C₁' ⟶ C₁''}
          {K : C₂' ⟶ C₂''}
          {D : twosided_disp_cat C₁ C₂}
          {D' : twosided_disp_cat C₁' C₂'}
          {D'' : twosided_disp_cat C₁'' C₂''}
          (FG : twosided_disp_functor F G D D')
          (FG' : twosided_disp_functor F' G' D D')
          {HK : twosided_disp_functor H K D' D''}
          (τθ : twosided_disp_nat_trans τ θ FG FG').

  Definition post_whisker_twosided_disp_nat_trans_data
    : twosided_disp_nat_trans_data
        (post_whisker τ H : F ∙ H ⟹ F' ∙ H)
        (post_whisker θ K : G ∙ K ⟹ G' ∙ K)
        (comp_twosided_disp_functor FG HK)
        (comp_twosided_disp_functor FG' HK)
    := λ x y xy, #2 HK (τθ _ _ xy).

  Definition post_whisker_twosided_disp_nat_trans_laws
    : twosided_disp_nat_trans_laws
        _ _ _ _
        post_whisker_twosided_disp_nat_trans_data.
  Proof.
    intros x₁ x₂ y₁ y₂ f g xy₁ xy₂ fg ; unfold post_whisker_twosided_disp_nat_trans_data.
    cbn.
    rewrite !twosided_disp_functor_comp_alt.
    etrans.
    {
      do 3 apply maponpaths.
      apply (pr2 τθ).
    }
    rewrite transportb_twosided_disp_functor_left.
    rewrite transportb_twosided_disp_functor_right.
    rewrite !twosided_prod_transportb.
    rewrite !twosided_prod_transport.
    unfold transportb.
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply isaset_dirprod ; apply homset_property.
  Qed.

  Definition post_whisker_twosided_disp_nat_trans
    : twosided_disp_nat_trans
        (post_whisker τ H : F ∙ H ⟹ F' ∙ H)
        (post_whisker θ K : G ∙ K ⟹ G' ∙ K)
        (comp_twosided_disp_functor FG HK)
        (comp_twosided_disp_functor FG' HK).
  Proof.
    simple refine (_ ,, _).
    - exact post_whisker_twosided_disp_nat_trans_data.
    - exact post_whisker_twosided_disp_nat_trans_laws.
  Defined.
End Postwhisker.

Arguments post_whisker_twosided_disp_nat_trans_data {C₁ C₁' C₁'' C₂ C₂' C₂'' F F' τ G G' θ H K D D' D'' FG FG'} HK _ /.
Arguments post_whisker_twosided_disp_nat_trans {C₁ C₁' C₁'' C₂ C₂' C₂'' F F' τ G G' θ H K D D' D'' FG FG'} HK _ /.


Definition twosided_disp_lunitor
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
  : twosided_disp_nat_trans
      (nat_trans_id F) (nat_trans_id F)
      (comp_twosided_disp_functor (twosided_disp_functor_identity D₁) FF)
      FF.
Proof.
  simple refine (_ ,, _).
  - exact (λ x y xy, id_two_disp _).
  - abstract
      (intros x₁ x₂ y₁ y₂ f g xy₁ xy₂ fg ; cbn ;
       rewrite id_two_disp_left, id_two_disp_right ;
       rewrite !twosided_prod_transportb ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply isaset_dirprod ; apply homset_property).
Defined.

Definition twosided_disp_runitor
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
  : twosided_disp_nat_trans
      (nat_trans_id F : F ∙ functor_identity _ ⟹ F)
      (nat_trans_id F : F ∙ functor_identity _ ⟹ F)
      (comp_twosided_disp_functor FF (twosided_disp_functor_identity D₂))
      FF.
Proof.
  simple refine (_ ,, _).
  - exact (λ x y xy, id_two_disp _).
  - abstract
      (intros x₁ x₂ y₁ y₂ f g xy₁ xy₂ fg ; cbn ;
       rewrite id_two_disp_left, id_two_disp_right ;
       rewrite !twosided_prod_transportb ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply isaset_dirprod ; apply homset_property).
Defined.

Definition twosided_disp_linvunitor
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
  : twosided_disp_nat_trans
      (nat_trans_id F) (nat_trans_id F)
      FF
      (comp_twosided_disp_functor (twosided_disp_functor_identity D₁) FF).
Proof.
  simple refine (_ ,, _).
  - exact (λ x y xy, id_two_disp _).
  - abstract
      (intros x₁ x₂ y₁ y₂ f g xy₁ xy₂ fg ; cbn ;
       rewrite id_two_disp_left, id_two_disp_right ;
       rewrite !twosided_prod_transportb ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply isaset_dirprod ; apply homset_property).
Defined.

Definition twosided_disp_rinvunitor
           {C₁ C₂ : category}
           {F : C₁ ⟶ C₂}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           (FF : twosided_disp_functor F F D₁ D₂)
  : twosided_disp_nat_trans
      (nat_trans_id F : F ⟹ F ∙ functor_identity _)
      (nat_trans_id F : F ⟹ F ∙ functor_identity _)
      FF
      (comp_twosided_disp_functor FF (twosided_disp_functor_identity D₂)).
Proof.
  simple refine (_ ,, _).
  - exact (λ x y xy, id_two_disp _).
  - abstract
      (intros x₁ x₂ y₁ y₂ f g xy₁ xy₂ fg ; cbn ;
       rewrite id_two_disp_left, id_two_disp_right ;
       rewrite !twosided_prod_transportb ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply isaset_dirprod ; apply homset_property).
Defined.

Definition twosided_disp_rassociator
           {C₁ C₂ C₃ C₄ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {H : C₃ ⟶ C₄}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {D₃ : twosided_disp_cat C₃ C₃}
           {D₄ : twosided_disp_cat C₄ C₄}
           (FF : twosided_disp_functor F F D₁ D₂)
           (GG : twosided_disp_functor G G D₂ D₃)
           (HH : twosided_disp_functor H H D₃ D₄)
  : twosided_disp_nat_trans
      (nat_trans_id _ : (F ∙ G) ∙ H ⟹ F ∙ (G ∙ H))
      (nat_trans_id _ : (F ∙ G) ∙ H ⟹ F ∙ (G ∙ H))
      (comp_twosided_disp_functor (comp_twosided_disp_functor FF GG) HH)
      (comp_twosided_disp_functor FF (comp_twosided_disp_functor GG HH)).
Proof.
  simple refine (_ ,, _).
  - exact (λ x y xy, id_two_disp _).
  - abstract
      (intros x₁ x₂ y₁ y₂ f g xy₁ xy₂ fg ; cbn ;
       rewrite id_two_disp_left, id_two_disp_right ;
       rewrite !twosided_prod_transportb ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply isaset_dirprod ; apply homset_property).
Defined.

Definition twosided_disp_lassociator
           {C₁ C₂ C₃ C₄ : category}
           {F : C₁ ⟶ C₂}
           {G : C₂ ⟶ C₃}
           {H : C₃ ⟶ C₄}
           {D₁ : twosided_disp_cat C₁ C₁}
           {D₂ : twosided_disp_cat C₂ C₂}
           {D₃ : twosided_disp_cat C₃ C₃}
           {D₄ : twosided_disp_cat C₄ C₄}
           (FF : twosided_disp_functor F F D₁ D₂)
           (GG : twosided_disp_functor G G D₂ D₃)
           (HH : twosided_disp_functor H H D₃ D₄)
  : twosided_disp_nat_trans
      (nat_trans_id _ : F ∙ (G ∙ H) ⟹ (F ∙ G) ∙ H)
      (nat_trans_id _ : F ∙ (G ∙ H) ⟹ (F ∙ G) ∙ H)
      (comp_twosided_disp_functor FF (comp_twosided_disp_functor GG HH))
      (comp_twosided_disp_functor (comp_twosided_disp_functor FF GG) HH).
Proof.
  simple refine (_ ,, _).
  - exact (λ x y xy, id_two_disp _).
  - abstract
      (intros x₁ x₂ y₁ y₂ f g xy₁ xy₂ fg ; cbn ;
       rewrite id_two_disp_left, id_two_disp_right ;
       rewrite !twosided_prod_transportb ;
       unfold transportb ;
       rewrite transport_f_f ;
       apply maponpaths_2 ;
       apply isaset_dirprod ; apply homset_property).
Defined.

(**
 8. Displayed two-sided natural transformations versus one-sided ones
 *)
Definition twosided_disp_nat_trans_to_disp_nat_trans
           {C₁ C₁' C₂ C₂' : category}
           {F F' : C₁ ⟶ C₁'}
           {τ : F ⟹ F'}
           {G G' : C₂ ⟶ C₂'}
           {θ : G ⟹ G'}
           {D : twosided_disp_cat C₁ C₂}
           {D' : twosided_disp_cat C₁' C₂'}
           {FG : twosided_disp_functor F G D D'}
           {FG' : twosided_disp_functor F' G' D D'}
           (τθ : twosided_disp_nat_trans τ θ FG FG')
  : disp_nat_trans
      (pair_nat_trans τ θ)
      (two_sided_disp_functor_to_disp_functor FG)
      (two_sided_disp_functor_to_disp_functor FG').
Proof.
  refine ((λ x xx, τθ (pr1 x) (pr2 x) xx) ,, _).
  abstract
    (intros x y xx yy f ff ;
     cbn ;
     rewrite twosided_disp_nat_trans_ax ;
     rewrite <- transportb_dirprodeq ;
     apply maponpaths_2 ;
     apply isasetdirprod ; apply homset_property).
Defined.

Definition twosided_disp_nat_trans_from_disp_nat_trans
           {C₁ C₁' C₂ C₂' : category}
           {F F' : C₁ ⟶ C₁'}
           {τ : F ⟹ F'}
           {G G' : C₂ ⟶ C₂'}
           {θ : G ⟹ G'}
           {D : twosided_disp_cat C₁ C₂}
           {D' : twosided_disp_cat C₁' C₂'}
           {FG : twosided_disp_functor F G D D'}
           {FG' : twosided_disp_functor F' G' D D'}
           (τθ : disp_nat_trans
                   (pair_nat_trans τ θ)
                   (two_sided_disp_functor_to_disp_functor FG)
                   (two_sided_disp_functor_to_disp_functor FG'))
  : twosided_disp_nat_trans τ θ FG FG'.
Proof.
  refine ((λ x y xy, τθ (x ,, y) xy) ,, _).
  abstract
    (intros x₁ x₂ y₁ y₂ f g xy₁ xy₂ fg ; cbn ;
     pose (@disp_nat_trans_ax
              _ _ _ _ _ _ _ _ _
              τθ
              (x₁ ,, y₁)
              (x₂ ,, y₂)
              (f ,, g)
              xy₁ xy₂
              fg)
       as p ;
     cbn in p ;
     rewrite p ;
     rewrite <- transportb_dirprodeq ;
     apply maponpaths_2 ;
     apply isasetdirprod ; apply homset_property).
Defined.

Definition twosided_disp_nat_trans_weq_disp_nat_trans
           {C₁ C₁' C₂ C₂' : category}
           {F F' : C₁ ⟶ C₁'}
           (τ : F ⟹ F')
           {G G' : C₂ ⟶ C₂'}
           (θ : G ⟹ G')
           {D : twosided_disp_cat C₁ C₂}
           {D' : twosided_disp_cat C₁' C₂'}
           (FG : twosided_disp_functor F G D D')
           (FG' : twosided_disp_functor F' G' D D')
  : twosided_disp_nat_trans τ θ FG FG'
    ≃
    disp_nat_trans
      (pair_nat_trans τ θ)
      (two_sided_disp_functor_to_disp_functor FG)
      (two_sided_disp_functor_to_disp_functor FG').
Proof.
  use weq_iso.
  - exact twosided_disp_nat_trans_to_disp_nat_trans.
  - exact twosided_disp_nat_trans_from_disp_nat_trans.
  - abstract
      (intros τθ ;
       use subtypePath ; [ intro ; apply isaprop_twosided_disp_nat_trans_laws | ] ;
       apply idpath).
  - abstract
      (intros τθ ;
       use subtypePath ; [ intro ; apply isaprop_disp_nat_trans_axioms | ] ;
       apply idpath).
Defined.
