(**********************************************************************************

 Functors of two-sided displayed categories

 We define functors of two-sided displayed categories and we show that every such
 functor gives rise to a functor between the total categories. In addition, we give
 examples of such functors, namely the identity and composition. We also show that
 if the target two-sided displayed category is discrete, then the type of functors
 between them forms a set.

 Contents
 1. Functors of two-sided displayed categories
 2. Some laws
 3. The total functor
 4. The identity
 5. Composition
 6. Functors between discrete two-sided displayed categories form a set
 7. Two-sided displayed functors versus displayed functors

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.

Local Open Scope cat.

(**
 1. Functors of two-sided displayed categories
 *)
Section DisplayedFunctor.
  Context {C₁ C₁' C₂ C₂' : category}
          (F : C₁ ⟶ C₁')
          (G : C₂ ⟶ C₂')
          (D₁ : twosided_disp_cat C₁ C₂)
          (D₂ : twosided_disp_cat C₁' C₂').

  Definition twosided_disp_functor_data
    : UU
    := ∑ (FGob : ∏ (x : C₁) (y : C₂), D₁ x y → D₂ (F x) (G y)),
       ∏ (x₁ x₂ : C₁)
         (y₁ y₂ : C₂)
         (xy₁ : D₁ x₁ y₁)
         (xy₂ : D₁ x₂ y₂)
         (f : x₁ --> x₂)
         (g : y₁ --> y₂)
         (fg : xy₁ -->[ f ][ g ] xy₂),
       FGob _ _ xy₁ -->[ #F f ][ #G g] FGob _ _ xy₂.

  Definition twosided_disp_functor_data_ob
             (FG : twosided_disp_functor_data)
             {x : C₁}
             {y : C₂}
             (xy : D₁ x y)
    : D₂ (F x) (G y)
    := pr1 FG x y xy.

  Coercion twosided_disp_functor_data_ob : twosided_disp_functor_data >-> Funclass.

  Definition twosided_disp_functor_data_mor
             (FG : twosided_disp_functor_data)
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D₁ x₁ y₁}
             {xy₂ : D₁ x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : FG _ _ xy₁ -->[ #F f ][ #G g] FG _ _ xy₂
    := pr2 FG _ _ _ _ _ _ _ _ fg.

  Local Notation "'#2' F" := (twosided_disp_functor_data_mor F) (at level 10).

  Definition twosided_disp_functor_id_law
             (FG : twosided_disp_functor_data)
    : UU
    := ∏ (x : C₁) (y : C₂) (xy : D₁ x y),
       #2 FG (id_two_disp xy)
       =
       transportb_disp_mor2
         (functor_id F x)
         (functor_id G y)
         (id_two_disp (FG _ _ xy)).

  Definition twosided_disp_functor_comp_law
             (FG : twosided_disp_functor_data)
    : UU
    := ∏ (x₁ x₂ x₃ : C₁)
         (y₁ y₂ y₃ : C₂)
         (xy₁ : D₁ x₁ y₁)
         (xy₂ : D₁ x₂ y₂)
         (xy₃ : D₁ x₃ y₃)
         (f₁ : x₁ --> x₂)
         (g₁ : y₁ --> y₂)
         (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
         (f₂ : x₂ --> x₃)
         (g₂ : y₂ --> y₃)
         (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃),
       #2 FG (fg₁ ;;2 fg₂)
       =
       transportb_disp_mor2
         (functor_comp F f₁ f₂)
         (functor_comp G g₁ g₂)
         (#2 FG fg₁ ;;2 #2 FG fg₂).

  Definition twosided_disp_functor_laws
             (FG : twosided_disp_functor_data)
    : UU
    := twosided_disp_functor_id_law FG × twosided_disp_functor_comp_law FG.

  Proposition isaprop_twosided_disp_functor_laws
              (FG : twosided_disp_functor_data)
    : isaprop (twosided_disp_functor_laws FG).
  Proof.
    use isapropdirprod ; repeat (use impred ; intro) ; apply isaset_disp_mor.
  Qed.

  Definition twosided_disp_functor
    : UU
    := ∑ (FG : twosided_disp_functor_data), twosided_disp_functor_laws FG.

  #[reversible=no] Coercion twosided_disp_functor_to_data
           (FG : twosided_disp_functor)
    : twosided_disp_functor_data
    := pr1 FG.

  Definition twosided_disp_functor_id
             (FG : twosided_disp_functor)
             {x : C₁}
             {y : C₂}
             (xy : D₁ x y)
    : #2 FG (id_two_disp xy)
      =
      transportb_disp_mor2
        (functor_id F x)
        (functor_id G y)
        (id_two_disp (FG _ _ xy))
    := pr12 FG x y xy.

  Definition twosided_disp_functor_id_alt
             (FG : twosided_disp_functor)
             {x : C₁}
             {y : C₂}
             (xy : D₁ x y)
    : id_two_disp (FG _ _ xy)
      =
      transportf_disp_mor2
        (functor_id F x)
        (functor_id G y)
        (#2 FG (id_two_disp xy)).
  Proof.
    rewrite twosided_disp_functor_id.
    rewrite transportfb_disp_mor2.
    apply idpath.
  Qed.

  Definition twosided_disp_functor_comp
             (FG : twosided_disp_functor)
             {x₁ x₂ x₃ : C₁}
             {y₁ y₂ y₃ : C₂}
             {xy₁ : D₁ x₁ y₁}
             {xy₂ : D₁ x₂ y₂}
             {xy₃ : D₁ x₃ y₃}
             {f₁ : x₁ --> x₂}
             {g₁ : y₁ --> y₂}
             (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             {f₂ : x₂ --> x₃}
             {g₂ : y₂ --> y₃}
             (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
    : #2 FG (fg₁ ;;2 fg₂)
      =
      transportb_disp_mor2
        (functor_comp F f₁ f₂)
        (functor_comp G g₁ g₂)
        (#2 FG fg₁ ;;2 #2 FG fg₂)
    := pr22 FG _ _ _ _ _ _ _ _ _ _ _ fg₁ _ _ fg₂.

  Definition twosided_disp_functor_comp_alt
             (FG : twosided_disp_functor)
             {x₁ x₂ x₃ : C₁}
             {y₁ y₂ y₃ : C₂}
             {xy₁ : D₁ x₁ y₁}
             {xy₂ : D₁ x₂ y₂}
             {xy₃ : D₁ x₃ y₃}
             {f₁ : x₁ --> x₂}
             {g₁ : y₁ --> y₂}
             (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             {f₂ : x₂ --> x₃}
             {g₂ : y₂ --> y₃}
             (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
    : #2 FG fg₁ ;;2 #2 FG fg₂
      =
      transportf_disp_mor2
        (functor_comp F f₁ f₂)
        (functor_comp G g₁ g₂)
        (#2 FG (fg₁ ;;2 fg₂)).
  Proof.
    rewrite twosided_disp_functor_comp.
    rewrite transportfb_disp_mor2.
    apply idpath.
  Qed.
End DisplayedFunctor.

Arguments twosided_disp_functor_data_mor
            {C₁ C₁' C₂ C₂' F G D₁ D₂}
            FG
            {x₁ x₂ y₁ y₂ xy₁ xy₂ f g}
            fg.
Notation "'#2' F" := (twosided_disp_functor_data_mor F) (at level 10) : cat.

(**
 2. Some laws
 *)
Definition transportb_twosided_disp_functor_left
           {C₁ C₁' C₂ C₂' : category}
           {F : C₁ ⟶ C₁'}
           {G : C₂ ⟶ C₂'}
           {D₁ : twosided_disp_cat C₁ C₂}
           {D₂ : twosided_disp_cat C₁' C₂'}
           (FG : twosided_disp_functor F G D₁ D₂)
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {xy₁ : D₁ x₁ y₁}
           {xy₂ : D₁ x₂ y₂}
           {f f' : x₁ --> x₂}
           (p : f = f')
           {g : y₁ --> y₂}
           (fg : xy₁ -->[ f' ][ g ] xy₂)
  : #2 FG (transportb (λ z, xy₁ -->[ z ][ g ] xy₂) p fg)
    =
    transportb
      (λ z, FG _ _ xy₁ -->[ z ][ _ ] FG _ _ xy₂)
      (maponpaths (λ z, #F z) p)
      (#2 FG fg).
Proof.
  induction p.
  apply idpath.
Qed.

Definition transportb_twosided_disp_functor_right
           {C₁ C₁' C₂ C₂' : category}
           {F : C₁ ⟶ C₁'}
           {G : C₂ ⟶ C₂'}
           {D₁ : twosided_disp_cat C₁ C₂}
           {D₂ : twosided_disp_cat C₁' C₂'}
           (FG : twosided_disp_functor F G D₁ D₂)
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {xy₁ : D₁ x₁ y₁}
           {xy₂ : D₁ x₂ y₂}
           {f : x₁ --> x₂}
           {g g' : y₁ --> y₂}
           (p : g = g')
           (fg : xy₁ -->[ f ][ g' ] xy₂)
  : #2 FG (transportb (λ z, xy₁ -->[ f ][ z ] xy₂) p fg)
    =
    transportb
      (λ z, FG _ _ xy₁ -->[ _ ][ z ] FG _ _ xy₂)
      (maponpaths (λ z, #G z) p)
      (#2 FG fg).
Proof.
  induction p.
  apply idpath.
Qed.

Definition transportf_twosided_disp_functor_left
           {C₁ C₁' C₂ C₂' : category}
           {F : C₁ ⟶ C₁'}
           {G : C₂ ⟶ C₂'}
           {D₁ : twosided_disp_cat C₁ C₂}
           {D₂ : twosided_disp_cat C₁' C₂'}
           (FG : twosided_disp_functor F G D₁ D₂)
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {xy₁ : D₁ x₁ y₁}
           {xy₂ : D₁ x₂ y₂}
           {f f' : x₁ --> x₂}
           (p : f' = f)
           {g : y₁ --> y₂}
           (fg : xy₁ -->[ f' ][ g ] xy₂)
  : #2 FG (transportf (λ z, xy₁ -->[ z ][ g ] xy₂) p fg)
    =
    transportf
      (λ z, FG _ _ xy₁ -->[ z ][ _ ] FG _ _ xy₂)
      (maponpaths (λ z, #F z) p)
      (#2 FG fg).
Proof.
  induction p.
  apply idpath.
Qed.

Definition transportf_twosided_disp_functor_right
           {C₁ C₁' C₂ C₂' : category}
           {F : C₁ ⟶ C₁'}
           {G : C₂ ⟶ C₂'}
           {D₁ : twosided_disp_cat C₁ C₂}
           {D₂ : twosided_disp_cat C₁' C₂'}
           (FG : twosided_disp_functor F G D₁ D₂)
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {xy₁ : D₁ x₁ y₁}
           {xy₂ : D₁ x₂ y₂}
           {f : x₁ --> x₂}
           {g g' : y₁ --> y₂}
           (p : g' = g)
           (fg : xy₁ -->[ f ][ g' ] xy₂)
  : #2 FG (transportf (λ z, xy₁ -->[ f ][ z ] xy₂) p fg)
    =
    transportf
      (λ z, FG _ _ xy₁ -->[ _ ][ z ] FG _ _ xy₂)
      (maponpaths (λ z, #G z) p)
      (#2 FG fg).
Proof.
  induction p.
  apply idpath.
Qed.

Definition transportf_twosided_disp_functor
           {C₁ C₁' C₂ C₂' : category}
           {F : C₁ ⟶ C₁'}
           {G : C₂ ⟶ C₂'}
           {D₁ : twosided_disp_cat C₁ C₂}
           {D₂ : twosided_disp_cat C₁' C₂'}
           (FG : twosided_disp_functor F G D₁ D₂)
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {xy₁ : D₁ x₁ y₁}
           {xy₂ : D₁ x₂ y₂}
           {f f' : x₁ --> x₂}
           (p : f = f')
           {g g' : y₁ --> y₂}
           (q : g = g')
           (fg : xy₁ -->[ f ][ g ] xy₂)
  : #2 FG (transportf_disp_mor2 p q fg)
    =
    transportf_disp_mor2
      (maponpaths (λ z, #F z) p)
      (maponpaths (λ z, #G z) q)
      (#2 FG fg).
Proof.
  induction p, q.
  apply idpath.
Qed.

Definition transportb_twosided_disp_functor
           {C₁ C₁' C₂ C₂' : category}
           {F : C₁ ⟶ C₁'}
           {G : C₂ ⟶ C₂'}
           {D₁ : twosided_disp_cat C₁ C₂}
           {D₂ : twosided_disp_cat C₁' C₂'}
           (FG : twosided_disp_functor F G D₁ D₂)
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {xy₁ : D₁ x₁ y₁}
           {xy₂ : D₁ x₂ y₂}
           {f f' : x₁ --> x₂}
           (p : f = f')
           {g g' : y₁ --> y₂}
           (q : g = g')
           (fg : xy₁ -->[ f' ][ g' ] xy₂)
  : #2 FG (transportb_disp_mor2 p q fg)
    =
    transportb_disp_mor2
      (maponpaths (λ z, #F z) p)
      (maponpaths (λ z, #G z) q)
      (#2 FG fg).
Proof.
  induction p, q.
  apply idpath.
Qed.

(**
 3. The total functor
 *)
Section TotalFunctor.
  Context {C₁ C₁' C₂ C₂' : category}
          {F : C₁ ⟶ C₁'}
          {G : C₂ ⟶ C₂'}
          {D₁ : twosided_disp_cat C₁ C₂}
          {D₂ : twosided_disp_cat C₁' C₂'}
          (FG : twosided_disp_functor F G D₁ D₂).

  Definition total_twosided_disp_functor_data
    : functor_data
        (total_twosided_disp_category D₁)
        (total_twosided_disp_category D₂).
  Proof.
    use make_functor_data.
    - exact (λ xy, F (pr1 xy) ,, G (pr12 xy) ,, FG _ _ (pr22 xy)).
    - exact (λ xy₁ xy₂ fg, #F (pr1 fg) ,, #G (pr12 fg) ,, #2 FG (pr22 fg)).
  Defined.

  Definition total_twosided_disp_functor_is_functor
    : is_functor total_twosided_disp_functor_data.
  Proof.
    split.
    - intro ; intros ; cbn.
      use total2_paths_2_b.
      + apply functor_id.
      + apply functor_id.
      + apply twosided_disp_functor_id.
    - intro ; intros ; cbn.
      use total2_paths_2_b.
      + apply functor_comp.
      + apply functor_comp.
      + apply twosided_disp_functor_comp.
  Qed.

  Definition total_twosided_disp_functor
    : total_twosided_disp_category D₁ ⟶ total_twosided_disp_category D₂.
  Proof.
    use make_functor.
    - exact total_twosided_disp_functor_data.
    - exact total_twosided_disp_functor_is_functor.
  Defined.
End TotalFunctor.

(**
 4. The identity
 *)
Section IdFunctor.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂).

  Definition twosided_disp_functor_identity_data
    : twosided_disp_functor_data
        (functor_identity C₁) (functor_identity C₂)
        D D.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y xy, xy).
    - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg, fg).
  Defined.

  Definition twosided_disp_functor_identity_laws
    : twosided_disp_functor_laws
        _ _ _ _
        twosided_disp_functor_identity_data.
  Proof.
    split.
    - intros x y xy ; cbn.
      apply idpath.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ g₁ fg₁ f₂ g₂ fg₂ ; cbn.
      apply idpath.
  Qed.

  Definition twosided_disp_functor_identity
    : twosided_disp_functor
        (functor_identity C₁) (functor_identity C₂)
        D D.
  Proof.
    simple refine (_ ,, _).
    - exact twosided_disp_functor_identity_data.
    - exact twosided_disp_functor_identity_laws.
  Defined.
End IdFunctor.

(**
 5. Composition
 *)
Section CompFunctor.
  Context {C₁ C₁' C₁'' C₂ C₂' C₂'' : category}
          {F : C₁ ⟶ C₁'} {F' : C₁' ⟶ C₁''}
          {G : C₂ ⟶ C₂'} {G' : C₂' ⟶ C₂''}
          {D : twosided_disp_cat C₁ C₂}
          {D' : twosided_disp_cat C₁' C₂'}
          {D'' : twosided_disp_cat C₁'' C₂''}
          (FG : twosided_disp_functor F G D D')
          (FG' : twosided_disp_functor F' G' D' D'').

  Definition comp_twosided_disp_functor_data
    : twosided_disp_functor_data (F ∙ F') (G ∙ G') D D''.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y xy, FG' _ _ (FG _ _ xy)).
    - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg, #2 FG' (#2 FG fg)).
  Defined.

  Definition comp_twosided_disp_functor_laws
    : twosided_disp_functor_laws _ _ _ _ comp_twosided_disp_functor_data.
  Proof.
    split.
    - intro ; intros ; cbn.
      rewrite twosided_disp_functor_id.
      rewrite transportb_twosided_disp_functor.
      rewrite twosided_disp_functor_id.
      rewrite transport_b_b_disp_mor2.
      use transportb_disp_mor2_eq.
      apply idpath.
    - intro ; intros ; cbn.
      rewrite twosided_disp_functor_comp.
      rewrite transportb_twosided_disp_functor.
      rewrite twosided_disp_functor_comp.
      rewrite transport_b_b_disp_mor2.
      use transportb_disp_mor2_eq.
      apply idpath.
  Qed.

  Definition comp_twosided_disp_functor
    : twosided_disp_functor (F ∙ F') (G ∙ G') D D''.
  Proof.
    simple refine (_ ,, _).
    - exact comp_twosided_disp_functor_data.
    - exact comp_twosided_disp_functor_laws.
  Defined.
End CompFunctor.

(**
 6. Functors between discrete two-sided displayed categories form a set
 *)
Definition isaset_twosided_disp_functor_to_discrete
           {C₁ C₁' C₂ C₂' : category}
           {F : C₁ ⟶ C₁'}
           {G : C₂ ⟶ C₂'}
           (D₁ : twosided_disp_cat C₁ C₂)
           {D₂ : twosided_disp_cat C₁' C₂'}
           (HD : discrete_twosided_disp_cat D₂)
  : isaset (twosided_disp_functor F G D₁ D₂).
Proof.
  use isaset_total2.
  - use isaset_total2.
    + repeat (use impred_isaset ; intro).
      apply isaset_discrete_twosided_cat_ob.
      exact HD.
    + intro.
      repeat (use impred_isaset ; intro).
      apply isaset_disp_mor.
  - intro.
    apply isasetaprop.
    apply isaprop_twosided_disp_functor_laws.
Qed.

(**
 7. Two-sided displayed functors versus displayed functors
 *)
Section ToDispFunctor.
  Context {C₁ C₁' C₂ C₂' : category}
          {F : C₁ ⟶ C₁'}
          {G : C₂ ⟶ C₂'}
          {D₁ : twosided_disp_cat C₁ C₂}
          {D₂ : twosided_disp_cat C₁' C₂'}
          (FG : twosided_disp_functor F G D₁ D₂).

  Definition two_sided_disp_functor_to_disp_functor_data
    : disp_functor_data
        (pair_functor F G)
        (twosided_disp_cat_to_disp_cat _ _ D₁)
        (twosided_disp_cat_to_disp_cat _ _ D₂).
  Proof.
    simple refine (_ ,, _).
    - exact (λ xy, FG (pr1 xy) (pr2 xy)).
    - exact (λ x₁ x₂ xx₁ xx₂ f ff, #2 FG ff).
  Defined.

  Proposition two_sided_disp_functor_to_disp_functor_axioms
    : disp_functor_axioms
        two_sided_disp_functor_to_disp_functor_data.
  Proof.
    split.
    - intros x xx ; cbn.
      rewrite twosided_disp_functor_id.
      unfold transportb_disp_mor2, transportf_disp_mor2.
      rewrite twosided_prod_transport.
      unfold transportb.
      apply maponpaths_2.
      apply isasetdirprod ; apply homset_property.
    - intros x y z xx yy zz f g ff gg ; cbn.
      rewrite twosided_disp_functor_comp.
      unfold transportb_disp_mor2, transportf_disp_mor2.
      rewrite twosided_prod_transport.
      unfold transportb.
      apply maponpaths_2.
      apply isasetdirprod ; apply homset_property.
  Qed.

  Definition two_sided_disp_functor_to_disp_functor
    : disp_functor
        (pair_functor F G)
        (twosided_disp_cat_to_disp_cat _ _ D₁)
        (twosided_disp_cat_to_disp_cat _ _ D₂).
  Proof.
    simple refine (_ ,, _).
    - exact two_sided_disp_functor_to_disp_functor_data.
    - exact two_sided_disp_functor_to_disp_functor_axioms.
  Defined.
End ToDispFunctor.

Section FromDispFunctor.
  Context {C₁ C₁' C₂ C₂' : category}
          {F : C₁ ⟶ C₁'}
          {G : C₂ ⟶ C₂'}
          {D₁ : twosided_disp_cat C₁ C₂}
          {D₂ : twosided_disp_cat C₁' C₂'}
          (FG : disp_functor
                  (pair_functor F G)
                  (twosided_disp_cat_to_disp_cat _ _ D₁)
                  (twosided_disp_cat_to_disp_cat _ _ D₂)).

  Definition disp_functor_to_two_sided_disp_functor_data
    : twosided_disp_functor_data F G D₁ D₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y xy, FG (x ,, y) xy).
    - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg,
             @disp_functor_on_morphisms
                _ _ _ _ _
                FG
                (x₁ ,, y₁) (x₂ ,, y₂)
                xy₁ xy₂
                (f ,, g)
                fg).
  Defined.

  Proposition disp_functor_to_two_sided_disp_functor_axioms
    : twosided_disp_functor_laws
        F G D₁ D₂
        disp_functor_to_two_sided_disp_functor_data.
  Proof.
    split.
    - intros x y xy ; cbn.
      etrans.
      {
        exact (@disp_functor_id _ _ _ _ _ FG (x ,, y) xy).
      }
      unfold transportb_disp_mor2, transportf_disp_mor2.
      rewrite twosided_prod_transport.
      unfold transportb.
      apply maponpaths_2.
      apply isasetdirprod ; apply homset_property.
    - intros x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ g₁ fg₁ f₂ g₂ fg₂ ; cbn.
      etrans.
      {
        exact (@disp_functor_comp
                 _ _ _ _ _
                 FG
                 (x₁ ,, y₁) (x₂ ,, y₂) (x₃ ,, y₃)
                 xy₁ xy₂ xy₃
                 (f₁ ,, g₁) (f₂ ,, g₂)
                 fg₁ fg₂).
      }
      unfold transportb_disp_mor2, transportf_disp_mor2.
      rewrite twosided_prod_transport.
      unfold transportb.
      apply maponpaths_2.
      apply isasetdirprod ; apply homset_property.
  Qed.

  Definition disp_functor_to_two_sided_disp_functor
    : twosided_disp_functor F G D₁ D₂.
  Proof.
    simple refine (_ ,, _).
    - exact disp_functor_to_two_sided_disp_functor_data.
    - exact disp_functor_to_two_sided_disp_functor_axioms.
  Defined.
End FromDispFunctor.

Definition two_sided_disp_functor_weq_disp_functor
           {C₁ C₁' C₂ C₂' : category}
           (F : C₁ ⟶ C₁')
           (G : C₂ ⟶ C₂')
           (D₁ : twosided_disp_cat C₁ C₂)
           (D₂ : twosided_disp_cat C₁' C₂')
  : twosided_disp_functor F G D₁ D₂
    ≃
    disp_functor
      (pair_functor F G)
      (twosided_disp_cat_to_disp_cat _ _ D₁)
      (twosided_disp_cat_to_disp_cat _ _ D₂).
Proof.
  use weq_iso.
  - exact two_sided_disp_functor_to_disp_functor.
  - exact disp_functor_to_two_sided_disp_functor.
  - abstract
      (intros FG ;
       use subtypePath ; [ intro ; apply isaprop_twosided_disp_functor_laws | ] ;
       apply idpath).
  - abstract
      (intros FG ;
       use subtypePath ; [ intro ; apply isaprop_disp_functor_axioms | ] ;
       apply idpath).
Defined.
