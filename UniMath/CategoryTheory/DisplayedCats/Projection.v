(**
Author: Niels van der Weide

In this file, we show the following:
- a displayed category adds properties if the type of displayed morphisms is contractible
- a displayed category adds structure if the type of displayed morphisms is a proposition
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Local Open Scope cat.

(**
We start with the definitions from
https://ncatlab.org/nlab/show/stuff%2C+structure%2C+property#definitions
 *)
Definition adds_structure
           {C : category}
           (D : disp_cat C)
  : UU
  := faithful (pr1_category D).

Definition adds_properties
           {C : category}
           (D : disp_cat C)
  : UU
  := full_and_faithful (pr1_category D).

(**
Now we give some conditions to check whether structure or properties are being added via the hlevel of the displayed morphisms.
We start with local propositionality.
 *)
Definition locally_propositional
           {C : category}
           (D : disp_cat C)
  : UU
  := ∏ (x y : C)
       (f : x --> y)
       (xx : D x) (yy : D y),
     isaprop (xx -->[ f ] yy).

Definition isaprop_locally_propositional
           {C : category}
           (D : disp_cat C)
  : isaprop (locally_propositional D).
Proof.
  do 5 (use impred ; intro).
  apply isapropisaprop.
Defined.

(**
A displayed category is locally inhabited if there is a displayed morphism above each morphism in the base.
 *)
Definition locally_inhabited
           {C : category}
           (D : disp_cat C)
  : UU
  := ∏ (x y : C)
       (f : x --> y)
       (xx : D x) (yy : D y),
     xx -->[ f ] yy.

(**
Lastly, we look at local contractability.
 *)
Definition locally_contractible
           {C : category}
           (D : disp_cat C)
  : UU
  := ∏ (x y : C)
       (f : x --> y)
       (xx : D x) (yy : D y),
     iscontr (xx -->[ f ] yy).

Definition isaprop_locally_contractible
           {C : category}
           (D : disp_cat C)
  : isaprop (locally_contractible D).
Proof.
  do 5 (use impred ; intro).
  apply isapropiscontr.
Defined.

(**
Now let us look at the relations between these three properties.
 *)
Definition locally_propositional_if_locally_contractible
           {C : category}
           (D : disp_cat C)
  : locally_contractible D → locally_propositional D.
Proof.
  intros HD ? ; intros.
  apply isapropifcontr.
  apply HD.
Defined.

Definition locally_inhabited_if_locally_contractible
           {C : category}
           (D : disp_cat C)
  : locally_contractible D → locally_inhabited D.
Proof.
  intros HD ? ; intros.
  apply HD.
Defined.

Definition locally_contractible_if_locally_inhabited_prop
           {C : category}
           (D : disp_cat C)
  : locally_inhabited D
    → locally_propositional D
    → locally_contractible D.
Proof.
  intros HD₁ HD₂ x y f xx yy.
  use iscontraprop1.
  - exact (HD₂ x y f xx yy).
  - exact (HD₁ x y f xx yy).
Defined.

(**
Locally propositionality implies the displayed objects form a set.
For this, we assume the displayed univalence.
 *)
Definition locally_propositional_to_obj_set
           {C : category}
           (D : disp_cat C)
           (HD₁ : is_univalent_disp D)
           (HD₂ : locally_propositional D)
  : ∏ (x : C), isaset (D x).
Proof.
  intros x xx yy.
  specialize (HD₁ x x (idpath _) xx yy).
  apply (isofhlevelweqb 1 (make_weq _ HD₁)).
  use isofhleveltotal2.
  - apply HD₂.
  - intro.
    apply isaprop_is_iso_disp.
Defined.

(**
Locally contractibility implies the displayed objects form a proposition.
We first show that all displayed morphisms are invertible.
Again we assume displayed univalence.
 *)
Definition locally_contractible_disp_iso
           {C : category}
           (D : disp_cat C)
           {x y : C}
           {f : iso x y}
           {xx : D x} {yy : D y}
           (ff : xx -->[ f ] yy)
           (HD : locally_contractible D)
  : is_iso_disp f ff.
Proof.
  simple refine (_ ,, _ ,, _).
  - apply HD.
  - apply (locally_propositional_if_locally_contractible _ HD).
  - apply (locally_propositional_if_locally_contractible _ HD).
Defined.

Definition locally_contractible_to_obj_prop
           {C : category}
           (D : disp_cat C)
           (HD₁ : is_univalent_disp D)
           (HD₂ : locally_contractible D)
  : ∏ (x : C), isaprop (D x).
Proof.
  intros x xx yy.
  specialize (HD₁ x x (idpath _) xx yy).
  apply (isofhlevelweqb 0 (make_weq _ HD₁)).
  use isofhleveltotal2.
  - apply HD₂.
  - intro f.
    apply iscontraprop1.
    + apply isaprop_is_iso_disp.
    + apply locally_contractible_disp_iso.
      apply HD₂.
Defined.

(**
Adding properties is the same as being locally propositional
 *)
Section DispProjectionIsFaithful.
  Context {C : category}
          (D : disp_cat C)
          (HD : locally_propositional D).

  Definition pr1_category_faithful
    : adds_structure D.
  Proof.
    intros x y f.
    use invproofirrelevance.
    intros fib₁ fib₂.
    use subtypePath.
    { intro ; apply homset_property. }
    use subtypePath.
    { intro ; apply HD. }
    exact (pr2 fib₁ @ !(pr2 fib₂)).
  Defined.
End DispProjectionIsFaithful.

Section DispProjectionIsPropositional.
  Context {C : category}
          (D : disp_cat C)
          (HD : adds_structure D).

  Definition disp_cat_is_locally_propositional
    : locally_propositional D.
  Proof.
    intros x y f xx yy.
    apply invproofirrelevance.
    intros ff gg.
    unfold faithful in HD.
    specialize (HD (x ,, xx) (y ,, yy) f).
    pose (proofirrelevance _ HD ((f ,, ff) ,, idpath _) ((f ,, gg) ,, idpath _)) as HD'.
    simpl in HD'.
    pose (maponpaths pr1 HD') as p.
    refine (_ @ fiber_paths p).
    refine (!_) ; cbn.
    apply transportf_set.
    apply homset_property.
  Defined.
End DispProjectionIsPropositional.

Definition adds_structure_weq_locally_propositional
           {C : category}
           (D : disp_cat C)
  : adds_structure D ≃ locally_propositional D.
Proof.
  use weqimplimpl.
  - exact (disp_cat_is_locally_propositional D).
  - exact (pr1_category_faithful D).
  - apply isaprop_faithful.
  - apply isaprop_locally_propositional.
Defined.

(**
Adding structure is the same as being locally contractible
 *)
Section DispProjectionIsFull.
  Context {C : category}
          (D : disp_cat C)
          (HD : locally_inhabited D).

  Definition pr1_category_full
    : full (pr1_category D).
  Proof.
    intros x y f.
    apply hinhpr.
    refine ((f ,, _) ,, idpath _) ; cbn.
    exact (HD (pr1 x) (pr1 y) f (pr2 x) (pr2 y)).
  Defined.
End DispProjectionIsFull.

Section DispProjectionIsFullAndFaithful.
  Context {C : category}
          (D : disp_cat C)
          (HD : locally_contractible D).

  Definition pr1_category_fully_faithful
    : adds_properties D.
  Proof.
    split.
    - apply pr1_category_full.
      apply locally_inhabited_if_locally_contractible.
      apply HD.
    - apply pr1_category_faithful.
      apply locally_propositional_if_locally_contractible.
      apply HD.
  Defined.
End DispProjectionIsFullAndFaithful.

Section DispProjectionIsContractible.
  Context {C : category}
          (D : disp_cat C)
          (HD : adds_properties D).

  Definition pr1_category_inhabited
    : locally_inhabited D.
  Proof.
    intros x y f xx yy.
    pose (pr1 HD (x ,, xx) (y ,, yy) f) as i.
    unfold issurjective in i.
    cbn in i.
    use (@hinhuniv _ (make_hProp _ _) _ i).
    - apply disp_cat_is_locally_propositional.
      apply HD.
    - cbn ; intros z.
      pose (pr21 z) as m.
      pose (pr2 z) as p.
      cbn in m, p.
      exact (transportf (λ z, xx -->[ z ] yy) p m).
  Defined.

  Definition pr1_category_locally_contractible
    : locally_contractible D.
  Proof.
    use locally_contractible_if_locally_inhabited_prop.
    - exact pr1_category_inhabited.
    - apply disp_cat_is_locally_propositional.
      apply HD.
  Defined.
End DispProjectionIsContractible.

Definition adds_properties_weq_locally_contractible
           {C : category}
           (D : disp_cat C)
  : adds_properties D ≃ locally_contractible D.
Proof.
  use weqimplimpl.
  - exact (pr1_category_locally_contractible D).
  - exact (pr1_category_fully_faithful D).
  - apply isaprop_full_and_faithful.
  - apply isaprop_locally_contractible.
Defined.
