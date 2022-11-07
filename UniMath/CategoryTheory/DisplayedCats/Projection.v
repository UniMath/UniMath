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
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
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

Definition discrete_pr1_category
           {C : category}
           (D : disp_cat C)
  : UU
  := faithful (pr1_category D)
     ×
     conservative (pr1_category D).

Definition pseudomonic_pr1_category
           {C : category}
           (D : disp_cat C)
  : UU
  := pseudomonic (pr1_category D).

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

Definition locally_iso_inhabited
           {C : category}
           (D : disp_cat C)
  : UU
  := ∏ (x y : C)
       (f : z_iso x y)
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

Definition locally_iso_contractible
           {C : category}
           (D : disp_cat C)
  : UU
  := ∏ (x y : C)
       (f : z_iso x y)
       (xx : D x) (yy : D y),
     iscontr (xx -->[ f ] yy).

Definition isaprop_locally_iso_contractible
           {C : category}
           (D : disp_cat C)
  : isaprop (locally_iso_contractible D).
Proof.
  do 5 (use impred ; intro).
  apply isapropiscontr.
Defined.

(**
 A displayed category is called groupoidal if all morphisms over
 isomorphisms are also isomorphisms.
 *)
Definition groupoidal_disp_cat
           {C : category}
           (D : disp_cat C)
  : UU
  := ∏ (x y : C)
       (f : x --> y)
       (Hf : is_z_isomorphism f)
       (xx : D x) (yy : D y)
       (ff : xx -->[ f ] yy),
     is_z_iso_disp (make_z_iso' f Hf) ff.

Definition isaprop_groupoidal_disp_cat
           {C : category}
           (D : disp_cat C)
  : isaprop (groupoidal_disp_cat D).
Proof.
  do 7 (use impred ; intro).
  apply isaprop_is_z_iso_disp.
Qed.

(**
 Discrete displayed categories are both groupoidal and locally propositional.
 *)
Definition discrete_disp_cat
           {C : category}
           (D : disp_cat C)
  : UU
  := locally_propositional D × groupoidal_disp_cat D.

(**
 We define pseudomonic displayed categories as well
 *)
Definition pseudomonic_disp_cat
           {C : category}
           (D : disp_cat C)
  : UU
  := locally_propositional D × locally_iso_inhabited D.

Definition isaprop_pseudomonic_disp_cat
           {C : category}
           (D : disp_cat C)
  : isaprop (pseudomonic_disp_cat D).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use pathsdirprod.
  - apply isaprop_locally_propositional.
  - repeat (use funextsec ; intro).
    apply (pr1 φ₁).
Qed.

(**
Now let us look at the relations between these properties.
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

Definition locally_groupoid_if_pseudomonic
           {C : category}
           (D : disp_cat C)
           (H : pseudomonic_disp_cat D)
  : groupoidal_disp_cat D.
Proof.
  intros x y f Hf xx yy ff.
  simple refine (_ ,, (_ ,, _)).
  + exact (pr2 H y x (z_iso_inv (f ,, Hf)) yy xx).
  + apply H.
  + apply H.
Defined.

Definition pseudomonic_to_iso_contractible
           {C : category}
           {D : disp_cat C}
           (H : pseudomonic_disp_cat D)
  : locally_iso_contractible D.
Proof.
  intros x y f xx yy.
  use iscontraprop1.
  - apply H.
  - apply H.
Qed.

Definition pseudomonic_weq_locally_prop_and_iso_contractible
           {C : category}
           (D : disp_cat C)
  : pseudomonic_disp_cat D
    ≃
    locally_propositional D × locally_iso_contractible D.
Proof.
  use weqimplimpl.
  - intro H.
    split.
    + apply H.
    + apply pseudomonic_to_iso_contractible.
      exact H.
  - intro H.
    split.
    + exact (pr1 H).
    + intros x y f xx yy.
      apply (pr2 H).
  - apply isaprop_pseudomonic_disp_cat.
  - apply isapropdirprod.
    + apply isaprop_locally_propositional.
    + apply isaprop_locally_iso_contractible.
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
    apply isaprop_is_z_iso_disp.
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
           {f : z_iso x y}
           {xx : D x} {yy : D y}
           (ff : xx -->[ f ] yy)
           (HD : locally_contractible D)
  : is_z_iso_disp f ff.
Proof.
  simple refine (_ ,, _ ,, _).
  - apply HD.
  - apply (locally_propositional_if_locally_contractible _ HD).
  - apply (locally_propositional_if_locally_contractible _ HD).
Defined.

Definition locally_iso_contractible_disp_iso
           {C : category}
           (D : disp_cat C)
           {x y : C}
           {f : z_iso x y}
           {xx : D x} {yy : D y}
           (ff : xx -->[ f ] yy)
           (HD : locally_iso_contractible D)
           (HD' : locally_propositional D)
  : is_z_iso_disp f ff.
Proof.
  simple refine (_ ,, _ ,, _).
  - apply (HD y x (z_iso_inv f) yy xx).
  - apply HD'.
  - apply HD'.
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
    + apply isaprop_is_z_iso_disp.
    + apply locally_contractible_disp_iso.
      apply HD₂.
Defined.

Definition locally_iso_contractible_to_obj_prop
           {C : category}
           (D : disp_cat C)
           (HD₁ : is_univalent_disp D)
           (HD₂ : locally_iso_contractible D)
           (HD₃ : locally_propositional D)
  : ∏ (x : C), isaprop (D x).
Proof.
  intros x xx yy.
  specialize (HD₁ x x (idpath _) xx yy).
  apply (isofhlevelweqb 0 (make_weq _ HD₁)).
  use isofhleveltotal2.
  - apply HD₂.
  - intro f.
    apply iscontraprop1.
    + apply isaprop_is_z_iso_disp.
    + apply locally_iso_contractible_disp_iso.
      * apply HD₂.
      * exact HD₃.
Defined.

(**
 We can instantiate this to pseudomonic displayed categories
 *)
Definition pseudomonic_disp_cat_to_obj_prop
           {C : category}
           (D : disp_cat C)
           (HD₁ : is_univalent_disp D)
           (HD₂ : pseudomonic_disp_cat D)
  : ∏ (x : C), isaprop (D x).
Proof.
  apply locally_iso_contractible_to_obj_prop.
  - exact HD₁.
  - apply pseudomonic_to_iso_contractible.
    exact HD₂.
  - apply HD₂.
Defined.

(**
Adding properties is the same as being locally propositional
 *)
Definition pr1_category_faithful
           {C : category}
           (D : disp_cat C)
           (HD : locally_propositional D)
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

Definition disp_cat_is_locally_propositional
           {C : category}
           (D : disp_cat C)
           (HD : adds_structure D)
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

Definition pr1_category_full
          {C : category}
          (D : disp_cat C)
          (HD : locally_inhabited D)
  : full (pr1_category D).
Proof.
  intros x y f.
  apply hinhpr.
  refine ((f ,, _) ,, idpath _) ; cbn.
  exact (HD (pr1 x) (pr1 y) f (pr2 x) (pr2 y)).
Defined.

Definition pr1_category_fully_faithful
          {C : category}
          (D : disp_cat C)
          (HD : locally_contractible D)
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

(**
 Next we relate groupoidal displayed categories with conservativity
 *)
Definition groupoidal_disp_cat_to_conservative
          {C : category}
          {D : disp_cat C}
          (HD : groupoidal_disp_cat D)
  : conservative (pr1_category D).
Proof.
  intros x y f Hf.
  use is_z_iso_total.
  - exact Hf.
  - apply HD.
Defined.

Definition conservative_to_groupoidal_disp_cat
          {C : category}
          {D : disp_cat C}
          (HD : conservative (pr1_category D))
  : groupoidal_disp_cat D.
Proof.
  intros x y f Hf xx yy ff.
  assert (@is_z_isomorphism (total_category D) (_ ,, _) (_ ,, _) (f ,, ff)) as Hff.
  {
    apply HD.
    apply Hf.
  }
  refine (transportf
            (λ z, is_z_iso_disp (make_z_iso' f z) ff)
            _
            (is_z_iso_disp_from_total Hff)).
  apply isaprop_is_z_isomorphism.
Defined.

Definition groupoidal_disp_cat_weq_conservative
          {C : category}
          (D : disp_cat C)
  : groupoidal_disp_cat D ≃ conservative (pr1_category D).
Proof.
  use weqimplimpl.
  - exact groupoidal_disp_cat_to_conservative.
  - exact conservative_to_groupoidal_disp_cat.
  - exact (isaprop_groupoidal_disp_cat D).
  - apply isaprop_conservative.
Defined.

(**
 We can also characterize discrete displayed categories
 *)
Definition discrete_disp_cat_weq_discrete_projection
          {C : category}
          (D : disp_cat C)
  : discrete_disp_cat D ≃ discrete_pr1_category D.
Proof.
  use weqdirprodf.
  - exact (invweq (adds_structure_weq_locally_propositional D)).
  - exact (groupoidal_disp_cat_weq_conservative D).
Defined.

(**
 Now we characterize at pseudomonic displayed categories
 *)
Definition pseudomonic_disp_cat_to_pseudomonic_pr1
          {C : category}
          (D : disp_cat C)
          (H : pseudomonic_disp_cat D)
  : pseudomonic_pr1_category D.
Proof.
  split.
  - apply pr1_category_faithful.
    apply H.
  - intros x y f.
    apply hinhpr.
    simple refine (((pr1 f ,, pr2 H (pr1 x) (pr1 y) f (pr2 x) (pr2 y)) ,, _) ,, _).
    + cbn.
      use is_z_iso_total.
      * exact (pr2 f).
      * cbn.
        apply locally_groupoid_if_pseudomonic.
        apply H.
    + use z_iso_eq ; cbn.
      apply idpath.
Qed.

Definition pseudomonic_disp_cat_from_pseudomonic_pr1
          {C : category}
          (D : disp_cat C)
          (H : pseudomonic_pr1_category D)
  : pseudomonic_disp_cat D.
Proof.
  split.
  - apply disp_cat_is_locally_propositional.
    apply H.
  - intros x y f xx yy.
    use (factor_through_squash _ _ (pr2 H (x ,, xx) (y ,, yy) f)).
    + apply disp_cat_is_locally_propositional.
      apply H.
    + intros ff.
      exact (transportf
               (λ z, _ -->[ z ] _)
               (maponpaths pr1 (pr2 ff))
               (pr211 ff)).
Qed.

Definition pseudomonic_disp_cat_weq_pseudomonic_pr1
          {C : category}
          (D : disp_cat C)
  : pseudomonic_disp_cat D ≃ pseudomonic_pr1_category D.
Proof.
  use weqimplimpl.
  - exact (pseudomonic_disp_cat_to_pseudomonic_pr1 D).
  - exact (pseudomonic_disp_cat_from_pseudomonic_pr1 D).
  - apply isaprop_pseudomonic_disp_cat.
  - apply isaprop_pseudomonic.
Defined.
