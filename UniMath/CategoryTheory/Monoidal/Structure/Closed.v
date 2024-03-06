(*********************************************************************************

 Closed monoidal categories

 A closed monoidal category is one for which tensoring with a fixed object has a
 right adjoint. Depending on whether the monoidal category is symmetric or not,
 there are different variations of this definition. If the monoidal category is
 not symmetric, then there are two variations, namely left closed and right
 closed, and their difference is whether we look at an adjoint for tensoring with
 an object on the left or on the right. For symmetric monoidal categories, these
 two definitions coincide.

 We also define accessors and a builder for symmetric monoidal categories. They
 are based on having lambda abstraction and application with the usual beta and
 eta laws. In addition, we define some standard functions and we prove some laws
 about them.

 Contents
 1. Basic definitions
 2. Accessors for symmetric monoidal categories
 3. Standard functions

 *********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

(**
 1. Basic definitions
 *)
Section ClosedMonoidalCategories.

  (** the choice of "left closed" for this definition follows the convention at https://ncatlab.org/nlab/show/closed+monoidal+category, but it is called "right closed" at https://en.wikipedia.org/wiki/Closed_monoidal_category *)
  Definition monoidal_leftclosed {C : category} (M : monoidal C) : UU
    := ∏ X : C, ∑ homX : functor C C,
          are_adjoints
            (rightwhiskering_functor M X)
            homX.

  Definition monoidal_leftclosed_exp {C : category} {M : monoidal C}
             (LC : monoidal_leftclosed M) : C -> functor C C
    := λ X, pr1 (LC X).

  Definition monoidal_rightclosed {C : category} (M : monoidal C) : UU
    := ∏ X : C, ∑ homX : functor C C,
          are_adjoints
            (leftwhiskering_functor M X)
            homX.

  Definition monoidal_biclosed {C : category} (M : monoidal C) : UU
    := monoidal_leftclosed M × monoidal_rightclosed M.

  Lemma adj_closed_under_nat_z_iso
        {C D : category} {F1 F2 : functor C D} (α : nat_z_iso F1 F2) (G : functor D C)
    : are_adjoints F2 G -> are_adjoints F1 G.
  Proof.
    intro adj.
    simple refine (are_adjoints_closed_under_iso F2 F1 G _ adj).
    apply z_iso_inv.
    apply z_iso_is_nat_z_iso.
    assumption.
  Defined.

  Lemma leftclosed_symmetric_is_rightclosed {C : category} (M : monoidal C)
    : symmetric M -> monoidal_leftclosed M -> monoidal_rightclosed M.
  Proof.
    intros B LC.
    intro x.
    exists (monoidal_leftclosed_exp LC x).
    apply (adj_closed_under_nat_z_iso (F2 := rightwhiskering_functor M x)).
    - apply symmetric_whiskers_swap_nat_z_iso.
      exact B.
    - exact (pr2 (LC x)).
  Defined.

  Lemma leftclosed_symmetric_is_biclosed {C : category} (M : monoidal C)
    : symmetric M -> monoidal_leftclosed M -> monoidal_biclosed M.
  Proof.
    exact (λ S LC, LC ,, leftclosed_symmetric_is_rightclosed M S LC).
  Defined.
End ClosedMonoidalCategories.

(**
 2. Accessors for symmetric monoidal categories
 *)
Definition sym_mon_closed_cat
  : UU
  := ∑ (V : sym_monoidal_cat), monoidal_leftclosed V.

#[reversible=no] Coercion sym_monoidal_closed_cat_to_sym_monoidal_cat
         (V : sym_mon_closed_cat)
  : sym_monoidal_cat
  := pr1 V.

Section Builder.
  Context (V : sym_monoidal_cat)
          (HomV : V → V → V)
          (eval : ∏ (x y : V), HomV x y ⊗ x --> y)
          (lam : ∏ (x y z : V) (f : z ⊗ x --> y), z --> HomV x y)
          (betaEq : ∏ (x y z : V) (f : z ⊗ x --> y),
                    lam x y z f #⊗ identity x · eval x y
                    =
                    f)
          (etaEq : ∏ (x y z : V) (g : z --> HomV x y),
                   g
                   =
                   lam x y z (g #⊗ identity _ · eval x y)).

  Definition make_left_closed_universal
             (x y : V)
    : is_universal_arrow_from
        (rightwhiskering_functor V x)
        y
        (HomV x y)
        (eval x y).
  Proof.
    intros z f.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         refine (etaEq _ _ _ _ @ _ @ !(etaEq _ _ _ _)) ;
         apply maponpaths ;
         refine (_ @ !(pr2 φ₁) @ pr2 φ₂ @ !_) ;
         apply maponpaths_2 ;
         refine (_ @ id_right _) ;
         unfold rightwhiskering_on_morphisms ;
         unfold monoidal_cat_tensor_mor ;
         unfold functoronmorphisms1 ;
         apply maponpaths ;
         apply (bifunctor_leftid V)).
    - simple refine (_ ,, _).
      + exact (lam x y z f).
      + abstract
          (refine (!(betaEq x y z f) @ _) ; cbn ;
           apply maponpaths_2 ;
           refine (_ @ id_right _) ;
           unfold rightwhiskering_on_morphisms ;
           unfold monoidal_cat_tensor_mor ;
           unfold functoronmorphisms1 ;
           apply maponpaths ;
           apply (bifunctor_leftid V)).
  Defined.

  Definition make_monoidal_leftclosed
    : monoidal_leftclosed V.
  Proof.
    intros x.
    pose (right_adjoint_from_partial
             (rightwhiskering_functor V x)
             (HomV x)
             (eval x)
             (make_left_closed_universal x))
      as A.
    exists (Core.G _ _ _ (make_left_closed_universal x)).
    exact (pr2 A).
  Defined.

  Definition make_sym_mon_closed_cat
    : sym_mon_closed_cat
    := V ,, make_monoidal_leftclosed.
End Builder.

Definition internal_hom
           {V : sym_mon_closed_cat}
           (x y : V)
  : V
  := pr1 (pr2 V x) y.

Notation "x ⊸ y" := (internal_hom x y) (at level 45, right associativity) : moncat.
(* \-o or \r-o *)

Section Accessors.
  Context {V : sym_mon_closed_cat}.

  Definition internal_eval
             (x y : V)
    : (x ⊸ y) ⊗ x --> y
    := counit_from_are_adjoints (pr2 (pr2 V x)) y.

  Definition internal_lam
             {x y z : V}
             (f : x ⊗ y --> z)
    : x --> y ⊸ z
    := unit_from_are_adjoints (pr2 (pr2 V y)) x · #(pr1 (pr2 V y)) f.

  Proposition internal_beta
              {x y z : V}
              (f : z ⊗ x --> y)
    : internal_lam f #⊗ identity x · internal_eval x y
      =
      f.
  Proof.
    unfold internal_lam.
    rewrite tensor_comp_r_id_l.
    rewrite !assoc'.
    unfold internal_eval.
    etrans.
    {
      apply maponpaths.
      pose (nat_trans_ax
              (counit_from_are_adjoints (pr2 (pr2 V x)))
              _
              _
              f)
        as p.
      refine (_ @ p).
      apply maponpaths_2.
      cbn.
      unfold rightwhiskering_on_morphisms.
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      refine (_ @ id_right _).
      apply maponpaths.
      apply (bifunctor_leftid V).
    }
    cbn.
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    refine (_ @ triangle_id_left_ad (pr2 (pr2 V x)) _).
    apply maponpaths_2.
    cbn.
    unfold rightwhiskering_on_morphisms.
    unfold monoidal_cat_tensor_mor.
    unfold functoronmorphisms1.
    refine (_ @ id_right _).
    apply maponpaths.
    apply (bifunctor_leftid V).
  Qed.

  Proposition internal_eta
              {x y z : V}
              (f : z --> x ⊸ y)
    : f
      =
      internal_lam (f #⊗ identity _ · internal_eval x y).
  Proof.
    unfold internal_lam.
    unfold internal_eval.
    refine (!_).
    rewrite functor_comp.
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      pose (nat_trans_ax
              (unit_from_are_adjoints (pr2 (pr2 V x)))
              _
              _
              f)
        as p.
      cbn in p.
      refine (_ @ !p).
      do 2 apply maponpaths.
      unfold rightwhiskering_on_morphisms.
      unfold monoidal_cat_tensor_mor.
      unfold functoronmorphisms1.
      refine (_ @ id_right _).
      apply maponpaths.
      apply (bifunctor_leftid V).
    }
    refine (_ @ id_right _).
    rewrite !assoc'.
    apply maponpaths.
    exact (triangle_id_right_ad (pr2 (pr2 V x)) _).
  Qed.
End Accessors.

Definition sym_mon_closed_left_tensor_left_adjoint_universal
           (V : sym_mon_closed_cat)
           (x y : V)
  : is_universal_arrow_from
      (monoidal_left_tensor x)
      y
      (x ⊸ y)
      (sym_mon_braiding V x (x ⊸ y) · internal_eval x y).
Proof.
  intros z f.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply homset_property | ] ;
       refine (internal_eta _ @ _ @ !(internal_eta _)) ;
       apply maponpaths ;
       refine (!(id_left _) @ _ @ id_left _) ;
       rewrite <- !sym_mon_braiding_inv ;
       rewrite !assoc' ;
       apply maponpaths ;
       rewrite !assoc ;
       rewrite <- !tensor_sym_mon_braiding ;
       rewrite !assoc' ;
       exact (!(pr2 φ₁) @ pr2 φ₂)).
  - refine (internal_lam (sym_mon_braiding V z x · f) ,, _).
    abstract
      (cbn -[sym_mon_braiding] ;
       rewrite !assoc ;
       rewrite tensor_sym_mon_braiding ;
       rewrite !assoc' ;
       rewrite internal_beta ;
       rewrite !assoc ;
       rewrite sym_mon_braiding_inv ;
       rewrite id_left ;
       apply idpath).
Defined.

Definition sym_mon_closed_left_tensor_left_adjoint
           (V : sym_mon_closed_cat)
           (x : V)
  : is_left_adjoint (monoidal_left_tensor x).
Proof.
  use left_adjoint_from_partial.
  - exact (λ y, x ⊸ y).
  - exact (λ y, sym_mon_braiding V _ _ · internal_eval _ _).
  - exact (sym_mon_closed_left_tensor_left_adjoint_universal V x).
Defined.

Definition sym_mon_closed_left_tensor_right_adjoint_universal
           (V : sym_mon_closed_cat)
           (x y : V)
  : is_universal_arrow_from
      (monoidal_right_tensor x)
      y
      (x ⊸ y)
      (internal_eval x y).
Proof.
  intros z f.
  use iscontraprop1.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; apply homset_property | ] ;
       refine (internal_eta _ @ _ @ !(internal_eta _)) ;
       apply maponpaths ;
       exact (!(pr2 φ₁) @ pr2 φ₂)).
  - refine (internal_lam f ,, _).
    abstract
      (cbn ;
       rewrite internal_beta ;
       apply idpath).
Defined.

Definition sym_mon_closed_right_tensor_left_adjoint
           (V : sym_mon_closed_cat)
           (x : V)
  : is_left_adjoint (monoidal_right_tensor x).
Proof.
  use left_adjoint_from_partial.
  - exact (λ y, x ⊸ y).
  - exact (λ y, internal_eval _ _).
  - exact (sym_mon_closed_left_tensor_right_adjoint_universal V x).
Defined.

(**
 3. Standard functions
 *)
Section StandardFunctions.
  Context {V : sym_mon_closed_cat}.

  Definition internal_id
             (x : V)
    : I_{V} --> x ⊸ x
    := internal_lam (mon_lunitor _).

  Definition internal_comp
             (x y z : V)
    : (y ⊸ z) ⊗ (x ⊸ y) --> x ⊸ z
    := internal_lam
         (mon_lassociator _ _ _
          · identity _ #⊗ internal_eval x y
          · internal_eval y z).

  Definition internal_from_arr
             {x y : V}
             (f : x --> y)
    : I_{V} --> x ⊸ y
    := internal_lam (mon_lunitor x · f).

  Definition internal_to_arr
             {x y : V}
             (f : I_{V} --> x ⊸ y)
    : x --> y
    := mon_linvunitor x · f #⊗ identity x · internal_eval x y.

  Definition internal_pair
             (x y : V)
    : x --> y ⊸ x ⊗ y
    := internal_lam (identity _).

  Definition internal_swap_arg
             (v₁ v₂ w : V)
    : v₁ ⊸ w ⊸ v₂ --> w ⊸ v₁ ⊸ v₂
    := internal_lam
         (internal_lam
            (mon_lassociator _ _ _
             · identity _ #⊗ sym_mon_braiding _ _ _
             · mon_rassociator _ _ _
             · internal_eval _ _ #⊗ identity _
             · internal_eval _ _)).

  Definition internal_curry
             (v₁ v₂ v₃ : V)
    : v₁ ⊗ v₂ ⊸ v₃ --> v₁ ⊸ v₂ ⊸ v₃
    := internal_lam (internal_lam (mon_lassociator _ _ _ · internal_eval _ _)).

  Definition internal_uncurry
             (v₁ v₂ v₃ : V)
    : v₁ ⊸ v₂ ⊸ v₃ --> v₁ ⊗ v₂ ⊸ v₃
    := internal_lam
         (mon_rassociator _ _ _
          · internal_eval _ _ #⊗ identity _
          · internal_eval _ _).

  Definition internal_precomp
             {x₁ x₂ : V}
             (f : x₁ --> x₂)
             (y : V)
    : x₂ ⊸ y --> x₁ ⊸ y
    := internal_lam (identity _ #⊗ f · internal_eval _ _).

  Definition internal_postcomp
             (x : V)
             {y₁ y₂ : V}
             (g : y₁ --> y₂)
    : x ⊸ y₁ --> x ⊸ y₂
    := internal_lam (internal_eval _ _ · g).

  Definition internal_pre_post_comp
             {x₁ x₂ : V}
             (f : x₁ --> x₂)
             {y₁ y₂ : V}
             (g : y₁ --> y₂)
    : x₂ ⊸ y₁ --> x₁ ⊸ y₂
    := internal_lam (identity _ #⊗ f · internal_eval _ _ · g).

  Proposition internal_funext
              (w x y : V)
              (f g : w --> x ⊸ y)
              (p : ∏ (a : V)
                     (h : a --> x),
                   f #⊗ h · internal_eval x y
                   =
                   g #⊗ h · internal_eval x y)
    : f = g.
  Proof.
    refine (internal_eta f @ _ @ !(internal_eta g)).
    apply maponpaths.
    exact (p x (identity x)).
  Qed.

  Proposition internal_id_left
              (x y : V)
    : mon_lunitor _
      =
      internal_id y #⊗ identity _
      · internal_comp x y y.
  Proof.
    use internal_funext.
    intros w h.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_comp.
    rewrite internal_beta.
    rewrite !assoc.
    rewrite tensor_lassociator.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      rewrite tensor_comp_l_id_l.
      rewrite !assoc'.
      apply maponpaths.
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      unfold internal_id.
      apply internal_beta.
    }
    rewrite tensor_lunitor.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite tensor_lunitor.
    rewrite !assoc.
    rewrite mon_lunitor_triangle.
    rewrite <- tensor_split'.
    apply idpath.
  Qed.

  Proposition internal_id_right
              (x y : V)
    : mon_runitor _
      =
      identity _ #⊗ internal_id x
      · internal_comp x x y.
  Proof.
    use internal_funext.
    intros w h.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_comp.
    rewrite internal_beta.
    rewrite !assoc.
    rewrite tensor_lassociator.
    apply maponpaths_2.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      apply maponpaths.
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      unfold internal_id.
      apply internal_beta.
    }
    rewrite tensor_lunitor.
    rewrite tensor_comp_id_l.
    rewrite !assoc.
    rewrite <- mon_triangle.
    rewrite <- tensor_split'.
    apply idpath.
  Qed.

  Proposition internal_assoc
              (w x y z : V)
    : (internal_comp x y z #⊗ identity _)
      · internal_comp w x z
      =
      mon_lassociator _ _ _
      · (identity _ #⊗ internal_comp w x y)
      · internal_comp w y z.
  Proof.
    use internal_funext.
    intros a h.
    etrans.
    {
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      apply maponpaths.
      apply internal_beta.
    }
    etrans.
    {
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      rewrite tensor_split.
      rewrite !assoc'.
      apply maponpaths.
      apply internal_beta.
    }
    refine (!_).
    etrans.
    {
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      apply maponpaths.
      apply internal_beta.
    }
    rewrite !assoc.
    apply maponpaths_2.
    etrans.
    {
      rewrite !assoc'.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      rewrite <- tensor_comp_id_l.
      do 2 apply maponpaths.
      apply internal_beta.
    }
    rewrite !tensor_comp_id_l.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      rewrite <- tensor_id_id.
      rewrite tensor_lassociator.
      rewrite !tensor_comp_id_l.
      apply idpath.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite mon_lassociator_lassociator.
    rewrite !assoc'.
    rewrite <- tensor_comp_id_l.
    rewrite <- tensor_lassociator.
    rewrite tensor_comp_id_l.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite <- tensor_lassociator.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- tensor_comp_mor.
    rewrite id_left.
    rewrite !tensor_id_id.
    rewrite id_right.
    apply idpath.
  Qed.

  Proposition internal_from_to_arr
              {x y : V}
              (f : I_{V} --> x ⊸ y)
    : internal_from_arr (internal_to_arr f) = f.
  Proof.
    unfold internal_from_arr, internal_to_arr.
    rewrite !assoc.
    rewrite mon_lunitor_linvunitor.
    rewrite id_left.
    exact (!(internal_eta f)).
  Qed.

  Proposition internal_to_from_arr
              {x y : V}
              (f : x --> y)
    : internal_to_arr (internal_from_arr f) = f.
  Proof.
    unfold internal_from_arr, internal_to_arr.
    rewrite !assoc'.
    rewrite internal_beta.
    rewrite !assoc.
    rewrite mon_linvunitor_lunitor.
    apply id_left.
  Qed.

  Proposition internal_to_arr_id
              (x : V)
    : internal_to_arr (internal_id x) = identity x.
  Proof.
    unfold internal_to_arr.
    rewrite !assoc'.
    unfold internal_id.
    rewrite internal_beta.
    apply mon_linvunitor_lunitor.
  Qed.

  Proposition internal_to_arr_comp
              {x y z : V}
              (f : x --> y)
              (g : y --> z)
    : f · g
      =
      internal_to_arr
        (mon_linvunitor I_{V}
         · internal_from_arr g #⊗ internal_from_arr f
         · internal_comp x y z).
  Proof.
    unfold internal_to_arr.
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    unfold internal_comp.
    rewrite internal_beta.
    rewrite tensor_comp_id_r.
    rewrite !assoc'.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite !assoc.
      rewrite tensor_lassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_mor.
      rewrite id_right.
      unfold internal_from_arr.
      rewrite internal_beta.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      apply idpath.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite tensor_lunitor.
    rewrite !assoc.
    refine (_ @ id_left _).
    apply maponpaths_2.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_lunitor_triangle.
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      rewrite mon_linvunitor_lunitor.
      rewrite tensor_id_id.
      apply id_left.
    }
    apply mon_linvunitor_lunitor.
  Qed.

  Proposition internal_eval_natural
              (x : V)
              {y₁ y₂ : V}
              (f : y₁ --> y₂)
    : internal_eval x y₁ · f
      =
      internal_lam (internal_eval _ _ · f) #⊗ identity x · internal_eval x y₂.
  Proof.
    rewrite internal_beta.
    apply idpath.
  Qed.

  Proposition internal_pair_natural
              {x₁ x₂ : V}
              (y : V)
              (f : x₁ --> x₂)
    : f · internal_pair x₂ y
      =
      internal_pair x₁ y · internal_lam (internal_eval _ _ · f #⊗ identity _).
  Proof.
    use internal_funext.
    intros w h.
    rewrite !tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_pair.
    rewrite !internal_beta.
    rewrite !assoc.
    rewrite id_right.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      apply id_right.
    }
    rewrite <- tensor_split.
    apply idpath.
  Qed.

  Proposition internal_lam_natural
              {x₁ x₂ y z : V}
              (f : x₁ --> x₂)
              (g : x₂ ⊗ y --> z)
    : f · internal_lam g = internal_lam (f #⊗ identity y · g).
  Proof.
    use internal_funext.
    intros w h.
    etrans.
    {
      rewrite tensor_split.
      rewrite tensor_comp_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
    }
    apply idpath.
  Qed.

  Proposition internal_pair_eval
              (x y : V)
    : (internal_pair x y) #⊗ identity y · internal_eval y (x ⊗ y) = identity (x ⊗ y).
  Proof.
    unfold internal_pair.
    rewrite internal_beta.
    apply idpath.
  Qed.

  Proposition internal_eval_pair
              (x y : V)
    : internal_pair (x ⊸ y) x · internal_lam (internal_eval _ _ · internal_eval _ _)
      =
      identity (x ⊸ y).
  Proof.
    use internal_funext.
    intros a h.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    rewrite internal_beta.
    etrans.
    {
      rewrite !assoc.
      apply maponpaths_2.
      rewrite tensor_split.
      rewrite !assoc'.
      unfold internal_pair.
      rewrite internal_beta.
      apply id_right.
    }
    apply idpath.
  Qed.

  Proposition internal_curry_uncurry
              (v₁ v₂ v₃ : V)
    : internal_curry v₁ v₂ v₃ · internal_uncurry v₁ v₂ v₃ = identity _.
  Proof.
    use internal_funext.
    intros w h.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_uncurry.
    rewrite internal_beta.
    rewrite tensor_split.
    rewrite <- tensor_id_id.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite tensor_rassociator.
      rewrite !assoc'.
      apply maponpaths.
      rewrite !assoc.
      rewrite <- tensor_comp_id_r.
      unfold internal_curry.
      rewrite !internal_beta.
      apply idpath.
    }
    rewrite !assoc.
    apply maponpaths_2.
    rewrite !assoc'.
    rewrite mon_rassociator_lassociator.
    apply id_right.
  Qed.

  Proposition internal_uncurry_curry
              (v₁ v₂ v₃ : V)
    : internal_uncurry v₁ v₂ v₃ · internal_curry v₁ v₂ v₃ = identity _.
  Proof.
    use internal_funext.
    intros w₁ h₁.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_curry.
    rewrite internal_beta.
    use internal_funext.
    intros w₂ h₂.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    rewrite internal_beta.
    rewrite !assoc.
    rewrite tensor_lassociator.
    rewrite tensor_split.
    rewrite !assoc'.
    unfold internal_uncurry.
    rewrite internal_beta.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- tensor_lassociator.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      rewrite !assoc.
      rewrite mon_lassociator_rassociator.
      apply id_left.
    }
    rewrite <- !tensor_comp_mor.
    rewrite id_right.
    apply idpath.
  Qed.

  Definition internal_hom_equiv
             (x y z : V)
    : (x --> y ⊸ z) ≃ (x ⊗ y --> z).
  Proof.
    use weq_iso.
    - exact (λ f, f #⊗ identity y · internal_eval y z).
    - exact (λ f, internal_lam f).
    - abstract
        (intro f ; cbn ;
         use internal_funext ;
         intros w h ;
         rewrite tensor_split ;
         rewrite !assoc' ;
         rewrite internal_beta ;
         rewrite !assoc ;
         rewrite <- tensor_split ;
         apply idpath).
    - abstract
        (intro f ; cbn ;
         apply internal_beta).
  Defined.

  Proposition internal_precomp_id
              (x y : V)
    : internal_precomp (identity x) y = identity _.
  Proof.
    use internal_funext.
    intros a h.
    rewrite tensor_split.
    rewrite assoc'.
    unfold internal_precomp.
    rewrite internal_beta.
    rewrite tensor_id_id.
    rewrite id_left.
    apply idpath.
  Qed.

  Proposition internal_precomp_comp
              {x₁ x₂ x₃ : V}
              (f₁ : x₁ --> x₂)
              (f₂ : x₂ --> x₃)
              (y : V)
    : internal_precomp (f₁ · f₂) y
      =
      internal_precomp f₂ y · internal_precomp f₁ y.
  Proof.
    use internal_funext.
    intros a h.
    rewrite tensor_split.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_precomp.
    rewrite !internal_beta.
    refine (!_).
    rewrite tensor_split.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split'.
    rewrite tensor_split.
    rewrite !assoc'.
    rewrite internal_beta.
    rewrite !assoc.
    rewrite <- tensor_comp_id_l.
    apply idpath.
  Qed.

  Proposition internal_postcomp_id
              (x y : V)
    : internal_postcomp x (identity y) = identity _.
  Proof.
    use internal_funext.
    intros a h.
    rewrite tensor_split.
    rewrite assoc'.
    unfold internal_postcomp.
    rewrite internal_beta.
    rewrite id_right.
    apply idpath.
  Qed.

  Proposition internal_postcomp_comp
              (x : V)
              {y₁ y₂ y₃ : V}
              (g₁ : y₁ --> y₂)
              (g₂ : y₂ --> y₃)
    : internal_postcomp x (g₁ · g₂)
      =
      internal_postcomp x g₁ · internal_postcomp x g₂.
  Proof.
    use internal_funext.
    intros a h.
    rewrite tensor_split.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_postcomp.
    rewrite !internal_beta.
    refine (!_).
    rewrite tensor_split.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite internal_beta.
    apply idpath.
  Qed.

  Proposition internal_pre_post_comp_as_pre_post_comp
              {x₁ x₂ : V}
              (f : x₁ --> x₂)
              {y₁ y₂ : V}
              (g : y₁ --> y₂)
    : internal_pre_post_comp f g
      =
      internal_precomp f y₁ · internal_postcomp x₁ g.
  Proof.
    use internal_funext.
    intros a h.
    rewrite tensor_split.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_precomp, internal_postcomp, internal_pre_post_comp.
    rewrite !internal_beta.
    refine (!_).
    rewrite tensor_split.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite internal_beta.
    apply idpath.
  Qed.

  Proposition internal_pre_post_comp_as_post_pre_comp
              {x₁ x₂ : V}
              (f : x₁ --> x₂)
              {y₁ y₂ : V}
              (g : y₁ --> y₂)
    : internal_pre_post_comp f g
      =
      internal_postcomp x₂ g · internal_precomp f y₂.
  Proof.
    use internal_funext.
    intros a h.
    rewrite tensor_split.
    rewrite tensor_comp_r_id_r.
    rewrite !assoc'.
    unfold internal_precomp, internal_postcomp, internal_pre_post_comp.
    rewrite !internal_beta.
    refine (!_).
    rewrite tensor_split.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    rewrite <- tensor_split'.
    rewrite tensor_split.
    rewrite !assoc'.
    rewrite internal_beta.
    apply idpath.
  Qed.

  Proposition internal_pre_post_comp_id
              (x y : V)
    : internal_pre_post_comp (identity x) (identity y)
      =
      identity _.
  Proof.
    rewrite internal_pre_post_comp_as_pre_post_comp.
    rewrite internal_precomp_id.
    rewrite internal_postcomp_id.
    rewrite id_left.
    apply idpath.
  Qed.

  Proposition internal_pre_post_comp_comp
              {x₁ x₂ x₃ : V}
              (f₁ : x₁ --> x₂)
              (f₂ : x₂ --> x₃)
              {y₁ y₂ y₃ : V}
              (g₁ : y₁ --> y₂)
              (g₂ : y₂ --> y₃)
    : internal_pre_post_comp (f₁ · f₂) (g₁ · g₂)
      =
      internal_pre_post_comp f₂ g₁ · internal_pre_post_comp f₁ g₂.
  Proof.
    rewrite !internal_pre_post_comp_as_pre_post_comp.
    rewrite internal_precomp_comp.
    rewrite internal_postcomp_comp.
    rewrite !assoc'.
    apply maponpaths.
    rewrite !assoc.
    apply maponpaths_2.
    rewrite <- internal_pre_post_comp_as_pre_post_comp.
    rewrite <- internal_pre_post_comp_as_post_pre_comp.
    apply idpath.
  Qed.
End StandardFunctions.
