(*******************************************************************************

 Strict 2-sided displayed categories

 A strict 2-sided displayed category is a 2-sided displayed category for which
 the displayed objects form a set. Generally speaking, this notion is rather restricting.
 Most examples of (displayed) categories are univalent but not strict. However,
 if one is looking at strict categories, then strict 2-sided displayed categories
 come up naturally.

 Finally, when one is looking at strict 2-sided displayed categories, then one
 is also interested in the equality of 2-sided displayed functors. We prove
 that the type of 2-sided displayed functors forms a set and we provide equality
 principles for 2-sided displayed functors.

 Contents
 1. Strict 2-sided displayed categories
 2. The total category of a strict 2-sided displayed category
 3. Equality of 2-sided displayed functors

 *******************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.DisplayedFunctor.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.

Local Open Scope cat.

(** * 1. Strict 2-sided displayed categories *)
Definition is_strict_twosided_disp_cat
           {C₁ C₂ : category}
           (D : twosided_disp_cat C₁ C₂)
  : UU
  := ∏ (x : C₁)
       (y : C₂),
     isaset (D x y).

Proposition isaprop_is_strict_twosided_disp_cat
            {C₁ C₂ : category}
            (D : twosided_disp_cat C₁ C₂)
  : isaprop (is_strict_twosided_disp_cat D).
Proof.
  do 2 (use impred ; intro).
  apply isapropisaset.
Qed.

Definition strict_twosided_disp_cat
           (C₁ C₂ : category)
  : UU
  := ∑ (D : twosided_disp_cat C₁ C₂), is_strict_twosided_disp_cat D.

#[reversible=no] Coercion strict_twosided_disp_cat_to_twosided_disp_cat
         {C₁ C₂ : category}
         (D : strict_twosided_disp_cat C₁ C₂)
  : twosided_disp_cat C₁ C₂
  := pr1 D.

Proposition is_strict_strict_twosided_disp_cat
            {C₁ C₂ : category}
            (D : strict_twosided_disp_cat C₁ C₂)
            (x : C₁)
            (y : C₂)
  : isaset (D x y).
Proof.
  exact (pr2 D x y).
Qed.

(** * 2. The total category of a strict 2-sided displayed category *)
Proposition isaset_total_strict_twosided_disp_cat_ob
            {C₁ C₂ : setcategory}
            (D : strict_twosided_disp_cat C₁ C₂)
  : isaset (total_twosided_disp_category D).
Proof.
  use isaset_total2.
  - apply isaset_ob.
  - intro x.
    use isaset_total2.
    + apply isaset_ob.
    + intro y.
      apply is_strict_strict_twosided_disp_cat.
Qed.

Definition total_strict_twosided_disp_cat
           {C₁ C₂ : setcategory}
           (D : strict_twosided_disp_cat C₁ C₂)
  : setcategory.
Proof.
  use make_setcategory.
  - exact (total_twosided_disp_category D).
  - apply isaset_total_strict_twosided_disp_cat_ob.
Defined.

(** * 3. Equality of 2-sided displayed functors *)
Proposition isaset_twosided_disp_functor
            {C₁ C₁' C₂ C₂' : category}
            (F : C₁ ⟶ C₁') (G : C₂ ⟶ C₂')
            (D : strict_twosided_disp_cat C₁ C₂)
            (D' : strict_twosided_disp_cat C₁' C₂')
  : isaset (twosided_disp_functor F G D D').
Proof.
  use isaset_total2.
  - use isaset_total2.
    + repeat (use impred_isaset ; intro).
      apply is_strict_strict_twosided_disp_cat.
    + intro f ; cbn.
      repeat (use impred_isaset ; intro).
      apply isaset_disp_mor.
  - intro FG.
    use isasetaprop.
    apply isaprop_twosided_disp_functor_laws.
Qed.

Proposition eq_twosided_disp_functor_help
            {C₁ C₁' C₂ C₂' : category}
            {F : C₁ ⟶ C₁'} {G : C₂ ⟶ C₂'}
            {D : twosided_disp_cat C₁ C₂}
            {D' : twosided_disp_cat C₁' C₂'}
            (FG₁ FG₂ : twosided_disp_functor F G D D')
            (p : pr11 FG₁ = pr11 FG₂)
            (q : ∏ (x₁ x₂ : C₁)
                   (f : x₁ --> x₂)
                   (y₁ y₂ : C₂)
                   (g : y₁ --> y₂)
                   (xy₁ : D x₁ y₁)
                   (xy₂ : D x₂ y₂)
                   (fg : xy₁ -->[ f ][ g ] xy₂),
                 #2 FG₁ fg
                 ;;2
                 idtoiso_twosided_disp
                   (idpath _) (idpath _)
                   (toforallpaths
                      _ _ _
                      (toforallpaths
                         _ _ _
                         (toforallpaths _ _ _ p x₂)
                         y₂)
                      xy₂)
                 =
                 transportf_disp_mor2
                   (id_left _ @ !(id_right _))
                   (id_left _ @ !(id_right _))
                   (idtoiso_twosided_disp
                      (idpath _) (idpath _)
                      (toforallpaths
                         _ _ _
                         (toforallpaths
                            _ _ _
                            (toforallpaths _ _ _ p x₁)
                            y₁)
                         xy₁)
                    ;;2
                    (#2 FG₂ fg)))
  : FG₁ = FG₂.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_twosided_disp_functor_laws.
  }
  induction FG₁ as [ [ FG₁o FG₁m ] FG₁H ].
  induction FG₂ as [ [ FG₂o FG₂m ] FG₂H ].
  cbn in *.
  induction p ; cbn in q.
  apply maponpaths.
  use funextsec ; intro x₁.
  use funextsec ; intro x₂.
  use funextsec ; intro y₁.
  use funextsec ; intro y₂.
  use funextsec ; intro xy₁.
  use funextsec ; intro xy₂.
  use funextsec ; intro f.
  use funextsec ; intro g.
  use funextsec ; intro fg.
  specialize (q x₁ x₂ f y₁ y₂ g xy₁ xy₂ fg).
  rewrite id_two_disp_left in q.
  rewrite id_two_disp_right in q.
  unfold transportb_disp_mor2 in q.
  rewrite transport_f_f_disp_mor2 in q.
  refine (!(transportbf_disp_mor2 (!(id_right _)) (!(id_right _)) _)
          @ maponpaths (transportb_disp_mor2 _ _) (_ @ q @ _)
          @ transportbf_disp_mor2 _ _ _).
  - use transportf_disp_mor2_eq.
    apply idpath.
  - use transportf_disp_mor2_eq.
    apply idpath.
Qed.

Proposition eq_twosided_disp_functor
            {C₁ C₁' C₂ C₂' : category}
            {F : C₁ ⟶ C₁'} {G : C₂ ⟶ C₂'}
            {D : twosided_disp_cat C₁ C₂}
            {D' : twosided_disp_cat C₁' C₂'}
            (FG₁ FG₂ : twosided_disp_functor F G D D')
            (p : ∏ (x : C₁) (y : C₂) (xy : D x y), FG₁ x y xy = FG₂ x y xy)
            (q : ∏ (x₁ x₂ : C₁)
                   (f : x₁ --> x₂)
                   (y₁ y₂ : C₂)
                   (g : y₁ --> y₂)
                   (xy₁ : D x₁ y₁)
                   (xy₂ : D x₂ y₂)
                   (fg : xy₁ -->[ f ][ g ] xy₂),
                 #2 FG₁ fg
                 ;;2
                 idtoiso_twosided_disp (idpath _) (idpath _) (p x₂ y₂ xy₂)
                 =
                 transportf_disp_mor2
                   (id_left _ @ !(id_right _))
                   (id_left _ @ !(id_right _))
                   (idtoiso_twosided_disp (idpath _) (idpath _) (p x₁ y₁ xy₁)
                    ;;2
                    (#2 FG₂ fg)))
  : FG₁ = FG₂.
Proof.
  use eq_twosided_disp_functor_help.
  - use funextsec ; intro x.
    use funextsec ; intro y.
    use funextsec ; intro xy.
    exact (p x y xy).
  - intros x₁ x₂ f y₁ y₂ g xy₁ xy₂ fg.
    rewrite !toforallpaths_funextsec.
    apply q.
Qed.
