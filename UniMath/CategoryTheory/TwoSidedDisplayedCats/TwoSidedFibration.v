From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac Batch Debug.
(**********************************************************************************

 Two-sided fibrations

 In this file, we study two-sided fibrations and we use two-sided displayed
 categories to define them. Note that the 'two-sided' in the name
 'two-sided displayed categories' is taken from two-sided fibrations, and defining
 two-sided fibrations is one of the main goal.

 Our definition is based on Definition 2.3.4 in
    https://arxiv.org/pdf/1806.06129.pdf
 Let's say we have the span `C₁ ⟵ D ⟶ C₂`. In the definition by Loregian and Riehl,
 the functor `D ⟶ C₂` has a cleaving and the functor `D ⟶ C₁` has an opcleaving.
 However, in our definition, it is the other way around. For us, the functor
 `D ⟶ C₁` has a cleaving and `D ⟶ C₂` has an opcleaving. This change has minor
 consequence. For example, if we consider the arrow category on a category `C`,
 then we have a two-sided fibration `C ⟵ Arr(C) ⟶ C` where the left functor is the
 domain and the right functor is the codomain. In the definition by Loregian and
 Riehl, this would be the other way around. If we would use their definition in our
 setting, then we would need to reveres the arrows when defining the arrow category.

 Contents
 1. Opcartesian morphisms
 2. Cartesian morphisms
 3. Cleavings
 4. Two-sided fibrations

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.

Local Open Scope cat.

Section TwoSidedFibration.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂).

  (**
   1. Opcartesian morphisms
   *)
  Definition twosided_opcartesian
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : UU
    := ∏ (x₃ : C₁)
         (y₃ : C₂)
         (xy₃ : D x₃ y₃)
         (f' : x₂ --> x₃)
         (g' : y₂ --> y₃)
         (fg' : xy₁ -->[ f · f' ][ g · g' ] xy₃),
       ∃! (ℓ : xy₂ -->[ f' ][ g' ] xy₃),
       fg ;;2 ℓ = fg'.

  Definition twosided_opcartesian_factorisation
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             {fg : xy₁ -->[ f ][ g ] xy₂}
             (H : twosided_opcartesian fg)
             {x₃ : C₁}
             {y₃ : C₂}
             {xy₃ : D x₃ y₃}
             {f' : x₂ --> x₃}
             {g' : y₂ --> y₃}
             (fg' : xy₁ -->[ f · f' ][ g · g' ] xy₃)
    : xy₂ -->[ f' ][ g' ] xy₃
    := pr11 (H _ _ _ _ _ fg').

  Definition twosided_opcartesian_factorisation_commutes
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             {fg : xy₁ -->[ f ][ g ] xy₂}
             (H : twosided_opcartesian fg)
             {x₃ : C₁}
             {y₃ : C₂}
             {xy₃ : D x₃ y₃}
             {f' : x₂ --> x₃}
             {g' : y₂ --> y₃}
             (fg' : xy₁ -->[ f · f' ][ g · g' ] xy₃)
    : fg ;;2 twosided_opcartesian_factorisation H fg' = fg'
    := pr21 (H _ _ _ _ _ fg').

  (**
   2. Cartesian morphisms
   *)
  Definition twosided_cartesian
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : UU
    := ∏ (x₀ : C₁)
         (y₀ : C₂)
         (xy₀ : D x₀ y₀)
         (f' : x₀ --> x₁)
         (g' : y₀ --> y₁)
         (fg' : xy₀ -->[ f' · f ][ g' · g ] xy₂),
       ∃! (ℓ : xy₀ -->[ f' ][ g' ] xy₁),
       ℓ ;;2 fg = fg'.

  Definition twosided_cartesian_factorisation
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             {fg : xy₁ -->[ f ][ g ] xy₂}
             (H : twosided_cartesian fg)
             {x₀ : C₁}
             {y₀ : C₂}
             {xy₀ : D x₀ y₀}
             {f' : x₀ --> x₁}
             {g' : y₀ --> y₁}
             (fg' : xy₀ -->[ f' · f ][ g' · g ] xy₂)
    : xy₀ -->[ f' ][ g' ] xy₁
    := pr11 (H _ _ _ _ _ fg').

  Definition twosided_cartesian_factorisation_commutes
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             {fg : xy₁ -->[ f ][ g ] xy₂}
             (H : twosided_cartesian fg)
             {x₀ : C₁}
             {y₀ : C₂}
             {xy₀ : D x₀ y₀}
             {f' : x₀ --> x₁}
             {g' : y₀ --> y₁}
             (fg' : xy₀ -->[ f' · f ][ g' · g ] xy₂)
    : twosided_cartesian_factorisation H fg' ;;2 fg = fg'
    := pr21 (H _ _ _ _ _ fg').

  (**
   3. Cleavings
   *)
  Definition twosided_opcleaving
    : UU
    := ∏ (x : C₁)
         (y₁ y₂ : C₂)
         (xy₁ : D x y₁)
         (g : y₁ --> y₂),
       ∑ (xy₂ : D x y₂)
         (ℓ : xy₁ -->[ identity _ ][ g ] xy₂),
       twosided_opcartesian ℓ.

  Definition twosided_opcleaving_ob
             (H : twosided_opcleaving)
             {x : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x y₁)
             (g : y₁ --> y₂)
    : D x y₂
    := pr1 (H x y₁ y₂ xy₁ g).

  Definition twosided_opcleaving_mor
             (H : twosided_opcleaving)
             {x : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x y₁)
             (g : y₁ --> y₂)
    : xy₁ -->[ identity _ ][ g ] twosided_opcleaving_ob H xy₁ g
    := pr12 (H x y₁ y₂ xy₁ g).

  Definition twosided_opcleaving_opcartesian
             (H : twosided_opcleaving)
             {x : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x y₁)
             (g : y₁ --> y₂)
    : twosided_opcartesian (twosided_opcleaving_mor H xy₁ g)
    := pr22 (H x y₁ y₂ xy₁ g).

  Definition twosided_cleaving
    : UU
    := ∏ (x₁ x₂ : C₁)
         (y : C₂)
         (xy₂ : D x₂ y)
         (f : x₁ --> x₂),
       ∑ (xy₁ : D x₁ y)
         (ℓ : xy₁ -->[ f ][ identity _ ] xy₂),
       twosided_cartesian ℓ.

  Definition twosided_cleaving_ob
             (H : twosided_cleaving)
             {x₁ x₂ : C₁}
             {y : C₂}
             (xy₂ : D x₂ y)
             (f : x₁ --> x₂)
    : D x₁ y
    := pr1 (H x₁ x₂ y xy₂ f).

  Definition twosided_cleaving_mor
             (H : twosided_cleaving)
             {x₁ x₂ : C₁}
             {y : C₂}
             (xy₂ : D x₂ y)
             (f : x₁ --> x₂)
    : twosided_cleaving_ob H xy₂ f -->[ f ][ identity _ ] xy₂
    := pr12 (H x₁ x₂ y xy₂ f).

  Definition twosided_cleaving_cartesian
             (H : twosided_cleaving)
             {x₁ x₂ : C₁}
             {y : C₂}
             (xy₂ : D x₂ y)
             (f : x₁ --> x₂)
    : twosided_cartesian (twosided_cleaving_mor H xy₂ f)
    := pr22 (H x₁ x₂ y xy₂ f).

  Definition twosided_commute
             (H₁ : twosided_opcleaving)
             (H₂ : twosided_cleaving)
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (xy : D x₂ y₁)
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : twosided_opcleaving_ob H₁ (twosided_cleaving_ob H₂ xy f) g
      -->[ identity _ ][ identity _ ]
      twosided_cleaving_ob H₂ (twosided_opcleaving_ob H₁ xy g) f.
  Proof.
    use (twosided_opcartesian_factorisation
           (twosided_opcleaving_opcartesian H₁ _ g)).
    use (twosided_cartesian_factorisation
           (twosided_cleaving_cartesian H₂ _ f)).
    refine (transportb
              (λ z, _ -->[ z ][ _ ] _)
              _
              (transportb
                 (λ z, _ -->[ _ ][ z ] _)
                 _
                 (twosided_cleaving_mor H₂ xy f ;;2 twosided_opcleaving_mor H₁ xy g))).
    - abstract
        (rewrite !id_left, !id_right ;
         apply idpath).
    - abstract
        (rewrite !id_left, !id_right ;
         apply idpath).
  Defined.

  Definition is_iso_twosided_commute
             (H₁ : twosided_opcleaving)
             (H₂ : twosided_cleaving)
    : UU
    := ∏ (x₁ x₂ : C₁)
         (y₁ y₂ : C₂)
         (xy : D x₂ y₁)
         (f : x₁ --> x₂)
         (g : y₁ --> y₂),
       is_iso_twosided_disp
         (identity_is_z_iso _)
         (identity_is_z_iso _)
         (twosided_commute H₁ H₂ xy f g).

  (**
   4. Two-sided fibrations
   *)
  Definition twosided_fibration
    : UU
    := ∑ (H₁ : twosided_opcleaving)
         (H₂ : twosided_cleaving),
       is_iso_twosided_commute H₁ H₂.
End TwoSidedFibration.

(**
 5. Discrete two-sided fibrations
 *)
Section DiscreteTwoSidedFibration.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂).

  Definition discrete_twosided_opcartesian
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : UU
    := ∏ (x₃ : C₁)
         (y₃ : C₂)
         (xy₃ : D x₃ y₃)
         (f' : x₂ --> x₃)
         (g' : y₂ --> y₃)
         (fg' : xy₁ -->[ f · f' ][ g · g' ] xy₃),
       xy₂ -->[ f' ][ g' ] xy₃.

  Definition discrete_twosided_opcartesian_is_opcartesian
             (HD : discrete_twosided_disp_cat D)
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             {fg : xy₁ -->[ f ][ g ] xy₂}
             (Hfg : discrete_twosided_opcartesian fg)
    : twosided_opcartesian D fg.
  Proof.
    intros x₃ y₃ xy₃ f' g' fg'.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intro ; intros ;
         use subtypePath ; [ intro ; apply isaset_disp_mor | ] ;
         apply HD).
    - simple refine (_ ,, _).
      + apply Hfg.
        exact fg'.
      + apply HD.
  Defined.

  Definition discrete_twosided_cartesian
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : UU
    := ∏ (x₀ : C₁)
         (y₀ : C₂)
         (xy₀ : D x₀ y₀)
         (f' : x₀ --> x₁)
         (g' : y₀ --> y₁)
         (fg' : xy₀ -->[ f' · f ][ g' · g ] xy₂),
       xy₀ -->[ f' ][ g' ] xy₁.

  Definition discrete_twosided_cartesian_is_cartesian
             (HD : discrete_twosided_disp_cat D)
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             {fg : xy₁ -->[ f ][ g ] xy₂}
             (Hfg : discrete_twosided_cartesian fg)
    : twosided_cartesian D fg.
  Proof.
    intros x₃ y₃ xy₃ f' g' fg'.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intro ; intros ;
         use subtypePath ; [ intro ; apply isaset_disp_mor | ] ;
         apply HD).
    - simple refine (_ ,, _).
      + apply Hfg.
        exact fg'.
      + apply HD.
  Defined.

  Definition discrete_twosided_opcleaving
    : UU
    := ∏ (x : C₁)
         (y₁ y₂ : C₂)
         (xy₁ : D x y₁)
         (g : y₁ --> y₂),
       ∑ (xy₂ : D x y₂)
         (ℓ : xy₁ -->[ identity _ ][ g ] xy₂),
       discrete_twosided_opcartesian ℓ.

  Definition discrete_twosided_opcleaving_ob
             (H : discrete_twosided_opcleaving)
             {x : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x y₁)
             (g : y₁ --> y₂)
    : D x y₂
    := pr1 (H x y₁ y₂ xy₁ g).

  Definition discrete_twosided_opcleaving_mor
             (H : discrete_twosided_opcleaving)
             {x : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x y₁)
             (g : y₁ --> y₂)
    : xy₁ -->[ identity _ ][ g ] discrete_twosided_opcleaving_ob H xy₁ g
    := pr12 (H x y₁ y₂ xy₁ g).

  Definition discrete_twosided_opcleaving_opcartesian
             (H : discrete_twosided_opcleaving)
             {x : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x y₁)
             (g : y₁ --> y₂)
    : discrete_twosided_opcartesian (discrete_twosided_opcleaving_mor H xy₁ g)
    := pr22 (H x y₁ y₂ xy₁ g).

  Definition discrete_twosided_disp_cat_to_opcleaving
             (HD : discrete_twosided_disp_cat D)
             (HD' : discrete_twosided_opcleaving)
    : twosided_opcleaving D.
  Proof.
    intros x y₁ y₂ xy₁ g.
    simple refine (_ ,, _ ,, _).
    - exact (pr1 (HD' x y₁ y₂ xy₁ g)).
    - exact (pr12 (HD' x y₁ y₂ xy₁ g)).
    - apply (discrete_twosided_opcartesian_is_opcartesian HD).
      exact (pr22 (HD' x y₁ y₂ xy₁ g)).
  Defined.

  Definition discrete_twosided_cleaving
    : UU
    := ∏ (x₁ x₂ : C₁)
         (y : C₂)
         (xy₂ : D x₂ y)
         (f : x₁ --> x₂),
       ∑ (xy₁ : D x₁ y)
         (ℓ : xy₁ -->[ f ][ identity _ ] xy₂),
       discrete_twosided_cartesian ℓ.

  Definition discrete_twosided_cleaving_ob
             (H : discrete_twosided_cleaving)
             {x₁ x₂ : C₁}
             {y : C₂}
             (xy₂ : D x₂ y)
             (f : x₁ --> x₂)
    : D x₁ y
    := pr1 (H x₁ x₂ y xy₂ f).

  Definition discrete_twosided_cleaving_mor
             (H : discrete_twosided_cleaving)
             {x₁ x₂ : C₁}
             {y : C₂}
             (xy₂ : D x₂ y)
             (f : x₁ --> x₂)
    : discrete_twosided_cleaving_ob H xy₂ f -->[ f ][ identity _ ] xy₂
    := pr12 (H x₁ x₂ y xy₂ f).

  Definition discrete_twosided_cleaving_cartesian
             (H : discrete_twosided_cleaving)
             {x₁ x₂ : C₁}
             {y : C₂}
             (xy₂ : D x₂ y)
             (f : x₁ --> x₂)
    : discrete_twosided_cartesian (discrete_twosided_cleaving_mor H xy₂ f)
    := pr22 (H x₁ x₂ y xy₂ f).

  Definition discrete_twosided_disp_cat_to_cleaving
             (HD : discrete_twosided_disp_cat D)
             (HD' : discrete_twosided_cleaving)
    : twosided_cleaving D.
  Proof.
    intros x y₁ y₂ xy₁ g.
    simple refine (_ ,, _ ,, _).
    - exact (pr1 (HD' x y₁ y₂ xy₁ g)).
    - exact (pr12 (HD' x y₁ y₂ xy₁ g)).
    - apply (discrete_twosided_cartesian_is_cartesian HD).
      exact (pr22 (HD' x y₁ y₂ xy₁ g)).
  Defined.
End DiscreteTwoSidedFibration.

Definition is_discrete_twosided_fibration
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           (HD : discrete_twosided_disp_cat D)
  : UU
  := discrete_twosided_cleaving D × discrete_twosided_opcleaving D.

Definition discrete_twosided_fibration
           (C₁ C₂ : category)
  : UU
  := ∑ (D : twosided_disp_cat C₁ C₂)
       (HD : discrete_twosided_disp_cat D),
     is_discrete_twosided_fibration HD.

Coercion discrete_twosided_fibration_to_twosided_disp_cat
         {C₁ C₂ : category}
         (D : discrete_twosided_fibration C₁ C₂)
  : twosided_disp_cat C₁ C₂
  := pr1 D.

Definition discrete_twosided_disp_cat_is_fibration
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           (HD : discrete_twosided_disp_cat D)
           (HD' : is_discrete_twosided_fibration HD)
  : twosided_fibration D.
Proof.
  simple refine (_ ,, _ ,, _).
  - apply discrete_twosided_disp_cat_to_opcleaving.
    + exact HD.
    + apply HD'.
  - apply discrete_twosided_disp_cat_to_cleaving.
    + exact HD.
    + apply HD'.
  - cbn.
    unfold is_iso_twosided_commute.
    intro ; intros.
    apply HD.
Defined.
