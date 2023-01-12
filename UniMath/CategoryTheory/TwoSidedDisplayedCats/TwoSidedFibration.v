Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.

Local Open Scope cat.

Section TwoSidedFibration.
  Context {C₁ C₂ : category}
          (D : twosided_disp_cat C₁ C₂).

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

  Definition twosided_fibration
    : UU
    := ∑ (H₁ : twosided_opcleaving)
         (H₂ : twosided_cleaving),
       is_iso_twosided_commute H₁ H₂.
End TwoSidedFibration.
