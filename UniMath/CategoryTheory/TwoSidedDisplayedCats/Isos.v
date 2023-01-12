Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.

Local Open Scope cat.

Definition is_iso_twosided_disp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {xy₁ : D x₁ y₁}
           {xy₂ : D x₂ y₂}
           {f : x₁ --> x₂}
           {g : y₁ --> y₂}
           (Hf : is_z_isomorphism f)
           (Hg : is_z_isomorphism g)
           (fg : xy₁ -->[ f ][ g ] xy₂)
  : UU
  := let f_z_iso : z_iso x₁ x₂ := f ,, Hf in
     let g_z_iso : z_iso y₁ y₂ := g ,, Hg in
     ∑ (gf : xy₂
             -->[ inv_from_z_iso f_z_iso ][ inv_from_z_iso g_z_iso ]
             xy₁),
     (fg ;;2 gf
      =
      transportb
        (λ z, _ -->[ z ][ _ ] _)
        (z_iso_inv_after_z_iso f_z_iso)
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (z_iso_inv_after_z_iso g_z_iso)
           (id_two_disp _)))
     ×
     (gf ;;2 fg
      =
      transportb
        (λ z, _ -->[ z ][ _ ] _)
        (z_iso_after_z_iso_inv f_z_iso)
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           (z_iso_after_z_iso_inv g_z_iso)
           (id_two_disp _))).

Definition iso_inv_twosided_disp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {xy₁ : D x₁ y₁}
           {xy₂ : D x₂ y₂}
           {f : x₁ --> x₂}
           {g : y₁ --> y₂}
           {Hf : is_z_isomorphism f}
           {Hg : is_z_isomorphism g}
           {fg : xy₁ -->[ f ][ g ] xy₂}
           (Hfg : is_iso_twosided_disp Hf Hg fg)
  : xy₂
    -->[ inv_from_z_iso (f ,, Hf) ][ inv_from_z_iso (g ,, Hg) ]
    xy₁
  := pr1 Hfg.

Definition inv_after_iso_twosided_disp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {xy₁ : D x₁ y₁}
           {xy₂ : D x₂ y₂}
           {f : x₁ --> x₂}
           {g : y₁ --> y₂}
           {Hf : is_z_isomorphism f}
           {Hg : is_z_isomorphism g}
           {fg : xy₁ -->[ f ][ g ] xy₂}
           (Hfg : is_iso_twosided_disp Hf Hg fg)
  : fg ;;2 iso_inv_twosided_disp Hfg
    =
    transportb
      (λ z, _ -->[ z ][ _ ] _)
      (z_iso_inv_after_z_iso (f ,, Hf))
      (transportb
         (λ z, _ -->[ _ ][ z ] _)
         (z_iso_inv_after_z_iso (g ,, Hg))
         (id_two_disp _))
  := pr12 Hfg.

Definition iso_after_inv_twosided_disp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {xy₁ : D x₁ y₁}
           {xy₂ : D x₂ y₂}
           {f : x₁ --> x₂}
           {g : y₁ --> y₂}
           {Hf : is_z_isomorphism f}
           {Hg : is_z_isomorphism g}
           {fg : xy₁ -->[ f ][ g ] xy₂}
           (Hfg : is_iso_twosided_disp Hf Hg fg)
  : iso_inv_twosided_disp Hfg ;;2 fg
    =
    transportb
      (λ z, _ -->[ z ][ _ ] _)
      (z_iso_after_z_iso_inv (f ,, Hf))
      (transportb
         (λ z, _ -->[ _ ][ z ] _)
         (z_iso_after_z_iso_inv (g ,, Hg))
         (id_two_disp _))
  := pr22 Hfg.

Definition isaprop_is_iso_twosided_disp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {xy₁ : D x₁ y₁}
           {xy₂ : D x₂ y₂}
           {f : x₁ --> x₂}
           {g : y₁ --> y₂}
           (Hf : is_z_isomorphism f)
           (Hg : is_z_isomorphism g)
           (fg : xy₁ -->[ f ][ g ] xy₂)
  : isaprop (is_iso_twosided_disp Hf Hg fg).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use subtypePath.
  {
    intro.
    use isapropdirprod ; apply isaset_disp_mor.
  }
Admitted.

Definition iso_twosided_disp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           (f : z_iso x₁ x₂)
           (g : z_iso y₁ y₂)
           (xy₁ : D x₁ y₁)
           (xy₂ : D x₂ y₂)
  : UU
  := ∑ (fg : xy₁ -->[ f ][ g ] xy₂),
     is_iso_twosided_disp (pr2 f) (pr2 g) fg.

Definition make_iso_twosided_disp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           {f : z_iso x₁ x₂}
           {g : z_iso y₁ y₂}
           {xy₁ : D x₁ y₁}
           {xy₂ : D x₂ y₂}
           (fg : xy₁ -->[ f ][ g ] xy₂)
           (Hfg : is_iso_twosided_disp (pr2 f) (pr2 g) fg)
  : iso_twosided_disp f g xy₁ xy₂
  := fg ,, Hfg.

Definition id_iso_twosided_disp
           {C₁ C₂ : category}
           {D : twosided_disp_cat C₁ C₂}
           {x : C₁}
           {y : C₂}
           (xy : D x y)
  : iso_twosided_disp (identity_z_iso x) (identity_z_iso y) xy xy.
Proof.
  use make_iso_twosided_disp.
  - apply id_two_disp.
  - simple refine (_ ,, _ ,, _).
    + apply id_two_disp.
    + apply id_two_disp_left.
    + apply id_two_disp_left.
Defined.
