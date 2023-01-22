(**********************************************************************************

 Isos in two-sided displayed categories

 We define isomorphisms in two-sided displayed categories.

 Contents
 1. Isos in two-sided displayed categories
 2. Accessors for isos
 3. Derived laws
 4. Being an iso is a proposition
 5. The identity iso

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.

Local Open Scope cat.

(**
 1. Isos in two-sided displayed categories
 *)
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

(**
 2. Accessors for isos
 *)
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

(**
 3. Derived laws
 *)
Definition inv_after_iso_twosided_disp_alt
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
  : id_two_disp _
    =
    transportf
      (λ z, _ -->[ z ][ _ ] _)
      (z_iso_inv_after_z_iso (f ,, Hf))
      (transportf
         (λ z, _ -->[ _ ][ z ] _)
         (z_iso_inv_after_z_iso (g ,, Hg))
         (fg ;;2 iso_inv_twosided_disp Hfg)).
Proof.
  use (@transportf_transpose_right _ (λ z, _ -->[ z ][ _ ] _)).
  use (@transportf_transpose_right _ (λ z, _ -->[ _ ][ z ] _)).
  refine (!_).
  etrans.
  {
    apply inv_after_iso_twosided_disp.
  }
  refine (!_).
  apply twosided_swap_transport.
Qed.

Definition iso_after_inv_twosided_disp_alt
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
  : id_two_disp _
    =
    transportf
      (λ z, _ -->[ z ][ _ ] _)
      (z_iso_after_z_iso_inv (f ,, Hf))
      (transportf
         (λ z, _ -->[ _ ][ z ] _)
         (z_iso_after_z_iso_inv (g ,, Hg))
         (iso_inv_twosided_disp Hfg ;;2 fg)).
Proof.
  use (@transportf_transpose_right _ (λ z, _ -->[ z ][ _ ] _)).
  use (@transportf_transpose_right _ (λ z, _ -->[ _ ][ z ] _)).
  refine (!_).
  etrans.
  {
    apply iso_after_inv_twosided_disp.
  }
  refine (!_).
  apply twosided_swap_transport.
Qed.

(**
 4. Being an iso is a proposition
 *)
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
  etrans.
  {
    apply id_two_disp_right_alt.
  }
  refine (twosided_prod_transport _ _ _ @ _).
  etrans.
  {
    do 2 apply maponpaths.
    exact (inv_after_iso_twosided_disp_alt φ₂).
  }
  rewrite two_disp_post_whisker_left.
  rewrite two_disp_post_whisker_right.
  etrans.
  {
    apply maponpaths.
    apply twosided_prod_transport.
  }
  rewrite transport_f_f.
  rewrite assoc_two_disp.
  unfold transportb.
  etrans.
  {
    apply maponpaths.
    apply twosided_prod_transport.
  }
  rewrite transport_f_f.
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply (iso_after_inv_twosided_disp φ₁).
  }
  unfold transportb.
  rewrite two_disp_pre_whisker_left.
  rewrite two_disp_pre_whisker_right.
  etrans.
  {
    apply maponpaths.
    apply twosided_prod_transport.
  }
  rewrite transport_f_f.
  rewrite id_two_disp_left.
  unfold transportb.
  etrans.
  {
    apply maponpaths.
    apply twosided_prod_transport.
  }
  rewrite transport_f_f.
  unfold iso_inv_twosided_disp.
  use (@transportf_set
         _
         (λ z, xy₂ -->[ pr1 z ][ dirprod_pr2 z ] xy₁)
         (_ ,, _)).
  apply isasetdirprod ; apply homset_property.
Qed.

(**
 5. The identity iso
 *)
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
