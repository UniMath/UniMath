(**********************************************************************************

 Two-sided displayed categories

 In this file, we define two-sided displayed categories. These are rather similar
 to displayed categories, but they are displayed over 2 categories instead of
 just one.

 More specifically, given two categories `C₁` and `C₂` a two-sided displayed
 category `D` over `C₁` and `C₂` has displayed objects `xy` over every `x : C₁`
 and `y : C₂`. For morphisms `f : C₁ ⟦ x₁ , x₂ ⟧`, `g : C₂ ⟦ y₁ , y₂ ⟧` and
 displayed objects `xy₁ : D x₁ y₁` and `xy₂ : D x₂ y₂`, we have a set of
 displayed morhisms.

 Contents
 1.1. Definition of two-sided displayed categories
 1.2. Derived laws
 2. Two-sided displayed categories are displayed categories over the product

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Local Open Scope cat.

Definition total2_paths_2_b
           {X Y : UU}
           (Z : X → Y → UU)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           {y₁ y₂ : Y}
           (q : y₁ = y₂)
           {z₁ : Z x₁ y₁}
           {z₂ : Z x₂ y₂}
           (r : z₁
                =
                transportb
                  (λ w, Z w _)
                  p
                  (transportb
                     (λ w, Z _ w)
                     q
                     z₂))
  : (x₁ ,, y₁ ,, z₁ : ∑ (x : X) (y : Y), Z x y)
    =
    (x₂ ,, y₂ ,, z₂ : ∑ (x : X) (y : Y), Z x y).
Proof.
  induction p, q ; cbn in *.
  induction r.
  apply idpath.
Defined.

Definition transportb_dirprodeq
           {X Y : UU}
           (Z : X → Y → UU)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           {y₁ y₂ : Y}
           (q : y₁ = y₂)
           (z : Z x₂ y₂)
  : transportb
      (λ (w : X × Y), Z (pr1 w) (pr2 w))
      (dirprodeq _ _ (x₁ ,, y₁) (x₂ ,, y₂) p q)
      z
    =
    transportb
      (λ w, Z w _)
      p
      (transportb
         (λ w, Z _ w)
         q
         z).
Proof.
  induction p, q.
  apply idpath.
Defined.

Definition transportb_dirprodeq'
           {X Y : UU}
           (Z : X × Y → UU)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           {y₁ y₂ : Y}
           (q : y₁ = y₂)
           (z : Z (x₂ ,, y₂))
  : transportb
      (λ (w : X × Y), Z w)
      (dirprodeq _ _ (x₁ ,, y₁) (x₂ ,, y₂) p q)
      z
    =
    transportb
      (λ w, Z (w ,, _))
      p
      (transportb
         (λ w, Z (_ ,, w))
         q
         z).
Proof.
  induction p, q.
  apply idpath.
Defined.

(** * 1.1. Definition of two-sided displayed categories *)
Definition twosided_disp_cat_ob_mor
           (C₁ C₂ : precategory_ob_mor)
    : UU
    := ∑ (D : C₁ → C₂ → UU),
       ∏ (x₁ x₂ : C₁)
         (y₁ y₂ : C₂),
       D x₁ y₁
       →
       D x₂ y₂
       →
       x₁ --> x₂
       →
       y₁ --> y₂
       →
       UU.

Definition twosided_disp_cat_ob_mor_to_ob
           {C₁ C₂ : precategory_ob_mor}
           {D : twosided_disp_cat_ob_mor C₁ C₂}
           (x : C₁)
           (y : C₂)
  : UU
  := pr1 D x y.

Coercion twosided_disp_cat_ob_mor_to_ob : twosided_disp_cat_ob_mor >-> Funclass.

Definition twosided_disp_cat_ob_mor_to_mor
           {C₁ C₂ : precategory_ob_mor}
           {D : twosided_disp_cat_ob_mor C₁ C₂}
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           (xy₁ : D x₁ y₁)
           (xy₂ : D x₂ y₂)
           (f : x₁ --> x₂)
           (g : y₁ --> y₂)
  : UU
  := pr2 D x₁ x₂ y₁ y₂ xy₁ xy₂ f g.

Notation "xy₁ -->[ f ][ g ] xy₂"
  := (twosided_disp_cat_ob_mor_to_mor xy₁ xy₂ f g)
       (at level 50, left associativity, xy₂ at next level).

Definition twosided_disp_cat_id
           {C₁ C₂ : precategory_data}
           (D : twosided_disp_cat_ob_mor C₁ C₂)
  : UU
  := ∏ (x : C₁)
       (y : C₂)
       (xy : D x y),
     xy -->[ identity x ][ identity y ] xy.

Definition twosided_disp_cat_comp
           {C₁ C₂ : precategory_data}
           (D : twosided_disp_cat_ob_mor C₁ C₂)
  : UU
  := ∏ (x₁ x₂ x₃ : C₁)
       (y₁ y₂ y₃ : C₂)
       (xy₁ : D x₁ y₁)
       (xy₂ : D x₂ y₂)
       (xy₃ : D x₃ y₃)
       (f₁ : x₁ --> x₂)
       (f₂ : x₂ --> x₃)
       (g₁ : y₁ --> y₂)
       (g₂ : y₂ --> y₃),
    xy₁ -->[ f₁ ][ g₁ ] xy₂
    →
    xy₂ -->[ f₂ ][ g₂ ] xy₃
    →
    xy₁ -->[ f₁ · f₂ ][ g₁ · g₂ ] xy₃.

Definition twosided_disp_cat_id_comp
           {C₁ C₂ : precategory_data}
           (D : twosided_disp_cat_ob_mor C₁ C₂)
  : UU
  := twosided_disp_cat_id D × twosided_disp_cat_comp D.

Definition twosided_disp_cat_data
           {C₁ C₂ : precategory_data}
  : UU
  := ∑ (D : twosided_disp_cat_ob_mor C₁ C₂),
     twosided_disp_cat_id_comp D.

#[reversible=no] Coercion twosided_disp_cat_data_to_twosided_disp_cat_ob_mor
         {C₁ C₂ : precategory_data}
         (D : twosided_disp_cat_data)
  : twosided_disp_cat_ob_mor C₁ C₂
  := pr1 D.

Definition id_two_disp
           {C₁ C₂ : precategory_data}
           {D : twosided_disp_cat_data}
           {x : C₁}
           {y : C₂}
           (xy : D x y)
  : xy -->[ identity x ][ identity y ] xy
  := pr12 D x y xy.

Definition comp_two_disp
           {C₁ C₂ : precategory_data}
           {D : twosided_disp_cat_data}
           {x₁ x₂ x₃ : C₁}
           {y₁ y₂ y₃ : C₂}
           {xy₁ : D x₁ y₁}
           {xy₂ : D x₂ y₂}
           {xy₃ : D x₃ y₃}
           {f₁ : x₁ --> x₂}
           {f₂ : x₂ --> x₃}
           {g₁ : y₁ --> y₂}
           {g₂ : y₂ --> y₃}
           (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
           (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
  : xy₁ -->[ f₁ · f₂ ][ g₁ · g₂ ] xy₃
  := pr22 D _ _ _ _ _ _ _ _ _ _ _ _ _ fg₁ fg₂.

Notation "fg₁ ;;2 fg₂"
  := (comp_two_disp fg₁ fg₂)
       (at level 50, left associativity, format "fg₁  ;;2  fg₂").

Section TwoSidedDispCat.
  Context {C₁ C₂ : category}.

  Definition transportf_disp_mor2
             {D : twosided_disp_cat_data}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f₁ f₂ : x₁ --> x₂}
             (p : f₁ = f₂)
             {g₁ g₂ : y₁ --> y₂}
             (q : g₁ = g₂)
             (fg : xy₁ -->[ f₁ ][ g₁ ] xy₂)
    : xy₁ -->[ f₂ ][ g₂ ] xy₂
    := transportf
         (λ z, _ -->[ z ][ _ ] _)
         p
         (transportf
            (λ z, _ -->[ _ ][ z ] _)
            q
            fg).

  Definition transportb_disp_mor2
             {D : twosided_disp_cat_data}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f₁ f₂ : x₁ --> x₂}
             (p : f₁ = f₂)
             {g₁ g₂ : y₁ --> y₂}
             (q : g₁ = g₂)
             (fg : xy₁ -->[ f₂ ][ g₂ ] xy₂)
    : xy₁ -->[ f₁ ][ g₁ ] xy₂
    := transportf_disp_mor2 (!p) (!q) fg.

  Proposition transport_f_f_disp_mor2
              {D : twosided_disp_cat_data}
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {xy₁ : D x₁ y₁}
              {xy₂ : D x₂ y₂}
              {f₁ f₂ f₃ : x₁ --> x₂}
              (p₁ : f₁ = f₂) (p₂ : f₂ = f₃)
              {g₁ g₂ g₃ : y₁ --> y₂}
              (q₁ : g₁ = g₂) (q₂ : g₂ = g₃)
              (fg : xy₁ -->[ f₁ ][ g₁ ] xy₂)
    : transportf_disp_mor2
        p₂ q₂
        (transportf_disp_mor2
           p₁ q₁
           fg)
      =
      transportf_disp_mor2
        (p₁ @ p₂) (q₁ @ q₂)
        fg.
  Proof.
    induction p₁, p₂, q₁, q₂ ; cbn.
    apply idpath.
  Qed.

  Proposition transportfb_disp_mor2
              {D : twosided_disp_cat_data}
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {xy₁ : D x₁ y₁}
              {xy₂ : D x₂ y₂}
              {f₁ f₂ : x₁ --> x₂}
              (p : f₁ = f₂)
              {g₁ g₂ : y₁ --> y₂}
              (q : g₁ = g₂)
              (fg : xy₁ -->[ f₂ ][ g₂ ] xy₂)
    : transportf_disp_mor2 p q (transportb_disp_mor2 p q fg) = fg.
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Proposition transport_b_b_disp_mor2
              {D : twosided_disp_cat_data}
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {xy₁ : D x₁ y₁}
              {xy₂ : D x₂ y₂}
              {f₁ f₂ f₃ : x₁ --> x₂}
              (p₁ : f₂ = f₁) (p₂ : f₃ = f₂)
              {g₁ g₂ g₃ : y₁ --> y₂}
              (q₁ : g₂ = g₁) (q₂ : g₃ = g₂)
              (fg : xy₁ -->[ f₁ ][ g₁ ] xy₂)
    : transportb_disp_mor2
        p₂ q₂
        (transportb_disp_mor2
           p₁ q₁
           fg)
      =
      transportb_disp_mor2
        (p₂ @ p₁) (q₂ @ q₁)
        fg.
  Proof.
    induction p₁, p₂, q₁, q₂ ; cbn.
    apply idpath.
  Qed.

  Proposition transportbf_disp_mor2
              {D : twosided_disp_cat_data}
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {xy₁ : D x₁ y₁}
              {xy₂ : D x₂ y₂}
              {f₁ f₂ : x₁ --> x₂}
              (p : f₁ = f₂)
              {g₁ g₂ : y₁ --> y₂}
              (q : g₁ = g₂)
              (fg : xy₁ -->[ f₁ ][ g₁ ] xy₂)
    : transportb_disp_mor2 p q (transportf_disp_mor2 p q fg) = fg.
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Definition id_two_disp_left_law
             (D : twosided_disp_cat_data)
    : UU
    := ∏ (x₁ x₂ : C₁)
         (y₁ y₂ : C₂)
         (xy₁ : D x₁ y₁)
         (xy₂ : D x₂ y₂)
         (f : x₁ --> x₂)
         (g : y₁ --> y₂)
         (fg : xy₁ -->[ f ][ g ] xy₂),
       id_two_disp xy₁ ;;2 fg
       =
       transportb_disp_mor2
         (id_left _)
         (id_left _)
         fg.

  Definition id_two_disp_right_law
             (D : twosided_disp_cat_data)
    : UU
    := ∏ (x₁ x₂ : C₁)
         (y₁ y₂ : C₂)
         (xy₁ : D x₁ y₁)
         (xy₂ : D x₂ y₂)
         (f : x₁ --> x₂)
         (g : y₁ --> y₂)
         (fg : xy₁ -->[ f ][ g ] xy₂),
       fg ;;2 id_two_disp xy₂
       =
       transportb_disp_mor2
         (id_right _)
         (id_right _)
         fg.

  Definition assoc_two_disp_law
             (D : twosided_disp_cat_data)
    : UU
    := ∏ (x₁ x₂ x₃ x₄ : C₁)
         (y₁ y₂ y₃ y₄ : C₂)
         (xy₁ : D x₁ y₁)
         (xy₂ : D x₂ y₂)
         (xy₃ : D x₃ y₃)
         (xy₄ : D x₄ y₄)
         (f₁ : x₁ --> x₂)
         (f₂ : x₂ --> x₃)
         (f₃ : x₃ --> x₄)
         (g₁ : y₁ --> y₂)
         (g₂ : y₂ --> y₃)
         (g₃ : y₃ --> y₄)
         (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
         (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
         (fg₃ : xy₃ -->[ f₃ ][ g₃ ] xy₄),
       (fg₁ ;;2 (fg₂ ;;2 fg₃))
       =
       transportb_disp_mor2
         (assoc _ _ _)
         (assoc _ _ _)
         ((fg₁ ;;2 fg₂) ;;2 fg₃).

  Definition isaset_disp_mor_law
             (D : twosided_disp_cat_data)
    : UU
    := ∏ (x₁ x₂ : C₁)
         (y₁ y₂ : C₂)
         (xy₁ : D x₁ y₁)
         (xy₂ : D x₂ y₂)
         (f : x₁ --> x₂)
         (g : y₁ --> y₂),
       isaset (xy₁ -->[ f ][ g ] xy₂).

  Definition twosided_disp_cat_axioms
             (D : twosided_disp_cat_data)
    : UU
    := id_two_disp_left_law D
       ×
       id_two_disp_right_law D
       ×
       assoc_two_disp_law D
       ×
       isaset_disp_mor_law D.

  Definition isaprop_twosided_disp_cat_axioms
             (D : twosided_disp_cat_data)
    : isaprop (twosided_disp_cat_axioms D).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    repeat (use pathsdirprod).
    - do 9 (use funextsec ; intro).
      apply (pr222 φ₂).
    - do 9 (use funextsec ; intro).
      apply (pr222 φ₂).
    - do 21 (use funextsec ; intro).
      apply (pr222 φ₂).
    - do 8 (use funextsec ; intro).
      apply isapropisaset.
  Qed.

  Definition twosided_disp_cat
    : UU
    := ∑ (D : twosided_disp_cat_data),
       twosided_disp_cat_axioms D.

  #[reversible] Coercion twosided_disp_cat_to_twosided_disp_cat_data
           (D : twosided_disp_cat)
    : twosided_disp_cat_data
    := pr1 D.

  Definition id_two_disp_left
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : id_two_disp xy₁ ;;2 fg
      =
      transportb_disp_mor2
        (id_left _)
        (id_left _)
        fg.
  Proof.
    exact (pr12 D _ _ _ _ _ _ _ _ fg).
  Defined.

  Definition id_two_disp_right
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : fg ;;2 id_two_disp xy₂
      =
      transportb_disp_mor2
        (id_right _)
        (id_right _)
        fg.
  Proof.
    exact (pr122 D _ _ _ _ _ _ _ _ fg).
  Defined.

  Definition assoc_two_disp
             {D : twosided_disp_cat}
             {x₁ x₂ x₃ x₄ : C₁}
             {y₁ y₂ y₃ y₄ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {xy₃ : D x₃ y₃}
             {xy₄ : D x₄ y₄}
             {f₁ : x₁ --> x₂}
             {f₂ : x₂ --> x₃}
             {f₃ : x₃ --> x₄}
             {g₁ : y₁ --> y₂}
             {g₂ : y₂ --> y₃}
             {g₃ : y₃ --> y₄}
             (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
             (fg₃ : xy₃ -->[ f₃ ][ g₃ ] xy₄)
    : (fg₁ ;;2 (fg₂ ;;2 fg₃))
      =
      transportb_disp_mor2
        (assoc _ _ _)
        (assoc _ _ _)
        ((fg₁ ;;2 fg₂) ;;2 fg₃).
  Proof.
    exact (pr1 (pr222 D) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fg₁ fg₂ fg₃).
  Defined.

  Definition isaset_disp_mor
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             (xy₁ : D x₁ y₁)
             (xy₂ : D x₂ y₂)
             (f : x₁ --> x₂)
             (g : y₁ --> y₂)
    : isaset (xy₁ -->[ f ][ g ] xy₂).
  Proof.
    exact (pr2 (pr222 D) _ _ _ _ xy₁ xy₂ f g).
  Defined.

  (**
   1.2. Derived laws
   *)
  Definition twosided_swap_transport
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ g₂ : y₁ --> y₂}
             (fg : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (p : f₁ = f₂)
             (q : g₁ = g₂)
    : transportf
        (λ z, _ -->[ _ ][ z ] _)
        q
        (transportf
           (λ z, _ -->[ z ][ _ ] _)
           p
           fg)
      =
      transportf
        (λ z, _ -->[ z ][ _ ] _)
        p
        (transportf
           (λ z, _ -->[ _ ][ z ] _)
           q
           fg).
  Proof.
    induction p, q.
    apply idpath.
  Qed.

  Definition twosided_prod_transport
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ g₂ : y₁ --> y₂}
             (fg : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (p : f₁ = f₂)
             (q : g₁ = g₂)
    : transportf
        (λ z, _ -->[ z ][ _ ] _)
        p
        (transportf
           (λ z, _ -->[ _ ][ z ] _)
           q
           fg)
      =
      transportf
        (λ z, _ -->[ pr1 z ][ pr2 z ] _)
        (pathsdirprod p q)
        fg.
  Proof.
    induction p ; induction q.
    apply idpath.
  Qed.

  Definition twosided_prod_transport_alt
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ g₂ : y₁ --> y₂}
             (fg : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (p : f₁ = f₂)
             (q : g₁ = g₂)
    : transportf
        (λ z, _ -->[ _ ][ z ] _)
        q
        (transportf
           (λ z, _ -->[ z ][ _ ] _)
           p
           fg)
      =
      transportf
        (λ z, _ -->[ pr1 z ][ pr2 z ] _)
        (pathsdirprod p q)
        fg.
  Proof.
    induction p ; induction q.
    apply idpath.
  Qed.

  Definition twosided_prod_transportb
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ g₂ : y₁ --> y₂}
             (fg : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (p : f₂ = f₁)
             (q : g₂ = g₁)
    : transportb
        (λ z, _ -->[ z ][ _ ] _)
        p
        (transportb
           (λ z, _ -->[ _ ][ z ] _)
           q
           fg)
      =
      transportb
        (λ z, _ -->[ pr1 z ][ pr2 z ] _)
        (pathsdirprod p q)
        fg.
  Proof.
    induction p ; induction q.
    apply idpath.
  Qed.

  Definition twosided_prod_transportb_alt
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f₁ f₂ : x₁ --> x₂}
             {g₁ g₂ : y₁ --> y₂}
             (fg : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (p : f₂ = f₁)
             (q : g₂ = g₁)
    : transportb
        (λ z, _ -->[ _ ][ z ] _)
        q
        (transportb
           (λ z, _ -->[ z ][ _ ] _)
           p
           fg)
      =
      transportb
        (λ z, _ -->[ pr1 z ][ pr2 z ] _)
        (pathsdirprod p q)
        fg.
  Proof.
    induction p ; induction q.
    apply idpath.
  Qed.

  Definition id_two_disp_left_alt
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : fg
      =
      transportf_disp_mor2
        (id_left _)
        (id_left _)
        (id_two_disp xy₁ ;;2 fg).
  Proof.
    rewrite id_two_disp_left.
    rewrite transportfb_disp_mor2.
    apply idpath.
  Qed.

  Definition id_two_disp_right_alt
             {D : twosided_disp_cat}
             {x₁ x₂ : C₁}
             {y₁ y₂ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {f : x₁ --> x₂}
             {g : y₁ --> y₂}
             (fg : xy₁ -->[ f ][ g ] xy₂)
    : fg
      =
      transportf_disp_mor2
        (id_right _)
        (id_right _)
        (fg ;;2 id_two_disp xy₂).
  Proof.
    rewrite id_two_disp_right.
    rewrite transportfb_disp_mor2.
    apply idpath.
  Qed.

  Definition assoc_two_disp_alt
             {D : twosided_disp_cat}
             {x₁ x₂ x₃ x₄ : C₁}
             {y₁ y₂ y₃ y₄ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {xy₃ : D x₃ y₃}
             {xy₄ : D x₄ y₄}
             {f₁ : x₁ --> x₂}
             {f₂ : x₂ --> x₃}
             {f₃ : x₃ --> x₄}
             {g₁ : y₁ --> y₂}
             {g₂ : y₂ --> y₃}
             {g₃ : y₃ --> y₄}
             (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
             (fg₃ : xy₃ -->[ f₃ ][ g₃ ] xy₄)
    : ((fg₁ ;;2 fg₂) ;;2 fg₃)
      =
      transportf_disp_mor2
        (assoc _ _ _)
        (assoc _ _ _)
        (fg₁ ;;2 (fg₂ ;;2 fg₃)).
  Proof.
    rewrite assoc_two_disp.
    rewrite transportfb_disp_mor2.
    apply idpath.
  Qed.

  Definition two_disp_post_whisker_left
             {D : twosided_disp_cat}
             {x₁ x₂ x₃ : C₁}
             {y₁ y₂ y₃ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {xy₃ : D x₃ y₃}
             {f₁ : x₁ --> x₂}
             {f₂ f₂' : x₂ --> x₃}
             (p : f₂' = f₂)
             {g₁ : y₁ --> y₂}
             {g₂ : y₂ --> y₃}
             (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (fg₂ : xy₂ -->[ f₂' ][ g₂ ] xy₃)
    : fg₁ ;;2 transportf (λ z, _ -->[ z ][ _ ] _) p fg₂
      =
      transportf
        (λ z, _ -->[ z ][ _ ] _)
        (maponpaths (λ z, _ · z) p)
        (fg₁ ;;2 fg₂).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Definition two_disp_post_whisker_right
             {D : twosided_disp_cat}
             {x₁ x₂ x₃ : C₁}
             {y₁ y₂ y₃ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {xy₃ : D x₃ y₃}
             {f₁ : x₁ --> x₂}
             {f₂ : x₂ --> x₃}
             {g₁ : y₁ --> y₂}
             {g₂ g₂' : y₂ --> y₃}
             (p : g₂' = g₂)
             (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (fg₂ : xy₂ -->[ f₂ ][ g₂' ] xy₃)
    : fg₁ ;;2 transportf (λ z, _ -->[ _ ][ z ] _) p fg₂
      =
      transportf
        (λ z, _ -->[ _ ][ z ] _)
        (maponpaths (λ z, _ · z) p)
        (fg₁ ;;2 fg₂).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Definition two_disp_post_whisker_f
             {D : twosided_disp_cat}
             {x₁ x₂ x₃ : C₁}
             {y₁ y₂ y₃ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {xy₃ : D x₃ y₃}
             {f₁ : x₁ --> x₂}
             {f₂ f₂' : x₂ --> x₃}
             (p : f₂' = f₂)
             {g₁ : y₁ --> y₂}
             {g₂ g₂' : y₂ --> y₃}
             (q : g₂' = g₂)
             (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (fg₂ : xy₂ -->[ f₂' ][ g₂' ] xy₃)
    : fg₁ ;;2 transportf_disp_mor2 p q fg₂
      =
      transportf_disp_mor2
        (maponpaths (λ z, _ · z) p)
        (maponpaths (λ z, _ · z) q)
        (fg₁ ;;2 fg₂).
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Definition two_disp_post_whisker_b
             {D : twosided_disp_cat}
             {x₁ x₂ x₃ : C₁}
             {y₁ y₂ y₃ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {xy₃ : D x₃ y₃}
             {f₁ : x₁ --> x₂}
             {f₂ f₂' : x₂ --> x₃}
             (p : f₂ = f₂')
             {g₁ : y₁ --> y₂}
             {g₂ g₂' : y₂ --> y₃}
             (q : g₂ = g₂')
             (fg₁ : xy₁ -->[ f₁ ][ g₁ ] xy₂)
             (fg₂ : xy₂ -->[ f₂' ][ g₂' ] xy₃)
    : fg₁ ;;2 transportb_disp_mor2 p q fg₂
      =
      transportb_disp_mor2
        (maponpaths (λ z, _ · z) p)
        (maponpaths (λ z, _ · z) q)
        (fg₁ ;;2 fg₂).
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Definition two_disp_pre_whisker_left
             {D : twosided_disp_cat}
             {x₁ x₂ x₃ : C₁}
             {y₁ y₂ y₃ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {xy₃ : D x₃ y₃}
             {f₁ f₁' : x₁ --> x₂}
             (p : f₁' = f₁)
             {f₂ : x₂ --> x₃}
             {g₁ : y₁ --> y₂}
             {g₂ : y₂ --> y₃}
             (fg₁ : xy₁ -->[ f₁' ][ g₁ ] xy₂)
             (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
    : transportf (λ z, _ -->[ z ][ _ ] _) p fg₁ ;;2 fg₂
      =
      transportf
        (λ z, _ -->[ z ][ _ ] _)
        (maponpaths (λ z, z · _) p)
        (fg₁ ;;2 fg₂).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Definition two_disp_pre_whisker_right
             {D : twosided_disp_cat}
             {x₁ x₂ x₃ : C₁}
             {y₁ y₂ y₃ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {xy₃ : D x₃ y₃}
             {f₁ : x₁ --> x₂}
             {f₂ : x₂ --> x₃}
             {g₁ g₁' : y₁ --> y₂}
             (p : g₁' = g₁)
             {g₂ : y₂ --> y₃}
             (fg₁ : xy₁ -->[ f₁ ][ g₁' ] xy₂)
             (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
    : transportf (λ z, _ -->[ _ ][ z ] _) p fg₁ ;;2 fg₂
      =
      transportf
        (λ z, _ -->[ _ ][ z ] _)
        (maponpaths (λ z, z · _) p)
        (fg₁ ;;2 fg₂).
  Proof.
    induction p ; cbn.
    apply idpath.
  Qed.

  Definition two_disp_pre_whisker_f
             {D : twosided_disp_cat}
             {x₁ x₂ x₃ : C₁}
             {y₁ y₂ y₃ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {xy₃ : D x₃ y₃}
             {f₁ f₁' : x₁ --> x₂}
             (p : f₁' = f₁)
             {f₂ : x₂ --> x₃}
             {g₁ g₁' : y₁ --> y₂}
             (q : g₁' = g₁)
             {g₂ : y₂ --> y₃}
             (fg₁ : xy₁ -->[ f₁' ][ g₁' ] xy₂)
             (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
    : transportf_disp_mor2 p q fg₁ ;;2 fg₂
      =
      transportf_disp_mor2
        (maponpaths (λ z, z · _) p)
        (maponpaths (λ z, z · _) q)
        (fg₁ ;;2 fg₂).
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Definition two_disp_pre_whisker_b
             {D : twosided_disp_cat}
             {x₁ x₂ x₃ : C₁}
             {y₁ y₂ y₃ : C₂}
             {xy₁ : D x₁ y₁}
             {xy₂ : D x₂ y₂}
             {xy₃ : D x₃ y₃}
             {f₁ f₁' : x₁ --> x₂}
             (p : f₁ = f₁')
             {f₂ : x₂ --> x₃}
             {g₁ g₁' : y₁ --> y₂}
             (q : g₁ = g₁')
             {g₂ : y₂ --> y₃}
             (fg₁ : xy₁ -->[ f₁' ][ g₁' ] xy₂)
             (fg₂ : xy₂ -->[ f₂ ][ g₂ ] xy₃)
    : transportb_disp_mor2 p q fg₁ ;;2 fg₂
      =
      transportb_disp_mor2
        (maponpaths (λ z, z · _) p)
        (maponpaths (λ z, z · _) q)
        (fg₁ ;;2 fg₂).
  Proof.
    induction p, q ; cbn.
    apply idpath.
  Qed.

  Proposition transportf_disp_mor2_idpath
              {D : twosided_disp_cat}
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {xy₁ : D x₁ y₁}
              {xy₂ : D x₂ y₂}
              {f : x₁ --> x₂}
              (p : f = f)
              {g : y₁ --> y₂}
              (q : g = g)
              (fg : xy₁ -->[ f ][ g ] xy₂)
    : transportf_disp_mor2 p q fg = fg.
  Proof.
    assert (p = idpath _) as h₁.
    {
      apply homset_property.
    }
    assert (q = idpath _) as h₂.
    {
      apply homset_property.
    }
    rewrite h₁, h₂ ; cbn.
    apply idpath.
  Qed.

  Proposition transportb_disp_mor2_idpath
              {D : twosided_disp_cat}
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {xy₁ : D x₁ y₁}
              {xy₂ : D x₂ y₂}
              {f : x₁ --> x₂}
              (p : f = f)
              {g : y₁ --> y₂}
              (q : g = g)
              (fg : xy₁ -->[ f ][ g ] xy₂)
    : transportb_disp_mor2 p q fg = fg.
  Proof.
    apply transportf_disp_mor2_idpath.
  Qed.

  Proposition transportf_disp_mor2_eq
              {D : twosided_disp_cat}
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {xy₁ : D x₁ y₁}
              {xy₂ : D x₂ y₂}
              {f f' : x₁ --> x₂}
              {p p' : f = f'}
              {g g' : y₁ --> y₂}
              {q q' : g = g'}
              {fg fg' : xy₁ -->[ f ][ g ] xy₂}
              (s : fg = fg')
    : transportf_disp_mor2 p q fg = transportf_disp_mor2 p' q' fg'.
  Proof.
    assert (p = p') as h₁.
    {
      apply homset_property.
    }
    assert (q = q') as h₂.
    {
      apply homset_property.
    }
    rewrite h₁, h₂, s.
    apply idpath.
  Qed.

  Proposition transportb_disp_mor2_eq
              {D : twosided_disp_cat}
              {x₁ x₂ : C₁}
              {y₁ y₂ : C₂}
              {xy₁ : D x₁ y₁}
              {xy₂ : D x₂ y₂}
              {f f' : x₁ --> x₂}
              {p p' : f' = f}
              {g g' : y₁ --> y₂}
              {q q' : g' = g}
              {fg fg' : xy₁ -->[ f ][ g ] xy₂}
              (s : fg = fg')
    : transportb_disp_mor2 p q fg = transportb_disp_mor2 p' q' fg'.
  Proof.
    assert (p = p') as h₁.
    {
      apply homset_property.
    }
    assert (q = q') as h₂.
    {
      apply homset_property.
    }
    rewrite h₁, h₂, s.
    apply idpath.
  Qed.
End TwoSidedDispCat.

Arguments twosided_disp_cat_ob_mor _ _ : clear implicits.
Arguments twosided_disp_cat_data _ _ : clear implicits.
Arguments twosided_disp_cat _ _ : clear implicits.

Notation "'trf₂' fg" := (transportf_disp_mor2 _ _ fg) (at level 50, only printing).
Notation "'trb₂' fg" := (transportb_disp_mor2 _ _ fg) (at level 50, only printing).

(**
 2. Two-sided displayed categories are displayed categories over the product
 *)
Section TwoSidedDispCatVersusDispCat.
  Context (C₁ C₂ : category).

  Definition twosided_disp_cat_to_disp_cat_ob_mor
             (D : twosided_disp_cat C₁ C₂)
    : disp_cat_ob_mor (category_binproduct C₁ C₂).
  Proof.
    simple refine (_ ,, _).
    - exact (λ xy, D (pr1 xy) (pr2 xy)).
    - exact (λ xy₁ xy₂ z₁ z₂ fg, z₁ -->[ pr1 fg ][ pr2 fg ] z₂).
  Defined.

  Definition twosided_disp_cat_to_disp_cat_id_comp
             (D : twosided_disp_cat C₁ C₂)
    : disp_cat_id_comp
        (category_binproduct C₁ C₂)
        (twosided_disp_cat_to_disp_cat_ob_mor D).
  Proof.
    simple refine (_ ,, _).
    - exact (λ xy z, id_two_disp z).
    - exact (λ xy₁ xy₂ xy₃ fg₁ fg₂ z₁ z₂ z₃ h₁ h₂,
             h₁ ;;2 h₂).
  Defined.

  Definition twosided_disp_cat_to_disp_cat_data
             (D : twosided_disp_cat C₁ C₂)
    : disp_cat_data (category_binproduct C₁ C₂).
  Proof.
    simple refine (_ ,, _).
    - exact (twosided_disp_cat_to_disp_cat_ob_mor D).
    - exact (twosided_disp_cat_to_disp_cat_id_comp D).
  Defined.

  Definition twosided_disp_cat_to_disp_cat_axioms
             (D : twosided_disp_cat C₁ C₂)
    : disp_cat_axioms
        (category_binproduct C₁ C₂)
        (twosided_disp_cat_to_disp_cat_data D).
  Proof.
    repeat split.
    - intros x y f g xx yy ; cbn in *.
      refine (id_two_disp_left _ @ _).
      refine (!_).
      apply transportb_dirprodeq.
    - intros x y f g xx yy ; cbn in *.
      refine (id_two_disp_right _ @ _).
      refine (!_).
      apply transportb_dirprodeq.
    - intros w x y z f g h ww xx yy zz ff gg hh ; cbn in *.
      refine (assoc_two_disp _ _ _ @ _).
      refine (!_).
      apply transportb_dirprodeq.
    - intros x y f xx yy ; cbn in *.
      apply isaset_disp_mor.
  Qed.

  Definition twosided_disp_cat_to_disp_cat
             (D : twosided_disp_cat C₁ C₂)
    : disp_cat (category_binproduct C₁ C₂).
  Proof.
    simple refine (_ ,, _).
    - exact (twosided_disp_cat_to_disp_cat_data D).
    - exact (twosided_disp_cat_to_disp_cat_axioms D).
  Defined.

  Definition disp_cat_to_twosided_disp_cat_ob_mor
             (D : disp_cat (category_binproduct C₁ C₂))
    : twosided_disp_cat_ob_mor C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x y, D (x ,, y)).
    - exact (λ x₁ x₂ y₁ y₂ xy₁ xy₂ f g, xy₁ -->[ f ,, g ] xy₂).
  Defined.

  Definition disp_cat_to_twosided_disp_cat_id_comp
             (D : disp_cat (category_binproduct C₁ C₂))
    : twosided_disp_cat_id_comp
        (disp_cat_to_twosided_disp_cat_ob_mor D).
  Proof.
    split.
    - exact (λ x y xy, id_disp _).
    - refine (λ x₁ x₂ x₃ y₁ y₂ y₃ xy₁ xy₂ xy₃ f₁ f₂ g₁ g₂ fg₁ fg₂,
              _).
      cbn in *.
      exact (fg₁ ;; fg₂)%mor_disp.
  Defined.

  Definition disp_cat_to_twosided_disp_cat_data
             (D : disp_cat (category_binproduct C₁ C₂))
    : twosided_disp_cat_data C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (disp_cat_to_twosided_disp_cat_ob_mor D).
    - exact (disp_cat_to_twosided_disp_cat_id_comp D).
  Defined.

  Definition disp_cat_to_twosided_disp_cat_axioms
             (D : disp_cat (category_binproduct C₁ C₂))
    : twosided_disp_cat_axioms (disp_cat_to_twosided_disp_cat_data D).
  Proof.
    repeat split.
    - intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg ; cbn in *.
      refine (id_left_disp fg @ _).
      apply transportb_dirprodeq'.
    - intros x₁ x₂ y₁ y₂ xy₁ xy₂ f g fg ; cbn in *.
      refine (id_right_disp fg @ _).
      apply transportb_dirprodeq'.
    - intros x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ xy₁ xy₂ xy₃ xy₄ f₁ f₂ f₃ g₁ g₂ g₃ fg₁ fg₂ fg₃.
      cbn in *.
      refine (assoc_disp fg₁ fg₂ fg₃ @ _).
      apply transportb_dirprodeq'.
    - intro ; intros.
      apply D.
  Qed.

  Definition disp_cat_to_twosided_disp_cat
             (D : disp_cat (category_binproduct C₁ C₂))
    : twosided_disp_cat C₁ C₂.
  Proof.
    simple refine (_ ,, _).
    - exact (disp_cat_to_twosided_disp_cat_data D).
    - exact (disp_cat_to_twosided_disp_cat_axioms D).
  Defined.

  Definition two_sided_disp_cat_weq_disp_cat_inv_left
             (D : twosided_disp_cat C₁ C₂)
    : disp_cat_to_twosided_disp_cat (twosided_disp_cat_to_disp_cat D)
      =
      D.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_twosided_disp_cat_axioms.
    }
    apply idpath.
  Qed.

  Definition two_sided_disp_cat_weq_disp_cat_inv_right
             (D : disp_cat (category_binproduct C₁ C₂))
    : twosided_disp_cat_to_disp_cat (disp_cat_to_twosided_disp_cat D)
      =
      D.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_disp_cat_axioms.
    }
    apply idpath.
  Qed.

  Definition two_sided_disp_cat_weq_disp_cat
    : twosided_disp_cat C₁ C₂ ≃ disp_cat (category_binproduct C₁ C₂).
  Proof.
    use weq_iso.
    - exact twosided_disp_cat_to_disp_cat.
    - exact disp_cat_to_twosided_disp_cat.
    - exact two_sided_disp_cat_weq_disp_cat_inv_left.
    - exact two_sided_disp_cat_weq_disp_cat_inv_right.
  Defined.
End TwoSidedDispCatVersusDispCat.
