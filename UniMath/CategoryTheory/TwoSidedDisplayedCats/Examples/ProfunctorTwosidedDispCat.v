(**********************************************************************************

 The 2-sided displayed category of profunctors

 We define a 2-sided displayed category over the category of strict categories as
 follows:
 - The displayed objects over `C` and `D` are profunctors from `C` to `D`.
 - The displayed morphisms are profunctor squares.
 In fact, this 2-sided displayed category is univalent. The reason for that is
 because profunctors are functors into the category of sets, which is univalent.
 For that reason, the category of profunctors from `C` to `D` is univalent
 regardless of whether `C` and `D` are univalent. This is the first building
 block for constructing the univalent pseudo double category of strict categories,
 functors, and profunctors.

 Contents
 1. The data of the 2-sided displayed category
 2. Transport laws for this 2-sided displayed category
 3. The 2-sided displayed category of profunctors
 4. Isomorphisms of profunctors
 5. It is a univalent 2-sided displayed category

 **********************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.categories.CategoryOfSetCategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.Profunctors.Examples.
Require Import UniMath.CategoryTheory.Profunctors.Transformation.
Require Import UniMath.CategoryTheory.Profunctors.Squares.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.

Local Open Scope cat.

(** * 1. The data of the 2-sided displayed category *)
Definition twosided_disp_cat_of_profunctors_ob_mor
  : twosided_disp_cat_ob_mor
      cat_of_setcategory
      cat_of_setcategory.
Proof.
  simple refine (_ ,, _).
  - exact (λ (C₁ C₂ : setcategory), C₁ ↛ C₂).
  - exact (λ C₁ C₂ D₁ D₂ P Q F G, profunctor_square G F P Q).
Defined.

Definition twosided_disp_cat_of_profunctors_id_comp
  : twosided_disp_cat_id_comp
      twosided_disp_cat_of_profunctors_ob_mor.
Proof.
  simple refine (_ ,, _).
  - exact (λ C D P, id_h_profunctor_square P).
  - exact (λ C₁ C₂ C₃ D₁ D₂ D₃ P₁ P₂ P₃ F₁ F₂ G₁ G₂ τ₁ τ₂, comp_h_profunctor_square τ₁ τ₂).
Defined.

Definition twosided_disp_cat_of_profunctors_data
  : twosided_disp_cat_data
      cat_of_setcategory
      cat_of_setcategory.
Proof.
  simple refine (_ ,, _).
  - exact twosided_disp_cat_of_profunctors_ob_mor.
  - exact twosided_disp_cat_of_profunctors_id_comp.
Defined.

(** * 2. Transport laws for this 2-sided displayed category *)
Proposition transportf_disp_mor2_profunctors_help
            {C₁ C₂ D₁ D₂ : cat_of_setcategory}
            {P : twosided_disp_cat_of_profunctors_data C₁ D₁}
            {Q : twosided_disp_cat_of_profunctors_data C₂ D₂}
            {F₁ F₂ : (C₁ : setcategory) ⟶ (C₂ : setcategory)}
            (p : F₁ = F₂)
            {G₁ G₂ : (D₁ : setcategory) ⟶ (D₂ : setcategory)}
            (q : G₁ = G₂)
            (τ : P -->[ F₁ ][ G₁] Q)
            {y : (D₁ : setcategory)}
            {x : (C₁ : setcategory)}
            (h : (P : profunctor _ _) y x)
  : (@transportf_disp_mor2
        _ _
        (twosided_disp_cat_of_profunctors_data)
        C₁ C₂ D₁ D₂
        P Q
        F₁ F₂
        p
        G₁ G₂
        q
        τ : profunctor_square _ _ _ _)
      y x h
    =
    transportf
      (λ z, (Q : _ ↛ _) z _)
      (path_functor_ob q y)
      (transportf
         (λ z, (Q : _ ↛ _) _ z)
         (path_functor_ob p x)
         ((τ : profunctor_square _ _ _ _) y x h)).
Proof.
  induction p, q ; cbn.
  apply idpath.
Qed.

Proposition transportf_disp_mor2_profunctors
            {C₁ C₂ D₁ D₂ : cat_of_setcategory}
            {P : twosided_disp_cat_of_profunctors_data C₁ D₁}
            {Q : twosided_disp_cat_of_profunctors_data C₂ D₂}
            {FD : functor_data (C₁ : setcategory) (C₂ : setcategory)}
            {HF₁ HF₂ : is_functor FD}
            (F₁ := make_functor FD HF₁)
            (F₂ := make_functor FD HF₂)
            (p : F₁ = F₂)
            {GD : functor_data (D₁ : setcategory) (D₂ : setcategory)}
            {HG₁ HG₂ : is_functor GD}
            (G₁ := make_functor GD HG₁)
            (G₂ := make_functor GD HG₂)
            (q : G₁ = G₂)
            (τ : P -->[ F₁ ][ G₁] Q)
            {y : (D₁ : setcategory)}
            {x : (C₁ : setcategory)}
            (h : (P : profunctor _ _) y x)
  : (@transportf_disp_mor2
       _ _
       (twosided_disp_cat_of_profunctors_data)
       C₁ C₂ D₁ D₂
       P Q
       F₁ F₂
       p
       G₁ G₂
       q
       τ : profunctor_square _ _ _ _)
      y x h
    =
    (τ : profunctor_square _ _ _ _) y x h.
Proof.
  rewrite transportf_disp_mor2_profunctors_help.
  cbn.
  assert (path_functor_ob q y = idpath _) as r.
  {
    apply isaset_ob.
  }
  rewrite r ; clear r.
  assert (path_functor_ob p x = idpath _) as r.
  {
    apply isaset_ob.
  }
  rewrite r ; clear r.
  cbn.
  apply idpath.
Qed.

Proposition twosided_disp_cat_of_profunctors_axioms
  : twosided_disp_cat_axioms twosided_disp_cat_of_profunctors_data.
Proof.
  repeat split.
  - intros C₁ C₂ D₁ D₂ P Q F G τ.
    use eq_profunctor_square.
    intros y x h ; cbn.
    refine (!_).
    apply transportf_disp_mor2_profunctors.
  - intros C₁ C₂ D₁ D₂ P Q F G τ.
    use eq_profunctor_square.
    intros y x h ; cbn.
    refine (!_).
    exact (transportf_disp_mor2_profunctors (!(id_right F)) (!(id_right G)) τ h).
  - intros C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ P₁ P₂ P₃ P₄ F₁ F₂ F₃ G₁ G₂ G₃ τ₁ τ₂ τ₃.
    use eq_profunctor_square.
    intros y x h ; cbn.
    refine (!_).
    exact (transportf_disp_mor2_profunctors
             (!(assoc F₁ F₂ F₃)) (!(assoc G₁ G₂ G₃))
             (comp_h_profunctor_square (comp_h_profunctor_square τ₁ τ₂) τ₃)
             h).
  - intro ; intros.
    apply isaset_profunctor_square.
Qed.

(** * 3. The 2-sided displayed category of profunctors *)
Definition twosided_disp_cat_of_profunctors
  : twosided_disp_cat
      cat_of_setcategory
      cat_of_setcategory.
Proof.
  simple refine (_ ,, _).
  - exact twosided_disp_cat_of_profunctors_data.
  - exact twosided_disp_cat_of_profunctors_axioms.
Defined.

(** * 4. Isomorphisms of profunctors *)
Section ToProfunctorIso.
  Context {C D : setcategory}
          {P Q : C ↛ D}
          (τ : profunctor_square (functor_identity _) (functor_identity _) P Q)
          (Hτ : is_profunctor_nat_iso τ).

  Definition inv_square_profunctor
    : profunctor_square (functor_identity _) (functor_identity _) Q P.
  Proof.
    use make_profunctor_square.
    - exact (λ y x h, invmap (make_weq _ (Hτ y x)) h).
    - abstract
        (intros y₁ y₂ g x₁ x₂ f h ; cbn ;
         use (invmaponpathsweq (make_weq _ (Hτ _ _))) ;
         rewrite homotweqinvweq ; cbn ;
         rewrite (profunctor_square_lmap_rmap τ) ; cbn ;
         do 2 apply maponpaths ;
         refine (!_) ;
         apply (homotweqinvweq (make_weq _ (Hτ _ _)))).
  Defined.

  Definition to_iso_twosided_disp_profunctor
    : is_iso_twosided_disp
        (D := twosided_disp_cat_of_profunctors)
        (identity_is_z_iso _) (identity_is_z_iso _)
        τ.
  Proof.
    refine (inv_square_profunctor ,, _ ,, _).
    - abstract
        (use eq_profunctor_square ;
         intros y x h ; cbn ;
         refine (homotinvweqweq (make_weq _ (Hτ _ _)) _ @ _) ;
         refine (!_) ;
         exact (transportf_disp_mor2_profunctors
                  (!(id_left (C := cat_of_setcategory) (functor_identity _)))
                  (!(id_left (C := cat_of_setcategory) (functor_identity _)))
                  (id_h_profunctor_square P)
                  h)).
    - abstract
        (use eq_profunctor_square ;
         intros y x h ; cbn ;
         refine (homotweqinvweq (make_weq _ (Hτ _ _)) _ @ _) ;
         refine (!_) ;
         exact (transportf_disp_mor2_profunctors
                  (!(id_left (C := cat_of_setcategory) (functor_identity _)))
                  (!(id_left (C := cat_of_setcategory) (functor_identity _)))
                  (id_h_profunctor_square Q)
                  h)).
  Defined.
End ToProfunctorIso.

Section FromProfunctorIso.
  Context {C D : setcategory}
          {P Q : C ↛ D}
          {τ : profunctor_square (functor_identity _) (functor_identity _) P Q}
          (Hτ : is_iso_twosided_disp
                  (D := twosided_disp_cat_of_profunctors)
                  (identity_is_z_iso _) (identity_is_z_iso _)
                  τ).

  Let θ : profunctor_square (functor_identity _) (functor_identity _) Q P
    := iso_inv_twosided_disp Hτ.

  Definition from_iso_twosided_disp_profunctor
             (y : D)
             (x : C)
    : isweq (τ y x).
  Proof.
    use isweq_iso.
    - exact (θ y x).
    - abstract
        (intros h ;
         refine (profunctor_square_eq_pointwise (inv_after_iso_twosided_disp Hτ) h @ _) ;
         exact (transportf_disp_mor2_profunctors
                  (!(id_left (C := cat_of_setcategory) (functor_identity _)))
                  (!(id_left (C := cat_of_setcategory) (functor_identity _)))
                  (id_h_profunctor_square P)
                  h)).
    - abstract
        (intros h ;
         refine (profunctor_square_eq_pointwise (iso_after_inv_twosided_disp Hτ) h @ _) ;
         exact (transportf_disp_mor2_profunctors
                  (!(id_left (C := cat_of_setcategory) (functor_identity _)))
                  (!(id_left (C := cat_of_setcategory) (functor_identity _)))
                  (id_h_profunctor_square Q)
                  h)).
  Defined.
End FromProfunctorIso.

Definition iso_twosided_disp_profunctor_weq
           {C D : setcategory}
           (P Q : C ↛ D)
  : profunctor_iso_square (functor_identity _) (functor_identity _) P Q
    ≃
    iso_twosided_disp
      (D := twosided_disp_cat_of_profunctors)
      (identity_z_iso _) (identity_z_iso _)
      P Q.
Proof.
  use weqfibtototal.
  intro τ.
  use weqimplimpl.
  - apply to_iso_twosided_disp_profunctor.
  - intros H y x.
    exact (from_iso_twosided_disp_profunctor H y x).
  - apply isaprop_is_profunctor_nat_iso.
  - apply isaprop_is_iso_twosided_disp.
Defined.

(** * 5. It is a univalent 2-sided displayed category *)
Definition is_univalent_twosided_disp_cat_of_profunctors
  : is_univalent_twosided_disp_cat twosided_disp_cat_of_profunctors.
Proof.
  intros C C' D D' p q P Q.
  induction p, q ; cbn in *.
  use weqhomot.
  - exact (iso_twosided_disp_profunctor_weq P Q
           ∘ profunctor_nat_iso_weq_iso_square P Q
           ∘ path_profunctor_weq_profunctor_nat_iso P Q)%weq.
  - intro p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_iso_twosided_disp.
    }
    use eq_profunctor_square.
    intros y x h ; cbn.
    apply idpath.
Qed.
