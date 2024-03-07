(*****************************************************************************************

 Squares of profunctors

 A standard example of a double (bi)category is given by categories, functors, profunctors,
 and natural transformations. In this file, we define the squares of this double
 (bi)category as natural transformations between profunctors. We also provide suitable
 accessors and a builder for these. Finally, we discuss some standard examples of squares
 of profunctors. These come up when one defines the double (bi)category of functors and
 profunctors. The examples that we need are:
 - Vertical and horizontal identity squares
 - Vertical and horizontal composition of squares
 - Whiskering operations on every side
 - Associators and unitors
 Note that the associators and unitors are globular squares. We can construct these from
 natural transformations between profunctors.

 Contents
 1. Squares of profunctors
 2. Builder for squares of profunctors
 3. Transformations to squares
 4. Standard profunctor squares
 4.1. Identity squares
 4.2. Composition of squares
 4.3. Whiskering operations
 4.4. Companion pairs
 4.5. Conjoints

 *****************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Categories.HSET.SetCoends.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.Profunctors.Examples.
Require Import UniMath.CategoryTheory.Profunctors.Transformation.

Local Open Scope cat.

(** * 1. Squares of profunctors *)
Definition profunctor_square
           {C₁ C₂ D₁ D₂ : category}
           (F : C₁ ⟶ C₂)
           (G : D₁ ⟶ D₂)
           (P : D₁ ↛ C₁)
           (Q : D₂ ↛ C₂)
  : UU
  := profunctor_nat_trans P (precomp_profunctor G F Q).

Identity Coercion square_to_nat_trans : profunctor_square >-> profunctor_nat_trans.

Proposition profunctor_square_natural
            {C₁ C₂ D₁ D₂ : category}
            {F : C₁ ⟶ C₂}
            {G : D₁ ⟶ D₂}
            {P : D₁ ↛ C₁}
            {Q : D₂ ↛ C₂}
            (τ : profunctor_square F G P Q)
            {y₁ y₂ : C₁}
            {x₁ x₂ : D₁}
            (g : y₂ --> y₁)
            (f : x₁ --> x₂)
            (h : P y₁ x₁)
  : τ y₂ x₂ (P #[ g , f ] h)
    =
    Q #[ #F g , #G f ] (τ y₁ x₁ h).
Proof.
  pose (eqtohomot (pr2 τ (y₁ ,, x₁) (y₂ ,, x₂) (g ,, f)) h) as p.
  cbn in p.
  refine (p @ _).
  rewrite lmap_rmap_functor.
  apply idpath.
Qed.

Proposition profunctor_square_lmap
            {C₁ C₂ D₁ D₂ : category}
            {F : C₁ ⟶ C₂}
            {G : D₁ ⟶ D₂}
            {P : D₁ ↛ C₁}
            {Q : D₂ ↛ C₂}
            (τ : profunctor_square F G P Q)
            {y₁ y₂ : C₁}
            {x : D₁}
            (g : y₂ --> y₁)
            (h : P y₁ x)
  : τ y₂ x (lmap P g h)
    =
    lmap Q (#F g) (τ y₁ x h).
Proof.
  pose (eqtohomot (pr2 τ (y₁ ,, x) (y₂ ,, x) (g ,, identity _)) h) as p.
  cbn in p.
  rewrite functor_id in p.
  rewrite rmap_id in p.
  exact p.
Qed.

Proposition profunctor_square_rmap
            {C₁ C₂ D₁ D₂ : category}
            {F : C₁ ⟶ C₂}
            {G : D₁ ⟶ D₂}
            {P : D₁ ↛ C₁}
            {Q : D₂ ↛ C₂}
            (τ : profunctor_square F G P Q)
            {y : C₁}
            {x₁ x₂ : D₁}
            (f : x₁ --> x₂)
            (h : P y x₁)
  : τ y x₂ (rmap P f h)
    =
    rmap Q (#G f) (τ y x₁ h).
Proof.
  pose (eqtohomot (pr2 τ (y ,, x₁) (y ,, x₂) (identity _ ,, f)) h) as p.
  cbn in p.
  rewrite functor_id in p.
  rewrite lmap_id in p.
  exact p.
Qed.

Proposition profunctor_square_lmap_rmap
            {C₁ C₂ D₁ D₂ : category}
            {F : C₁ ⟶ C₂}
            {G : D₁ ⟶ D₂}
            {P : D₁ ↛ C₁}
            {Q : D₂ ↛ C₂}
            (τ : profunctor_square F G P Q)
            {y₁ y₂ : C₁}
            {x₁ x₂ : D₁}
            (g : y₂ --> y₁)
            (f : x₁ --> x₂)
            (h : P y₁ x₁)
  : τ y₂ x₂ (lmap P g (rmap P f h))
    =
    lmap Q (#F g) (rmap Q (#G f) (τ y₁ x₁ h)).
Proof.
  rewrite (profunctor_square_lmap τ g).
  apply maponpaths.
  apply profunctor_square_rmap.
Qed.

Definition profunctor_iso_square
           {C₁ C₂ D₁ D₂ : category}
           (F : C₁ ⟶ C₂)
           (G : D₁ ⟶ D₂)
           (P : D₁ ↛ C₁)
           (Q : D₂ ↛ C₂)
  : UU
  := ∑ (τ : profunctor_square F G P Q), is_profunctor_nat_iso τ.

#[reversible=no] Coercion profunctor_iso_square_to_square
         {C₁ C₂ D₁ D₂ : category}
         {F : C₁ ⟶ C₂}
         {G : D₁ ⟶ D₂}
         {P : D₁ ↛ C₁}
         {Q : D₂ ↛ C₂}
         (τ : profunctor_iso_square F G P Q)
  : profunctor_square F G P Q
  := pr1 τ.

#[reversible=no] Coercion profunctor_iso_square_is_iso
         {C₁ C₂ D₁ D₂ : category}
         {F : C₁ ⟶ C₂}
         {G : D₁ ⟶ D₂}
         {P : D₁ ↛ C₁}
         {Q : D₂ ↛ C₂}
         (τ : profunctor_iso_square F G P Q)
  : is_profunctor_nat_iso τ
  := pr2 τ.

(** * 2. Builder for squares of profunctors *)
Definition profunctor_square_data
           {C₁ C₂ D₁ D₂ : category}
           (F : C₁ ⟶ C₂)
           (G : D₁ ⟶ D₂)
           (P : D₁ ↛ C₁)
           (Q : D₂ ↛ C₂)
  : UU
  := ∏ (y : C₁) (x : D₁), P y x → Q (F y) (G x).

Definition profunctor_square_laws
           {C₁ C₂ D₁ D₂ : category}
           {F : C₁ ⟶ C₂}
           {G : D₁ ⟶ D₂}
           {P : D₁ ↛ C₁}
           {Q : D₂ ↛ C₂}
           (τ : profunctor_square_data F G P Q)
  : UU
  := ∏ (y₁ y₂ : C₁)
       (x₁ x₂ : D₁)
       (g : y₂ --> y₁)
       (f : x₁ --> x₂)
       (h : P y₁ x₁),
     τ y₂ x₂ (lmap P g (rmap P f h))
     =
     lmap Q (#F g) (rmap Q (#G f) (τ y₁ x₁ h)).

Section ProfunctorSquareBuilder.
  Context {C₁ C₂ D₁ D₂ : category}
          {F : C₁ ⟶ C₂}
          {G : D₁ ⟶ D₂}
          {P : D₁ ↛ C₁}
          {Q : D₂ ↛ C₂}
          (τ : profunctor_square_data F G P Q)
          (Hτ : profunctor_square_laws τ).

  Definition make_profunctor_square_data
    : profunctor_nat_trans_data P (precomp_profunctor G F Q)
    := τ.

  Arguments make_profunctor_square_data /.

  Proposition make_profunctor_square_law
    : profunctor_nat_trans_law make_profunctor_square_data.
  Proof.
    intros y₁ y₂ x₁ x₂ g f h ; cbn -[lmap rmap].
    rewrite lmap_precomp_profunctor, rmap_precomp_profunctor.
    apply Hτ.
  Qed.

  Definition make_profunctor_square
    : profunctor_square F G P Q.
  Proof.
    use make_profunctor_nat_trans.
    - exact make_profunctor_square_data.
    - exact make_profunctor_square_law.
  Defined.
End ProfunctorSquareBuilder.

Arguments make_profunctor_square_data {C₁ C₂ D₁ D₂ F G P Q} τ /.

Proposition eq_profunctor_square
            {C₁ C₂ D₁ D₂ : category}
            {F : C₁ ⟶ C₂}
            {G : D₁ ⟶ D₂}
            {P : D₁ ↛ C₁}
            {Q : D₂ ↛ C₂}
            {τ τ' : profunctor_square F G P Q}
            (p : ∏ (y : C₁) (x : D₁)
                   (h : P y x),
                 τ y x h = τ' y x h)
  : τ = τ'.
Proof.
  use eq_profunctor_nat_trans.
  exact p.
Qed.

Proposition profunctor_square_eq_pointwise
            {C₁ C₂ D₁ D₂ : category}
            {F : C₁ ⟶ C₂}
            {G : D₁ ⟶ D₂}
            {P : D₁ ↛ C₁}
            {Q : D₂ ↛ C₂}
            {τ τ' : profunctor_square F G P Q}
            (p : τ = τ')
            {y : C₁} {x : D₁}
            (h : P y x)
  : τ y x h = τ' y x h.
Proof.
  induction p.
  apply idpath.
Qed.

Proposition isaset_profunctor_square
            {C₁ C₂ D₁ D₂ : category}
            (F : C₁ ⟶ C₂)
            (G : D₁ ⟶ D₂)
            (P : D₁ ↛ C₁)
            (Q : D₂ ↛ C₂)
  : isaset (profunctor_square F G P Q).
Proof.
  apply isaset_profunctor_nat_trans.
Qed.

(** * 3. Transformations to squares *)
Definition profunctor_nat_trans_to_square
           {C D : category}
           {P Q : D ↛ C}
           (τ : profunctor_nat_trans P Q)
  : profunctor_square (functor_identity _) (functor_identity _) P Q.
Proof.
  use make_profunctor_square.
  - exact (λ y x h, τ y x h).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn -[lmap rmap] ;
       rewrite profunctor_nat_trans_lmap_rmap ;
       apply idpath).
Defined.

Definition profunctor_square_to_profunctor_nat_trans
           {C D : category}
           {P Q : D ↛ C}
           (τ : profunctor_square (functor_identity _) (functor_identity _) P Q)
  : profunctor_nat_trans P Q.
Proof.
  use make_profunctor_nat_trans.
  - exact (λ y x h, τ y x h).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn -[lmap rmap] ;
       rewrite profunctor_square_lmap_rmap ; cbn ;
       apply idpath).
Defined.

Definition profunctor_nat_trans_weq_square
           {C D : category}
           (P Q : D ↛ C)
  : profunctor_nat_trans P Q
    ≃
    profunctor_square (functor_identity _) (functor_identity _) P Q.
Proof.
  use weq_iso.
  - exact profunctor_nat_trans_to_square.
  - exact profunctor_square_to_profunctor_nat_trans.
  - abstract
      (intros τ ;
       use eq_profunctor_nat_trans ;
       intros ; cbn ;
       apply idpath).
  - abstract
      (intros τ ;
       use eq_profunctor_square ;
       intros ; cbn ;
       apply idpath).
Defined.

Definition profunctor_nat_iso_weq_iso_square
           {C D : category}
           (P Q : D ↛ C)
  : profunctor_nat_iso P Q
    ≃
    profunctor_iso_square (functor_identity _) (functor_identity _) P Q.
Proof.
  use (weqtotal2 (profunctor_nat_trans_weq_square P Q)).
  intro τ.
  use weqimplimpl.
  - intros Hτ y x.
    exact (Hτ y x).
  - intros Hτ y x.
    exact (Hτ y x).
  - apply isaprop_is_profunctor_nat_iso.
  - apply isaprop_is_profunctor_nat_iso.
Defined.

Definition profunctor_square_to_nat_trans
           {C₁ C₂ : category}
           {F G : C₁ ⟶ C₂}
           (τ : profunctor_square G F (id_profunctor C₁) (id_profunctor C₂))
  : G ⟹ F.
Proof.
  use make_nat_trans.
  - exact (λ x, τ x x (identity x)).
  - abstract
      (intros x y f ; cbn ;
       pose (profunctor_square_natural τ (identity x) f (identity x)) as p ;
       cbn in p ;
       rewrite !functor_id in p ;
       rewrite !id_left in p ;
       rewrite <- p ;
       pose (profunctor_square_natural τ f (identity y) (identity y)) as q ;
       cbn in q ;
       rewrite !functor_id in q ;
       rewrite !id_right in q ;
       rewrite <- q ;
       apply idpath).
Defined.

(** * 4. Standard profunctor squares *)

(** ** 4.1. Identity squares *)
Definition id_h_profunctor_square
           {C D : category}
           (P : D ↛ C)
  : profunctor_square (functor_identity C) (functor_identity D) P P.
Proof.
  use make_profunctor_square.
  - exact (λ y x h, h).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn -[lmap rmap] ;
       apply idpath).
Defined.

Definition id_v_profunctor_square
           {C D : category}
           (F : C ⟶ D)
  : profunctor_square F F (id_profunctor C) (id_profunctor D).
Proof.
  use make_profunctor_square.
  - exact (λ y x h, #F h).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn -[lmap rmap] ;
       rewrite !lmap_id_profunctor, !rmap_id_profunctor ;
       rewrite !functor_comp ;
       apply idpath).
Defined.

(** ** 4.2. Composition of squares *)
Definition comp_h_profunctor_square
           {C₁ C₂ C₃ D₁ D₂ D₃ : category}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : C₂ ⟶ C₃}
           {G₁ : D₁ ⟶ D₂}
           {G₂ : D₂ ⟶ D₃}
           {P₁ : D₁ ↛ C₁}
           {P₂ : D₂ ↛ C₂}
           {P₃ : D₃ ↛ C₃}
           (τ : profunctor_square F₁ G₁ P₁ P₂)
           (θ : profunctor_square F₂ G₂ P₂ P₃)
  : profunctor_square (F₁ ∙ F₂) (G₁ ∙ G₂) P₁ P₃.
Proof.
  use make_profunctor_square.
  - exact (λ y x h, θ (F₁ y) (G₁ x) (τ y x h)).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn -[lmap rmap] ;
       rewrite (profunctor_square_lmap_rmap τ) ;
       rewrite (profunctor_square_lmap_rmap θ) ;
       apply idpath).
Defined.

Definition comp_v_profunctor_square_mor
           {C₁ C₂ D₁ D₂ E₁ E₂ : category}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : D₁ ⟶ D₂}
           {F₃ : E₁ ⟶ E₂}
           {P₁ : C₁ ↛ D₁}
           {Q₁ : D₁ ↛ E₁}
           {P₂ : C₂ ↛ D₂}
           {Q₂ : D₂ ↛ E₂}
           (τ : profunctor_square F₂ F₁ P₁ P₂)
           (θ : profunctor_square F₃ F₂ Q₁ Q₂)
           (z : E₁)
           (x : C₁)
  : comp_profunctor P₁ Q₁ z x → comp_profunctor P₂ Q₂ (F₃ z) (F₁ x).
Proof.
  use from_comp_profunctor_ob.
  - exact (λ y h h', comp_profunctor_ob_in P₂ Q₂ (F₂ y) (τ y x h) (θ z y h')).
  - abstract
      (intros y₁ y₂ g h h' ; cbn ;
       rewrite (profunctor_square_rmap θ) ;
       rewrite (profunctor_square_lmap τ) ;
       rewrite comp_profunctor_ob_in_comm ;
       apply idpath).
Defined.

Proposition comp_v_profunctor_square_mor_comm
            {C₁ C₂ D₁ D₂ E₁ E₂ : category}
            {F₁ : C₁ ⟶ C₂}
            {F₂ : D₁ ⟶ D₂}
            {F₃ : E₁ ⟶ E₂}
            {P₁ : C₁ ↛ D₁}
            {Q₁ : D₁ ↛ E₁}
            {P₂ : C₂ ↛ D₂}
            {Q₂ : D₂ ↛ E₂}
            (τ : profunctor_square F₂ F₁ P₁ P₂)
            (θ : profunctor_square F₃ F₂ Q₁ Q₂)
            (z : E₁)
            (x : C₁)
            (y : D₁)
            (h₁ : P₁ y x)
            (h₂ : Q₁ z y)
  : comp_v_profunctor_square_mor
      τ θ z x
      (comp_profunctor_ob_in _ _ y h₁ h₂)
    =
    comp_profunctor_ob_in P₂ Q₂ (F₂ y) (τ y x h₁) (θ z y h₂).
Proof.
  unfold comp_v_profunctor_square_mor.
  rewrite from_comp_profunctor_ob_comm.
  apply idpath.
Qed.

Proposition comp_v_profunctor_square_laws
            {C₁ C₂ D₁ D₂ E₁ E₂ : category}
            {F₁ : C₁ ⟶ C₂}
            {F₂ : D₁ ⟶ D₂}
            {F₃ : E₁ ⟶ E₂}
            {P₁ : C₁ ↛ D₁}
            {Q₁ : D₁ ↛ E₁}
            {P₂ : C₂ ↛ D₂}
            {Q₂ : D₂ ↛ E₂}
            (τ : profunctor_square F₂ F₁ P₁ P₂)
            (θ : profunctor_square F₃ F₂ Q₁ Q₂)
  : profunctor_square_laws (comp_v_profunctor_square_mor τ θ).
Proof.
  intros z₁ z₂ x₁ x₂ k f h.
  cbn.
  use (mor_from_comp_profunctor_ob_eq
         P₁ Q₁
         z₁ x₁
         (λ h,
          comp_v_profunctor_square_mor
            τ θ z₂ x₂
            (comp_profunctor_mor
               P₁ Q₁ k (identity x₂)
               (comp_profunctor_mor
                  P₁ Q₁ (identity z₁) f
                  h)))
         (λ h,
          comp_profunctor_mor
            P₂ Q₂ (# F₃ k) (identity (F₁ x₂))
            (comp_profunctor_mor
               P₂ Q₂ (identity (F₃ z₁)) (# F₁ f)
               (comp_v_profunctor_square_mor
                  τ θ z₁ x₁
                  h)))).
  clear h.
  intros y h h'.
  cbn.
  rewrite !comp_profunctor_mor_comm.
  etrans.
  {
    exact (comp_v_profunctor_square_mor_comm τ θ z₂ x₂ y _ _).
  }
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    exact (comp_v_profunctor_square_mor_comm τ θ z₁ x₁ y _ _).
  }
  rewrite !comp_profunctor_mor_comm.
  rewrite !lmap_id.
  rewrite !rmap_id.
  rewrite (profunctor_square_lmap θ).
  rewrite (profunctor_square_rmap τ).
  apply idpath.
Qed.

Definition comp_v_profunctor_square
           {C₁ C₂ D₁ D₂ E₁ E₂ : category}
           {F₁ : C₁ ⟶ C₂}
           {F₂ : D₁ ⟶ D₂}
           {F₃ : E₁ ⟶ E₂}
           {P₁ : C₁ ↛ D₁}
           {Q₁ : D₁ ↛ E₁}
           {P₂ : C₂ ↛ D₂}
           {Q₂ : D₂ ↛ E₂}
           (τ : profunctor_square F₂ F₁ P₁ P₂)
           (θ : profunctor_square F₃ F₂ Q₁ Q₂)
  : profunctor_square F₃ F₁ (comp_profunctor P₁ Q₁) (comp_profunctor P₂ Q₂).
Proof.
  use make_profunctor_square.
  - exact (λ z x, comp_v_profunctor_square_mor τ θ z x).
  - exact (comp_v_profunctor_square_laws τ θ).
Defined.

(** ** 4.3. Whiskering operations *)
Definition uwhisker_profunctor_square
           {C₁ C₂ D₁ D₂ : category}
           {F F' : C₁ ⟶ C₂}
           {G : D₁ ⟶ D₂}
           {P : D₁ ↛ C₁}
           {Q : D₂ ↛ C₂}
           (τ : F ⟹ F')
           (θ : profunctor_square F' G P Q)
  : profunctor_square F G P Q.
Proof.
  use make_profunctor_square.
  - exact (λ y x h, lmap Q (τ y) (θ y x h)).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn -[lmap rmap] ;
       rewrite (profunctor_square_lmap_rmap θ) ;
       rewrite <- lmap_rmap ;
       rewrite <- !lmap_comp ;
       rewrite (nat_trans_ax τ _ _ g) ;
       apply idpath).
Defined.

Definition dwhisker_profunctor_square
           {C₁ C₂ D₁ D₂ : category}
           {F : C₁ ⟶ C₂}
           {G G' : D₁ ⟶ D₂}
           {P : D₁ ↛ C₁}
           {Q : D₂ ↛ C₂}
           (τ : G ⟹ G')
           (θ : profunctor_square F G P Q)
  : profunctor_square F G' P Q.
Proof.
  use make_profunctor_square.
  - exact (λ y x h, rmap Q (τ x) (θ y x h)).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn -[lmap rmap] ;
       rewrite (profunctor_square_lmap_rmap θ) ;
       rewrite <- lmap_rmap ;
       apply maponpaths ;
       rewrite <- !rmap_comp ;
       rewrite (nat_trans_ax τ _ _ f) ;
       apply idpath).
Defined.

Definition lwhisker_profunctor_square
           {C₁ C₂ D₁ D₂ : category}
           {F : C₁ ⟶ C₂}
           {G : D₁ ⟶ D₂}
           {P P' : D₁ ↛ C₁}
           {Q : D₂ ↛ C₂}
           (τ : profunctor_nat_trans P P')
           (θ : profunctor_square F G P' Q)
  : profunctor_square F G P Q.
Proof.
  use make_profunctor_square.
  - exact (λ y x h, θ y x (τ y x h)).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn -[lmap rmap] ;
       rewrite profunctor_nat_trans_lmap_rmap ;
       rewrite profunctor_square_lmap_rmap ;
       apply idpath).
Defined.

Definition rwhisker_profunctor_square
           {C₁ C₂ D₁ D₂ : category}
           {F : C₁ ⟶ C₂}
           {G : D₁ ⟶ D₂}
           {P : D₁ ↛ C₁}
           {Q Q' : D₂ ↛ C₂}
           (τ : profunctor_nat_trans Q Q')
           (θ : profunctor_square F G P Q)
  : profunctor_square F G P Q'.
Proof.
  use make_profunctor_square.
  - exact (λ y x h, τ (F y) (G x) (θ y x h)).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn -[lmap rmap] ;
       rewrite profunctor_square_lmap_rmap ;
       rewrite profunctor_nat_trans_lmap_rmap ;
       apply idpath).
Defined.

(** * 4.4. Unitors and associators *)
Definition lunitor_profunctor_square
           {C₁ C₂ : category}
           (P : C₁ ↛ C₂)
  : profunctor_square
      (functor_identity C₂)
      (functor_identity C₁)
      (comp_profunctor (id_profunctor C₁) P)
      P.
Proof.
  use profunctor_nat_trans_to_square.
  exact (lunitor_profunctor_nat_trans P).
Defined.

Definition runitor_profunctor_square
           {C₁ C₂ : category}
           (P : C₁ ↛ C₂)
  : profunctor_square
      (functor_identity C₂)
      (functor_identity C₁)
      (comp_profunctor P (id_profunctor C₂))
      P.
Proof.
  use profunctor_nat_trans_to_square.
  exact (runitor_profunctor_nat_trans P).
Defined.

Definition associator_profunctor_square
           {C₁ C₂ C₃ C₄ : category}
           (P₁ : C₁ ↛ C₂)
           (P₂ : C₂ ↛ C₃)
           (P₃ : C₃ ↛ C₄)
  :  profunctor_square
       (functor_identity C₄)
       (functor_identity C₁)
       (comp_profunctor P₁ (comp_profunctor P₂ P₃))
       (comp_profunctor (comp_profunctor P₁ P₂) P₃).
Proof.
  use profunctor_nat_trans_to_square.
  exact (associator_profunctor_nat_trans P₁ P₂ P₃).
Defined.

(** * 4.4. Companion pairs *)
Definition representable_profunctor_left_unit
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : profunctor_square
      (functor_identity C₂)
      F
      (representable_profunctor_left F)
      (id_profunctor C₂).
Proof.
  use make_profunctor_square.
  - exact (λ y x f, f).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn in * ;
       rewrite functor_id ;
       rewrite !id_left, !id_right ;
       apply idpath).
Defined.

Definition representable_profunctor_left_counit
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : profunctor_square
      F
      (functor_identity C₁)
      (id_profunctor C₁)
      (representable_profunctor_left F).
Proof.
  use make_profunctor_square.
  - exact (λ y x f, #F f).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn in * ;
       rewrite functor_id ;
       rewrite !id_left, !id_right ;
       rewrite !functor_comp ;
       apply idpath).
Defined.

(** * 4.5. Conjoints *)
Definition representable_profunctor_right_unit
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : profunctor_square
      (functor_identity C₁)
      F
      (id_profunctor C₁)
      (representable_profunctor_right F).
Proof.
  use make_profunctor_square.
  - exact (λ y x f, #F f).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn in * ;
       rewrite functor_id ;
       rewrite !id_left, !id_right ;
       rewrite !functor_comp ;
       apply idpath).
Defined.

Definition representable_profunctor_right_counit
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : profunctor_square
      F
      (functor_identity C₂)
      (representable_profunctor_right F)
      (id_profunctor C₂).
Proof.
  use make_profunctor_square.
  - exact (λ y x f, f).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ; cbn in * ;
       rewrite functor_id ;
       rewrite !id_left, !id_right ;
       apply idpath).
Defined.
