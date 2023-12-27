(*****************************************************************************************

 Transformations of profunctors

 In this file we study natural transformations between profunctors. We provide a builder
 for such transformations and we give equality principles for them. In addition, we
 provide several standard examples of natural transformations between profunctors, which
 are needed to construct the bicategory of categories, profunctors, and natural
 transformations.

 Contents
 1. Natural transformations between profunctors
 2. Builder for natural transformations between profunctors
 3. Equality of natural transformations between profunctors
 4. Natural isomorphisms between profunctors
 5. Standard natural transformations between profunctors
 6. Equality of profunctors

 *****************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.Profunctors.Examples.

Local Open Scope cat.

(** * 1. Natural transformations between profunctors *)
Definition profunctor_nat_trans
           {C₁ C₂ : category}
           (P Q : profunctor C₁ C₂)
  : UU
  := nat_trans (P : _ ⟶ _) (Q : _ ⟶ _).

Definition profunctor_nat_trans_point
           {C₁ C₂ : category}
           {P Q : profunctor C₁ C₂}
           (τ : profunctor_nat_trans P Q)
           {y : C₂} {x : C₁}
           (h : P y x)
  : Q y x
  := pr1 τ (y ,, x) h.

Coercion profunctor_nat_trans_point
  : profunctor_nat_trans >-> Funclass.

Proposition profunctor_nat_trans_natural
            {C₁ C₂ : category}
            {P Q : profunctor C₁ C₂}
            (τ : profunctor_nat_trans P Q)
            {y₁ y₂ : C₂} {x₁ x₂ : C₁}
            (g : y₂ --> y₁) (f : x₁ --> x₂)
            (h : P y₁ x₁)
  : τ y₂ x₂ (P #[ g , f ] h)
    =
    Q #[ g , f ] (τ y₁ x₁ h).
Proof.
  exact (eqtohomot
           (nat_trans_ax τ (y₁ ,, x₁) (y₂ ,, x₂) (g ,, f))
           h).
Qed.

Proposition profunctor_nat_trans_lmap_rmap
            {C₁ C₂ : category}
            {P Q : profunctor C₁ C₂}
            (τ : profunctor_nat_trans P Q)
            {y₁ y₂ : C₂} {x₁ x₂ : C₁}
            (g : y₂ --> y₁) (f : x₁ --> x₂)
            (h : P y₁ x₁)
  : τ y₂ x₂ (lmap P g (rmap P f h))
    =
    lmap Q g (rmap Q f (τ y₁ x₁ h)).
Proof.
  rewrite !lmap_rmap_functor.
  rewrite profunctor_nat_trans_natural.
  apply idpath.
Qed.

(** * 2. Builder for natural transformations between profunctors *)
Definition profunctor_nat_trans_data
           {C₁ C₂ : category}
           (P Q : profunctor C₁ C₂)
  : UU
  := ∏ (y : C₂) (x : C₁),
     P y x → Q y x.

Definition profunctor_nat_trans_law
           {C₁ C₂ : category}
           {P Q : profunctor C₁ C₂}
           (τ : profunctor_nat_trans_data P Q)
  : UU
  := ∏ (y₁ y₂ : C₂) (x₁ x₂ : C₁)
       (g : y₂ --> y₁) (f : x₁ --> x₂)
       (h : P y₁ x₁),
     τ y₂ x₂ (lmap P g (rmap P f h))
     =
     lmap Q g (rmap Q f (τ y₁ x₁ h)).

Section MakeProfunctorNatTrans.
  Context {C₁ C₂ : category}
          {P Q : profunctor C₁ C₂}
          (τ : profunctor_nat_trans_data P Q)
          (H : profunctor_nat_trans_law τ).

   Definition make_profunctor_nat_trans_data
     : nat_trans_data (P : _ ⟶ _) (Q : _ ⟶ _)
     := λ xy, τ (pr1 xy) (pr2 xy).

   Arguments make_profunctor_nat_trans_data /.

   Proposition make_profunctor_nat_trans_law
     : is_nat_trans _ _ make_profunctor_nat_trans_data.
   Proof.
     intros xy₁ xy₂ fg.
     induction xy₁ as [ y₁ x₁ ].
     induction xy₂ as [ y₂ x₂ ].
     induction fg as [ g f ].
     use funextsec.
     intro h.
     pose (H _ _ _ _ g f h) as p.
     cbn in *.
     refine (_ @ p @ _) ; clear p.
     - rewrite lmap_rmap_functor.
       apply idpath.
     - rewrite lmap_rmap_functor.
       apply idpath.
   Qed.

  Definition make_profunctor_nat_trans
    : profunctor_nat_trans P Q.
  Proof.
    use make_nat_trans.
    - exact make_profunctor_nat_trans_data.
    - exact make_profunctor_nat_trans_law.
  Defined.
End MakeProfunctorNatTrans.

Arguments make_profunctor_nat_trans_data {C₁ C₂ P Q} τ /.

(** * 3. Equality of natural transformations between profunctors *)
Proposition eq_profunctor_nat_trans
            {C₁ C₂ : category}
            {P Q : profunctor C₁ C₂}
            {τ τ' : profunctor_nat_trans P Q}
            (p : ∏ (y : C₂) (x : C₁)
                   (h : P y x),
                 τ y x h = τ' y x h)
  : τ = τ'.
Proof.
  use nat_trans_eq.
  {
    apply homset_property.
  }
  intros xy.
  induction xy as [ y x ] ; cbn.
  use funextsec.
  intro h.
  exact (p y x h).
Qed.

Proposition profunctor_nat_trans_eq_pointwise
            {C₁ C₂ : category}
            {P Q : profunctor C₁ C₂}
            {τ τ' : profunctor_nat_trans P Q}
            (p : τ = τ')
            {y : C₂} {x : C₁}
            (h : P y x)
  : τ y x h = τ' y x h.
Proof.
  induction p.
  apply idpath.
Qed.

Proposition isaset_profunctor_nat_trans
            {C₁ C₂ : category}
            (P Q : profunctor C₁ C₂)
  : isaset (profunctor_nat_trans P Q).
Proof.
  use isaset_nat_trans.
  apply homset_property.
Qed.

(** * 4. Natural isomorphisms between profunctors *)
Definition is_profunctor_nat_iso
           {C₁ C₂ : category}
           {P Q : profunctor C₁ C₂}
           (τ : profunctor_nat_trans P Q)
  : UU
  := ∏ (y : C₂) (x : C₁), isweq (τ y x).

Definition inv_profunctor_nat_iso
           {C₁ C₂ : category}
           {P Q : profunctor C₁ C₂}
           {τ : profunctor_nat_trans P Q}
           (Hτ : is_profunctor_nat_iso τ)
           {y : C₂}
           {x : C₁}
           (h : Q y x)
  : P y x
  := invmap (make_weq _ (Hτ y x)) h.

Proposition inv_profunctor_nat_iso_left
            {C₁ C₂ : category}
            {P Q : profunctor C₁ C₂}
            {τ : profunctor_nat_trans P Q}
            (Hτ : is_profunctor_nat_iso τ)
            {y : C₂}
            {x : C₁}
            (h : P y x)
  : inv_profunctor_nat_iso Hτ (τ y x h) = h.
Proof.
  apply (homotinvweqweq (make_weq _ (Hτ y x))).
Qed.

Proposition inv_profunctor_nat_iso_right
            {C₁ C₂ : category}
            {P Q : profunctor C₁ C₂}
            {τ : profunctor_nat_trans P Q}
            (Hτ : is_profunctor_nat_iso τ)
            {y : C₂}
            {x : C₁}
            (h : Q y x)
  : τ y x (inv_profunctor_nat_iso Hτ h) = h.
Proof.
  apply (homotweqinvweq (make_weq _ (Hτ y x))).
Qed.

Definition inv_profunctor_nat_trans
           {C₁ C₂ : category}
           {P Q : profunctor C₁ C₂}
           {τ : profunctor_nat_trans P Q}
           (Hτ : is_profunctor_nat_iso τ)
  : profunctor_nat_trans Q P.
Proof.
  use make_profunctor_nat_trans.
  - exact (λ y x h, inv_profunctor_nat_iso Hτ h).
  - abstract
      (intros y₁ y₂ x₁ x₂ g f h ;
       cbn ;
       use (invmaponpathsweq (make_weq _ (Hτ _ _))) ;
       cbn ;
       rewrite inv_profunctor_nat_iso_right ;
       rewrite (profunctor_nat_trans_lmap_rmap τ) ;
       rewrite inv_profunctor_nat_iso_right ;
       apply idpath).
Defined.

Definition isaprop_is_profunctor_nat_iso
           {C₁ C₂ : category}
           {P Q : profunctor C₁ C₂}
           (τ : profunctor_nat_trans P Q)
  : isaprop (is_profunctor_nat_iso τ).
Proof.
  do 2 (use impred ; intro).
  apply isapropisweq.
Qed.

Definition profunctor_nat_iso
           {C₁ C₂ : category}
           (P Q : profunctor C₁ C₂)
  : UU
  := ∑ (τ : profunctor_nat_trans P Q), is_profunctor_nat_iso τ.

Definition make_profunctor_nat_iso
           {C₁ C₂ : category}
           {P Q : profunctor C₁ C₂}
           (τ : profunctor_nat_trans P Q)
           (Hτ : is_profunctor_nat_iso τ)
  : profunctor_nat_iso P Q
  := τ ,, Hτ.

Coercion profunctor_nat_iso_to_profunctor_nat_trans
         {C₁ C₂ : category}
         {P Q : profunctor C₁ C₂}
         (τ : profunctor_nat_iso P Q)
  : profunctor_nat_trans P Q
  := pr1 τ.

Coercion profunctor_nat_iso_to_is_profunctor_nat_iso
         {C₁ C₂ : category}
         {P Q : profunctor C₁ C₂}
         (τ : profunctor_nat_iso P Q)
  : is_profunctor_nat_iso τ
  := pr2 τ.

Section IsoToProfunctorIso.
  Context {C₁ C₂ : category}
          {P Q : profunctor C₁ C₂}
          {τ : profunctor_nat_trans P Q}
          (Hτ : is_z_isomorphism
                  (C := [category_binproduct C₂^op C₁ , HSET_univalent_category])
                  τ).

  Let τiso
    : z_iso (C := [category_binproduct C₂^op C₁ , HSET_univalent_category]) P Q
    := _ ,, Hτ.
  Let θ : profunctor_nat_trans Q P := inv_from_z_iso τiso.

  Definition is_z_iso_to_is_profunctor_nat_iso
    : is_profunctor_nat_iso τ.
  Proof.
    intros y x.
    use isweq_iso.
    - exact (θ y x).
    - abstract
        (intros h ;
         exact (profunctor_nat_trans_eq_pointwise (z_iso_inv_after_z_iso τiso) h)).
    - abstract
        (intros h ;
         exact (profunctor_nat_trans_eq_pointwise (z_iso_after_z_iso_inv τiso) h)).
  Defined.
End IsoToProfunctorIso.

Definition is_profunctor_nat_iso_to_is_z_iso
           {C₁ C₂ : category}
           {P Q : profunctor C₁ C₂}
           {τ : profunctor_nat_trans P Q}
           (Hτ : is_profunctor_nat_iso τ)
  : is_z_isomorphism
      (C := [category_binproduct C₂^op C₁ , HSET_univalent_category])
      τ.
Proof.
  use make_is_z_isomorphism.
  - exact (inv_profunctor_nat_trans Hτ).
  - split.
    + abstract
        (use eq_profunctor_nat_trans ;
         intros y x h ; cbn ;
         apply inv_profunctor_nat_iso_left).
    + abstract
        (use eq_profunctor_nat_trans ;
         intros y x h ; cbn ;
         apply inv_profunctor_nat_iso_right).
Defined.

Definition is_profunctor_nat_iso_weq_is_z_iso
           {C₁ C₂ : category}
           {P Q : profunctor C₁ C₂}
           (τ : profunctor_nat_trans P Q)
  : is_z_isomorphism (C := [category_binproduct C₂^op C₁ , HSET_univalent_category]) τ
    ≃
    is_profunctor_nat_iso τ.
Proof.
  use weqimplimpl.
  - exact is_z_iso_to_is_profunctor_nat_iso.
  - exact is_profunctor_nat_iso_to_is_z_iso.
  - apply isaprop_is_z_isomorphism.
  - apply isaprop_is_profunctor_nat_iso.
Defined.

(** * 5. Standard natural transformations between profunctors *)
Definition profunctor_nat_trans_id
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
  : profunctor_nat_trans P P
  := nat_trans_id (P : _ ⟶ _).

Definition profunctor_nat_iso_id
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
  : profunctor_nat_iso P P.
Proof.
  use make_profunctor_nat_iso.
  - exact (profunctor_nat_trans_id P).
  - intros y x.
    apply idisweq.
Defined.

Definition profunctor_nat_trans_comp
           {C₁ C₂ : category}
           {P₁ P₂ P₃ : profunctor C₁ C₂}
           (τ₁ : profunctor_nat_trans P₁ P₂)
           (τ₂ : profunctor_nat_trans P₂ P₃)
  : profunctor_nat_trans P₁ P₃
  := nat_trans_comp _ _ _ τ₁ τ₂.

(** * 6. Equality of profunctors *)
Definition path_profunctor_to_profunctor_nat_iso
           {C₁ C₂ : category}
           {P Q : profunctor C₁ C₂}
           (p : P = Q)
  : profunctor_nat_iso P Q.
Proof.
  induction p.
  exact (profunctor_nat_iso_id P).
Defined.

Definition isweq_path_profunctor_to_profunctor_nat_iso
           {C₁ C₂ : category}
           (P Q : profunctor C₁ C₂)
  : isweq (@path_profunctor_to_profunctor_nat_iso C₁ C₂ P Q).
Proof.
  use weqhomot.
  - refine (_
            ∘ make_weq
                _
                (is_univalent_functor_category
                   (category_binproduct C₂^op C₁)
                   HSET_univalent_category
                   (univalent_category_is_univalent _)
                   P Q))%weq.
    use weqfibtototal.
    intro τ.
    exact (is_profunctor_nat_iso_weq_is_z_iso τ).
  - intro p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_profunctor_nat_iso.
    }
    use eq_profunctor_nat_trans.
    intros y x h ; cbn.
    apply idpath.
Qed.

Definition path_profunctor_weq_profunctor_nat_iso
           {C₁ C₂ : category}
           (P Q : profunctor C₁ C₂)
  : (P = Q) ≃ profunctor_nat_iso P Q.
Proof.
  use make_weq.
  - exact path_profunctor_to_profunctor_nat_iso.
  - exact (isweq_path_profunctor_to_profunctor_nat_iso P Q).
Defined.
