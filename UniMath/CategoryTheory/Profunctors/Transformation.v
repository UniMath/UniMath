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
 5.1. Identity and composition
 5.2. Left unitor
 5.3. Right unitor
 5.4. Associator
 5.5. Inverse laws
 6. Equality of profunctors

 *****************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Categories.HSET.SetCoends.
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

Proposition profunctor_nat_trans_lmap
            {C₁ C₂ : category}
            {P Q : profunctor C₁ C₂}
            (τ : profunctor_nat_trans P Q)
            {y₁ y₂ : C₂} {x : C₁}
            (g : y₂ --> y₁)
            (h : P y₁ x)
  : τ y₂ x (lmap P g h)
    =
    lmap Q g (τ y₁ x h).
Proof.
  rewrite lmap_functor.
  rewrite (profunctor_nat_trans_natural τ g (identity _) h).
  apply idpath.
Qed.

Proposition profunctor_nat_trans_rmap
            {C₁ C₂ : category}
            {P Q : profunctor C₁ C₂}
            (τ : profunctor_nat_trans P Q)
            {y : C₂} {x₁ x₂ : C₁}
            (f : x₁ --> x₂)
            (h : P y x₁)
  : τ y x₂ (rmap P f h)
    =
    rmap Q f (τ y x₁ h).
Proof.
  rewrite rmap_functor.
  rewrite (profunctor_nat_trans_natural τ (identity _) f h).
  apply idpath.
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
  rewrite profunctor_nat_trans_lmap.
  rewrite profunctor_nat_trans_rmap.
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

#[reversible=no] Coercion profunctor_nat_iso_to_profunctor_nat_trans
         {C₁ C₂ : category}
         {P Q : profunctor C₁ C₂}
         (τ : profunctor_nat_iso P Q)
  : profunctor_nat_trans P Q
  := pr1 τ.

#[reversible=no] Coercion profunctor_nat_iso_to_is_profunctor_nat_iso
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

(** * 5.1. Identity and composition *)
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

(** * 5.2. Left unitor *)
Definition lunitor_profunctor_nat_trans_mor
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
           (y : C₂)
           (x : C₁)
  : comp_profunctor (id_profunctor C₁) P y x → P y x.
Proof.
  use from_comp_profunctor_ob.
  - exact (λ z h h', rmap P h h').
  - abstract
      (intros z₁ z₂ f h h' ; cbn ;
       rewrite id_right ;
       rewrite rmap_comp ;
       apply idpath).
Defined.

Proposition lunitor_profunctor_nat_trans_mor_comm
            {C₁ C₂ : category}
            (P : profunctor C₁ C₂)
            {y : C₂}
            {x x' : C₁}
            (f : x' --> x)
            (h : P y x')
  : lunitor_profunctor_nat_trans_mor
      P
      y x
      (comp_profunctor_ob_in (id_profunctor C₁) P x' f h)
    =
    rmap P f h.
Proof.
  unfold lunitor_profunctor_nat_trans_mor.
  rewrite from_comp_profunctor_ob_comm.
  apply idpath.
Qed.

Proposition lunitor_profunctor_nat_trans_law
            {C₁ C₂ : category}
            (P : profunctor C₁ C₂)
  : profunctor_nat_trans_law (lunitor_profunctor_nat_trans_mor P).
Proof.
  intros y₁ y₂ x₁ x₂ g f h.
  use (mor_from_comp_profunctor_ob_eq
         (id_profunctor C₁) P
         y₁ x₁
         (λ h,
          lunitor_profunctor_nat_trans_mor
            P
            y₂ x₂
            (comp_profunctor_mor
               (id_profunctor C₁) P
               g (identity x₂)
               (comp_profunctor_mor
                  (id_profunctor C₁) P
                  (identity y₁) f
                  h)))
         (λ h, lmap P g (rmap P f (lunitor_profunctor_nat_trans_mor P y₁ x₁ h)))).
  clear h.
  intros y h h' ; cbn.
  rewrite !comp_profunctor_mor_comm.
  rewrite !lunitor_profunctor_nat_trans_mor_comm ; cbn.
  rewrite !id_left, !id_right.
  rewrite lmap_id.
  rewrite <- lmap_rmap.
  rewrite rmap_comp.
  apply idpath.
Qed.

Definition lunitor_profunctor_nat_trans
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
  : profunctor_nat_trans (comp_profunctor (id_profunctor C₁) P) P.
Proof.
  use make_profunctor_nat_trans.
  - exact (lunitor_profunctor_nat_trans_mor P).
  - exact (lunitor_profunctor_nat_trans_law P).
Defined.

Definition is_profunctor_nat_iso_lunitor_profunctor_nat_trans
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
  : is_profunctor_nat_iso (lunitor_profunctor_nat_trans P).
Proof.
  intros y x.
  use isweq_iso.
  - refine (comp_profunctor_ob_in _ _ _ _).
    exact (identity x).
  - abstract
      (intro h ;
       use (mor_from_comp_profunctor_ob_eq
              (id_profunctor C₁) P
              _ _
              (λ h,
               comp_profunctor_ob_in
                 (id_profunctor C₁) P
                 x (identity x)
                 (lunitor_profunctor_nat_trans P y x h))
              (idfun _)) ;
       clear h ;
       intros z h h' ; cbn ;
       rewrite lunitor_profunctor_nat_trans_mor_comm ;
       rewrite comp_profunctor_ob_in_comm ; cbn ;
       rewrite !id_right ;
       apply idpath).
  - abstract
      (intro h ; cbn ;
       rewrite lunitor_profunctor_nat_trans_mor_comm ;
       rewrite rmap_id;
       apply idpath).
Defined.

Definition linvunitor_profunctor_nat_trans
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
  : profunctor_nat_trans P (comp_profunctor (id_profunctor C₁) P)
  := inv_profunctor_nat_trans (is_profunctor_nat_iso_lunitor_profunctor_nat_trans P).

(** *  5.3. Right unitor *)
Definition runitor_profunctor_nat_trans_mor
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
           (y : C₂)
           (x : C₁)
  : comp_profunctor P (id_profunctor C₂) y x → P y x.
Proof.
  use from_comp_profunctor_ob.
  - exact (λ z h h', lmap P h' h).
  - abstract
      (intros z₁ z₂ f h h' ; cbn ;
       rewrite !id_left ;
       rewrite lmap_comp ;
       apply idpath).
Defined.

Proposition runitor_profunctor_nat_trans_mor_comm
            {C₁ C₂ : category}
            (P : profunctor C₁ C₂)
            {x : C₁}
            {y y' : C₂}
            (g : y --> y')
            (h : P y' x)
  : runitor_profunctor_nat_trans_mor
      P
      y x
      (comp_profunctor_ob_in P (id_profunctor C₂) y' h g)
    =
    lmap P g h.
Proof.
  unfold runitor_profunctor_nat_trans_mor.
  rewrite from_comp_profunctor_ob_comm.
  apply idpath.
Qed.

Proposition runitor_profunctor_nat_trans_law
            {C₁ C₂ : category}
            (P : profunctor C₁ C₂)
  : profunctor_nat_trans_law (runitor_profunctor_nat_trans_mor P).
Proof.
  intros y₁ y₂ x₁ x₂ g f h.
  cbn.
  use (mor_from_comp_profunctor_ob_eq
         P (id_profunctor C₂)
         y₁ x₁
         (λ h,
          runitor_profunctor_nat_trans_mor
            P
            y₂ x₂
            (comp_profunctor_mor
               P (id_profunctor C₂)
               g (identity x₂)
               (comp_profunctor_mor
                  P (id_profunctor C₂)
                  (identity y₁) f
                  h)))
         (λ h, lmap P g (rmap P f (runitor_profunctor_nat_trans_mor P y₁ x₁ h)))).
  clear h.
  intros y h h' ; cbn.
  rewrite !comp_profunctor_mor_comm.
  rewrite !runitor_profunctor_nat_trans_mor_comm ; cbn.
  rewrite !id_left, !id_right.
  rewrite rmap_id.
  rewrite <- lmap_rmap.
  rewrite lmap_comp.
  apply idpath.
Qed.

Definition runitor_profunctor_nat_trans
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
  : profunctor_nat_trans (comp_profunctor P (id_profunctor C₂)) P.
Proof.
  use make_profunctor_nat_trans.
  - exact (runitor_profunctor_nat_trans_mor P).
  - exact (runitor_profunctor_nat_trans_law P).
Defined.

Definition is_profunctor_nat_iso_runitor_profunctor_nat_trans
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
  : is_profunctor_nat_iso (runitor_profunctor_nat_trans P).
Proof.
  intros y x.
  use isweq_iso.
  - refine (λ h, comp_profunctor_ob_in _ _ _ h _).
    exact (identity y).
  - abstract
      (intro h ;
       use (mor_from_comp_profunctor_ob_eq
              P (id_profunctor C₂)
              _ _
              (λ h,
               comp_profunctor_ob_in
                 P (id_profunctor C₂)
                 _
                 (runitor_profunctor_nat_trans P y x h)
                 (identity y))
              (idfun _)) ;
       clear h ;
       intros z h h' ; cbn ;
       rewrite runitor_profunctor_nat_trans_mor_comm ;
       rewrite <- comp_profunctor_ob_in_comm ; cbn ;
       rewrite !id_left ;
       apply idpath).
  - abstract
      (intro h ; cbn ;
       rewrite runitor_profunctor_nat_trans_mor_comm ;
       rewrite lmap_id;
       apply idpath).
Defined.

Definition rinvunitor_profunctor_nat_trans
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
  : profunctor_nat_trans P (comp_profunctor P (id_profunctor C₂))
  := inv_profunctor_nat_trans (is_profunctor_nat_iso_runitor_profunctor_nat_trans P).

(** * 5.4. Associator *)
Definition associator_profunctor_nat_trans_mor_ob
           {C₁ C₂ C₃ C₄ : category}
           (P₁ : C₁ ↛ C₂)
           (P₂ : C₂ ↛ C₃)
           (P₃ : C₃ ↛ C₄)
           (z : C₄)
           (w : C₁)
           (x : C₂)
           (h : P₁ x w)
  : comp_profunctor P₂ P₃ z x → comp_profunctor (comp_profunctor P₁ P₂) P₃ z w.
Proof.
  use from_comp_profunctor_ob.
  - refine (λ y h' h'', comp_profunctor_ob_in _ _ y _ h'').
    exact (comp_profunctor_ob_in P₁ P₂ x h h').
  - abstract
      (intros y₁ y₂ g k k' ; cbn ;
       rewrite comp_profunctor_ob_in_comm ;
       cbn ;
       rewrite comp_profunctor_mor_comm ;
       rewrite rmap_id ;
       apply idpath).
Defined.

Proposition associator_profunctor_nat_trans_mor_ob_comm
            {C₁ C₂ C₃ C₄ : category}
            (P₁ : C₁ ↛ C₂)
            (P₂ : C₂ ↛ C₃)
            (P₃ : C₃ ↛ C₄)
            {z : C₄}
            {w : C₁}
            {x : C₂}
            {y : C₃}
            (h : P₁ x w)
            (k : P₂ y x)
            (l : P₃ z y)
  : associator_profunctor_nat_trans_mor_ob
      P₁ P₂ P₃
      z w x h
      (comp_profunctor_ob_in P₂ P₃ y k l)
    =
    comp_profunctor_ob_in (comp_profunctor P₁ P₂) P₃ y (comp_profunctor_ob_in P₁ P₂ x h k) l.
Proof.
  unfold associator_profunctor_nat_trans_mor_ob.
  rewrite from_comp_profunctor_ob_comm.
  apply idpath.
Qed.

Definition associator_profunctor_nat_trans_mor
           {C₁ C₂ C₃ C₄ : category}
           (P₁ : C₁ ↛ C₂)
           (P₂ : C₂ ↛ C₃)
           (P₃ : C₃ ↛ C₄)
           (z : C₄)
           (w : C₁)
  : comp_profunctor P₁ (comp_profunctor P₂ P₃) z w
    →
    comp_profunctor (comp_profunctor P₁ P₂) P₃ z w.
Proof.
  use from_comp_profunctor_ob.
  - exact (λ x h, associator_profunctor_nat_trans_mor_ob P₁ P₂ P₃ z w x h).
  - abstract
      (intros x₁ x₂ f h h' ; cbn in * ;
       use (mor_from_comp_profunctor_ob_eq
              P₂ P₃
              _ _
              (λ k,
               associator_profunctor_nat_trans_mor_ob
                 P₁ P₂ P₃ z w x₂ h
                 (comp_profunctor_mor P₂ P₃ (identity z) f k))
              (associator_profunctor_nat_trans_mor_ob P₁ P₂ P₃ z w x₁ (lmap P₁ f h))) ;
       clear h' ;
       intros y k k' ; cbn ;
       rewrite comp_profunctor_mor_comm ;
       rewrite lmap_id ;
       refine (associator_profunctor_nat_trans_mor_ob_comm P₁ P₂ P₃ h (rmap P₂ f k) k' @ _) ;
       refine (!_) ;
       etrans ; [ apply associator_profunctor_nat_trans_mor_ob_comm | ] ;
       rewrite comp_profunctor_ob_in_comm ;
       apply idpath).
Defined.

Proposition associator_profunctor_nat_trans_mor_comm
            {C₁ C₂ C₃ C₄ : category}
            (P₁ : C₁ ↛ C₂)
            (P₂ : C₂ ↛ C₃)
            (P₃ : C₃ ↛ C₄)
            (z : C₄)
            (w : C₁)
            (x : C₂)
            (h : P₁ x w)
            (kl : comp_profunctor_ob P₂ P₃ z x)
  : associator_profunctor_nat_trans_mor
      P₁ P₂ P₃
      z w
      (comp_profunctor_ob_in
         P₁ (comp_profunctor P₂ P₃)
         x
         h
         kl)
    =
    associator_profunctor_nat_trans_mor_ob P₁ P₂ P₃ _ _ x h kl.
Proof.
  unfold associator_profunctor_nat_trans_mor.
  rewrite from_comp_profunctor_ob_comm.
  apply idpath.
Qed.

Proposition associator_profunctor_nat_trans_law
            {C₁ C₂ C₃ C₄ : category}
            (P₁ : C₁ ↛ C₂)
            (P₂ : C₂ ↛ C₃)
            (P₃ : C₃ ↛ C₄)
  : profunctor_nat_trans_law (associator_profunctor_nat_trans_mor P₁ P₂ P₃).
Proof.
  intros z₁ z₂ w₁ w₂ f₄ f₁ h ; cbn.
  use (mor_from_comp_profunctor_ob_eq
         P₁ (comp_profunctor P₂ P₃)
         _ _
         (λ h,
          associator_profunctor_nat_trans_mor
            P₁ P₂ P₃ z₂ w₂
            (comp_profunctor_mor
               P₁ (comp_profunctor P₂ P₃)
               f₄ (identity w₂)
               (comp_profunctor_mor
                  P₁ (comp_profunctor P₂ P₃)
                  (identity z₁) f₁ h)))
         (λ h,
          comp_profunctor_mor
            (comp_profunctor P₁ P₂) P₃
            f₄ (identity w₂)
            (comp_profunctor_mor
               (comp_profunctor P₁ P₂) P₃ (identity z₁)
               f₁
               (associator_profunctor_nat_trans_mor P₁ P₂ P₃ z₁ w₁ h)))).
  clear h.
  intros x h kl ; cbn.
  use (mor_from_comp_profunctor_ob_eq
         P₂ P₃
         z₁ x
         (λ kl,
          associator_profunctor_nat_trans_mor
            P₁ P₂ P₃
            z₂ w₂
            (comp_profunctor_mor
               P₁ (comp_profunctor P₂ P₃)
               f₄ (identity w₂)
               (comp_profunctor_mor
                  P₁ (comp_profunctor P₂ P₃)
                  (identity z₁) f₁
                  (comp_profunctor_ob_in
                     P₁ (comp_profunctor P₂ P₃)
                     x h kl))))
         (λ kl,
          comp_profunctor_mor
            (comp_profunctor P₁ P₂) P₃
            f₄ (identity w₂)
            (comp_profunctor_mor
               (comp_profunctor P₁ P₂) P₃
               (identity z₁) f₁
               (associator_profunctor_nat_trans_mor
                  P₁ P₂ P₃
                  z₁ w₁
                  (comp_profunctor_ob_in
                     P₁ (comp_profunctor P₂ P₃)
                     x h kl))))).
  clear kl.
  intros y k l ; cbn.
  rewrite !comp_profunctor_mor_comm ; cbn.
  rewrite !comp_profunctor_mor_comm.
  rewrite !associator_profunctor_nat_trans_mor_comm.
  rewrite !rmap_id, !lmap_id.
  etrans.
  {
    exact (associator_profunctor_nat_trans_mor_ob_comm
             P₁ P₂ P₃
             (rmap P₁ f₁ h) k (lmap P₃ f₄ l)).
  }
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    exact (associator_profunctor_nat_trans_mor_ob_comm
             P₁ P₂ P₃
             h k l).
  }
  rewrite !comp_profunctor_mor_comm.
  cbn.
  rewrite lmap_id.
  rewrite !comp_profunctor_mor_comm.
  rewrite !lmap_id, !rmap_id.
  apply idpath.
Qed.

Definition associator_profunctor_nat_trans
           {C₁ C₂ C₃ C₄ : category}
           (P₁ : C₁ ↛ C₂)
           (P₂ : C₂ ↛ C₃)
           (P₃ : C₃ ↛ C₄)
  : profunctor_nat_trans
      (comp_profunctor P₁ (comp_profunctor P₂ P₃))
      (comp_profunctor (comp_profunctor P₁ P₂) P₃).
Proof.
  use make_profunctor_nat_trans.
  - exact (associator_profunctor_nat_trans_mor P₁ P₂ P₃).
  - exact (associator_profunctor_nat_trans_law P₁ P₂ P₃).
Defined.

Definition associator_profunctor_inv_mor_ob
           {C₁ C₂ C₃ C₄ : category}
           (P₁ : C₁ ↛ C₂)
           (P₂ : C₂ ↛ C₃)
           (P₃ : C₃ ↛ C₄)
           (z : C₄)
           (w : C₁)
           (y : C₃)
           (h : P₃ z y)
  : comp_profunctor_ob P₁ P₂ y w → comp_profunctor_ob P₁ (comp_profunctor P₂ P₃) z w.
Proof.
  use from_comp_profunctor_ob.
  - refine (λ x k l,
            comp_profunctor_ob_in _ _ _ k _).
    exact (comp_profunctor_ob_in _ _ y l h).
  - abstract
      (intros x₁ x₂ f k k' ; cbn ;
       rewrite <- comp_profunctor_ob_in_comm ;
       cbn ;
       rewrite comp_profunctor_mor_comm ;
       rewrite lmap_id ;
       apply idpath).
Defined.

Proposition associator_profunctor_inv_mor_ob_comm
            {C₁ C₂ C₃ C₄ : category}
            (P₁ : C₁ ↛ C₂)
            (P₂ : C₂ ↛ C₃)
            (P₃ : C₃ ↛ C₄)
            (z : C₄)
            (w : C₁)
            (y : C₃)
            (x : C₂)
            (h : P₃ z y)
            (k : P₁ x w)
            (l : P₂ y x)
  : associator_profunctor_inv_mor_ob
      P₁ P₂ P₃
      z w y h
      (comp_profunctor_ob_in P₁ P₂ x k l)
    =
    comp_profunctor_ob_in
      P₁ (comp_profunctor P₂ P₃)
      x
      k
      (comp_profunctor_ob_in P₂ P₃ y l h).
Proof.
  unfold associator_profunctor_inv_mor_ob.
  rewrite from_comp_profunctor_ob_comm.
  apply idpath.
Qed.

Definition associator_profunctor_inv_mor
           {C₁ C₂ C₃ C₄ : category}
           (P₁ : C₁ ↛ C₂)
           (P₂ : C₂ ↛ C₃)
           (P₃ : C₃ ↛ C₄)
           (z : C₄)
           (w : C₁)
  : comp_profunctor (comp_profunctor P₁ P₂) P₃ z w
    →
    comp_profunctor P₁ (comp_profunctor P₂ P₃) z w.
Proof.
  use from_comp_profunctor_ob.
  - exact (λ y kl h, associator_profunctor_inv_mor_ob P₁ P₂ P₃ z w y h kl).
  - abstract
      (intros y₁ y₂ f k l ; cbn in * ;
       use (mor_from_comp_profunctor_ob_eq
              P₁ P₂
              y₂ w
              (associator_profunctor_inv_mor_ob
                 P₁ P₂ P₃
                 z w y₂
                 (rmap P₃ f l))
              (λ k,
               associator_profunctor_inv_mor_ob
                 P₁ P₂ P₃
                 z w y₁
                 l (comp_profunctor_mor P₁ P₂ f (identity w) k))) ;
       clear k ;
       intros x h k ; cbn ;
       rewrite comp_profunctor_mor_comm ;
       rewrite !associator_profunctor_inv_mor_ob_comm ;
       rewrite comp_profunctor_ob_in_comm ;
       rewrite rmap_id ;
       apply idpath).
Defined.

Proposition associator_profunctor_inv_mor_comm
            {C₁ C₂ C₃ C₄ : category}
            (P₁ : C₁ ↛ C₂)
            (P₂ : C₂ ↛ C₃)
            (P₃ : C₃ ↛ C₄)
            (z : C₄)
            (w : C₁)
            (y : C₃)
            (h : P₃ z y)
            (kl : comp_profunctor_ob P₁ P₂ y w)
  : associator_profunctor_inv_mor
      P₁ P₂ P₃
      z w
      (comp_profunctor_ob_in (comp_profunctor P₁ P₂) P₃ y kl h)
    =
    associator_profunctor_inv_mor_ob P₁ P₂ P₃ z w y h kl.
Proof.
  unfold associator_profunctor_inv_mor.
  rewrite from_comp_profunctor_ob_comm.
  apply idpath.
Qed.

Lemma is_profunctor_nat_iso_associator_profunctor_nat_trans_left
      {C₁ C₂ C₃ C₄ : category}
      (P₁ : C₁ ↛ C₂)
      (P₂ : C₂ ↛ C₃)
      (P₃ : C₃ ↛ C₄)
      (z : C₄)
      (w : C₁)
      (h : comp_profunctor P₁ (comp_profunctor P₂ P₃) z w)
  : associator_profunctor_inv_mor
      P₁ P₂ P₃ z w
      (associator_profunctor_nat_trans
         P₁ P₂ P₃ z w h)
    =
    h.
Proof.
  use (mor_from_comp_profunctor_ob_eq
         P₁ (comp_profunctor P₂ P₃)
         z w
         (λ h,
          associator_profunctor_inv_mor
            P₁ P₂ P₃ z w
            (associator_profunctor_nat_trans
               P₁ P₂ P₃ z w h))
         (idfun _)).
  clear h.
  intros x h kl ; cbn.
  use (mor_from_comp_profunctor_ob_eq
         P₂ P₃
         z x
         (λ kl,
          associator_profunctor_inv_mor
            P₁ P₂ P₃ z w
            (associator_profunctor_nat_trans_mor
               P₁ P₂ P₃ z w
               (comp_profunctor_ob_in P₁ (comp_profunctor P₂ P₃) x h kl)))
         (λ kl, comp_profunctor_ob_in P₁ (comp_profunctor P₂ P₃) x h kl)).
  clear kl.
  intros y k l ; cbn.
  rewrite associator_profunctor_nat_trans_mor_comm.
  etrans.
  {
    apply maponpaths.
    apply associator_profunctor_nat_trans_mor_ob_comm.
  }
  etrans.
  {
    apply (associator_profunctor_inv_mor_comm P₁ P₂ P₃ z w y l).
  }
  rewrite associator_profunctor_inv_mor_ob_comm.
  apply idpath.
Qed.

Lemma is_profunctor_nat_iso_associator_profunctor_nat_trans_right
      {C₁ C₂ C₃ C₄ : category}
      (P₁ : C₁ ↛ C₂)
      (P₂ : C₂ ↛ C₃)
      (P₃ : C₃ ↛ C₄)
      (z : C₄)
      (w : C₁)
      (h : comp_profunctor (comp_profunctor P₁ P₂) P₃ z w)
  : associator_profunctor_nat_trans
      P₁ P₂ P₃ z w
      (associator_profunctor_inv_mor
         P₁ P₂ P₃ z w h)
    =
    h.
Proof.
  use (mor_from_comp_profunctor_ob_eq
         (comp_profunctor P₁ P₂) P₃
         z w
         (λ h,
          associator_profunctor_nat_trans
            P₁ P₂ P₃ z w
            (associator_profunctor_inv_mor
               P₁ P₂ P₃ z w h))
         (idfun _)).
  clear h.
  intros x h l ; cbn.
  use (mor_from_comp_profunctor_ob_eq
         P₁ P₂
         x w
         (λ h,
          associator_profunctor_nat_trans_mor P₁ P₂ P₃ z w
            (associator_profunctor_inv_mor P₁ P₂ P₃ z w
               (comp_profunctor_ob_in (comp_profunctor P₁ P₂) P₃ x h l)))
         (λ h, comp_profunctor_ob_in (comp_profunctor P₁ P₂) P₃ x h l)).
  clear h.
  intros y h k ; cbn.
  etrans.
  {
    apply maponpaths.
    apply associator_profunctor_inv_mor_comm.
  }
  etrans.
  {
    apply maponpaths.
    exact (associator_profunctor_inv_mor_ob_comm P₁ P₂ P₃ z w x y l h k).
  }
  rewrite associator_profunctor_nat_trans_mor_comm.
  exact (associator_profunctor_nat_trans_mor_ob_comm P₁ P₂ P₃ h k l).
Qed.

Definition is_profunctor_nat_iso_associator_profunctor_nat_trans
           {C₁ C₂ C₃ C₄ : category}
           (P₁ : C₁ ↛ C₂)
           (P₂ : C₂ ↛ C₃)
           (P₃ : C₃ ↛ C₄)
  : is_profunctor_nat_iso (associator_profunctor_nat_trans P₁ P₂ P₃).
Proof.
  intros z w.
  use isweq_iso.
  - exact (associator_profunctor_inv_mor P₁ P₂ P₃ z w).
  - exact (is_profunctor_nat_iso_associator_profunctor_nat_trans_left P₁ P₂ P₃ z w).
  - exact (is_profunctor_nat_iso_associator_profunctor_nat_trans_right P₁ P₂ P₃ z w).
Defined.

Definition inv_associator_profunctor_nat_trans
           {C₁ C₂ C₃ C₄ : category}
           (P₁ : C₁ ↛ C₂)
           (P₂ : C₂ ↛ C₃)
           (P₃ : C₃ ↛ C₄)
  : profunctor_nat_trans
      (comp_profunctor (comp_profunctor P₁ P₂) P₃)
      (comp_profunctor P₁ (comp_profunctor P₂ P₃))
  := inv_profunctor_nat_trans
       (is_profunctor_nat_iso_associator_profunctor_nat_trans P₁ P₂ P₃).

(** * 5.5. Inverse laws *)
Proposition inv_profunctor_nat_trans_left
            {C₁ C₂ : category}
            {P Q : profunctor C₁ C₂}
            {τ : profunctor_nat_trans P Q}
            (Hτ : is_profunctor_nat_iso τ)
  : profunctor_nat_trans_comp (inv_profunctor_nat_trans Hτ) τ
    =
    profunctor_nat_trans_id _.
Proof.
  use eq_profunctor_nat_trans.
  intros y x h ; cbn.
  apply (homotweqinvweq (make_weq _ (Hτ y x))).
Qed.

Proposition inv_profunctor_nat_trans_right
            {C₁ C₂ : category}
            {P Q : profunctor C₁ C₂}
            {τ : profunctor_nat_trans P Q}
            (Hτ : is_profunctor_nat_iso τ)
  : profunctor_nat_trans_comp τ (inv_profunctor_nat_trans Hτ)
    =
    profunctor_nat_trans_id _.
Proof.
  use eq_profunctor_nat_trans.
  intros y x h ; cbn.
  apply homotinvweqweq.
Qed.

(** * 5.6. Whiskering *)
Definition lwhisker_profunctor_nat_trans_mor
           {C₁ C₂ C₃ : category}
           (P : C₁ ↛ C₂)
           {Q₁ Q₂ : C₂ ↛ C₃}
           (τ : profunctor_nat_trans Q₁ Q₂)
           (z : C₃)
           (x : C₁)
  : comp_profunctor P Q₁ z x → comp_profunctor P Q₂ z x.
Proof.
  use from_comp_profunctor_ob.
  - exact (λ y h h', comp_profunctor_ob_in _ _ y h (τ z y h')).
  - abstract
      (intros y₁ y₂ g h h' ; cbn ;
       rewrite profunctor_nat_trans_rmap ;
       rewrite comp_profunctor_ob_in_comm ;
       apply idpath).
Defined.

Proposition lwhisker_profunctor_nat_trans_mor_comm
            {C₁ C₂ C₃ : category}
            (P : C₁ ↛ C₂)
            {Q₁ Q₂ : C₂ ↛ C₃}
            (τ : profunctor_nat_trans Q₁ Q₂)
            {z : C₃}
            {y : C₂}
            {x : C₁}
            (h : P y x)
            (h' : Q₁ z y)
  : lwhisker_profunctor_nat_trans_mor P τ z x (comp_profunctor_ob_in P Q₁ y h h')
    =
    comp_profunctor_ob_in P Q₂ y h (τ z y h').
Proof.
  unfold lwhisker_profunctor_nat_trans_mor.
  rewrite from_comp_profunctor_ob_comm.
  apply idpath.
Qed.

Proposition lwhisker_profunctor_nat_trans_law
            {C₁ C₂ C₃ : category}
            (P : C₁ ↛ C₂)
            {Q₁ Q₂ : C₂ ↛ C₃}
            (τ : profunctor_nat_trans Q₁ Q₂)
  : profunctor_nat_trans_law (lwhisker_profunctor_nat_trans_mor P τ).
Proof.
  intros z₁ z₂ x₁ x₂ k f h ; cbn in *.
  use (mor_from_comp_profunctor_ob_eq
         P Q₁
         z₁ x₁
         (λ h,
          lwhisker_profunctor_nat_trans_mor
            P τ z₂ x₂
            (comp_profunctor_mor
               P Q₁ k (identity x₂)
               (comp_profunctor_mor P Q₁ (identity z₁) f h)))
         (λ h,
          comp_profunctor_mor
            P Q₂ k (identity x₂)
            (comp_profunctor_mor
               P Q₂ (identity z₁) f
               (lwhisker_profunctor_nat_trans_mor P τ z₁ x₁ h)))).
  clear h.
  intros y h h' ; cbn.
  rewrite !comp_profunctor_mor_comm.
  rewrite rmap_id, lmap_id.
  etrans.
  {
    exact (lwhisker_profunctor_nat_trans_mor_comm P τ (rmap P f h) (lmap Q₁ k h')).
  }
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    exact (lwhisker_profunctor_nat_trans_mor_comm P τ h h').
  }
  rewrite !comp_profunctor_mor_comm.
  rewrite rmap_id, lmap_id.
  rewrite profunctor_nat_trans_lmap.
  apply idpath.
Qed.

Definition lwhisker_profunctor_nat_trans
           {C₁ C₂ C₃ : category}
           (P : C₁ ↛ C₂)
           {Q₁ Q₂ : C₂ ↛ C₃}
           (τ : profunctor_nat_trans Q₁ Q₂)
  : profunctor_nat_trans
      (comp_profunctor P Q₁)
      (comp_profunctor P Q₂).
Proof.
  use make_profunctor_nat_trans.
  - exact (lwhisker_profunctor_nat_trans_mor P τ).
  - exact (lwhisker_profunctor_nat_trans_law P τ).
Defined.

Definition rwhisker_profunctor_nat_trans_mor
           {C₁ C₂ C₃ : category}
           {P₁ P₂ : C₁ ↛ C₂}
           (τ : profunctor_nat_trans P₁ P₂)
           (Q : C₂ ↛ C₃)
           (z : C₃)
           (x : C₁)
  : comp_profunctor P₁ Q z x → comp_profunctor P₂ Q z x.
Proof.
  use from_comp_profunctor_ob.
  - exact (λ y h h', comp_profunctor_ob_in _ _ y (τ y x h) h').
  - abstract
      (intros y₁ y₂ g h h' ; cbn ;
       rewrite profunctor_nat_trans_lmap ;
       rewrite comp_profunctor_ob_in_comm ;
       apply idpath).
Defined.

Proposition rwhisker_profunctor_nat_trans_mor_comm
            {C₁ C₂ C₃ : category}
            {P₁ P₂ : C₁ ↛ C₂}
            (τ : profunctor_nat_trans P₁ P₂)
            (Q : C₂ ↛ C₃)
            {z : C₃}
            {y : C₂}
            {x : C₁}
            (h : P₁ y x)
            (h' : Q z y)
  : rwhisker_profunctor_nat_trans_mor τ Q z x (comp_profunctor_ob_in P₁ Q y h h')
    =
    comp_profunctor_ob_in P₂ Q y (τ y x h) h'.
Proof.
  unfold rwhisker_profunctor_nat_trans_mor.
  rewrite from_comp_profunctor_ob_comm.
  apply idpath.
Qed.

Proposition rwhisker_profunctor_nat_trans_law
            {C₁ C₂ C₃ : category}
            {P₁ P₂ : C₁ ↛ C₂}
            (τ : profunctor_nat_trans P₁ P₂)
            (Q : C₂ ↛ C₃)
  : profunctor_nat_trans_law (rwhisker_profunctor_nat_trans_mor τ Q).
Proof.
  intros z₁ z₂ x₁ x₂ k f h ; cbn in *.
  use (mor_from_comp_profunctor_ob_eq
         P₁ Q
         z₁ x₁
         (λ h,
          rwhisker_profunctor_nat_trans_mor
            τ Q z₂ x₂
            (comp_profunctor_mor
               P₁ Q
               k (identity x₂)
               (comp_profunctor_mor P₁ Q (identity z₁) f h)))
         (λ h,
          comp_profunctor_mor
            P₂ Q k (identity x₂)
            (comp_profunctor_mor
               P₂ Q (identity z₁) f
               (rwhisker_profunctor_nat_trans_mor τ Q z₁ x₁ h)))).
  clear h.
  intros y h h' ; cbn.
  rewrite !comp_profunctor_mor_comm.
  rewrite rmap_id, lmap_id.
  etrans.
  {
    exact (rwhisker_profunctor_nat_trans_mor_comm τ Q (rmap P₁ f h) (lmap Q k h')).
  }
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    exact (rwhisker_profunctor_nat_trans_mor_comm τ Q h h').
  }
  rewrite !comp_profunctor_mor_comm.
  rewrite rmap_id, lmap_id.
  rewrite profunctor_nat_trans_rmap.
  apply idpath.
Qed.

Definition rwhisker_profunctor_nat_trans
           {C₁ C₂ C₃ : category}
           {P₁ P₂ : C₁ ↛ C₂}
           (τ : profunctor_nat_trans P₁ P₂)
           (Q : C₂ ↛ C₃)
  : profunctor_nat_trans
      (comp_profunctor P₁ Q)
      (comp_profunctor P₂ Q).
Proof.
  use make_profunctor_nat_trans.
  - exact (rwhisker_profunctor_nat_trans_mor τ Q).
  - exact (rwhisker_profunctor_nat_trans_law τ Q).
Defined.

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
