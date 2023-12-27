Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Profunctors.Core.

Local Open Scope cat.


Section IdentityProfunctor.
  Context (C : category).

  Definition id_profunctor_data
    : profunctor_data C C.
  Proof.
    use make_profunctor_data.
    - exact (λ x y, x --> y).
    - exact (λ y₁ y₂ g x₁ x₂ f h, g · h · f).
  Defined.

  Proposition id_profunctor_laws
    : profunctor_laws id_profunctor_data.
  Proof.
    repeat split ; intros ; cbn.
    - rewrite id_left, id_right.
      apply idpath.
    - rewrite !assoc'.
      apply idpath.
    - apply homset_property.
  Qed.

  Definition id_profunctor
    : C ↛ C.
  Proof.
    use make_profunctor.
    - exact id_profunctor_data.
    - exact id_profunctor_laws.
  Defined.

  Proposition lmap_id_profunctor
              {x y₁ y₂ : C}
              (f : y₂ --> y₁)
              (h : y₁ --> x)
    : lmap id_profunctor f h = f · h.
  Proof.
    cbn.
    rewrite id_right.
    apply idpath.
  Qed.

  Proposition rmap_id_profunctor
              {x₁ x₂ y : C}
              (f : x₁ --> x₂)
              (h : y --> x₁)
    : rmap id_profunctor f h = h · f.
  Proof.
    cbn.
    rewrite id_left.
    apply idpath.
  Qed.
End IdentityProfunctor.

Section RepresentableProfunctor.
  Context {C₁ C₂ : category}
          (F : C₁ ⟶ C₂).

  Definition representable_profunctor_left_data
    : profunctor_data C₁ C₂.
  Proof.
    use make_profunctor_data.
    - exact (λ y x, y --> F x).
    - exact (λ y₁ y₂ g x₁ x₂ f h, g · h · #F f).
  Defined.

  Proposition representable_profunctor_left_laws
    : profunctor_laws representable_profunctor_left_data.
  Proof.
    repeat split ; intros ; cbn.
    - rewrite functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - rewrite functor_comp.
      rewrite !assoc'.
      apply idpath.
    - apply homset_property.
  Qed.

  Definition representable_profunctor_left
    : C₁ ↛ C₂.
  Proof.
    use make_profunctor.
    - exact representable_profunctor_left_data.
    - exact representable_profunctor_left_laws.
  Defined.

  Proposition lmap_representable_profunctor_left
              {x : C₁}
              {y₁ y₂ : C₂}
              (g : y₂ --> y₁)
              (h : y₁ --> F x)
    : lmap representable_profunctor_left g h = g · h.
  Proof.
    cbn.
    rewrite functor_id.
    rewrite id_right.
    apply idpath.
  Qed.

  Proposition rmap_representable_profunctor_left
              {x₁ x₂ : C₁}
              {y : C₂}
              (f : x₁ --> x₂)
              (h : y --> F x₁)
    : rmap representable_profunctor_left f h = h · #F f.
  Proof.
    cbn.
    rewrite id_left.
    apply idpath.
  Qed.

  Definition representable_profunctor_right_data
    : profunctor_data C₂ C₁.
  Proof.
    use make_profunctor_data.
    - exact (λ y x, F y --> x).
    - exact (λ y₁ y₂ g x₁ x₂ f h, #F g · h · f).
  Defined.

  Proposition representable_profunctor_right_laws
    : profunctor_laws representable_profunctor_right_data.
  Proof.
    repeat split ; intros ; cbn.
    - rewrite functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - rewrite functor_comp.
      rewrite !assoc'.
      apply idpath.
    - apply homset_property.
  Qed.

  Definition representable_profunctor_right
    : C₂ ↛ C₁.
  Proof.
    use make_profunctor.
    - exact representable_profunctor_right_data.
    - exact representable_profunctor_right_laws.
  Defined.

  Proposition lmap_representable_profunctor_right
              {x : C₂}
              {y₁ y₂ : C₁}
              (g : y₂ --> y₁)
              (h : F y₁ --> x)
    : lmap representable_profunctor_right g h = #F g · h.
  Proof.
    cbn.
    rewrite id_right.
    apply idpath.
  Qed.

  Proposition rmap_representable_profunctor_right
              {x₁ x₂ : C₂}
              {y : C₁}
              (f : x₁ --> x₂)
              (h : F y --> x₁)
    : rmap representable_profunctor_right f h = h · f.
  Proof.
    cbn.
    rewrite functor_id.
    rewrite id_left.
    apply idpath.
  Qed.
End RepresentableProfunctor.

Section PrecompProfunctor.
  Context {C₁ C₂ D₁ D₂ : category}
          (F : C₁ ⟶ C₂)
          (G : D₁ ⟶ D₂)
          (P : C₂ ↛ D₂).

  Definition precomp_profunctor_data
    : profunctor_data C₁ D₁.
  Proof.
    use make_profunctor_data.
    - exact (λ y x, P (G y) (F x)).
    - exact (λ y₁ y₂ g x₁ x₂ f h, lmap P (#G g) (rmap P (#F f) h)).
  Defined.

  Proposition precomp_profunctor_laws
    : profunctor_laws precomp_profunctor_data.
  Proof.
    repeat split ; intros ; cbn -[lmap rmap].
    - rewrite !functor_id.
      rewrite lmap_id, rmap_id.
      apply idpath.
    - rewrite !functor_comp.
      rewrite lmap_comp.
      rewrite rmap_comp.
      apply maponpaths.
      rewrite lmap_rmap.
      apply idpath.
    - apply setproperty.
  Qed.

  Definition precomp_profunctor
    : C₁ ↛ D₁.
  Proof.
    use make_profunctor.
    - exact precomp_profunctor_data.
    - exact precomp_profunctor_laws.
  Defined.

  Proposition lmap_precomp_profunctor
              {x : C₁}
              {y₁ y₂ : D₁}
              (f : y₂ --> y₁)
              (h : P (G y₁) (F x))
    : lmap precomp_profunctor f h = lmap P (#G f) h.
  Proof.
    cbn.
    rewrite functor_id.
    apply maponpaths.
    apply (eqtohomot (@functor_id _ _ P (_ ,, _))).
  Qed.

  Proposition rmap_precomp_profunctor
              {x₁ x₂ : C₁}
              {y : D₁}
              (f : x₁ --> x₂)
              (h : P (G y) (F x₁))
    : rmap precomp_profunctor f h = rmap P (#F f) h.
  Proof.
    cbn.
    rewrite functor_id.
    apply (eqtohomot (@functor_id _ _ P (_ ,, _))).
  Qed.
End PrecompProfunctor.

(** ** Transformations between profunctors *)
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
  : τ y₂ x₂ (lmap P g (rmap P f h))
    =
    lmap Q g (rmap Q f (τ y₁ x₁ h)).
Proof.
  refine (_
          @ eqtohomot
              (nat_trans_ax τ (y₁ ,, x₁) (y₂ ,, x₂) (g ,, f))
              h
          @ _) ; cbn.
  - apply maponpaths ; cbn.
    pose (eqtohomot
            (@functor_comp
               _ _
               P
               (y₁ ,, x₁) (y₁ ,, x₂) (y₂ ,, x₂)
               (identity _ ,, f)
               (g ,, identity _))
            h)
      as p.
    cbn in p.
    rewrite !id_right in p.
    exact (!p).
  - pose (eqtohomot
            (@functor_comp
               _ _
               Q
               (y₁ ,, x₁) (y₁ ,, x₂) (y₂ ,, x₂)
               (identity _ ,, f)
               (g ,, identity _))
            )
      as p.
    cbn in p.
    rewrite !id_right in p.
    apply p.
Qed.

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
     - apply maponpaths ; cbn.
       pose (eqtohomot
               (@functor_comp
                  _ _
                  P
                  (y₁ ,, x₁) (y₁ ,, x₂) (y₂ ,, x₂)
                  (identity _ ,, f)
                  (g ,, identity _))
               h)
         as p.
       cbn in p.
       rewrite !id_right in p.
       exact p.
     - pose (eqtohomot
               (@functor_comp
                  _ _
                  Q
                  (y₁ ,, x₁) (y₁ ,, x₂) (y₂ ,, x₂)
                  (identity _ ,, f)
                  (g ,, identity _))
            )
         as p.
       cbn in p.
       rewrite !id_right in p.
       apply (!(p _)).
   Qed.

  Definition make_profunctor_nat_trans
    : profunctor_nat_trans P Q.
  Proof.
    use make_nat_trans.
    - exact make_profunctor_nat_trans_data.
    - exact make_profunctor_nat_trans_law.
  Defined.
End MakeProfunctorNatTrans.


(* separate file on profunctor squares *)
Definition profunctor_square
           {C₁ C₂ D₁ D₂ : category}
           (F : C₁ ⟶ C₂)
           (G : D₁ ⟶ D₂)
           (P : D₁ ↛ C₁)
           (Q : D₂ ↛ C₂)
  : UU
  := profunctor_nat_trans P (precomp_profunctor G F Q).

Identity Coercion square_to_nat_trans : profunctor_square >-> profunctor_nat_trans.

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
  : τ y₂ x₂ (lmap P g (rmap P f h))
    =
    lmap Q (#F g) (rmap Q (#G f) (τ y₁ x₁ h)).
Proof.
  pose (eqtohomot (pr2 τ (y₁ ,, x₁) (y₂ ,, x₂) (g ,, f)) h) as p.
  cbn in p.
  refine (_ @ p).
  rewrite lmap_rmap_functor.
  apply idpath.
Qed.

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
       rewrite (profunctor_square_natural τ) ;
       rewrite (profunctor_square_natural θ) ;
       apply idpath).
Defined.

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
       rewrite (profunctor_square_natural θ) ;
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
       rewrite (profunctor_square_natural θ) ;
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
       rewrite profunctor_nat_trans_natural ;
       rewrite profunctor_square_natural ;
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
       rewrite profunctor_square_natural ;
       rewrite profunctor_nat_trans_natural ;
       apply idpath).
Defined.
