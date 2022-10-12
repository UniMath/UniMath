(** **********************************************************
Contents:
        - Definition of the Kleisli category of a monad.
        - The canonical adjunction between a category C and the Kleisli
          category of a monad on C.
TODO:
        - Show that this definition is equivalent to the Kleisli category of a
          relative monad with respect to the identity functor.


Written by: Brandon Doherty (July 2018)
************************************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Section Monad_Lemmas.

(*A couple of lemmas involving bind*)

Lemma bind_comp_η {C : category} {T : Monad C} {a b : C} (f : C ⟦a , b⟧) :
  bind (f · (η T) b) = # T f.
Proof.
  unfold bind; rewrite functor_comp.
  rewrite <- assoc.
  rewrite <- id_right.
  apply cancel_precomposition.
  apply bind_η.
Qed.

Lemma bind_identity {C : category} {T : Monad C} (a : C) :
  bind (identity (T a)) = (μ T) a.
Proof.
  unfold bind.
  rewrite functor_id.
  apply id_left.
Qed.

End Monad_Lemmas.

Section Kleisli_Categories.

Definition Kleisli_precat_ob_mor_monad {C : precategory_data} (T : Monad_data C) :
  precategory_ob_mor.
Proof.
  use tpair.
  - exact (ob C).
  - intros X Y.
    exact (X --> T Y).
Defined.

Definition Kleisli_precat_data_monad {C : precategory_data} (T : Monad_data C) :
  precategory_data.
Proof.
  use make_precategory_data.
  - exact (Kleisli_precat_ob_mor_monad T).
  - intro c.
    exact (η T c).
  - intros a b c f g.
    exact (f · (bind g)).
Defined.

Lemma Kleisli_precat_monad_is_precat {C : category} (T : Monad C) :
  is_precategory (Kleisli_precat_data_monad T).
Proof.
  apply is_precategory_one_assoc_to_two.
  split.
  - split.
    + intros a b f.
      unfold identity; unfold compose; cbn.
      apply η_bind.
    + intros a b f.
      unfold identity; unfold compose; cbn.
      rewrite <- id_right.
      apply cancel_precomposition.
      apply bind_η.
  - intros a b c d f g h.
    unfold compose; cbn.
    rewrite <- bind_bind.
    apply assoc.
Defined.

Definition Kleisli_precat_monad {C : category} (T : Monad C) : precategory := (Kleisli_precat_data_monad T,,Kleisli_precat_monad_is_precat T).

Lemma Kleisli_precat_monad_has_homsets {C : category} (T : Monad C)
      (hs : has_homsets C) : has_homsets (Kleisli_precat_data_monad T).
Proof.
  intros a b.
  apply hs.
Defined.

Definition Kleisli_cat_monad {C : category} (T : Monad C): category
  := (Kleisli_precat_monad T,, Kleisli_precat_monad_has_homsets T
  (homset_property C)).

(*TODO: show that this is equivalent to the definition of the Kleisli category of a relative monad with respect to the identity*)

(*The canonical adjunction between C and the Kleisli category of a monad on C*)

Definition Left_Kleisli_functor_data {C : category} (T: Monad C) :
  functor_data C (Kleisli_precat_monad T).
Proof.
  use make_functor_data.
  - apply idfun.
  - intros a b f; unfold idfun.
    exact (f · (η T) b).
Defined.

Lemma Left_Kleisli_is_functor {C : category} (T: Monad C) :
  is_functor (Left_Kleisli_functor_data T).
Proof.
  split.
  - intro a.
    unfold Left_Kleisli_functor_data; cbn.
    apply id_left.
  - intros a b c f g.
    unfold Left_Kleisli_functor_data; cbn.
    do 2 (rewrite <- assoc).
    apply cancel_precomposition.
    apply pathsinv0.
    apply η_bind.
Defined.

Definition Left_Kleisli_functor {C : category} (T : Monad C) :
  functor C (Kleisli_cat_monad T)
  := (Left_Kleisli_functor_data T,,Left_Kleisli_is_functor T).

Definition Right_Kleisli_functor_data {C : category} (T : Monad C) :
  functor_data (Kleisli_cat_monad T) C.
Proof.
  use make_functor_data.
  - exact T.
  - intros a b.
    apply bind.
Defined.

Lemma Right_Kleisli_is_functor {C : category} (T : Monad C) :
  is_functor (Right_Kleisli_functor_data T).
Proof.
  use tpair.
  - intro a.
    unfold Right_Kleisli_functor_data; unfold identity;
    unfold functor_on_morphisms; cbn.
    apply bind_η.
  - intros a b c f g; cbn.
    apply pathsinv0.
    apply bind_bind.
Defined.

Definition Right_Kleisli_functor {C : category} (T : Monad C) :
  functor (Kleisli_cat_monad T) C
  := (Right_Kleisli_functor_data T,,Right_Kleisli_is_functor T).

(*Composition of the left and right Kleisli functors is equal to T as a functor*)

Definition Kleisli_functor_left_right_compose {C : category} (T : Monad C) :
  (Left_Kleisli_functor T) ∙ (Right_Kleisli_functor T) = T.
Proof.
  use functor_eq.
  - apply homset_property.
  - use functor_data_eq_from_nat_trans.
    + intro a; apply idpath.
    + intros a b f; cbn.
      rewrite id_right.
      rewrite id_left.
      apply bind_comp_η.
Defined.

(*Showing that these functors are adjoints*)

Definition Kleisli_homset_iso {C : category} (T : Monad C) : natural_hom_weq (Left_Kleisli_functor T) (Right_Kleisli_functor T).
Proof.
  use tpair.
  - intros a b; cbn.
    apply idweq.
  - cbn; split.
    + intros.
      rewrite <- assoc.
      apply cancel_precomposition.
      apply η_bind.
    + intros; apply idpath.
Defined.

Definition Kleisli_functors_are_adjoints {C : category} (T : Monad C) : are_adjoints (Left_Kleisli_functor T) (Right_Kleisli_functor T) := adj_from_nathomweq (Kleisli_homset_iso T).

Definition Left_Kleisli_is_left_adjoint {C : category} (T : Monad C)
  : is_left_adjoint (Left_Kleisli_functor T)
    := are_adjoints_to_is_left_adjoint (Left_Kleisli_functor T)
    (Right_Kleisli_functor T) (Kleisli_functors_are_adjoints T).

Definition Right_Kleisli_is_right_adjoint {C : category} (T : Monad C)
  : is_right_adjoint (Right_Kleisli_functor T)
    := are_adjoints_to_is_right_adjoint (Left_Kleisli_functor T)
    (Right_Kleisli_functor T) (Kleisli_functors_are_adjoints T).

Theorem Kleisli_adjunction_monad_eq {C : category} (T : Monad C)  : Monad_from_adjunction (Kleisli_functors_are_adjoints T) = T.
Proof.
  use Monad_eq_raw_data.
  apply total2_paths_equiv; use tpair.
  + cbn.
    apply idpath.
  + cbn.
    apply total2_paths_equiv; use tpair.
    * cbn.
      apply total2_paths_equiv; use tpair.
      -- cbn.
         do 2 (apply funextsec; intro).
         apply funextfun; intro f.
         cbn.
         apply bind_comp_η.
      -- cbn.
         rewrite transportf_const.
         cbn.
         apply funextsec; intro c.
         apply bind_identity.
    * cbn.
      rewrite transportf_const.
      apply idpath.
Defined.

End Kleisli_Categories.

(**
 Two useful laws
 *)
Definition η_η_bind
           {C : category}
           (M : Monad C)
           (x : C)
  : η M x · η M _ · bind (identity _) = η M x.
Proof.
  rewrite bind_identity.
  rewrite !assoc'.
  refine (_ @ id_right _).
  apply maponpaths.
  apply Monad_law1.
Qed.

Definition η_bind_bind
           {C : category}
           (M : Monad C)
           (x : C)
  : η M (M(M x)) · bind (identity _) · bind (identity _)
    =
    μ M x · η M (M x) · bind (identity _).
Proof.
  rewrite !bind_identity.
  rewrite Monad_law1, id_left.
  rewrite !assoc'.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    apply Monad_law1.
  }
  apply id_right.
Qed.

(** The universal mapping property of the Kleisli category *)
Section KleisliUMP1.
  Context {C₁ C₂ : category}
          (m : Monad C₁)
          (F : C₁ ⟶ C₂)
          (γ : m ∙ F ⟹ F)
          (p₁ : ∏ (x : C₁), #F (η m x) · γ x = identity _)
          (p₂ : ∏ (x : C₁), γ _ · γ x = #F (μ m x) · γ x).

  Definition functor_from_kleisli_cat_monad_data
    : functor_data (Kleisli_cat_monad m) C₂.
  Proof.
    use make_functor_data.
    - exact F.
    - exact (λ x y f, #F f · γ y).
  Defined.

  Definition functor_from_kleisli_cat_monad_is_functor
    : is_functor functor_from_kleisli_cat_monad_data.
  Proof.
    split.
    - intro x ; cbn.
      apply p₁.
    - intros x y z f g ; cbn ; unfold bind.
      rewrite !functor_comp.
      rewrite !assoc'.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!(p₂ z)).
      }
      rewrite !assoc.
      apply maponpaths_2.
      exact (nat_trans_ax γ _ _ g).
  Qed.

  Definition functor_from_kleisli_cat_monad
    : Kleisli_cat_monad m ⟶ C₂.
  Proof.
    use make_functor.
    - exact functor_from_kleisli_cat_monad_data.
    - exact functor_from_kleisli_cat_monad_is_functor.
  Defined.

  Definition functor_from_kleisli_cat_monad_nat_trans
    : Left_Kleisli_functor m ∙ functor_from_kleisli_cat_monad ⟹ F.
  Proof.
    use make_nat_trans.
    - exact (λ x, identity _).
    - abstract
        (intros x y f ; cbn ;
         rewrite id_right, id_left ;
         rewrite functor_comp ;
         rewrite !assoc' ;
         etrans ;
           [ apply maponpaths ;
             exact (p₁ y)
           | ] ;
         apply id_right).
  Defined.

  Definition functor_from_kleisli_cat_monad_nat_trans_is_z_iso
    : is_nat_z_iso functor_from_kleisli_cat_monad_nat_trans.
  Proof.
    intro x.
    apply is_z_isomorphism_identity.
  Defined.
End KleisliUMP1.

Definition kleisli_monad_nat_trans
           {C : category}
           (m : Monad C)
  : m ∙ Left_Kleisli_functor m ⟹ Left_Kleisli_functor m.
Proof.
  use make_nat_trans.
  - exact (λ x, identity (m x)).
  - abstract
      (intros x y f ; cbn ; unfold bind ;
       rewrite functor_id, !id_left ;
       rewrite functor_comp ;
       rewrite !assoc' ;
       apply maponpaths ;
       exact (Monad_law1 _ @ !(Monad_law2 _))).
Defined.

Section KleisliUMP2.
  Context {C₁ C₂ : category}
          (m : Monad C₁)
          {G₁ G₂ : Kleisli_cat_monad m ⟶ C₂}
          (α : Left_Kleisli_functor m ∙ G₁ ⟹ Left_Kleisli_functor m ∙ G₂)
          (p : ∏ (x : C₁),
               #G₁ (kleisli_monad_nat_trans m x) · α x
               =
               α (m x) · # G₂ (kleisli_monad_nat_trans m x)).

  Definition nat_trans_from_kleisli_cat_monad_is_nat_trans
    : is_nat_trans G₁ G₂ (λ x, α x).
  Proof.
    intros x y f.
    pose (maponpaths (λ z, z · # G₂ (identity (m y))) (nat_trans_ax α _ _ f)) as q.
    cbn in q.
    refine (_ @ q @ _) ; clear q.
    - rewrite !assoc'.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (!(p y)).
      }
      cbn.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!(functor_comp G₁ _ _) @ _).
      apply maponpaths.
      cbn ; unfold bind.
      rewrite functor_id, id_left.
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      apply Monad_law1.
    - rewrite !assoc'.
      apply maponpaths.
      refine (!(functor_comp G₂ _ _) @ _).
      apply maponpaths.
      cbn ; unfold bind.
      rewrite functor_id, id_left.
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      apply Monad_law1.
  Qed.

  Definition nat_trans_from_kleisli_cat_monad
    : G₁ ⟹ G₂.
  Proof.
    use make_nat_trans.
    - exact (λ x, α x).
    - exact nat_trans_from_kleisli_cat_monad_is_nat_trans.
  Defined.

  Definition pre_whisker_nat_trans_from_kleisli_cat_monad
    : pre_whisker _ nat_trans_from_kleisli_cat_monad = α.
  Proof.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro ; cbn.
    apply idpath.
  Qed.

  Definition nat_trans_from_kleisli_cat_monad_unique
             {β₁ β₂ : G₁ ⟹ G₂}
             (q₁ : pre_whisker _ β₁ = α)
             (q₂ : pre_whisker _ β₂ = α)
    : β₁ = β₂.
  Proof.
    use nat_trans_eq.
    {
      apply homset_property.
    }
    intro ; cbn.
    exact (nat_trans_eq_pointwise q₁ x @ !(nat_trans_eq_pointwise q₂ x)).
  Qed.
End KleisliUMP2.
