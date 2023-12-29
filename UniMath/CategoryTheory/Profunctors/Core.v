(** * Profunctors *)

(** Set-valued profunctors *)

(** References:
    - https://link.springer.com/content/pdf/10.1007/BFb0060443.pdf
    - https://bartoszmilewski.com/2017/03/29/ends-and-coends/
 *)

(** ** Contents

  - Definition
  - Dinatural transformations
    - Dinatural transformation from a natural transformation
  - (Co)ends
    - Wedges
    - Ends
      - Accessors/coercions
    - Cowedges
    - Coends

 *)

Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.categories.HSET.All.

Local Open Scope cat.

(** ** Definition *)

(** A profunctor (or distributor) [C ↛ D] is a functor [D^op × C → HSET]. *)
Definition profunctor (C D : category) : UU :=
  functor (category_binproduct (op_category D) C) HSET_univalent_category.

Infix "↛" := profunctor (at level 99, only parsing) : cat. (* \nrightarrow *)

(** A builder for profunctors *)
Definition profunctor_data
           (C₁ C₂ : category)
  : UU
  := ∑ (Fo : C₂ → C₁ → UU),
     ∏ (y₁ y₂ : C₂)
       (g : y₂ --> y₁)
       (x₁ x₂ : C₁)
       (f : x₁ --> x₂),
     Fo y₁ x₁ → Fo y₂ x₂.

Definition make_profunctor_data
           {C₁ C₂ : category}
           (Fo : C₂ → C₁ → UU)
           (Fm : ∏ (y₁ y₂ : C₂)
                   (g : y₂ --> y₁)
                   (x₁ x₂ : C₁)
                   (f : x₁ --> x₂),
                 Fo y₁ x₁ → Fo y₂ x₂)
  : profunctor_data C₁ C₂
  := Fo ,, Fm.

Definition profunctor_laws
           {C₁ C₂ : category}
           (F : profunctor_data C₁ C₂)
  : UU
  := (∏ (y : C₂)
        (x : C₁)
        (h : pr1 F y x),
      pr2 F _ _ (identity y) _ _ (identity x) h = h)
     ×
     (∏ (y₁ y₂ y₃ : C₂)
        (g₁ : y₂ --> y₁)
        (g₂ : y₃ --> y₂)
        (x₁ x₂ x₃ : C₁)
        (f₁ : x₁ --> x₂)
        (f₂ : x₂ --> x₃)
        (h : pr1 F y₁ x₁),
      pr2 F _ _ (g₂ · g₁) _ _ (f₁ · f₂) h
      =
      pr2 F _ _ g₂ _ _ f₂ (pr2 F _ _ g₁ _ _ f₁ h))
     ×
     (∏ (y : C₂)
        (x : C₁),
      isaset (pr1 F y x)).

Section ProfunctorBuilder.
  Context {C₁ C₂ : category}
          (F : profunctor_data C₁ C₂)
          (HF : profunctor_laws F).

  Definition make_data_of_profunctor
    : functor_data (category_binproduct C₂^op C₁) HSET.
  Proof.
    use make_functor_data.
    - refine (λ xy, make_hSet (pr1 F (pr1 xy) (pr2 xy)) _).
      apply HF.
    - exact (λ xy₁ xy₂ fg h, pr2 F _ _ (pr1 fg) _ _ (pr2 fg) h).
  Defined.

  Proposition make_laws_profunctor
    : is_functor make_data_of_profunctor.
  Proof.
    split ; intro ; intros ; use funextsec ; intro ; cbn.
    - apply HF.
    - apply HF.
  Qed.

  Definition make_profunctor
    : C₁ ↛ C₂.
  Proof.
    use make_functor.
    - exact make_data_of_profunctor.
    - exact make_laws_profunctor.
  Defined.
End ProfunctorBuilder.

(** Accessors for profunctors *)
Definition profunctor_point
           {C₁ C₂ : category}
           (P : C₁ ↛ C₂)
           (y : C₂)
           (x : C₁)
  : hSet
  := pr1 P (y ,, x).

Coercion profunctor_point : profunctor >-> Funclass.

Definition profunctor_on_morphisms
           {C₁ C₂ : category}
           (P : C₁ ↛ C₂)
           {y₁ y₂ : C₂}
           (g : y₂ --> y₁)
           {x₁ x₂ : C₁}
           (f : x₁ --> x₂)
           (h : P y₁ x₁)
  : P y₂ x₂
  := @functor_on_morphisms _ _ (P : _ ⟶ _) (_ ,, _) (_ ,, _) (g ,, f) h.

Notation "P #[ g , f ] h" := (profunctor_on_morphisms P g f h) (at level 60) : cat.

Proposition profunctor_id
            {C₁ C₂ : category}
            (P : C₁ ↛ C₂)
            {y : C₂}
            {x : C₁}
            (h : P y x)
  : P #[ identity _ , identity _ ] h = h.
Proof.
  exact (eqtohomot (functor_id P _) h).
Qed.

Proposition profunctor_comp
            {C₁ C₂ : category}
            (P : C₁ ↛ C₂)
            {y₁ y₂ y₃: C₂}
            (g₂ : y₃ --> y₂) (g₁ : y₂ --> y₁)
            {x₁ x₂ x₃ : C₁}
            (f₁ : x₁ --> x₂) (f₂ : x₂ --> x₃)
            (h : P y₁ x₁)
  : P #[ g₂ · g₁ , f₁ · f₂ ] h = P #[ g₂ , f₂ ] (P #[ g₁ , f₁ ] h).
Proof.
  exact (eqtohomot (@functor_comp _ _ P (_ ,, _) (_ ,, _) (_ ,, _) (_ ,, _) (_ ,, _)) h).
Qed.

(** Map over the first argument contravariantly.
    Inspired by Data.Profunctor in Haskell. *)
Definition lmap {C D : category} (F : C ↛ D) {a : ob C} {b b' : ob D} (g : b' --> b)
  : HSET ⟦ F b a , F b' a ⟧
  := λ h, F #[ g , identity _ ] h.

(** Map over the second argument covariantly.
    Inspired by Data.Profunctor in Haskell. *)
Definition rmap {C D : category} (F : C ↛ D) {a a' : ob C} {b : ob D} (f : a --> a')
  : HSET ⟦ F b a , F b a' ⟧
  := λ h, F #[ identity _ , f ] h.

(** Laws for `rmap` and `lmap` *)
Definition lmap_id
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
           {x : C₁}
           {y : C₂}
           (z : P y x)
  : lmap P (identity y) z = z.
Proof.
  unfold lmap.
  rewrite profunctor_id.
  apply idpath.
Qed.

Definition rmap_id
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
           {x : C₁}
           {y : C₂}
           (z : P y x)
  : rmap P (identity x) z = z.
Proof.
  unfold rmap.
  rewrite profunctor_id.
  apply idpath.
Qed.

Definition lmap_comp
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
           {x : C₁}
           {y₁ y₂ y₃ : C₂}
           (g₁ : y₁ --> y₂)
           (g₂ : y₂ --> y₃)
           (z : P y₃ x)
  : lmap P (g₁ · g₂) z
    =
    lmap P g₁ (lmap P g₂ z).
Proof.
  unfold lmap.
  rewrite <- profunctor_comp.
  rewrite id_right.
  apply idpath.
Qed.

Definition rmap_comp
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
           {x₁ x₂ x₃ : C₁}
           {y : C₂}
           (f₁ : x₁ --> x₂)
           (f₂ : x₂ --> x₃)
           (z : P y x₁)
  : rmap P (f₁ · f₂) z
    =
    rmap P f₂ (rmap P f₁ z).
Proof.
  unfold rmap.
  rewrite <- profunctor_comp.
  rewrite id_right.
  apply idpath.
Qed.

Definition lmap_rmap
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           (f : x₁ --> x₂)
           (g : y₂ --> y₁)
           (z : P y₁ x₁)
  : lmap P g (rmap P f z) = rmap P f (lmap P g z).
Proof.
  unfold lmap, rmap.
  rewrite <- !profunctor_comp.
  rewrite !id_right, !id_left.
  apply idpath.
Qed.

Definition rmap_lmap
           {C₁ C₂ : category}
           (P : profunctor C₁ C₂)
           {x₁ x₂ : C₁}
           {y₁ y₂ : C₂}
           (f : x₁ --> x₂)
           (g : y₂ --> y₁)
           (z : P y₁ x₁)
  : rmap P f (lmap P g z) = lmap P g (rmap P f z).
Proof.
  rewrite lmap_rmap.
  apply idpath.
Qed.

Proposition lmap_functor
            {C D : category}
            (F : C ↛ D)
            {a : ob C} {b b' : ob D}
            (g : b' --> b)
            (h : F b a)
  : lmap F g h = F #[ g , identity _ ] h.
Proof.
  apply idpath.
Qed.

Proposition rmap_functor
            {C D : category}
            (F : C ↛ D)
            {a a' : ob C} {b : ob D}
            (f : a --> a')
            (h : F b a)
  : rmap F f h = F #[ identity _ , f ] h.
Proof.
  apply idpath.
Qed.

Proposition lmap_rmap_functor
            {C₁ C₂ : category}
            (P : profunctor C₁ C₂)
            {x₁ x₂ : C₁}
            {y₁ y₂ : C₂}
            (f : x₁ --> x₂)
            (g : y₂ --> y₁)
            (z : P y₁ x₁)
  : lmap P g (rmap P f z)
    =
    P #[ g , f ] z.
Proof.
  unfold lmap, rmap ; cbn.
  rewrite <- profunctor_comp.
  rewrite !id_right.
  apply idpath.
Qed.

(** ** Dinatural transformations *)

Section Dinatural.

  Context {C : category}.

  Definition dinatural_transformation_data (f : C ↛ C) (g : C ↛ C) : UU :=
    ∏ a : C, f a a → g a a.

  Definition is_dinatural {F : C ↛ C} {G : C ↛ C}
             (data : dinatural_transformation_data F G) : hProp.
  Proof.
    use make_hProp.
    - exact (∏ (a b : ob C) (f : a --> b),
               lmap F f · data a · rmap G f = rmap F f · data b · lmap G f).
    - abstract (do 3 (apply impred; intro); apply homset_property).
  Defined.

  Definition dinatural_transformation (f : C ↛ C) (g : C ↛ C) : UU :=
    ∑ d : dinatural_transformation_data f g, is_dinatural d.

  (** The second projection is made opaque for efficiency.
      Nothing is lost because it's an [hProp]. *)
  Definition make_dinatural_transformation {F : C ↛ C} {G : C ↛ C}
      (data : dinatural_transformation_data F G)
      (is_dinat : is_dinatural data) : dinatural_transformation F G.
  Proof.
    use tpair.
    - assumption.
    - abstract assumption.
  Defined.

  Section Accessors.
    Context {f : C ↛ C} {g : C ↛ C} (d : dinatural_transformation f g).

    Definition dinatural_transformation_get_data :
      ∏ a : C, HSET ⟦ f a a , g a a ⟧ := pr1 d.

    Definition dinatural_transformation_is_dinatural :
      is_dinatural dinatural_transformation_get_data := pr2 d.
  End Accessors.

  Coercion dinatural_transformation_get_data : dinatural_transformation >-> Funclass.

  (** See below for the non-local notation *)
  Local Notation "F ⇏ G" := (dinatural_transformation F G) (at level 39) : cat.

  (** *** Dinatural transformation from a natural transformation *)

  Lemma nat_trans_to_dinatural_transformation {f : C ↛ C} {g : C ↛ C}
        (alpha : nat_trans (f : _ ⟶ _) (g : _ ⟶ _)) : f ⇏ g.
  Proof.
    use make_dinatural_transformation.
    - exact (λ z, alpha (_ ,, _)).
    - abstract
        (intros a b h ;
         use funextsec ; intro z ;
         unfold lmap, rmap ;
         pose (p := eqtohomot (nat_trans_ax alpha (_ ,, _) (_ ,, _) (h ,, identity _)) z) ;
         cbn in p ; cbn ;
         refine (maponpaths _ p @ _) ; clear p ;
         refine (!(profunctor_comp g _ _ _ _ _) @ _) ;
         rewrite !id_left ;
         refine (!_) ;
         refine (maponpaths _ (eqtohomot (nat_trans_ax alpha (_ ,, _) (_ ,, _) (_ ,, _)) _) @ _) ;
         refine (!(profunctor_comp g _ _ _ _ _) @ _) ;
         rewrite !id_right ;
         apply idpath).
  Defined.
End Dinatural.

Notation "F ⇏ G" := (dinatural_transformation F G) (at level 39) : cat.

(** ** (Co)ends *)

Section Ends.

  Context {C : category} (F : C ↛ C).

  (** *** Wedges *)

  (** Wedge diagram:
<<
          w -----> F(a, a)
          |           |
          | F(f, id)  | F(id, f)
          V           V
        F(b, b) --> F(a, b)
>>
  *)

  Definition is_wedge (w : ob HSET_univalent_category) (pi : ∏ a : C, w --> F a a) : hProp.
  Proof.
    use make_hProp.
    - exact (∏ (a b : ob C) (f : a --> b), pi a · rmap F f = pi b · lmap F f).
    - abstract (do 3 (apply impred; intro); apply homset_property).
  Defined.

  (** Following the convention for limits, the tip is explicit in the type. *)
  Definition wedge (w : ob HSET_univalent_category) : UU :=
    ∑ pi : (∏ a : ob C, w --> F a a), is_wedge w pi.

  Definition make_wedge (w : hSet) (pi : (∏ a : C, (w : HSET) --> F a a)) :
   (∏ (a b : ob C) (f : a --> b), pi a · rmap F f = pi b · lmap F f) -> wedge w.
  Proof.
    intro.
    use tpair.
    - assumption.
    - abstract assumption.
  Qed.

  Definition wedge_pr (w : HSET) (W : wedge w) :
    ∏ a : C, w --> F a a := (pr1 W).

  Coercion wedge_pr : wedge >-> Funclass.

  (** *** Ends *)

  Definition is_end (w : ob HSET_univalent_category) (W : wedge w) : hProp.
  Proof.
    use make_hProp.
    - exact (∏ v (V : wedge v),
               iscontr (∑ f : v --> w, ∏ a, f · W a = V a)).
    - abstract (do 2 (apply impred; intro); apply isapropiscontr).
  Qed.

  (** This must be capitalized because 'end' is a Coq keyword.
      It also matches the convention for limits. *)
  Definition End : UU := ∑ w W, is_end w W.

  (** **** Accessors/coercions *)

  Definition end_ob (e : End) : ob HSET_univalent_category  := pr1 e.
  Coercion end_ob : End >-> ob.

  Definition end_wedge (e : End) : wedge e := pr1 (pr2 e).
  Coercion end_wedge : End >-> wedge.

  (** *** Cowedges *)
  (** *** Coends *)

End Ends.

Notation "∫↓ F" := (End F) (at level 40) : cat.
(* Notation "∫↑ F" := (Coend F) (at level 40) : cat. *)
