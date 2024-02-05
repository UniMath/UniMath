(*****************************************************************************************

 Coends of profunctors

 We show that the category of sets admits coends for profunctors. We also provide nice
 accessors for them

 Contents
 1. Coends of profunctors
 2. Accessors for coends of profunctors

 *****************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Profunctors.Core.
Require Import UniMath.CategoryTheory.limits.Coends.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.coequalizers.

Local Open Scope cat.

Section CoendsHSET.
  Context {C : category}
          (F : profunctor C C).

  (** * 1. Coends of profunctors *)
  Definition HSET_coend_colimit
    : coend_colimit F
    := construction_of_coends
         F
         Coequalizers_HSET
         (CoproductsHSET_type _) (CoproductsHSET_type _).

  (** * 2. Accessors for coends of profunctors *)
  Definition HSET_coend
    : hSet
    := HSET_coend_colimit : HSET.

  Definition HSET_coend_in
             (x : C)
             (h : F x x)
    : HSET_coend
    := mor_of_cowedge _ HSET_coend_colimit x h.

  Proposition HSET_coend_comm
              {x y : C}
              (f : x --> y)
              (h : F y x)
    : HSET_coend_in y (rmap F f h)
      =
      HSET_coend_in x (lmap F f h).
  Proof.
    exact (eqtohomot (eq_of_cowedge _ HSET_coend_colimit f) h).
  Qed.

  Section MorToCoend.
    Context (X : hSet)
            (fs : ∏ (x : C), F x x → X)
            (ps : ∏ (x y : C)
                    (f : x --> y)
                    (h : F y x),
                  fs _ (rmap F f h)
                  =
                  fs _ (lmap F f h)).

    Definition mor_from_HSET_coend
               (x : HSET_coend)
      : X.
    Proof.
      refine (mor_to_coend' _ (pr2 HSET_coend_colimit) X fs _ x).
      abstract
        (intros y₁ y₂ g ;
         use funextsec ; intro h ;
         apply ps).
    Defined.

    Definition mor_from_HSET_coend_comm
               {x : C}
               (h : F x x)
      : mor_from_HSET_coend (HSET_coend_in x h)
        =
        fs x h.
    Proof.
      refine (eqtohomot (mor_to_coend'_comm _ (pr2 HSET_coend_colimit) X fs _ x) h).
      abstract
        (intros y₁ y₂ g ;
         use funextsec ; intro ;
         apply ps).
    Qed.
  End MorToCoend.

  Proposition mor_from_HSET_coend_eq
              (X : hSet)
              (f g : HSET_coend → X)
              (x : HSET_coend)
              (p : ∏ (y : C)
                     (h : F y y),
                   f (HSET_coend_in y h) = g (HSET_coend_in y h))
    : f x = g x.
  Proof.
    use (eqtohomot (mor_to_coend_eq F (pr2 HSET_coend_colimit) X _)).
    intro y.
    use funextsec.
    intro h.
    apply p.
  Qed.
End CoendsHSET.

#[global] Opaque HSET_coend HSET_coend_in mor_from_HSET_coend.
