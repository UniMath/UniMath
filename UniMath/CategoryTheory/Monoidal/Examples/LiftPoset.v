(*****************************************************************

 Lifting posets as a monoidal comonad

 We show that the lifting operation on posets (i.e., adding a new
 bottom element) gives rise to a monoidal comonad on the monoidal
 category of pointed posets with the smash product.

 Content
 1. Lifting as a functor
 2. Extraction and duplication
 3. The comonad
 4. Lifting is symmetric monoidal
 5. The natural transformations are monoidal
 6. Every object has a natural comonoid structure

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.OrderTheory.Posets.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.CartesianStructure.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructureLimitsAndColimits.
Require Import UniMath.CategoryTheory.DisplayedCats.Structures.StructuresSmashProduct.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.PointedPosetStrict.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Examples.SmashProductMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Examples.PosetsMonoidal.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.CategoryOfPosets.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.

Local Open Scope cat.

(**
 1. Lifting as a functor
 *)
Definition lift_poset_functor_data
  : functor_data
      category_of_pointed_poset_strict
      category_of_pointed_poset_strict.
Proof.
  use make_functor_data.
  - exact (λ X, _ ,, lift_pointed_PartialOrder (pr12 X)).
  - exact (λ X Y f, _ ,, lift_strict_and_monotone_map (pr12 f)).
Defined.

Proposition lift_poset_functor_laws
  : is_functor lift_poset_functor_data.
Proof.
  split.
  - intros X.
    use eq_mor_hset_struct ; cbn.
    intro x.
    induction x as [ x | ] ; cbn.
    + apply idpath.
    + apply idpath.
  - intros X Y Z f g.
    use eq_mor_hset_struct ; cbn.
    intro x.
    induction x as [ x | ] ; cbn.
    + apply idpath.
    + apply idpath.
Qed.

Definition lift_poset_functor
  : category_of_pointed_poset_strict ⟶ category_of_pointed_poset_strict.
Proof.
  use make_functor.
  - exact lift_poset_functor_data.
  - exact lift_poset_functor_laws.
Defined.

(**
 2. Extraction and duplication
 *)
Definition lift_poset_dupl
  : lift_poset_functor ⟹ lift_poset_functor ∙ lift_poset_functor.
Proof.
  use make_nat_trans.
  - exact (λ X, _ ,, is_strict_and_monotone_lift_pointed_PartialOrder_dupl _).
  - abstract
      (intros X Y f ;
       use eq_mor_hset_struct ; cbn ;
       intros [ x | [] ] ; cbn ; apply idpath).
Defined.

Definition lift_poset_extract
  : lift_poset_functor ⟹ functor_identity _.
Proof.
  use make_nat_trans.
  - exact (λ X, _ ,, is_strict_and_monotone_lift_pointed_PartialOrder_extract _).
  - abstract
      (intros X Y f ;
       use eq_mor_hset_struct ; cbn ;
       intros [ x | [] ] ; [ apply idpath | ] ; cbn ;
       refine (!_) ;
       apply f).
Defined.

(**
 3. The comonad
 *)
Proposition lift_poset_comonad_laws
  : disp_Comonad_laws (lift_poset_dupl,, lift_poset_extract).
Proof.
  repeat split.
  - intro X.
    use eq_mor_hset_struct.
    intros [ x | [] ] ; cbn.
    + apply idpath.
    + apply idpath.
  - intro X.
    use eq_mor_hset_struct.
    intros [ x | [] ] ; cbn.
    + apply idpath.
    + apply idpath.
  - intro X.
    use eq_mor_hset_struct.
    intros [ x | [] ] ; cbn.
    + apply idpath.
    + apply idpath.
Qed.

Definition lift_poset_comonad
  : Comonad pointed_poset_sym_mon_closed_cat.
Proof.
  refine (lift_poset_functor ,, ((lift_poset_dupl ,, lift_poset_extract) ,, _)).
  exact lift_poset_comonad_laws.
Defined.

(**
 4. Lifting is symmetric monoidal
 *)
Definition lift_poset_comonad_smash
           (X Y : pointed_poset_sym_mon_closed_cat)
  : lift_poset_comonad X ∧* lift_poset_comonad Y --> lift_poset_comonad (X ∧* Y).
Proof.
  simple refine (_ ,, _).
  - use map_from_smash.
    + intros x y.
      induction x as [ x | ] ; induction y as [ y | ].
      * refine (inl _).
        use setquotpr.
        exact (x ,, y).
      * exact (inr tt).
      * exact (inr tt).
      * exact (inr tt).
    + abstract
        (intros [ y₁ | ] [ y₂ | ] ; cbn ; apply idpath).
    + abstract
        (intros [ x | ] [ y | ] ; cbn ; apply idpath).
    + abstract
        (intros [ x₁ | ] [ x₂ | ] ; cbn ; apply idpath).
  - use hset_struct_with_smash_map_from_smash.
    split.
    + abstract
        (intros xy₁ xy₂ p ;
         induction xy₁ as [ x₁ y₁ ] ; induction xy₂ as [ x₂ y₂ ] ;
         induction x₁ as [ x₁ | ], y₁ as [ y₁ | ], x₂ as [ x₂ | ], y₂ as [ y₂ | ] ;
         cbn in * ;
         try (apply tt) ;
         try (apply p) ;
         apply hinhpr ;
         use inr ;
         exact p ).
    + abstract
        (cbn ;
         apply idpath).
Defined.

Definition lax_monoidal_data_lift_poset_comonad
  : fmonoidal_data
      pointed_poset_sym_mon_closed_cat
      pointed_poset_sym_mon_closed_cat
      lift_poset_comonad.
Proof.
  split.
  - exact lift_poset_comonad_smash.
  - simple refine (_ ,, _).
    + exact (λ b, if b then inl true else inr tt).
    + split.
      * abstract
          (intros b₁ b₂ p ; cbn ;
           induction b₁, b₂ ; cbn in * ; try (exact tt) ;
           exact p).
      * apply idpath.
Defined.

Proposition lax_monoidal_lift_poset_comonad_laws
  : fmonoidal_laxlaws lax_monoidal_data_lift_poset_comonad.
Proof.
  repeat split.
  - intros X Y₁ Y₂ g.
    use eq_mor_hset_struct.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intros xy.
    induction xy as [ x y ].
    induction x as [ x | ] ; induction y as [ y | ] ; apply idpath.
  - intros X₁ X₂ Y f.
    use eq_mor_hset_struct.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intros xy.
    induction xy as [ x y ].
    induction x as [ x | ] ; induction y as [ y | ] ; apply idpath.
  - intros X Y Z.
    use eq_mor_hset_struct.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intros xy.
    induction xy as [ xy z ].
    revert xy.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intros xy.
    induction xy as [ x y ].
    induction x as [ x | ] ; induction y as [ y | ] ; induction z as [ z | ] ; apply idpath.
  - intros X.
    use eq_mor_hset_struct.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intros xy.
    cbn in xy.
    induction xy as [ b x ].
    induction b ; induction x as [ x | [] ] ; cbn ; apply idpath.
  - intros X.
    use eq_mor_hset_struct.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intros xy.
    cbn in xy.
    induction xy as [ x b ].
    induction b ; induction x as [ x | [] ] ; apply idpath.
Qed.

Definition lax_monoidal_lift_poset_comonad
  : fmonoidal_lax
      pointed_poset_sym_mon_closed_cat
      pointed_poset_sym_mon_closed_cat
      lift_poset_comonad.
Proof.
  simple refine (_ ,, _).
  - exact lax_monoidal_data_lift_poset_comonad.
  - exact lax_monoidal_lift_poset_comonad_laws.
Defined.

Proposition is_symmetric_lift_poset_comonad
  : is_symmetric_monoidal_functor
      (pr21 pointed_poset_sym_mon_closed_cat)
      (pr21 pointed_poset_sym_mon_closed_cat)
      lax_monoidal_lift_poset_comonad.
Proof.
  intros X Y.
  use eq_mor_hset_struct.
  use setquotunivprop' ; [ intro ; apply setproperty | ].
  intros xy.
  induction xy as [ x y ].
  induction x as [ x | ] ; induction y as [ y | ] ; apply idpath.
Qed.

(**
 5. The natural transformations are monoidal
 *)
Proposition is_mon_nat_trans_lift_poset_extract
  : is_mon_nat_trans
      lax_monoidal_lift_poset_comonad
      (identity_fmonoidal _)
      lift_poset_extract.
Proof.
  split.
  - intros X Y.
    use eq_mor_hset_struct.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intros xy.
    induction xy as [ x y ].
    induction x as [ x | ] ; induction y as [ y | ].
    + use iscompsetquotpr ; cbn.
      apply hinhpr.
      apply inl.
      apply idpath.
    + use iscompsetquotpr ; cbn.
      apply hinhpr.
      apply inr.
      split.
      * apply inl.
        apply idpath.
      * apply inr.
        apply idpath.
    + use iscompsetquotpr ; cbn.
      apply hinhpr.
      apply inr.
      split.
      * apply inl.
        apply idpath.
      * apply inl.
        apply idpath.
    + use iscompsetquotpr ; cbn.
      apply hinhpr.
      apply inr.
      split.
      * apply inl.
        apply idpath.
      * apply inr.
        apply idpath.
  - use eq_mor_hset_struct.
    intro x.
    induction x ; cbn ; apply idpath.
Qed.

Proposition is_mon_nat_trans_lift_poset_dupl
  : is_mon_nat_trans
      lax_monoidal_lift_poset_comonad
      (comp_fmonoidal_lax
         lax_monoidal_lift_poset_comonad
         lax_monoidal_lift_poset_comonad)
      lift_poset_dupl.
Proof.
  split.
  - intros X Y.
    use eq_mor_hset_struct.
    use setquotunivprop' ; [ intro ; apply setproperty | ].
    intros xy.
    induction xy as [ x y ].
    induction x as [ x | ] ; induction y as [ y | ].
    + apply idpath.
    + apply idpath.
    + apply idpath.
    + apply idpath.
  - use eq_mor_hset_struct.
    intro x.
    induction x ; cbn ; apply idpath.
Qed.

Definition lift_poset_symmetric_monoidal_comonad :
  symmetric_monoidal_comonad pointed_poset_sym_mon_closed_cat.
Proof.
  use make_symmetric_monoidal_comonad.
  - exact lift_poset_comonad.
  - exact lax_monoidal_lift_poset_comonad.
  - exact is_symmetric_lift_poset_comonad.
  - apply is_mon_nat_trans_lift_poset_dupl.
  - apply is_mon_nat_trans_lift_poset_extract.
Defined.

(**
 6. Every object has a natural comonoid structure
 *)
Definition lift_poset_comult_map
           {X : pointed_poset_sym_mon_closed_cat}
           (x : pr11 X ⨿ unit)
  : pr11 (lift_poset_comonad X ∧* lift_poset_comonad X).
Proof.
  induction x as [ x | ].
  - exact (setquotpr _ (inl x ,, inl x)).
  - exact (setquotpr _ (inr tt ,, inr tt)).
Defined.

Proposition is_strict_and_monotone_lift_poset_comult_map
            (X : pointed_poset_sym_mon_closed_cat)
  : is_strict_and_monotone
      (pr2 (lift_poset_comonad X))
      (pr2 (lift_poset_comonad X ∧* lift_poset_comonad X))
      (@lift_poset_comult_map X).
Proof.
  split.
  - intros x₁ x₂ p.
    induction x₁ as [ x₁ | ], x₂ as [ x₂ | ] ; cbn in *.
    + refine (hinhpr (inr _)).
      exact (p ,, p).
    + exact (fromempty p).
    + refine (hinhpr (inr _)).
      exact (tt ,, tt).
    + refine (hinhpr (inr _)).
      exact (tt ,, tt).
  - apply idpath.
Qed.

Definition lift_poset_comult
  : lift_poset_functor
    ⟹
    bindelta_pair_functor lift_poset_functor lift_poset_functor
    ∙
    bifunctor_to_functorfromproductcat pointed_poset_sym_mon_closed_cat.
Proof.
  use make_nat_trans.
  - refine (λ X, lift_poset_comult_map ,, _).
    exact (is_strict_and_monotone_lift_poset_comult_map X).
  - abstract
      (intros X Y f ;
       use eq_mor_hset_struct ;
       intro x ;
       induction x as [ x | ] ; apply idpath).
Defined.

Definition lift_poset_counit
  : lift_poset_functor
    ⟹
    constant_functor _ _ (monoidal_unit pointed_poset_sym_mon_closed_cat).
Proof.
  use make_nat_trans.
  - simple refine (λ X, _ ,, _).
    + intro x.
      induction x as [ x | ].
      * exact true.
      * exact false.
    + split.
      * abstract
          (intros x₁ x₂ p ;
           induction x₁ as [ x₁ | ], x₂ as [ x₂ | ] ; try (exact tt) ;
           cbn in * ;
           exact p).
      * abstract
          (cbn ;
           apply idpath).
  - abstract
      (intros X Y f ;
       use eq_mor_hset_struct ;
       intro x ;
       induction x as [ x | ] ; cbn ;
       apply idpath).
Defined.

Definition lift_commutative_comonoid
           (X : pointed_poset_sym_mon_closed_cat)
  : commutative_comonoid pointed_poset_sym_mon_closed_cat.
Proof.
  use make_commutative_comonoid.
  - exact (lift_poset_functor X).
  - exact (lift_poset_comult X).
  - exact (lift_poset_counit X).
  - abstract
      (use eq_mor_hset_struct ;
       intro x ; cbn in x ;
       induction x as [ x | [ ] ] ;
       apply idpath).
  - abstract
      (use eq_mor_hset_struct ;
       intro x ; cbn in x ;
       induction x as [ x | [ ] ] ;
       apply idpath).
  - abstract
      (use eq_mor_hset_struct ;
       intro x ; cbn in x ;
       induction x as [ x | [ ] ] ;
       apply idpath).
Defined.
