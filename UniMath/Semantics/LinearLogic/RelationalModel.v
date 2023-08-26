(*******************************************************************************

 The relational model of linear logic

 In this file, we formalize the relational model of linear logic. To do so,
 we use Lafont categories. As such, the only thing that we have to verify is
 that the symmetric monoidal category of relations has cofree commutative
 comonoids.

 The proof in this file is based on two sources:
 - Theorems 4.1 and 4.7 Free Commutative Monoids in Homotopy Type Theory
 - Section 1.1.4 in Bicategorical Orthogonality Constructions for Linear Logic

 The idea behind the construction of the cofree commutative comonoid is as
 follows:
 1. In `SET`, we have free commutative monoids. In UniMath, we can construct
    these as quotients, but they can also be constructed with higher inductive
    types.
 2. `REL` is equivalent to the Kleisli category of the powerset monad on `SET`.
 3. We can lift monoids in `SET` to monoids in `REL`.
 4. `REL` is self-dual.

 The main idea behind the third point is that there is a distributive law
 between the power set monad and the free commutative monoid monad. The proof
 in this file combines these 4 facts.

 First we construct the cofree comonoid ([cofree_comonoid_REL]) using the free
 commutative monoid.

 Second we show that comonoids in `REL` give rise to monoids in `SET`
 ([REL_comonoid_to_monoid]). We need this to prove the universal property. This
 is because for the universal property of the cofree comonoid, we get a comonoid
 in `REL`, but we can only instantiate the universal property of the free
 commutative monoid to commutative monoids. This translation is what allows us
 to use this universal property. Note that we use the power set here: a comonoid
 over `X` in `REL` gives a monoid in `SET` whose carrier is the power set of `X`.

 Third we show that monoid homomorphisms in `SET` give rise to comonoid
 homomorphisms in `REL` ([cofree_comonoid_REL_map]). The universal property of
 the free commutative monoid gives a monoid homomorphism, but we want a comonoid
 homomorphism.

 Fourth we show the converse: comonoid morphisms in `REL` give rise to monoid
 homomorphisms in `SET` ([comonoid_mor_REL_to_monoid_mor]). This is so that we
 can instantiate the uniqueness of the universal property.

 The construction of comonoids in `REL` from monoids in `SET` can be seen as the
 composition of the following functors.
 - We have a functor from `Mon(SET) -> Mon(REL)`. It sends a monoid `X` to the
   powerset of `X`. The reason why this functor exists, is because we have a
   distributive law between the free monoid monad and the powerset monad.
 - For every symmetric monoidal category `V` we have an equivalence
   `Mon(V) ≃ Comon(V^op)`. This follows from the fact that the notion of monoid
   and comonoid are dual to each other.
 - From an equivalence `V ≃ V'` we get an equivalence `Comon(V) ≃ Comon(V')`.
 - We have that `REL ≃ REL^op`, because relations can be reversed.
 Now we can make the following composition of functors:
 `Mon(SET) -> Mon(REL) ≃ Comon(REL^op) ≃ Comon(REL)`

 Contents
 1. The cofree comonoid on a set
 2. Every comonoid in `REL` gives rise to a monoid in `SET`
 3. The universal property of the cofree comonoid in `REL`
 4. The relational model of linear logic

 *******************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Free_Monoids_and_Groups.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.categories.Relations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Functors.
Require Import UniMath.CategoryTheory.Monoidal.Adjunctions.
Require Import UniMath.CategoryTheory.Monoidal.FunctorCategories.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.TotalMonoidal.
Require Import UniMath.CategoryTheory.Monoidal.Displayed.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Category.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Monoidal.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Comonoids.CommComonoidsCartesian.
Require Import UniMath.CategoryTheory.Monoidal.Examples.Relations.
Require Import UniMath.Semantics.LinearLogic.LafontCategory.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Opaque free_abmonoid free_abmonoid_extend free_abmonoid_unit.

(** * 1. The cofree comonoid on a set *)
Section CofreeComonoid.
  Context (X : hSet).

  Let Mmonoid : abmonoid := free_abmonoid X.
  Let M : hSet := Mmonoid.
  Let z : M := unel Mmonoid.
  Let m : M → M → M := λ x y, op x y.

  Definition cofree_comonoid_REL_comult
    : REL_sym_mon_closed_cat ⟦ M , (M × M)%set ⟧
    := λ x y, (m (pr1 y) (pr2 y) = x)%logic.

  Definition cofree_comonoid_REL_counit
    : REL_sym_mon_closed_cat ⟦ M , unitset ⟧
    := λ x y, (x = z)%logic.

  Proposition cofree_comonoid_REL_counit_left
    : cofree_comonoid_REL_comult
      · (cofree_comonoid_REL_counit #⊗ identity _)
      · mon_lunitor _
      =
      identity _.
  Proof.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use hPropUnivalence.
    - use factor_through_squash_hProp.
      intros H.
      induction H as [ [ [] a ] [ H p ] ] ; cbn in a, p.
      revert H.
      use factor_through_squash_hProp.
      intros H.
      induction H as [ [ b c ] [ q H ] ] ; cbn in q.
      revert H.
      use factor_through_squash_hProp.
      intros [ [ [] d ] [ [ r₁ r₂ ] [ r₃ r₄ ] ] ].
      cbn in r₁, r₂, r₃, r₄ ; cbn.
      refine (!q @ _ @ p).
      rewrite <- r₄.
      rewrite <- r₁.
      rewrite r₂.
      apply (lunax Mmonoid).
    - intros p ; cbn in p.
      induction p.
      refine (hinhpr _).
      refine ((tt ,, x) ,, _).
      refine (_ ,, idpath _).
      refine (hinhpr _).
      refine ((z ,, x) ,, _ ,, _).
      + apply (lunax Mmonoid).
      + refine (hinhpr _).
        refine ((tt ,, x) ,, _) ; cbn.
        repeat split ; apply idpath.
  Qed.

  Proposition cofree_comonoid_REL_coassoc
    : cofree_comonoid_REL_comult
      · cofree_comonoid_REL_comult #⊗ identity _
      · mon_lassociator _ _ _
      =
      cofree_comonoid_REL_comult
      · identity _ #⊗ cofree_comonoid_REL_comult.
  Proof.
    use funextsec ; intro x.
    use funextsec ; intro y.
    induction y as [ y₁ [ y₂ y₃ ]].
    use hPropUnivalence.
    - use factor_through_squash_hProp.
      intros H.
      induction H as [ [ [ a₁ a₂ ] a₃ ] [ H [ p₁ [ p₂ p₃ ] ] ] ] ; cbn in p₁, p₂, p₃.
      revert H.
      use factor_through_squash_hProp.
      intros H.
      induction H as [ [ b₁ b₂ ] [ q H ] ] ; cbn in q.
      revert H.
      use factor_through_squash_hProp.
      intros H.
      cbn in H.
      induction H as [ [ [ c₁ c₂ ] c₃ ] [ [ r₁ r₂ ] [ r₃ r₄ ] ] ] ; cbn in r₁, r₂, r₃, r₄.
      induction p₁, p₂, p₃, r₁, r₄.
      pose (r₅ := maponpaths dirprod_pr1 r₃) ; cbn in r₅.
      pose (r₆ := maponpaths dirprod_pr2 r₃) ; cbn in r₆.
      induction r₅, r₆.
      rewrite <- r₂ in q.
      assert (m (m c₁ c₂) b₂ = m c₁ (m c₂ b₂)) as s.
      {
        exact (assocax Mmonoid c₁ c₂ b₂).
      }
      rewrite s in q.
      refine (hinhpr _).
      refine ((c₁ ,, m c₂ b₂) ,, _).
      split.
      + exact q.
      + refine (hinhpr _).
        exact ((_ ,, _) ,, (idpath _ ,, idpath _) ,, (idpath _ ,, idpath _)).
    - use factor_through_squash_hProp.
      intros H.
      induction H as [ [ a₁ a₂ ] [ p H ]] ; cbn in p.
      revert H.
      use factor_through_squash_hProp.
      intros H.
      induction H as [ [ b₁ b₂ ] [ [ q₁ q₂ ] [ q₃ q₄ ]]] ; cbn in q₁, q₂, q₃, q₄.
      induction q₁, q₂, q₃.
      rewrite <- q₄ in p ; clear q₄.
      assert (m a₁ (m y₂ y₃) = m (m a₁ y₂) y₃) as s.
      {
        exact (!(assocax Mmonoid a₁ y₂ y₃)).
      }
      rewrite s in p.
      refine (hinhpr (((a₁ ,, y₂) ,, y₃) ,, _)).
      refine (_ ,, idpath _ ,, idpath _ ,, idpath _).
      refine (hinhpr ((m a₁ y₂ ,, y₃) ,, p ,, _)).
      refine (hinhpr _) ; cbn.
      simple refine (((a₁ ,, y₂) ,, y₃) ,, _) ; repeat split.
  Qed.

  Proposition cofree_comonoid_REL_comm
    : cofree_comonoid_REL_comult
      · sym_mon_braiding REL_sym_mon_closed_cat _ _
      =
      cofree_comonoid_REL_comult.
  Proof.
    use funextsec ; intro x.
    use funextsec ; intro y.
    induction y as [ y₁ y₂ ].
    use hPropUnivalence.
    - use factor_through_squash_hProp ; cbn.
      intros [ [ a₁ a₂ ] [ p₁ [ p₂ p₃ ] ] ] ; cbn in p₁, p₂, p₃.
      induction p₂, p₃.
      refine (_ @ p₁).
      apply (commax Mmonoid).
    - intro p ; cbn in p.
      refine (hinhpr ((y₂ ,, y₁) ,, _ ,, _ ,, _)) ; cbn.
      + refine (_ @ p).
        apply (commax Mmonoid).
      + apply idpath.
      + apply idpath.
  Qed.

  Definition cofree_comonoid_REL
    : commutative_comonoid REL_sym_mon_closed_cat.
  Proof.
    use make_commutative_comonoid.
    - exact M.
    - exact cofree_comonoid_REL_comult.
    - exact cofree_comonoid_REL_counit.
    - exact cofree_comonoid_REL_counit_left.
    - exact cofree_comonoid_REL_coassoc.
    - exact cofree_comonoid_REL_comm.
  Defined.
End CofreeComonoid.

Definition map_to_cofree_comonoid_REL
           (X : REL)
  : REL ⟦ cofree_comonoid_REL X , X ⟧
  := λ y x, (free_abmonoid_unit x = y)%logic.

(** * 2. Every comonoid in `REL` gives rise to a monoid in `SET` *)
Section ComonoidToMonoid.
  Context (C : commutative_comonoid REL_sym_mon_closed_cat).

  Let U : hSet := underlying_commutative_comonoid _ C.

  Definition REL_comonoid_to_mult
             (X Y : U → hProp)
             (y : U)
    : hProp
    := ∃ (x₁ x₂ : U), X x₁ ∧ Y x₂ ∧ comonoid_comult _ C y (x₁ ,, x₂).

  Definition REL_comonoid_to_unit
    : U → hProp
    := λ x, comonoid_counit _ C x tt.

  Definition REL_comonoid_to_setwithbinop
    : setwithbinop.
  Proof.
    use make_setwithbinop.
    - exact (funset U hPropset).
    - exact REL_comonoid_to_mult.
  Defined.

  Proposition REL_comonoid_to_assoc
    : isassoc (pr2 REL_comonoid_to_setwithbinop).
  Proof.
    intros X Y Z.
    use funextsec ; intro y.
    use hPropUnivalence.
    - use factor_through_squash_hProp.
      intros ( a₁ & a₂ & H & p₁ & p₂ ).
      revert H.
      use factor_through_squash_hProp.
      intros ( b₁ & b₂ & q₁ & q₂ & q₃ ).
      pose (eqweqmaphProp
              (eqtohomot
                 (eqtohomot
                    (comonoid_to_law_assoc _ C)
                    y)
                 (b₁ ,, (b₂ ,, a₂))))
        as H.
      cbn in H.
      assert (H' := H (hinhpr
                         ((((b₁ ,, b₂) ,, a₂)
                           ,,
                           hinhpr
                             ((a₁ ,, a₂)
                              ,,
                              p₂
                              ,,
                              idpath _
                              ,,
                              q₃)
                           ,,
                           idpath _
                           ,,
                           idpath _
                           ,,
                           idpath _)))).
      revert H'.
      use factor_through_squash_hProp.
      intros [ [ c₁ c₂ ] [ r₁ [ r₂ r₃ ] ] ] ; cbn in r₁, r₂, r₃.
      induction r₂.
      apply hinhpr.
      simple refine (c₁ ,, c₂ ,, q₁ ,, _ ,, _).
      + use hinhpr ; cbn.
        exact (b₂ ,, a₂ ,, q₂ ,, p₁ ,, r₃).
      + exact r₁.
    - use factor_through_squash_hProp.
      intros ( a₁ & a₂ & p₁ & H & p₂ ).
      revert H.
      use factor_through_squash_hProp.
      intros ( b₁ & b₂ & q₁ & q₂ & q₃ ).
      pose (eqweqmaphProp
              (!eqtohomot
                 (eqtohomot
                    (comonoid_to_law_assoc _ C)
                    y)
                 (a₁ ,, (b₁ ,, b₂))))
        as H.
      assert (H' := H (hinhpr ((a₁ ,, a₂) ,, p₂ ,, idpath _ ,, q₃))).
      revert H'.
      use factor_through_squash_hProp.
      intros [ [ [ c₁ c₂ ] c₃ ] [ K [ r₁ [ r₂ r₃ ] ] ] ] ; cbn in r₁, r₂, r₃.
      revert K.
      use factor_through_squash_hProp.
      intros [ [ d₁ d₂ ] [ s₁ [ s₂ s₃ ] ] ] ; cbn in s₁, s₂, s₃.
      induction r₁, r₂, r₃, s₂.
      apply hinhpr.
      simple refine (d₁ ,, d₂ ,, _ ,, q₂ ,, s₁).
      apply hinhpr ; cbn.
      simple refine (c₁ ,, c₂ ,, p₁ ,, q₁ ,, _) ; cbn.
      exact s₃.
  Qed.

  Proposition REL_comonoid_to_lunit
    : islunit (pr2 REL_comonoid_to_setwithbinop) REL_comonoid_to_unit.
  Proof.
  intro X.
  use funextsec ; intro y ; cbn in y.
  use hPropUnivalence.
  - use factor_through_squash_hProp.
    intros ( x₁ & x₂ & p₁ & p₂ & p₃ ).
    unfold REL_comonoid_to_unit in p₁.
    assert (y = x₂) as q.
    {
      apply (eqweqmaphProp (eqtohomot (eqtohomot (comonoid_to_law_unit_left _ C) y) x₂)).
      cbn.
      use hinhpr.
      refine ((tt ,, x₂) ,, _ ,, idpath _).
      use hinhpr ; cbn.
      refine ((x₁ ,, x₂) ,, _) ; cbn.
      refine (p₃ ,, idpath _ ,, p₁).
    }
    rewrite q.
    exact p₂.
  - intro Hy.
    assert (q := eqweqmaphProp
                   (!eqtohomot
                      (eqtohomot
                         (comonoid_to_law_unit_left _ C)
                         y)
                      y)
                   (idpath _)).
    revert q.
    use factor_through_squash_hProp.
    intros [ [ [] a ] [ H p ] ] ; cbn in p.
    induction p.
    revert H.
    use factor_through_squash_hProp.
    intros [ [ b₁ b₂ ] [ q₁ [ q₂ q₃ ] ] ] ; cbn in q₁, q₂, q₃.
    induction q₂.
    use hinhpr.
    refine (b₁ ,, b₂ ,, _ ,, _ ,, _) ; cbn.
    + exact q₃.
    + exact Hy.
    + exact q₁.
  Qed.

  Proposition REL_comonoid_to_comm
    : iscomm (pr2 REL_comonoid_to_setwithbinop).
  Proof.
    intros X Y.
    use funextsec ; intro y ; cbn in y.
    use hPropUnivalence.
    - use factor_through_squash_hProp.
      intros ( x₁ & x₂ & p₁ & p₂ & H ).
      use hinhpr.
      refine (x₂ ,, x₁ ,, p₂ ,, p₁ ,, _).
      assert (q := eqweqmaphProp
                     (!eqtohomot
                        (eqtohomot
                           (commutative_comonoid_is_commutative _ C)
                           y)
                        (x₁ ,, x₂))
                     H).
      revert q.
      use factor_through_squash_hProp.
      intros [ [ a₁ a₂ ] [ q₁ [ q₂ q₃ ] ] ] ; cbn in q₁, q₂, q₃.
      induction q₂, q₃.
      exact q₁.
    - use factor_through_squash_hProp.
      intros ( x₁ & x₂ & p₁ & p₂ & H ).
      use hinhpr.
      refine (x₂ ,, x₁ ,, p₂ ,, p₁ ,, _).
      assert (q := eqweqmaphProp
                     (!eqtohomot
                        (eqtohomot
                           (commutative_comonoid_is_commutative _ C)
                           y)
                        (x₁ ,, x₂))
                     H).
      revert q.
      use factor_through_squash_hProp.
      intros [ [ a₁ a₂ ] [ q₁ [ q₂ q₃ ] ] ] ; cbn in q₁, q₂, q₃.
      induction q₂, q₃.
      exact q₁.
  Qed.

  Proposition REL_comonoid_to_runit
    : isrunit (pr2 REL_comonoid_to_setwithbinop) REL_comonoid_to_unit.
  Proof.
    intro X.
    refine (REL_comonoid_to_comm _ _ @ _).
    apply REL_comonoid_to_lunit.
  Qed.

  Definition REL_comonoid_to_is_unital
    : isunital (pr2 REL_comonoid_to_setwithbinop).
  Proof.
    use make_isunital.
    - exact REL_comonoid_to_unit.
    - split.
      + exact REL_comonoid_to_lunit.
      + exact REL_comonoid_to_runit.
  Defined.

  Definition REL_comonoid_to_is_monoidop
    : ismonoidop (pr2 REL_comonoid_to_setwithbinop).
  Proof.
    use make_ismonoidop.
    - exact REL_comonoid_to_assoc.
    - exact REL_comonoid_to_is_unital.
  Defined.

  Definition REL_comonoid_to_is_abmonoidop
    : isabmonoidop (pr2 REL_comonoid_to_setwithbinop).
  Proof.
    use make_isabmonoidop.
    - exact REL_comonoid_to_is_monoidop.
    - exact REL_comonoid_to_comm.
  Defined.

  Definition REL_comonoid_to_monoid
    : abmonoid.
  Proof.
    use make_abmonoid.
    - exact REL_comonoid_to_setwithbinop.
    - exact REL_comonoid_to_is_abmonoidop.
  Defined.
End ComonoidToMonoid.

(** * 3. The universal property of the cofree comonoid in `REL` *)
Section CofreeComonoidUMP.
  Context (X : REL)
          (C : commutative_comonoid REL_sym_mon_closed_cat)
          (f : underlying_commutative_comonoid _ C --> X).

  Definition cofree_comonoid_REL_underlying
    : underlying_commutative_comonoid _ C
      -->
      underlying_commutative_comonoid _ (cofree_comonoid_REL X)
    := λ c x, @free_abmonoid_extend X (REL_comonoid_to_monoid C) (λ c x, f x c) x c.

  Proposition cofree_comonoid_REL_map_comult
    : comonoid_comult REL_sym_mon_closed_cat C
      · cofree_comonoid_REL_underlying #⊗ cofree_comonoid_REL_underlying
      =
      cofree_comonoid_REL_underlying
      · comonoid_comult REL_sym_mon_closed_cat (cofree_comonoid_REL X).
  Proof.
    use funextsec ; intro y.
    use funextsec ; intros [ x₁ x₂ ] ; cbn in x₁, x₂.
    use hPropUnivalence.
    - use factor_through_squash_hProp.
      intros [ [ a₁ a₂ ] [ p H ] ].
      revert H.
      use factor_through_squash_hProp.
      intros [ [ b₁ b₂ ] [ [ q₁ q₂ ] [ q₃ q₄ ] ] ] ; cbn in q₁, q₂, q₃, q₄.
      induction q₁, q₃.
      pose (eqweqmaphProp
              (!(eqtohomot
                   (monoidfunmul
                      (@free_abmonoid_extend X (REL_comonoid_to_monoid C) (λ c x, f x c))
                      b₁ x₂)
                   y))
              (hinhpr (a₁ ,, a₂ ,, q₂ ,, q₄ ,, p)))
        as q.
      apply hinhpr.
      exact (_ ,, q ,, idpath _).
    - use factor_through_squash_hProp.
      intros [ a [ p₁ p₂ ]] ; cbn in p₁, p₂.
      induction p₂.
      assert (H := eqweqmaphProp
                     (eqtohomot
                        (monoidfunmul
                           (@free_abmonoid_extend X (REL_comonoid_to_monoid C) (λ c x, f x c))
                           x₁ x₂)
                        y)
                     p₁).
      revert H.
      use factor_through_squash_hProp.
      intros [ a₁ [ a₂ [ q₁ [ q₂ q₃ ] ] ] ] ; cbn in a₁, a₂, q₁, q₂, q₃.
      refine (hinhpr ((a₁ ,, a₂) ,, q₃ ,, _)).
      apply hinhpr ; cbn.
      simple refine ((x₁ ,, a₂) ,, (_ ,, _) ,, (_ ,, _)) ; cbn.
      + apply idpath.
      + exact q₁.
      + apply idpath.
      + exact q₂.
  Qed.

  Proposition cofree_comonoid_REL_map_counit
    : comonoid_counit REL_sym_mon_closed_cat C
      =
      cofree_comonoid_REL_underlying
      · comonoid_counit REL_sym_mon_closed_cat (cofree_comonoid_REL X).
  Proof.
    use funextsec ; intros x₁.
    use funextsec ; intros x₂.
    induction x₂.
    use hPropUnivalence.
    - intros y.
      refine (hinhpr (_ ,, _ ,, idpath _)).
      exact (eqweqmaphProp
               (!eqtohomot
                  (monoidfununel
                     (@free_abmonoid_extend X (REL_comonoid_to_monoid C) (λ c x, f x c)))
                  x₁)
               y).
    - use factor_through_squash_hProp.
      intros [ a [ p₁ p₂ ]] ; cbn in p₁, p₂, a.
      apply (eqweqmaphProp
               (eqtohomot
                  (monoidfununel
                     (@free_abmonoid_extend X (REL_comonoid_to_monoid C) (λ c x, f x c)))
                  x₁)).
      rewrite <- p₂.
      exact p₁.
  Qed.

  Definition cofree_comonoid_REL_map
    : C --> cofree_comonoid_REL X.
  Proof.
    use make_commutative_comonoid_mor.
    - exact (cofree_comonoid_REL_underlying).
    - exact cofree_comonoid_REL_map_comult.
    - exact cofree_comonoid_REL_map_counit.
  Defined.

  Proposition cofree_comonoid_REL_map_comm
    : f = cofree_comonoid_REL_underlying · map_to_cofree_comonoid_REL X.
  Proof.
    use funextsec ; intro x.
    use funextsec ; intro y.
    use hPropUnivalence.
    - intro p.
      use hinhpr.
      exact (free_abmonoid_unit y ,, p ,, idpath _).
    - use factor_through_squash_hProp.
      intros ( a & H & p ).
      simpl in a, H, p.
      rewrite <- p in H.
      exact H.
  Qed.

  Section ToMonoidMor.
    Context (φ : C --> cofree_comonoid_REL X).

    Definition comonoid_mor_REL_to_map
      : free_abmonoid X → REL_comonoid_to_monoid C
      := λ x y, pr1 φ y x.

    Proposition ismonoidfun_comonoid_mor_REL_to_map
      : ismonoidfun comonoid_mor_REL_to_map.
    Proof.
      split.
      - intros y₁ y₂.
        use funextsec ; intro x.
        use hPropUnivalence.
        + intro z.
          assert (H := eqweqmaphProp
                         (!eqtohomot
                            (eqtohomot (underlying_comonoid_mor_comult φ) x)
                            (y₁ ,, y₂))
                         (hinhpr (_ ,, z ,, idpath _))).
          revert H.
          use factor_through_squash_hProp.
          intros [ [ a₁ a₂ ] [ p H ] ].
          revert H.
          use factor_through_squash_hProp.
          intros [ [ b₁ b₂ ] [ [ q₁ q₂ ] [ q₃ q₄ ] ] ] ; cbn in q₁, q₂, q₃, q₄.
          induction q₁, q₃.
          apply hinhpr.
          exact (a₁ ,, a₂ ,, q₂ ,, q₄ ,, p).
        + use factor_through_squash_hProp.
          intros ( a₁ & a₂ & p₁ & p₂ & p₃ ).
          assert (H := eqweqmaphProp
                         (eqtohomot
                            (eqtohomot (underlying_comonoid_mor_comult φ) x)
                            (y₁ ,, y₂))
                         (hinhpr
                            ((a₁ ,, a₂)
                             ,,
                             p₃
                             ,,
                             hinhpr ((_ ,, _)
                                     ,,
                                     (idpath _ ,, p₁)
                                     ,,
                                     (idpath _ ,, p₂))))).
          revert H.
          use factor_through_squash_hProp.
          cbn.
          intros [ b [ q₁ q₂ ]].
          rewrite <- q₂ in q₁.
          exact q₁.
      - use funextsec ; intro x.
        use hPropUnivalence.
        + intro z.
          exact (eqweqmaphProp
                   (!eqtohomot (eqtohomot (underlying_comonoid_mor_counit φ) x) tt)
                   (hinhpr (_ ,, z ,, idpath _))).
        + intro z ; cbn in z.
          assert (H := eqweqmaphProp
                         (eqtohomot (eqtohomot (underlying_comonoid_mor_counit φ) x) tt)
                         z).
          revert H.
          use factor_through_squash_hProp.
          intros [ a [ p q ]] ; cbn in q.
          rewrite q in p.
          exact p.
    Qed.

    Definition comonoid_mor_REL_to_monoid_mor
      : monoidfun (free_abmonoid X) (REL_comonoid_to_monoid C)
      := comonoid_mor_REL_to_map ,, ismonoidfun_comonoid_mor_REL_to_map.
  End ToMonoidMor.

  Proposition cofree_comonoid_REL_map_unique
    : isaprop
        (∑ f',
         f
         =
         # (underlying_commutative_comonoid REL_sym_mon_closed_cat) f'
         · map_to_cofree_comonoid_REL X).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    use subtypePath.
    {
      intro.
      apply is_locally_propositional_commutative_comonoid.
    }
    enough (comonoid_mor_REL_to_monoid_mor (pr1 φ₁)
            =
            comonoid_mor_REL_to_monoid_mor (pr1 φ₂))
      as H.
    {
      use funextsec ; intro y₁.
      use funextsec ; intro y₂.
      use hPropUnivalence.
      - intro p.
        exact (eqweqmaphProp (eqtohomot (eqtohomot (maponpaths pr1 H) y₂) y₁) p).
      - intro p.
        exact (eqweqmaphProp (!eqtohomot (eqtohomot (maponpaths pr1 H) y₂) y₁) p).
    }
    use free_abmonoid_mor_eq.
    intro x ; cbn.
    use funextsec ; intro y.
    use hPropUnivalence.
    - intros a.
      unfold comonoid_mor_REL_to_map in a.
      assert (p := eqweqmaphProp
                     (eqtohomot
                        (eqtohomot (!(pr2 φ₁) @ pr2 φ₂) y)
                        x)
                     (hinhpr (_ ,, a ,, idpath _))).
      revert p.
      use factor_through_squash_hProp.
      cbn ; intros [ b [ p₁ p₂ ] ].
      rewrite <- p₂ in p₁.
      exact p₁.
    - intros a.
      unfold comonoid_mor_REL_to_map in a.
      assert (p := eqweqmaphProp
                     (!eqtohomot
                        (eqtohomot (!(pr2 φ₁) @ pr2 φ₂) y)
                        x)
                     (hinhpr (_ ,, a ,, idpath _))).
      revert p.
      use factor_through_squash_hProp.
      cbn ; intros [ b [ p₁ p₂ ] ].
      rewrite <- p₂ in p₁.
      exact p₁.
  Qed.

  Corollary cofree_comonoid_REL_map_contr
    : iscontr
        (∑ f' : commutative_comonoid_category REL_sym_mon_closed_cat ⟦ C, cofree_comonoid_REL X ⟧,
         f
         =
         # (underlying_commutative_comonoid REL_sym_mon_closed_cat) f'
         · map_to_cofree_comonoid_REL X).
  Proof.
    use iscontraprop1.
    - apply cofree_comonoid_REL_map_unique.
    - simple refine (_ ,, _).
      + exact cofree_comonoid_REL_map.
      + exact cofree_comonoid_REL_map_comm.
  Defined.
End CofreeComonoidUMP.

(** * 4. The relational model of linear logic *)
Definition relational_model
  : lafont_category.
Proof.
  use make_lafont_category.
  - exact REL_sym_mon_closed_cat.
  - use left_adjoint_from_partial.
    + exact cofree_comonoid_REL.
    + exact map_to_cofree_comonoid_REL.
    + exact cofree_comonoid_REL_map_contr.
Defined.
