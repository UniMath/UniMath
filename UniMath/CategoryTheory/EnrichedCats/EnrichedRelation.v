(******************************************************************************************

 Enriched relations

 Let `V` be a quantale. Then an enriched relation between two sets `X` and `Y` is given by
 a map `X → Y → V`. This generalizes the notion of a binary relation, which would be a
 relation enriched in `hProp`. In this file, we give the basic definitions on enriched
 relations.

 Recall that the identity relation on a set `X` is defined to be the relation that sends
 every `x : X` and `y : X` to the proposition `x = y`. To define the enriched version of
 this relation, we take the supremum of a constant diagram over `x = y`, whose value are
 given by the monoidal unit of `V`. The composition of quantale enriched relations follows
 the same idea as the composition of ordinary relations.

 To define all operations (unitors, associators, identity, composition) on squares, we use
 the universal property. Here we use that `V` is symmetric monoidal closed. More specifically,
 we use that tensoring preserves coproducts. The remainder is a matter of applying universal
 properties.

 Content
 1. Enriched relations
 2. Identity and composition of enriched relations
 3. Order on enriched relations
 4. Squares of enriched relations
 5. Associators and unitors
 6. Identity squares
 7. Composition of squares
 8. Converses of enriched relations
 9. Companion pairs of enriched relations

 ******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.PosetCat.
Require Import UniMath.CategoryTheory.Limits.Coends.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

(** * 1. Enriched relations *)
Definition enriched_relation
           (V : quantale_cosmos)
           (X Y : hSet)
  : UU
  := X → Y → V.

Proposition isaset_enriched_relation
            (V : quantale_cosmos)
            (X Y : hSet)
  : isaset (enriched_relation V X Y).
Proof.
  use funspace_isaset.
  use funspace_isaset.
  exact (isaset_ob_poset (_ ,, is_poset_category_quantale_cosmos V)).
Qed.

Section EnrichedRelation.
  Context {V : quantale_cosmos}.

  (** * 2. Identity and composition of enriched relations *)
  Definition id_enriched_relation
             (X : hSet)
    : enriched_relation V X X
    := λ (x y : X),
       benabou_cosmos_coproducts
         V
         (x = y)
         (λ _, I_{V}).

  Definition comp_enriched_relation
             {X Y Z : hSet}
             (R : enriched_relation V X Y)
             (S : enriched_relation V Y Z)
    : enriched_relation V X Z
    := λ (x : X)
         (z : Z),
       benabou_cosmos_coproducts
         V
         Y
         (λ (y : Y), R x y ⊗ S y z).

  (** * 3. Order on enriched relations *)
  Definition enriched_relation_le
             {X Y : hSet}
             (R S : enriched_relation V X Y)
    : UU
    := ∏ (x : X) (y : Y), R x y --> S x y.

  Proposition isaprop_enriched_relation_le
              {X Y : hSet}
              (R S : enriched_relation V X Y)
    : isaprop (enriched_relation_le R S).
  Proof.
    do 2 (use impred ; intro).
    apply is_poset_category_quantale_cosmos.
  Qed.

  (** * 4. Squares of enriched relations *)
  Definition enriched_relation_square
             {X₁ X₂ Y₁ Y₂ : hSet}
             (f : X₁ → X₂)
             (g : Y₁ → Y₂)
             (R₁ : enriched_relation V X₁ Y₁)
             (R₂ : enriched_relation V X₂ Y₂)
    : UU
    := ∏ (x : X₁)
         (y : Y₁),
       R₁ x y --> R₂ (f x) (g y).

  Proposition isaprop_enriched_relation_square
              {X₁ X₂ Y₁ Y₂ : hSet}
              (f : X₁ → X₂)
              (g : Y₁ → Y₂)
              (R₁ : enriched_relation V X₁ Y₁)
              (R₂ : enriched_relation V X₂ Y₂)
    : isaprop (enriched_relation_square f g R₁ R₂).
  Proof.
    do 2 (use impred ; intro).
    apply is_poset_category_quantale_cosmos.
  Qed.

  (** * 5. Associators and unitors *)
  Proposition enriched_relation_lunitor
              {X Y : hSet}
              (R : enriched_relation V X Y)
    : enriched_relation_square
        (idfun _)
        (idfun _)
        (comp_enriched_relation (id_enriched_relation _) R)
        R.
  Proof.
    intros x y ; cbn.
    use CoproductArrow.
    intro y' ; cbn.
    refine (sym_mon_braiding _ _ _ · _).
    use arrow_from_tensor_coproduct_benabou_cosmos.
    intro p ; cbn.
    induction p.
    apply mon_runitor.
  Qed.

  Proposition enriched_relation_linvunitor
              {X Y : hSet}
              (R : enriched_relation V X Y)
    : enriched_relation_square
        (idfun _)
        (idfun _)
        R
        (comp_enriched_relation (id_enriched_relation _) R).
  Proof.
    intros x y ; cbn.
    refine (_ · CoproductIn _ _ _ x).
    refine (mon_linvunitor _ · _).
    refine (_ #⊗ identity _).
    exact (CoproductIn _ _ _ (idpath x)).
  Qed.

  Proposition enriched_relation_runitor
              {X Y : hSet}
              (R : enriched_relation V X Y)
    : enriched_relation_square
        (idfun _)
        (idfun _)
        (comp_enriched_relation R (id_enriched_relation _))
        R.
  Proof.
    intros x y ; cbn.
    use CoproductArrow.
    intro y'.
    use arrow_from_tensor_coproduct_benabou_cosmos.
    intro p ; cbn.
    induction p.
    apply mon_runitor.
  Qed.

  Proposition enriched_relation_rinvunitor
              {X Y : hSet}
              (R : enriched_relation V X Y)
    : enriched_relation_square
        (idfun _)
        (idfun _)
        R
        (comp_enriched_relation R (id_enriched_relation _)).
  Proof.
    intros x y ; cbn.
    refine (_ · CoproductIn _ _ _ y).
    refine (mon_rinvunitor _ · _).
    refine (identity _ #⊗ _).
    exact (CoproductIn _ _ _ (idpath y)).
  Qed.

  Proposition enriched_relation_lassociator
              {W X Y Z : hSet}
              (R₁ : enriched_relation V W X)
              (R₂ : enriched_relation V X Y)
              (R₃ : enriched_relation V Y Z)
    : enriched_relation_square
        (idfun _)
        (idfun _)
        (comp_enriched_relation (comp_enriched_relation R₁ R₂) R₃)
        (comp_enriched_relation R₁ (comp_enriched_relation R₂ R₃)).
  Proof.
    intros w z ; cbn.
    use CoproductArrow.
    intro y ; cbn.
    refine (sym_mon_braiding _ _ _ · _).
    use arrow_from_tensor_coproduct_benabou_cosmos.
    intro x ; cbn.
    refine (sym_mon_braiding _ _ _ · _).
    refine (mon_lassociator _ _ _ · _).
    refine ((identity _ #⊗ _)· CoproductIn _ _ _ x).
    exact (CoproductIn _ _ _ y).
  Qed.

  Proposition enriched_relation_rassociator
              {W X Y Z : hSet}
              (R₁ : enriched_relation V W X)
              (R₂ : enriched_relation V X Y)
              (R₃ : enriched_relation V Y Z)
    : enriched_relation_square
        (idfun _)
        (idfun _)
        (comp_enriched_relation R₁ (comp_enriched_relation R₂ R₃))
        (comp_enriched_relation (comp_enriched_relation R₁ R₂) R₃).
  Proof.
    intros w z ; cbn.
    use CoproductArrow.
    intro x.
    use arrow_from_tensor_coproduct_benabou_cosmos.
    intro y ; cbn.
    refine (mon_rassociator _ _ _ · _).
    refine ((_ #⊗ identity _)· CoproductIn _ _ _ y).
    exact (CoproductIn _ _ _ x).
  Qed.

  (** * 6. Identity squares *)
  Definition id_v_enriched_relation_square
             {X Y : hSet}
             (R : enriched_relation V X Y)
    : enriched_relation_square (idfun _) (idfun _) R R.
  Proof.
    intros x y ; cbn.
    apply identity.
  Qed.

  Definition id_h_enriched_relation_square
             {X Y : hSet}
             (f : X → Y)
    : enriched_relation_square
        f f
        (id_enriched_relation X) (id_enriched_relation Y).
  Proof.
    intros x y.
    use CoproductArrow.
    intro p.
    induction p ; cbn.
    exact (CoproductIn _ _ _ (idpath _)).
  Qed.

  (** * 7. Composition of squares *)
  Definition comp_v_enriched_relation_square
             {X₁ X₂ X₃ Y₁ Y₂ Y₃ : hSet}
             {f₁ : X₁ → X₂} {f₂ : X₂ → X₃}
             {g₁ : Y₁ → Y₂} {g₂ : Y₂ → Y₃}
             {R₁ : enriched_relation V X₁ Y₁}
             {R₂ : enriched_relation V X₂ Y₂}
             {R₃ : enriched_relation V X₃ Y₃}
             (τ : enriched_relation_square f₁ g₁ R₁ R₂)
             (θ : enriched_relation_square f₂ g₂ R₂ R₃)
    : enriched_relation_square (f₂ ∘ f₁)%functions (g₂ ∘ g₁)%functions R₁ R₃.
  Proof.
    intros x y.
    exact (τ x y · θ (f₁ x) (g₁ y)).
  Qed.

  Definition comp_h_enriched_relation_square
             {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : hSet}
             {f : X₁ → X₂}
             {g : Y₁ → Y₂}
             {h : Z₁ → Z₂}
             {R₁ : enriched_relation V X₁ Y₁}
             {S₁ : enriched_relation V Y₁ Z₁}
             {R₂ : enriched_relation V X₂ Y₂}
             {S₂ : enriched_relation V Y₂ Z₂}
             (τ : enriched_relation_square f g R₁ R₂)
             (θ : enriched_relation_square g h S₁ S₂)
    : enriched_relation_square
        f h
        (comp_enriched_relation R₁ S₁)
        (comp_enriched_relation R₂ S₂).
  Proof.
    intros x z.
    use CoproductArrow.
    intro y ; cbn.
    refine (_ · CoproductIn _ _ _ (g y)).
    exact (τ x y #⊗ θ y z).
  Qed.

  (** * 8. Converses of enriched relations *)
  Definition enriched_relation_converse
             {X Y : hSet}
             (R : enriched_relation V X Y)
    : enriched_relation V Y X
    := λ y x, R x y.

  (** * 9. Companion pairs of enriched relations *)
  Definition companion_enriched_relation
             {X Y : hSet}
             (f : X → Y)
    : enriched_relation V X Y
    := λ (x : X) (y : Y),
       benabou_cosmos_coproducts
         V
         (f x = y)
         (λ _, I_{V}).

  Proposition companion_enriched_relation_left
              {X Y : hSet}
              (f : X → Y)
    : enriched_relation_square
        f (idfun _)
        (companion_enriched_relation f) (id_enriched_relation Y).
  Proof.
    intros x y.
    use CoproductArrow.
    intro p.
    exact (CoproductIn _ _ _ p).
  Qed.

  Proposition companion_enriched_relation_right
              {X Y : hSet}
              (f : X → Y)
    : enriched_relation_square
        (idfun _) f
        (id_enriched_relation X) (companion_enriched_relation f).
  Proof.
  Proof.
    intros x y.
    use CoproductArrow.
    intro p.
    exact (CoproductIn _ _ _ (maponpaths f p)).
  Qed.
End EnrichedRelation.
