(******************************************************************************************

 Lax extensions of endofunctors on sets

 Suppose that we have an endofunctor `F` on sets. Our goal is to define a suitable notion of
 bisimilarity for coalgebras for `F`. To do so, we need a suitable action of `F` on relations.
 There are various notions that describe that, and in this file, we look at lax extensions.
 In essence, a lax extension of `F` extends `F` to a lax double functor on the double category
 of enriched relations, and in another file, we prove that these notions are actually
 equivalent. In this file, we set up the basic notions and properties that are needed for
 the theory of lax extensions.

 References
 - "Monoidal Topology: A Categorical Approach to Order, Metric and Topology", editors Dirk
   Hofmann, Gavin Seal, Walter Tholen.
 - "Relation lifting, a survey" by Kurz and Velebil

 Content
 1. Definition of lax extensions
 2. Builder and equality
 3. Functors with a lax extension
 4. Properties of lax extensions

 ******************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.EnrichedCats.BenabouCosmos.
Require Import UniMath.CategoryTheory.EnrichedCats.EnrichedRelation.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Limits.Coproducts.

Local Open Scope cat.
Local Open Scope moncat.

Import MonoidalNotations.

(** * 1. Definition of lax extensions *)
Definition lax_extension_data
           (V : quantale_cosmos)
           (F : SET ⟶ SET)
  : UU
  := ∏ (X Y : hSet),
     enriched_relation V X Y
     →
     enriched_relation V (F X) (F Y).

Definition lax_extension_laws
           {V : quantale_cosmos}
           {F : SET ⟶ SET}
           (L : lax_extension_data V F)
  : UU
  := (∏ (X Y : hSet)
        (R S : enriched_relation V X Y),
      R ≤e S → L _ _ R ≤e L _ _ S)
     ×
     (∏ (X Y Z : hSet)
        (R : enriched_relation V X Y)
        (S : enriched_relation V Y Z),
      L _ _ R ·e L _ _ S ≤e L _ _ (R ·e S))
     ×
     (∏ (X Y : hSet)
        (f : X → Y),
      (#F f)^* ≤e L _ _ (f^*))
     ×
     (∏ (X Y : hSet)
        (f : X → Y),
      (#F f)^o ≤e L _ _ (f^o)).

Proposition isaprop_lax_extension_laws
            {V : quantale_cosmos}
            {F : SET ⟶ SET}
            (L : lax_extension_data V F)
  : isaprop (lax_extension_laws L).
Proof.
  repeat (use isapropdirprod) ;
  repeat (use impred ; intro) ;
  apply is_poset_category_quantale_cosmos.
Qed.

Definition lax_extension
           (V : quantale_cosmos)
           (F : SET ⟶ SET)
  : UU
  := ∑ (L : lax_extension_data V F), lax_extension_laws L.

Definition lax_extension_rel
           {V : quantale_cosmos}
           {F : SET ⟶ SET}
           (L : lax_extension V F)
           {X Y : hSet}
           (R : enriched_relation V X Y)
  : enriched_relation V (F X) (F Y)
  := pr1 L X Y R.

Coercion lax_extension_rel : lax_extension >-> Funclass.

Proposition lax_extension_enriched_rel_le
            {V : quantale_cosmos}
            {F : SET ⟶ SET}
            (L : lax_extension V F)
            {X Y : hSet}
            {R S : enriched_relation V X Y}
            (p : R ≤e S)
  : L _ _ R ≤e L _ _ S.
Proof.
  exact (pr12 L X Y R S p).
Defined.

Proposition lax_extension_enriched_rel_comp
            {V : quantale_cosmos}
            {F : SET ⟶ SET}
            (L : lax_extension V F)
            {X Y Z : hSet}
            (R : enriched_relation V X Y)
            (S : enriched_relation V Y Z)
  : L _ _ R ·e L _ _ S ≤e L _ _ (R ·e S).
Proof.
  exact (pr122 L X Y Z R S).
Defined.

Proposition lax_extension_enriched_rel_companion
            {V : quantale_cosmos}
            {F : SET ⟶ SET}
            (L : lax_extension V F)
            {X Y : hSet}
            (f : X → Y)
  : (#F f)^* ≤e L _ _ (f^*).
Proof.
  exact (pr1 (pr222 L) X Y f).
Defined.

Proposition lax_extension_enriched_rel_conjoint
            {V : quantale_cosmos}
            {F : SET ⟶ SET}
            (L : lax_extension V F)
            {X Y : hSet}
            (f : X → Y)
  : (#F f)^o ≤e L _ _ (f^o).
Proof.
  exact (pr2 (pr222 L) X Y f).
Defined.

(** * 2. Builder and equality *)
Definition make_lax_extension
           (V : quantale_cosmos)
           (F : SET ⟶ SET)
           (L : lax_extension_data V F)
           (HL : lax_extension_laws L)
  : lax_extension V F
  := L ,, HL.

Proposition eq_lax_extension
            {V : quantale_cosmos}
            {F : SET ⟶ SET}
            {L L' : lax_extension V F}
            (p : ∏ (X Y : hSet)
                   (R : enriched_relation V X Y),
                 L X Y R = L' X Y R)
  : L = L'.
Proof.
  use subtypePath.
  {
    intro.
    apply isaprop_lax_extension_laws.
  }
  use funextsec ; intro X.
  use funextsec ; intro Y.
  use funextsec ; intro R.
  exact (p X Y R).
Qed.

(** * 3. Functors with a lax extension *)
Definition functor_with_lax_extension
           (V : quantale_cosmos)
  : UU
  := ∑ (F : SET ⟶ SET), lax_extension V F.

Coercion functor_with_lax_extension_to_functor
         {V : quantale_cosmos}
         (F : functor_with_lax_extension V)
  : SET ⟶ SET.
Proof.
  exact (pr1 F).
Defined.

Definition lax_extension_of_functor
           {V : quantale_cosmos}
           (F : functor_with_lax_extension V)
  : lax_extension V F.
Proof.
  exact (pr2 F).
Defined.

(** * 4. Properties of lax extensions *)
Proposition lax_extension_companion_left
            {V : quantale_cosmos}
            {F : SET ⟶ SET}
            (L : lax_extension V F)
            {X Y Z : hSet}
            (f : X → Y)
            (R : enriched_relation V Y Z)
  : L _ _ (f^* ·e R)
    =
    (#F f)^* ·e L _ _ R.
Proof.
  use eq_enriched_relation_le.
  - refine (enriched_relation_le_trans _ _).
    {
      use enriched_relation_square_to_le.
      apply enriched_relation_linvunitor.
    }
    refine (enriched_relation_le_trans _ _).
    {
      refine (enriched_relation_le_comp _ (enriched_relation_le_refl _)).
      exact (comp_companion_conjoint_enriched_relation (#F f)).
    }
    refine (enriched_relation_le_trans _ _).
    {
      use enriched_relation_square_to_le.
      apply enriched_relation_lassociator.
    }
    refine (enriched_relation_le_comp (enriched_relation_le_refl _) _).
    refine (enriched_relation_le_trans _ _).
    {
      refine (enriched_relation_le_comp _ (enriched_relation_le_refl _)).
      apply (lax_extension_enriched_rel_conjoint L).
    }
    refine (enriched_relation_le_trans _ _).
    {
      apply lax_extension_enriched_rel_comp.
    }
    use lax_extension_enriched_rel_le.
    refine (enriched_relation_le_trans _ _).
    {
      use enriched_relation_square_to_le.
      apply enriched_relation_rassociator.
    }
    refine (enriched_relation_le_trans _ _).
    {
      refine (enriched_relation_le_comp _ (enriched_relation_le_refl _)).
      apply comp_conjoint_companion_enriched_relation.
    }
    use enriched_relation_square_to_le.
    apply enriched_relation_lunitor.
  - intros x z.
    refine (_ · lax_extension_enriched_rel_comp _ _ _ _ _).
    use enriched_relation_le_comp.
    + apply lax_extension_enriched_rel_companion.
    + apply enriched_relation_le_refl.
Qed.

Proposition lax_extension_conjoint_right
            {V : quantale_cosmos}
            {F : SET ⟶ SET}
            (L : lax_extension V F)
            {X Y Z : hSet}
            (f : Z → Y)
            (R : enriched_relation V X Y)
  : L _ _ (R ·e f^o)
    =
    L _ _ R ·e (#F f)^o.
Proof.
  use eq_enriched_relation_le.
  - refine (enriched_relation_le_trans _ _).
    {
      use enriched_relation_square_to_le.
      apply enriched_relation_rinvunitor.
    }
    refine (enriched_relation_le_trans _ _).
    {
      refine (enriched_relation_le_comp (enriched_relation_le_refl _) _).
      exact (comp_companion_conjoint_enriched_relation (#F f)).
    }
    refine (enriched_relation_le_trans _ _).
    {
      use enriched_relation_square_to_le.
      apply enriched_relation_rassociator.
    }
    refine (enriched_relation_le_comp _ (enriched_relation_le_refl _)).
    refine (enriched_relation_le_trans _ _).
    {
      refine (enriched_relation_le_comp (enriched_relation_le_refl _) _).
      apply (lax_extension_enriched_rel_companion L).
    }
    refine (enriched_relation_le_trans _ _).
    {
      apply lax_extension_enriched_rel_comp.
    }
    use lax_extension_enriched_rel_le.
    refine (enriched_relation_le_trans _ _).
    {
      use enriched_relation_square_to_le.
      apply enriched_relation_lassociator.
    }
    refine (enriched_relation_le_trans _ _).
    {
      refine (enriched_relation_le_comp (enriched_relation_le_refl _) _).
      apply comp_conjoint_companion_enriched_relation.
    }
    use enriched_relation_square_to_le.
    apply enriched_relation_runitor.
  - intros x z.
    refine (_ · lax_extension_enriched_rel_comp _ _ _ _ _).
    use enriched_relation_le_comp.
    + apply enriched_relation_le_refl.
    + apply lax_extension_enriched_rel_conjoint.
Qed.

Proposition lax_extension_companion_conjoint
            {V : quantale_cosmos}
            {F : SET ⟶ SET}
            (L : lax_extension V F)
            {W X Y Z : hSet}
            (f : W → X)
            (g : Z → Y)
            (R : enriched_relation V X Y)
  : L _ _ (f^* ·e R ·e g^o)
    =
    (#F f)^* ·e L _ _ R ·e (#F g)^o.
Proof.
  rewrite <- lax_extension_companion_left.
  rewrite lax_extension_conjoint_right.
  apply idpath.
Qed.

Proposition lax_extension_id_enriched_relation
            {V : quantale_cosmos}
            {F : SET ⟶ SET}
            (L : lax_extension V F)
            (X : hSet)
  : id_enriched_relation (F X) ≤e L _ _ (id_enriched_relation X).
Proof.
  rewrite <- !companion_enriched_relation_id.
  refine (enriched_relation_le_trans _ (lax_extension_enriched_rel_companion L (idfun X))).
  use enriched_relation_companion_le.
  refine (!_).
  exact (functor_id F X).
Qed.

Proposition lax_extension_enriched_relation_square
            {V : quantale_cosmos}
            {F : SET ⟶ SET}
            (L : lax_extension V F)
            {X₁ X₂ Y₁ Y₂ : hSet}
            {R : enriched_relation V X₁ Y₁}
            {S : enriched_relation V X₂ Y₂}
            {f : X₁ → X₂}
            {g : Y₁ → Y₂}
            (p : enriched_relation_square f g R S)
  : enriched_relation_square (# F f) (# F g) (L X₁ Y₁ R) (L X₂ Y₂ S).
Proof.
  unfold enriched_relation_square in *.
  rewrite <- enriched_relation_comp_conj.
  rewrite <- lax_extension_conjoint_right.
  rewrite <- lax_extension_companion_left.
  apply lax_extension_enriched_rel_le.
  rewrite enriched_relation_comp_conj.
  apply p.
Qed.
