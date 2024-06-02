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
 10. Conjoints of enriched relations
 11. Calculational lemmas
 12. Basic properties of the order of enriched relations

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

Proposition eq_enriched_relation
            {V : quantale_cosmos}
            {X Y : hSet}
            {R R' : enriched_relation V X Y}
            (p : ∏ (x : X) (y : Y), R x y --> R' x y)
            (q : ∏ (x : X) (y : Y), R' x y --> R x y)
  : R = R'.
Proof.
  use funextsec ; intro x.
  use funextsec ; intro y.
  use isotoid.
  {
    apply is_univalent_quantale_cosmos.
  }
  use make_z_iso.
  - exact (p x y).
  - exact (q x y).
  - split ; apply is_poset_category_quantale_cosmos.
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


  Notation "R ·e S" := (comp_enriched_relation R S) (at level 40) : cat.

  (** * 3. Order on enriched relations *)
  Definition enriched_relation_le
             {X Y : hSet}
             (R S : enriched_relation V X Y)
    : UU
    := ∏ (x : X) (y : Y), R x y --> S x y.

  Notation "R ≤e S" := (enriched_relation_le R S) (at level 70) : cat.

  Proposition isaprop_enriched_relation_le
              {X Y : hSet}
              (R S : enriched_relation V X Y)
    : isaprop (enriched_relation_le R S).
  Proof.
    do 2 (use impred ; intro).
    apply is_poset_category_quantale_cosmos.
  Qed.

  Proposition eq_enriched_relation_le
              {X Y : hSet}
              {R R' : enriched_relation V X Y}
              (p : R ≤e R')
              (q : R' ≤e R)
    : R = R'.
  Proof.
    use eq_enriched_relation.
    - exact p.
    - exact q.
  Qed.

  (** * 4. Squares of enriched relations *)
  Definition fun_comp_enriched_relation
              {W X Y Z : hSet}
              (R : enriched_relation V X Y)
              (f : W → X)
              (g : Z → Y)
    : enriched_relation V W Z
    := λ (w : W) (z : Z), R (f w) (g z).

  Definition enriched_relation_square
             {X₁ X₂ Y₁ Y₂ : hSet}
             (f : X₁ → X₂)
             (g : Y₁ → Y₂)
             (R₁ : enriched_relation V X₁ Y₁)
             (R₂ : enriched_relation V X₂ Y₂)
    : UU
    := R₁ ≤e fun_comp_enriched_relation R₂ f g.

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

  Proposition enriched_relation_square_to_le
              {X Y : hSet}
              {R₁ : enriched_relation V X Y}
              {R₂ : enriched_relation V X Y}
              (p : enriched_relation_square (idfun _) (idfun _) R₁ R₂)
    : R₁ ≤e R₂.
  Proof.
    exact p.
  Qed.

  Proposition enriched_relation_le_to_square
              {X Y : hSet}
              {R₁ : enriched_relation V X Y}
              {R₂ : enriched_relation V X Y}
              (p : R₁ ≤e R₂)
    : enriched_relation_square (idfun _) (idfun _) R₁ R₂.
  Proof.
    exact p.
  Qed.

  (** * 5. Associators and unitors *)
  Proposition enriched_relation_lunitor
              {X Y : hSet}
              (R : enriched_relation V X Y)
    : enriched_relation_square
        (idfun _)
        (idfun _)
        (id_enriched_relation _ ·e R)
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
        (id_enriched_relation _ ·e R).
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
        (R ·e id_enriched_relation _)
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
        (R ·e id_enriched_relation _).
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
        ((R₁ ·e R₂) ·e R₃)
        (R₁ ·e (R₂ ·e R₃)).
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
        (R₁ ·e (R₂ ·e R₃))
        ((R₁ ·e R₂) ·e R₃).
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
        (R₁ ·e S₁)
        (R₂ ·e S₂).
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

  Notation "f ^*" := (companion_enriched_relation f) (at level 20) : cat.

  Proposition companion_enriched_relation_id
              (X : hSet)
    : (idfun X)^* = id_enriched_relation X.
  Proof.
    apply idpath.
  Qed.

  Proposition companion_enriched_relation_comp
              {X Y Z : hSet}
              (f : X → Y)
              (g : Y → Z)
    : (λ x, g(f x))^* ≤e f^* ·e g^*.
  Proof.
    intros x z.
    use CoproductArrow ; cbn.
    intro p.
    refine (_ · CoproductIn _ _ _ (f x)).
    refine (_ · (CoproductIn _ _ _ (idpath _) #⊗ CoproductIn _ _ _ p)).
    apply mon_linvunitor.
  Qed.

  Proposition companion_enriched_relation_left
              {X Y : hSet}
              (f : X → Y)
    : enriched_relation_square
        f (idfun _)
        (f^*) (id_enriched_relation Y).
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
        (id_enriched_relation X) (f^*).
  Proof.
    intros x y.
    use CoproductArrow.
    intro p.
    exact (CoproductIn _ _ _ (maponpaths f p)).
  Qed.

  (** * 10. Conjoints of enriched relations *)
  Definition conjoint_enriched_relation
             {X Y : hSet}
             (f : X → Y)
    : enriched_relation V Y X
    := enriched_relation_converse (companion_enriched_relation f).

  Notation "f ^o" := (conjoint_enriched_relation f) (at level 20) : cat.

  Proposition conjoint_enriched_relation_id
              (X : hSet)
    : (idfun X)^o = id_enriched_relation X.
  Proof.
    use eq_enriched_relation.
    - intros x y.
      use CoproductArrow ; cbn.
      intro p.
      exact (CoproductIn _ _ _ (!p)).
    - intros x y.
      use CoproductArrow ; cbn.
      intro p.
      exact (CoproductIn _ _ _ (!p)).
  Qed.

  Proposition conjoint_enriched_relation_comp
              {X Y Z : hSet}
              (f : X → Y)
              (g : Y → Z)
    : (λ x, g(f x))^o ≤e g^o ·e f^o.
  Proof.
    intros z x.
    use CoproductArrow ; cbn.
    intro p.
    refine (_ · CoproductIn _ _ _ (f x)).
    refine (_ · (CoproductIn _ _ _ p #⊗ CoproductIn _ _ _ (idpath _))).
    apply mon_linvunitor.
  Qed.

  Proposition conjoint_enriched_relation_left
              {X Y : hSet}
              (f : X → Y)
    : enriched_relation_square
        f (idfun _)
        (id_enriched_relation X) (f^o).
  Proof.
    intros x y.
    use CoproductArrow.
    intro p.
    exact (CoproductIn _ _ _ (maponpaths f (!p))).
  Qed.

  Proposition conjoint_enriched_relation_right
              {X Y : hSet}
              (f : X → Y)
    : enriched_relation_square
        (idfun _) f
        (f^o) (id_enriched_relation Y).
  Proof.
    intros x y.
    use CoproductArrow.
    intro p.
    exact (CoproductIn _ _ _ (!p)).
  Qed.

  Proposition comp_companion_conjoint_enriched_relation
              {X Y : hSet}
              (f : X → Y)
    : enriched_relation_le
        (id_enriched_relation _)
        (f^* ·e f^o).
  Proof.
    intros x x'.
    use CoproductArrow.
    intro p ; induction p ; cbn.
    refine (_ · CoproductIn _ _ _ (f x)).
    refine (_ · (CoproductIn _ _ _ (idpath _) #⊗ CoproductIn _ _ _ (idpath _))).
    apply mon_linvunitor.
  Qed.

  Proposition comp_conjoint_companion_enriched_relation
              {X Y : hSet}
              (f : X → Y)
    : enriched_relation_le
        (f^o ·e f^*)
        (id_enriched_relation _).
  Proof.
    intros y y'.
    use CoproductArrow ; cbn.
    intro x.
    use arrow_from_tensor_coproduct_benabou_cosmos.
    intro p.
    refine (sym_mon_braiding _ _ _ · _).
    use arrow_from_tensor_coproduct_benabou_cosmos.
    intro q.
    cbn.
    refine (_ · CoproductIn _ _ _ _).
    - apply mon_lunitor.
    - exact (!q @ p).
  Qed.

  (** * 11. Calculational lemmas *)
  Proposition enriched_relation_comp_fun_left
              {X Y Z : hSet}
              (f : X → Y)
              (R : enriched_relation V Y Z)
    : f^* ·e R
      =
      fun_comp_enriched_relation R f (idfun _).
  Proof.
    use eq_enriched_relation.
    - intros x z.
      use CoproductArrow.
      intro y.
      refine (sym_mon_braiding _ _ _ · _).
      use arrow_from_tensor_coproduct_benabou_cosmos.
      intro p ; cbn.
      induction p.
      apply mon_runitor.
    - intros x z.
      exact (mon_linvunitor _
             · (CoproductIn _ _ _ (idpath _) #⊗ identity _)
             · CoproductIn _ _ _ (f x)).
  Qed.

  Proposition enriched_relation_conj_fun_right
              {X Y Z : hSet}
              (R : enriched_relation V X Y)
              (f : Z → Y)
    : R ·e f^o
      =
      fun_comp_enriched_relation R (idfun _) f.
  Proof.
    use eq_enriched_relation.
    - intros x z.
      use CoproductArrow.
      intro y.
      use arrow_from_tensor_coproduct_benabou_cosmos.
      intro p ; cbn.
      induction p.
      apply mon_runitor.
    - intros x z.
      exact (mon_rinvunitor _
             · (identity _ #⊗ CoproductIn _ _ _ (idpath _))
             · CoproductIn _ _ _ (f z)).
  Qed.

  Proposition enriched_relation_comp_conj
              {W X Y Z : hSet}
              (R : enriched_relation V X Y)
              (f : W → X)
              (g : Z → Y)
    : f^* ·e (R ·e g^o)
      =
      fun_comp_enriched_relation R f g.
  Proof.
    use eq_enriched_relation.
    - intros w z.
      use CoproductArrow.
      intro x.
      use arrow_from_tensor_coproduct_benabou_cosmos.
      intro y.
      refine (sym_mon_braiding _ _ _ · _).
      use arrow_from_tensor_coproduct_benabou_cosmos.
      intro p ; cbn.
      induction p.
      refine (mon_runitor _ · _).
      use arrow_from_tensor_coproduct_benabou_cosmos.
      intro q ; cbn.
      induction q.
      apply mon_runitor.
    - intros w z.
      refine (_ · CoproductIn _ _ _ (f w)) ; cbn.
      refine (_ · (CoproductIn _ _ _ (idpath _) #⊗ identity _)).
      refine (mon_linvunitor _ · (identity _ #⊗ _)).
      refine (_ · CoproductIn _ _ _ (g z)).
      refine (mon_rinvunitor _ · (identity _ #⊗ _)).
      exact (CoproductIn _ _ _ (idpath _)).
  Qed.

  (** * 12. Basic properties of the order of enriched relations *)
  Proposition enriched_relation_le_refl
              {X Y : hSet}
              (R : enriched_relation V X Y)
    : enriched_relation_le R R.
  Proof.
    intros x y.
    apply identity.
  Qed.

  Proposition enriched_relation_eq_to_le
              {X Y : hSet}
              {R S : enriched_relation V X Y}
              (p : R = S)
    : enriched_relation_le R S.
  Proof.
    induction p.
    apply enriched_relation_le_refl.
  Qed.

  Proposition enriched_relation_le_trans
              {X Y : hSet}
              {R₁ R₂ R₃ : enriched_relation V X Y}
              (p : enriched_relation_le R₁ R₂)
              (q : enriched_relation_le R₂ R₃)
    : enriched_relation_le R₁ R₃.
  Proof.
    intros x y.
    exact (p _ _ · q _ _).
  Qed.

  Proposition enriched_relation_le_comp
              {X Y Z : hSet}
              {R₁ R₂ : enriched_relation V X Y}
              {S₁ S₂ : enriched_relation V Y Z}
              (p : enriched_relation_le R₁ R₂)
              (q : enriched_relation_le S₁ S₂)
    : enriched_relation_le
        (R₁ ·e S₁)
        (R₂ ·e S₂).
  Proof.
    intros x z.
    use CoproductArrow.
    intros y ; cbn.
    exact ((p _ _ #⊗ q _ _) · CoproductIn _ _ _ y).
  Qed.

  Proposition enriched_relation_companion_le
              {X Y : hSet}
              {f g : X → Y}
              (p : f = g)
    : enriched_relation_le (f^*) (g^*).
  Proof.
    use enriched_relation_eq_to_le.
    induction p.
    apply idpath.
  Qed.

  Proposition enriched_relation_conjoint_le
              {X Y : hSet}
              {f g : X → Y}
              (p : f = g)
    : enriched_relation_le (f^o) (g^o).
  Proof.
    use enriched_relation_eq_to_le.
    induction p.
    apply idpath.
  Qed.
End EnrichedRelation.

Notation "R ·e S" := (comp_enriched_relation R S) (at level 40) : cat.
Notation "R ≤e S" := (enriched_relation_le R S) (at level 70) : cat.
Notation "f ^*" := (companion_enriched_relation f) (at level 20) : cat.
Notation "f ^o" := (conjoint_enriched_relation f) (at level 20) : cat.
