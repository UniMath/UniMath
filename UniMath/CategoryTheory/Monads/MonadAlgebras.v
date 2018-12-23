(** ***************************************************************

Contents :

  - Definition of the category of algebras of a monad

  - The free-forgetful adjunction between a category C and the
    category of algebras of a monad on C

  - For monads S, T on C: lifting of T to a monad on the category
    of S-algebras

******************************************************************)



Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.Adjunctions.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.Derivative.

Local Open Scope cat.

Ltac rewrite_cbn x := let H := fresh in (set (H := x); cbn in H; rewrite H; clear H).
Ltac rewrite_cbn_inv x := let H := fresh in (set (H := x); cbn in H; rewrite <- H; clear H).


Section Algebras.

Context {C : precategory} (T : Monad C).


(** Definition of an algebra of a monad T *)

Section Algebra_def.

Definition Algebra_data : UU := ∑ X : C, T X --> X.

Coercion Alg_carrier (X : Algebra_data) : C := pr1 X.

Definition Alg_map (X : Algebra_data) : T X --> X := pr2 X.

Definition Algebra_laws (X : Algebra_data) : UU
  := (η T X · Alg_map X = identity X)
   × (μ T X · Alg_map X = #T (Alg_map X) · Alg_map X).

Definition Algebra : UU := ∑ X : Algebra_data, Algebra_laws X.

Coercion Algebra_data_from_Algebra (X : Algebra) : Algebra_data := pr1 X.

Definition Algebra_idlaw (X : Algebra) : η T X · Alg_map X = identity X
  := pr1 (pr2 X).

Definition Algebra_multlaw (X : Algebra) : μ T X · Alg_map X = #T (Alg_map X) · Alg_map X
  := pr2 (pr2 X).

Definition free_Algebra (X : C) : Algebra.
Proof.
  use tpair.
  - exists (T X).
    exact (μ T X).
  - abstract (split;
              [apply Monad_law1 |
               apply pathsinv0;
               apply Monad_law3]).
Defined.

End Algebra_def.


(** Data for the category of algebras of the monad T, following FunctorAlgebras.v *)

Section Algebra_precategory_data.

Definition is_Algebra_mor {X Y : Algebra} (f : X --> Y) : UU
  := Alg_map X · f = #T f · Alg_map Y.

Definition Algebra_mor (X Y : Algebra) : UU
  := ∑ f : X --> Y, is_Algebra_mor f.

Coercion mor_from_Algebra_mor {X Y : Algebra} (f : Algebra_mor X Y)
  : X --> Y := pr1 f.

Definition Algebra_mor_commutes {X Y : Algebra} (f : Algebra_mor X Y)
  : Alg_map X · f = #T f · Alg_map Y := pr2 f.

Definition Algebra_mor_id (X : Algebra) : Algebra_mor X X.
Proof.
  exists (identity X).
  abstract (unfold is_Algebra_mor;
            rewrite functor_id, id_right, id_left;
            apply idpath).
Defined.

Definition Algebra_mor_comp (X Y Z : Algebra) (f : Algebra_mor X Y) (g : Algebra_mor Y Z)
  : Algebra_mor X Z.
Proof.
  exists (f · g).
  abstract (unfold is_Algebra_mor;
            rewrite assoc;
            rewrite Algebra_mor_commutes;
            rewrite <- assoc;
            rewrite Algebra_mor_commutes;
            rewrite functor_comp, assoc;
            apply idpath).
Defined.

Definition precategory_Alg_ob_mor : precategory_ob_mor
  := (Algebra,, Algebra_mor).

Definition precategory_Alg_data : precategory_data
  := (precategory_Alg_ob_mor,, Algebra_mor_id,, Algebra_mor_comp).

End Algebra_precategory_data.

End Algebras.


(** Definition of the category MonadAlg of algebras for T. Requires that C is a category. *)

Section Algebra_category.

Context {C : category} (T : Monad C).

Definition Algebra_mor_eq {X Y : Algebra T} {f g : Algebra_mor T X Y}
  : (f : X --> Y) = g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro h.
  apply homset_property.
Defined.

Lemma is_precategory_precategory_Alg_data : is_precategory (precategory_Alg_data T).
Proof.
  apply mk_is_precategory; intros;
  apply Algebra_mor_eq.
  - apply id_left.
  - apply id_right.
  - apply assoc.
  - apply assoc'.
Qed.

Definition MonadAlg : precategory := ( _,, is_precategory_precategory_Alg_data).

Lemma has_homsets_MonadAlg : has_homsets MonadAlg.
Proof.
  intros X Y.
  apply (isofhleveltotal2 2).
  - apply homset_property.
  - intro f.
    apply isasetaprop.
    apply homset_property.
Qed.

End Algebra_category.


(** Adjunction between MonadAlg T and C, with right adjoint the forgetful functor
   and left adjoint the free algebra functor. *)

Section Algebra_adjunction.

Context {C : category} (T : Monad C).

Definition forget_Alg_data : functor_data (MonadAlg T) C.
Proof.
  exists (fun X => (X : Algebra T)).
  intros X Y f.
  apply f.
Defined.

(* forgetful functor from MonadAlg T to its underlying category *)

Definition forget_Alg : functor (MonadAlg T) C.
Proof.
  exists forget_Alg_data.
  abstract (split; red; intros; apply idpath).
Defined.

Definition free_Alg_data : functor_data C (MonadAlg T).
Proof.
  exists (free_Algebra T).
  intros X Y f.
  exists (#T f).
  apply pathsinv0.
  apply (nat_trans_ax (μ T)).
Defined.

(* free T-algebra functor on C *)

Definition free_Alg : functor C (MonadAlg T).
Proof.
  exists free_Alg_data.
  abstract (split; red; intros;
            apply subtypePairEquality';
            [ apply functor_id |
              apply homset_property |
              apply functor_comp |
              apply homset_property]).
Defined.

Definition free_forgetful_are_adjoints : are_adjoints free_Alg forget_Alg.
Proof.
  use mk_are_adjoints.
  - apply (mk_nat_trans _ _ (η T)).
    intros X Y f.
    apply η.
  - use mk_nat_trans.
    + intro X.
      exact (Alg_map T (X : Algebra T),, Algebra_multlaw T X).
    + intros X Y f.
      apply Algebra_mor_eq; cbn.
      apply pathsinv0.
      apply f.
  - abstract (split; intro X;
              [apply Algebra_mor_eq; cbn;
               apply Monad_law2 |
               apply Algebra_idlaw]).
Defined.

Definition forget_free_is_T : free_Alg ∙ forget_Alg = T.
Proof.
  apply functor_eq.
  - apply homset_property.
  - apply idpath.
Defined.

Definition Alg_adjunction_monad_eq : Monad_from_adjunction free_forgetful_are_adjoints = T.
Proof.
  apply Monad_eq_raw_data.
  - apply homset_property.
  - apply idpath.
Defined.

End Algebra_adjunction.


Section Liftings.

Context {C : category} (S T : Monad C).

(** A lifting of (T, η, μ) is a monad (T', η', μ') on (MonadAlg S) which commutes with the
forgetful functor:
<<
                    T'
  (MonadAlg S) ----------> (MonadAlg S)
       |                        |
       | forget_Alg             | forget_Alg
       |                        |
       V                        V
       C ---------------------> C
                    T
>>
and forget_Alg ∙ η = η' ∙ forget_Alg,
    forget_Alg ∙ μ = μ' ∙ forget_Alg.
 *)

Definition lift_eq (T' : Monad (MonadAlg S)) : UU
  := functor_composite_data (forget_Alg S) T  =
      functor_composite_data T' (forget_Alg S).

Definition lift_η_commutes (T' : Monad (MonadAlg S)) (e : lift_eq T') : UU
  := transportf _ e (pre_whisker (forget_Alg S) (η T)) =
     (post_whisker (η T') (forget_Alg S)).

(* forget_Alg S ∙ (T ∙ T) = (T' ∙ T') ∙ forget_Alg S *)
Definition eq2 (T' : Monad (MonadAlg S))(e : lift_eq T')
  : functor_composite_data (forget_Alg S) (functor_composite_data T T) =
  functor_composite_data (functor_composite_data T' T') (forget_Alg S).
Proof.
  apply (pathscomp0 (maponpaths (fun X => functor_composite_data X T) e)).
  exact (maponpaths (functor_composite_data T') e).
Defined.

Definition lift_μ_commutes (T' : Monad (MonadAlg S)) (e : lift_eq T') : UU
  := transportf (fun X => X ⟹ (T' ∙ forget_Alg S)) (eq2 T' e)
                (transportf _ e (pre_whisker (forget_Alg S) (μ T)))  =
     (post_whisker (μ T') (forget_Alg S)).

Definition lifting : UU
  := ∑ T' : Monad (MonadAlg S),
      (∑ e : lift_eq T', (lift_η_commutes T' e) × (lift_μ_commutes T' e)).


(** A distributive law of S over T induces a lifting of T to S-Algebras *)

Section Lifting_from_dist_law.

Context  {a : T ∙ S ⟹ S ∙ T} (l : monad_dist_laws a).

Definition T_on_SAlg : Algebra S -> Algebra S.
Proof.
  intro X.
  use tpair.
  - exists (T X).
    exact (a X · (# T) (Alg_map S X)).
  - abstract (split; cbn;
              [ rewrite assoc;
                rewrite <- functor_id;
                rewrite <- Algebra_idlaw;
                rewrite functor_comp;
                rewrite <- (monad_dist_law1 l);
                apply idpath |
                rewrite 2 assoc;
                rewrite functor_comp;
                rewrite assoc4;
                rewrite_cbn (nat_trans_ax a _ _ (Alg_map S X));
                rewrite_cbn_inv (monad_dist_law4 l X);
                rewrite <- assoc4;
                rewrite <- assoc;
                rewrite <- functor_comp;
                rewrite_cbn (Algebra_multlaw S X);
                rewrite functor_comp;
                apply assoc]).
Defined.

Definition lift_functor : (MonadAlg S) ⟶ (MonadAlg S).
Proof.
  use mk_functor.
  - exists T_on_SAlg.
    intros X Y f.
    exists ((# T) (mor_from_Algebra_mor S f)).
    abstract (red; cbn;
              rewrite <- assoc;
              rewrite <- functor_comp;
              rewrite Algebra_mor_commutes;
              rewrite functor_comp;
              rewrite 2 assoc;
              apply cancel_postcomposition;
              apply pathsinv0;
              apply a).
  - abstract (split; red; intros; cbn;
              apply subtypePairEquality';
              [ apply functor_id |
                apply homset_property |
                apply functor_comp |
                apply homset_property]).
Defined.

Definition lift_η : functor_identity (MonadAlg S) ⟹ lift_functor.
Proof.
  use mk_nat_trans.
    - intro X. cbn in X.
      exists (η T X).
      abstract (red; cbn;
                rewrite assoc;
                rewrite_cbn (monad_dist_law2 l X);
                apply (nat_trans_ax (η T))).
    - abstract (intros X Y f;
                apply subtypeEquality';
                cbn;
                [ apply (nat_trans_ax (η T)) |
                  apply homset_property]).
Defined.

Definition lift_μ : lift_functor ∙ lift_functor ⟹ lift_functor.
Proof.
  use mk_nat_trans.
    - intro X. cbn in X.
      exists (μ T X).
      abstract (red; cbn;
                rewrite functor_comp;
                rewrite <- assoc4;
                rewrite assoc;
                rewrite_cbn_inv (monad_dist_law3 l X);
                rewrite <- assoc;
                rewrite_cbn (nat_trans_ax (μ T) _ _ (Alg_map S X));
                apply assoc).
     - abstract (intros X Y f;
                 apply subtypeEquality';
                 cbn;
                 [ apply (nat_trans_ax (μ T)) |
                   apply homset_property]).
Defined.

Definition lift_monad : Monad (MonadAlg S).
Proof.
  exists ((lift_functor ,, lift_μ) ,, lift_η).
  abstract (split;
            [ split; intro X;
              apply subtypeEquality';
              [ apply Monad_law1 |
                apply homset_property |
                apply Monad_law2 |
                apply homset_property] |
              intro X; apply subtypeEquality';
              [ apply Monad_law3 |
                apply homset_property] ]).
Defined.

Definition lifting_from_dist_law : lifting.
Proof.
  exists lift_monad.
  exists (idpath _).
  split.
  - apply nat_trans_eq.
    + apply homset_property.
    + intro X.
      apply idpath.
  - apply nat_trans_eq.
    + apply homset_property.
    + intro X.
      apply idpath.
Defined.

End Lifting_from_dist_law.

(** TODO: Construct distributive law from lifting, show distributive laws are equivalent
          to liftings. *)

End Liftings.
