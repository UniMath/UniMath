(**
    An alternative definition of coalgebra in type_precat that
    gives a precategory, so that an adjunction can be shown
    in MWithSets
*)

Require Import UniMath.Foundations.Propositions.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Categories.Type.Core.

Local Open Scope cat.

Section Coalgebra_Definition.

Context (F : functor type_precat type_precat).

Definition coalgebra : UU := ∑ X : type_precat, X --> F X.

Definition coalgebra_ob (X : coalgebra) : type_precat := pr1 X.
Local Coercion coalgebra_ob : coalgebra >-> ob.

Definition coalgebra_mor (X : coalgebra) : type_precat ⟦X, F X ⟧ := pr2 X.

(** A homomorphism of F-coalgebras (F A, α : C ⟦A, F A⟧) and (F B, β : C ⟦B, F B⟧)
    is a morphism f : C ⟦A, B⟧ s.t. the below diagram commutes.

  <<
         f
     A -----> B
     |        |
     | α      | β
     |        |
     V        V
    F A ---> F B
        F f
  >>
*)

Definition is_coalgebra_homo {X Y : coalgebra} (f : type_precat ⟦X, Y⟧) (x : coalgebra_ob X) : UU
  := ((coalgebra_mor X) · #F f) x = (f · (coalgebra_mor Y)) x.

Definition coalgebra_homo (X Y : coalgebra) := ∑ f : type_precat ⟦X, Y⟧, ∏ x : coalgebra_ob X, ∥ is_coalgebra_homo f x ∥.

Definition mor_from_coalgebra_homo (X Y : coalgebra) (f : coalgebra_homo X Y)
  : type_precat ⟦X, Y⟧ := pr1 f.
Coercion mor_from_coalgebra_homo : coalgebra_homo >-> precategory_morphisms.

Lemma coalgebra_homo_commutes {X Y : coalgebra} (f : coalgebra_homo X Y) (x : coalgebra_ob X) (P : hProp) :
  (((coalgebra_mor X) · #F f) x = (f · (coalgebra_mor Y)) x -> P) -> P.
Proof.
  intro Hyp.
  apply (factor_through_squash (pr2 P) Hyp).
  exact (pr2 f x).
Qed.

Definition coalgebra_homo_id (X : coalgebra) : coalgebra_homo X X.
Proof.
  exists (identity _).
  intro x.
  unfold is_coalgebra_homo.
  rewrite id_left.
  rewrite functor_id.
  rewrite id_right.
  exact (hinhpr (idpath (coalgebra_mor X x))).
Defined.

Lemma coalgebra_homo_comp (X Y Z : coalgebra) (f : coalgebra_homo X Y)
           (g : coalgebra_homo Y Z) : coalgebra_homo X Z.
Proof.
  exists (f · g).
  intro x.
  unfold is_coalgebra_homo.
  rewrite functor_comp.
  rewrite assoc.
  apply (coalgebra_homo_commutes f x).
  intro Hypf.
  assert (p1 : (coalgebra_mor X · # F f · # F g) x = (# F g) ((coalgebra_mor X · # F f) x)) by apply idpath.
  rewrite p1.
  rewrite Hypf.
  assert (p2 : # F g ((f · coalgebra_mor Y) x) = (f · coalgebra_mor Y · # F g) x) by apply idpath.
  rewrite p2.
  rewrite <- assoc.
  apply (coalgebra_homo_commutes g (pr1 f x)).
  intro Hypg.
  assert (p3 : (f · (coalgebra_mor Y · # F g)) x = (coalgebra_mor Y · # F g) (pr1 f x)) by apply idpath.
  rewrite p3.
  rewrite Hypg.
  assert (p4 : (g · coalgebra_mor Z) (pr1 f x) = (f · (g · coalgebra_mor Z)) x) by apply idpath.
  rewrite p4.
  rewrite assoc.
  exact (hinhpr (idpath _)).
Defined.

Definition CoAlg_precategory_ob_mor : precategory_ob_mor :=
  make_precategory_ob_mor coalgebra coalgebra_homo.

Definition CoAlg_precategory_data: precategory_data :=
  make_precategory_data CoAlg_precategory_ob_mor
                        coalgebra_homo_id
                        coalgebra_homo_comp.

End Coalgebra_Definition.

Lemma CoAlg_is_precategory (F : functor type_precat type_precat)
  : is_precategory (CoAlg_precategory_data F).
Proof.
  split.
  - split.
    + intros.
      use total2_paths_f.
      * apply idpath.
      * apply funextsec.
        intro.
        apply isapropishinh.
    + intros.
      use total2_paths_f.
      * apply idpath.
      * apply funextsec.
        intro.
        apply isapropishinh.
  - split.
    + intros.
      use total2_paths_f.
      * apply idpath.
      * apply funextsec.
        intro.
        apply isapropishinh.
    + intros.
      use total2_paths_f.
      * apply idpath.
      * apply funextsec.
        intro.
        apply isapropishinh.
Qed.

Definition CoAlg_precategory (F : functor type_precat type_precat) : precategory
  := make_precategory (CoAlg_precategory_data F) (CoAlg_is_precategory F).
