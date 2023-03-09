Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

Require Import UniMath.ArnoudsThesis.FiniteSetSkeleton.
Require Import UniMath.ArnoudsThesis.AlgebraicBase.

Local Open Scope cat.
Local Open Scope algebraic_theory.

Section AlgebraicTheory.

  Definition algebraic_theory_data := ∑ (T : algebraic_base),
    (T 1) × (∏ {m n : nat}, (stn m → stn n) → T m → T n).

  Definition make_algebraic_theory_data (T : algebraic_base)
    (e : T 1) (Tmor : ∏ {m n : nat}, (stn m → stn n) → T m → T n) : algebraic_theory_data.
  Proof.
    exact (T ,, e ,, Tmor).
  Defined.

  Definition algebraic_base_from_algebraic_theory_data (d : algebraic_theory_data) : algebraic_base := pr1 d.
  Coercion algebraic_base_from_algebraic_theory_data : algebraic_theory_data >-> algebraic_base.

  Definition e {T : algebraic_theory_data} : T 1 := pr12 T.

  Definition Tmor {T : algebraic_theory_data} {m n} : (stn m → stn n) → T m → T n := pr22 T m n.

  Definition pr {T : algebraic_theory_data} {n : nat} (i : stn n) : T n := Tmor (λ (x : stn 1), i) e.

  (* Define the associativity property of the algebraic theory *)
  Definition comp_is_assoc (T : algebraic_theory_data) : Prop := ∏
    (l m n : nat)
    (f_l : T l)
    (f_m : stn l → T m)
    (f_n : stn m → T n),
      (f_l • f_m) • f_n = f_l • (λ t_l, (f_m t_l) • f_n).

  (* Define the unitality property of the algebraic theory *)
  Definition comp_is_unital (T : algebraic_theory_data) : Prop := ∏
    (n : nat)
    (f : T n),
      e • (λ _, f) = f.

  (* Define the compatibility of the projection function with composition *)
  Definition comp_identity_projections (T : algebraic_theory_data) : Prop := ∏
    (n : nat)
    (f : T n),
      f • (λ i, pr i) = f.

  (* Define naturality of the composition in the first argument *)
  Definition comp_is_natural_l (T : algebraic_theory_data) : Prop := ∏
    (m m' n : finite_set_skeleton_category)
    (a : finite_set_skeleton_category⟦m, m'⟧)
    (f : T m)
    (g : stn m' → T n),
    (Tmor a f) • g = f • (λ i, g (a i)).

  Definition is_algebraic_theory (T : algebraic_theory_data) :=
      (is_functor (make_functor_data (T : finite_set_skeleton_category → HSET) (@Tmor T))) ×
      (comp_is_assoc T) ×
      (comp_is_unital T) ×
      (comp_identity_projections T) ×
      (comp_is_natural_l T).

  Definition make_is_algebraic_theory
    {T : algebraic_theory_data}
    (H1 : (is_functor (make_functor_data (T : finite_set_skeleton_category → HSET) (@Tmor T))))
    (H2 : comp_is_assoc T)
    (H3 : comp_is_unital T)
    (H4 : comp_identity_projections T)
    (H5 : comp_is_natural_l T) : is_algebraic_theory T := (H1 ,, H2 ,, H3 ,, H4 ,, H5).

  Lemma isaprop_is_algebraic_theory (T : algebraic_theory_data) : isaprop (is_algebraic_theory T).
  Proof.
    apply isapropdirprod.
    - apply isaprop_is_functor.
      apply SET.
    - repeat apply isapropdirprod;
        repeat (apply impred_isaprop; intros);
        try apply isapropisfunctor;
        try apply setproperty.
  Qed.

  Definition algebraic_theory := total2 is_algebraic_theory.

  Definition make_algebraic_theory (T : algebraic_theory_data) (H : is_algebraic_theory T) : algebraic_theory := (T ,, H).

  Definition algebraic_theory_data_from_algebraic_theory : algebraic_theory -> algebraic_theory_data := pr1.
  Coercion algebraic_theory_data_from_algebraic_theory : algebraic_theory >-> algebraic_theory_data.

  Lemma algebraic_theory_eq
    (X Y : algebraic_theory)
    (H1 : pr11 X = pr11 Y)
    (H2 : transportf _ H1 (pr121 X) = (pr121 Y))
    : X = Y.
  Proof.
    destruct X as [[Xbase Xpr] HX].
    destruct Y as [[Ybase Ypr] HY].
    use (subtypePairEquality' _ (isaprop_is_abstract_clone _)).
    use total2_paths2_f; repeat assumption.
  Qed.

  (* Lemma functor_uses_projections (T : algebraic_theory) (m n : finite_set_skeleton_category) (a : finite_set_skeleton_category⟦m, n⟧) (f : T m) : Tmor a f = f • (λ i, pr (a i)).
  Proof.
    rewrite <- (pr12 (pr222 T) n (Tmor a f)).
    apply T.
  Qed.

  Lemma comp_project_component (T : algebraic_theory) (m n : nat) (i : stn m) (f : (stn m → T n)) : (pr i) • f = f i.
  Proof.
    unfold pr.
    rewrite (pr22 (pr222 T)).
    apply T.
  Qed.

  (* The composition is natural in the second argument *)
  Lemma comp_is_natural_r (T : algebraic_theory)
    (m n n' : finite_set_skeleton_category)
    (a: finite_set_skeleton_category⟦n, n'⟧)
    (f : T m)
    (g : stn m → T n) :
      f • (λ i, Tmor a (g i)) = Tmor a (f • g).
  Proof.
    rewrite functor_uses_projections.
    rewrite (pr122 T).
    apply maponpaths.
    apply funextsec2.
    intros i.
    rewrite functor_uses_projections.
    apply idpath.
  Qed. *)

End AlgebraicTheory.

(* Section AlgebraicTheoryMorphismData.

  Definition algebraic_theory_morphism_data (T T' : algebraic_theory) := T ⟹ T'.
  Context {T T' : algebraic_theory}.

  Variable F : algebraic_theory_morphism_data T T'.

  Definition preserves_projections : Prop := ∏
    (n : finite_set_skeleton_category)
    (i : stn n),
      ((F : nat_trans _ _) n (pr i)) = (pr i).

  Definition preserves_composition : Prop := ∏
    (m n : finite_set_skeleton_category)
    (f_m : T m)
    (f_n : stn m → T n),
    ((F : nat_trans _ _) n (comp f_m f_n)) = (comp ((F : nat_trans _ _) m f_m) (λ i, (F : nat_trans _ _) n (f_n i))).

End AlgebraicTheoryMorphismData.

Section AlgebraicTheoryMorphism.

  Definition is_algebraic_theory_morphism {T T' : algebraic_theory} (F : algebraic_theory_morphism_data T T') : Prop := preserves_projections F × preserves_composition F.

  Definition make_is_algebraic_theory_morphism {T T' : algebraic_theory} (F : algebraic_theory_morphism_data T T') (H1 : preserves_projections F) (H2 : preserves_composition F) := (H1 ,, H2).

  Lemma ispredicate_is_algebraic_theory_morphism {T T' : algebraic_theory} : isPredicate (@is_algebraic_theory_morphism T T').
  Proof.
    intros ?.
    repeat apply isapropdirprod;
      repeat (apply impred_isaprop; intros);
      apply setproperty.
  Qed.

  Definition algebraic_theory_morphism (T T' : algebraic_theory) : UU := total2 (@is_algebraic_theory_morphism T T').

  Definition make_algebraic_theory_morphism {T T' : algebraic_theory} (F : algebraic_theory_morphism_data T T') (H : is_algebraic_theory_morphism F) : algebraic_theory_morphism T T' := (F ,, H).

  Definition algebraic_theory_morphism_id (T : algebraic_theory) : algebraic_theory_morphism T T.
  Proof.
    apply (make_algebraic_theory_morphism (nat_trans_id T)).
    apply make_is_algebraic_theory_morphism;
      unfold preserves_projections, preserves_composition;
      intros;
      apply idpath.
  Defined.

  Definition algebraic_theory_morphism_comp (T1 T2 T3 : algebraic_theory) (F1 : algebraic_theory_morphism T1 T2) (F2 : algebraic_theory_morphism T2 T3) : algebraic_theory_morphism T1 T3.
  Proof.
    destruct F1 as [F1 [F1proj F1comp]].
    destruct F2 as [F2 [F2proj F2comp]].
    apply (make_algebraic_theory_morphism (nat_trans_comp _ _ _ F1 F2)).
    apply make_is_algebraic_theory_morphism;
      unfold preserves_projections, preserves_composition;
      simpl;
      unfold compose;
      simpl;
      intros.
    - rewrite F1proj.
      apply F2proj.
    - rewrite F1comp.
      apply F2comp.
  Defined.

End AlgebraicTheoryMorphism.

Section AlgebraicTheoryCategory.

  Definition algebraic_theory_precat : precategory.
  Proof.
    apply (make_precategory (make_precategory_data
      (algebraic_theory ,,
      algebraic_theory_morphism)
      algebraic_theory_morphism_id
      algebraic_theory_morphism_comp)).

    repeat split;
      intros;
      apply (subtypePath ispredicate_is_algebraic_theory_morphism).
    - apply (nat_trans_comp_id_left has_homsets_HSET).
    - apply (nat_trans_comp_id_right has_homsets_HSET).
    - apply (nat_trans_comp_assoc has_homsets_HSET).
    - symmetry.
      apply (nat_trans_comp_assoc has_homsets_HSET).
  Defined.

  Definition algebraic_theory_category : category.
  Proof.
    apply (make_category algebraic_theory_precat).
    intros ? ?.
    apply isaset_total2.
    - apply (isaset_nat_trans has_homsets_HSET).
    - intros ?.
      exact (isasetaprop (ispredicate_is_algebraic_theory_morphism _)).
  Defined.

  (* Definition algebraic_theory_univalent_category : univalent_category.
  Proof.
    use tpair.
    - exact algebraic_theory_category.
    - simpl.
      intros a b.
      simpl in a, b.
      unfold algebraic_theory in a, b.
      apply isweqinclandsurj.
      + intros f x x'.
        simpl.
  Defined. *)

End AlgebraicTheoryCategory. *)