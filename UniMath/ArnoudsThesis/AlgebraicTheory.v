Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.preorder_categories.
Require Import UniMath.CategoryTheory.categories.HSET.Core.

(* Define a preorder category over the natural numbers *)
Definition nat_po_category : category := po_category (make_po natleh (@istransnatleh ,, isreflnatleh)).

Local Open Scope cat.

Section AlgebraicTheoryData.

  Definition algebraic_theory_data := ∑ (T: nat_po_category ⟶ hset_precategory),
    (∏ {n}, stn n → (T n : hSet)) × (∏ {m n}, (T n : hSet) → (stn n → (T m : hSet)) → (T m : hSet)).

  Definition make_algebraic_theory_data (T: nat_po_category ⟶ hset_precategory) (proj: ∏ {n}, stn n → (T n : hSet)) (comp: ∏ {m n}, (T n : hSet) → (stn n → (T m : hSet)) → (T m : hSet)) : algebraic_theory_data.
  Proof.
    exact (T ,, (proj ,, comp)).
  Defined.

  Variable T : algebraic_theory_data.

  Definition f_T (d : algebraic_theory_data) : (nat_po_category ⟶ hset_precategory) := pr1 d.
  Coercion f_T : algebraic_theory_data >-> functor.

  Local Definition pr : ∏ {n}, stn n → (T n : hSet) := pr1 (pr2 T).
  Local Definition comp: ∏ {m n}, (T n : hSet) → (stn n → (T m : hSet)) → (T m : hSet) := pr2 (pr2 T).

  Local Definition id : (T 1 : hSet) := pr (@firstelement 0).

  (* Define the associativity property of the algebraic theory *)
  Definition comp_is_assoc : Prop := ∏
    (l m n : nat)
    (f_l : (T l : hSet))
    (f_m : stn l → (T m : hSet))
    (f_n : stn m → (T n : hSet)),
      (comp (comp f_l f_m) f_n) = (comp f_l (λ t_l, comp (f_m t_l) f_n)).

  (* Define the unitality property of the algebraic theory *)
  Definition comp_is_unital : Prop := ∏
    (n : nat)
    (f_n : (T n : hSet)),
      (comp f_n (λ t, pr t)) = f_n.

  (* Define the compatibility of the projection function with composition *)
  Definition comp_is_compatible_with_projections : Prop := ∏
    (m n : nat)
    (l : stn m)
    (f_n : stn m → (T n : hSet)),
      (comp (pr l) f_n) = f_n l.

  (* Define naturality of the composition in the first argument *)
  Definition comp_is_natural_l : Prop := ∏
    (s t n : nat_po_category)
    (f: nat_po_category⟦s, t⟧)
    (f_s : (T s : hSet))
    (f_n : stn s → (T n : hSet)),
    unit.
  (* Proof.
    destruct (natgtb s m) eqn:hm.
    - apply f_n.
      use tpair.
      + exact m.
      + simpl.
        rewrite hm.
        apply idpath.
    - apply pr.
      apply firstelement.
  End. *)

  (* Define naturality of the composition in the second argument *)
  Definition comp_is_natural_r := ∏
    (m s t : nat_po_category)
    (f: nat_po_category⟦s, t⟧)
    (f_m : (T m : hSet))
    (f_s : stn m → (T s : hSet)),
      ((comp f_m (λ x, #T f (f_s x))) = (#T f) (comp f_m f_s)).
    
End AlgebraicTheoryData.

Section AlgebraicTheory.

  Definition is_algebraic_theory (T : algebraic_theory_data) :=
      (comp_is_assoc T) ×
      (comp_is_unital T) ×
      (comp_is_compatible_with_projections T) ×
      (comp_is_natural_l T) ×
      (comp_is_natural_r T).

  Definition make_is_algebraic_theory
    {T : algebraic_theory_data}
    (H1 : comp_is_assoc T)
    (H2 : comp_is_unital T)
    (H3 : comp_is_compatible_with_projections T)
    (H4 : comp_is_natural_l T)
    (H5 : comp_is_natural_r T) : is_algebraic_theory T := (H1 ,, H2 ,, H3 ,, H4 ,, H5).

  Lemma ispredicate_is_algebraic_theory : isPredicate is_algebraic_theory.
  Proof.
    intros T.
    repeat apply isapropdirprod;
      repeat (apply impred_isaprop; intros);
      try apply setproperty.
    exact isapropunit.
  Qed.

  Definition algebraic_theory := total2 is_algebraic_theory.

  Definition make_algebraic_theory (T : algebraic_theory_data) (H : is_algebraic_theory T) : algebraic_theory := (T ,, H).

  Definition algebraic_theory_data_from_algebraic_theory : algebraic_theory -> algebraic_theory_data := pr1.
  Coercion algebraic_theory_data_from_algebraic_theory : algebraic_theory >-> algebraic_theory_data.

End AlgebraicTheory.

Section AlgebraicTheoryMorphismData.

  Definition algebraic_theory_morphism_data (T T' : algebraic_theory) := T ⟹ T'.
  Context {T T' : algebraic_theory}.

  Variable F : algebraic_theory_morphism_data T T'.

  Definition preserves_projections : Prop := ∏
    (n : nat_po_category)
    (i : stn n),
      ((F : nat_trans _ _) n (pr T i)) = (pr T' i).

  Definition preserves_composition : Prop := ∏
    (m n : nat_po_category)
    (f_m : (T m : hSet))
    (f_n : stn m → (T n : hSet)),
    ((F : nat_trans _ _) n (comp T f_m f_n)) = (comp T' ((F : nat_trans _ _) m f_m) (λ i, (F : nat_trans _ _) n (f_n i))).

End AlgebraicTheoryMorphismData.

Section AlgebraicTheoryMorphism.

  Definition is_algebraic_theory_morphism {T T' : algebraic_theory} (F : algebraic_theory_morphism_data T T') : Prop := preserves_projections F × preserves_composition F.

  Definition make_is_algebraic_theory_morphism {T T' : algebraic_theory} (F : algebraic_theory_morphism_data T T') (H1 : preserves_projections F) (H2 : preserves_composition F) := (H1 ,, H2).

  Lemma ispredicate_is_algebraic_theory_morphism {T T' : algebraic_theory} : isPredicate (@is_algebraic_theory_morphism T T').
  Proof.
    intros F.
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
      use idpath.
  Defined.

  Definition algebraic_theory_morphism_comp (T1 T2 T3 : algebraic_theory) (F1 : algebraic_theory_morphism T1 T2) (F2 : algebraic_theory_morphism T2 T3) : algebraic_theory_morphism T1 T3.
  Proof.
    destruct F1 as [F1 [F1proj F1comp]].
    destruct F2 as [F2 [F2proj F2comp]].
    use (make_algebraic_theory_morphism (nat_trans_comp _ _ _ F1 F2)).
    use make_is_algebraic_theory_morphism; unfold preserves_projections, preserves_composition; simpl; intros.
    - unfold compose.
      simpl.
      rewrite F1proj, F2proj.
      apply idpath.
    - unfold compose.
      simpl.
      rewrite F1comp, F2comp.
      apply idpath.
  Defined.

End AlgebraicTheoryMorphism.

Section AlgebraicTheoryCategory.

  Definition algebraic_theory_precat : precategory.
  Proof.
    pose (hset_has_homset := (λ x y, isaset_set_fun_space (pr1 x) y) : (has_homsets hset_precategory)).

    use (make_precategory (make_precategory_data
      (algebraic_theory ,,
      algebraic_theory_morphism)
      algebraic_theory_morphism_id
      algebraic_theory_morphism_comp)).

    repeat split;
      intros;
      use (subtypePath ispredicate_is_algebraic_theory_morphism).
    - use (nat_trans_comp_id_left hset_has_homset).
    - use (nat_trans_comp_id_right hset_has_homset).
    - use (nat_trans_comp_assoc hset_has_homset).
    - symmetry.
      use (nat_trans_comp_assoc hset_has_homset).
  Defined.

End AlgebraicTheoryCategory.