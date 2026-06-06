(*********************************************
Quasicartesian versus Markov categories

In this file, we show that quasicartesian categories and Markov categories
are equivalent axiomatizations. 

Showing that every Markov category induces a quasicartesian one follows
from our combined previous results on Markov categories, but involves
a lot of wrangling of coherence maps.

Showing that every quasicartesian category carries a Markov structure is
comparatively very simple. There is a lot of coherence to be checked, 
but these proofs can largely be automated by the [qcart_coherence] tactic. 

Table of Contents
1. Construction: Markov To Quasicartesian
2. Construction: Quasicartesian To Markov
3. Round trips (proof of isomorphism)
4. Construction of equivalence [markov_category = quasicartesian_category]
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Cartesian.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.SymmetricDiagonal.

Require Import UniMath.CategoryTheory.MarkovCategories.MarkovCategory.
Require Import UniMath.CategoryTheory.MarkovCategories.Determinism.

Require UniMath.CategoryTheory.MarkovCategories.AlternativeDefinitions.Stratified.
Require Import UniMath.CategoryTheory.MarkovCategories.AlternativeDefinitions.Quasicartesian.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

(** * 1. Construction: Markov To Quasicartesian *)

Section MarkovToQuasiCartesian.
  Context (C : markov_category).

  Local Open Scope markov.

  Definition markov_to_quasicartesian_data : quasicartesian_data.
  Proof.
    simple refine ((C :> category) ,, _ ,, _).
    - simple refine (I_{C} ,, _).
      intros x.
      exact (MarkovCategory.del x).
    - simple refine ((λ x y, x ⊗ y) ,, _). repeat split.
      * intros x y z f g. exact (⟨f,g⟩).
      * intros x y. exact (MarkovCategory.proj1).
      * intros x y. exact (MarkovCategory.proj2).
  Defined.   
  
  Lemma det_from_deterministic {x y : C} {f : x --> y} : 
    @is_deterministic C x y f -> @det (markov_to_quasicartesian_data) x y f.
  Proof.
    intros df. apply is_deterministic_eq'. exact df.
  Qed.

  Lemma deterministic_from_det {x y : C} {f : x --> y} : 
    @det (markov_to_quasicartesian_data) x y f -> @is_deterministic C x y f.
  Proof.
    intros d. apply make_is_deterministic'. exact d.
  Qed.

  Definition markov_to_quasicartesian_laws : quasicartesian_laws markov_to_quasicartesian_data.
  Proof.
    unfold quasicartesian_laws. repeat split; intros; cbn.
    - apply MarkovCategory.pairing_proj1.
    - apply MarkovCategory.pairing_proj2.
    - apply markov_category_unit_eq.
    - apply det_from_deterministic. apply is_deterministic_proj1.
    - apply det_from_deterministic. apply is_deterministic_proj2.
    - apply det_from_deterministic. apply is_deterministic_del.
    - apply det_from_deterministic. 
      apply is_deterministic_pairing; apply deterministic_from_det; assumption.
    - apply pairing_proj_id.
    - rewrite <- pairing_proj_tensor. apply MarkovCategory.pairing_tensor.
    - rewrite <- pairing_proj_lassociator. apply pairing_lassociator.
    - rewrite <- pairing_proj_braiding. apply pairing_sym_mon_braiding.
  Defined.
  
  Definition markov_to_quasicartesian : quasicartesian_category
    := (markov_to_quasicartesian_data ,, markov_to_quasicartesian_laws).

End MarkovToQuasiCartesian.


(** * 2. Construction: Quasicartesian To Markov *)

Section QuasiCartesianToMarkov.
  Context (Q : quasicartesian_category).

  Local Open Scope quasicartesian.

  Definition quasicartesian_tensor_data : tensor_data Q.
  Proof. 
    use make_bifunctor_data.
    - exact tensor.
    - intros a b1 b2 g. exact ⟨proj1, proj2 · g⟩.
    - intros b a1 a2 f. exact ⟨proj1 · f, proj2⟩.
  Defined.

  Definition quasicartesian_monoidal_data : monoidal_data Q.
  Proof.
    use make_monoidal_data.
    - exact quasicartesian_tensor_data.
    - exact Unit.
    - intros x. exact proj2.
    - intros x. exact ⟨del x, identity x⟩.
    - intros x. exact proj1.
    - intros x. exact ⟨identity x, del x⟩.
    - intros x y z. exact ⟨ proj1 · proj1, ⟨ proj1 · proj2, proj2 ⟩ ⟩.
    - intros x y z. cbn. exact ⟨⟨ proj1, proj2 · proj1⟩, proj2 · proj2⟩.
  Defined.  

  Proposition pentagon : pentagon_identity α_{ quasicartesian_monoidal_data}.
  Proof.
    intros x y z w. cbn. qcart_coherence.
  Qed.

  Proposition left_whisker_natural : associator_nat_leftwhisker α_{ quasicartesian_monoidal_data}.
  Proof.
    intros x y z w f. cbn.
    symmetry. etrans. {
      rewrite proj1_expand.
      reflexivity.
    }
    rewrite pairing_assoc.
    symmetry. etrans. {
      apply maponpaths.
      apply maponpaths_2.
      rewrite <- (id_right proj1).
      reflexivity.
    }
    rewrite pairing_tensor.
    etrans. {
      apply maponpaths.
      apply maponpaths.
      apply maponpaths_2.
      rewrite <- (id_right proj1).
      reflexivity.
    }
    rewrite pairing_tensor, !id_right.
    reflexivity.
  Qed.

  Proposition right_whisker_natural : associator_nat_rightwhisker α_{ quasicartesian_monoidal_data}.
  Proof.
    intros x y z w f. cbn.
    symmetry. etrans. {
      apply maponpaths_2.
      rewrite <- pairing_nat_det; try auto with autodet.
    }
    rewrite pairing_assoc, pairing_nat_l, !assoc.
    reflexivity.
  Qed.

  Proposition left_right_whisker_natural : associator_nat_leftrightwhisker α_{ quasicartesian_monoidal_data}.
  Proof.
    intros x y z z2 w. cbn.
    rewrite <- pairing_nat_det with (f:=proj1); try auto with autodet.
    rewrite pairing_assoc.
    rewrite pairing_nat_r, pairing_nat_l, assoc.
    reflexivity.
  Qed. 
  
  Definition quasicartesian_monoidal_laws : monoidal_laws quasicartesian_monoidal_data.
  Proof.
    repeat split.
    - (* left identity*)
       intros x y. cbn. qcart_coherence.
    - (* right identity *)
      intros x y. cbn. qcart_coherence.
    - (* bifunctor_leftcompax *)
      intros x b1 b2 b3 g1 g2. cbn.
      rewrite pairing_nat_r, assoc. reflexivity.
    - (* bifunctor_rightcompax *)
      intros x a1 a2 a3 f1 f2. cbn.
      rewrite pairing_nat_l, assoc. reflexivity.
    - (* functoronmorphisms_are_equal *)
      intros a1 a2 b1 b2 f g.  
      unfold functoronmorphisms1, functoronmorphisms2; cbn.
      rewrite pairing_nat_l, pairing_nat_r. reflexivity.
    - (* Left unitor natural *) 
      intros x y f. cbn. qcart_coherence.
    - (* Left unitor iso 1 *)    
      cbn. qcart_coherence.
    - (* Left unitor iso 2 *) 
      cbn. qcart_coherence.
    - (* Right unitor natural *)
      intros x y f. cbn. qcart_coherence.
    - (* Right unitor iso 1 *) 
      cbn. qcart_coherence.
    - (* Right unitor iso 2 *)
      cbn. qcart_coherence.
    - (* Left whiskering natural *)   
      apply left_whisker_natural.
    - (* Right whiskering natural *)
      apply right_whisker_natural.
    - (* Left right whisker *)
      apply left_right_whisker_natural.
    - (* Associator iso 1 *)
      cbn. qcart_coherence.
    - (* Associator iso 2 *)  
      cbn. qcart_coherence.
    - (* Triangle identity *)   
      intros x y. cbn. qcart_coherence.
    - (* Pentagon identity *) 
      apply pentagon.
  Defined.

  Definition quasicartesian_monoidal : monoidal Q
    := (quasicartesian_monoidal_data ,, quasicartesian_monoidal_laws).

  Definition quasicartesian_monoidal_cat : monoidal_cat
    := ((Q :> category) ,, quasicartesian_monoidal).

  (* Symmetry *)

  Definition quasicartesian_swap_laws : sym_mon_cat_laws_tensored
       quasicartesian_monoidal_cat (λ x y : Q, swap).
  Proof.
    repeat split.
    - (* involution *)
      intros x y. cbn. unfold swap. qcart_coherence.
    - (* naturality *)
      intros x y z w f g. 
      unfold swap, monoidal_cat_tensor_mor, functoronmorphisms1. cbn.
      rewrite !pairing_nat_r, pairing_tensor, pairing_swap. reflexivity.
    - (* hexagon *)
      intros x y z. cbn. 
      unfold swap, monoidal_cat_tensor_mor, functoronmorphisms1. cbn.
      qcart_coherence.
  Defined.      

  Definition quasicartesian_symmetric : symmetric quasicartesian_monoidal.
  Proof.
    use (make_symmetric quasicartesian_monoidal_cat _ _).
    - exact (@swap Q).
    - exact quasicartesian_swap_laws.
  Defined.
  
  Definition quasicartesian_sym_monoidal_cat : sym_monoidal_cat
    := (quasicartesian_monoidal_cat ,, quasicartesian_symmetric).

  (* Markov category *)

  Definition quasicartesian_to_markov_data : markov_category_data.
  Proof.
    simple refine (quasicartesian_sym_monoidal_cat ,, _ ,, _).
    - intros x. simple refine (del x ,, _).
      intros f. apply del_unique.
    - intros x. exact ⟨ identity x , identity x ⟩.
  Defined.

  Definition quasicartesian_to_markov_laws : markov_category_laws quasicartesian_to_markov_data.
  Proof.
    repeat split; cbn; unfold swap, monoidal_cat_tensor_mor, functoronmorphisms1; cbn.
    - intros x. qcart_coherence.
    - intros x. qcart_coherence.
    - intros x. qcart_coherence.
    - intros x. qcart_coherence.
    - intros x y. unfold SymmetricDiagonal.inner_swap. cbn. unfold swap. 
      qcart_coherence. 
  Defined.
  
  Definition quasicartesian_to_markov : markov_category
    := (quasicartesian_to_markov_data ,, quasicartesian_to_markov_laws).

End QuasiCartesianToMarkov.

(** * 3. Round trips (proof of isomorphism) *)

Section Roundtrips.

  Local Open Scope quasicartesian.

  Proposition quasicartesian_roundtrip (Q : quasicartesian_category) :
    markov_to_quasicartesian (quasicartesian_to_markov Q) = Q.
  Proof.
    apply subtypePath. { exact isaprop_quasicartesian_laws. } 
    
    unfold markov_to_quasicartesian_data,
        quasicartesian_to_markov,
        quasicartesian_data_to_cat; cbn.

    apply total2asstor_path. unfold total2asstor. cbn.
    do 2 apply maponpaths.
    apply total2asstor_path. unfold total2asstor. cbn.
    do 2 apply maponpaths.

    use total2_paths_f. { apply idpath. }
    rewrite idpath_transportf. cbn.

    (repeat apply dirprod_paths)
    ; (repeat (apply funextsec2; intros))
    ; cbn.
    - assert (aux : pr122 (pr21 Q) x x0 x1 x2 x3 = @pairing (pr1 Q) x x0 x1 x2 x3). { reflexivity. }
      simple refine (_ @ !aux).
      unfold MarkovCategory.pairing,
             copy, 
             monoidal_cat_tensor_mor,
             functoronmorphisms1.
      apply pairing_lemma.
    - unfold MarkovCategory.proj1, 
            MarkovCategory.proj2,
            monoidal_cat_tensor_mor,
            MarkovCategory.del,
            functoronmorphisms1.
      cbn.
      qcart_simpl.
      reflexivity.
    - unfold MarkovCategory.proj1, 
            MarkovCategory.proj2,
            monoidal_cat_tensor_mor,
            MarkovCategory.del,
            functoronmorphisms1.
      cbn.
      qcart_simpl.
      reflexivity.
  Qed.

  Local Open Scope markov.

  Proposition markov_roundtrip (C : markov_category) : 
    quasicartesian_to_markov (markov_to_quasicartesian C) = C.
  Proof.
    simple refine (invmaponpathsweq Stratified.markov_laws_weq _ _ _).
    
    apply total2asstor_path. unfold total2asstor. cbn.
    
    (* signatures are equal on the nose *)
    apply maponpaths.

    (* laws are mere propositions *)
    apply subtypePath. { intros cc. apply Stratified.isaprop_markov_laws. }

    (* It remains to show that the structures are equal *)
    (repeat apply dirprod_paths)
    ; (repeat (apply funextsec2; intros))
    ; cbn.
    - rewrite <- pairing_proj_whisker_l. reflexivity.
    - rewrite <- pairing_proj_whisker_r. reflexivity.
    - rewrite <- pairing_proj_lunitor. reflexivity.
    - rewrite <- pairing_proj_linvunitor. reflexivity.
    - rewrite <- pairing_proj_runitor. reflexivity.
    - rewrite <- pairing_proj_rinvunitor. reflexivity.
    - rewrite <- pairing_proj_lassociator. reflexivity.
    - rewrite <- pairing_proj_rassociator. reflexivity.
    - rewrite <- pairing_proj_braiding. reflexivity.
    - reflexivity.
    - rewrite <- MarkovCategory.pairing_id. reflexivity.
  Defined.

End Roundtrips.

(** * 4. Construction of equivalence [markov_category = quasicartesian_category] *)

Theorem markov_quasicartesian_weq :
  markov_category ≃ quasicartesian_category.
Proof.
  use weq_iso.
  - exact markov_to_quasicartesian.
  - exact quasicartesian_to_markov.
  - exact markov_roundtrip.
  - exact quasicartesian_roundtrip.
Defined.

Theorem markov_quasicartesian_eq :
  markov_category = quasicartesian_category.
Proof.
  exact (weqtopaths markov_quasicartesian_weq).
Defined.