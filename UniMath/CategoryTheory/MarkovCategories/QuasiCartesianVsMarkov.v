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
1. Markov To Quasicartesian
2. Quasicartesian To Markov
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
Require Import UniMath.CategoryTheory.MarkovCategories.Stratified.
Require Import UniMath.CategoryTheory.MarkovCategories.Determinism.
Require Import UniMath.CategoryTheory.MarkovCategories.QuasiCartesian.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

(** * 1. Markov To Quasicartesian *)
Section MarkovToQuasiCartesian.
  Context (C : markov_category).

  Local Open Scope markov.

  Definition markov_to_quasicartesian_data : quasicartesian_data.
  Proof.
    refine ((C :> category) ,, _ ,, _).
    - refine (I_{C} ,, _).
      intros x.
      exact (MarkovCategory.del x).
    - refine ((λ x y, x ⊗ y) ,, _). repeat split.
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
  
  Definition markov_to_quasicartesian : quasicartesian_category.
  Proof.
    refine (markov_to_quasicartesian_data ,, markov_to_quasicartesian_laws).
  Defined.

End MarkovToQuasiCartesian.


(** * 2. Quasicartesian To Markov *)

Section QuasiCartesianToMarkov.
  Context (C : quasicartesian_category).

  Local Open Scope quasicartesian.

  Definition quasicartesian_sig : mon_sig C.
  Proof. 
    repeat split.
    - exact tensor.
    - exact Unit.  
  Defined.

  Definition quasicartesian_sig_cat : mon_sig_cat := ((C :> category) ,, quasicartesian_sig).

  Definition quasicartesian_struct : markov_struct quasicartesian_sig_cat.
  Proof.
    repeat split.
    - intros a b1 b2 g. exact ⟨proj1, proj2 · g⟩.
    - intros b a1 a2 f. exact ⟨proj1 · f, proj2⟩.
    - intros x. exact proj2.
    - intros x. exact ⟨del x, identity x⟩.
    - intros x. exact proj1.
    - intros x. exact ⟨identity x, del x⟩.
    - intros x y z. exact ⟨ proj1 · proj1, ⟨ proj1 · proj2, proj2 ⟩ ⟩.
    - intros x y z. exact ⟨⟨ proj1, proj2 · proj1⟩, proj2 · proj2⟩.
    - intros x y. exact swap.
    - intros x. exact (del x).
    - intros x. exact ⟨ identity x, identity x ⟩.   
  Defined.  

  Definition quasicartesian_struct_cat : markov_struct_cat 
    := (quasicartesian_sig_cat ,, quasicartesian_struct).

  Definition quasicartesian_monoidal_data := markov_monoidal_data quasicartesian_struct_cat.


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
  
  Definition quasicartesian_monoidal_laws : markov_laws quasicartesian_struct_cat.
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
    - (* symmetry involution *) 
      intros x y. cbn. unfold swap. qcart_coherence.
    - (* symmetry natural *)
      intros x y z w f g. 
      unfold tensor_mor, monoidal_cat_tensor_mor, functoronmorphisms1. cbn.
      unfold swap.
      rewrite !pairing_nat_r, pairing_tensor, pairing_swap. reflexivity.
    - (* symmetry hexagon *) 
      intros x y z. cbn. 
      unfold swap, monoidal_cat_tensor_mor, functoronmorphisms1, tensor_mor. cbn.
      qcart_coherence.
    - (* semicartesian *)
      intros x. apply del_unique.
    - (* copy associative *)
      intros x. unfold swap, monoidal_cat_tensor_mor, tensor_mor, functoronmorphisms1; cbn.
      qcart_coherence.
    - (* right unitality *)
      intros x. unfold swap, monoidal_cat_tensor_mor, tensor_mor, functoronmorphisms1; cbn.
      qcart_coherence.
    - (* left unitality *)
      intros x. unfold swap, monoidal_cat_tensor_mor, tensor_mor, functoronmorphisms1; cbn.
      qcart_coherence.
    - (* copy commutativity *)
      intros x. unfold swap, monoidal_cat_tensor_mor, tensor_mor, functoronmorphisms1; cbn.
      unfold swap. qcart_coherence. 
    - (* copy monoidality *)
      intros x y. unfold SymmetricDiagonal.inner_swap. cbn. 
      unfold swap, Stratified.inner_swap, tensor_mor. cbn.
      unfold swap.
      qcart_coherence. 
  Defined.

  Definition quasicartesian_laws_cat : markov_laws_cat 
    := (quasicartesian_struct_cat ,, quasicartesian_monoidal_laws).
  
  Definition quasicartesian_to_markov : markov_category
    := markov_category_from_cat quasicartesian_laws_cat.

End QuasiCartesianToMarkov.

(* TODO ?? replace with [change] *)
Lemma pair_eta {X : UU} (P : X -> UU) (p : ∑ x, P x) : p = (pr1 p ,, pr2 p).
Proof.
  reflexivity.
Qed.

Section QuasiCartesianToMarkovToQuasiCartesian.
  Context (C : quasicartesian_category).

  Local Open Scope quasicartesian.

  Local Lemma markov_pairing_lemma {x y z : C} (f : x --> y) (g : x --> z) : 
    ⟨ identity x, identity x ⟩ · (⟨ proj1 · f, proj2 ⟩ · ⟨ proj1, proj2 · g ⟩) 
    = ⟨ f, g ⟩.
  Proof.
    rewrite assoc.
    rewrite pairing_nat_l, pairing_nat_r.
    rewrite !id_left.
    reflexivity.
  Qed.

  (* TODO can be improved with [total2_paths_f] *)
  Proposition quasicartesian_to_markov_inv_data :
    markov_to_quasicartesian_data (quasicartesian_to_markov C) = C.
  Proof.
    unfold markov_to_quasicartesian_data,
           quasicartesian_to_markov,
           quasicartesian_data_to_cat.
    cbn.
    
    do 3 (rewrite pair_eta; refine (maponpaths _ _)).
    rewrite pair_eta; refine (map_on_two_paths _ _ _).
    
    - do 5 (apply funextsec2; intros).
      assert (aux : pr122 (pr21 C) x x0 x1 x2 x3 = @pairing (pr1 C) x x0 x1 x2 x3). { reflexivity. }
      refine (_ @ !aux).
      
      unfold MarkovCategory.pairing,
             copy, monoidal_cat_tensor_mor, functoronmorphisms1.
      cbn.
      apply markov_pairing_lemma.
    - rewrite pair_eta.
      refine (map_on_two_paths _ _ _).
      all: 
        do 2 (apply funextsec2; intros);
        unfold MarkovCategory.proj1, 
               MarkovCategory.proj2,
               monoidal_cat_tensor_mor,
               MarkovCategory.del,
               functoronmorphisms1;
        cbn;
        qcart_simpl;
        reflexivity. 
  Qed.

  Proposition quasicartesian_roundtrip :
    markov_to_quasicartesian (quasicartesian_to_markov C) = C.
  Proof.
    unfold markov_to_quasicartesian, quasicartesian_to_markov.
    apply subtypePath.
    - exact isaprop_quasicartesian_laws.
    - exact quasicartesian_to_markov_inv_data.
  Defined.

End QuasiCartesianToMarkovToQuasiCartesian.

Section MarkovToQuasiCartesianToMarkov.
  Context (C : markov_category).

  Local Open Scope markov.

  Proposition markov_roundtrip : 
    quasicartesian_to_markov (markov_to_quasicartesian C) = C.
  Proof.
    refine (invmaponpathsweq markov_laws_weq _ _ _).
    
    apply reassoc_eq. unfold total2asstor. cbn.
    
    (* signatures are equal *)
    apply maponpaths.

    (* laws are mere propositions *)
    apply subtypePath. { intros cc. apply isaprop_markov_laws. }

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

End MarkovToQuasiCartesianToMarkov.

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