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

  Definition quasicartesian_tensor_data : tensor_data C.
  Proof. 
    use make_bifunctor_data.
    - exact tensor.
    - intros a b1 b2 g. exact ⟨proj1, proj2 · g⟩.
    - intros b a1 a2 f. exact ⟨proj1 · f, proj2⟩.
  Defined.

  Definition quasicartesian_monoidal_data : monoidal_data C.
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

  Definition quasicartesian_monoidal : monoidal C.
  Proof.
    exact (quasicartesian_monoidal_data ,, quasicartesian_monoidal_laws).
  Defined.

  Definition quasicartesian_monoidal_cat : monoidal_cat.
  Proof.
    refine ((C :> category) ,, _).
    apply quasicartesian_monoidal.
  Defined.

  (* Symmetry *)

  Definition quasicartesian_swap_laws : sym_mon_cat_laws_tensored
       quasicartesian_monoidal_cat (λ x y : C, swap).
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
    - exact (@swap C).
    - exact quasicartesian_swap_laws.
  Defined.
  
  Definition quasicartesian_sym_monoidal_cat : sym_monoidal_cat.
  Proof.
    exact (quasicartesian_monoidal_cat ,, quasicartesian_symmetric).
  Defined.

  (* Markov category *)

  Definition quasicartesian_to_markov_data : markov_category_data.
  Proof.
    refine (quasicartesian_sym_monoidal_cat ,, _ ,, _).
    - intros x. refine (del x ,, _).
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
  
  Definition quasicartesian_to_markov : markov_category.
  Proof.
    exact (quasicartesian_to_markov_data ,, quasicartesian_to_markov_laws).
  Defined.

End QuasiCartesianToMarkov.

(* TODO ?? replace with [change] *)
Lemma pair_eta {X : UU} (P : X -> UU) (p : ∑ x, P x) : p = (pr1 p ,, pr2 p).
Proof.
  reflexivity.
Qed.

Section QuasiCartesianToMarkovToQuasiCartesian.
  Context {C : quasicartesian_category}.

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

  Proposition quasicartesian_to_markov_inv :
    markov_to_quasicartesian (quasicartesian_to_markov C) = C.
  Proof.
    unfold markov_to_quasicartesian, quasicartesian_to_markov.
    apply subtypePath.
    - exact isaprop_quasicartesian_laws.
    - exact quasicartesian_to_markov_inv_data.
  Qed.

End QuasiCartesianToMarkovToQuasiCartesian.

Section Practice.

Definition vertical
  {A : UU}
  {B : A -> UU}
  {a : A}
  {b b' : B a}
  (v : b = b') : (a ,, b) = (a ,, b').
Proof.
  apply maponpaths.
  exact v.
Defined.

(* TODO tiny aside *)
Lemma vertical'
  {A : UU}
  {B : A -> UU}
  {a : A}
  {b b' : B a}
  (v : b = b') : (a ,, b) = (a ,, b').
Proof.
  refine (@total2_paths_f _ _ (a ,, b) (a ,, b') (idpath a) _).
  etrans. { apply idpath_transportf. }
  exact v.
Defined.

Lemma vertical_eq
  {A : UU}
  {B : A -> UU}
  {a : A}
  {b b' : B a}
  (v : b = b') : vertical v = vertical' v.
Proof.
  induction v.
  unfold vertical, vertical'.
  rewrite maponpaths_idpath.
  rewrite pathscomp0rid.
  unfold total2_paths_f, idpath_transportf.
  apply idpath.
Defined.

(* TODO does this lemma exist? *)
Lemma total2_paths_vertical
  {A : UU}
  {B : A -> UU} 
  {C : (∑ a : A, B a) -> UU}
  {a a' : A}
  {b b' : B a}
  {c : C (a ,, b)}
  (v : b = b') : transportf C (vertical v) c = transportf (λ bb, C (a ,, bb)) v c.
Proof.
  induction v.
  rewrite idpath_transportf.
  unfold vertical.
  rewrite maponpaths_idpath.
  rewrite idpath_transportf.
  apply idpath.
Defined.

Lemma total2_paths_vertical'
  {A : UU}
  {B : A -> UU} 
  {C : (∑ a : A, B a) -> UU}
  {a a' : A}
  {b b' : B a}
  {c : C (a ,, b)}
  (v : b = b') : transportf C (maponpaths (tpair _ a) v) c = transportf (λ bb, C (a ,, bb)) v c.
Proof.
  induction v.
  rewrite idpath_transportf.
  rewrite maponpaths_idpath.
  rewrite idpath_transportf.
  apply idpath.
Defined.

End Practice.

Section Dependency.
  Context {A : UU} {B : A -> UU} {C0 : A -> UU}.

  Definition S := ∑ a : A, B a.
  Definition C : S -> UU := λ s, C0 (pr1 s).

  Context (a : A) (b b' : B a).

  Context (v : b = b').

  Let e : (a ,, b) = (a ,, b') := vertical' v.

  Context (c : C (a ,, b)).

  Proposition dep1 : ((a ,, b) ,, c) = ((a ,, b') ,, c).
  Proof.
    use total2_paths_f. { exact e. }
    etrans. {
      unfold e, vertical'.
      apply transportf_total2_paths_f. 
    }
    rewrite idpath_transportf.
    apply idpath.
  Qed.

  Definition order :
    (∑ s : S, C s) -> ∑ a : A, (B a) × (C0 a).
  Proof.
    intros [[aa bb] cc].
    refine (aa ,, (bb ,, cc)).
  Defined.

  Definition restore :
    (∑ a : A, (B a) × (C0 a)) -> (∑ s : S, C s).
  Proof.
    intros [aa [bb cc]].
    refine ((aa ,, bb),, cc).
  Defined.

  Proposition order_equiv :
     (∑ s : S, C s) ≃ (∑ a : A, (B a) × (C0 a)).
  Proof.
    
    use make_weq. { exact order. }
    use isweq_iso.
    - exact restore.
    - intros [[aa bb] cc]. unfold restore, order. cbn. reflexivity.
    - intros [aa [bb cc]]. unfold order, restore. cbn. reflexivity.
  Defined.     

  Proposition dep2 : ((a ,, b) ,, c) = ((a ,, b') ,, c).
  Proof.
    refine (invmaponpathsweq order_equiv _ _ _). cbn; unfold order.
    rewrite v.
    apply idpath.
  Qed.

End Dependency.


Definition descend {A : UU} {B : A -> UU} (C : (∑ a : A, B a) -> UU) : UU
  := A -> UU.
  
Definition descend_sigma
  {A : UU} {B : A -> UU} {D : UU}
  (C : ∏ d : D, (∑ a : A, B a) -> UU)
  (c0 : ∏ d : D, descend (λ z, C d z))
  : descend (λ z, ∑ d : D, C d z).
Proof.
  refine (λ a, ∑ d : D, c0 d a).
Defined.

Definition descend_prod 
    {A : UU} {B : A -> UU}
    {C1 C2 : (∑ a : A, B a) -> UU}
    (d1 : descend C1) (d2 : descend C2)
  : descend (λ z, (C1 z) × (C2 z)).
Proof.
  exact (λ a, (d1 a) × (d2 a)).
Defined. 

Definition descend_pi
  {A : UU} {B : A -> UU} {D : UU}
  (C : ∏ d : D, (∑ a : A, B a) -> UU)
  (c0 : ∏ d : D, descend (λ z, C d z))
  : descend (λ z, ∏ d : D, C d z).
Proof.
  refine (λ a, ∏ d : D, c0 d a).
Defined.

  Lemma transportf_subtypePath'
    {A : UU} 
    {P : A -> UU}
    {Q : (∑ a : A, P a) -> UU}
    {pred : isPredicate P}
    {a1 a2 : A}
    {p1 : P a1}
    {p2 : P a2}
    {e1 : a1 = a2}
    {q : Q (a1 ,, p1)}
    {e2 : transportf P e1 p1 = p2}
    : UU.
  Proof.
    Check @subtypePath.
    refine(transportf Q (@subtypePath _ _ pred (a1 ,, p1) (a2 ,, p2) e1) q = _).
  Admitted.

Section MarkovToQuasiCartesianToMarkov.
  Context {C : markov_category}.

  Local Open Scope markov.

  Let Q := markov_to_quasicartesian C.

  Definition quasicartesian_tensor_data_eq' :
    quasicartesian_tensor_data Q = C.
  Proof.
    unfold quasicartesian_tensor_data.
    use total2_paths_f. { apply idpath. }
    (* TODO make subproofs abstract *)
    rewrite idpath_transportf. cbn.
    use dirprod_paths.
    - do 4 (apply funextsec2; intros). cbn.
      etrans. {
        rewrite <- pairing_proj_whisker_l. reflexivity.
      }
      reflexivity.
    - do 4 (apply funextsec2; intros). cbn.
      etrans. {
        rewrite <- pairing_proj_whisker_r. reflexivity.
      }
      reflexivity.
  Defined.

  Definition quasicartesian_tensor_data_eq :
    quasicartesian_tensor_data Q = C.
  Proof.
    unfold quasicartesian_tensor_data.
    use total2_paths_f. { apply idpath. }
    abstract (
      rewrite idpath_transportf; cbn;
      use dirprod_paths;
      (do 4 (apply funextsec2; intros)); cbn;
      (etrans; [   rewrite <- pairing_proj_whisker_l
                || rewrite <- pairing_proj_whisker_r ; reflexivity | reflexivity])
    ).
  Defined.

  Definition famoflife := 
    (λ t : Q → Q → Q,
    ∑ I : Q,
    (∏ x0 : Q, Q ⟦ t I x0, x0 ⟧)
    × (∏ x0 : Q, Q ⟦ x0, t I x0 ⟧)
    × (∏ x0 : Q, Q ⟦ t x0 I, x0 ⟧)
    × (∏ x0 : Q, Q ⟦ x0, t x0 I ⟧)
    × (∏ x0 y z : Q, Q ⟦ t (t x0 y) z, t x0 (t y z) ⟧)
    × (∏ x0 y z : Q, Q ⟦ t x0 (t y z), t (t x0 y) z ⟧)).


  (* Note:
     This proof is a bit nasty because while formally [monoidal_data] depends on
     [tensor_data], it really only depends on the first field, i.e. the tensor-on-objects.
     We need to use [transportf_total2_paths_f] to kick out the spurious dependence, but that
     requires unfolding everything to really show that there is no dependence.
  *)
  

  Definition fam := (λ x : tensor_data Q,
    ∑ I : Q,
    leftunitor_data x I
    × leftunitorinv_data x I
    × rightunitor_data x I
    × rightunitorinv_data x I × associator_data x
    × associatorinv_data x).


  (* Unification Hack:
     - If [C] is definitionally equal to a ∑-type [∑ a, B a], then
       [sigma_fiber (idpath C)] is definitionally equal to [B].
  *)
  Definition sigma_base {A : UU} {B : A -> UU} {C : UU} (p : C = ∑ a : A, B a) : UU := A.
  Definition sigma_fiber {A : UU} {B : A -> UU} {C : UU} (p : C = ∑ a : A, B a) : A -> UU := B.


  Goal ∏ z : sigma_base (idpath (monoidal_data C)), 
    sigma_fiber (idpath (monoidal_data C)) z = famoflife (pr1 z).
  Proof.
    reflexivity.
  Qed.

  Definition monoidal_data_descends : 
    descend (sigma_fiber (idpath (monoidal_data C))).
  Proof.
    apply descend_sigma. intros d.
    repeat apply descend_prod.
    - apply descend_pi. intros. unfold bifunctor_on_objects.  
  Admitted.

  Definition mk_descend {A : UU} {B : A -> UU} (C : (∑ a : A, B a) -> UU)
    (C0 : A -> UU)
    : descend C := C0.

  (* transportf (λ x : monoidal (pr1 C), braiding_data x) *)
  Definition braiding_data_descends :
    descend (λ x : monoidal (pr1 C), braiding_data x).
  Proof.
    unfold monoidal.
    unfold braiding_data.
    apply descend_pi. intros.
    apply descend_pi. intros.
    intros a.
    refine (C ⟦ bifunctor_on_objects a d d0, bifunctor_on_objects a d0 d ⟧).
  Defined.

  Definition braiding_data_descends' :
    descend braiding_data_descends.
  Proof.
    unfold braiding_data_descends.
    repeat (apply descend_prod || (apply descend_pi || apply descend_sigma); intros).
    intros a.
    exact (C ⟦ bifunctor_on_objects a d d0, bifunctor_on_objects a d0 d ⟧).
  Defined.

  Definition braiding_data_descends'' :
    descend braiding_data_descends'.
  Proof.
    unfold braiding_data_descends.
    repeat (apply descend_prod || (apply descend_pi || apply descend_sigma); intros).
    intros a.
    exact (C ⟦ a d d0, a d0 d ⟧).
  Defined.

  Goal ∏ z : monoidal C, braiding_data z = braiding_data_descends (pr1 z).
  Proof.
    reflexivity.
  Qed.

  Goal ∏ z, braiding_data_descends z = braiding_data_descends' (pr1 z).
  Proof.
    reflexivity.
  Qed.

  Definition monoidal_data_irrelevance {x y1 y2 q c}
    : transportf (sigma_fiber (idpath (monoidal_data C))) (@total2_paths_f _ _ (x ,, y1) (x ,, y2) (idpath x) q) c = c.
  Proof.
    cbn in *. induction q. apply idpath.
  Defined.

  Definition quasicartesian_monoidal_data_eq :
    quasicartesian_monoidal_data Q = C.
  Proof.
    Print monoidal_data.
    use total2_paths_f. { exact quasicartesian_tensor_data_eq. }

    Search "total2_paths".

    etrans. {
      Check transportf_total2_paths_f.
      fold fam.

(*       
      unfold tensor_data,
             bifunctor_data,
             leftunitor_data,
             leftunitorinv_data,
             rightunitor_data,
             rightunitorinv_data,
             associator_data,
             associatorinv_data,
             bifunctor_on_objects. *)
(* 
      evar (C0 : (Q -> Q -> Q) -> Type). *)
      change fam with (λ z : tensor_data Q, famoflife (pr1 z)).
        
      refine (transportf_total2_paths_f _ _ _ _).
    }

    (* etrans. { refine monoidal_data_irrelevance. }  *)

    unfold make_monoidal_data. cbn.
    use total2_paths_f. { apply idpath. }
    rewrite idpath_transportf. cbn.

    do 5 (try apply dirprod_paths); cbn;
    do 3 (try apply funextsec2; intros);
    symmetry.
    - apply pairing_proj_lunitor.
    - apply pairing_proj_linvunitor.
    - apply pairing_proj_runitor.
    - apply pairing_proj_rinvunitor.
    - apply pairing_proj_lassociator.
    - apply pairing_proj_rassociator.
  Defined.

  Definition quasicartesian_monoidal_eq :
    quasicartesian_monoidal Q = C.
  Proof.
    unfold quasicartesian_monoidal.
    use subtypePath. 
    - unfold isPredicate. intros. apply isaprop_monoidal_laws.
    - exact quasicartesian_monoidal_data_eq.
  Defined.

  Definition quasicartesian_monoidal_cat_eq :
    quasicartesian_monoidal_cat Q = C.
  Proof.
    unfold quasicartesian_monoidal_cat.
    change C with (pr1 C ,, pr2 C).
    use maponpaths.
    exact quasicartesian_monoidal_eq.
  Defined.

  (* Symmetry *)

  Definition quasicartesian_sym_monoidal_eq :
    quasicartesian_sym_monoidal_cat Q = C.
  Proof.
    use total2_paths_f. { apply quasicartesian_monoidal_cat_eq. }
    unfold quasicartesian_monoidal_cat_eq.
    unfold monoidal_cat.
    etrans. {
      refine (total2_paths_vertical' quasicartesian_monoidal_eq). exact C.
    }
    unfold quasicartesian_monoidal_eq.
    cbn.
    apply subtypeInjectivity. { intros x. apply isaprop_braiding_laws. }
    Check pr1_transportf.
    etrans. { refine (pr1_transportf _ _). }
    cbn.

    Print braiding_data.
    unfold subtypePath.

    (* We need to re-prove that [braiding_data] only depends on the object tensor) *)
    
    unfold quasicartesian_monoidal_eq. 
    unfold quasicartesian_monoidal_data_eq.

    etrans. {
      refine (transportf_total2_paths_f braiding_data_descends _ _ _).
    }

    etrans. {
      refine (transportf_total2_paths_f braiding_data_descends' _ _ _).
    }

    etrans. {
      refine (transportf_total2_paths_f braiding_data_descends'' _ _ _).
    }

    etrans. {
      refine (idpath_transportf _ _).
    }

    do 2 (apply funextsec2; intros).
    etrans. {
      refine (!pairing_proj_braiding _ _).
    }
    reflexivity. 
  Defined.

  Definition markov_category_data_descends :
    descend (sigma_fiber (idpath markov_category_data)).
  Proof.
    Print markov_category_data.
    repeat (apply descend_prod || (apply descend_pi || apply descend_sigma); intros).
    - intros a. exact (is_semicartesian a).
    - intros c. exact (∏ x : c, c ⟦ x, x ⊗ x ⟧).
  Defined.   

  Definition quasicartesian_to_markov_data_eq :
    quasicartesian_to_markov_data Q = C.
  Proof.
    unfold quasicartesian_to_markov_data.
    use total2_paths_f. { apply quasicartesian_sym_monoidal_eq. }
    cbn.
    unfold quasicartesian_sym_monoidal_eq.
    unfold quasicartesian_monoidal_cat_eq.

    etrans. {
      refine (transportf_total2_paths_f markov_category_data_descends _ _ _).
    }

    etrans. {
      refine (total2_paths_vertical' quasicartesian_monoidal_eq). exact C.
    }

    Search "path" "assoc".

    unfold quasicartesian_monoidal_eq.
    unfold subtypePath.
    (* unfold quasicartesian_monoidal_data_eq. *)
    unfold markov_category_data_descends, descend_prod. cbn.
    unfold quasicartesian_monoidal_data_eq.
    unfold quasicartesian_tensor_data_eq.
  Admitted.


  (* Proposition markov_to_quasicartesian_inv_data :
    quasicartesian_to_markov_data (markov_to_quasicartesian C) = C.
  Proof.
    unfold quasicartesian_to_markov_data,
           markov_to_quasicartesian.
    cbn.
    (* rewrite pair_eta.
    pose(D := C).
    assert(E : C = D). { reflexivity. } *)

    destruct C as [[[[C0 [mon monlaws]] sym] [semicart copy]] laws].
    unfold quasicartesian_sym_monoidal_cat, 
           quasicartesian_monoidal_cat,
           quasicartesian_monoidal,
           quasicartesian_monoidal_data,
           markov_to_quasicartesian_data.
    cbn.
    
    use total2_paths_f. { cbn.
      use total2_paths_f. { cbn. 
        use total2_paths_f. { apply idpath. }
        rewrite idpath_transportf. cbn.
        use total2_paths_f. { cbn.
          unfold make_monoidal_data, 
                 quasicartesian_tensor_data,
                 make_bifunctor_data.
          use total2_paths_f. { cbn.
            use total2_paths_f. { cbn. apply idpath. }
            rewrite idpath_transportf. cbn.
            apply dirprod_paths.
            - do 4 (apply funextsec2; intros). cbn.
              etrans. {
                rewrite <- (pairing_proj_whisker_l).
              }
          }
        }
      }
    }
  Admitted. *)

  Proposition markov_to_quasicartesian_inv : 
    quasicartesian_to_markov (markov_to_quasicartesian C) = C.
  Proof.
    unfold quasicartesian_to_markov, markov_to_quasicartesian.
    apply subtypePath.
    - exact isaprop_markov_category_laws.
    - cbn. 
  Admitted. 

End MarkovToQuasiCartesianToMarkov.

(* isequivalence markov_cat qcart *)