(*********************************************
An Alternative Axiomatization of Markov Categories

Cartesian categories have an equational presentation using 
pairing and projections. We adapt this presentation to give an
alternative axiomatization of Markov categories. 
* The advantage is that reasoning about coherence 
  in the new axioms is much simpler and easy to automate.
* Our presentation becomes implicational because some 
  η-laws only hold for deterministic morphisms.

It also seems related to the equational presentation 
of the CD calculus, and centrality in Freyd categories

We call this presentation "quasicartesian".
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

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.
(* 
Declare Scope markov.
Delimit Scope markov with markov.

Local Open Scope markov. *)

Section Quasicartesian.
  Context (C : category)
          (I : C)
          (tensor : C -> C -> C)
          (pairing : 
            ∏ (x y z : C) (f : x --> y) (g : x --> z), 
            x --> tensor y z)
          (proj1 : ∏ x y, tensor x y --> x)
          (proj2 : ∏ x y, tensor x y --> y)
          (del : ∏ (x : C), x --> I).

  Arguments pairing {x y z}.
  Arguments proj1 {x y}.
  Arguments proj2 {x y}.

  Notation "x ⊗ y" := (tensor x y).
  Notation "⟨ f , g ⟩" := (pairing f g).

  Context (pairing_proj1 : ∏ (x y z : C) (f : x --> y) (g : x --> z),
             ⟨f,g⟩ · proj1 = f)
          (pairing_proj2 : ∏ (x y z : C) (f : x --> y) (g : x --> z),
             ⟨f,g⟩ · proj2 = g).

  Context (del_unique : ∏ (x : C) (f : x --> I), f = del x).  

  Definition det {x y : C} (f : x --> y) := 
    f · ⟨ identity y , identity y ⟩ = ⟨ f , f ⟩.

  Context (det_id : ∏ x, det (identity x))
          (det_proj1 : ∏ x y, det (@proj1 x y))
          (det_proj2 : ∏ x y, det (@proj2 x y))
          (det_del : ∏ x, det (del x)).

  Context (det_comp : ∏ (x y z : C) (f : x --> y) (g : y --> z),
             det f -> det g -> det (f · g)).
  
  Context (det_pairing : ∏ (x y z : C) (f : x --> y) (g : x --> z),
             det f -> det g -> det ⟨f,g⟩ ).

  Context (det_proj : ∏ (x y z : C) (f : x --> y ⊗ z),
             det f -> ⟨f · proj1, f · proj2⟩ = f).

  Context (pairing_nat : ∏ (a x1 x2 y1 y2 : C)
                           (f1 : a --> x1) (f2 : a --> x2)
                           (g1 : x1 --> y1) (g2 : x2 --> y2),
            ⟨f1,f2⟩ · ⟨proj1 · g1, proj2 · g2⟩ = ⟨f1·g1, f2·g2⟩).

  
  Create HintDb autodet.
  Hint Resolve det_id : autodet.
  Hint Resolve det_proj1 : autodet.
  Hint Resolve det_proj2 : autodet.
  Hint Resolve det_del : autodet.
  Hint Resolve det_comp : autodet.
  Hint Resolve det_pairing : autodet. 

  (* Derived definitions *)

  Proposition eta_det {x y z : C} (f g : x --> y ⊗ z) :
    det f -> det g ->
    (f · proj1 = g · proj1) -> (f · proj2 = g · proj2) -> f = g.
  Proof.
    intros df dg e1 e2.
    rewrite <- (det_proj _ _ _ f df), <- (det_proj _ _ _ g dg) .
    rewrite e1, e2. reflexivity.
  Qed.

  Proposition eta_I {x : C} (f g : x --> I) : f = g.
  Proof.
    now rewrite (del_unique _ f), (del_unique _ g).
  Qed.

  (* Tensor *)
  Definition tensor_mor {x1 x2 y1 y2} (f1 : x1 --> y1) (f2 : x2 --> y2) : 
      x1 ⊗ x2 --> y1 ⊗ y2 := ⟨proj1 · f1, proj2 · f2⟩.
  
  Notation "f #⊗ g" := (tensor_mor f g).

  Hint Unfold tensor_mor : autodet.

  Proposition tensor_det {x1 x2 y1 y2} (f1 : x1 --> y1) (f2 : x2 --> y2) :
    det f1 -> det f2 -> det (f1 #⊗ f2).
  Proof.
    intros d1 d2. unfold tensor_mor. auto with autodet.
  Qed.

  (* Associator *)


  (* Lemmas *)
  Lemma pairing_id (x y : C) : identity (x ⊗ y) = ⟨proj1, proj2⟩.
  Proof.
    apply eta_det; try auto with autodet.
    - rewrite id_left, pairing_proj1. reflexivity.
    - rewrite id_left, pairing_proj2. reflexivity.
  Qed.   

  (* Building a monoidal category *)

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
    - exact I.
    - intros x. exact proj2.
    - intros x. exact ⟨del x, identity x⟩.
    - intros x. exact proj1.
    - intros x. exact ⟨identity x, del x⟩.
    - intros x y z. exact ⟨ proj1 · proj1, ⟨ proj1 · proj2, proj2 ⟩ ⟩.
    - intros x y z. cbn. exact ⟨⟨ proj1, proj2 · proj1⟩, proj2 · proj2⟩.
  Defined.  

    (* Automation *)

  Lemma proj1_inner {a b x y} (f : a --> b) (g : b --> x) (h : b --> y) :
    f · ⟨ g , h ⟩ · proj1 = f · g.
  Proof.
    now rewrite assoc', pairing_proj1.
  Qed.

  Lemma proj2_inner {a b x y} (f : a --> b) (g : b --> x) (h : b --> y) :
    f · ⟨ g , h ⟩ · proj2 = f · h.
  Proof.
    now rewrite assoc', pairing_proj2.
  Qed.
  
  (* Lemma proj1_inner' {b x y z} (g : b --> x) (h : b --> y) (j : x --> z) :
    ⟨ g , h ⟩ · (proj1 · j) = g · j.
  Proof.
    rewrite assoc.
    apply maponpaths_2.
    now rewrite pairing_proj1.
  Qed.

  Lemma proj2_inner' {b x y z} (g : b --> x) (h : b --> y) (j : y --> z) :
    ⟨ g , h ⟩ · (proj2 · j) = h · j.
  Proof.
    rewrite assoc.
    apply maponpaths_2.
    now rewrite pairing_proj2.
  Qed. *)

  (* Normalize composite terms; right-associate everything *)
  Ltac normalize := repeat (rewrite assoc).

  (* A single reduction step *)
  Ltac qcart_simpl_step :=
    normalize ||
       (rewrite id_left 
    || rewrite id_right 
    || rewrite pairing_proj1
    || rewrite pairing_proj2
    || rewrite proj1_inner
    || rewrite proj2_inner).

  (* Many reduction steps *)
  Ltac qcart_simpl := repeat qcart_simpl_step.

  (* Simplify and solve trivial goals (reflexivity or unit type) *)
  Ltac qcart_progress :=
       apply eta_I (* solve goals of type x --> I *)
    || (qcart_simpl; try reflexivity). (* try simplifying and solving *)

  (* Eta-expand deterministic morphisms of tensor type, followed by simplification *)
  Ltac qcart_eta :=
    (try qcart_progress); (apply eta_det; try auto 20 with autodet; try qcart_progress).

  Ltac qcart_coherence := repeat qcart_eta.

  Proposition pentagon : pentagon_identity α_{ quasicartesian_monoidal_data}.
  Proof.
    intros x y z w. cbn. 
    do 3 qcart_eta.
  Qed.

  Lemma proj1_expand {x y z : C} :
    ⟨ proj1 · proj1 , proj1 · proj2 ⟩ = @proj1 (x ⊗ y) z.
  Proof.
    qcart_eta.
  Qed.

  Lemma proj2_expand {x y z : C} :
    ⟨ proj2 · proj1 , proj2 · proj2 ⟩ = @proj2 z (x ⊗ y).
  Proof.
    qcart_eta.
  Qed.


  Context (pairing_assoc : ∏ (x y z w : C)
    (f : x --> y) (g : x --> z) (h : x --> w),
    ⟨ ⟨ f, g ⟩, h ⟩ · ⟨ proj1 · proj1, ⟨ proj1 · proj2, proj2 ⟩ ⟩
    = ⟨ f , ⟨ g, h ⟩ ⟩).

  Context (pairing_swap : ∏ (a x y : C) (f : a --> x) (g : a --> y),
    ⟨ f , g ⟩ · ⟨ proj2, proj1 ⟩ = ⟨ g , f ⟩).

  (* Let's see if this is provable without assuming it *)
  Proposition pairing_assoc' (x y z w : C)
    (f : x --> y) (g : x --> z) (h : x --> w) :
    ⟨ ⟨ f, g ⟩, h ⟩ · ⟨ proj1 · proj1, ⟨ proj1 · proj2, proj2 ⟩ ⟩
    = ⟨ f , ⟨ g, h ⟩ ⟩.
  Proof.
  Abort.

  Proposition left_whisker_natural : associator_nat_leftwhisker α_{ quasicartesian_monoidal_data}.
  Proof.
    intros x y z w f. cbn.
    symmetry. etrans. {
      rewrite <- proj1_expand.
      reflexivity.
    }
    rewrite pairing_assoc.
    symmetry. etrans. {
      apply maponpaths.
      apply maponpaths_2.
      rewrite <- (id_right proj1).
      reflexivity.
    }
    rewrite pairing_nat.
    etrans. {
      apply maponpaths.
      apply maponpaths.
      apply maponpaths_2.
      rewrite <- (id_right proj1).
      reflexivity.
    }
    rewrite pairing_nat, !id_right.
    reflexivity.
  Qed.

  Lemma pairing_nat_det {x y z w : C} (f : x --> y) (g : y --> z) (h : y --> w) :
    det f -> ⟨ f · g, f · h ⟩ = f · ⟨ g, h ⟩.
  Proof.
    intros df.
    rewrite <- pairing_nat, <- df, !assoc'.
    rewrite pairing_nat, !id_left.
    reflexivity.
  Qed.

  Lemma pairing_nat_l {a x y z : C} (f1 : a --> x) (f2 : a --> y) (g : x --> z) :
    ⟨ f1 , f2 ⟩ · ⟨ proj1 · g, proj2 ⟩ = ⟨ f1 · g, f2 ⟩.
  Proof.
    now rewrite <- (id_right proj2), pairing_nat, id_right.
  Qed.

  Lemma pairing_nat_r {a x y z : C} (f1 : a --> x) (f2 : a --> y) (g : y --> z) :
    ⟨ f1 , f2 ⟩ · ⟨ proj1 , proj2 · g ⟩ = ⟨ f1 , f2 · g ⟩.
  Proof.
    now rewrite <- (id_right proj1), pairing_nat, id_right.
  Qed.

  Proposition right_whisker_natural : associator_nat_rightwhisker α_{ quasicartesian_monoidal_data}.
  Proof.
    intros x y z w f. cbn.
    symmetry. etrans. {
      apply maponpaths_2.
      rewrite <- pairing_nat_det; try auto with autodet.
    }
    rewrite pairing_assoc.
    now rewrite pairing_nat_l, !assoc.
  Qed.

  Proposition left_right_whisker_natural : associator_nat_leftrightwhisker α_{ quasicartesian_monoidal_data}.
  Proof.
    intros x y z z2 w. cbn.
    rewrite <- pairing_nat_det with (f:=proj1); try auto with autodet.
    rewrite pairing_assoc.
    now rewrite pairing_nat_r, pairing_nat_l, assoc.
  Qed. 
  

  Definition quasicartesian_monoidal_laws : monoidal_laws quasicartesian_monoidal_data.
  Proof.
    repeat split.
    - (* left identity*)
       intros x y. cbn. qcart_eta.
    - (* right identity *)
      intros x y. cbn. qcart_eta.
    - (* bifunctor_leftcompax *)
      intros x b1 b2 b3 g1 g2. cbn.
      now rewrite pairing_nat_r, assoc.
    - (* bifunctor_rightcompax *)
      intros x a1 a2 a3 f1 f2. cbn.
      now rewrite pairing_nat_l, assoc.
    - (* functoronmorphisms_are_equal *)
      intros a1 a2 b1 b2 f g.  
      unfold functoronmorphisms1, functoronmorphisms2; cbn.
      now rewrite pairing_nat_l, pairing_nat_r.
    - (* Left unitor natural *) 
      intros x y f. cbn. qcart_progress.
    - (* Left unitor iso 1 *)    
      cbn. qcart_eta.
    - (* Left unitor iso 2 *) 
      cbn. qcart_progress.
    - (* Right unitor natural *)
      intros x y f. cbn. qcart_progress.
    - (* Right unitor iso 1 *) 
      cbn. qcart_eta.
    - (* Right unitor iso 2 *)
      cbn. qcart_progress.
    - (* Left whiskering natural *)   
      apply left_whisker_natural.
    - (* Right whiskering natural *)
      apply right_whisker_natural.
    - (* Left right whisker *)
      apply left_right_whisker_natural.
    - (* Associator iso 1 *)
      cbn. do 2 qcart_eta.
    - (* Associator iso 2 *)  
      cbn. do 2 qcart_eta.
    - (* Triangle identity *)   
      intros x y. cbn. qcart_eta.
    - (* Pentagon identity *) 
      apply pentagon.
  Defined.

  Definition quasicartesian_monoidal : monoidal C.
  Proof.
    exact (quasicartesian_monoidal_data ,, quasicartesian_monoidal_laws).
  Defined.

  Definition quasicartesian_monoidal_cat : monoidal_cat.
  Proof.
    refine (C ,, _).
    apply quasicartesian_monoidal.
  Defined.

  (* Symmetry *)
       
  Definition swap {x y : C} : x ⊗ y --> y ⊗ x := ⟨ proj2, proj1 ⟩.

  Definition swap_laws : sym_mon_cat_laws_tensored
       quasicartesian_monoidal_cat (λ x y : C, swap).
  Proof.
    repeat split.
    - (* involution *)
      intros x y. cbn. unfold swap.
      qcart_eta.
    - intros x y z w f g. 
      unfold swap, monoidal_cat_tensor_mor, functoronmorphisms1. cbn.
      now rewrite !pairing_nat_r, pairing_nat, pairing_swap.
    - intros x y z. cbn. 
      unfold swap, monoidal_cat_tensor_mor, functoronmorphisms1. cbn.
      do 2 qcart_eta.
  Defined.      

  Definition sym : symmetric quasicartesian_monoidal.
  Proof.
    use (make_symmetric quasicartesian_monoidal_cat _ _).
    - intros x y. apply swap.
    - apply swap_laws.
  Defined.
  
  Definition quasicartesian_sym_monoidal_cat : sym_monoidal_cat.
  Proof.
    refine (quasicartesian_monoidal_cat ,, sym).
  Defined.

  (* Markov category -- ez *)

  Definition quasicartesian_markov_data : markov_category_data.
  Proof.
    refine (quasicartesian_sym_monoidal_cat ,, _ ,, _).
    - intros x. refine (del x ,, _).
      intros f. apply del_unique.
    - intros x. exact ⟨ identity x , identity x ⟩.
  Defined.

  Definition quasicartesian_markov_laws : markov_category_laws quasicartesian_markov_data.
  Proof.
    repeat split; cbn; unfold swap, monoidal_cat_tensor_mor, functoronmorphisms1; cbn.
    - intros x. do 2 qcart_eta.
    - intros x. qcart_eta.
    - intros x. qcart_eta.
    - intros x. qcart_eta.
    - intros x y. unfold inner_swap. cbn. unfold swap. 
      do 2 qcart_eta. 
  Defined.
  
  Definition quasicartesian_markov : markov_category.
  Proof.
    refine (quasicartesian_markov_data ,, quasicartesian_markov_laws).
  Defined.

End Quasicartesian.