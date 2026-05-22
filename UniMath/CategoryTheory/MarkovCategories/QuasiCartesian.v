(*********************************************
An Alternative Axiomatization of Markov Categories

Cartesian categories with chosen products have an equational presentation
using pairing and projections. This presentation is convenient because
deciding coherence is easily automated using η-laws and rewriting.

We adapt this style of presentation to give an alternative axiomatization 
for Markov categories, which we dub "quasicartesian". 
This has a series of advantages over the traditional axiomatization
1. The same automation strategy for coherence remains functional, which is a 
   big improvement over reasoning with the original Markov category axioms. 
2. The quasicartesian axioms are simpler than the full Markov category axiomatization,
   which helps in constructing instances. Unlike for cartesian categories where
   picking a monoidal structure requires a choice, no choice is needed here. 

The only difference to the cartesian axioms is that η-laws only hold for
deterministic morphisms, so we need to axiomatize determinism separately. 
But again, discharging these determinism assumptions is easily automated. 

We show that the two axiomatizations of Markov categories are equivalent
in QuasiCartesianVsMarkov.v.

Table of Contents
1. Definition of quasicartesian categories
2. Accessors
3. Derived laws
4. Automation
5. Further laws

**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Local Open Scope cat.

Declare Scope quasicartesian.
Delimit Scope quasicartesian with quasicartesian.

Local Open Scope quasicartesian.

(** * 1. Definition of quasicartesian categories *)

Definition quasicartesian_data : UU :=
  ∑ (C : category),
      (∑ (Unit : C), ∏ (x : C), x --> Unit)
      × 
      ∑ (tensor : C -> C -> C),
        (∏ (x y z : C), (x --> y) -> (x --> z) -> (x --> tensor y z))
        ×
        (∏ x y, tensor x y --> x)
        × 
        (∏ x y, tensor x y --> y).

Coercion quasicartesian_data_to_cat (Q : quasicartesian_data) : category := pr1 Q.

(** * 2. Accessors *)

Definition Unit {C : quasicartesian_data} : C := pr112 C.

Definition del {C : quasicartesian_data} (x : C) : x --> Unit := pr212 C x.

Definition tensor {C : quasicartesian_data} (x y : C) : C := pr122 C x y.

Notation "x ⊗ y" := (tensor x y) : quasicartesian.

Definition pairing {C : quasicartesian_data} {x y z : C} 
                   (f : x --> y) (g : x --> z) : x --> y ⊗ z
           := pr1 (pr222 C) x y z f g.

Notation "⟨ f , g ⟩" := (pairing f g) : quasicartesian.

Definition proj1 {C : quasicartesian_data} {x y : C} : x ⊗ y --> x
  := pr12 (pr222 C) x y.

Definition proj2 {C : quasicartesian_data} {x y : C} : x ⊗ y --> y
  := pr22 (pr222 C) x y.

(* Determinism *)

Definition det {C : quasicartesian_data} {x y : C} (f : x --> y) :=
  f · ⟨identity _, identity _⟩ = ⟨f, f⟩.

(** Laws *)

Definition quasicartesian_laws (C : quasicartesian_data) : UU :=
  (∏ (x y z : C) (f : x --> y) (g : x --> z), ⟨f,g⟩ · proj1 = f)
  ×
  (∏ (x y z : C) (f : x --> y) (g : x --> z), ⟨f,g⟩ · proj2 = g)
  ×
  (∏ (x : C) (f : x --> Unit), f = del x)
  ×
  (∏ (x y : C), det (@proj1 C x y))
  ×
  (∏ (x y : C), det (@proj2 C x y))
  ×
  (∏ (x : C), det (del x))
  ×
  (∏ (x y z : C) (f : x --> y) (g : x --> z),
      det f -> det g -> det ⟨f,g⟩)
  ×
  (∏ (x y : C), identity (x ⊗ y) = ⟨proj1, proj2⟩)
  ×
  (∏ (a x1 x2 y1 y2 : C) (f1 : a --> x1) (f2 : a --> x2)
                         (g1 : x1 --> y1) (g2 : x2 --> y2),
      ⟨f1,f2⟩ · ⟨proj1 · g1, proj2 · g2⟩ = ⟨f1·g1, f2·g2⟩)
  ×
  (∏ (x y z w : C) (f : x --> y) (g : x --> z) (h : x --> w),
      ⟨ ⟨ f, g ⟩, h ⟩ · ⟨ proj1 · proj1, ⟨ proj1 · proj2, proj2 ⟩ ⟩
      = ⟨ f , ⟨ g, h ⟩ ⟩)
  ×
  (∏ (a x y : C) (f : a --> x) (g : a --> y),
      ⟨ f , g ⟩ · ⟨ proj2, proj1 ⟩ = ⟨ g , f ⟩).

Proposition isaprop_quasicartesian_laws 
            (C : quasicartesian_data)
     : isaprop (quasicartesian_laws C).
Proof.
  unfold quasicartesian_laws.
  (repeat apply isapropdirprod)
  ; repeat (apply impred_isaprop; intros)
  ; try apply homset_property.
Qed.

Definition quasicartesian_category : UU
  := ∑ (C : quasicartesian_data),
     quasicartesian_laws C.

Coercion quasicartesian_category_to_data (C : quasicartesian_category) : quasicartesian_data 
  := pr1 C.

Notation "f #⊗ g" := (⟨ proj1 · f, proj2 · g⟩) (at level 31) : quasicartesian.

Section QuasicartesianLaws.
  Context {C : quasicartesian_category}.

  (** Accessors for the laws *)

  Proposition pairing_proj1 {x y z : C} (f : x --> y) (g : x --> z) :
    ⟨f, g⟩ · proj1 = f.
  Proof.
    exact ((pr12 C) x y z f g).
  Qed.

  Proposition pairing_proj2 {x y z : C} (f : x --> y) (g : x --> z) :
    ⟨f, g⟩ · proj2 = g.
  Proof.
    exact ((pr122 C) x y z f g).
  Qed.
  
  Proposition del_unique {x : C} (f : x --> Unit) : f = del x.
  Proof.
    exact (pr1 (pr222 C) x f).
  Qed.

  Proposition det_proj1 {x y : C} : det (@proj1 C x y).
  Proof.
    exact (pr12 (pr222 C) x y).
  Qed.

  Proposition det_proj2 {x y : C} : det (@proj2 C x y).
  Proof.
    exact (pr122 (pr222 C) x y).
  Qed.

  Proposition det_del {x : C} : det (del x).
  Proof.
    exact (pr1 (pr222 (pr222 C)) x).
  Qed.

  Proposition det_pairing {x y z : C} (f : x --> y) (g : x --> z) :
      det f -> det g -> det ⟨f, g⟩.
  Proof.
    exact (pr12 (pr222 (pr222 C)) x y z f g).
  Qed.

  Proposition pairing_id {x y : C} :  identity (x ⊗ y) = ⟨proj1, proj2⟩.
  Proof.
    exact (pr122 (pr222 (pr222 C)) x y).
  Qed.

  Proposition pairing_tensor {a x1 x2 y1 y2 : C} 
                             (f1 : a --> x1) (f2 : a --> x2)
                             (g1 : x1 --> y1) (g2 : x2 --> y2) :
      ⟨f1, f2⟩ · ⟨proj1 · g1, proj2 · g2⟩ = ⟨f1 · g1, f2 · g2⟩.
  Proof.
    exact (pr1 (pr222 (pr222 (pr222 C))) a x1 x2 y1 y2 f1 f2 g1 g2).
  Qed.

  Proposition pairing_assoc {x y z w : C} (f : x --> y) (g : x --> z) (h : x --> w) :
        ⟨ ⟨ f, g ⟩, h ⟩ · ⟨ proj1 · proj1, ⟨ proj1 · proj2, proj2 ⟩ ⟩
      = ⟨ f , ⟨ g, h ⟩ ⟩.
  Proof.
    exact (pr12 (pr222 (pr222 (pr222 C))) x y z w f g h).
  Qed.

  Proposition pairing_swap {a x y : C} (f : a --> x) (g : a --> y) :
      ⟨ f , g ⟩ · ⟨ proj2, proj1 ⟩ = ⟨ g , f ⟩.
  Proof.
    exact (pr22 (pr222 (pr222 (pr222 C))) a x y f g).
  Qed.

  (** * 3. Derived laws *)

  Proposition det_id {x : C} : det (identity x).
  Proof.
    unfold det.
    now rewrite id_left.
  Qed.

  Proposition det_comp {x y z : C} (f : x --> y) (g : y --> z) :
    det f -> det g -> det (f · g).
  Proof.
    intros df dg. unfold det in *.
    rewrite assoc', dg.
    transitivity (f · ⟨ identity y · g, identity y · g⟩). { rewrite id_left. reflexivity. }
    rewrite <- pairing_tensor, assoc.
    rewrite df.
    rewrite pairing_tensor.
    reflexivity.
  Qed.

  Proposition det_proj (x y z : C) (f : x --> y ⊗ z) :
    det f -> ⟨f · proj1, f · proj2⟩ = f.
  Proof.
    intros df.
    rewrite <- pairing_tensor.
    rewrite <- df.
    rewrite assoc'.
    rewrite pairing_tensor.
    rewrite !id_left.
    rewrite <- pairing_id.
    rewrite id_right.
    reflexivity.
  Qed.

  Proposition eta_det {x y z : C} (f g : x --> y ⊗ z) :
    det f -> det g ->
    (f · proj1 = g · proj1) -> (f · proj2 = g · proj2) -> f = g.
  Proof.
    intros df dg e1 e2.
    rewrite <- (det_proj _ _ _ f df), <- (det_proj _ _ _ g dg) .
    rewrite e1, e2. reflexivity.
  Qed.

  Proposition eta_Unit {x : C} (f g : x --> Unit) : f = g.
  Proof.
    rewrite (del_unique f), (del_unique g).
    reflexivity.
  Qed.

  (* Auxiliary lemmas *)

  Lemma proj1_inner {a b x y : C} (f : a --> b) (g : b --> x) (h : b --> y) :
    f · ⟨ g , h ⟩ · proj1 = f · g.
  Proof.
    rewrite assoc', pairing_proj1. reflexivity.
  Qed.

  Lemma proj2_inner {a b x y : C} (f : a --> b) (g : b --> x) (h : b --> y) :
    f · ⟨ g , h ⟩ · proj2 = f · h.
  Proof.
    rewrite assoc', pairing_proj2. reflexivity.
  Qed.

  Lemma pairing_nat_det {x y z w : C} (f : x --> y) (g : y --> z) (h : y --> w) :
    det f -> ⟨ f · g, f · h ⟩ = f · ⟨ g, h ⟩.
  Proof.
    intros df.
    rewrite <- pairing_tensor, <- df, !assoc'.
    rewrite pairing_tensor, !id_left.
    reflexivity.
  Qed.

  Lemma pairing_nat_l {a x y z : C} (f1 : a --> x) (f2 : a --> y) (g : x --> z) :
    ⟨ f1 , f2 ⟩ · ⟨ proj1 · g, proj2 ⟩ = ⟨ f1 · g, f2 ⟩.
  Proof.
    rewrite <- (id_right proj2), pairing_tensor, id_right. reflexivity.
  Qed.

  Lemma pairing_nat_r {a x y z : C} (f1 : a --> x) (f2 : a --> y) (g : y --> z) :
    ⟨ f1 , f2 ⟩ · ⟨ proj1 , proj2 · g ⟩ = ⟨ f1 , f2 · g ⟩.
  Proof.
    rewrite <- (id_right proj1), pairing_tensor, id_right. reflexivity.
  Qed.

End QuasicartesianLaws.

(** * 4. Automation *)

Create HintDb autodet.
Hint Resolve det_id : autodet.
Hint Resolve det_proj1 : autodet.
Hint Resolve det_proj2 : autodet.
Hint Resolve det_del : autodet.
Hint Resolve det_comp : autodet.
Hint Resolve det_pairing : autodet. 

(* Normalize by right-associating everything *)
Ltac normalize := repeat (rewrite assoc).

(* A single simplification step *)
Ltac qcart_simpl_step :=
     (rewrite id_left)
  || (rewrite id_right) 
  || (rewrite pairing_proj1)
  || (rewrite pairing_proj2)
  || (rewrite proj1_inner)
  || (rewrite proj2_inner).

(* Simplify by repeated steps *)
Ltac qcart_simpl := repeat (normalize; qcart_simpl_step).

(* Try solving some simple goals at unit or ground type *)
Ltac qcart_solve :=
  (try apply eta_Unit) || (qcart_simpl; try reflexivity).

(* At tensor type, repeatedly split goals using the eta law *)
Ltac qcart_split :=
  repeat (apply eta_det; try auto 20 with autodet).

(* Repeatedly split and solve *)
Ltac qcart_coherence :=
  qcart_simpl; qcart_split; qcart_solve.


(** * 5. Further laws *)
  
Section MoreLaws.
  Context {C : quasicartesian_category}.

  Proposition proj1_expand {x y z : C} :
    @proj1 C (x ⊗ y) z = ⟨ proj1 · proj1 , proj1 · proj2 ⟩.
  Proof.
    qcart_coherence.
  Qed.

  Lemma proj2_expand {x y z : C} :
    @proj2 C z (x ⊗ y) = ⟨ proj2 · proj1 , proj2 · proj2 ⟩.
  Proof.
    qcart_coherence.
  Qed.

  Proposition pairing_assoc' {x y z w : C} (f : x --> y) (g : x --> z) (h : x --> w) :
        ⟨ f , ⟨ g, h ⟩ ⟩ · ⟨ ⟨ proj1, proj2 · proj1 ⟩, proj2 · proj2 ⟩ 
      = ⟨ ⟨ f, g ⟩, h ⟩.
  Proof.
    rewrite <- (id_right ⟨ ⟨ f, g ⟩, h ⟩).
    rewrite <- pairing_assoc.
    rewrite assoc'.
    apply maponpaths.
    qcart_coherence.
  Qed.

  (* Defining coherence maps *)

  (* TODO do we need this? *)
  Definition lassociator {x y z : C} : (x ⊗ y) ⊗ z --> x ⊗ (y ⊗ z)
    :=  ⟨ proj1 · proj1, ⟨ proj1 · proj2, proj2 ⟩ ⟩. 

  Definition rassociator {x y z : C} : x ⊗ (y ⊗ z) --> (x ⊗ y) ⊗ z 
    :=   ⟨ ⟨ proj1, proj2 · proj1 ⟩, proj2 · proj2 ⟩.

  Definition lunitor {x : C} : Unit ⊗ x --> x := proj2.
  Definition linvunitor {x : C} : x --> Unit ⊗ x := ⟨ del x, identity x ⟩.
  
  Definition runitor {x : C} : x ⊗ Unit --> x := proj1.
  Definition rinvunitor {x : C} : x --> x ⊗ Unit := ⟨ identity x, del x ⟩.

  Definition swap {x y : C} : x ⊗ y --> y ⊗ x := ⟨ proj2, proj1 ⟩.

  (* Example *)

  Definition inner_swap {x y z w : C} : (x ⊗ y) ⊗ (z ⊗ w) --> (x ⊗ z) ⊗ (y ⊗ w) 
    := ⟨ proj1 #⊗ proj1, proj2 #⊗ proj2 ⟩.
  
  Definition inner_swap_linear {x y z w : C} : (x ⊗ y) ⊗ (z ⊗ w) --> (x ⊗ z) ⊗ (y ⊗ w).
  Proof.
    refine(
      lassociator
      · (identity x #⊗ _)
      · rassociator).
    refine(rassociator · (_ #⊗ identity w) · lassociator).
    exact swap.
  Defined.

  (* The proof strategy follows the definition of [inner_swap_linear ]*)
  Proposition pairing_inner_swap_linear {a x y z w : C} (f : a --> x) (g : a --> y) (h : a --> z) (i : a --> w) :
    ⟨ ⟨ f, g ⟩, ⟨ h, i ⟩ ⟩ · inner_swap_linear = ⟨ ⟨ f, h ⟩, ⟨ g, i ⟩ ⟩.
  Proof.
    unfold inner_swap_linear.
    rewrite !assoc.
    unfold lassociator. rewrite pairing_assoc. (* lassoc *)
    etrans. {
      apply maponpaths_2.
      rewrite !assoc'.
      rewrite pairing_tensor. (* tensor *)
      rewrite assoc.
      unfold rassociator. rewrite pairing_assoc'. (* rassoc *)
      rewrite assoc.
      rewrite pairing_tensor. (* tensor *)
      unfold swap. rewrite pairing_swap. (* swap *)
      rewrite !id_right.
      rewrite pairing_assoc. (* lassoc *)
      reflexivity.
    }
    unfold rassociator. rewrite pairing_assoc'. (* rassoc *)
    reflexivity.
  Qed.

  Proposition pairing_inner_swap {a x y z w : C} (f : a --> x) (g : a --> y) (h : a --> z) (i : a --> w) :
    ⟨ ⟨ f, g ⟩, ⟨ h, i ⟩ ⟩ · inner_swap = ⟨ ⟨ f, h ⟩, ⟨ g, i ⟩ ⟩.
  Proof.
    assert(e : @inner_swap x y z w = @inner_swap_linear x y z w). {
      unfold inner_swap, inner_swap_linear.
      unfold lassociator, rassociator, swap. 
      qcart_coherence.
    }
    rewrite e.
    apply pairing_inner_swap_linear.
  Qed.

End MoreLaws.