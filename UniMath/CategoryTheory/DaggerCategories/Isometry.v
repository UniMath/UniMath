(*********************************************
This file defines the auxiliary notions of isometries and coisometries in dagger categories

* An isometry is a morphism satisfying f · f† = identity
* A coisometry is a morphism satisfying f† · f = identity

A morphism is unitary if and only if it is an isometry and a coisometry
**********************************************)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.

Local Open Scope cat.

Section IsometriesDef.
  Context {C : category} (dag : dagger_structure C).
  Local Notation "f †" := (dag _ _ f).

  Definition is_isometry {x y : C} (f : x --> y) : UU
    := f · (f †) = identity x.

  Definition isometry (x y : C) : UU
    := ∑ f : x --> y, is_isometry f.

  Definition make_isometry {x y : C} (f : x --> y) (p : is_isometry f) : isometry x y
    := f ,, p.

  Coercion isometry_to_mor {x y : C} (f : isometry x y) : x --> y 
    := pr1 f.

  Proposition isometry_property {x y : C} (f : isometry x y) : is_isometry f.
  Proof.
    exact (pr2 f).
  Qed. 

  Lemma isaprop_is_isometry {x y : C} (f : x --> y) 
    : isaprop (is_isometry f).
  Proof.
    apply homset_property.
  Qed.

  Lemma isaset_isometry {x y : C} : isaset (isometry x y).
  Proof.
    apply isaset_total2.
    - apply homset_property.
    - intro ; apply isasetaprop ; apply isaprop_is_isometry.
  Qed.

  Lemma isometry_eq {x y : C} (f g : isometry x y) :
    pr1 f = pr1 g -> f = g.
  Proof.
    use subtypePath.
    intro p.
    apply isaprop_is_isometry.    
  Qed.

End IsometriesDef.

Section CoisometriesDef.
  Context {C : category} (dag : dagger_structure C).
  Local Notation "f †" := (dag _ _ f).

  Definition is_coisometry {x y : C} (f : x --> y) : UU
    := (f †) · f = identity y.

  Definition coisometry (x y : C) : UU
    := ∑ f : x --> y, is_coisometry f.

  Definition make_coisometry {x y : C} (f : x --> y) (p : is_coisometry f) : coisometry x y
    := f ,, p.

  Coercion coisometry_to_mor {x y : C} (f : coisometry x y) : x --> y 
    := pr1 f.

  Proposition coisometry_property {x y : C} (f : coisometry x y) : is_coisometry f.
  Proof.
    exact (pr2 f).
  Qed. 

  Lemma isaprop_is_coisometry {x y : C} (f : x --> y) 
    : isaprop (is_coisometry f).
  Proof.
    apply homset_property.
  Qed.

  Lemma isaset_coisometry {x y : C} : isaset (coisometry x y).
  Proof.
    apply isaset_total2.
    - apply homset_property.
    - intro ; apply isasetaprop ; apply isaprop_is_coisometry.
  Qed.

  Lemma coisometry_eq {x y : C} (f g : coisometry x y) :
    pr1 f = pr1 g -> f = g.
  Proof.
    use subtypePath.
    intro p.
    apply isaprop_is_coisometry.
  Qed.

End CoisometriesDef.

Section IsometryCoisometryProperties.
  Context {C : category} (dag : dagger C).
  Local Notation "f †" := (dag _ _ f).

  (* Isometries: Identity and composition *)

  Proposition is_isometry_id {x : C} : is_isometry dag (identity x).
  Proof.
    unfold is_isometry.
    rewrite dagger_to_law_id.
    apply id_left.
  Qed.

  Definition isometry_id (x : C) : isometry dag x x.
  Proof.
    use make_isometry.
    - exact (identity x).
    - apply is_isometry_id.
  Defined.

  Proposition is_isometry_comp {x y z : C} {f : x --> y} {g : y --> z} 
    : is_isometry dag f -> is_isometry dag g -> is_isometry dag (f · g).
  Proof.
    unfold is_isometry. 
    intros isomf isomg.
    rewrite dagger_to_law_comp.
    assert(e : f · g · (g † · f †) = f · (g · g †) · f †). { rewrite !assoc. reflexivity. }
    rewrite e, isomg, id_right, isomf.
    reflexivity.
  Qed.

  Definition isometry_comp {x y z : C} (f : isometry dag x y) (g : isometry dag y z) 
    : isometry dag x z.
  Proof.
    use make_isometry.
    - exact (f · g).
    - apply is_isometry_comp; apply isometry_property.
  Defined.

  (* Coisometries: Identity and composition *)
  
  Proposition is_coisometry_id {x : C} : is_coisometry dag (identity x).
  Proof.
    unfold is_coisometry.
    rewrite dagger_to_law_id.
    apply id_left.
  Qed.

  Definition coisometry_id (x : C) : coisometry dag x x.
  Proof.
    use make_coisometry.
    - exact (identity x).
    - apply is_coisometry_id.
  Defined.

  Proposition is_coisometry_comp {x y z : C} {f : x --> y} {g : y --> z} 
    : is_coisometry dag f -> is_coisometry dag g -> is_coisometry dag (f · g).
  Proof.
    unfold is_coisometry. 
    intros coisomf coisomg.
    rewrite dagger_to_law_comp.
    assert(e : g † · f † · (f · g) = g † · (f † · f) · g). { rewrite !assoc. reflexivity. }
    rewrite e, coisomf, id_right, coisomg.
    reflexivity.
  Qed.

  Definition coisometry_comp {x y z : C} (f : coisometry dag x y) (g : coisometry dag y z)
    : coisometry dag x z.
  Proof.
    use make_coisometry.
    - exact (f · g).
    - apply is_coisometry_comp; apply coisometry_property.
  Defined.

  (* Dagger lemmas *)

  Proposition isometry_coisometry_dagger {x y : C} {f : x --> y}
    : is_isometry dag f <-> is_coisometry dag (f †).
  Proof.
    unfold is_isometry, is_coisometry.
    split ; (intros ; rewrite dagger_to_law_idemp in *; assumption).
  Qed.

  Proposition coisometry_isometry_dagger {x y : C} {f : x --> y}
    : is_coisometry dag f <-> is_isometry dag (f †).
  Proof.
    unfold is_isometry, is_coisometry.
    split ; (intros ; rewrite dagger_to_law_idemp in *; assumption).
  Qed.

  Definition isometry_dag {x y : C} (f : isometry dag x y) : coisometry dag y x.
  Proof.
    use make_coisometry.
    - exact (f †).
    - abstract (apply isometry_coisometry_dagger; apply isometry_property).
  Defined.  

  Definition coisometry_dag {x y : C} (f : coisometry dag x y) : isometry dag y x.
  Proof.
    use make_isometry.
    - exact (f †).
    - abstract (apply coisometry_isometry_dagger; apply coisometry_property).
  Defined. 

  (* Relation with unitaries *)

  Proposition unitary_isometry_coisometry {x y : C} {f : x --> y} 
    : is_unitary dag f <-> (is_isometry dag f) × (is_coisometry dag f).
  Proof.
    unfold is_unitary, is_inverse_in_precat, is_isometry, is_coisometry.
    split; intros p; exact p.
  Qed.
  
  Definition unitary_to_isometry {x y : C} (f : unitary dag x y) : isometry dag x y.
  Proof.
    use make_isometry.
    - exact f.
    - abstract (apply unitary_isometry_coisometry; exact (pr2 f)).
  Defined.  

  Lemma z_iso_isometry_unitary {x y : C} (f : z_iso x y) 
    : is_isometry dag f -> is_unitary dag f.
  Proof.
    unfold is_isometry.
    intros isomf.
    pose (g := inv_from_z_iso f).
    assert (e : f † = g).
    { 
      rewrite <- (id_left (f †)).
      rewrite <- z_iso_after_z_iso_inv with f.
      rewrite <- assoc, isomf, id_right.
      reflexivity.     
    }
    split.
    - exact isomf.
    - rewrite e.
      apply z_iso_after_z_iso_inv.
  Qed.

  Lemma z_iso_coisometry_unitary {x y : C} (f : z_iso x y) 
    : is_coisometry dag f -> is_unitary dag f.
  Proof.
    unfold is_coisometry.
    intros coisomf.
    pose (g := inv_from_z_iso f).
    assert (e : f † = g).
    { 
      rewrite <- (id_right (f †)).
      rewrite <- z_iso_inv_after_z_iso with f.
      rewrite assoc, coisomf, id_left.
      reflexivity.     
    }
    split.
    - rewrite e.
      apply z_iso_inv_after_z_iso.
    - assumption.
  Qed.

  (* Cancellation lemmas *)

  Proposition coisometry_epi {x y z : C} (f : coisometry dag x y) (g1 g2 : y --> z) 
    : f · g1 = f · g2 -> g1 = g2.
  Proof. 
    intros e.
    rewrite <- (id_left g1), <- (id_left g2).
    rewrite <- (coisometry_property dag f).
    rewrite <- !assoc.
    rewrite e.
    reflexivity.
  Qed.

  Proposition isometry_mono {x y z : C} (f : isometry dag y z) (g1 g2 : x --> y) 
    : g1 · f = g2 · f -> g1 = g2.
  Proof. 
    intros e.
    rewrite <- (id_right g1), <- (id_right g2).
    rewrite <- (isometry_property dag f).
    rewrite !assoc.
    rewrite e.
    reflexivity.
  Qed.

End IsometryCoisometryProperties.