(* *********************************************************************************** *)
(** * Internal adjunction in displayed bicategories

    Benedikt Ahrens, Marco Maggesi, Niels van der Weide, Dan Frumin
    April 2018                                                                         *)
(* *********************************************************************************** *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.EquivToAdjequiv.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Unitors.
Require Export UniMath.Bicategories.Morphisms.Adjunctions.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(** * Definitions and properties of displayed adjunctions *)
Section Displayed_Internal_Adjunction.

Context {C : bicat} {D : disp_prebicat C}.

(** ** Displayed left adjoints *)
(** *** Data & laws for left adjoints *)
Definition disp_left_adjoint_data
           {a b : C}
           {f : a --> b}
           (αd : left_adjoint_data f)
           {aa : D a} {bb : D b}
           (ff : aa -->[f] bb)
 : UU
  := ∑ (gg : bb -->[left_adjoint_right_adjoint αd] aa),
         (id_disp aa ==>[left_adjoint_unit αd] ff ;; gg)
       × (gg ;; ff ==>[left_adjoint_counit αd] id_disp bb).

Definition disp_left_adjoint_right_adjoint
           {a b : C}
           {f : a --> b}
           (αd : left_adjoint_data f)
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           (ααd : disp_left_adjoint_data αd ff) :
  bb -->[left_adjoint_right_adjoint αd] aa := pr1 ααd.

Definition disp_left_adjoint_unit
           {a b : C}
           {f : a --> b}
           (αd : left_adjoint_data f)
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           (ααd : disp_left_adjoint_data αd ff) :
  id_disp aa ==>[left_adjoint_unit αd] ff ;; disp_left_adjoint_right_adjoint αd ααd
  := pr12 ααd.

Definition disp_left_adjoint_counit
           {a b : C}
           {f : a --> b}
           (αd : left_adjoint_data f)
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           (ααd : disp_left_adjoint_data αd ff) :
  disp_left_adjoint_right_adjoint αd ααd ;; ff ==>[left_adjoint_counit αd] id_disp bb
  := pr22 ααd.

Definition disp_left_adjoint_axioms
           {a b : C}
           {f : a --> b}
           (j : left_adjoint f)
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           (ααd : disp_left_adjoint_data j ff)
  : UU
  := let gg := disp_left_adjoint_right_adjoint j ααd in
     let ηη := disp_left_adjoint_unit j ααd in
     let εε := disp_left_adjoint_counit j ααd in
( disp_linvunitor ff •• (ηη ▹▹ ff) •• disp_rassociator _ _ _ ••
         (ff ◃◃ εε) •• disp_runitor ff =
         transportb (λ x, _ ==>[x] _) (internal_triangle1 j) (disp_id2 ff) )
     × ( disp_rinvunitor gg •• (gg ◃◃ ηη) •• disp_lassociator _ _ _ ••
         (εε ▹▹ gg) •• disp_lunitor gg =
         transportb (λ x, _ ==>[x] _) (internal_triangle2 j) (disp_id2 gg) ).

Definition disp_internal_triangle1
           {a b : C}
           {f : a --> b}
           (j : left_adjoint f)
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           {ααd : disp_left_adjoint_data j ff}
           (H : disp_left_adjoint_axioms j ααd)
  := pr1 H.

Definition disp_internal_triangle2
           {a b : C}
           {f : a --> b}
           (j : left_adjoint f)
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           {ααd : disp_left_adjoint_data j ff}
           (H : disp_left_adjoint_axioms j ααd)
  := pr2 H.

Definition internal_triangle2
           {a b : C} {f : C⟦a,b⟧}
           {adj : left_adjoint_data f}
           (L : left_adjoint_axioms adj)
           (g := left_adjoint_right_adjoint adj)
  : rinvunitor g • (g ◃ left_adjoint_unit adj) • lassociator _ _ _ • (left_adjoint_counit adj ▹ g) • lunitor g = id2 g
  := pr2 L.

Definition disp_left_adjoint
           {a b : C}
           {f : a --> b}
           (α : left_adjoint f)
           {aa : D a} {bb : D b}
           (ff : aa -->[f] bb)
  := ∑ (ααd : disp_left_adjoint_data α ff),
       disp_left_adjoint_axioms α ααd.

Coercion disp_data_of_left_adjoint
         {a b : C}
         {f : a --> b}
         (α : left_adjoint f)
         {aa : D a} {bb : D b}
         {ff : aa -->[f] bb}
         (αα : disp_left_adjoint α ff)
  : disp_left_adjoint_data α ff
  := pr1 αα.

Coercion disp_axioms_of_left_adjoint
         {a b : C}
         {f : a --> b}
         (α : left_adjoint f)
         {aa : D a} {bb : D b}
         {ff : aa -->[f] bb}
         (αα : disp_left_adjoint α ff)
  : disp_left_adjoint_axioms α αα
  := pr2 αα.

(** *** Laws for equivalences *)
Definition disp_left_equivalence_axioms
         {a b : C}
         {f : a --> b}
         (αe : left_equivalence f)
         {aa : D a} {bb : D b}
         {ff : aa -->[f] bb}
         (ααd : disp_left_adjoint_data αe ff)
  : UU
  := is_disp_invertible_2cell (left_equivalence_unit_iso _)
       (disp_left_adjoint_unit αe ααd)
   × is_disp_invertible_2cell (left_equivalence_counit_iso _)
   (disp_left_adjoint_counit αe ααd).

Definition disp_left_equivalence
           {x y : C}
           {f : x --> y}
           (Hf : left_equivalence f)
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
  : UU
  := ∑ (d : disp_left_adjoint_data Hf ff),
     disp_left_equivalence_axioms Hf d.


Definition disp_left_adjoint_equivalence
         {a b : C}
         {f : a --> b}
         (αe : left_adjoint_equivalence f)
         {aa : D a} {bb : D b}
         (ff : aa -->[f] bb)
  := ∑ (ααd : disp_left_adjoint_data αe ff),
       disp_left_adjoint_axioms αe ααd
     × disp_left_equivalence_axioms αe ααd.

(* the coercion to the adjoint axioms will be induced *)
Coercion disp_left_adjoint_of_left_adjoint_equivalence
         {a b : C}
         {f : a --> b}
         {αe : left_adjoint_equivalence f}
         {aa : D a} {bb : D b}
         {ff : aa -->[f] bb}
         (ααe : disp_left_adjoint_equivalence αe ff)
  : disp_left_adjoint αe ff := (pr1 ααe,, pr12 ααe).

Coercion axioms_of_left_adjoint_equivalence
         {a b : C}
         {f : a --> b}
         {αe : left_adjoint_equivalence f}
         {aa : D a} {bb : D b}
         {ff : aa -->[f] bb}
         (ααe : disp_left_adjoint_equivalence αe ff)
  : disp_left_equivalence_axioms αe ααe := pr22 ααe.

(** *** Packaged *)
Definition disp_adjunction
           {a b : C}
           (f : adjunction a b)
           (aa : D a) (bb : D b) : UU
  := ∑ ff : aa -->[f] bb, disp_left_adjoint f ff.

Coercion disp_arrow_of_adjunction
         {a b : C}
         {f : adjunction a b}
         {aa : D a} {bb : D b}
         (ff : disp_adjunction f aa bb)
  : aa -->[f] bb
  := pr1 ff.

Coercion disp_left_adjoint_of_adjunction
         {a b : C}
         {f : adjunction a b}
         {aa : D a} {bb : D b}
         (ff : disp_adjunction f aa bb)
  : disp_left_adjoint f ff
  := pr2 ff.

Definition disp_adjoint_equivalence
           {a b : C}
           (f : adjoint_equivalence a b)
           (aa : D a) (bb : D b) : UU
  := ∑ ff : aa -->[f] bb, disp_left_adjoint_equivalence f ff.

Coercion disp_adjunction_of_adjoint_equivalence
         {a b : C}
         {f : adjoint_equivalence a b}
         {aa : D a} {bb : D b}
         (ff : disp_adjoint_equivalence f aa bb)
  : disp_adjunction f aa bb.
Proof.
  refine (pr1 ff,, _).
  apply (disp_left_adjoint_of_left_adjoint_equivalence (pr2 ff)).
Defined.

Coercion disp_left_adjoint_equivalence_of_adjoint_equivalence
         {a b : C}
         {f : adjoint_equivalence a b}
         {aa : D a} {bb : D b}
         (ff : disp_adjoint_equivalence f aa bb)
  : disp_left_adjoint_equivalence f ff
  := pr2 ff.

(* Definition internal_right_adjoint {a b : C} *)
(*            (f : adjunction a b) : C⟦b,a⟧ := *)
(*   left_adjoint_right_adjoint f. *)

End Displayed_Internal_Adjunction.

(** From now on, we need the [has_disp_cellset property]. *)

(** ** Identity is a displayed adjoint *)
(* TODO LOL MOVE THIS TO DISPLAYED UNIVALNCE  *)
Require Import UniMath.Bicategories.Core.Univalence.
Definition disp_internal_adjunction_data_identity
           {C : bicat} {D : disp_bicat C}
           {a : C}
           (aa : D a)
  : disp_left_adjoint_data (internal_adjoint_equivalence_identity a)
                           (id_disp aa).
Proof.
  exists (id_disp _ ).
  split.
  - exact (disp_linvunitor _ ).
  - exact (disp_lunitor _ ).
Defined.

Definition is_disp_internal_adjunction_identity
           {C : bicat} {D : disp_bicat C}
           {a : C} (aa : D a)
  : disp_left_adjoint_axioms
      (internal_adjoint_equivalence_identity a)
      (disp_internal_adjunction_data_identity aa).
Proof.
  split.
  - etrans.
    { apply maponpaths_2.
      etrans; [apply disp_vassocl | ].
      etrans.
      { apply maponpaths. apply maponpaths.
        etrans; [apply disp_lunitor_lwhisker | ].
        apply maponpaths.
        apply maponpaths.
        apply disp_runitor_lunitor_identity. }
      etrans. { apply maponpaths. apply disp_mor_transportf_prewhisker. }
      etrans. { apply (transport_f_f (λ x, _ ==>[x] _)). }
      etrans.
      { etrans.
        { apply maponpaths.
          apply maponpaths.
          apply disp_rwhisker_transport_left_new. }
        cbn.
        etrans.
        { apply maponpaths.
          apply disp_mor_transportf_prewhisker. }
        etrans. { apply (transport_f_f (λ x, _ ==>[x] _)). }
        etrans.
        { apply maponpaths. apply disp_vassocl. }
        etrans. { apply (transport_f_f (λ x, _ ==>[x] _)). }
        etrans.
        { apply maponpaths. apply maponpaths.
          etrans; [apply disp_rwhisker_vcomp | ].
          etrans; [apply maponpaths, maponpaths, disp_linvunitor_lunitor | ].
          etrans.
          { apply maponpaths.
            apply disp_rwhisker_transport_left_new. }
          etrans. { apply (transport_f_f (λ x, _ ==>[x] _)). }
          apply maponpaths. apply disp_id2_rwhisker.
        }
        etrans. { apply maponpaths, disp_mor_transportf_prewhisker. }
        etrans; [ apply (transport_f_f (λ x, _ ==>[x] _)) | ].
        etrans. { apply maponpaths, disp_mor_transportf_prewhisker. }
        etrans; [ apply (transport_f_f (λ x, _ ==>[x] _)) | ].
        apply maponpaths, disp_id2_right. }
      apply (transport_f_f (λ x, _ ==>[x] _)).
    }
    etrans; [ apply disp_mor_transportf_postwhisker | ].
    etrans.
    { apply maponpaths.
      etrans; [ apply maponpaths, disp_runitor_lunitor_identity | ].
      etrans; [ apply disp_mor_transportf_prewhisker | ].
      apply maponpaths. apply disp_linvunitor_lunitor.
    }
    etrans; [ apply (transport_f_f (λ x, _ ==>[x] _)) | ].
    etrans; [ apply (transport_f_f (λ x, _ ==>[x] _)) | ].
    cbn.
    unfold transportb.
    apply maponpaths_2.
    apply cellset_property.
  - etrans.
    { apply maponpaths_2.
      etrans; [apply disp_vassocl | ].
      etrans.
      { apply maponpaths, maponpaths.
        etrans; [ apply maponpaths, maponpaths, disp_lunitor_runitor_identity | ].
        etrans; [ apply maponpaths, disp_rwhisker_transport_left_new | ].
        etrans; [ apply disp_mor_transportf_prewhisker | ].
        apply maponpaths, disp_runitor_rwhisker. }
      etrans; [apply maponpaths, disp_vassocl | ].
      apply maponpaths, maponpaths.
      etrans; [ apply maponpaths, disp_mor_transportf_prewhisker | ].
      etrans; [ apply disp_mor_transportf_prewhisker | ].
      etrans.
      { apply maponpaths, maponpaths.
        etrans; [ apply disp_mor_transportf_prewhisker | ].
        apply maponpaths, disp_lwhisker_vcomp. }
      etrans; [ apply maponpaths, disp_mor_transportf_prewhisker | ].
      etrans; [ apply (transport_f_f (λ x, _ ==>[x] _)) | ].
      apply maponpaths.
      etrans; [ apply disp_mor_transportf_prewhisker | ].
      { apply maponpaths, maponpaths, maponpaths.
        apply disp_linvunitor_lunitor. }
    }
    etrans; [ apply disp_mor_transportf_postwhisker | ].
    etrans; [ apply maponpaths, disp_mor_transportf_postwhisker | ].
    etrans; [ apply (transport_f_f (λ x, _ ==>[x] _)) | ].
    etrans; [ apply maponpaths, disp_mor_transportf_postwhisker | ].
    etrans; [ apply (transport_f_f (λ x, _ ==>[x] _)) | ].
    etrans; [ apply maponpaths, disp_mor_transportf_postwhisker | ].
    etrans; [ apply (transport_f_f (λ x, _ ==>[x] _)) | ].
    etrans.
    { apply maponpaths.
      etrans; [apply disp_vassocl | ].
      apply maponpaths.
      etrans.
      { apply maponpaths.
        etrans.
        { apply maponpaths_2.
          apply disp_rwhisker_transport_right. }
        cbn.
        etrans; [ apply disp_mor_transportf_postwhisker | ].
        etrans; [ apply maponpaths, maponpaths_2, disp_lwhisker_id2 | ].
        etrans; [ apply maponpaths, disp_mor_transportf_postwhisker | ].
        etrans; [ apply (transport_f_f (λ x, _ ==>[x] _)) | ].
        apply maponpaths. apply disp_id2_left.
      }
      etrans; [ apply maponpaths, (transport_f_f (λ x, _ ==>[x] _)) | ].
      etrans; [ apply disp_mor_transportf_prewhisker | ].
      etrans; [ apply maponpaths, maponpaths, disp_lunitor_runitor_identity | ].
      etrans; [ apply maponpaths, disp_mor_transportf_prewhisker | ].
      etrans; [ apply (transport_f_f (λ x, _ ==>[x] _)) | ].
      etrans.
      { apply maponpaths.
        apply disp_rinvunitor_runitor. }
      apply (transport_f_f (λ x, _ ==>[x] _)).
    }
    etrans; [ apply (transport_f_f (λ x, _ ==>[x] _)) | ].
    etrans; [ apply (transport_f_f (λ x, _ ==>[x] _)) | ].
    cbn.
    unfold transportb.
    apply maponpaths_2.
    apply cellset_property.
Qed.

Definition disp_identity_adjoint_equivalence
           {C : bicat} {D : disp_bicat C}
           {a : C} (aa : D a)
  : disp_adjoint_equivalence (internal_adjoint_equivalence_identity a) aa aa.
Proof.
  use tpair.
  - apply disp_internal_adjunction_data_identity.
  - cbn. use tpair.
    + apply disp_internal_adjunction_data_identity.
    + cbn. split.
      { apply is_disp_internal_adjunction_identity. }
      {
        split.
        - use tpair.
          + apply disp_lunitor.
          + split.
            * cbn.
              refine (disp_linvunitor_lunitor (id_disp aa) @ _).
              apply (@transportf_paths _ (λ z, _ ==>[ z ] _)).
              apply C.
            * cbn.
              refine (disp_lunitor_linvunitor (id_disp aa) @ _).
              apply (@transportf_paths _ (λ z, _ ==>[ z ] _)).
              apply C.
        - use tpair.
          + apply disp_linvunitor.
          + split.
            * cbn.
              refine (disp_lunitor_linvunitor (id_disp aa) @ _).
              apply (@transportf_paths _ (λ z, _ ==>[ z ] _)).
              apply C.
            * cbn.
              refine (disp_linvunitor_lunitor (id_disp aa) @ _).
              apply (@transportf_paths _ (λ z, _ ==>[ z ] _)).
              apply C. }
Defined.


(** * Classification of internal adjunctions in the total category *)
Section Total_Internal_Adjunction.

Context {B : bicat} {D : disp_bicat B}.
Local Definition E := total_bicat D.

(** Equivalences for data *)
Local Definition left_adjoint_data_total_to_base
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb} :
  @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff) →
  left_adjoint_data f.
Proof.
  intros f_d.
  set (g' := pr1 f_d).
  set (Hdat := pr2 f_d).
  set (g := pr1 g').
  set (η := pr1 (pr1 Hdat)).
  set (ε := pr1 (pr2 Hdat)).
  exists g.
  exact (η,,ε).
Defined.

Local Definition left_adjoint_data_total_to_fiber
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb} :
  forall (j : @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff)),
  disp_left_adjoint_data (left_adjoint_data_total_to_base j) ff.
Proof.
  intros f_d.
  set (g' := pr1 f_d).
  set (Hdat := pr2 f_d).
  set (gg := pr2 g').
  set (ηη := pr2 (pr1 Hdat)).
  set (εε := pr2 (pr2 Hdat)).
  exists gg. exact (ηη,,εε).
Defined.

Definition left_adjoint_data_total_to_disp
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      (ff : aa -->[f] bb) :
  @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff) →
  ∑ (α : left_adjoint_data f), disp_left_adjoint_data α ff.
Proof.
  intros j.
  exists (left_adjoint_data_total_to_base j).
  apply left_adjoint_data_total_to_fiber.
Defined.

Definition left_adjoint_data_disp_to_total
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      (ff : aa -->[f] bb) :
  (∑ (α : left_adjoint_data f), disp_left_adjoint_data α ff) →
  @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff).
Proof.
  intros j'.
  pose (j := pr1 j').
  pose (jj := pr2 j').
  pose (g := left_adjoint_right_adjoint j).
  pose (gg := (disp_left_adjoint_right_adjoint _ jj : bb -->[g] aa)).
  use tpair.
  - exact (g,, gg).
  - simpl. (* Units/counits *)
    use tpair.
    + (* Units *)
      use tpair; simpl.
      * apply (left_adjoint_unit j).
      * apply (disp_left_adjoint_unit _ jj).
    + (* Counits *)
      use tpair; simpl.
      * apply (left_adjoint_counit j).
      * apply (disp_left_adjoint_counit _ jj).
Defined.

Definition left_adjoint_data_total_weq
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      (ff : aa -->[f] bb) :
  @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff) ≃
  ∑ (α : left_adjoint_data f), disp_left_adjoint_data α ff.
Proof.
  exists (left_adjoint_data_total_to_disp ff).
  use isweq_iso.
  - exact (left_adjoint_data_disp_to_total ff).
  - intros ?. reflexivity.
  - intros ?. reflexivity.
Defined.

(** The equivalence for adjunction laws *)
Definition left_adjoint_axioms_total_to_base
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb}
      {td : @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff)} :
  left_adjoint_axioms td →
  left_adjoint_axioms (left_adjoint_data_total_to_base td).
Proof.
  intros Hlaw.
  use tpair.
  + apply (base_paths _ _ (pr1 Hlaw)).
  + apply (base_paths _ _ (pr2 Hlaw)).
Defined.

Definition left_adjoint_axioms_total_to_fiber
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb}
      (td : @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff))
      (ta : left_adjoint_axioms td) :
  disp_left_adjoint_axioms
    (_,, left_adjoint_axioms_total_to_base ta)
    (left_adjoint_data_total_to_fiber td).
Proof.
  use tpair.
  - apply (transportf_transpose_right (P:=λ x, _ ==>[x] _)).
    etrans; [| apply (fiber_paths (pr1 ta)) ].
    apply (transportf_transpose_right (P:=λ x, _ ==>[x] _)).
    apply (transportfbinv (λ x, _ ==>[x] _)).
  - apply (transportf_transpose_right (P:=λ x, _ ==>[x] _)).
    etrans; [| apply (fiber_paths (pr2 ta)) ].
    apply (transportf_transpose_right (P:=λ x, _ ==>[x] _)).
    apply (transportfbinv (λ x, _ ==>[x] _)).
Qed.

Definition left_adjoint_axioms_total_to_disp
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb}
      (td : @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff))
      (ta : left_adjoint_axioms td) :
  ∑ (ba : left_adjoint_axioms _),
    disp_left_adjoint_axioms
      (_,, ba)
      (left_adjoint_data_total_to_fiber td).
Proof.
  exists (left_adjoint_axioms_total_to_base ta).
  apply left_adjoint_axioms_total_to_fiber.
Defined.

Definition left_adjoint_axioms_disp_to_total
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb}
      (td : @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff)) :
  (∑ (ba : left_adjoint_axioms _),
     disp_left_adjoint_axioms
       (_,, ba)
       (left_adjoint_data_total_to_fiber td))
 → left_adjoint_axioms td.
Proof.
  intros j'.
  pose (j := pr1 j').
  pose (jj := pr2 j').
  simpl; split; use total2_paths_b; (apply j || apply jj).
Qed.

Definition left_adjoint_axioms_total_weq
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb}
      (td : @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff)):
  left_adjoint_axioms td
 ≃
 ∑ (ba : left_adjoint_axioms _),
  disp_left_adjoint_axioms
    (_,, ba)
    (left_adjoint_data_total_to_fiber td).
Proof.
  apply weqimplimpl.
  - exact (left_adjoint_axioms_total_to_disp td).
  - exact (left_adjoint_axioms_disp_to_total td).
  - apply isofhleveltotal2; try intro; apply cellset_property.
  - apply isofhleveltotal2.
    { apply isofhleveltotal2; try intro; apply cellset_property. }
    intros ?.
    apply isofhleveltotal2; try intro; apply disp_cellset_property.
Defined.

(** The equivalence for equivalence laws *)
Definition left_equivalence_axioms_total_to_base
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb}
      {td : @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff)} :
  left_equivalence_axioms td →
  left_equivalence_axioms (left_adjoint_data_total_to_base td).
Proof.
  intros Hlaw.
  pose (Hη := pr1 Hlaw).
  pose (Hε := pr2 Hlaw).
  use tpair.
  + apply (is_invertible_total_to_base _ _ Hη).
  + apply (is_invertible_total_to_base _ _ Hε).
Defined.

Definition left_equivalence_axioms_total_to_fiber
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb}
      (td : @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff))
      (ta : left_equivalence_axioms td) :
  disp_left_equivalence_axioms
    (left_adjoint_data_total_to_base td,,
     left_equivalence_axioms_total_to_base ta)
    (left_adjoint_data_total_to_fiber td).
Proof.
  pose (Hη := pr1 ta).
  pose (Hε := pr2 ta).
  cbn in Hη,Hε.
  use tpair.
  - apply (is_invertible_total_to_fiber _ _ Hη).
  - apply (is_invertible_total_to_fiber _ _ Hε).
Qed.

Definition left_equivalence_axioms_total_to_disp
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb}
      (td : @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff))
      (ta : left_equivalence_axioms td) :
  ∑ (ba : left_equivalence_axioms _),
    disp_left_equivalence_axioms
      (_,, ba)
      (left_adjoint_data_total_to_fiber td).
Proof.
  exists (left_equivalence_axioms_total_to_base ta).
  apply left_equivalence_axioms_total_to_fiber.
Defined.

Definition left_equivalence_axioms_disp_to_total
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb}
      (td : @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff)) :
  (∑ (ba : left_equivalence_axioms _),
     disp_left_equivalence_axioms
       (_,, ba)
       (left_adjoint_data_total_to_fiber td))
 → left_equivalence_axioms td.
Proof.
  intros αe.
  pose (ba := pr1 αe).
  pose (ta := pr2 αe).
  cbn in ba, ta.
  split.
  - apply is_invertible_disp_to_total.
    use tpair.
    + apply ba.
    + apply ta.
  - apply is_invertible_disp_to_total.
    use tpair.
    + apply ba.
    + apply ta.
Qed.

Definition left_equivalence_axioms_total_weq
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb}
      (td : @left_adjoint_data E (a,,aa) (b,,bb) (f,,ff)):
  left_equivalence_axioms td
 ≃
 ∑ (ba : left_equivalence_axioms _),
  disp_left_equivalence_axioms
    (_,, ba)
    (left_adjoint_data_total_to_fiber td).
Proof.
  apply weqimplimpl.
  - exact (left_equivalence_axioms_total_to_disp td).
  - exact (left_equivalence_axioms_disp_to_total td).
  - apply isapropdirprod; apply isaprop_is_invertible_2cell.
  - apply isofhleveltotal2.
    { apply isapropdirprod; apply isaprop_is_invertible_2cell. }
    intros ?.
    apply isapropdirprod; apply isaprop_is_disp_invertible_2cell.
Defined.

(***************************************************)
(***************************************************)
(***************************************************)

Lemma adjunction_total_disp_weq
      {a b : B}
      (aa : D a) (bb : D b) :
  @adjunction E (a,,aa) (b,,bb)
≃ ∑ (f : adjunction a b), disp_adjunction f aa bb.
Proof.
  unfold adjunction. cbn.
  (* First we get out the base left adjoint f *)
  eapply weqcomp. {
    apply weqinvweq.
    apply weqtotal2asstol. }
  eapply weqcomp. 2: {
    apply weqtotal2asstol. }
  eapply weqfibtototal. intros f.

  (* Getting rid of the displayed arrow ff *)
  unfold disp_adjunction. cbn.
  eapply weqcomp. 2: {
    apply weqtotal2comm. }
  eapply weqfibtototal. intros ff.

  unfold left_adjoint.

  (* Apply the equivalence for data & laws *)
  eapply weqcomp. {
    pose (Q:=λ (w : (∑ αd, disp_left_adjoint_data αd ff)),
                    (∑ l, disp_left_adjoint_axioms (pr1 w,,l) (pr2 w))).
    eapply (weqbandf (left_adjoint_data_total_weq ff) _ Q).
    intros td. unfold Q; cbn.
    apply left_adjoint_axioms_total_weq. }
  cbn.

  (* Move the quantifiers around *)
  eapply weqcomp. {
    apply weqinvweq.
    apply weqtotal2asstol. }
  cbn.
  eapply weqcomp. 2: {
    apply weqtotal2asstol. }
  cbn.
  eapply weqfibtototal. intros αd.
  eapply weqcomp. {
    apply weqtotal2comm. }
  cbn.
  apply idweq.
Defined.

Lemma left_adjoint_equivalence_total_disp_weq
      {a b : B}
      {aa : D a} {bb : D b}
      (f : a --> b)
      (ff : aa -->[f] bb) :
  @left_adjoint_equivalence E (a,,aa) (b,,bb) (f,,ff)
≃ ∑ (αe : left_adjoint_equivalence f),
  disp_left_adjoint_equivalence αe ff.
Proof.
  (* Factor this out *)
  (* left adjoint equivalences part *)
  unfold left_adjoint_equivalence.
  cbn.
  (* Apply the equivalence for data & laws *)
  eapply weqcomp. {
    pose (Q:=
      λ (w : (∑ αd, disp_left_adjoint_data αd ff)),
        (∑ l, disp_left_adjoint_axioms (pr1 w,,l) (pr2 w))
      × (∑ l, disp_left_equivalence_axioms (pr1 w,,l) (pr2 w))).
    eapply (weqbandf (left_adjoint_data_total_weq ff) _ Q).
    intros td. unfold Q; cbn.
    apply weqdirprodf.
    - apply left_adjoint_axioms_total_weq.
    - apply left_equivalence_axioms_total_weq. }
  cbn.
  (* TIME TO REARANGE THE QUANTIFIERS OwO *)
  cbn.
  (* Getting rid of the left adjoint data for the base *)
  eapply weqcomp. {
    apply weqinvweq.
    apply weqtotal2asstol. }
  cbn.
  eapply weqcomp. 2: {
    apply weqtotal2asstol. }
  cbn.
  eapply weqfibtototal. intros αd.

  (* Getting rid of the displayed left adjoint data *)
  unfold disp_left_adjoint_equivalence.
  cbn.
  eapply weqcomp. 2: {
    apply weqtotal2comm. }
  cbn.
  eapply weqfibtototal. intros ααd.
  cbn.

  (* now to distribute the ∑s *)
  eapply weqcomp. 2: {
    apply weqtotal2asstol. }
  cbn.
  eapply weqcomp. {
    apply weqinvweq.
    apply weqtotal2asstol. }
  cbn.
  eapply weqfibtototal. intros αa.
  cbn.
  eapply weqcomp. {
    apply weqtotal2comm. }
  apply idweq.
Defined.

Lemma adjoint_equivalence_total_disp_weq
      {a b : B}
      (aa : D a) (bb : D b) :
  @adjoint_equivalence E (a,,aa) (b,,bb)
≃ ∑ (f : adjoint_equivalence a b), disp_adjoint_equivalence f aa bb.
Proof.
  unfold adjoint_equivalence, disp_adjoint_equivalence. cbn.
  (* First we get out the base left adjoint f *)
  eapply weqcomp. {
    apply weqinvweq.
    apply weqtotal2asstol. }
  eapply weqcomp. 2: {
    apply weqtotal2asstol. }
  eapply weqfibtototal. intros f.

  (* Getting rid of the displayed arrow ff *)
  cbn.
  eapply weqcomp. 2: {
    apply weqtotal2comm. }
  eapply weqfibtototal. intros ff.

  apply left_adjoint_equivalence_total_disp_weq.
Defined.


(* TODO. DF: MOVE TO A SANER PLACE, merge with transportf_subtypePath' *)
(* Definition transportf_subtypePath'_QUALITY *)
(*            {A : UU} *)
(*            {P : A → UU} *)
(*            (Pprop : ∏ (a : A), isaprop (P a)) *)
(*            {C : total2 P → UU} *)
(*            (x : A) (P₁ P₂ : P x) *)
(*            (y : C (x,,P₁)) : *)
(*   transportf (λ (z : total2 P), C z) *)
(*              (@subtypePath' _ _ (x,,P₁) (x,,P₂) (idpath x) (Pprop x)) *)
(*              y *)
(*   = transportf (λ (p : P x), C (x,, p)) (pr1 (Pprop x P₁ P₂)) y. *)
(* Proof. *)
(*   cbn. *)
(*   induction (Pprop x P₁ P₂) as [p q]. *)
(*   induction p. *)
(*   reflexivity. *)
(* Defined. *)

End Total_Internal_Adjunction.

Definition disp_left_equivalence_to_total
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f : x --> y}
           {Hf : left_equivalence f}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           (Hff : disp_left_equivalence Hf ff)
  : @left_equivalence (total_bicat D) (x ,, xx) (y ,, yy) (f ,, ff).
Proof.
  simple refine (_ ,, _).
  - exact (left_adjoint_data_disp_to_total ff (pr1 Hf ,, pr1 Hff)).
  - use (left_equivalence_axioms_disp_to_total _ (_ ,, _)).
    + exact (pr2 Hf).
    + exact (pr2 Hff).
Defined.

Definition disp_left_equivalence_to_left_adjoint_equivalence
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f : x --> y}
           {Hf : left_equivalence f}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           (Hff : disp_left_equivalence Hf ff)
  : ∑ (Hf' : left_adjoint_equivalence f),
    disp_left_adjoint_equivalence Hf' ff
  := left_adjoint_equivalence_total_disp_weq
       f ff
       (pr2 (equiv_to_adjequiv _ (disp_left_equivalence_to_total Hff))).
