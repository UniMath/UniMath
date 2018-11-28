(* *********************************************************************************** *)
(** * Internal adjunction in displayed bicategories

    Benedikt Ahrens, Marco Maggesi
    April 2018                                                                         *)
(* *********************************************************************************** *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.
(* Internal adjunctions are definied in this file:  *)
Require Import UniMath.CategoryTheory.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(** * Definitions and properties of displayed adjunctions *)
Section Displayed_Internal_Adjunction.

Context {C : bicat} {D : disp_prebicat C}.

Definition disp_internal_adjunction_over {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
           (j : internal_adjunction_over f g)
           {aa : D a} {bb : D b}
           (ff : aa -->[f] bb) (gg : bb -->[g] aa)
  : UU
  := let (η,ε) := j in
       (id_disp aa ==>[η] ff ;; gg)
     × (gg ;; ff ==>[ε] id_disp bb).

Definition disp_internal_adjunction_data {a b : C} (j : internal_adjunction_data a b)
           (aa : D a) (bb : D b)
           (f := internal_left_adjoint j)
           (g := internal_right_adjoint j)
  : UU
  := ∑ (ff : aa -->[f] bb) (gg : bb -->[g] aa), disp_internal_adjunction_over j ff gg.

Definition disp_internal_left_adjoint {a b : C} {j : internal_adjunction_data a b}
           {aa : D a} {bb : D b}
           (jj : disp_internal_adjunction_data j aa bb)
  : aa -->[internal_left_adjoint j] bb
  := pr1 jj.

Definition disp_internal_right_adjoint {a b : C} {j : internal_adjunction_data a b}
           {aa : D a} {bb : D b}
           (jj : disp_internal_adjunction_data j aa bb)
  : bb -->[internal_right_adjoint j] aa
  := pr1 (pr2 jj).

Coercion disp_internal_adjunction_over_from_data
         {a b : C} {j : internal_adjunction_data a b}
         {aa : D a} {bb : D b}
         (jj : disp_internal_adjunction_data j aa bb)
  : disp_internal_adjunction_over
      j (disp_internal_left_adjoint jj) (disp_internal_right_adjoint jj)
  := pr2 (pr2 jj).

Definition disp_internal_unit
           {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
           {j : internal_adjunction_over f g}
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb} {gg : bb -->[g] aa}
           (jj : disp_internal_adjunction_over j ff gg)
  : id_disp aa ==>[internal_unit j] (ff ;; gg)
  := pr1 jj.

Definition disp_internal_counit
           {a b : C} {f : C⟦a,b⟧} {g : C⟦b,a⟧}
           {j : internal_adjunction_over f g}
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb} {gg : bb -->[g] aa}
           (jj : disp_internal_adjunction_over j ff gg)
  : (gg ;; ff) ==>[internal_counit j] id_disp bb
  := pr2 jj.

Definition is_disp_internal_adjunction {a b : C}
           (j : internal_adjunction a b)
           (f := internal_left_adjoint j)
           (g := internal_right_adjoint j)
           {aa : D a} {bb : D b}
           {ff : aa -->[f] bb}
           {gg : bb -->[g] aa}
           (jj : disp_internal_adjunction_over j ff gg)
           (ηη := disp_internal_unit jj)
           (εε := disp_internal_counit jj)
  : UU
  :=   ( disp_linvunitor ff •• (ηη ▹▹ ff) •• disp_rassociator _ _ _ ••
         (ff ◃◃ εε) •• disp_runitor ff =
         transportb (λ x, _ ==>[x] _) (internal_triangle1 j) (disp_id2 ff) )
     × ( disp_rinvunitor gg •• (gg ◃◃ ηη) •• disp_lassociator _ _ _ ••
         (εε ▹▹ gg) •• disp_lunitor gg =
         transportb (λ x, _ ==>[x] _) (internal_triangle2 j) (disp_id2 gg) ).

Definition disp_internal_adjunction {a b : C}
           (j : internal_adjunction a b)
           (aa : D a) (bb : D b) : UU
  := ∑ (jj : disp_internal_adjunction_data j aa bb),
     is_disp_internal_adjunction j jj.

Coercion disp_internal_adjunction_data_from_internal_adjunction {a b : C}
           {j : internal_adjunction a b}
           {aa : D a} {bb : D b}
           (jj : disp_internal_adjunction j aa bb)
 : disp_internal_adjunction_data j aa bb := pr1 jj.

(** ** Displayed left adjoints *)
Definition disp_internal_left_adjoint_data {a b : C}
           {f : a --> b}
           (j : internal_left_adjoint_data f)
           {aa : D a} {bb : D b}
           (g := internal_right_adjoint j)
           (ff : aa -->[f] bb)
  : UU
  := ∑ (gg : bb -->[g] aa), disp_internal_adjunction_over j ff gg.


Coercion disp_internal_adjunction_over_from_left_adjoint
         {a b : C}
         {f : a --> b}
         {j : internal_left_adjoint_data f}
         {aa : D a} {bb : D b}
         {ff : aa -->[f] bb}
         (jj : disp_internal_left_adjoint_data j ff) :
  disp_internal_adjunction_over j ff (pr1 jj) := pr2 jj.

Definition is_disp_internal_left_adjoint
         {a b : C}
         {f : a --> b}
         (j : is_internal_left_adjoint f)
         {aa : D a} {bb : D b}
         (ff : aa -->[f] bb)
  : UU
  := ∑ (jj : disp_internal_left_adjoint_data j ff),
     is_disp_internal_adjunction j jj.

Coercion disp_internal_adjunction_from_left_adjoint
         {a b : C}
         {f : a --> b}
         (j : is_internal_left_adjoint f)
         {aa : D a} {bb : D b}
         (ff : aa -->[f] bb)
         (jj : is_disp_internal_left_adjoint j ff)
  : disp_internal_adjunction j aa bb.
Proof.
  simple refine (_ ,, _).
  - simple refine (ff,, _,, _); apply (pr1 jj).
  - apply jj.
Defined.

(** ** Displayed internal equivalences *)
Definition form_disp_internal_equivalence {a b : C}
           {j : internal_equivalence a b}
           (f := internal_left_adjoint j)
           (g := internal_right_adjoint j)
           {aa: D a} {bb : D b}
           {ff : aa -->[f] bb}
           {gg : bb -->[g] aa}
           (η := internal_unit_iso j)
           (ε := internal_counit_iso j)
           (ηη : id_disp aa ==>[η] (ff ;; gg))
           (εε : (gg ;; ff) ==>[ε] id_disp bb)
  : UU
  := is_disp_invertible_2cell η ηη × is_disp_invertible_2cell ε εε.

Definition is_disp_internal_equivalence
           {a b : C}
           {j : internal_equivalence a b}
           {aa: D a} {bb : D b}
           (jj: disp_internal_adjunction_data j aa bb)
  : UU
  := form_disp_internal_equivalence (disp_internal_unit jj) (disp_internal_counit jj).

Definition disp_internal_equivalence
           {a b : C}
           (j : internal_equivalence a b)
           (aa: D a) (bb : D b)
  : UU
  := ∑ jj : disp_internal_adjunction_data j aa bb, is_disp_internal_equivalence jj.

Definition disp_internal_adjoint_equivalence
           {a b : C}
           (j : internal_adjoint_equivalence a b)
           (aa: D a) (bb : D b)
  : UU
  := ∑ jj : disp_internal_adjunction_data j aa bb,
            is_disp_internal_equivalence
               (j := internal_equivalence_from_internal_adjoint_equivalence j) jj
         ×  is_disp_internal_adjunction
               (internal_adjunction_from_internal_adjoint_equivalence j) jj.

(** ** Identity is a displayed adjoint *)
Definition disp_internal_adjunction_data_identity {a : C} (aa : D a)
  : disp_internal_adjunction_data (internal_adjunction_identity a) aa aa.
Proof.
  exists (id_disp _ ).
  exists (id_disp _ ).
  exists (disp_linvunitor _ ).
  apply (disp_lunitor _ ).
Defined.


End Displayed_Internal_Adjunction.

(** From now on, we need the [has_disp_cellset property]. *)

Definition is_disp_internal_adjunction_identity
           {C : bicat} {D : disp_bicat C}
           {a : C} (aa : D a)
  : is_disp_internal_adjunction _ (disp_internal_adjunction_data_identity aa).
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
        apply maponpaths. apply disp_vassocl.
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

(** * Classification of internal adjunctions in the total category *)
Section Total_Internal_Adjunction.

Context {B : bicat} {D : disp_bicat B}.
Local Definition E := total_bicat D.

(** A left adjoint in the total category gives a left adjoint in the base .. *)
Local Definition left_adjoint_total_to_base
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb} :
  @is_internal_left_adjoint E (a,,aa) (b,,bb) (f,,ff) →
  is_internal_left_adjoint f.
Proof.
  intros f_d.
  set (Hlaw := pr2 f_d).
  set (g' := pr1 (pr1 f_d)).
  set (Hdat := pr2 (pr1 f_d)).
  set (g := pr1 g').
  set (η := pr1 (pr1 Hdat)).
  set (ε := pr1 (pr2 Hdat)).
  use tpair.
  - (* Data for the adjunction in the base *)
    exists g.
    exact (η,,ε).
  - (* Laws for the adjunction in the base *)
    use tpair.
    + apply (base_paths _ _ (pr1 Hlaw)).
    + apply (base_paths _ _ (pr2 Hlaw)).
Defined.

(** .. and a displayed left adjoint over that. *)
Local Definition left_adjoint_total_to_fiber
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb} :
  forall (j : @is_internal_left_adjoint E (a,,aa) (b,,bb) (f,,ff)),
  is_disp_internal_left_adjoint (left_adjoint_total_to_base j) ff.
Proof.
  intros f_d.
  set (Hlaw := pr2 f_d).
  set (g' := pr1 (pr1 f_d)).
  set (Hdat := pr2 (pr1 f_d)).
  set (gg := pr2 g').
  set (ηη := pr2 (pr1 Hdat)).
  set (εε := pr2 (pr2 Hdat)).
  use tpair.
  - (* Data for the displayed adjunction *)
    exists gg. exact (ηη,,εε).
  - (* Laws for the displayed adjunction *)
    abstract (use tpair;
    [ apply (transportf_transpose (P:=λ x, _ ==>[x] _));
      etrans; [| apply (fiber_paths (pr1 Hlaw)) ];
      apply (transportf_transpose (P:=λ x, _ ==>[x] _));
      apply (transportfbinv (λ x, _ ==>[x] _))
    | apply (transportf_transpose (P:=λ x, _ ==>[x] _));
      etrans; [| apply (fiber_paths (pr2 Hlaw)) ];
      apply (transportf_transpose (P:=λ x, _ ==>[x] _));
      apply (transportfbinv (λ x, _ ==>[x] _)) ]).
Defined.

Definition left_adjoint_total_to_disp
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      (ff : aa -->[f] bb) :
  @is_internal_left_adjoint E (a,,aa) (b,,bb) (f,,ff) →
  ∑ (α : is_internal_left_adjoint f), is_disp_internal_left_adjoint α ff.
Proof.
  intros j.
  exists (left_adjoint_total_to_base j).
  apply left_adjoint_total_to_fiber.
Defined.

(** Given a displayed left adjoint we construct a left adjoint in the total category *)
Definition left_adjoint_disp_to_total
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      (ff : aa -->[f] bb) :
  (∑ (α : is_internal_left_adjoint f), is_disp_internal_left_adjoint α ff) →
  @is_internal_left_adjoint E (a,,aa) (b,,bb) (f,,ff).
Proof.
  intros j'.
  pose (j := pr1 j').
  pose (jj := pr2 j').
  pose (g := internal_right_adjoint j).
  pose (gg := (disp_internal_right_adjoint jj : bb -->[g] aa)).
  use tpair.
  - (* Data for the total adjunction *)
    use tpair.
    + exact (g,, gg).
    + simpl. (* Units/counits *)
      use tpair.
      * (* Units *)
        use tpair; simpl.
        apply (internal_unit j).
        apply (disp_internal_unit jj).
      * (* Counits *)
        use tpair; simpl.
        apply (internal_counit j).
        apply (disp_internal_counit jj).
  - abstract (simpl; split; use total2_paths_b; (apply j || apply jj)).
Defined.

Lemma left_adjoint_disp_total_eq
      {a b : B}
      (aa : D a) (bb : D b)
      (f : a --> b)
      (ff : aa -->[f] bb)
      (jj : @is_internal_left_adjoint E (a,,aa) (b,,bb) (f,,ff)) :
  left_adjoint_disp_to_total ff (left_adjoint_total_to_disp ff jj) = jj.
Proof.
  use total2_paths_f.
  - reflexivity.
  - use total2_paths_f; apply cellset_property.
Defined.

(* TODO MOVE TO A SANER PLACE, merge with transportf_subtypeEquality' *)
Definition transportf_subtypeEquality'_QUALITY
           {A : UU}
           {P : A → UU}
           (Pprop : ∏ (a : A), isaprop (P a))
           {C : total2 P → UU}
           (x : A) (P₁ P₂ : P x)
           (y : C (x,,P₁)) :
  transportf (λ (z : total2 P), C z)
             (@subtypeEquality' _ _ (x,,P₁) (x,,P₂) (idpath x) (Pprop x))
             y
  = transportf (λ (p : P x), C (x,, p)) (pr1 (Pprop x P₁ P₂)) y.
Proof.
  cbn.
  induction (Pprop x P₁ P₂) as [p q].
  induction p.
  reflexivity.
Defined.

Lemma left_adjoint_total_disp_eq
      {a b : B}
      (aa : D a) (bb : D b)
      (f : a --> b)
      (ff : aa -->[f] bb)
      (jj : ∑ α : is_internal_left_adjoint f,
           is_disp_internal_left_adjoint α ff) :
  left_adjoint_total_to_disp ff (left_adjoint_disp_to_total ff jj) = jj.
Proof.
  use total2_paths_f.
  - apply subtypeEquality'.
    + reflexivity.
    + induction jj as [j jj]. cbn-[isaprop].
      induction j as [jd jl]. cbn[pr1].
      (** The reason we are destructing `j` here is because we want to obtain an abstract subproof
        that only depends on the `jd : internal_left_adjoint_data f`.
        This sublemma will later be used for transportf_subtypeEquality' *)
      abstract (apply isofhleveltotal2; try intro; apply cellset_property).
  - use total2_paths_f.
    + etrans. apply (pr1_transportf
                       (is_internal_left_adjoint f)
                       (λ x, disp_internal_left_adjoint_data x ff)).
      destruct jj as [j jj].
      destruct jj as [jjd jjl].
      destruct j as [jd jl].
      etrans. {
        pose (QQ := @transportf_subtypeEquality'_QUALITY).
        specialize (QQ (internal_left_adjoint_data f)).
        specialize (QQ (λ j, is_internal_adjunction j)).
        specialize (QQ (left_adjoint_total_disp_eq_subproof _ _ f)).
        specialize (QQ (λ x, disp_internal_left_adjoint_data
                               (is_internal_left_adjoint_internal_left_adjoint_data x) ff)).
        apply QQ. }
      cbn.
      apply (toforallpaths _ _ _ (transportf_const _ _)).
    + use total2_paths_f; apply disp_cellset_property.
Qed.

Lemma left_adjoint_total_disp_left_adjoint
      {a b : B}
      (aa : D a) (bb : D b)
      (f : a --> b)
      (ff : aa -->[f] bb) :
  @is_internal_left_adjoint E (a,,aa) (b,,bb) (f,,ff)
≃ ∑ (α : is_internal_left_adjoint f), is_disp_internal_left_adjoint α ff.
Proof.
  exists (left_adjoint_total_to_disp ff).
  use gradth.
  - exact (left_adjoint_disp_to_total ff).
  - intros ?. apply left_adjoint_disp_total_eq.
  - intros ?. apply left_adjoint_total_disp_eq.
Defined.

End Total_Internal_Adjunction.
