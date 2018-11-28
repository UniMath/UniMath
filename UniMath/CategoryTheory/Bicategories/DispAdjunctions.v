(* *********************************************************************************** *)
(** * Internal adjunction in displayed bicategories

    Benedikt Ahrens, Marco Maggesi, Niels van der Weide, Dan Frumin
    April 2018                                                                         *)
(* *********************************************************************************** *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.

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
           (ααd : disp_left_adjoint_data j ff) : UU
  := let gg := disp_left_adjoint_right_adjoint j ααd in
     let ηη := disp_left_adjoint_unit j ααd in
     let εε := disp_left_adjoint_counit j ααd in
( disp_linvunitor ff •• (ηη ▹▹ ff) •• disp_rassociator _ _ _ ••
         (ff ◃◃ εε) •• disp_runitor ff =
         transportb (λ x, _ ==>[x] _) (internal_triangle1 j) (disp_id2 ff) )
     × ( disp_rinvunitor gg •• (gg ◃◃ ηη) •• disp_lassociator _ _ _ ••
         (εε ▹▹ gg) •• disp_lunitor gg =
         transportb (λ x, _ ==>[x] _) (internal_triangle2 j) (disp_id2 gg) ).

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
         (αe : left_adjoint_equivalence f)
         {aa : D a} {bb : D b}
         {ff : aa -->[f] bb}
         (ααd : disp_left_adjoint_data αe ff)
  : UU
  := is_disp_invertible_2cell (left_adjoint_equivalence_unit_iso _)
       (disp_left_adjoint_unit αe ααd)
   × is_disp_invertible_2cell (left_adjoint_equivalence_counit_iso _)
       (disp_left_adjoint_counit αe ααd).

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
Require Import UniMath.CategoryTheory.Bicategories.Univalence.
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

(** A left adjoint in the total category gives a left adjoint in the base .. *)
Local Definition left_adjoint_total_to_base
      {a b : B}
      {aa : D a} {bb : D b}
      {f : a --> b}
      {ff : aa -->[f] bb} :
  @left_adjoint E (a,,aa) (b,,bb) (f,,ff) →
  left_adjoint f.
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
  forall (j : @left_adjoint E (a,,aa) (b,,bb) (f,,ff)),
  disp_left_adjoint (left_adjoint_total_to_base j) ff.
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
  @left_adjoint E (a,,aa) (b,,bb) (f,,ff) →
  ∑ (α : left_adjoint f), disp_left_adjoint α ff.
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
  (∑ (α : left_adjoint f), disp_left_adjoint α ff) →
  @left_adjoint E (a,,aa) (b,,bb) (f,,ff).
Proof.
  intros j'.
  pose (j := pr1 j').
  pose (jj := pr2 j').
  pose (g := left_adjoint_right_adjoint j).
  pose (gg := (disp_left_adjoint_right_adjoint _ jj : bb -->[g] aa)).
  use tpair.
  - (* Data for the total adjunction *)
    use tpair.
    + exact (g,, gg).
    + simpl. (* Units/counits *)
      use tpair.
      * (* Units *)
        use tpair; simpl.
        apply (left_adjoint_unit j).
        apply (disp_left_adjoint_unit _ jj).
      * (* Counits *)
        use tpair; simpl.
        apply (left_adjoint_counit j).
        apply (disp_left_adjoint_counit _ jj).
  - abstract (simpl; split; use total2_paths_b; (apply j || apply jj)).
Defined.

Lemma left_adjoint_disp_total_eq
      {a b : B}
      (aa : D a) (bb : D b)
      (f : a --> b)
      (ff : aa -->[f] bb)
      (jj : @left_adjoint E (a,,aa) (b,,bb) (f,,ff)) :
  left_adjoint_disp_to_total ff (left_adjoint_total_to_disp ff jj) = jj.
Proof.
  use total2_paths_f.
  - reflexivity.
  - use total2_paths_f; apply cellset_property.
Defined.

(* TODO. DF: MOVE TO A SANER PLACE, merge with transportf_subtypeEquality' *)
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
      (jj : ∑ α : left_adjoint f,
           disp_left_adjoint α ff) :
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
                       (left_adjoint f)
                       (λ x, disp_left_adjoint_data x ff)).
      destruct jj as [j jj].
      destruct jj as [jjd jjl].
      destruct j as [jd jl].
      etrans. {
        pose (QQ := @transportf_subtypeEquality'_QUALITY).
        specialize (QQ (left_adjoint_data f)).
        specialize (QQ left_adjoint_axioms).
        specialize (QQ (left_adjoint_total_disp_eq_subproof _ _ f)).
        specialize (QQ (λ x, disp_left_adjoint_data
                               (data_of_left_adjoint x) ff)).
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
  @left_adjoint E (a,,aa) (b,,bb) (f,,ff)
≃ ∑ (α : left_adjoint f), disp_left_adjoint α ff.
Proof.
  exists (left_adjoint_total_to_disp ff).
  use gradth.
  - exact (left_adjoint_disp_to_total ff).
  - intros ?. apply left_adjoint_disp_total_eq.
  - intros ?. apply left_adjoint_total_disp_eq.
Defined.

(* (** Inverse of [internal_adjunction_from_left_adjoint] *)
(*    This has nothing to do with displayed categories and should be *)
(*    moved to the file with internal adjunctions. *)
(* TODO! *)
(* *) *)
(* Definition left_adjoint_from_internal_adjunction {C : bicat} *)
(*     {x y : C} : *)
(*   internal_adjunction x y → *)
(*   ∑ (f : C⟦x,y⟧), is_internal_left_adjoint f. *)
(* Proof. *)
(*   unfold internal_adjunction. cbn. *)
(*   induction 1 as [j Hj]. *)
(*   induction j as [f Hf]. *)
(*   induction Hf as [g Hfg]. *)
(*   exists f. *)
(*   unfold is_internal_left_adjoint. *)
(*   use tpair. *)
(*   - exists g. apply Hfg. *)
(*   - apply Hj. *)
(* Defined. *)

(* Lemma left_adjoint_from_internal_adjunction_weq {C : bicat} *)
(*     {x y : C} : *)
(*   internal_adjunction x y ≃ *)
(*   ∑ (f : C⟦x,y⟧), is_internal_left_adjoint f. *)
(* Proof. *)
(*   exists left_adjoint_from_internal_adjunction. *)
(*   use gradth. *)
(*   - exact (λ x, internal_adjunction_from_left_adjoint (pr2 x)). *)
(*   - reflexivity. *)
(*   - reflexivity. *)
(* Defined. *)

(* (** Conversion between displayed left adjoints and displayed adjunctions *)
(* TODO! *)
(* *) *)
(* Definition disp_left_adjoint_from_internal_adjunction *)
(*          {a b : B} *)
(*          {f : a --> b} *)
(*          (j : is_internal_left_adjoint f) *)
(*          {aa : D a} {bb : D b} *)
(*   : disp_internal_adjunction j aa bb → *)
(*     ∑ (ff : aa -->[f] bb), is_disp_internal_left_adjoint j ff. *)
(* Proof. *)
(*   induction 1 as [jj Hjj]. *)
(*   induction jj as [ff Hff]. *)
(*   exists ff. *)
(*   use tpair. apply Hff. *)
(*   apply Hjj. *)
(* Defined. *)

(* Definition disp_left_adjoint_from_internal_adjunction_weq *)
(*          {a b : B} *)
(*          {f : a --> b} *)
(*          (j : is_internal_left_adjoint f) *)
(*          {aa : D a} {bb : D b} *)
(*   : disp_internal_adjunction j aa bb ≃ *)
(*     ∑ (ff : aa -->[f] bb), is_disp_internal_left_adjoint j ff. *)
(* Proof. *)
(*   exists (disp_left_adjoint_from_internal_adjunction j). *)
(*   use gradth. *)
(*   - refine (λ x,disp_internal_adjunction_from_left_adjoint j (pr1 x) (pr2 x)). *)
(*   - reflexivity. *)
(*   - reflexivity. *)
(* Defined. *)

End Total_Internal_Adjunction.
