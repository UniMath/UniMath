Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.DispUnivalence.

Local Open Scope bicategory_scope.
Local Open Scope cat.

Section internal_adjoint_equivalences.

Context {B : bicat} {D : disp_bicat B}.
Local Definition E := total_bicat D.

Definition disp_internal_left_adjoint_data {a b : B}
           {f : a --> b}
           (j : internal_left_adjoint_data f)
           {aa : D a} {bb : D b}
           (g := internal_right_adjoint j)
           (ff : aa -->[f] bb)
  : UU
  := ∑ (gg : bb -->[g] aa), disp_internal_adjunction_over j ff gg.


Coercion disp_internal_adjunction_over_from_left_adjoint
         {a b : B}
         {f : a --> b}
         {j : internal_left_adjoint_data f}
         {aa : D a} {bb : D b}
         {ff : aa -->[f] bb}
         (jj : disp_internal_left_adjoint_data j ff) :
  disp_internal_adjunction_over j ff (pr1 jj) := pr2 jj.

Definition is_disp_internal_left_adjoint
         {a b : B}
         {f : a --> b}
         (j : is_internal_left_adjoint f)
         {aa : D a} {bb : D b}
         (ff : aa -->[f] bb)
  : UU
  := ∑ (jj : disp_internal_left_adjoint_data j ff),
     is_disp_internal_adjunction j jj.

Coercion disp_internal_adjunction_from_left_adjoint
         {a b : B}
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

(* TODO MOVE TO A SANER PLACE *)
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
      (* The reason we are destructing `j` here is because we want to obtain an abstract subproof
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

End internal_adjoint_equivalences.
