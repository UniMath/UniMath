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
Require Import UniMath.CategoryTheory.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section Displayed_Local_Univalence.
  Context {C : bicat}.
  Variable (D : disp_prebicat C).

  Definition disp_id2_invertible_2cell
             {a b : C}
             {f : C⟦a, b⟧}
             {aa : D a} {bb : D b}
             (ff : aa -->[ f ] bb)
    : disp_invertible_2cell (id2_invertible_2cell f) ff ff.
  Proof.
    use tpair.
    - exact (disp_id2 ff).
    - use tpair.
      + cbn.
        exact (disp_id2 ff).
      + split ; cbn.
        * exact (disp_id2_left (disp_id2 ff)).
        * exact (disp_id2_left (disp_id2 ff)).
  Defined.

  Definition disp_idtoiso_2_1
             {a b : C}
             {f g : C⟦a, b⟧}
             (p : f = g)
             {aa : D a} {bb : D b}
             (ff : aa -->[ f ] bb)
             (gg : aa -->[ g ] bb)
             (pp : transportf (λ z, _ -->[ z ] _) p ff = gg)
    : disp_invertible_2cell (idtoiso_2_1 f g p) ff gg.
  Proof.
    induction p.
    induction pp.
    exact (disp_id2_invertible_2cell ff).
  Defined.

  Definition disp_locally_univalent
    : UU
    := ∏ (a b : C) (f g : C⟦a,b⟧) (p : f = g) (aa : D a) (bb : D b)
         (ff : aa -->[ f ] bb) (gg : aa -->[ g ] bb),
       isweq (disp_idtoiso_2_1 p ff gg).
End Displayed_Local_Univalence.

Definition transportf_subtypeEquality'
           {A : UU}
           {B : A → UU}
           (Bprop : ∏ (a : A), isaprop (B a))
           {C : A → UU}
           {a : A}
           (b₁ : B a) (b₂ : B a)
           (x : C a)
  : transportf (λ (z : ∑ (x : A), B x), C (pr1 z))
               (@subtypeEquality' A B (a ,, b₁) (a ,, b₂) (idpath _) (Bprop _))
               x
    =
    x.
Proof.
  cbn.
  induction (Bprop a b₁ b₂) as [p q].
  induction p.
  cbn.
  reflexivity.
Defined.

Definition transportf_cell_from_invertible_2cell_eq
           {C : bicat}
           {a b : C}
           {f g : C⟦a,b⟧}
           (Y : f ==> g → UU)
           {α : f ==> g}
           (H₁ : is_invertible_2cell α) (H₂ : is_invertible_2cell α)
           (y : Y α)
  : transportf (λ (z : invertible_2cell f g), Y (pr1 z))
               (@cell_from_invertible_2cell_eq C _ _ _ _
                                               (α ,, H₁) (α ,, H₂)
                                               (idpath α))
               y
    =
    y.
Proof.
  apply transportf_subtypeEquality'.
Qed.

Section Total_Category_Locally_Univalent.
  Context {C : bicat} {D : disp_bicat C}.
  Variable (HC : is_univalent_2_1 C)
           (HD : disp_locally_univalent D).
  Local Definition E := (total_bicat D).

  Local Definition path_E
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             (ff : xx -->[ f ] yy)
             (gg : xx -->[ g ] yy)
    : (f,, ff = g,, gg) ≃ ∑ (p : f = g), transportf _ p ff = gg
    := total2_paths_equiv _ (f ,, ff) (g ,, gg).

  Local Definition path_to_iso_E
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             (ff : xx -->[ f ] yy)
             (gg : xx -->[ g ] yy)
    : (∑ (p : f = g), transportf _ p ff = gg)
        ≃
        ∑ (i : invertible_2cell f g), disp_invertible_2cell i ff gg.
  Proof.
    use weqbandf.
    - exact (idtoiso_2_1 f g ,, HC x y f g).
    - cbn.
      intros p.
      exact (disp_idtoiso_2_1 D p ff gg ,, HD x y f g p xx yy ff gg).
  Defined.

  Local Definition iso_in_E
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             (ff : xx -->[ f ] yy)
             (gg : xx -->[ g ] yy)
    : (∑ (i : invertible_2cell f g), disp_invertible_2cell i ff gg)
      → (@invertible_2cell E (x ,, xx) (y ,, yy) (f,, ff) (g,, gg)).
  Proof.
    intros z.
    use tpair.
    - use tpair.
      + exact (pr1 z). (* coerced to a function *)
      + exact (pr2 z).
   - use tpair.
      + use tpair.
        * exact (inv_cell (pr1 z)).
        * exact (disp_inv_cell (pr2 z)).
      + split.
        * cbn.
          use total2_paths_b.
          ** apply vcomp_rinv.
          ** apply disp_vcomp_lid.
        * cbn.
          use total2_paths_b.
          ** apply vcomp_lid.
          ** apply disp_vcomp_rinv.
  Defined.

  Local Definition iso_in_E_inv
        {x y : C}
        {xx : D x}
        {yy : D y}
        {f g : C⟦x,y⟧}
        (ff : xx -->[ f ] yy)
        (gg : xx -->[ g ] yy)
    : @invertible_2cell E (x ,, xx) (y ,, yy) (f,, ff) (g,, gg)
      → ∑ (i : invertible_2cell f g), disp_invertible_2cell i ff gg.
  Proof.
    intros z.
    induction z as [z Hz].
    induction z as [z zz].
    induction Hz as [inv Hz].
    induction inv as [i ii].
    induction Hz as [Hz1 Hz2].
    cbn in *.
    use tpair.
    - exists z.
      use tpair.
      + exact i.
      + cbn.
        split.
        * exact (base_paths _ _ Hz1).
        * exact (base_paths _ _ Hz2).
    - cbn.
      exists zz.
      use tpair.
      + exact ii.
      + cbn.
        split.
        * apply (@transportf_transpose _ (λ α : f ==> f, ff ==>[ α] ff)).
          refine (_ @ fiber_paths Hz1).
          apply (@transportf_paths _ (λ α : f ==> f, ff ==>[ α] ff)).
          apply pathsinv0inv0.
        * apply (@transportf_transpose _ (λ α : g ==> g, gg ==>[ α] gg)).
          refine (_ @ fiber_paths Hz2).
          apply (@transportf_paths _ (λ α : g ==> g, gg ==>[ α] gg)).
          apply pathsinv0inv0.
  Defined.

  Definition TODO {A : UU} : A.
  Admitted.

  Local Definition iso_in_E_weq
        {x y : C}
        {xx : D x}
        {yy : D y}
        {f g : C⟦x,y⟧}
        (ff : xx -->[ f ] yy)
        (gg : xx -->[ g ] yy)
    : (∑ (i : invertible_2cell f g), disp_invertible_2cell i ff gg)
        ≃
        (@invertible_2cell E (x ,, xx) (y ,, yy) (f,, ff) (g,, gg)).
  Proof.
    refine (iso_in_E ff gg ,, _).
    use isweq_iso.
    - exact (iso_in_E_inv ff gg).
    - intros z.
      induction z as [z zz].
      use total2_paths2_f.
      + apply cell_from_invertible_2cell_eq.
        reflexivity.
      + use subtypeEquality'.
        * unfold disp_invertible_2cell.
          rewrite pr1_transportf.
          unfold pr1.
          induction zz as [zz Hzz].
          unfold invertible_2cell.
          apply (transportf_cell_from_invertible_2cell_eq (λ z, ff ==>[ z ] gg)).
        * apply TODO.
    - intros z.
      destruct z as [z Hz].
      destruct z as [z zz].
      destruct Hz as [inv Hz].
      destruct inv as [i ii].
      destruct Hz as [Hz1 Hz2].
      apply (@cell_from_invertible_2cell_eq E).
      reflexivity.
  Defined.

  Local Definition idtoiso_alt
             {x y : E}
             (f g : E⟦x,y⟧)
    : (idtoiso_2_1 f g
       ~
       (iso_in_E_weq (pr2 f) (pr2 g))
         ∘ (path_to_iso_E (pr2 f) (pr2 g))
         ∘ (path_E (pr2 f) (pr2 g)))%weq.
  Proof.
    intros p.
    induction p.
    apply (@cell_from_invertible_2cell_eq E).
    reflexivity.
  Defined.

  Definition total_is_locally_univalent : is_univalent_2_1 E.
  Proof.
    intros x y f g.
    exact (weqhomot (idtoiso_2_1 f g) _ (invhomot (idtoiso_alt f g))).
  Defined.
End Total_Category_Locally_Univalent.



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
           {j : internal_adjunction a b}
           (f := internal_left_adjoint j)
           (g := internal_right_adjoint j)
           {aa : D a} {bb : D b}
           (jj : disp_internal_adjunction_data j aa bb)
           (ff := disp_internal_left_adjoint jj)
           (gg := disp_internal_right_adjoint jj)
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
  : UU
  := ∑ (aa : D a) (bb : D b) (jj : disp_internal_adjunction_data j aa bb),
     is_disp_internal_adjunction jj.

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
               (j := internal_adjunction_from_internal_adjoint_equivalence j) jj.


Definition disp_internal_adjunction_data_identity {a : C} (aa : D a)
  : disp_internal_adjunction_data (internal_adjunction_identity a) aa aa.
Proof.
  exists (id_disp _ ).
  exists (id_disp _ ).
  exists (disp_linvunitor _ ).
  apply (disp_lunitor _ ).
Defined.

Lemma disp_rwhisker_transport_left {a b c : C}
      {f1 f2 : C⟦a,b⟧} {g : C⟦b,c⟧}
      {x x' : f1 ==> f2} (p : x = x')
      {aa : D a} {bb : D b} {cc : D c}
      {ff1 : aa -->[f1] bb}
      {ff2 : aa -->[f2] bb}
      (xx : ff1 ==>[x] ff2)
      (gg : bb -->[g] cc)
  : (transportf (λ x, _ ==>[x] _) p xx) ▹▹ gg =
    transportf (λ x, _ ==>[x ▹ g] _) p (xx ▹▹ gg).
Proof.
  induction p. apply idpath.
Defined.

Lemma disp_rwhisker_transport_left_new {a b c : C}
      {f1 f2 : C⟦a,b⟧} {g : C⟦b,c⟧}
      {x x' : f1 ==> f2} (p : x = x')
      {aa : D a} {bb : D b} {cc : D c}
      {ff1 : aa -->[f1] bb}
      {ff2 : aa -->[f2] bb}
      (xx : ff1 ==>[x] ff2)
      (gg : bb -->[g] cc)
  : (transportf (λ x, _ ==>[x] _) p xx) ▹▹ gg =
    transportf (λ x, _ ==>[x] _) (maponpaths (λ x, x ▹ g) p) (xx ▹▹ gg).
Proof.
  induction p. apply idpath.
Defined.

Lemma disp_rwhisker_transport_right {a b c : C}
      {f : C⟦a,b⟧} {g1 g2 : C⟦b,c⟧}
      {x x' : g1 ==> g2} (p : x = x')
      {aa : D a} {bb : D b} {cc : D c}
      {ff : aa -->[f] bb}
      (gg1 : bb -->[g1] cc)
      (gg2 : bb -->[g2] cc)
      (xx : gg1 ==>[x] gg2)
  : ff ◃◃ (transportf (λ x, _ ==>[x] _) p xx) =
    transportf (λ x, _ ==>[x] _) (maponpaths (λ x, f ◃ x) p) (ff ◃◃ xx).
Proof.
  induction p. apply idpath.
Defined.

End Displayed_Internal_Adjunction.

(** From now on, we need the [has_disp_cellset property]. *)

Definition is_disp_internal_adjunction_identity
           {C : bicat} {D : disp_bicat C}
           {a : C} (aa : D a)
  : is_disp_internal_adjunction (disp_internal_adjunction_data_identity aa).
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
