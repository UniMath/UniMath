(* *********************************************************************************** *)
(** * Displayed invertible 2-cells

    This file contains:
    - Proof that being an displayed invertible 2-cell is a proposition
    - The classification of invertible 2-cells in the total category in terms of displayed
    invertible 2-cells. *)
(* *********************************************************************************** *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.

Local Open Scope cat.
Local Open Scope mor_disp_scope.


Definition transportf_subtypePath'
           {A : UU}
           {B : A → UU}
           (Bprop : ∏ (a : A), isaprop (B a))
           {C : A → UU}
           {a : A}
           (b₁ : B a) (b₂ : B a)
           (x : C a)
  : transportf (λ (z : ∑ (x : A), B x), C (pr1 z))
               (@subtypePath' A B (a ,, b₁) (a ,, b₂) (idpath _) (Bprop _))
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

(* TODO: should be moved to Bicat.v or bicategory_laws.v *)
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
  apply transportf_subtypePath'.
Qed.

(** The displayed identity 2-cells are invertible *)
Definition disp_id2_invertible_2cell
           {C : bicat}
           {D : disp_prebicat C}
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

(** ** Being a displayed invertible 2-cell is a proposition *)
(** The proof of this fact is a bit tricky, and used an intermediate datastructure [disp_iso_total].
*)
Section Prop_disp_invertible_2cell.
  Context {C : bicat}.
  Context {D : disp_bicat C}.

  Definition disp_iso_total
             {a b : C}
             {f g : C⟦a,b⟧}
             {x : invertible_2cell f g}
             {aa : D a} {bb : D b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : UU
    := ∑ (zz : gg ==>[ x^-1 ] ff),
       (@vcomp2 (total_bicat D)
                (a ,, aa) (b ,, bb)
                (f ,, ff) (g ,, gg) (f ,, ff)
                (pr1 x ,, xx) (x^-1 ,, zz)
        =
        @id2 (total_bicat D) (a ,, aa) (b ,, bb) (f ,, ff))
         ×
         (@vcomp2 (total_bicat D)
                  (a ,, aa) (b ,, bb)
                  (g ,, gg) (f ,, ff) (g ,, gg)
                  (x^-1 ,, zz) (pr1 x ,, xx)
          =
          @id2 (total_bicat D) (a ,, aa) (b ,, bb) (g ,, gg)).

  Definition disp_invertible_2cell_to_disp_iso
             {a b : C}
             {f g : C⟦a,b⟧}
             {x : invertible_2cell f g}
             {aa : D a} {bb : D b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : is_disp_invertible_2cell x xx
      →
      disp_iso_total xx.
  Proof.
    intros p.
    use tpair.
    - exact (pr1 p).
    - split ; cbn.
      + use total2_paths2_b.
        * apply vcomp_rinv.
        * apply p.
      + use total2_paths2_b.
        * apply vcomp_lid.
        * apply p.
  Defined.

  Definition disp_invertible_2cell_to_disp_iso_inv
             {a b : C}
             {f g : C⟦a,b⟧}
             {x : invertible_2cell f g}
             {aa : D a} {bb : D b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : disp_iso_total xx
      →
      is_disp_invertible_2cell x xx.
  Proof.
    intros z.
    use tpair.
    - exact (pr1 z).
    - split ; cbn.
      + cbn in *.
        apply (@transportf_transpose _ (λ α : f ==> f, ff ==>[ α] ff)).
        refine (_ @ fiber_paths (pr1 (pr2 z))).
        apply (@transportf_paths _ (λ α : f ==> f, ff ==>[ α] ff)).
        apply C.
      + apply (@transportf_transpose _ (λ α : g ==> g, gg ==>[ α] gg)).
        refine (_ @ fiber_paths (pr2 (pr2 z))).
        apply (@transportf_paths _ (λ α : g ==> g, gg ==>[ α] gg)).
        apply C.
  Defined.

  Definition disp_invertible_2cell_to_disp_iso_weq
             {a b : C}
             {f g : C⟦a,b⟧}
             {x : invertible_2cell f g}
             {aa : D a} {bb : D b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : is_disp_invertible_2cell x xx ≃ disp_iso_total xx.
  Proof.
    exists (disp_invertible_2cell_to_disp_iso xx).
    use isweq_iso.
    - apply disp_invertible_2cell_to_disp_iso_inv.
    - intros z.
      apply subtypePath.
      + intro; apply isapropdirprod ; apply D.
      + reflexivity.
    - intros z.
      apply subtypePath.
      + intro; apply isapropdirprod ; apply (total_bicat D).
      + reflexivity.
  Defined.

  Definition disp_iso_to_invetible_2cell
             {a b : C}
             {f g : C⟦a,b⟧}
             {x : invertible_2cell f g}
             {aa : D a} {bb : D b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : disp_iso_total xx
      →
      @is_invertible_2cell (total_bicat D) (a ,, aa) (b ,, bb) (f ,, ff) (g ,, gg) (pr1 x ,, xx).
  Proof.
    intros z.
    use tpair.
    - use tpair.
      + exact (x^-1).
      + exact (pr1 z).
    - split ; cbn.
      + use total2_paths_f ; cbn.
        * apply vcomp_rinv.
        * refine (_ @ fiber_paths (pr1 (pr2 z))) ; cbn.
          apply (@transportf_paths _ (λ α : f ==> f, ff ==>[ α] ff)).
          apply C.
      + use total2_paths_f ; cbn.
        * apply vcomp_lid.
        * refine (_ @ fiber_paths (pr2 (pr2 z))) ; cbn.
          apply (@transportf_paths _ (λ α : g ==> g, gg ==>[ α] gg)).
          apply C.
  Defined.

  Definition pr1_invertible_2cell_total
             {a b : C}
             {f g : C⟦a,b⟧}
             {x : f ==> g}
             {aa : D a} {bb : D b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : @is_invertible_2cell (total_bicat D) (a ,, aa) (b ,, bb) (f ,, ff) (g ,, gg) (x ,, xx)
      →
      is_invertible_2cell x.
  Proof.
    intros z.
    use tpair.
    - exact (pr11 z).
    - split.
      + exact (base_paths _ _ (pr12 z)).
      + exact (base_paths _ _ (pr22 z)).
  Defined.

  Definition disp_iso_to_invetible_2cell_inv
             {a b : C}
             {f g : C⟦a,b⟧}
             {x : invertible_2cell f g}
             {aa : D a} {bb : D b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : @is_invertible_2cell (total_bicat D) (a ,, aa) (b ,, bb) (f ,, ff) (g ,, gg) (pr1 x ,, xx)
      →
      disp_iso_total xx.
  Proof.
    intros z.
    use tpair.
    - refine (transportb (λ z, _ ==>[ z ] _) _ (pr2 (pr1 z))).
      exact (base_paths _ _
                        (pr1 (isaprop_is_invertible_2cell
                                (pr1 x) (pr2 x)
                                (pr1_invertible_2cell_total xx z)))).
    - split ; cbn.
      + use total2_paths_b.
        * apply vcomp_rinv.
        * cbn.
          induction z as [inv Hz].
          induction inv as [inv1 inv2].
          induction Hz as [H1 H2].
          cbn in H1, H2.
          pose (fiber_paths H1) as p.
          cbn in p.
          rewrite <- p ; clear p.
          rewrite transport_b_f.
          cbn.
          unfold transportb.
          rewrite (@disp_mor_transportf_prewhisker).
          apply (@transportf_paths _ (λ z, ff ==>[ z ] ff)).
          apply C.
      + use total2_paths_b.
        * apply vcomp_lid.
        * cbn.
          induction z as [inv Hz].
          induction inv as [inv1 inv2].
          induction Hz as [H1 H2].
          cbn in H1, H2.
          pose (fiber_paths H2) as p.
          cbn in p.
          rewrite <- p ; clear p.
          rewrite transport_b_f.
          cbn.
          unfold transportb.
          rewrite (@disp_mor_transportf_postwhisker).
          apply (@transportf_paths _ (λ z, gg ==>[ z ] gg)).
          apply C.
  Defined.

  Definition disp_iso_to_invetible_2cell_weq
             {a b : C}
             {f g : C⟦a,b⟧}
             {x : invertible_2cell f g}
             {aa : D a} {bb : D b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : disp_iso_total xx
                     ≃
                     @is_invertible_2cell (total_bicat D) (a ,, aa) (b ,, bb) (f ,, ff) (g ,, gg) (pr1 x ,, xx).
  Proof.
    exists (disp_iso_to_invetible_2cell xx).
    use isweq_iso.
    - apply disp_iso_to_invetible_2cell_inv.
    - intros z.
      use subtypePath.
      + intro; apply isapropdirprod ; apply (total_bicat D).
      + cbn.
        apply (transportf_set (λ z, gg ==>[ z ] ff)).
        apply C.
    - intros z.
      use subtypePath.
      + intro; apply isapropdirprod ; apply (total_bicat D).
      + use total2_paths_b.
        * cbn.
          exact (base_paths _ _ (pr1
                                   (isaprop_is_invertible_2cell
                                      (pr1 x) (pr2 x)
                                      (pr1_invertible_2cell_total xx z)))).
        * cbn.
          reflexivity.
  Defined.

  Definition isaprop_is_disp_invertible_2cell
             {a b : C}
             {f g : C⟦a,b⟧}
             {x : invertible_2cell f g}
             {aa : D a} {bb : D b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : isaprop (is_disp_invertible_2cell x xx)
    := isofhlevelweqb
         1
         ((disp_iso_to_invetible_2cell_weq xx)
            ∘ disp_invertible_2cell_to_disp_iso_weq xx)%weq
         (isaprop_is_invertible_2cell _).

End Prop_disp_invertible_2cell.

(** ** Classification of invertible 2-cells in the total bicategory *)
Section Total_invertible_2cells.
  Context {C : bicat}.
  Context {D : disp_bicat C}.
  Local Definition E := (total_bicat D).

  (** *** If a 2-cell is invertible in the total category, then it is invertible in the base category *)
  Definition is_invertible_total_to_base
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             (α : f ==> g)
             (αα : ff ==>[α] gg)
    : @is_invertible_2cell E (x ,, xx) (y ,, yy) (f,, ff) (g,, gg) (α,,αα)
      → is_invertible_2cell α.
  Proof.
    intros Hz.
    induction Hz as [inv Hz].
    induction inv as [i ii].
    induction Hz as [Hz1 Hz2].
    cbn in *.
    use tpair.
    - exact i.
    -  cbn.
       split.
       + exact (base_paths _ _ Hz1).
       + exact (base_paths _ _ Hz2).
  Defined.

  (** *** If a 2-cell is invertible in the total category, then it is invertible in the fiber *)
  Definition is_invertible_total_to_fiber
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             (α : f ==> g)
             (αα : ff ==>[α] gg) :
    forall (Hαα:
      @is_invertible_2cell E (x ,, xx) (y ,, yy) (f,, ff) (g,, gg) (α,,αα)),
      is_disp_invertible_2cell
        (is_invertible_total_to_base _ _ Hαα)
        αα.
  Proof.
    intros Hz.
    induction Hz as [inv Hz].
    induction inv as [i ii].
    induction Hz as [Hz1 Hz2].
    cbn in *.
    use tpair.
    - exact ii.
    - cbn.
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

  Definition is_invertible_total_to_disp
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             (α : f ==> g)
             (αα : ff ==>[α] gg)
    : @is_invertible_2cell E (x ,, xx) (y ,, yy) (f,, ff) (g,, gg) (α,,αα)
      → ∑ (Hα : is_invertible_2cell α),
           is_disp_invertible_2cell Hα αα.
  Proof.
    intros Hαα.
    refine (is_invertible_total_to_base _ _ Hαα,,
            is_invertible_total_to_fiber _ _ Hαα).
  Defined.

  (** *** If the displayed 2-cell is invertible, then the corresponding 2-cell in the total bicategory is also invertible. *)
  Definition is_invertible_disp_to_total
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             (α : f ==> g)
             (αα : ff ==>[α] gg)
    : (∑ (Hα : is_invertible_2cell α),
         is_disp_invertible_2cell Hα αα)
      → (@is_invertible_2cell E (x ,, xx) (y ,, yy) (f,, ff) (g,, gg) (α,,αα)).
  Proof.
    intros H.
    pose (Hα := pr1 H).
    pose (Hαα := pr2 H). cbn in Hαα.
    pose (αα' := (αα,,Hαα) : disp_invertible_2cell (α,,Hα) _ _).
    use tpair.
    - use tpair.
      + exact (inv_cell Hα).
      + exact (disp_inv_cell αα').
    - split.
      + cbn.
        use total2_paths_b.
        ** apply vcomp_rinv.
        ** apply (disp_vcomp_rinv αα').
      + cbn.
        use total2_paths_b.
        ** apply vcomp_lid.
        ** apply (disp_vcomp_linv αα').
  Defined.

  (** those maps form a weak equivalence *)
  Definition is_invertible_total_to_disp_weq
             {x y : C}
             {xx : D x}
             {yy : D y}
             {f g : C⟦x,y⟧}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             (α : f ==> g)
             (αα : ff ==>[α] gg)
    : @is_invertible_2cell E (x ,, xx) (y ,, yy) (f,, ff) (g,, gg) (α,,αα)
      ≃ ∑ (Hα : is_invertible_2cell α),
           is_disp_invertible_2cell Hα αα.
  Proof.
    apply weqimplimpl.
    3: apply isaprop_is_invertible_2cell.
    3: { apply isofhleveltotal2.
         apply isaprop_is_invertible_2cell.
         intro Hα.
         pose (α' := (α,,Hα) : invertible_2cell _ _).
         apply (isaprop_is_disp_invertible_2cell (x:=α') αα). }
    apply is_invertible_total_to_disp.
    apply is_invertible_disp_to_total.
  Defined.


  (** Now we add some data in front of the [is_(disp)_invertible_2cell], and massage it a bit to get
    an equivalence between [(disp)_invertible_2cell]. *)
  Lemma step1
        {x y : C}
        {xx : D x}
        {yy : D y}
        {f g : C⟦x,y⟧}
        {ff : xx -->[ f ] yy}
        {gg : xx -->[ g ] yy} :
    @invertible_2cell E (x ,, xx) (y ,, yy) (f,, ff) (g,, gg)
≃
    (∑ (α : f ==> g) (αα : ff ==>[α] gg),
       ∑ (Hα : is_invertible_2cell α),
            is_disp_invertible_2cell Hα αα).
  Proof.
    eapply weqcomp. {
      apply weqfibtototal.
      intros ?. apply is_invertible_total_to_disp_weq. }
    eapply weqcomp. {
      apply weqinvweq.
      apply weqtotal2asstol. }
    apply idweq.
  Defined.

  Lemma step2
        {x y : C}
        {xx : D x}
        {yy : D y}
        {f g : C⟦x,y⟧}
        {ff : xx -->[ f ] yy}
        {gg : xx -->[ g ] yy} :
    (∑ (α : f ==> g) (αα : ff ==>[α] gg),
       ∑ (Hα : is_invertible_2cell α),
            is_disp_invertible_2cell Hα αα)
  ≃
    (∑ (i : invertible_2cell f g), disp_invertible_2cell i ff gg).
  Proof.
    eapply weqcomp. 2: {
      apply weqtotal2asstol. }
    unfold disp_invertible_2cell.
    eapply weqfibtototal. intros α.
    cbn.
    apply weqtotal2comm.
  Defined.

  (** Finally we combine all of the above into a single theorem *)
  Definition iso_in_E_weq
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
    apply weqinvweq.
    eapply weqcomp.
    - apply step1.
    - apply step2.
  Defined.

End Total_invertible_2cells.

Section VCompDispIsInvertible.

Context {B : bicat}
        {D : disp_bicat B}
        {a b : B}
        {aa : D a} {bb : D b}
        {f g h : a --> b}
        {ff : aa -->[ f ] bb}
        {gg : aa -->[ g ] bb}
        {hh : aa -->[ h ] bb}
        {α : invertible_2cell f g}
        {β : invertible_2cell g h}
        (αα : disp_invertible_2cell α ff gg)
        (ββ : disp_invertible_2cell β gg hh).

Definition vcomp_disp_is_invertible_rinv
  : (αα •• ββ) •• (disp_inv_cell ββ •• disp_inv_cell αα)
    =
    transportb
      (λ z, ff ==>[z] ff)
      (vcomp_rinv (comp_of_invertible_2cell α β))
      (disp_id2 ff).
Proof.
  cbn.
  rewrite disp_vassocl.
  etrans.
  {
    do 2 apply maponpaths.
    rewrite disp_vassocr.
    apply maponpaths.
    apply maponpaths_2.
    apply disp_vcomp_rinv.
  }
  unfold transportb.
  rewrite !disp_mor_transportf_postwhisker, !disp_mor_transportf_prewhisker.
  rewrite !transport_f_f.
  rewrite disp_id2_left.
  unfold transportb.
  rewrite !disp_mor_transportf_prewhisker.
  rewrite !transport_f_f.
  etrans.
  {
    apply maponpaths.
    exact (disp_vcomp_rinv αα).
  }
  unfold transportb.
  rewrite !transport_f_f.
  refine (maponpaths (λ p, transportf (λ z, _ ==>[ z ] _) p _) _).
  apply B.
Qed.

Definition vcomp_disp_is_invertible_linv
  : (disp_inv_cell ββ •• disp_inv_cell αα) •• (αα •• ββ)
    =
    transportb
      (λ z, hh ==>[z] hh)
      (vcomp_lid (comp_of_invertible_2cell α β))
      (disp_id2 hh).
Proof.
  cbn.
  etrans.
  {
    rewrite disp_vassocl.
    do 2 apply maponpaths.
    rewrite disp_vassocr.
    apply maponpaths.
    apply maponpaths_2.
    apply disp_vcomp_linv.
  }
  unfold transportb.
  rewrite !disp_mor_transportf_postwhisker, !disp_mor_transportf_prewhisker.
  rewrite !transport_f_f.
  rewrite disp_id2_left.
  unfold transportb.
  rewrite !disp_mor_transportf_prewhisker.
  rewrite !transport_f_f.
  etrans.
  {
    apply maponpaths.
    exact (disp_vcomp_linv ββ).
  }
  unfold transportb.
  rewrite !transport_f_f.
  refine (maponpaths (λ p, transportf (λ z, _ ==>[ z ] _) p _) _).
  apply B.
Qed.

Definition vcomp_disp_is_invertible
  : is_disp_invertible_2cell (comp_of_invertible_2cell α β) (αα •• ββ).
Proof.
  use tpair.
  - exact (disp_inv_cell ββ •• disp_inv_cell αα).
  - split.
    + exact vcomp_disp_is_invertible_rinv.
    + exact vcomp_disp_is_invertible_linv.
Defined.

End VCompDispIsInvertible.

Definition vcomp_disp_invertible
           {B : bicat}
           {D : disp_bicat B}
           {a b : B}
           {aa : D a} {bb : D b}
           {f g h : a --> b}
           {ff : aa -->[ f ] bb}
           {gg : aa -->[ g ] bb}
           {hh : aa -->[ h ] bb}
           {α : invertible_2cell f g}
           {β : invertible_2cell g h}
           (αα : disp_invertible_2cell α ff gg)
           (ββ : disp_invertible_2cell β gg hh)
  : disp_invertible_2cell (comp_of_invertible_2cell α β) ff hh.
Proof.
  use tpair.
  repeat use tpair.
  - exact (αα •• ββ).
  - apply vcomp_disp_is_invertible.
Defined.

Definition is_disp_invertible_2cell_lunitor
           {B : bicat}
           {x y : B}
           {f : x --> y}
           {D : disp_bicat B}
           {xx : D x}
           {yy : D y}
           (ff : xx -->[f] yy)
  : is_disp_invertible_2cell (is_invertible_2cell_lunitor f) (disp_lunitor ff).
Proof.
  use tpair.
  - exact (disp_linvunitor ff).
  - split.
    + etrans.
      { apply disp_lunitor_linvunitor. }
      apply (transportf_paths (λ p, _ ==>[p] _)).
      apply B.
    + etrans.
      { apply disp_linvunitor_lunitor. }
      apply (transportf_paths (λ p, _ ==>[p] _)).
      apply B.
Defined.

Definition disp_invertible_2cell_lunitor
           {B : bicat}
           {x y : B}
           {f : x --> y}
           {D : disp_bicat B}
           {xx : D x}
           {yy : D y}
           (ff : xx -->[f] yy)
  : disp_invertible_2cell (lunitor f,, is_invertible_2cell_lunitor f) (id_disp xx;; ff) ff
  := disp_lunitor ff,, is_disp_invertible_2cell_lunitor ff.

Definition is_disp_invertible_2cell_runitor
           {B : bicat}
           {x y : B}
           {f : x --> y}
           {D : disp_bicat B}
           {xx : D x}
           {yy : D y}
           (ff : xx -->[f] yy)
  : is_disp_invertible_2cell (is_invertible_2cell_runitor f) (disp_runitor ff).
Proof.
  use tpair.
  - exact (disp_rinvunitor ff).
  - split.
    + etrans.
      { apply disp_runitor_rinvunitor. }
      apply (transportf_paths (λ p, _ ==>[p] _)).
      apply B.
    + etrans.
      { apply disp_rinvunitor_runitor. }
      apply (transportf_paths (λ p, _ ==>[p] _)).
      apply B.
Defined.

Definition disp_invertible_2cell_runitor
           {B : bicat}
           {x y : B}
           {f : x --> y}
           {D : disp_bicat B}
           {xx : D x}
           {yy : D y}
           (ff : xx -->[f] yy)
  : disp_invertible_2cell (runitor f,, is_invertible_2cell_runitor f) (ff;; id_disp yy) ff
  := disp_runitor ff,, is_disp_invertible_2cell_runitor ff.

Definition is_disp_invertible_2cell_rinvunitor
           {B : bicat}
           {x y : B}
           {f : x --> y}
           {D : disp_bicat B}
           {xx : D x}
           {yy : D y}
           (ff : xx -->[f] yy)
  : is_disp_invertible_2cell (is_invertible_2cell_rinvunitor f) (disp_rinvunitor ff).
Proof.
  use tpair.
  - exact (disp_runitor ff).
  - split.
    + etrans.
      { apply disp_rinvunitor_runitor. }
      apply (transportf_paths (λ p, _ ==>[p] _)).
      apply B.
    + etrans.
      { apply disp_runitor_rinvunitor. }
      apply (transportf_paths (λ p, _ ==>[p] _)).
      apply B.
Defined.

Definition disp_invertible_2cell_rinvunitor
           {B : bicat}
           {x y : B}
           {f : x --> y}
           {D : disp_bicat B}
           {xx : D x}
           {yy : D y}
           (ff : xx -->[f] yy)
  : disp_invertible_2cell (rinvunitor f,, is_invertible_2cell_rinvunitor f) ff (ff;; id_disp yy)
  := disp_rinvunitor ff,, is_disp_invertible_2cell_rinvunitor ff.

Definition is_disp_invertible_2cell_lassociator
           {B : bicat}
           {w x y z : B}
           {f : w --> x}
           {g : x --> y}
           {h : y --> z}
           {D : disp_bicat B}
           {ww : D w}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           (ff : ww -->[f] xx)
           (gg : xx -->[g] yy)
           (hh : yy -->[h] zz)
  : is_disp_invertible_2cell (is_invertible_2cell_lassociator f g h) (disp_lassociator ff gg hh).
Proof.
  use tpair.
  - exact (disp_rassociator ff gg hh).
  - split.
    + etrans.
      { apply disp_lassociator_rassociator. }
      apply (transportf_paths (λ p, _ ==>[p] _)).
      apply B.
    + etrans.
      { apply disp_rassociator_lassociator. }
      apply (transportf_paths (λ p, _ ==>[p] _)).
      apply B.
Defined.

Definition disp_invertible_2cell_lassociator
           {B : bicat}
           {w x y z : B}
           {f : w --> x}
           {g : x --> y}
           {h : y --> z}
           {D : disp_bicat B}
           {ww : D w}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           (ff : ww -->[f] xx)
           (gg : xx -->[g] yy)
           (hh : yy -->[h] zz)
  : disp_invertible_2cell
      (lassociator f g h,,
                   is_invertible_2cell_lassociator f g h) _ _
  := disp_lassociator ff gg hh,, is_disp_invertible_2cell_lassociator ff gg hh.

Definition is_disp_invertible_2cell_rassociator
           {B : bicat}
           {w x y z : B}
           {f : w --> x}
           {g : x --> y}
           {h : y --> z}
           {D : disp_bicat B}
           {ww : D w}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           (ff : ww -->[f] xx)
           (gg : xx -->[g] yy)
           (hh : yy -->[h] zz)
  : is_disp_invertible_2cell (is_invertible_2cell_rassociator f g h) (disp_rassociator ff gg hh).
Proof.
  use tpair.
  - exact (disp_lassociator ff gg hh).
  - split.
    + etrans.
      { apply disp_rassociator_lassociator. }
      apply (transportf_paths (λ p, _ ==>[p] _)).
      apply B.
    + etrans.
      { apply disp_lassociator_rassociator. }
      apply (transportf_paths (λ p, _ ==>[p] _)).
      apply B.
Defined.

Definition disp_invertible_2cell_rassociator
           {B : bicat}
           {w x y z : B}
           {f : w --> x}
           {g : x --> y}
           {h : y --> z}
           {D : disp_bicat B}
           {ww : D w}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           (ff : ww -->[f] xx)
           (gg : xx -->[g] yy)
           (hh : yy -->[h] zz)
  : disp_invertible_2cell
      (rassociator f g h,,
                   is_invertible_2cell_rassociator f g h) _ _
  := disp_rassociator ff gg hh,, is_disp_invertible_2cell_rassociator ff gg hh.

Definition is_disp_invertible_2cell_lwhisker
           {B : bicat}
           {x y z : B}
           {f : x --> y}
           {g₁ g₂ : y --> z}
           {α : invertible_2cell g₁ g₂}
           {D : disp_bicat B}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           (ff : xx -->[f] yy)
           {gg₁ : yy -->[g₁] zz}
           {gg₂ : yy -->[g₂] zz}
           (αα : disp_invertible_2cell α gg₁ gg₂)
  : is_disp_invertible_2cell (is_invertible_2cell_lwhisker f (pr2 α)) (ff ◃◃ αα).
Proof.
  use tpair.
  - exact (ff ◃◃ disp_inv_cell αα).
  - split.
    + abstract
        (refine (disp_lwhisker_vcomp _ _ @ _) ;
         refine (maponpaths _ (maponpaths _ (disp_vcomp_rinv _)) @ _) ;
         unfold transportb ;
         rewrite disp_rwhisker_transport_right ;
         rewrite disp_lwhisker_id2 ;
         unfold transportb ;
         rewrite !transport_f_f ;
         apply (transportf_paths (λ p, _ ==>[ p ] _)) ;
         apply B).
    + abstract
        (refine (disp_lwhisker_vcomp _ _ @ _) ;
         refine (maponpaths _ (maponpaths _ (disp_vcomp_linv _)) @ _) ;
         unfold transportb ;
         rewrite disp_rwhisker_transport_right ;
         rewrite disp_lwhisker_id2 ;
         unfold transportb ;
         rewrite !transport_f_f ;
         apply (transportf_paths (λ p, _ ==>[ p ] _)) ;
         apply B).
Defined.

Definition disp_invertible_2cell_lwhisker
           {B : bicat}
           {x y z : B}
           {f : x --> y}
           {g₁ g₂ : y --> z}
           {α : invertible_2cell g₁ g₂}
           {D : disp_bicat B}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           (ff : xx -->[f] yy)
           {gg₁ : yy -->[g₁] zz}
           {gg₂ : yy -->[g₂] zz}
           (αα : disp_invertible_2cell α gg₁ gg₂)
  : disp_invertible_2cell (_ ,, is_invertible_2cell_lwhisker f (pr2 α)) _ _
  := disp_lwhisker ff αα,, is_disp_invertible_2cell_lwhisker ff αα.

Definition is_disp_invertible_2cell_rwhisker
           {B : bicat}
           {x y z : B}
           {f₁ f₂ : x --> y}
           {g : y --> z}
           {α : invertible_2cell f₁ f₂}
           {D : disp_bicat B}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           {ff₁ : xx -->[f₁] yy}
           {ff₂ : xx -->[f₂] yy}
           (gg : yy -->[g] zz)
           (αα : disp_invertible_2cell α ff₁ ff₂)
  : is_disp_invertible_2cell (is_invertible_2cell_rwhisker g (pr2 α)) (αα ▹▹ gg).
Proof.
  use tpair.
  - exact (disp_inv_cell αα ▹▹ gg).
  - split.
    + abstract
        (refine (disp_rwhisker_vcomp _ _ @ _) ;
         refine (maponpaths _ (maponpaths _ (disp_vcomp_rinv _)) @ _) ;
         unfold transportb ;
         rewrite disp_rwhisker_transport_left_new ;
         rewrite disp_id2_rwhisker ;
         unfold transportb ;
         rewrite !transport_f_f ;
         apply (transportf_paths (λ p, _ ==>[ p ] _)) ;
         apply B).
    +abstract
        (refine (disp_rwhisker_vcomp _ _ @ _) ;
         refine (maponpaths _ (maponpaths _ (disp_vcomp_linv _)) @ _) ;
         unfold transportb ;
         rewrite disp_rwhisker_transport_left_new ;
         rewrite disp_id2_rwhisker ;
         unfold transportb ;
         rewrite !transport_f_f ;
         apply (transportf_paths (λ p, _ ==>[ p ] _)) ;
         apply B).
Defined.

Definition disp_invertible_2cell_rwhisker
           {B : bicat}
           {x y z : B}
           {f₁ f₂ : x --> y}
           {g : y --> z}
           {α : invertible_2cell f₁ f₂}
           {D : disp_bicat B}
           {xx : D x}
           {yy : D y}
           {zz : D z}
           {ff₁ : xx -->[f₁] yy}
           {ff₂ : xx -->[f₂] yy}
           (gg : yy -->[g] zz)
           (αα : disp_invertible_2cell α ff₁ ff₂)
  : disp_invertible_2cell (_ ,, is_invertible_2cell_rwhisker g (pr2 α)) _ _
  := disp_rwhisker gg αα,, is_disp_invertible_2cell_rwhisker gg αα.
