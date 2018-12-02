(* *********************************************************************************** *)
(** * Displayed invertible 2-cells

    This file contains:
    - Proof that being an displayed invertible 2-cell is a proposition
    - The classification of invertible 2-cells in the total category in terms of displayed
    invertible 2-cells. *)
(* *********************************************************************************** *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Invertible_2cells.

Local Open Scope cat.
Local Open Scope mor_disp_scope.


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
  apply transportf_subtypeEquality'.
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
      apply subtypeEquality'.
      + reflexivity.
      + apply isapropdirprod ; apply D.
    - intros z.
      apply subtypeEquality'.
      + reflexivity.
      + apply isapropdirprod ; apply (total_bicat D).
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
      use subtypeEquality'.
      + cbn.
        apply (transportf_set (λ z, gg ==>[ z ] ff)).
        apply C.
      + apply isapropdirprod ; apply (total_bicat D).
    - intros z.
      use subtypeEquality'.
      + use total2_paths_b.
        * cbn.
          exact (base_paths _ _ (pr1
                                   (isaprop_is_invertible_2cell
                                      (pr1 x) (pr2 x)
                                      (pr1_invertible_2cell_total xx z)))).
        * cbn.
          reflexivity.
      + apply isapropdirprod ; apply (total_bicat D).
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
