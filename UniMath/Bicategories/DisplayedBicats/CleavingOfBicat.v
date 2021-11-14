(*********************************************************************

 Cleavings of bicategories

 In this file, we define cleaving of bicategories

 Content:
 1. Definition of cleaving
 2. Properties of cartesian 1-cells
 3. Properties of cartesian 2-cells

 *********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.Colimits.Pullback.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictPseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.StrictPseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.StrictToPseudo.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.


Definition disp_hcomp
           {B : bicat}
           {D : disp_bicat B}
           {b₁ b₂ b₃ : B}
           {f₁ f₂ : b₁ --> b₂}
           {g₁ g₂ : b₂ --> b₃}
           {α : f₁ ==> f₂}
           {β : g₁ ==> g₂}
           {bb₁ : D b₁}
           {bb₂ : D b₂}
           {bb₃ : D b₃}
           {ff₁ : bb₁ -->[ f₁ ] bb₂}
           {ff₂ : bb₁ -->[ f₂ ] bb₂}
           {gg₁ : bb₂ -->[ g₁ ] bb₃}
           {gg₂ : bb₂ -->[ g₂ ] bb₃}
           (αα : ff₁ ==>[ α ] ff₂)
           (ββ : gg₁ ==>[ β ] gg₂)
  : ff₁ ;; gg₁ ==>[ β ⋆⋆ α ] ff₂ ;; gg₂
  := (αα ▹▹ gg₁) •• (ff₂ ◃◃ ββ).


(** 1. Definition of cleaving *)

Section BicatCleaving.
  Context {B : bicat}
          (D : disp_bicat B).

  Section Cartesian1cell.
    Context {a b : B}
            {f : a --> b}
            {aa : D a}
            {bb : D b}
            (ff : aa -->[ f ] bb).

    Definition lift_1cell
               {c : B}
               {cc : D c}
               {h : c --> a}
               (gg : cc -->[ h · f ] bb)
      : UU
      := ∑ (hh : cc -->[ h ] aa),
         disp_invertible_2cell
           (id2_invertible_2cell _)
           (hh ;; ff)
           gg.

    Coercion disp_mor_lift_1cell
             {c : B}
             {cc : D c}
             {h : c --> a}
             {gg : cc -->[ h · f ] bb}
             (Lh : lift_1cell gg)
      : cc -->[ h ] aa
      := pr1 Lh.

    Definition disp_cell_lift_1cell
               {c : B}
               {cc : D c}
               {h : c --> a}
               {gg : cc -->[ h · f ] bb}
               (Lh : lift_1cell gg)
      : disp_invertible_2cell _ (disp_mor_lift_1cell Lh;; ff) gg
      := pr2 Lh.

    Definition lift_2cell
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell gg)
               (Lh' : lift_1cell gg')
      : UU
      := ∃! (δδ : disp_mor_lift_1cell Lh ==>[ δ ] disp_mor_lift_1cell Lh'),
         transportf
           (λ z, _ ==>[ z ] _)
           (id2_right _ @ ! id2_left _ )
           (δδ ▹▹ ff •• disp_cell_lift_1cell Lh')
         =
         disp_cell_lift_1cell Lh •• σσ.

    Definition disp_cell_lift_2cell
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               {σσ : gg ==>[ δ ▹ f] gg'}
               {Lh : lift_1cell gg}
               {Lh' : lift_1cell gg'}
               (Hσσ : lift_2cell σσ Lh Lh')
      : disp_mor_lift_1cell Lh ==>[ δ ] disp_mor_lift_1cell Lh'
      := pr11 Hσσ.

    Definition eq_lift_2cell
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               {σσ : gg ==>[ δ ▹ f] gg'}
               {Lh : lift_1cell gg}
               {Lh' : lift_1cell gg'}
               (Hσσ : lift_2cell σσ Lh Lh')
      : transportf
          (λ z, _ ==>[ z ] _)
          (id2_right _ @ ! id2_left _ )
          (disp_cell_lift_2cell Hσσ ▹▹ ff •• disp_cell_lift_1cell Lh')
        =
        disp_cell_lift_1cell Lh •• σσ
      := pr21 Hσσ.

    Definition isaprop_lift_of_lift_2cell
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               {σσ : gg ==>[ δ ▹ f] gg'}
               {Lh : lift_1cell gg}
               {Lh' : lift_1cell gg'}
               (Hσσ : lift_2cell σσ Lh Lh')
               (δδ₁ : disp_mor_lift_1cell Lh ==>[ δ ] disp_mor_lift_1cell Lh')
               (δδ₂ : disp_mor_lift_1cell Lh ==>[ δ ] disp_mor_lift_1cell Lh')
               (Pδδ₁ : transportf
                         (λ z, _ ==>[ z ] _)
                         (id2_right _ @ ! id2_left _ )
                         (δδ₁ ▹▹ ff •• disp_cell_lift_1cell Lh')
                       =
                       disp_cell_lift_1cell Lh •• σσ)
               (Pδδ₂ : transportf
                         (λ z, _ ==>[ z ] _)
                         (id2_right _ @ ! id2_left _ )
                         (δδ₂ ▹▹ ff •• disp_cell_lift_1cell Lh')
                       =
                       disp_cell_lift_1cell Lh •• σσ)
      : δδ₁ = δδ₂.
    Proof.
      pose (proofirrelevance _ (isapropifcontr Hσσ) (δδ₁ ,, Pδδ₁) (δδ₂ ,, Pδδ₂)) as p.
      exact (maponpaths pr1 p).
    Qed.

    Definition cartesian_1cell
      : UU
      := (∏ (c : B)
            (cc : D c)
            (h : c --> a)
            (gg : cc -->[ h · f ] bb),
          lift_1cell gg)
         ×
         ∏ (c : B)
           (cc : D c)
           (h h' : c --> a)
           (gg : cc -->[h · f ] bb)
           (gg' : cc -->[h' · f ] bb)
           (δ : h ==> h')
           (σσ : gg ==>[ δ ▹ f] gg')
           (Lh : lift_1cell gg)
           (Lh' : lift_1cell gg'),
         lift_2cell
           σσ
           Lh
           Lh'.

    Definition cartesian_1cell_lift_1cell
               (Hff : cartesian_1cell)
               {c : B}
               {cc : D c}
               {h : c --> a}
               (gg : cc -->[ h · f ] bb)
      : lift_1cell gg
      := pr1 Hff c cc h gg.

    Definition cartesian_1cell_lift_2cell
               (Hff : cartesian_1cell)
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell gg)
               (Lh' : lift_1cell gg')
      : disp_mor_lift_1cell Lh ==>[ δ ] disp_mor_lift_1cell Lh'
      := disp_cell_lift_2cell (pr2 Hff c cc h h' gg gg' δ σσ Lh Lh').

    Definition cartesian_1cell_lift_2cell_invertible
               (Hff : cartesian_1cell)
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (Hδ : is_invertible_2cell δ)
               {σσ : gg ==>[ δ ▹ f] gg'}
               (Hσσ : is_disp_invertible_2cell (is_invertible_2cell_rwhisker f Hδ) σσ)
               (Lh : lift_1cell gg)
               (Lh' : lift_1cell gg')
      : is_disp_invertible_2cell Hδ (cartesian_1cell_lift_2cell Hff σσ Lh Lh').
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact (cartesian_1cell_lift_2cell Hff (pr1 Hσσ) Lh' Lh).
      - apply TODO.
      - apply TODO.
    Defined.

    Definition cartesian_1cell_lift_2cell_commutes
               (Hff : cartesian_1cell)
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell gg)
               (Lh' : lift_1cell gg')
      : transportf
          (λ z, _ ==>[ z ] _)
          (id2_right _ @ ! id2_left _ )
          (cartesian_1cell_lift_2cell Hff σσ Lh Lh' ▹▹ ff •• disp_cell_lift_1cell Lh')
        =
        disp_cell_lift_1cell Lh •• σσ
      := eq_lift_2cell (pr2 Hff c cc h h' gg gg' δ σσ Lh Lh').
  End Cartesian1cell.

  Definition is_cartesian_2cell
             {x y : B}
             {xx : D x} {yy : D y}
             {f g : x --> y}
             {ff : xx -->[ f ] yy}
             {gg : xx -->[ g ] yy}
             {α : f ==> g}
             (αα : ff ==>[ α ] gg)
    : UU
    := ∏ (h : x --> y)
         (hh : xx -->[ h ] yy)
         (γ : h ==> f)
         (ββ : hh ==>[ γ • α ] gg),
       ∃! (γγ : hh ==>[ γ ] ff), (γγ •• αα) = ββ.

  Definition cartesian_lift_2cell
             {x y : B}
             {xx : D x}
             {yy : D y}
             {f g : x --> y}
             (gg : xx -->[ g ] yy)
             (α : f ==> g)
    : UU
    := ∑ (ff : xx -->[ f ] yy) (αα : ff ==>[ α ] gg), is_cartesian_2cell αα.

  Definition local_cleaving
    : UU
    := ∏ (x y : B)
         (xx : D x) (yy : D y)
         (f g : x --> y)
         (gg : xx -->[ g ] yy)
         (α : f ==> g),
       cartesian_lift_2cell gg α.

  Definition global_cleaving
    : UU
    := ∏ (a b : B)
         (bb : D b)
         (f : a --> b),
       ∑ (aa : D a) (ff : aa -->[ f ] bb), cartesian_1cell ff.

  Definition lwhisker_cartesian
    : UU
    := ∏ (w x y : B)
         (ww : D w) (xx : D x) (yy : D y)
         (h : w --> x)
         (f g : x --> y)
         (hh : ww -->[ h ] xx)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (α : f ==> g)
         (αα : ff ==>[ α ] gg),
       is_cartesian_2cell αα → is_cartesian_2cell (hh ◃◃ αα).

  Definition rwhisker_cartesian
    : UU
    := ∏ (x y z : B)
         (xx : D x) (yy : D y) (zz : D z)
         (f g : x --> y) (h : y --> z)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (hh : yy -->[ h ] zz)
         (α : f ==> g)
         (αα : ff ==>[ α ] gg),
       is_cartesian_2cell αα → is_cartesian_2cell (αα ▹▹ hh).

  Definition cleaving_of_bicats
    : UU
    := local_cleaving
       × global_cleaving
       × lwhisker_cartesian
       × rwhisker_cartesian.

  Coercion cleaving_of_bicats_local_cleaving
           (CD : cleaving_of_bicats)
    : local_cleaving
    := pr1 CD.

  Coercion cleaving_of_bicats_global_cleaving
           (CD : cleaving_of_bicats)
    : global_cleaving
    := pr12 CD.

  Coercion cleaving_of_bicats_lwhisker_cartesian
           (CD : cleaving_of_bicats)
    : lwhisker_cartesian
    := pr122 CD.

  Coercion cleaving_of_bicats_rwhisker_cartesian
           (CD : cleaving_of_bicats)
    : rwhisker_cartesian
    := pr222 CD.
End BicatCleaving.

(** 2. Properties of cartesian 1-cells *)
Definition isaprop_cartesian_1cell
           {B : bicat}
           (HB : is_univalent_2_1 B)
           {D : disp_bicat B}
           (HD : disp_univalent_2_1 D)
           {b₁ b₂ : B}
           {f : b₁ --> b₂}
           {bb₁ : D b₁}
           {bb₂ : D b₂}
           (ff : bb₁ -->[ f ] bb₂)
  : isaprop (cartesian_1cell D ff).
Proof.
  apply TODO.
Qed.

Section Cartesian1CellViaPb.
  Context {B : bicat}
          (HB : is_univalent_2_1 B)
          {D : disp_bicat B}
          (HD : disp_univalent_2_1 D)
          {b₁ b₂ : B}
          {f : b₁ --> b₂}
          {bb₁ : D b₁}
          {bb₂ : D b₂}
          (ff : bb₁ -->[ f ] bb₂).

  Definition cartesian_1cell_cone_comm
             {z : B}
             (zz : D z)
    : Fmor (pr1_psfunctor D) (z,, zz) (b₁,, bb₁) ∙ post_comp z f
      ⟹
      @post_comp (total_bicat D) (z ,, zz) (b₁ ,, bb₁) (b₂ ,, bb₂) (f,, ff)
      ∙
      Fmor (pr1_psfunctor D) (z,, zz) (b₂,, bb₂).
  Proof.
    use make_nat_trans.
    - exact (λ _, identity _).
    - abstract
        (intros x y g ; cbn ;
         rewrite id2_right, id2_left ;
         apply idpath).
  Defined.

  Definition cartesian_1cell_cone
             {z : B}
             (zz : D z)
    : @pb_cone
        bicat_of_univ_cats
        (univ_hom HB z b₁)
        (univ_hom
           (total_is_univalent_2_1 D HB HD)
           (z ,, zz)
           (b₂ ,, bb₂))
        (univ_hom HB z b₂)
        (post_comp _ f)
        (Fmor (pr1_psfunctor D) (z ,, zz) (b₂ ,, bb₂)).
  Proof.
    use make_pb_cone.
    - exact (univ_hom
               (total_is_univalent_2_1 D HB HD)
               (z ,, zz)
               (b₁ ,, bb₁)).
    - exact (Fmor (pr1_psfunctor D) (z ,, zz) (b₁ ,, bb₁)).
    - exact (@post_comp (total_bicat D) (z ,, zz) (b₁ ,, bb₁) (b₂ ,, bb₂) (f ,, ff)).
    - use make_invertible_2cell.
      + apply cartesian_1cell_cone_comm.
      + apply is_nat_iso_to_is_invertible_2cell.
        intro.
        apply identity_is_iso.
  Defined.

  Definition cartesian_1cell_to_pb
             (Hff : cartesian_1cell D ff)
             {z : B}
             (zz : D z)
    : has_pb_ump (cartesian_1cell_cone zz).
  Proof.
    apply TODO.
  Defined.

  Definition pb_to_cartesian_1cell
             (Hff : ∏ (z : B) (zz : D z), has_pb_ump (cartesian_1cell_cone zz))
    : cartesian_1cell D ff.
  Proof.
    apply TODO.
  Defined.

  Definition cartesian_1cell_weq_pb
    : cartesian_1cell D ff
      ≃
      (∏ (z : B) (zz : D z), has_pb_ump (cartesian_1cell_cone zz)).
  Proof.
    use weqimplimpl.
    - exact @cartesian_1cell_to_pb.
    - exact pb_to_cartesian_1cell.
    - exact (isaprop_cartesian_1cell HB HD ff).
    - abstract
        (do 2 (use impred ; intro) ;
         apply isaprop_has_pb_ump ;
         apply univalent_cat_is_univalent_2_1).
  Defined.
End Cartesian1CellViaPb.

Definition id1_is_cartesian_1cell
           {B : bicat}
           {D : disp_bicat B}
           {a : B}
           (aa : D a)
  : cartesian_1cell D (id_disp aa).
Proof.
  apply TODO.
Defined.

Definition comp_is_cartesian_1cell
           {B : bicat}
           {D : disp_bicat B}
           {b₁ b₂ b₃ : B}
           {f : b₁ --> b₂}
           {g : b₂ --> b₃}
           {bb₁ : D b₁}
           {bb₂ : D b₂}
           {bb₃ : D b₃}
           {ff : bb₁ -->[ f ] bb₂}
           {gg : bb₂ -->[ g ] bb₃}
           (Hff : cartesian_1cell D ff)
           (Hgg : cartesian_1cell D gg)
  : cartesian_1cell D (ff ;; gg).
Proof.
  apply TODO.
Defined.

(** 3. Properties of cartesian 2-cells *)

Definition local_fib
           {B : bicat}
           (D : disp_bicat B)
  : UU
  := ∏ (x y : B)
       (xx : D x)
       (yy : D y),
     cleaving (disp_hom xx yy).

(** Being a cartesian 2-cell is a proposition *)
Definition isaprop_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           (αα : ff ==>[ α ] gg)
  : isaprop (is_cartesian_2cell D αα).
Proof.
  unfold is_cartesian_2cell.
  repeat (use impred ; intro).
  apply isapropiscontr.
Qed.

(** The two definitions of local cleavings coincide *)
Definition cartesian_2cell_to_cartesian
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           (αα : ff ==>[ α ] gg)
           (Hαα : is_cartesian_2cell D αα)
  : @is_cartesian _ (disp_hom xx yy) _ _ _ _ _ αα.
Proof.
  intros h γ hh γα.
  exact (Hαα h hh γ γα).
Qed.

Definition cartesian_to_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           (αα : ff ==>[ α ] gg)
           (Hαα : @is_cartesian _ (disp_hom xx yy) _ _ _ _ _ αα)
  : is_cartesian_2cell D αα.
Proof.
  intros h hh γ γα.
  exact (Hαα h γ hh γα).
Qed.

Definition cartesian_2cell_weq_cartesian
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           (αα : ff ==>[ α ] gg)
  : (@is_cartesian _ (disp_hom xx yy) _ _ _ _ _ αα)
    ≃
    is_cartesian_2cell D αα.
Proof.
  use weqimplimpl.
  - apply cartesian_to_cartesian_2cell.
  - apply cartesian_2cell_to_cartesian.
  - apply isaprop_is_cartesian.
  - apply isaprop_is_cartesian_2cell.
Qed.

Definition local_cleaving_to_local_fib
           {B : bicat}
           {D : disp_bicat B}
           (HD : local_cleaving D)
  : local_fib D.
Proof.
  intros x y xx yy g f α gg ; cbn in *.
  pose (HD x y xx yy f g gg α) as lift.
  unfold cartesian_lift.
  unfold cartesian_lift_2cell in lift.
  cbn.
  refine (pr1 lift ,, pr12 lift ,, _).
  apply cartesian_2cell_to_cartesian.
  exact (pr22 lift).
Defined.

Definition local_fib_to_local_cleaving
           {B : bicat}
           {D : disp_bicat B}
           (HD : local_fib D)
  : local_cleaving D.
Proof.
  intros x y xx yy g f α gg ; cbn in *.
  pose (HD x y xx yy f g gg α) as lift.
  unfold cartesian_lift in lift.
  unfold cartesian_lift_2cell.
  cbn.
  refine (pr1 lift ,, pr12 lift ,, _).
  apply cartesian_to_cartesian_2cell.
  exact (pr22 lift).
Defined.

Definition local_fib_weq_local_cleaving
           {B : bicat}
           (D : disp_bicat B)
  : local_cleaving D ≃ local_fib D.
Proof.
  use make_weq.
  - exact local_cleaving_to_local_fib.
  - use gradth.
    + exact local_fib_to_local_cleaving.
    + abstract
        (intro HD ;
         repeat (use funextsec ; intro) ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         apply isaprop_is_cartesian_2cell).
    + abstract
        (intro HD ;
         repeat (use funextsec ; intro) ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         apply isaprop_is_cartesian).
Defined.

(** Properties of cartesian 2-cells *)
Definition identity_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f : x --> y}
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
  : is_cartesian_2cell D (disp_id2 ff).
Proof.
  apply cartesian_to_cartesian_2cell.
  exact (@is_cartesian_id_disp _ (disp_hom xx yy) f ff).
Defined.

Definition vcomp_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g h : x --> y}
           {α : f ==> g} {β : g ==> h}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           {hh : xx -->[ h ] yy}
           {αα : ff ==>[ α ] gg}
           {ββ : gg ==>[ β ] hh}
           (Hαα : is_cartesian_2cell D αα)
           (Hββ : is_cartesian_2cell D ββ)
  : is_cartesian_2cell D (αα •• ββ).
Proof.
  apply cartesian_to_cartesian_2cell.
  exact (@is_cartesian_comp_disp
           _ (disp_hom xx yy)
           f ff
           g gg
           h hh
           α β
           αα ββ
           (cartesian_2cell_to_cartesian _ Hαα)
           (cartesian_2cell_to_cartesian _ Hββ)).
Defined.

Definition invertible_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f g : x --> y}
           {α : f ==> g}
           {Hα : is_invertible_2cell α}
           {xx : D x}
           {yy : D y}
           {ff : xx -->[ f ] yy}
           {gg : xx -->[ g ] yy}
           {αα : ff ==>[ α ] gg}
           (Hαα : is_disp_invertible_2cell Hα αα)
  : is_cartesian_2cell D αα.
Proof.
  apply cartesian_to_cartesian_2cell.
  apply (is_cartesian_disp_iso (disp_hom_disp_invertible_2cell_to_iso _ Hαα)).
Defined.

Definition disp_hcomp_is_cartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           (CD : cleaving_of_bicats D)
           {b₁ b₂ b₃ : B}
           {f₁ f₂ : b₁ --> b₂}
           {g₁ g₂ : b₂ --> b₃}
           {α : f₁ ==> f₂}
           {β : g₁ ==> g₂}
           {bb₁ : D b₁}
           {bb₂ : D b₂}
           {bb₃ : D b₃}
           {ff₁ : bb₁ -->[ f₁ ] bb₂}
           {ff₂ : bb₁ -->[ f₂ ] bb₂}
           {gg₁ : bb₂ -->[ g₁ ] bb₃}
           {gg₂ : bb₂ -->[ g₂ ] bb₃}
           {αα : ff₁ ==>[ α ] ff₂}
           {ββ : gg₁ ==>[ β ] gg₂}
           (Hαα : is_cartesian_2cell D αα)
           (Hββ : is_cartesian_2cell D ββ)
  : is_cartesian_2cell D (disp_hcomp αα ββ).
Proof.
  use vcomp_is_cartesian_2cell.
  - apply CD.
    exact Hαα.
  - apply CD.
    exact Hββ.
Defined.
