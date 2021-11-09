Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.

Section BicatFibration.
  Context {B : bicat}.
  Variable (D : disp_bicat B).

  Section Cartesian1cell.
    Context {a b : B}
            {f : a --> b}
            {aa : D a}
            {bb : D b}.
    Variable (ff : aa -->[ f ] bb).

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

    Definition disp_mor_lift_1cell
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
      := ∑ (Lh : ∏ (c : B)
                   (cc : D c)
                   (h : c --> a)
                   (gg : cc -->[ h · f ] bb),
                 lift_1cell gg),
         ∏ (c : B)
           (cc : D c)
           (h h' : c --> a)
           (gg : cc -->[h · f ] bb)
           (gg' : cc -->[h' · f ] bb)
           (δ : h ==> h')
           (σσ : gg ==>[ δ ▹ f] gg'),
         lift_2cell
           σσ
           (Lh _ _ _ gg)
           (Lh _ _ _ gg').
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

  Definition fibration_of_bicats
    : UU
    := local_cleaving
       × global_cleaving
       × lwhisker_cartesian
       × rwhisker_cartesian.
End BicatFibration.

(** Lemmas on cartesian 1-cells *)
(*
Definition isaprop_cartesian_1cell
           {B : bicat}
           (D : disp_bicat B)
           {a b : B}
           {f : a --> b}
           {aa : D a}
           {bb : D b}
           (ff : aa -->[ f ] bb)
  : isaprop (cartesian_1cell D ff).
Proof.
  use invproofirrelevance.
  intros φ₁ φ₂.
  use subtypePath.
  {
    intro.
    repeat (use impred ; intro).
    apply isapropiscontr.
  }
  use funextsec ; intro c.
  use funextsec ; intro cc.
  use funextsec ; intro h.
  use funextsec ; intro gg.
  use total2_paths_f.
  - pose (pr2 φ₁ c cc h h gg gg (id2 _)).
    unfold lift_2cell in l.
    cbn in l.

  pose (pr1 φ₁) as p.
  unfold lift_1cell in p.
  pose (pr1 φ₂) as q.
  unfold lift_1cell in q.
  cbn in p.
 *)

Definition TODO {A : UU} : A.
Admitted.

(*
Definition id_cartesian_1cell
           {B : bicat}
           (D : disp_bicat B)
           {a : B}
           (aa : D a)
  : cartesian_1cell D (id_disp aa).
Proof.
  simple refine (_ ,, _).
  - intros c cc h gg.
    simple refine (_ ,, _).
    + refine (transportf (λ z, _ -->[ z ] _) _ gg).
      apply TODO.
    + simple refine (_ ,, _ ,, _ ,, _).
      * cbn.
        simple refine (transportf
                         (λ z, _ ==>[ z ] _)
                         _
                         (_ •• disp_runitor gg)).
        apply rinvunitor_runitor.
        refine (transportf
                  (λ z, _ ==>[ z ] _)
                  _
                  (_ ▹▹ id_disp aa)).
        refine (!_).
        Search (rinvunitor (_ · _)).
        refine (_ •• disp_runitor gg).
        refine (disp_runitor _
        rewrite id_disp_right.
        rewrite mor_disp_transportf_postwhisker.
        Search "transport" "pre".
        cbn.
    unfold lift_1cell.
    cbn.c
 *)



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
