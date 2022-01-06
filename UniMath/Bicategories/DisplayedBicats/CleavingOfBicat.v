(*********************************************************************

 Cleavings of bicategories

 In this file, we define cleaving of bicategories

 Content:
 1. Definition of cleaving
 2. Properties of cartesian 2-cells
 3. Local opcleavings
 4. Properties of opcartesian 2-cells

 Cartesians.v
 2. Properties of cartesian 1-cells

 CartesianPseudoFunctor.v
 6. Cartesian pseudofunctors
 7. Cartesian pseudofunctors from global cleavings

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
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Opposite.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.TransportLaws.
Require Import UniMath.Bicategories.Core.Examples.BicatOfUnivCats.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.StrictPseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.StrictPseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.StrictToPseudo.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.

Local Open Scope cat.
Local Open Scope mor_disp.

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

    Definition lift_1cell_factor
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

    Coercion disp_mor_lift_1cell_factor
             {c : B}
             {cc : D c}
             {h : c --> a}
             {gg : cc -->[ h · f ] bb}
             (Lh : lift_1cell_factor gg)
      : cc -->[ h ] aa
      := pr1 Lh.

    Definition disp_cell_lift_1cell_factor
               {c : B}
               {cc : D c}
               {h : c --> a}
               {gg : cc -->[ h · f ] bb}
               (Lh : lift_1cell_factor gg)
      : disp_invertible_2cell _ (Lh ;; ff) gg
      := pr2 Lh.

    Definition lift_2cell_factor_type
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[ h · f ] bb}
               {gg' : cc -->[ h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell_factor gg)
               (Lh' : lift_1cell_factor gg')
      : UU
      := ∑ (δδ : Lh ==>[ δ ] Lh'),
         transportf
           (λ z, _ ==>[ z ] _)
           (id2_right _ @ ! id2_left _ )
           (δδ ▹▹ ff •• disp_cell_lift_1cell_factor Lh')
         =
         disp_cell_lift_1cell_factor Lh •• σσ.

    Definition lift_2cell_factor
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell_factor gg)
               (Lh' : lift_1cell_factor gg')
      : UU
      := iscontr (lift_2cell_factor_type σσ Lh Lh').

    Coercion disp_cell_lift_2cell_factor
             {c : B}
             {cc : D c}
             {h h' : c --> a}
             {gg : cc -->[h · f ] bb}
             {gg' : cc -->[h' · f ] bb}
             {δ : h ==> h'}
             {σσ : gg ==>[ δ ▹ f] gg'}
             {Lh : lift_1cell_factor gg}
             {Lh' : lift_1cell_factor gg'}
             (Hσσ : lift_2cell_factor σσ Lh Lh')
      : Lh ==>[ δ ] Lh'
      := pr11 Hσσ.

    Definition eq_lift_2cell
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               {σσ : gg ==>[ δ ▹ f] gg'}
               {Lh : lift_1cell_factor gg}
               {Lh' : lift_1cell_factor gg'}
               (Hσσ : lift_2cell_factor σσ Lh Lh')
      : transportf
          (λ z, _ ==>[ z ] _)
          (id2_right _ @ ! id2_left _ )
          (Hσσ ▹▹ ff •• disp_cell_lift_1cell_factor Lh')
        =
        disp_cell_lift_1cell_factor Lh •• σσ
      := pr21 Hσσ.

    Definition eq_lift_2cell_alt
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               {σσ : gg ==>[ δ ▹ f] gg'}
               {Lh : lift_1cell_factor gg}
               {Lh' : lift_1cell_factor gg'}
               (Hσσ : lift_2cell_factor σσ Lh Lh')
      : Hσσ ▹▹ ff •• disp_cell_lift_1cell_factor Lh'
        =
        transportb
          (λ z, _ ==>[ z ] _)
          (id2_right _ @ ! id2_left _ )
          (disp_cell_lift_1cell_factor Lh •• σσ).
    Proof.
      rewrite <- (eq_lift_2cell Hσσ).
      rewrite transportbfinv.
      apply idpath.
    Qed.

    Definition isaprop_lift_of_lift_2cell
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               {σσ : gg ==>[ δ ▹ f] gg'}
               {Lh : lift_1cell_factor gg}
               {Lh' : lift_1cell_factor gg'}
               (Hσσ : lift_2cell_factor σσ Lh Lh')
               (δδ₁ : Lh ==>[ δ ] Lh')
               (δδ₂ : Lh ==>[ δ ] Lh')
               (Pδδ₁ : transportf
                         (λ z, _ ==>[ z ] _)
                         (id2_right _ @ ! id2_left _ )
                         (δδ₁ ▹▹ ff •• disp_cell_lift_1cell_factor Lh')
                       =
                       disp_cell_lift_1cell_factor Lh •• σσ)
               (Pδδ₂ : transportf
                         (λ z, _ ==>[ z ] _)
                         (id2_right _ @ ! id2_left _ )
                         (δδ₂ ▹▹ ff •• disp_cell_lift_1cell_factor Lh')
                       =
                       disp_cell_lift_1cell_factor Lh •• σσ)
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
          lift_1cell_factor gg)
         ×
         ∏ (c : B)
           (cc : D c)
           (h h' : c --> a)
           (gg : cc -->[h · f ] bb)
           (gg' : cc -->[h' · f ] bb)
           (δ : h ==> h')
           (σσ : gg ==>[ δ ▹ f] gg')
           (Lh : lift_1cell_factor gg)
           (Lh' : lift_1cell_factor gg'),
         lift_2cell_factor σσ Lh Lh'.

    Definition cartesian_1cell_lift_1cell
               (Hff : cartesian_1cell)
               {c : B}
               {cc : D c}
               {h : c --> a}
               (gg : cc -->[ h · f ] bb)
      : lift_1cell_factor gg
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
               (Lh : lift_1cell_factor gg)
               (Lh' : lift_1cell_factor gg')
      : Lh ==>[ δ ] Lh'
      := pr2 Hff c cc h h' gg gg' δ σσ Lh Lh'.

    Definition cartesian_1cell_lift_2cell_commutes
               (Hff : cartesian_1cell)
               {c : B}
               {cc : D c}
               {h h' : c --> a}
               {gg : cc -->[h · f ] bb}
               {gg' : cc -->[h' · f ] bb}
               {δ : h ==> h'}
               (σσ : gg ==>[ δ ▹ f] gg')
               (Lh : lift_1cell_factor gg)
               (Lh' : lift_1cell_factor gg')
      : transportf
          (λ z, _ ==>[ z ] _)
          (id2_right _ @ ! id2_left _ )
          (cartesian_1cell_lift_2cell Hff σσ Lh Lh' ▹▹ ff
           ••
           disp_cell_lift_1cell_factor Lh')
        =
        disp_cell_lift_1cell_factor Lh •• σσ
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

  Section Cartesian2Cell.
    Context {x y : B}
            {xx : D x} {yy : D y}
            {f g : x --> y}
            {ff : xx -->[ f ] yy}
            {gg : xx -->[ g ] yy}
            {α : f ==> g}
            {αα : ff ==>[ α ] gg}
            (Hαα : is_cartesian_2cell αα).

    Definition is_cartesian_2cell_factor
               {h : x --> y}
               (hh : xx -->[ h ] yy)
               (γ : h ==> f)
               (ββ : hh ==>[ γ • α ] gg)
      : hh ==>[ γ ] ff
      := pr11 (Hαα h hh γ ββ).

    Definition is_cartesian_2cell_comm
               {h : x --> y}
               (hh : xx -->[ h ] yy)
               (γ : h ==> f)
               (ββ : hh ==>[ γ • α ] gg)
      : (is_cartesian_2cell_factor hh γ ββ •• αα) = ββ
      := pr21 (Hαα h hh γ ββ).

    Definition is_cartesian_2cell_unique
               {h : x --> y}
               (hh : xx -->[ h ] yy)
               (γ : h ==> f)
               (ββ : hh ==>[ γ • α ] gg)
               {γγ₁ γγ₂ : hh ==>[ γ ] ff}
               (pγγ₁ : (γγ₁ •• αα) = ββ)
               (pγγ₂ : (γγ₂ •• αα) = ββ)
      : γγ₁ = γγ₂.
    Proof.
      exact (maponpaths
               pr1
               (proofirrelevance
                  _
                  (isapropifcontr (Hαα h hh γ ββ))
                  (γγ₁ ,, pγγ₁) (γγ₂ ,, pγγ₂))).
    Qed.
  End Cartesian2Cell.

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

(** 2. Properties of cartesian 2-cells *)
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
  apply (is_cartesian_iso_disp (disp_hom_disp_invertible_2cell_to_iso _ Hαα)).
Defined.

Section Cartesian2CellUnique.
  Context {B : bicat}
          {D : disp_bicat B}
          {x y : B}
          {f g : x --> y}
          {α : f ==> g}
          {xx : D x}
          {yy : D y}
          {ff₁ ff₂ : xx -->[ f ] yy}
          {gg : xx -->[ g ] yy}
          {αα : ff₁ ==>[ α ] gg}
          {ββ : ff₂ ==>[ α ] gg}
          (Hαα : is_cartesian_2cell D αα)
          (Hββ : is_cartesian_2cell D ββ).

  Let m : ff₁ ==>[ id₂ f] ff₂.
  Proof.
    use (is_cartesian_2cell_factor _ Hββ).
    exact (transportb
             (λ z, _ ==>[ z ] _)
             (id2_left _)
             αα).
  Defined.

  Let i : ff₂ ==>[ id₂ f] ff₁.
  Proof.
    use (is_cartesian_2cell_factor _ Hαα).
    exact (transportb
             (λ z, _ ==>[ z ] _)
             (id2_left _)
             ββ).
  Defined.

  Local Lemma is_cartesian_2cell_unique_iso_inv₁
    : m •• i
      =
      transportb
        (λ z, ff₁ ==>[ z ] ff₁)
        (id2_left (id₂ f))
        (disp_id2 ff₁).
  Proof.
    use (is_cartesian_2cell_unique _ Hαα).
    - refine (transportb
                (λ z, _ ==>[ z ] _)
                _
                αα).
      abstract
        (rewrite !vassocl ;
         rewrite !id2_left ;
         apply idpath).
    - rewrite disp_vassocl.
      unfold i.
      rewrite is_cartesian_2cell_comm.
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      unfold m.
      rewrite is_cartesian_2cell_comm.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
    - unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_id2_left.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
  Qed.

  Local Lemma is_cartesian_2cell_unique_iso_inv₂
    : i •• m
      =
      transportb
        (λ z, ff₂ ==>[ z ] ff₂)
        (id2_left (id₂ f))
        (disp_id2 ff₂).
  Proof.
    use (is_cartesian_2cell_unique _ Hββ).
    - refine (transportb
                (λ z, _ ==>[ z ] _)
                _
                ββ).
      abstract
        (rewrite !vassocl ;
         rewrite !id2_left ;
         apply idpath).
    - rewrite disp_vassocl.
      unfold m.
      rewrite is_cartesian_2cell_comm.
      unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite transport_f_f.
      unfold i.
      rewrite is_cartesian_2cell_comm.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
    - unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite disp_id2_left.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
  Qed.

  Definition is_cartesian_2cell_unique_iso
    : disp_invertible_2cell (id2_invertible_2cell _) ff₁ ff₂
    := (m
        ,, i
        ,, is_cartesian_2cell_unique_iso_inv₁
        ,, is_cartesian_2cell_unique_iso_inv₂).

  Definition is_cartesian_2cell_unique_iso_com
    : αα
      =
      transportf
        (λ z, _ ==>[ z ] _)
        (id2_left _)
        (is_cartesian_2cell_unique_iso •• ββ).
  Proof.
    cbn ; unfold m.
    rewrite is_cartesian_2cell_comm.
    unfold transportb.
    rewrite transport_f_f.
    rewrite pathsinv0l.
    apply idpath.
  Qed.
End Cartesian2CellUnique.

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

(** 3. Local Opcleavings *)
Section LocalOpcleaving.
  Context {B : bicat}
          (D : disp_bicat B).

  Definition is_opcartesian_2cell
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
         (γ : g ==> h)
         (ββ : ff ==>[ α • γ ] hh),
       ∃! (γγ : gg ==>[ γ ] hh), (αα •• γγ) = ββ.

  Section OpCartesian2Cell.
    Context {x y : B}
            {xx : D x} {yy : D y}
            {f g : x --> y}
            {ff : xx -->[ f ] yy}
            {gg : xx -->[ g ] yy}
            {α : f ==> g}
            {αα : ff ==>[ α ] gg}
            (Hαα : is_opcartesian_2cell αα).

    Definition is_opcartesian_2cell_factor
               {h : x --> y}
               (hh : xx -->[ h ] yy)
               (γ : g ==> h)
               (ββ : ff ==>[ α • γ ] hh)
      : gg ==>[ γ ] hh
      := pr11 (Hαα h hh γ ββ).

    Definition is_opcartesian_2cell_comm
               {h : x --> y}
               (hh : xx -->[ h ] yy)
               (γ : g ==> h)
               (ββ : ff ==>[ α • γ ] hh)
      : (αα •• is_opcartesian_2cell_factor hh γ ββ) = ββ
      := pr21 (Hαα h hh γ ββ).

    Definition is_opcartesian_2cell_unique
               {h : x --> y}
               (hh : xx -->[ h ] yy)
               (γ : g ==> h)
               (ββ : ff ==>[ α • γ ] hh)
               {γγ₁ γγ₂ : gg ==>[ γ ] hh}
               (pγγ₁ : (αα •• γγ₁) = ββ)
               (pγγ₂ : (αα •• γγ₂) = ββ)
      : γγ₁ = γγ₂.
    Proof.
      exact (maponpaths
               pr1
               (proofirrelevance
                  _
                  (isapropifcontr (Hαα h hh γ ββ))
                  (γγ₁ ,, pγγ₁) (γγ₂ ,, pγγ₂))).
    Qed.
  End OpCartesian2Cell.

  Definition opcartesian_lift_2cell
             {x y : B}
             {xx : D x}
             {yy : D y}
             {f g : x --> y}
             (ff : xx -->[ f ] yy)
             (α : f ==> g)
    : UU
    := ∑ (gg : xx -->[ g ] yy) (αα : ff ==>[ α ] gg), is_opcartesian_2cell αα.

  Definition local_opcleaving
    : UU
    := ∏ (x y : B)
         (xx : D x) (yy : D y)
         (f g : x --> y)
         (ff : xx -->[ f ] yy)
         (α : f ==> g),
       opcartesian_lift_2cell ff α.
End LocalOpcleaving.

(** 4. Properties of opcartesian 2-cells *)
Definition local_opfib
           {B : bicat}
           (D : disp_bicat B)
  : UU
  := ∏ (x y : B)
       (xx : D x)
       (yy : D y),
     opcleaving (disp_hom xx yy).

(** Being a cartesian 2-cell is a proposition *)
Definition isaprop_is_opcartesian_2cell
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
  : isaprop (is_opcartesian_2cell D αα).
Proof.
  repeat (use impred ; intro).
  apply isapropiscontr.
Qed.

(** The two definitions of local cleavings coincide *)
Definition opcartesian_2cell_to_opcartesian
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
           (Hαα : is_opcartesian_2cell D αα)
  : @is_opcartesian _ (disp_hom xx yy) _ _ _ _ _ αα.
Proof.
  intros h γ hh γα.
  apply Hαα.
Qed.

Definition opcartesian_to_opcartesian_2cell
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
           (Hαα : @is_opcartesian _ (disp_hom xx yy) _ _ _ _ _ αα)
  : is_opcartesian_2cell D αα.
Proof.
  intros h hh γ γα.
  apply Hαα.
Qed.

Definition opcartesian_2cell_weq_opcartesian
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
  : (@is_opcartesian _ (disp_hom xx yy) _ _ _ _ _ αα)
    ≃
    is_opcartesian_2cell D αα.
Proof.
  use weqimplimpl.
  - apply opcartesian_to_opcartesian_2cell.
  - apply opcartesian_2cell_to_opcartesian.
  - apply isaprop_is_opcartesian.
  - apply isaprop_is_opcartesian_2cell.
Qed.

Definition local_opcleaving_to_local_opfib
           {B : bicat}
           {D : disp_bicat B}
           (HD : local_opcleaving D)
  : local_opfib D.
Proof.
  intros x y xx yy f g ff α ; cbn in *.
  pose (HD x y xx yy f g ff α) as lift.
  refine (pr1 lift ,, pr12 lift ,, _).
  apply opcartesian_2cell_to_opcartesian.
  exact (pr22 lift).
Defined.

Definition local_opfib_to_local_opcleaving
           {B : bicat}
           {D : disp_bicat B}
           (HD : local_opfib D)
  : local_opcleaving D.
Proof.
  intros x y xx yy f g ff α ; cbn in *.
  pose (HD x y xx yy f g ff α) as lift.
  refine (pr1 lift ,, pr12 lift ,, _).
  apply opcartesian_to_opcartesian_2cell.
  exact (pr22 lift).
Defined.

Definition local_opfib_weq_local_opcleaving
           {B : bicat}
           (D : disp_bicat B)
  : local_opcleaving D ≃ local_opfib D.
Proof.
  use make_weq.
  - exact local_opcleaving_to_local_opfib.
  - use gradth.
    + exact local_opfib_to_local_opcleaving.
    + abstract
        (intro HD ;
         repeat (use funextsec ; intro) ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         apply isaprop_is_opcartesian_2cell).
    + abstract
        (intro HD ;
         repeat (use funextsec ; intro) ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         use total2_paths_f ; [ apply idpath | ] ; cbn ;
         apply isaprop_is_opcartesian).
Defined.

Definition identity_is_opcartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           {x y : B}
           {f : x --> y}
           {xx : D x}
           {yy : D y}
           (ff : xx -->[ f ] yy)
  : is_opcartesian_2cell D (disp_id2 ff).
Proof.
  apply opcartesian_to_opcartesian_2cell.
  exact (@is_opcartesian_id_disp _ (disp_hom xx yy) f ff).
Defined.

Definition vcomp_is_opcartesian_2cell
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
           (Hαα : is_opcartesian_2cell D αα)
           (Hββ : is_opcartesian_2cell D ββ)
  : is_opcartesian_2cell D (αα •• ββ).
Proof.
  apply opcartesian_to_opcartesian_2cell.
  exact (@is_opcartesian_comp_disp
           _ (disp_hom xx yy)
           f ff
           g gg
           h hh
           α β
           αα ββ
           (opcartesian_2cell_to_opcartesian _ Hαα)
           (opcartesian_2cell_to_opcartesian _ Hββ)).
Defined.

Definition invertible_is_opcartesian_2cell
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
  : is_opcartesian_2cell D αα.
Proof.
  apply opcartesian_to_opcartesian_2cell.
  apply (is_opcartesian_iso_disp (disp_hom_disp_invertible_2cell_to_iso _ Hαα)).
Defined.

Definition lwhisker_opcartesian
           {B : bicat}
           (D : disp_bicat B)
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
     is_opcartesian_2cell _ αα → is_opcartesian_2cell _ (hh ◃◃ αα).

Definition rwhisker_opcartesian
           {B : bicat}
           (D : disp_bicat B)
  : UU
  := ∏ (x y z : B)
       (xx : D x) (yy : D y) (zz : D z)
       (f g : x --> y) (h : y --> z)
       (ff : xx -->[ f ] yy)
       (gg : xx -->[ g ] yy)
       (hh : yy -->[ h ] zz)
       (α : f ==> g)
       (αα : ff ==>[ α ] gg),
     is_opcartesian_2cell _ αα → is_opcartesian_2cell _ (αα ▹▹ hh).

Section OpCartesian2CellUnique.
  Context {B : bicat}
          {D : disp_bicat B}
          {x y : B}
          {f g : x --> y}
          {α : f ==> g}
          {xx : D x}
          {yy : D y}
          {ff : xx -->[ f ] yy}
          {gg₁ gg₂ : xx -->[ g ] yy}
          {αα : ff ==>[ α ] gg₁}
          {ββ : ff ==>[ α ] gg₂}
          (Hαα : is_opcartesian_2cell D αα)
          (Hββ : is_opcartesian_2cell D ββ).

  Let m : gg₁ ==>[ id₂ g ] gg₂.
  Proof.
    use (is_opcartesian_2cell_factor _ Hαα).
    exact (transportb
             (λ z, _ ==>[ z ] _)
             (id2_right _)
             ββ).
  Defined.

  Let i : gg₂ ==>[ id₂ g ] gg₁.
  Proof.
    use (is_opcartesian_2cell_factor _ Hββ).
    exact (transportb
             (λ z, _ ==>[ z ] _)
             (id2_right _)
             αα).
  Defined.

  Local Lemma is_opcartesian_2cell_unique_iso_inv₁
    : i •• m
      =
      transportb
        (λ z, _ ==>[ z ] _)
        (id2_left _)
        (disp_id2 _).
  Proof.
    use (is_opcartesian_2cell_unique _ Hββ).
    - refine (transportb
                (λ z, _ ==>[ z ] _)
                _
                ββ).
      abstract
        (rewrite !id2_right ;
         apply idpath).
    - unfold i, m.
      rewrite disp_vassocr.
      rewrite is_opcartesian_2cell_comm.
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite is_opcartesian_2cell_comm.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
    - unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_id2_right.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
  Qed.

  Local Lemma is_opcartesian_2cell_unique_iso_inv₂
    : m •• i
      =
      transportb
        (λ z, _ ==>[ z ] _)
        (id2_left _)
        (disp_id2 gg₁).
  Proof.
    use (is_opcartesian_2cell_unique _ Hαα).
    - refine (transportb
                (λ z, _ ==>[ z ] _)
                _
                αα).
      abstract
        (rewrite !id2_right ;
         apply idpath).
    - unfold i, m.
      rewrite disp_vassocr.
      rewrite is_opcartesian_2cell_comm.
      unfold transportb.
      rewrite disp_mor_transportf_postwhisker.
      rewrite transport_f_f.
      rewrite is_opcartesian_2cell_comm.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
    - unfold transportb.
      rewrite disp_mor_transportf_prewhisker.
      rewrite disp_id2_right.
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply cellset_property.
  Qed.


  Definition is_opcartesian_2cell_unique_iso
    : disp_invertible_2cell (id2_invertible_2cell _) gg₂ gg₁
    := (i
        ,, m
        ,, is_opcartesian_2cell_unique_iso_inv₁
        ,, is_opcartesian_2cell_unique_iso_inv₂).

  Definition is_opcartesian_2cell_unique_iso_com
    : αα
      =
      transportf
        (λ z, _ ==>[ z ] _)
        (id2_right _)
        (ββ •• is_opcartesian_2cell_unique_iso).
  Proof.
    cbn ; unfold i.
    rewrite is_opcartesian_2cell_comm.
    unfold transportb.
    rewrite transport_f_f.
    rewrite pathsinv0l.
    apply idpath.
  Qed.
End OpCartesian2CellUnique.

Definition disp_hcomp_is_opcartesian_2cell
           {B : bicat}
           {D : disp_bicat B}
           (HD_l : lwhisker_opcartesian D)
           (HD_r : rwhisker_opcartesian D)
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
           (Hαα : is_opcartesian_2cell D αα)
           (Hββ : is_opcartesian_2cell D ββ)
  : is_opcartesian_2cell D (disp_hcomp αα ββ).
Proof.
  use vcomp_is_opcartesian_2cell.
  - apply HD_r.
    exact Hαα.
  - apply HD_l.
    exact Hββ.
Defined.
