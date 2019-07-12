Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.

Local Open Scope cat.

Definition rwhisker_of_invertible_2cell
           {B : bicat}
           {x y z : B}
           {f₁ f₂ : x --> y}
           (g : y --> z)
           (α : invertible_2cell f₁ f₂)
  : invertible_2cell (f₁ · g) (f₂ · g).
Proof.
  use make_invertible_2cell.
  - exact (α ▹ g).
  - is_iso.
    apply α.
Defined.

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
               {c : B} {cc : D c}
               {g : c --> b}
               (gg : cc -->[ g ] bb)
               {h : c --> a}
               (α : invertible_2cell (h · f) g)
      : UU
      := ∑ (h' : c --> a)
           (hh' : cc -->[ h' ] aa)
           (β : invertible_2cell h' h),
         disp_invertible_2cell
           (comp_of_invertible_2cell
              (rwhisker_of_invertible_2cell f β)
              α)
           (hh' ;; ff)
           gg.

    Definition mor_lift_1cell
               {c : B} {cc : D c}
               {g : c --> b}
               {gg : cc -->[ g ] bb}
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               (Lh : lift_1cell gg α)
      : c --> a
      := pr1 Lh.

    Definition disp_mor_lift_1cell
               {c : B} {cc : D c}
               {g : c --> b}
               {gg : cc -->[ g ] bb}
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               (Lh : lift_1cell gg α)
      : cc -->[ mor_lift_1cell Lh ] aa
      := pr12 Lh.

    Definition cell_lift_1cell
               {c : B} {cc : D c}
               {g : c --> b}
               {gg : cc -->[ g ] bb}
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               (Lh : lift_1cell gg α)
      : invertible_2cell (mor_lift_1cell Lh) h
      := pr122 Lh.

    Definition disp_cell_lift_1cell
               {c : B} {cc : D c}
               {g : c --> b}
               {gg : cc -->[ g ] bb}
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               (Lh : lift_1cell gg α)
      : disp_invertible_2cell
          (comp_of_invertible_2cell
             (rwhisker_of_invertible_2cell f (cell_lift_1cell Lh))
             α)
          (disp_mor_lift_1cell Lh ;; ff)
          gg
      := pr222 Lh.

    Definition lift_2cell_help
               {c : B} {cc : D c}
               {g g' : c --> b}
               {σ : g ==> g'}
               {gg : cc -->[ g ] bb}
               {gg' : cc -->[ g' ] bb}
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               {h' : c --> a}
               {α' : invertible_2cell (h' · f) g'}
               (Lh : lift_1cell gg α)
               (Lh' : lift_1cell gg' α')
               (δ : h ==> h')
               (Pδ : (δ ▹ f) • α' = α • σ)
      : ((cell_lift_1cell Lh ▹ f) • α) • σ
        =
        (((cell_lift_1cell Lh • δ)
            • (cell_lift_1cell Lh') ^-1) ▹ f)
          • ((cell_lift_1cell Lh' ▹ f) • α').
    Proof.
      refine (!_).
      etrans.
      {
        rewrite !vassocr.
        apply maponpaths_2.
        rewrite !vassocl.
        rewrite rwhisker_vcomp.
        rewrite !vassocl.
        rewrite vcomp_lid, id2_right.
        rewrite <- rwhisker_vcomp.
        apply idpath.
      }
      rewrite !vassocl.
      apply maponpaths.
      exact Pδ.
    Qed.

    Definition lift_2cell
               {c : B} {cc : D c}
               {g g' : c --> b}
               {σ : g ==> g'}
               {gg : cc -->[ g ] bb}
               {gg' : cc -->[ g' ] bb}
               (σσ : gg ==>[ σ ] gg')
               {h : c --> a}
               {α : invertible_2cell (h · f) g}
               {h' : c --> a}
               {α' : invertible_2cell (h' · f) g'}
               (Lh : lift_1cell gg α)
               (Lh' : lift_1cell gg' α')
               (δ : h ==> h')
               (Pδ : (δ ▹ f) • α' = α • σ)
      : UU
      := ∃! (δδ : (pr12 Lh)
                    ==>[ (cell_lift_1cell Lh)
                           • δ
                           • (cell_lift_1cell Lh')^-1 ]
                    pr12 Lh'),
         transportb
           (λ z, _ ==>[ z ] _)
           (lift_2cell_help Lh Lh' δ Pδ)
           (δδ ▹▹ ff •• disp_cell_lift_1cell Lh')
         =
         disp_cell_lift_1cell Lh •• σσ.

    Definition cartesian_1cell
      : UU
      :=
        (∏ (c : B) (cc : D c)
           (g : c --> b)
           (gg : cc -->[ g ] bb)
           (h : c --> a)
           (α : invertible_2cell (h · f) g),
         lift_1cell gg α)
          × (∏ (c : B) (cc : D c)
               (g g' : c --> b)
               (σ : g ==> g')
               (gg : cc -->[ g ] bb)
               (gg' : cc -->[ g' ] bb)
               (σσ : gg ==>[ σ ] gg')
               (h : c --> a)
               (α : invertible_2cell (h · f) g)
               (h' : c --> a)
               (α' : invertible_2cell (h' · f) g')
               (Lh : lift_1cell gg α)
               (Lh' : lift_1cell gg' α')
               (δ : h ==> h')
               (Pδ : (δ ▹ f) • α' = α • σ),
             lift_2cell σσ Lh Lh' δ Pδ).
  End Cartesian1cell.

  Definition cartesian_2cell
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
         (β : h ==> g)
         (ββ : hh ==>[ β ] gg)
         (γ : h ==> f)
         (p : β = γ • α),
       ∃! (γγ : hh ==>[ γ ] ff),
       transportb (λ z, _ ==>[ z ] _) p (γγ •• αα) = ββ.

  Definition locally_fibered
    : UU
    := ∏ (x y : B)
         (xx : D x) (yy : D y)
         (f g : x --> y)
         (ff : xx -->[ f ] yy)
         (gg : xx -->[ g ] yy)
         (α : f ==> g),
       ∑ (αα : ff ==>[ α ] gg), cartesian_2cell αα.

  Definition globally_fibered
    : UU
    := ∏ (a b : B)
         (aa : D a) (bb : D b)
         (f : a --> b),
       ∑ (ff : aa -->[ f ] bb), cartesian_1cell ff.

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
       cartesian_2cell αα → cartesian_2cell (hh ◃◃ αα).

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
       cartesian_2cell αα → cartesian_2cell (αα ▹▹ hh).

  Definition fibration_of_bicats
    : UU
    := locally_fibered
         × globally_fibered
         × lwhisker_cartesian
         × rwhisker_cartesian.
End BicatFibration.
