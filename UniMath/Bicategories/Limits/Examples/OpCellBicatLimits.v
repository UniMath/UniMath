(***********************************************************************

 Limits in op2 bicat

 Contents:
 1. Final object
 2. Products
 3. Mirroring pullbacks
 4. Pullbacks in op2 bicat
 5. Comma objects
 6. Eilenberg-Moore objects

 ***********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.CommaObjects.
Require Import UniMath.Bicategories.Limits.EilenbergMooreObjects.
Require Import UniMath.Bicategories.Limits.EilenbergMooreComonad.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.MonadsLax.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.MonadInclusion.

Local Open Scope cat.

(**
 1. Final object
 *)
Definition op2_bicat_bifinal
           {B : bicat}
           {x : B}
           (Hx : is_bifinal x)
  : @is_bifinal (op2_bicat B) x.
Proof.
  use make_is_bifinal.
  - exact (λ y, is_bifinal_1cell_property Hx y).
  - exact (λ y f g, is_bifinal_2cell_property Hx y g f).
  - exact (λ y f g α β, is_bifinal_eq_property Hx y g f α β).
Defined.

(**
 2. Products
 *)
Section ProductOp2.
  Context {B : bicat}
          {a x y : B}
          (p₁ : a --> x)
          (p₂ : a --> y)
          (cone := make_binprod_cone a p₁ p₂)
          (ump : has_binprod_ump cone).

  Definition op2_binprod_cone
    : @binprod_cone (op2_bicat B) x y
    := make_binprod_cone a p₁ p₂.

  Definition has_binprod_ump_1_op_cell
             (q : @binprod_cone (op2_bicat B) x y)
    : binprod_1cell q op2_binprod_cone.
  Proof.
    pose (k₁ := binprod_cone_pr1 q).
    pose (k₂ := binprod_cone_pr2 q).
    use make_binprod_1cell.
    - exact (binprod_ump_1cell ump k₁ k₂).
    - apply weq_op2_invertible_2cell.
      exact (inv_of_invertible_2cell (binprod_ump_1cell_pr1 ump _ k₁ k₂)).
    - apply weq_op2_invertible_2cell.
      exact (inv_of_invertible_2cell (binprod_ump_1cell_pr2 ump _ k₁ k₂)).
  Defined.

  Definition has_binprod_ump_2_op_cell
    : binprod_ump_2 op2_binprod_cone.
  Proof.
    intros q φ ψ α β.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros φ₁ φ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         exact (binprod_ump_2cell_unique_alt
                  ump
                  _ _
                  (pr12 φ₁ @ !(pr12 φ₂))
                  (pr22 φ₁ @ !(pr22 φ₂)))).
    - simple refine (_ ,, _ ,, _).
      + exact (binprod_ump_2cell ump α β).
      + exact (binprod_ump_2cell_pr1 ump α β).
      + exact (binprod_ump_2cell_pr2 ump α β).
  Defined.

  Definition op2_bicat_has_binprod_ump
    : has_binprod_ump op2_binprod_cone.
  Proof.
    split.
    - exact has_binprod_ump_1_op_cell.
    - exact has_binprod_ump_2_op_cell.
  Defined.
End ProductOp2.

(**
 3. Mirroring pullbacks
 *)
Definition mirror_cone
           {B : bicat}
           {x y z : B}
           {f : x --> z}
           {g : y --> z}
           (p : pb_cone f g)
  : pb_cone g f
  := make_pb_cone
       p
       (pb_cone_pr2 p) (pb_cone_pr1 p)
       (inv_of_invertible_2cell (pb_cone_cell p)).

Section Mirroring.
  Context {B : bicat}
          {pb x y z : B}
          {f : x --> z}
          {g : y --> z}
          {p₁ : pb --> x}
          {p₂ : pb --> y}
          {γ : invertible_2cell (p₁ · f) (p₂ · g)}
          (cone := make_pb_cone pb p₁ p₂ γ)
          (pb_sqr : has_pb_ump cone).

  Definition mirror_has_pb_ump
    : has_pb_ump (mirror_cone cone).
  Proof.
    split.
    - intros q.
      use make_pb_1cell.
      + exact (pb_ump_mor pb_sqr (mirror_cone q)).
      + exact (pb_ump_mor_pr2 pb_sqr (mirror_cone q)).
      + exact (pb_ump_mor_pr1 pb_sqr (mirror_cone q)).
      + abstract
          (pose (r := pb_ump_mor_cell pb_sqr (mirror_cone q)) ;
           cbn in r ;
           cbn ;
           rewrite !vassocl ;
           use vcomp_move_L_pM ; [ is_iso | ] ; cbn ;
           use vcomp_move_R_Mp ; [ is_iso | ] ; cbn ;
           rewrite !vassocl ;
           use vcomp_move_L_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
           cbn ;
           use vcomp_move_L_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
           cbn ;
           do 2 (use vcomp_move_L_pM ; [ is_iso | ] ; cbn) ;
           rewrite !vassocl in r ;
           exact (!r)).
    - intros w φ ψ α β q.
      use iscontraprop1.
      + abstract
          (use invproofirrelevance ;
           intros ζ₁ ζ₂ ;
           use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
           refine (pb_ump_eq
                     pb_sqr
                     φ ψ β α
                     _ _ _
                     (pr22 ζ₁) (pr12 ζ₁)
                     (pr22 ζ₂) (pr12 ζ₂)) ;
           rewrite !vassocl ;
           cbn in q ;
           use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
           cbn ;
           rewrite !vassocr ;
           rewrite q ;
           rewrite !vassocl ;
           rewrite lwhisker_vcomp ;
           rewrite vcomp_linv ;
           rewrite lwhisker_id2 ;
           rewrite id2_right ;
           apply idpath).
      + simple refine (_ ,, _ ,, _).
        * use (pb_ump_cell pb_sqr φ ψ β α).
          abstract
            (rewrite !vassocl ;
             cbn in q ;
             use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
             cbn ;
             rewrite !vassocr ;
             rewrite q ;
             rewrite !vassocl ;
             rewrite lwhisker_vcomp ;
             rewrite vcomp_linv ;
             rewrite lwhisker_id2 ;
             rewrite id2_right ;
             apply idpath).
        * exact (pb_ump_cell_pr2 pb_sqr φ ψ β α _).
        * exact (pb_ump_cell_pr1 pb_sqr φ ψ β α _).
  Defined.
End Mirroring.

(**
 4. Pullbacks in op2 bicat
 *)
Definition to_op2_pb_cone
           {B : bicat}
           {pb x y z : B}
           {f : x --> z}
           {g : y --> z}
           {p₁ : pb --> x}
           {p₂ : pb --> y}
           (γ : invertible_2cell (p₁ · f) (p₂ · g))
           (cone := make_pb_cone pb p₁ p₂ γ)
  : @pb_cone (op2_bicat B) _ _ _ f g.
Proof.
  use make_pb_cone.
  - exact pb.
  - exact p₁.
  - exact p₂.
  - apply weq_op2_invertible_2cell.
    exact (inv_of_invertible_2cell γ).
Defined.

Definition from_op2_pb_cone
           {B : bicat}
           {x y z : B}
           {f : x --> z}
           {g : y --> z}
           (cone : @pb_cone (op2_bicat B) _ _ _ f g)
  : pb_cone f g.
Proof.
  use make_pb_cone.
  - exact cone.
  - exact (pb_cone_pr1 cone).
  - exact (pb_cone_pr2 cone).
  - exact (inv_of_invertible_2cell
             (invmap
                (weq_op2_invertible_2cell _ _)
                (pb_cone_cell cone))).
Defined.

Section ToOp2Pullback.
  Context {B : bicat}
          {pb x y z : B}
          {f : x --> z}
          {g : y --> z}
          {p₁ : pb --> x}
          {p₂ : pb --> y}
          (γ : invertible_2cell (p₁ · f) (p₂ · g))
          (cone := make_pb_cone pb p₁ p₂ γ)
          (H : has_pb_ump cone).

  Definition to_op2_pb_ump_1
    : pb_ump_1 (to_op2_pb_cone γ).
  Proof.
    intro q.
    use make_pb_1cell ; cbn.
    - exact (pb_ump_mor H (from_op2_pb_cone q)).
    - apply weq_op2_invertible_2cell.
      exact (inv_of_invertible_2cell
               (pb_ump_mor_pr1 H (from_op2_pb_cone q))).
    - apply weq_op2_invertible_2cell.
      exact (inv_of_invertible_2cell
               (pb_ump_mor_pr2 H (from_op2_pb_cone q))).
    - abstract
        (cbn ;
         pose (pb_ump_mor_cell H (from_op2_pb_cone q)) as p ; cbn in p ;
         use vcomp_move_L_pM ; [ is_iso | ] ;
         use vcomp_move_R_Mp ; [ is_iso | ] ;
         cbn ;
         rewrite !vassocl ;
         use vcomp_move_L_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
         use vcomp_move_L_pM ;
         [ apply from_op2_is_invertible_2cell ;
           apply property_from_invertible_2cell
         | ] ;
         cbn ;
         use vcomp_move_L_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
         use vcomp_move_L_pM ; [ is_iso | ] ;
         cbn ;
         refine (_ @ !p) ;
         rewrite !vassocl ;
         apply idpath).
  Defined.

  Definition to_op2_pb_ump_2
    : pb_ump_2 (to_op2_pb_cone γ).
  Proof.
    intros w φ ψ α β p ; cbn in p.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros ζ₁ ζ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         use (pb_ump_eq H _ _ α β _ _ _ (pr12 ζ₁) (pr22 ζ₁) (pr12 ζ₂) (pr22 ζ₂)) ;
         cbn ; cbn in p ;
         rewrite !vassocl ;
         use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
         cbn ;
         rewrite !vassocr ;
         use vcomp_move_L_Mp ; [ is_iso ; apply property_from_invertible_2cell | ] ;
         cbn ;
         rewrite !vassocl ;
         exact p).
    - simple refine (_ ,, _).
      + use (pb_ump_cell H ψ φ α β).
        abstract
          (cbn ; cbn in p ;
           rewrite !vassocl ;
           use vcomp_move_R_pM ; [ is_iso ; apply property_from_invertible_2cell | ] ;
           cbn ;
           rewrite !vassocr ;
           use vcomp_move_L_Mp ; [ is_iso ; apply property_from_invertible_2cell | ] ;
           cbn ;
           rewrite !vassocl ;
           exact p).
      + split.
        * apply (pb_ump_cell_pr1 H ψ φ α β).
        * apply (pb_ump_cell_pr2 H ψ φ α β).
  Defined.

  Definition to_op2_has_pb_ump
    : has_pb_ump (to_op2_pb_cone γ).
  Proof.
    split.
    - exact to_op2_pb_ump_1.
    - exact to_op2_pb_ump_2.
  Defined.
End ToOp2Pullback.

(**
 5. Comma objects
 *)
Section Op2Comma.
  Context {B : bicat}
          {c x y z : B}
          {f : x --> z}
          {g : y --> z}
          {p₁ : c --> x}
          {p₂ : c --> y}
          {γ : p₁ · f ==> p₂ · g}
          (cone := make_comma_cone c p₁ p₂ γ)
          (comma_sqr : has_comma_ump cone).

  Definition op2_comma_cone
    : @comma_cone (op2_bicat B) _ _ _ g f.
  Proof.
    use make_comma_cone.
    - exact c.
    - exact p₂.
    - exact p₁.
    - exact γ.
  Defined.

  Definition op2_comma_has_comma_ump_1
    : comma_ump_1 op2_comma_cone.
  Proof.
    intro q.
    pose (q' := make_comma_cone
                  _
                  (comma_cone_pr2 q : B ⟦ _ , _ ⟧)
                  (comma_cone_pr1 q)
                  (comma_cone_cell q)).
    use make_comma_1cell ; cbn.
    - exact (comma_ump_mor comma_sqr q').
    - apply weq_op2_invertible_2cell.
      exact (inv_of_invertible_2cell (comma_ump_mor_pr2 comma_sqr q')).
    - apply weq_op2_invertible_2cell.
      exact (inv_of_invertible_2cell (comma_ump_mor_pr1 comma_sqr q')).
    - abstract
        (refine (comma_ump_mor_cell comma_sqr q' @ _) ; cbn ;
         rewrite !vassocl ;
         apply idpath).
  Defined.

  Definition op2_comma_has_comma_ump_2
    : comma_ump_2 op2_comma_cone.
  Proof.
    intros q φ ψ α β p.
    use iscontraprop1.
    - abstract
        (use invproofirrelevance ;
         intros ζ₁ ζ₂ ;
         use subtypePath ; [ intro ; apply isapropdirprod ; apply cellset_property | ] ;
         refine (comma_ump_eq
                   comma_sqr
                   _ _
                   β α
                   _ _ _
                   (pr22 ζ₁) (pr12 ζ₁) (pr22 ζ₂) (pr12 ζ₂)) ;
         cbn ; cbn in p ;
         rewrite !vassocl ;
         exact (!p)).
    - simple refine (_ ,, _ ,, _).
      + use (comma_ump_cell comma_sqr _ _ β α).
        abstract
          (cbn ; cbn in p ;
           rewrite !vassocl ;
           exact (!p)).
      + abstract (apply (comma_ump_cell_pr2 comma_sqr)).
      + abstract (apply (comma_ump_cell_pr1 comma_sqr)).
  Defined.

  Definition op2_comma_has_comma_ump
    : has_comma_ump op2_comma_cone.
  Proof.
    split.
    - exact op2_comma_has_comma_ump_1.
    - exact op2_comma_has_comma_ump_2.
  Defined.
End Op2Comma.

(**
 6. Eilenberg-Moore objects
 *)
Definition em_comnd_cone_to_op2_em_cone
           {B : bicat}
           {m : mnd (op2_bicat B)}
           (e : em_comnd_cone m)
  : em_cone m.
Proof.
  use make_em_cone.
  - exact e.
  - exact (mor_of_em_comnd_cone _ e).
  - exact (lunitor _ • cell_of_em_comnd_cone _ e).
  - abstract
      (cbn ;
       rewrite !vassocr ;
       use vcomp_move_L_Mp ; [ is_iso | ] ; cbn ;
       rewrite !vassocl ;
       apply maponpaths ;
       exact (!(em_comnd_cone_counit _ e))).
  - abstract
      (cbn ;
       rewrite !vassocl ;
       apply maponpaths ;
       refine (_ @ em_comnd_cone_comult _ e) ;
       rewrite !vassocl ;
       apply maponpaths ;
       rewrite !vassocr ;
       rewrite rwhisker_vcomp ;
       rewrite !vassocr ;
       rewrite linvunitor_lunitor ;
       rewrite id2_left ;
       apply idpath).
Defined.

Section ComonadEilenbergMoore.
  Context {B : bicat}
          {m : mnd (op2_bicat B)}
          {e : em_comnd_cone m}
          (He : has_em_comnd_ump m e).

  Section UMP1.
    Context (q : em_cone m).

    Let f : B ⟦ q , ob_of_mnd m ⟧ := mor_of_mnd_mor (mor_of_em_cone _ q).
    Let γ : id₁ _ · f
            ==>
            f · endo_of_mnd m
      := mnd_mor_endo (mor_of_em_cone _ q).

    Definition op2_bicat_has_em_ump_1_mor_unit
      : (linvunitor f • γ) • (f ◃ unit_of_mnd m) = rinvunitor f.
    Proof.
      rewrite !vassocl.
      use vcomp_move_R_pM ; [ is_iso | ] ; cbn.
      use vcomp_move_L_Mp ; [ is_iso | ] ; cbn.
      rewrite !vassocl.
      refine (!(mnd_mor_unit (mor_of_em_cone _ q)) @ _).
      refine (_ @ id2_right _).
      apply maponpaths.
      apply id2_rwhisker.
    Qed.

    Definition op2_bicat_has_em_ump_1_mor_mult
      : ((linvunitor f • γ)
        • ((linvunitor f • γ) ▹ endo_of_mnd m))
        • rassociator f (endo_of_mnd m) (endo_of_mnd m)
        =
        (linvunitor f
        • γ)
        • (f ◃ mult_of_mnd m).
    Proof.
      rewrite !vassocl.
      apply maponpaths.
      assert (γ
              • (((linvunitor _ • γ) ▹ _)
              • rassociator _ _ _)
              =
              (linvunitor _ ▹ _)
              • (rassociator _ _ _
              • ((_ ◃ γ)
              • (lassociator _ _ _
              • ((γ ▹ _)
              • rassociator _ _ _)))))
        as p.
      {
        rewrite <- !rwhisker_vcomp.
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite <- linvunitor_assoc.
        rewrite lwhisker_hcomp.
        rewrite <- linvunitor_natural.
        rewrite !vassocl.
        rewrite linvunitor_assoc.
        rewrite !vassocl.
        rewrite rassociator_lassociator.
        rewrite id2_right.
        apply idpath.
      }
      exact (p @ mnd_mor_mu (mor_of_em_cone _ q)).
    Qed.

    Definition op2_bicat_has_em_ump_1_mor
      : q --> em_comnd_cone_to_op2_em_cone e.
    Proof.
      use (em_comnd_ump_mor m He).
      - exact f.
      - exact (linvunitor _ • γ).
      - exact op2_bicat_has_em_ump_1_mor_unit.
      - exact op2_bicat_has_em_ump_1_mor_mult.
    Defined.

    Definition op2_bicat_has_em_ump_1_cell_data
      : mnd_cell_data
          (# (mnd_incl (op2_bicat B)) op2_bicat_has_em_ump_1_mor
           · mor_of_em_cone m (em_comnd_cone_to_op2_em_cone e))
          (mor_of_em_cone m q)
      := em_comnd_ump_mor_cell
           m He
           f
           (linvunitor _ • γ)
           op2_bicat_has_em_ump_1_mor_unit
           op2_bicat_has_em_ump_1_mor_mult.

    Let δ : (mor_of_mnd_mor (mor_of_em_cone m q) : B ⟦ _ , _ ⟧)
            ==>
            op2_bicat_has_em_ump_1_mor · mor_of_em_comnd_cone m e
      := op2_bicat_has_em_ump_1_cell_data.

    Definition op2_bicat_has_em_ump_1_cell_is_mnd_cell
      : is_mnd_cell op2_bicat_has_em_ump_1_cell_data.
    Proof.
      pose (p := em_comnd_ump_mor_cell_endo
                   m He
                   f
                   (linvunitor _ • γ)
                   op2_bicat_has_em_ump_1_mor_unit
                   op2_bicat_has_em_ump_1_mor_mult).
      use (vcomp_lcancel (linvunitor _)) ; [ is_iso | ].
      refine (_ @ vassocl _ _ _).
      refine (_ @ !p) ; clear p.
      assert (linvunitor _
              • ((_ ◃ δ)
              • (lassociator _ _ _
              • (((lunitor _ • rinvunitor _) ▹ mor_of_em_comnd_cone m e)
              • (rassociator _ _ _
              • ((_ ◃ (lunitor _ • cell_of_em_comnd_cone m e))
              • lassociator _ _ _)))))
              =
              (δ
              • (_ ◃ cell_of_em_comnd_cone m e))
              • lassociator _ _ _)
        as p.
      {
        rewrite !vassocr.
        rewrite lwhisker_hcomp.
        rewrite <- linvunitor_natural.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        etrans.
        {
          do 5 apply maponpaths_2.
          apply (@linvunitor_assoc B).
        }
        rewrite !vassocl.
        etrans.
        {
          apply maponpaths.
          rewrite !vassocr.
          rewrite (@rassociator_lassociator B).
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        rewrite (@rwhisker_vcomp B).
        rewrite !vassocr.
        rewrite linvunitor_lunitor.
        rewrite id2_left.
        rewrite rwhisker_hcomp.
        rewrite <- (@triangle_r_inv B).
        rewrite <- lwhisker_hcomp.
        rewrite (@lwhisker_vcomp B).
        rewrite !vassocr.
        rewrite linvunitor_lunitor.
        rewrite id2_left.
        apply idpath.
      }
      exact p.
    Qed.

    Definition op2_bicat_has_em_ump_1_cell
      : # (mnd_incl (op2_bicat B)) op2_bicat_has_em_ump_1_mor
        · mor_of_em_cone m (em_comnd_cone_to_op2_em_cone e)
        ==>
        mor_of_em_cone m q.
    Proof.
      use make_mnd_cell.
      - exact op2_bicat_has_em_ump_1_cell_data.
      - exact op2_bicat_has_em_ump_1_cell_is_mnd_cell.
    Defined.

    Definition op2_bicat_has_em_ump_1
      : em_cone_mor m q (em_comnd_cone_to_op2_em_cone e).
    Proof.
      use make_em_cone_mor.
      - exact op2_bicat_has_em_ump_1_mor.
      - use make_invertible_2cell.
        + exact op2_bicat_has_em_ump_1_cell.
        + use is_invertible_mnd_2cell.
          apply to_op2_is_invertible_2cell.
          apply (em_comnd_ump_mor_cell_is_invertible m He).
    Defined.
  End UMP1.

  Section UMP2.
    Context {x : op2_bicat B}
            {g₁ g₂ : x --> em_comnd_cone_to_op2_em_cone e}
            (α : # (mnd_incl (op2_bicat B)) g₁
                 · mor_of_em_cone m (em_comnd_cone_to_op2_em_cone e)
                 ==>
                 # (mnd_incl (op2_bicat B)) g₂
                 · mor_of_em_cone m (em_comnd_cone_to_op2_em_cone e)).

    Let αcell : (g₂ · mor_of_em_comnd_cone m e : B ⟦ _ , _ ⟧)
                ==>
                g₁ · mor_of_em_comnd_cone m e
        := cell_of_mnd_cell α.

    Definition op2_bicat_has_em_ump_2_help
      : αcell
        • (_ ◃ cell_of_em_comnd_cone m e)
        • lassociator _ _ _
        =
        (_ ◃ cell_of_em_comnd_cone m e)
        • lassociator _ _ _
        • (αcell ▹ endo_of_mnd m).
    Proof.
      use (vcomp_lcancel (lunitor _)) ; [ is_iso | ].
      assert (lunitor _
              • ((αcell
              • (_ ◃ cell_of_em_comnd_cone m e))
              • lassociator _ _ _)
              =
              (_ ◃ αcell)
              • (lassociator _ _ _
              • (((lunitor _ • rinvunitor _) ▹ mor_of_em_comnd_cone m e)
              • (rassociator _ _ _
              • ((_ ◃ (lunitor _ • cell_of_em_comnd_cone m e))
              • lassociator _ _ _)))))
        as p₁.
      {
        refine (!_).
        etrans.
        {
          apply maponpaths.
          rewrite <- rwhisker_vcomp.
          rewrite !vassocr.
          rewrite lunitor_triangle.
          rewrite !vassocl.
          refine (maponpaths (λ z, _ • z) _).
          rewrite !vassocr.
          rewrite rwhisker_hcomp.
          rewrite <- triangle_r_inv.
          rewrite <- lwhisker_hcomp.
          rewrite lwhisker_vcomp.
          rewrite !vassocr.
          rewrite linvunitor_lunitor.
          rewrite id2_left.
          apply idpath.
        }
        rewrite !vassocr.
        do 2 apply maponpaths_2.
        rewrite vcomp_lunitor.
        apply idpath.
      }
      assert ((lassociator _ _ _
              • (((lunitor _ • rinvunitor _) ▹ mor_of_em_comnd_cone m e)
              • (rassociator _ _ _
              • ((_ ◃ (lunitor _ • cell_of_em_comnd_cone m e))
              • lassociator _ _ _))))
              • (αcell ▹ _)
              =
              lunitor _
              • (((_ ◃ cell_of_em_comnd_cone m e)
              • lassociator _ _ _)
              • (αcell ▹ endo_of_mnd m)))
        as p₂.
      {
        rewrite <- !lwhisker_vcomp.
        rewrite !vassocr.
        do 3 apply maponpaths_2.
        rewrite <- rwhisker_vcomp.
        rewrite !vassocr.
        rewrite lunitor_triangle.
        rewrite !vassocl.
        refine (_ @ id2_right _).
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_hcomp.
        rewrite <- triangle_r_inv.
        rewrite <- lwhisker_hcomp.
        rewrite lwhisker_vcomp.
        rewrite linvunitor_lunitor.
        apply lwhisker_id2.
      }
      exact (p₁ @ mnd_cell_endo α @ p₂).
    Qed.

    Definition op2_bicat_has_em_ump_2_unique
      : isaprop (∑ β : g₁ ==> g₂, ## (mnd_incl (op2_bicat B)) β ▹ _ = α).
    Proof.
      use invproofirrelevance.
      intros β₁ β₂.
      use subtypePath.
      {
        intro.
        apply cellset_property.
      }
      use (em_comnd_ump_eq m He).
      - exact (pr1 β₁ ▹ mor_of_em_comnd_cone m e).
      - rewrite vcomp_whisker.
        rewrite !vassocl.
        rewrite rwhisker_rwhisker.
        apply idpath.
      - apply idpath.
      - exact (!(maponpaths pr1 (pr2 β₁ @ !(pr2 β₂)))).
    Qed.

    Definition op2_bicat_has_em_ump_2_cell
      : g₁ ==> g₂.
    Proof.
      use (em_comnd_ump_cell m He).
      - exact αcell.
      - exact op2_bicat_has_em_ump_2_help.
    Defined.

    Definition op2_bicat_has_em_ump_2_cell_eq
      : ## (mnd_incl (op2_bicat B)) op2_bicat_has_em_ump_2_cell ▹ _ = α.
    Proof.
      use eq_mnd_cell.
      apply (em_comnd_ump_cell_eq m He).
    Qed.
  End UMP2.

  Definition op2_bicat_has_em_ump_2
    : em_ump_2 m (em_comnd_cone_to_op2_em_cone e).
  Proof.
    intros x g₁ g₂ α.
    use iscontraprop1.
    - apply op2_bicat_has_em_ump_2_unique.
    - exact (op2_bicat_has_em_ump_2_cell α ,, op2_bicat_has_em_ump_2_cell_eq α).
  Defined.

  Definition op2_bicat_has_em_ump
    : has_em_ump m (em_comnd_cone_to_op2_em_cone e).
  Proof.
    split.
    - exact op2_bicat_has_em_ump_1.
    - exact op2_bicat_has_em_ump_2.
  Defined.
End ComonadEilenbergMoore.

Definition op2_bicat_has_em
           {B : bicat}
           (HB : has_em_comnd B)
  : bicat_has_em (op2_bicat B)
  := λ m,
     let e := HB m
     in em_comnd_cone_to_op2_em_cone (pr1 e) ,, op2_bicat_has_em_ump (pr2 e).
