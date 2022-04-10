(***********************************************************************

 Limits in op2 bicat

 Contents:
 1. Final object
 2. Products
 3. Mirroring pullbacks
 4. Pullbacks in op2 bicat
 5. Comma objects

 ***********************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.
Require Import UniMath.Bicategories.Limits.CommaObjects.

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
