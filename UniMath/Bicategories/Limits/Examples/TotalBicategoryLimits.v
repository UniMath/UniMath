(*****************************************************************************

 Limits in the total bicategory

 We consider one way to construct limits in the total bicategory. For this
 construction, we assume that all displayed 2-cells are invertible and that
 the types of displayed invertible 2-cells over some 2-cell is contractible.

 Contents
 1. Final objects
 2. Products
 3. Pullbacks

 *****************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.Bicategories.Limits.Final.
Require Import UniMath.Bicategories.Limits.Products.
Require Import UniMath.Bicategories.Limits.Pullbacks.

Local Open Scope cat.

Section LimitsTotalBicat.
  Context {B : bicat}
          (D : disp_bicat B)
          (HD₁ : disp_2cells_isaprop D)
          (HD₂ : ∏ (x y : B)
                   (f g : x --> y)
                   (α : f ==> g)
                   (xx : D x)
                   (yy : D y)
                   (ff : xx -->[ f ] yy)
                   (gg : xx -->[ g ] yy),
                 ff ==>[ α ] gg)
          (HD₃ : disp_locally_groupoid D).

  Definition is_invertible_in_total
             {x y : total_bicat D}
             {f g : x --> y}
             {α : f ==> g}
             (Hα : is_invertible_2cell (pr1 α))
    : is_invertible_2cell α.
  Proof.
    use is_invertible_disp_to_total.
    refine (Hα ,, _).
    exact (HD₃ (pr1 x) (pr1 y) (pr1 f) (pr1 g) (pr1 α ,, Hα)
               (pr2 x) (pr2 y) (pr2 f) (pr2 g) (pr2 α)).
  Defined.

  Definition invertible_in_total
             {x y : total_bicat D}
             {f g : x --> y}
             (α : invertible_2cell (pr1 f) (pr1 g))
    : invertible_2cell f g.
  Proof.
    use make_invertible_2cell.
    - refine (pr1 α ,, _).
      apply HD₂.
    - use is_invertible_in_total.
      apply property_from_invertible_2cell.
  Defined.

  (**
   1. Final objects
   *)
  Definition disp_bifinal_obj
             (HB : bifinal_obj B)
    : UU
    := ∑ (i : D (pr1 HB)),
       ∏ (x : B)
         (xx : D x),
       xx -->[ is_bifinal_1cell_property (pr2 HB) x ] i.

  Definition total_bicat_final
             (HB : bifinal_obj B)
             (HD₄ : disp_bifinal_obj HB)
    : bifinal_obj (total_bicat D).
  Proof.
    simple refine (_ ,, _).
    - exact (pr1 HB ,, pr1 HD₄).
    - use make_is_bifinal.
      + exact (λ x,
              is_bifinal_1cell_property (pr2 HB) (pr1 x)
              ,,
              pr2 HD₄ (pr1 x) (pr2 x)).
      + refine (λ x f g,
                 is_bifinal_2cell_property (pr2 HB) _ (pr1 f) (pr1 g)
                   ,,
                   _).
        apply HD₂.
      + abstract
          (intros x f g α β ;
           use subtypePath ; [ intro ; apply HD₁ | ] ;
           apply (is_bifinal_eq_property (pr2 HB))).
  Defined.

  Definition disp_bifinal_obj_stronger
             (HB : bifinal_obj B)
    : UU
    := ∑ (i : D (pr1 HB))
       (j : ∏ (x : B)
         (xx : D x),
           xx -->[ is_bifinal_1cell_property (pr2 HB) x ] i),
      ∏ (x : B)(xx : D x)(f g : x --> pr1 HB)(ff : xx -->[f] i)(gg : xx -->[g] i),
      ff ==>[ is_bifinal_2cell_property (pr2 HB) x f g] gg.

  Definition total_bicat_final_stronger
             (HB : bifinal_obj B)
             (HD₄ : disp_bifinal_obj_stronger HB)
    : bifinal_obj (total_bicat D).
  Proof.
    simple refine (_ ,, _).
    - exact (pr1 HB ,, pr1 HD₄).
    - use make_is_bifinal.
      + exact (λ x,
              is_bifinal_1cell_property (pr2 HB) (pr1 x)
              ,,
              pr12 HD₄ (pr1 x) (pr2 x)).
      + refine (λ x f g,
                 is_bifinal_2cell_property (pr2 HB) _ (pr1 f) (pr1 g)
                   ,,
                   _).
        apply (pr22 HD₄).
      + abstract
          (intros x f g α β ;
           use subtypePath ; [ intro ; apply HD₁ | ] ;
           apply (is_bifinal_eq_property (pr2 HB))).
  Defined.

  (**
   2. Products
   *)
  Definition disp_has_binprod
             (HB : has_binprod B)
    : UU
    := ∏ (x y : total_bicat D),
       let p_cone : binprod_cone (pr1 x) (pr1 y)
         := pr1 (HB (pr1 x) (pr1 y))
       in
       let Hp_cone : has_binprod_ump p_cone
         := pr2 (HB (pr1 x) (pr1 y))
       in
       ∑ (prod : D (binprod_cone_obj p_cone)),
       prod -->[ binprod_cone_pr1 p_cone ] pr2 x
       ×
       prod -->[ binprod_cone_pr2 p_cone ] pr2 y
       ×
       ∏ (z : total_bicat D)
         (f : z --> x)
         (g : z --> y),
       pr2 z -->[ binprod_ump_1cell Hp_cone (pr1 f) (pr1 g) ] prod.

  Section TotalBicatProd.
    Context (HB : has_binprod B)
            (x y : total_bicat D)
            (HD₄ : disp_has_binprod HB).

    Let p_cone : binprod_cone (pr1 x) (pr1 y)
      := pr1 (HB (pr1 x) (pr1 y)).

    Let Hp_cone : has_binprod_ump p_cone
      := pr2 (HB (pr1 x) (pr1 y)).

    Definition total_bicat_prod_cone
      : binprod_cone x y.
    Proof.
      use make_binprod_cone.
      - exact (binprod_cone_obj p_cone ,, pr1 (HD₄ x y)).
      - exact (binprod_cone_pr1 p_cone ,, pr12 (HD₄ x y)).
      - exact (binprod_cone_pr2 p_cone ,, pr122 (HD₄ x y)).
    Defined.

    Definition total_bicat_binprod_ump_1
      : binprod_ump_1 total_bicat_prod_cone.
    Proof.
      intro q.
      use make_binprod_1cell.
      - simple refine (_ ,, _).
        + exact (binprod_ump_1cell
                   Hp_cone
                   (pr1 (binprod_cone_pr1 q))
                   (pr1 (binprod_cone_pr2 q))).
        + exact (pr222 (HD₄ x y) _ (binprod_cone_pr1 q) (binprod_cone_pr2 q)).
      - use invertible_in_total.
        apply binprod_ump_1cell_pr1.
      - use invertible_in_total.
        apply binprod_ump_1cell_pr2.
    Defined.

    Definition total_bicat_binprod_ump_2
      : has_binprod_ump_2_cell total_bicat_prod_cone.
    Proof.
      intros z φ ψ α β.
      simple refine (_ ,, _).
      - exact (binprod_ump_2cell Hp_cone (pr1 α) (pr1 β)).
      - apply HD₂.
    Defined.
  End TotalBicatProd.

  Definition total_bicat_prod
             (HB : has_binprod B)
             (HD₄ : disp_has_binprod HB)
    : has_binprod (total_bicat D).
  Proof.
    intros x y.
    simple refine (_ ,, _).
    - exact (total_bicat_prod_cone HB x y HD₄).
    - use make_binprod_ump.
      + exact (total_bicat_binprod_ump_1 HB x y HD₄).
      + exact (total_bicat_binprod_ump_2 HB x y HD₄).
      + abstract
          (intros z φ ψ α β ;
           use subtypePath ; [ intro ; apply HD₁ | ] ;
           apply binprod_ump_2cell_pr1).
      + abstract
          (intros z φ ψ α β ;
           use subtypePath ; [ intro ; apply HD₁ | ] ;
           apply binprod_ump_2cell_pr2).
      + abstract
          (intros z φ ψ α β γ δ p₁ p₂ q₁ q₂ ;
           use subtypePath ; [ intro ; apply HD₁ | ] ;
           exact (binprod_ump_2cell_unique
                    (pr2 (HB (pr1 x) (pr1 y)))
                    (pr1 α) (pr1 β)
                    _ _
                    (maponpaths pr1 p₁)
                    (maponpaths pr1 p₂)
                    (maponpaths pr1 q₁)
                    (maponpaths pr1 q₂))).
  Defined.

  (**
   3. Pullbacks
   *)
  Definition total_pb_cone_help_cone
             {x y z : total_bicat D}
             {f : x --> z}
             {g : y --> z}
             (q : pb_cone f g)
    : pb_cone (pr1 f) (pr1 g)
    := make_pb_cone
         _
         (pr1 (pb_cone_pr1 q))
         (pr1 (pb_cone_pr2 q))
         (make_invertible_2cell
            (pr1_invertible_2cell_total _ (pb_cone_cell q))).

  Definition disp_has_pb
             (HB : has_pb B)
    : UU
    := ∏ (x y z : total_bicat D)
         (f : x --> z)
         (g : y --> z),
       let p_cone : pb_cone (pr1 f) (pr1 g)
         := pr1 (HB _ _ _ (pr1 f) (pr1 g))
       in
       let Hp_cone : has_pb_ump p_cone
         := pr2 (HB _ _ _ (pr1 f) (pr1 g))
       in
       ∑ (pb : D (pb_cone_obj p_cone)),
       pb -->[ pb_cone_pr1 p_cone ] pr2 x
       ×
       pb -->[ pb_cone_pr2 p_cone ] pr2 y
       ×
       ∏ (q : pb_cone f g),
       pr21 q -->[ pb_ump_mor Hp_cone (total_pb_cone_help_cone q) ] pb.

  Section TotalBicatPullback.
    Context (HB : has_pb B)
            (HD₄ : disp_has_pb HB)
            {x y z : total_bicat D}
            (f : x --> z)
            (g : y --> z).

    Let p_cone : pb_cone (pr1 f) (pr1 g)
      := pr1 (HB _ _ _ (pr1 f) (pr1 g)).

    Let Hp_cone : has_pb_ump p_cone
      := pr2 (HB _ _ _ (pr1 f) (pr1 g)).

    Definition total_pb_cone
      : pb_cone f g.
    Proof.
      use make_pb_cone.
      - exact (pb_cone_obj p_cone ,, pr1 (HD₄ x y z f g)).
      - exact (pb_cone_pr1 p_cone ,, pr12 (HD₄ x y z f g)).
      - exact (pb_cone_pr2 p_cone ,, pr122 (HD₄ x y z f g)).
      - apply invertible_in_total.
        exact (pb_cone_cell p_cone).
    Defined.

    Section UMP1.
      Context (q : pb_cone f g).

      Definition total_pb_cone_ump1
        : pb_1cell q total_pb_cone.
      Proof.
        use make_pb_1cell.
        - exact (pb_ump_mor Hp_cone (total_pb_cone_help_cone q)
                 ,,
                 pr222 (HD₄ x y z f g) q).
        - use invertible_in_total.
          exact (pb_ump_mor_pr1
                   Hp_cone
                   (total_pb_cone_help_cone q)).
        - use invertible_in_total.
          exact (pb_ump_mor_pr2
                   Hp_cone
                   (total_pb_cone_help_cone q)).
        - abstract
            (use subtypePath ; [ intro ; apply HD₁ | ] ;
             exact (pb_ump_mor_cell
                      Hp_cone
                      (total_pb_cone_help_cone q))).
      Defined.

    End UMP1.

    Section UMP2.
      Context {w : total_bicat D}
              (φ ψ : w --> total_pb_cone)
              (α : φ · pb_cone_pr1 total_pb_cone
                   ==>
                   ψ · pb_cone_pr1 total_pb_cone)
              (β : φ · pb_cone_pr2 total_pb_cone
                   ==>
                   ψ · pb_cone_pr2 total_pb_cone)
              (p : (φ ◃ pb_cone_cell total_pb_cone)
                   • lassociator _ _ _
                   • (β ▹ g)
                   • rassociator _ _ _
                   =
                   lassociator _ _ _
                   • (α ▹ f)
                   • rassociator _ _ _
                   • (ψ ◃ pb_cone_cell total_pb_cone)).

      Definition total_pb_cone_unique
        : isaprop
            (∑ (γ : φ ==> ψ),
              γ ▹ pb_cone_pr1 total_pb_cone = α
              ×
              γ ▹ pb_cone_pr2 total_pb_cone = β).
      Proof.
        use invproofirrelevance.
        intros γ₁ γ₂.
        use subtypePath.
        {
          intro.
          apply isapropdirprod ; apply cellset_property.
        }
        use subtypePath.
        {
          intro.
          apply HD₁.
        }
        exact (pb_ump_eq
                 Hp_cone
                 (pr1 φ) (pr1 ψ)
                 (pr1 α) (pr1 β)
                 (maponpaths pr1 p)
                 _ _
                 (maponpaths pr1 (pr12 γ₁))
                 (maponpaths pr1 (pr22 γ₁))
                 (maponpaths pr1 (pr12 γ₂))
                 (maponpaths pr1 (pr22 γ₂))).
      Qed.

      Definition total_pb_cone_ump2
        : ∑ (γ : φ ==> ψ),
          γ ▹ pb_cone_pr1 total_pb_cone = α
          ×
          γ ▹ pb_cone_pr2 total_pb_cone = β.
      Proof.
        simple refine (_ ,, _ ,, _).
        - simple refine (_ ,, _).
          + exact (pb_ump_cell
                     Hp_cone
                     (pr1 φ) (pr1 ψ)
                     (pr1 α) (pr1 β)
                     (maponpaths pr1 p)).
          + apply HD₂.
        - abstract
            (use subtypePath ; [ intro ; apply HD₁ | ] ;
             apply pb_ump_cell_pr1).
        - abstract
            (use subtypePath ; [ intro ; apply HD₁ | ] ;
             apply pb_ump_cell_pr2).
      Defined.

      Definition total_pb_cone_ump2_unique
        : ∃! (γ : φ ==> ψ),
          γ ▹ pb_cone_pr1 total_pb_cone = α
          ×
          γ ▹ pb_cone_pr2 total_pb_cone = β.
      Proof.
        use iscontraprop1.
        - exact total_pb_cone_unique.
        - exact total_pb_cone_ump2.
      Defined.
    End UMP2.
  End TotalBicatPullback.

  Definition total_bicat_has_pb
             (HB : has_pb B)
             (HD₄ : disp_has_pb HB)
    : has_pb (total_bicat D).
  Proof.
    intros x y z f g.
    simple refine (_ ,, _).
    - exact (total_pb_cone HB HD₄ f g).
    - simple refine (_ ,, _).
      + intro q.
        apply total_pb_cone_ump1.
      + simpl.
        intros w φ ψ α β p.
        apply total_pb_cone_ump2_unique.
        exact p.
  Defined.
End LimitsTotalBicat.
