(*************************************************************************************************

 The 2-sided displayed category of parametrized morphisms

 We define a 2-sided displayed of parametrized morphisms. A parametrized morphisms from an
 object `a` to `b` in a monoidal category `M` consists of an object `x` (representing the
 parameters) and a morphism `x ⊗ a --> b`. We also give the necessary operations to show that
 this is a double category.

 Reference
 - "Effectful semantics in bicategories: strong, commutative, and concurrent pseudomonads" by
   Paquet and Saville

 Contents
 1. The 2-sided displayed category of parametrized morphisms
 2. Univalence
 3. Builders and accessors
 4. Isomorphisms of parametrized morphisms
 5. The identity parametrized morphism
 6. The composition of parametrized morphisms
 7. The left unitor of parametrized morphisms
 8. The right unitor of parametrized morphisms
 9. The associator of parametrized morphisms
 10. Companions and conjoints

 *************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Setcategories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Projection.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.TwoSidedDispCat.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Isos.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Strictness.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Discrete.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Total.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.Constant.
Require Import UniMath.CategoryTheory.TwoSidedDisplayedCats.Examples.DispCatOnTwoSidedDispCat.

Import MonoidalNotations.

Local Open Scope cat.
Local Open Scope moncat.

Section Para.
  Context (M : monoidal_cat).

  (** * 1. The 2-sided displayed category of parametrized morphisms *)
  Definition para_ob
    : twosided_disp_cat M M
    := constant_twosided_disp_cat M M M.

  Definition disp_cat_para_mor_ob_mor
    : disp_cat_ob_mor (total_twosided_disp_category para_ob).
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, pr22 x ⊗ pr1 x --> pr12 x).
    - exact (λ x y φ ψ fgh, (pr22 fgh #⊗ pr1 fgh) · ψ = φ · pr12 fgh).
  Defined.

  Definition disp_cat_para_mor_id_comp
    : disp_cat_id_comp
        (total_twosided_disp_category para_ob)
        disp_cat_para_mor_ob_mor.
  Proof.
    split ; cbn.
    - intros.
      rewrite tensor_id_id.
      rewrite id_left, id_right.
      apply idpath.
    - intros x y z f g φ ψ χ p q.
      rewrite tensor_comp_mor.
      rewrite !assoc'.
      rewrite q.
      rewrite !assoc.
      apply maponpaths_2.
      exact p.
  Qed.

  Definition disp_cat_para_mor_data
    : disp_cat_data (total_twosided_disp_category para_ob).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_para_mor_ob_mor.
    - exact disp_cat_para_mor_id_comp.
  Defined.

  Proposition disp_cat_para_mor_axioms
    : disp_cat_axioms
        (total_twosided_disp_category para_ob)
        disp_cat_para_mor_data.
  Proof.
    repeat split ; intros.
    - apply homset_property.
    - apply homset_property.
    - apply homset_property.
    - apply isasetaprop.
      apply homset_property.
  Qed.

  Definition disp_cat_para_mor
    : disp_cat (total_twosided_disp_category para_ob).
  Proof.
    simple refine (_ ,, _).
    - exact disp_cat_para_mor_data.
    - exact disp_cat_para_mor_axioms.
  Defined.

  Definition para_twosided_disp_cat
    : twosided_disp_cat M M
    := sigma_twosided_disp_cat _ disp_cat_para_mor.

  (** * 2. Univalence *)
  Definition is_univalent_para_mor
    : is_univalent_disp disp_cat_para_mor.
  Proof.
    intros x y p f g.
    induction p.
    use isweqimplimpl.
    - intro p ; cbn.
      pose (pr1 p) as q ; cbn in q.
      rewrite tensor_id_id in q.
      rewrite id_left, id_right in q.
      exact (!q).
    - apply homset_property.
    - use isaproptotal2.
      + intro.
        apply isaprop_is_z_iso_disp.
      + intros.
        apply homset_property.
  Qed.

  Definition is_univalent_para_twosided_disp_cat
             (HM : is_univalent M)
    : is_univalent_twosided_disp_cat para_twosided_disp_cat.
  Proof.
    use is_univalent_sigma_of_twosided_disp_cat.
    - use is_univalent_constant_twosided_disp_cat.
      exact HM.
    - exact is_univalent_para_mor.
  Defined.

  Definition is_strict_para_twosided_disp_cat
             (HM : is_setcategory M)
    : is_strict_twosided_disp_cat para_twosided_disp_cat.
  Proof.
    intros x y ; cbn.
    use isaset_total2.
    - apply HM.
    - intro z.
      apply homset_property.
  Qed.

  (** * 3. Builders and accessors *)
  Definition para_mor
             (a b : M)
    : UU
    := para_twosided_disp_cat a b.

  Definition make_para_mor
             {a b x : M}
             (f : x ⊗ a --> b)
    : para_mor a b
    := x ,, f.

  Definition ob_of_para_mor
             {a b : M}
             (f : para_mor a b)
    : M
    := pr1 f.

  Coercion mor_of_para_mor
           {a b : M}
           (f : para_mor a b)
    : ob_of_para_mor f ⊗ a --> b.
  Proof.
    exact (pr2 f).
  Defined.

  Definition para_sqr
             {a₁ a₂ b₁ b₂ : M}
             (v : a₁ --> a₂)
             (w : b₁ --> b₂)
             (f : para_mor a₁ b₁)
             (g : para_mor a₂ b₂)
    : UU
    := f -->[ v ][ w ] g.

  Definition para_sqr_laws
             {a₁ a₂ b₁ b₂ : M}
             (v : a₁ --> a₂)
             (w : b₁ --> b₂)
             (f : para_mor a₁ b₁)
             (g : para_mor a₂ b₂)
             (φ : ob_of_para_mor f --> ob_of_para_mor g)
    : UU
    := φ #⊗ v · g = f · w.

  Definition make_para_sqr
             {a₁ a₂ b₁ b₂ : M}
             (v : a₁ --> a₂)
             (w : b₁ --> b₂)
             (f : para_mor a₁ b₁)
             (g : para_mor a₂ b₂)
             (φ : ob_of_para_mor f --> ob_of_para_mor g)
             (H : para_sqr_laws v w f g φ)
    : para_sqr v w f g
    := φ ,, H.

  Coercion mor_of_para_sqr
           {a₁ a₂ b₁ b₂ : M}
           {v : a₁ --> a₂}
           {w : b₁ --> b₂}
           {f : para_mor a₁ b₁}
           {g : para_mor a₂ b₂}
           (φ : para_sqr v w f g)
    : ob_of_para_mor f --> ob_of_para_mor g.
  Proof.
    exact (pr1 φ).
  Defined.

  Definition eq_of_para_sqr
             {a₁ a₂ b₁ b₂ : M}
             {v : a₁ --> a₂}
             {w : b₁ --> b₂}
             {f : para_mor a₁ b₁}
             {g : para_mor a₂ b₂}
             (φ : para_sqr v w f g)
    : φ #⊗ v · g = f · w.
  Proof.
    exact (pr2 φ).
  Qed.

  Proposition path_para_sqr
              {a₁ a₂ b₁ b₂ : M}
              {v : a₁ --> a₂}
              {w : b₁ --> b₂}
              {f : para_mor a₁ b₁}
              {g : para_mor a₂ b₂}
              {φ ψ : para_sqr v w f g}
              (p : mor_of_para_sqr φ = mor_of_para_sqr ψ)
    : φ = ψ.
  Proof.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    exact p.
  Qed.

  (** * 4. Isomorphisms of parametrized morphisms *)
  Proposition transportf_disp_mor2_para
              {a₁ a₂ b₁ b₂ : M}
              {v v' : a₁ --> a₂}
              (p : v = v')
              {w w' : b₁ --> b₂}
              (q : w = w')
              {f : para_mor a₁ b₁}
              {g : para_mor a₂ b₂}
              (φ : para_sqr v w f g)
    : mor_of_para_sqr (transportf_disp_mor2 p q φ) = φ.
  Proof.
    induction p, q.
    apply idpath.
  Qed.

  Proposition transportb_disp_mor2_para
              {a₁ a₂ b₁ b₂ : M}
              {v v' : a₁ --> a₂}
              (p : v' = v)
              {w w' : b₁ --> b₂}
              (q : w' = w)
              {f : para_mor a₁ b₁}
              {g : para_mor a₂ b₂}
              (φ : para_sqr v w f g)
    : mor_of_para_sqr (transportb_disp_mor2 p q φ) = φ.
  Proof.
    induction p, q.
    apply idpath.
  Qed.

  Section IsoSquare.
    Context {a b : M}
            {f : para_mor a b}
            {g : para_mor a b}
            (φ : para_sqr (identity _) (identity _) f g)
            (Hφ : is_z_isomorphism (mor_of_para_sqr φ)).

    Let i : z_iso (ob_of_para_mor f) (ob_of_para_mor g)
      := make_z_iso _ _ Hφ.

    Definition para_sqr_inv
      : para_sqr (identity _) (identity _) g f.
    Proof.
      use make_para_sqr.
      - exact (inv_from_z_iso i).
      - abstract
          (unfold para_sqr_laws ;
           rewrite id_right ;
           pose (eq_of_para_sqr φ) as p ;
           rewrite id_right in p ;
           rewrite <- p ;
           rewrite !assoc ;
           rewrite <- tensor_comp_mor ;
           rewrite id_right ;
           refine (_ @ id_left _) ;
           apply maponpaths_2 ;
           refine (_ @ tensor_id_id _ _) ;
           apply maponpaths_2 ;
           exact (z_iso_after_z_iso_inv i)).
    Defined.

    Definition is_iso_twosided_para_sqr
      : is_iso_twosided_disp
          (identity_is_z_iso _)
          (identity_is_z_iso _)
          φ.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact para_sqr_inv.
      - abstract
          (use path_para_sqr ;
           rewrite transportb_disp_mor2_para ; cbn ;
           exact (z_iso_inv_after_z_iso i)).
      - abstract
          (use path_para_sqr ;
           rewrite transportb_disp_mor2_para ; cbn ;
           exact (z_iso_after_z_iso_inv i)).
    Defined.
  End IsoSquare.

  (** * 5. The identity parametrized morphism *)
  Definition id_para_mor
             (a : M)
    : para_mor a a.
  Proof.
    use make_para_mor.
    - exact (I_{M}).
    - apply mon_lunitor.
  Defined.

  Definition id_para_sqr
             {x y : M}
             (f : x --> y)
    : para_sqr f f (id_para_mor x) (id_para_mor y).
  Proof.
    use make_para_sqr.
    - apply identity.
    - abstract
        (unfold para_sqr_laws ; cbn ;
         rewrite tensor_lunitor ;
         apply idpath).
  Defined.

  (** * 6. The composition of parametrized morphisms *)
  Definition comp_para_mor
             {x y z : M}
             (s : para_mor x y)
             (t : para_mor y z)
    : para_mor x z.
  Proof.
    use make_para_mor.
    - exact (ob_of_para_mor t ⊗ ob_of_para_mor s).
    - exact (mon_lassociator _ _ _ · (identity _ #⊗ s) · t).
  Defined.

  Definition comp_para_sqr
             {x₁ x₂ y₁ y₂ z₁ z₂ : M}
             {v₁ : x₁ --> x₂} {v₂ : y₁ --> y₂} {v₃ : z₁ --> z₂}
             {f₁ : para_mor x₁ y₁}
             {f₂ : para_mor y₁ z₁}
             {g₁ : para_mor x₂ y₂}
             {g₂ : para_mor y₂ z₂}
             (φ : para_sqr v₁ v₂ f₁ g₁)
             (ψ : para_sqr v₂ v₃ f₂ g₂)
    : para_sqr
        v₁ v₃
        (comp_para_mor f₁ f₂) (comp_para_mor g₁ g₂).
  Proof.
    use make_para_sqr.
    - exact (ψ #⊗ φ).
    - abstract
        (unfold para_sqr_laws ; cbn ;
         rewrite !assoc ;
         rewrite tensor_lassociator ;
         rewrite !assoc' ;
         apply maponpaths ;
         rewrite !assoc ;
         rewrite <- tensor_comp_mor ;
         rewrite eq_of_para_sqr ;
         rewrite id_right ;
         rewrite tensor_comp_l_id_l ;
         rewrite !assoc' ;
         rewrite eq_of_para_sqr ;
         apply idpath).
  Defined.

  (** * 7. The left unitor of parametrized morphisms *)
  Definition para_mor_lunitor
             {x y : M}
             (f : para_mor x y)
    : para_sqr
        (identity _) (identity _)
        (comp_para_mor (id_para_mor _) f)
        f.
  Proof.
    use make_para_sqr.
    - apply mon_runitor.
    - abstract
        (unfold para_sqr_laws ; cbn ;
         rewrite id_right ;
         rewrite mon_triangle ;
         rewrite !assoc' ;
         apply idpath).
  Defined.

  Definition is_z_iso_para_mor_lunitor
             {x y : M}
             (f : para_mor x y)
    : is_z_isomorphism (para_mor_lunitor f).
  Proof.
    use make_is_z_isomorphism.
    - apply mon_rinvunitor.
    - abstract
        (split ; [ apply mon_runitor_rinvunitor | apply mon_rinvunitor_runitor ]).
  Defined.

  (** * 8. The right unitor of parametrized morphisms *)
  Definition para_mor_runitor
             {x y : M}
             (f : para_mor x y)
    : para_sqr
        (identity _) (identity _)
        (comp_para_mor f (id_para_mor _))
        f.
  Proof.
    use make_para_sqr.
    - apply mon_lunitor.
    - abstract
        (unfold para_sqr_laws ; cbn ;
         rewrite id_right ;
         rewrite !assoc' ;
         rewrite tensor_lunitor ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         rewrite mon_lunitor_triangle ;
         apply idpath).
  Defined.

  Definition is_z_iso_para_mor_runitor
             {x y : M}
             (f : para_mor x y)
    : is_z_isomorphism (para_mor_runitor f).
  Proof.
    use make_is_z_isomorphism.
    - apply mon_linvunitor.
    - abstract
        (split ; [ apply mon_lunitor_linvunitor | apply mon_linvunitor_lunitor ]).
  Defined.

  (** * 9. The associator of parametrized morphisms *)
  Definition para_mor_associator
             {w x y z : M}
             (f : para_mor w x)
             (g : para_mor x y)
             (h : para_mor y z)
    : para_sqr
        (identity _) (identity _)
        (comp_para_mor f (comp_para_mor g h))
        (comp_para_mor (comp_para_mor f g) h).
  Proof.
    use make_para_sqr.
    - apply mon_lassociator.
    - abstract
        (unfold para_sqr_laws ; cbn ;
         rewrite id_right ;
         rewrite !tensor_comp_l_id_l ;
         rewrite !assoc ;
         rewrite <- mon_lassociator_lassociator ;
         rewrite !assoc' ;
         apply maponpaths ;
         rewrite !assoc ;
         rewrite <- tensor_lassociator ;
         rewrite tensor_id_id ;
         apply idpath).
  Defined.

  Definition is_z_iso_para_mor_associator
             {w x y z : M}
             (f : para_mor w x)
             (g : para_mor x y)
             (h : para_mor y z)
    : is_z_isomorphism (para_mor_associator f g h).
  Proof.
    use make_is_z_isomorphism.
    - apply mon_rassociator.
    - abstract
        (split ; [ apply mon_lassociator_rassociator | apply mon_rassociator_lassociator ]).
  Defined.

  (** * 10. Companions and conjoints *)
  Section Companions.
    Context {x y : M}
            (f : x --> y).

    Definition para_companion
      : para_mor x y.
    Proof.
      use make_para_mor.
      - exact (I_{M}).
      - exact (mon_lunitor _ · f).
    Defined.

    Definition para_companion_unit
      : para_sqr f (identity y) para_companion (id_para_mor y).
    Proof.
      use make_para_sqr.
      - apply identity.
      - abstract
          (unfold para_sqr_laws ; cbn ;
           rewrite id_right ;
           rewrite tensor_lunitor ;
           apply idpath).
    Defined.

    Definition para_companion_counit
      : para_sqr (identity x) f (id_para_mor x) para_companion.
    Proof.
      use make_para_sqr.
      - apply identity.
      - abstract
          (unfold para_sqr_laws ; cbn ;
           rewrite tensor_id_id ;
           apply id_left).
    Defined.
  End Companions.

  Section Conjoints.
    Context {x y : M}
            (f : z_iso y x).

    Definition para_conjoint
      : para_mor x y.
    Proof.
      use make_para_mor.
      - exact (I_{M}).
      - exact (mon_lunitor _ · inv_from_z_iso f).
    Defined.

    Definition para_conjoint_unit
      : para_sqr f (identity _) (id_para_mor _) para_conjoint.
    Proof.
      use make_para_sqr.
      - apply identity.
      - abstract
          (unfold para_sqr_laws ; cbn ;
           rewrite id_right ;
           rewrite !assoc ;
           rewrite tensor_lunitor ;
           rewrite !assoc' ;
           rewrite z_iso_inv_after_z_iso ;
           apply id_right).
    Defined.

    Definition para_conjoint_counit
      : para_sqr (identity _) f para_conjoint (id_para_mor _).
    Proof.
      use make_para_sqr.
      - apply identity.
      - abstract
          (unfold para_sqr_laws ; cbn ;
           rewrite tensor_lunitor ;
           rewrite !assoc' ;
           rewrite z_iso_after_z_iso_inv ;
           apply idpath).
    Defined.
  End Conjoints.
End Para.
