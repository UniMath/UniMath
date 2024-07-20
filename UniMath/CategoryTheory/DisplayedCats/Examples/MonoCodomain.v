(*******************************************************************************************

 The displayed category of monomorphisms

 In this file, we define the displayed category of monomorphisms. The definition is very
 similar to how the arrow category is defined, which is used to define the codomain functor.
 We also establish several basic facts, namely we characterize isomorphisms and we prove that
 this displayed category is univalent if the category is univalent.

 The most interesting thing about this construction lies in the question what is a subobject
 in a category. In standard texts on category theory, subobjects of `y` are defined to be
 monomorphisms `x --> y`. However, this does not lead to the right notion of equality
 between subobjects. More specifically, two subobjects `x₁ --> y` and `x₂ --> y` should be
 equal if we have an isomorphism `x₁ --> x₂` making the triangle commute. For this reason,
 one usually defines the collection of subobjects of `y` as a quotient of the collection of
 monomorphisms `x --> y`. Note that this is how subobjects are defined in the file
 `Subobjects.v`.

 Let us be more precise. Suppose that we have two monomorphisms `m₁ : x₁ --> y` and
 `m₂ : x₂ --> y` in a category `C`. If `C` is a strict category, then these two monomorphisms
 are equal if `x₁ = x₂` and `m₁ = m₂` using a suitable transport. However, this is not the
 right notion of equality of subobjects. For instance, if we work in the category of sets,
 we would like `m₁` and `m₂` to be equal if they present the same subset of `y`. For that
 reason, we identify subobjects up to isomorphism. Concretely, this means that we take a
 quotient of the type `∑ (x : C), Monic x y`, which identifies `x₁` and `x₂` up to isomorphism
 and the monomorphism if the resulting diagram commutes.

 For univalent categories, it is not necessary to take a quotient. This is because two
 inhabitants of the type `∑ (x : C), Monic x y` already are equal if their domains are
 isomorphic and if the resulting triangle commutes. For this reason, we can define the type
 of subobjects of an object `y` in a univalent category to be `∑ (x : C), Monic x y`. Note
 that we can also prove that `∑ (x : C), Monic x y` is a set in a univalent category. If we
 have two subobjects `m₁ : x₁ --> y` and `m₂ : x₂ --> y` and two isomorphisms `i₁ i₂ : x₁ ≅ x₂`
 making the obvious triangles commutes, then we must have that `i₁ = i₂` by the fact that `m₂`
 is a monomorphism. This is proven in [isaset_subobject_univ_cat].

 In terms of the fibers, we can say the following. If `C` is a univalent category, then the
 fiber of `y` along the displayed category of monomorphisms is a partial order. The underlying
 type of this partial order is a set. If `C` is not necessarily however, then we can only say
 that the fiber of `y` along this displayed category is a preorder. The underlying type of
 this preorder is not necessarily  set.

 Content
 1. The displayed category of monomorphisms
 2. Pullback squares are cartesian
 3. Cleaving for codomain of monomorphisms
 4. Isos in the codomain
 5. The univalence
 6. Subobjects in univalent categories

 *******************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.

Local Open Scope cat.

(** * 1. The displayed category of monomorphisms *)
Section MonoCodomain.
  Context (C : category).

  Definition mono_cod_disp_ob_mor : disp_cat_ob_mor C.
  Proof.
    simple refine (_ ,, _).
    - exact (λ (x : C), ∑ (y : C), Monic C y x).
    - exact (λ (x₁ x₂ : C)
               (m₁ : ∑ (y : C), Monic C y x₁)
               (m₂ : ∑ (y : C), Monic C y x₂)
               (f : x₁ --> x₂),
             ∑ (ff : pr1 m₁ --> pr1 m₂),
             ff · pr2 m₂ = pr2 m₁ · f).
  Defined.

  Definition mono_cod_id_comp : disp_cat_id_comp _ mono_cod_disp_ob_mor.
  Proof.
    split.
    - intros x m.
      refine (identity _ ,, _).
      abstract
        (rewrite id_left, id_right ;
         apply idpath).
    - intros x y z f g m₁ m₂ m₃ ff gg.
      refine (pr1 ff · pr1 gg ,, _).
      abstract
        (cbn in ff, gg ;
         rewrite !assoc' ;
         rewrite (pr2 gg) ;
         rewrite !assoc ;
         rewrite (pr2 ff) ;
         apply idpath).
  Defined.

  Definition mono_cod_disp_data : disp_cat_data _
    := mono_cod_disp_ob_mor
       ,,
       mono_cod_id_comp.

  Definition locally_propositional_mono_cod_disp_cat
    : locally_propositional mono_cod_disp_data.
  Proof.
    intros x₁ x₂ f m₁ m₂.
    induction m₁ as [ y₁ m₁ ].
    induction m₂ as [ y₂ m₂ ].
    use invproofirrelevance ; cbn.
    intros ff gg.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    use (MonicisMonic _ m₂).
    rewrite (pr2 ff).
    rewrite (pr2 gg).
    apply idpath.
  Qed.

  Lemma mono_cod_disp_axioms : disp_cat_axioms C mono_cod_disp_data.
  Proof.
    repeat split.
    - intros ; apply locally_propositional_mono_cod_disp_cat.
    - intros ; apply locally_propositional_mono_cod_disp_cat.
    - intros ; apply locally_propositional_mono_cod_disp_cat.
    - intros.
      apply isasetaprop.
      apply locally_propositional_mono_cod_disp_cat.
  Qed.

  Definition disp_mono_codomain : disp_cat C
    := mono_cod_disp_data
       ,,
       mono_cod_disp_axioms.

  Proposition transportf_mono_cod_disp
              {x y : C}
              {xx : disp_mono_codomain x}
              {yy : disp_mono_codomain y}
              {f g : x --> y}
              (p : f = g)
              (ff : xx -->[ f] yy)
    : pr1 (transportf
             (mor_disp xx yy)
             p
             ff)
      =
        pr1 ff.
  Proof.
    refine (pr1_transportf (A := C⟦_,_⟧) _ _ @ _).
    rewrite transportf_const ; cbn.
    apply idpath.
  Qed.

  Proposition transportb_mono_cod_disp
              {x y : C}
              {xx : disp_mono_codomain x}
              {yy : disp_mono_codomain y}
              {f g : x --> y}
              (p : g = f)
              (ff : xx -->[ f] yy)
    : pr1 (transportb
             (mor_disp xx yy)
             p
             ff)
      =
        pr1 ff.
  Proof.
    apply transportf_mono_cod_disp.
  Qed.
End MonoCodomain.

(** * 2. Pullback squares are cartesian *)
Section PullbackToCartesian.
  Context {C : category}
          {x₁ x₂ : C}
          {f : x₁ --> x₂}
          {gy₁ : disp_mono_codomain C x₁}
          {hy₂ : disp_mono_codomain C x₂}
          (ff : gy₁ -->[ f ] hy₂)
          (H : isPullback (pr2 ff))
          {w : C}
          (φ : w --> x₁)
          (vψ : disp_mono_codomain C w)
          (kp : vψ -->[ φ · f ] hy₂).

  Let y₁ : C := pr1 gy₁.
  Let y₂ : C := pr1 hy₂.
  Let v : C := pr1 vψ.
  Let g : y₁ --> x₁ := pr2 gy₁.
  Let h : y₂ --> x₂ := pr2 hy₂.
  Let ψ : v --> w := pr2 vψ.
  Let k : v --> y₂ := pr1 kp.
  Let l : y₁ --> y₂ := pr1 ff.

  Let P : Pullback h f := make_Pullback _ H.

  Proposition cartesian_mono_cod_disp_unique
    : isaprop (∑ (gg : vψ -->[ φ] gy₁), (gg ;; ff)%mor_disp = kp).
  Proof.
    use invproofirrelevance.
    intros ζ₁ ζ₂.
    use subtypePath.
    {
      intro.
      apply disp_mono_codomain.
    }
    apply locally_propositional_mono_cod_disp_cat.
  Qed.

  Definition cartesian_mono_cod_disp_map
    : v --> y₁.
  Proof.
    refine (PullbackArrow P v k (ψ · φ) _).
    abstract
      (refine (pr2 kp @ _) ;
       apply assoc).
  Defined.

  Proposition cartesian_mono_cod_disp_comm_pr1
    : cartesian_mono_cod_disp_map · l = k.
  Proof.
    apply (PullbackArrow_PullbackPr1 P).
  Qed.

  Proposition cartesian_mono_cod_disp_comm_pr2
    : cartesian_mono_cod_disp_map · g = ψ · φ.
  Proof.
    apply (PullbackArrow_PullbackPr2 P).
  Qed.
End PullbackToCartesian.

Definition isPullback_cartesian_in_mono_cod_disp
           {C : category}
           {x₁ x₂ : C }
           {f : x₁ --> x₂}
           {gy₁ : disp_mono_codomain _ x₁}
           {hy₂ : disp_mono_codomain _ x₂}
           (ff : gy₁ -->[ f ] hy₂)
           (H : isPullback (pr2 ff))
  : is_cartesian ff.
Proof.
  intros w φ vψ kp.
  use iscontraprop1.
  - exact (cartesian_mono_cod_disp_unique ff φ vψ kp).
  - simple refine ((_ ,, _) ,, _).
    + exact (cartesian_mono_cod_disp_map ff H φ vψ kp).
    + exact (cartesian_mono_cod_disp_comm_pr2 ff H φ vψ kp).
    + use subtypePath ; [ intro ; apply homset_property | ].
      exact (cartesian_mono_cod_disp_comm_pr1 ff H φ vψ kp).
Defined.

(** * 3. Cleaving for codomain of monomorphisms *)
Definition mono_cod_disp_cleaving
           {C : category}
           (H : Pullbacks C)
  : cleaving (disp_mono_codomain C).
Proof.
  intros x₁ x₂ f yg.
  pose (y := pr1 yg).
  pose (g := pr2 yg).
  pose (P := H _ _ _ g f).
  simple refine (_ ,, (_ ,, _) ,, _).
  - refine (PullbackObject P ,, PullbackPr2 P ,, _).
    apply MonicPullbackisMonic.
  - exact (PullbackPr1 P).
  - exact (PullbackSqrCommutes P).
  - use isPullback_cartesian_in_mono_cod_disp.
    apply P.
Defined.

(** * 4. Isos in the codomain *)
Section IsosCodomain.
  Context {C : category}
          {x : C}
          (fy gz : disp_mono_codomain C x).

  Let y : C := pr1 fy.
  Let f : y --> x := pr2 fy.
  Let z : C := pr1 gz.
  Let g : z --> x := pr2 gz.

  Definition iso_to_disp_iso_mono_cod
             (h : z_iso y z)
             (p : f = h · g)
    : z_iso_disp (identity_z_iso x) fy gz.
  Proof.
    use make_z_iso_disp.
    - refine (pr1 h ,, _).
      abstract
        (cbn ;
         rewrite id_right ;
         exact (!p)).
    - simple refine (_ ,, _ ,, _).
      + refine (inv_from_z_iso h ,, _).
        abstract
          (cbn ;
           rewrite id_right ;
           use z_iso_inv_on_right ;
           exact p).
      + apply locally_propositional_mono_cod_disp_cat.
      + apply locally_propositional_mono_cod_disp_cat.
  Defined.

  Definition disp_iso_to_iso_mono_cod
             (ff : z_iso_disp (identity_z_iso x) fy gz)
    : ∑ (h : z_iso y z), f = h · g.
  Proof.
    simple refine (_ ,, _).
    - use make_z_iso.
      + exact (pr11 ff).
      + exact (pr1 (inv_mor_disp_from_z_iso ff)).
      + split.
        * abstract
            (refine (maponpaths pr1 (inv_mor_after_z_iso_disp ff) @ _) ;
             rewrite transportb_mono_cod_disp ;
             apply idpath).
        * abstract
            (refine (maponpaths pr1 (z_iso_disp_after_inv_mor ff) @ _) ;
             rewrite transportb_mono_cod_disp ;
             apply idpath).
    - abstract
        (refine (!(pr21 ff @ _)) ;
         apply id_right).
  Defined.

  Definition disp_iso_weq_iso_mono_cod
    : (∑ (h : z_iso y z), f = h · g)
      ≃
      z_iso_disp (identity_z_iso x) fy gz.
  Proof.
    use weq_iso.
    - exact (λ h, iso_to_disp_iso_mono_cod (pr1 h) (pr2 h)).
    - exact disp_iso_to_iso_mono_cod.
    - abstract
        (intro ff ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use z_iso_eq ; cbn ;
         apply idpath).
    - abstract
        (intro ff ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         apply locally_propositional_mono_cod_disp_cat).
  Defined.
End IsosCodomain.

Definition is_z_iso_disp_mono_codomain
           {C : category}
           {x : C}
           {fy gz : disp_mono_codomain C x}
           (φp : fy -->[ identity x ] gz)
           (H : is_z_isomorphism (pr1 φp))
  : is_z_iso_disp (identity_z_iso x) φp.
Proof.
  pose (h := (_ ,, H) : z_iso _ _).
  simple refine (_ ,, _ ,, _).
  - refine (inv_from_z_iso h ,, _).
    abstract
      (cbn ;
       use z_iso_inv_on_right ;
       rewrite id_right ;
       refine (_ @ !(pr2 φp)) ;
       rewrite id_right ;
       apply idpath).
  - apply locally_propositional_mono_cod_disp_cat.
  - apply locally_propositional_mono_cod_disp_cat.
Defined.

Definition is_z_iso_disp_mono_codomain'
           {C : category}
           {x y : C}
           (h : z_iso x y)
           {fz : disp_mono_codomain C x}
           {fz' : disp_mono_codomain C y}
           (φp : fz -->[ h ] fz')
           (H : is_z_isomorphism (pr1 φp))
  : is_z_iso_disp h φp.
Proof.
  pose (l := (_ ,, H) : z_iso _ _).
  simple refine (_ ,, _ ,, _).
  - refine (inv_from_z_iso l ,, _).
    abstract
      (cbn ;
       use z_iso_inv_on_right ;
       rewrite !assoc ;
       refine (_ @ maponpaths (λ z, z · _) (!(pr2 φp))) ;
       rewrite !assoc' ;
       rewrite z_iso_inv_after_z_iso ;
       rewrite id_right ;
       apply idpath).
  - apply locally_propositional_mono_cod_disp_cat.
  - apply locally_propositional_mono_cod_disp_cat.
Defined.

Definition z_iso_disp_mono_codomain
           {C : category}
           {x y : C}
           {f : z_iso x y}
           {h₁ : disp_mono_codomain C x}
           {h₂ : disp_mono_codomain C y}
           (g : z_iso (pr1 h₁) (pr1 h₂))
           (p : g · pr2 h₂ = pr2 h₁ · f)
  : z_iso_disp f h₁ h₂.
Proof.
  use make_z_iso_disp.
  - exact (pr1 g ,, p).
  - simple refine (_ ,, _ ,, _).
    + refine (inv_from_z_iso g ,, _).
      abstract
        (use z_iso_inv_on_right ;
         rewrite !assoc ;
         use z_iso_inv_on_left ;
         exact p).
    + apply locally_propositional_mono_cod_disp_cat.
    + apply locally_propositional_mono_cod_disp_cat.
Defined.

Definition from_z_iso_disp_mono_codomain
           {C : category}
           {x y : C}
           {f : z_iso x y}
           {h₁ : disp_mono_codomain C x}
           {h₂ : disp_mono_codomain C y}
           (ff : z_iso_disp f h₁ h₂)
  : z_iso (pr1 h₁) (pr1 h₂).
Proof.
  use make_z_iso.
  - exact (pr11 ff).
  - exact (pr112 ff).
  - split.
    + abstract
        (refine (maponpaths pr1 (pr222 ff) @ _) ;
         rewrite transportb_mono_cod_disp ;
         apply idpath).
    + abstract
        (refine (maponpaths pr1 (pr122 ff) @ _) ;
         rewrite transportb_mono_cod_disp ;
         apply idpath).
Defined.

(** * 5. The univalence *)
Proposition disp_univalent_disp_mono_codomain
            (C : univalent_category)
  : is_univalent_disp (disp_mono_codomain C).
Proof.
  use is_univalent_disp_from_fibers.
  intros x fy gz.
  use weqhomot.
  - refine (disp_iso_weq_iso_mono_cod _ _
            ∘ weqtotal2 (make_weq _ (univalent_category_is_univalent C _ _)) _
            ∘ total2_paths_equiv _ _ _)%weq.
    abstract
      (induction fy as [ y f ] ;
       induction gz as [ z g ] ;
       cbn ;
       intro p ;
       induction p ; cbn ;
       rewrite id_left ;
       apply path_sigma_hprop ;
       apply isapropisMonic).
  - intro p.
    induction p.
    use subtypePath.
    {
      intro.
      apply isaprop_is_z_iso_disp.
    }
    apply locally_propositional_mono_cod_disp_cat.
Qed.

Definition univalent_disp_mono_codomain
           (C : univalent_category)
  : disp_univalent_category C.
Proof.
  use make_disp_univalent_category.
  - exact (disp_mono_codomain C).
  - apply disp_univalent_disp_mono_codomain.
Defined.

(** * 6. Subobjects in univalent categories *)
Definition subobject_univ_cat
           {C : univalent_category}
           (x : C)
  : UU
  := univalent_disp_mono_codomain C x.

Coercion subobject_univ_cat_to_ob
         {C : univalent_category}
         {x : C}
         (y : subobject_univ_cat x)
  : C.
Proof.
  exact (pr1 y).
Defined.

Definition mono_of_subobject_univ_cat
           {C : univalent_category}
           {x : C}
           (y : subobject_univ_cat x)
  : Monic C y x
  := pr2 y.

Section Subobjects.
  Context {C : univalent_category}
          (x : C).

  Definition isaset_subobject_univ_cat
    : isaset (subobject_univ_cat x).
  Proof.
    intros m₁ m₂.
    use isaset_disp_ob.
    apply locally_propositional_mono_cod_disp_cat.
  Qed.

  Definition set_of_subobject_univ_cat
    : hSet.
  Proof.
    use make_hSet.
    - exact (subobject_univ_cat x).
    - apply isaset_subobject_univ_cat.
  Defined.

  Proposition eq_subobject_univ_cat
              {y₁ y₂ : subobject_univ_cat x}
              (f : z_iso y₁ y₂)
              (p : f · mono_of_subobject_univ_cat y₂
                   =
                   mono_of_subobject_univ_cat y₁)
    : y₁ = y₂.
  Proof.
    use (isotoid_disp (univalent_disp_mono_codomain C) (idpath _)).
    use z_iso_disp_mono_codomain.
    - exact f.
    - cbn.
      rewrite id_right.
      exact p.
  Qed.
End Subobjects.

Definition subobject_univ_cat_pb
           {C : univalent_category}
           (PB : Pullbacks C)
           {x y : C}
           (f : x --> y)
           (m : set_of_subobject_univ_cat y)
  : set_of_subobject_univ_cat x
  := fiber_functor_from_cleaving _ (mono_cod_disp_cleaving PB) f m.
