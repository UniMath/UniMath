Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.

Local Open Scope cat.

(**
The definition of a Street fibration of categories
 *)
Section StreetFibration.
  Context {E B : category}
          (F : E ⟶ B).

  Definition is_cartesian_sfib
             {e₁ e₂ : E}
             (f : e₁--> e₂)
    : UU
    := ∏ (z : E)
         (g : z --> e₂)
         (h : F z --> F e₁)
         (p : #F g = h · #F f),
       ∃! (φ : z --> e₁),
       #F φ = h
       ×
       φ · f = g.

  Definition isaprop_is_cartesian_sfib
             {e₁ e₂ : E}
             (f : e₁--> e₂)
    : isaprop (is_cartesian_sfib f).
  Proof.
    do 4 (apply impred ; intro).
    apply isapropiscontr.
  Qed.

  Definition street_fib
    : UU
    := ∏ (e : E)
         (b : B)
         (f : b --> F e),
       ∑ (bb : E)
         (ff : bb --> e)
         (i : iso (F bb) b),
       # F ff = i · f
       ×
       is_cartesian_sfib ff.
End StreetFibration.

(**
The projection of a fibration is a Street fibration
 *)
Section CleavingToStreetFib.
  Context {B : category}
          {D : disp_cat B}.

  Let E : category := total_category D.
  Let P : E ⟶ B := pr1_category D.

  Local Definition is_cartesian_to_unique_sfib
        {e₁ e₂ : E}
        (f : e₁ --> e₂)
        (H : is_cartesian (pr2 f))
        {z : E}
        (g : z --> e₂)
        (h : P z --> P e₁)
        (p : # P g = h · # P f)
    : isaprop (∑ φ : E ⟦ z, e₁ ⟧, # P φ = h × φ · f = g).
  Proof.
    pose (lift := H (pr1 z) h (pr2 z) (transportf (λ z, _ -->[ z ] _) p (pr2 g))).
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply homset_property.
    }
    use (total2_paths_f (pr12 φ₁ @ !(pr12 φ₂))).
    pose (φφ₁ := transportf (λ z, _ -->[ z ] _) (pr12 φ₁) (pr21 φ₁)).
    pose (φφ₂ := transportf (λ z, _ -->[ z ] _) (pr12 φ₂) (pr21 φ₂)).
    simpl in φφ₁, φφ₂.
    assert ((φφ₁ ;; pr2 f)%mor_disp
            =
            transportf (λ w, pr2 z -->[ w ] pr2 e₂) p (pr2 g))
      as H₁.
    {
      unfold φφ₁.
      rewrite mor_disp_transportf_postwhisker.
      etrans.
      {
        apply maponpaths.
        exact (transportb_transpose_right (fiber_paths (pr22 φ₁))).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    }
    assert ((φφ₂ ;; pr2 f)%mor_disp
            =
            transportf (λ w, pr2 z -->[ w ] pr2 e₂) p (pr2 g))
      as H₂.
    {
      unfold φφ₂.
      rewrite mor_disp_transportf_postwhisker.
      etrans.
      {
        apply maponpaths.
        exact (transportb_transpose_right (fiber_paths (pr22 φ₂))).
      }
      unfold transportb.
      rewrite transport_f_f.
      apply maponpaths_2.
      apply homset_property.
    }
    pose (proofirrelevance _ (isapropifcontr lift)) as q.
    assert (r := maponpaths pr1 (q (φφ₁ ,, H₁) (φφ₂ ,, H₂))).
    cbn in r.
    unfold φφ₁, φφ₂ in r.
    simple refine (_ @ maponpaths (transportb _ (pr12 φ₂)) r @ _)
    ; unfold transportb
    ; rewrite transport_f_f.
    + apply maponpaths_2.
      apply homset_property.
    + apply transportf_set.
      apply homset_property.
  Qed.

  Definition is_cartesian_to_is_cartesian_sfib
             {e₁ e₂ : E}
             (f : e₁ --> e₂)
             (H : is_cartesian (pr2 f))
    : is_cartesian_sfib P f.
  Proof.
    intros z g h p.
    pose (lift := H (pr1 z) h (pr2 z) (transportf (λ z, _ -->[ z ] _) p (pr2 g))).
    use iscontraprop1.
    - exact (is_cartesian_to_unique_sfib f H g h p).
    - simple refine ((h ,, pr11 lift) ,, (idpath _ ,, _)) ; cbn.
      abstract
        (pose (pr21 lift) as q ; cbn in q ;
         use total2_paths_f ;
         [ exact (!p)
         | cbn ;
           rewrite q ;
           rewrite transport_f_f ;
           apply transportf_set ;
           apply homset_property ]).
  Defined.

  Local Definition is_cartesian_sfib_to_unique_cartesian
        {e₁ e₂ : E}
        (f : e₁ --> e₂)
        (H : is_cartesian_sfib P f)
        {z : B}
        (g : z --> pr1 e₁)
        (zz : D z)
        (gf : zz -->[ g · pr1 f] pr2 e₂)
    : isaprop (∑ gg, (gg ;; pr2 f)%mor_disp = gf).
  Proof.
    pose (lift := H (z ,, zz) (g · pr1 f ,, gf) g (idpath _)).
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply D.
    }
    pose (φφ₁ := (g ,, pr1 φ₁) : E ⟦ z,, zz, e₁ ⟧).
    assert (# P φφ₁ = g × φφ₁ · f = g · pr1 f,, gf) as H₁.
    {
      split ; cbn.
      - apply idpath.
      - apply maponpaths.
        exact (pr2 φ₁).
    }
    pose (φφ₂ := (g ,, pr1 φ₂) : E ⟦ z,, zz, e₁ ⟧).
    assert (# P φφ₂ = g × φφ₂ · f = g · pr1 f,, gf) as H₂.
    {
      split ; cbn.
      - apply idpath.
      - apply maponpaths.
        exact (pr2 φ₂).
    }
    assert (q := maponpaths
                   (λ z, pr1 z)
                   (proofirrelevance
                      _
                      (isapropifcontr lift)
                      (φφ₁ ,, H₁) (φφ₂ ,, H₂))).
    cbn in q.
    refine (!_ @ fiber_paths q).
    apply transportf_set.
    apply homset_property.
  Qed.

  Definition is_cartesian_sfib_to_is_cartesian
             {e₁ e₂ : E}
             (f : e₁ --> e₂)
             (H : is_cartesian_sfib P f)
    : is_cartesian (pr2 f).
  Proof.
    intros z g zz gf.
    pose (lift := H (z ,, zz) (g · pr1 f ,, gf) g (idpath _)).
    use iscontraprop1.
    - apply is_cartesian_sfib_to_unique_cartesian.
      exact H.
    - simple refine (_ ,, _).
      + exact (transportf
                 (λ z, _ -->[ z ] _)
                 (pr121 lift)
                 (pr211 lift)).
      + abstract
          (simpl ;
           pose (transportb_transpose_right (fiber_paths (pr221 lift))) as p ;
           rewrite mor_disp_transportf_postwhisker ;
           cbn in p ;
           refine (maponpaths _ p @ _) ;
           unfold transportb ;
           rewrite transport_f_f ;
           apply transportf_set ;
           apply homset_property).
  Defined.

  Definition fibration_is_street_fib
             (HD : cleaving D)
    : street_fib (pr1_category D).
  Proof.
    intros e b f.
    pose (HD (pr1 e) b f (pr2 e)) as c.
    simple refine ((b ,, pr1 c) ,, (f ,, pr12 c) ,, identity_iso b ,, _).
    simpl.
    split.
    - apply (!(id_left _)).
    - apply is_cartesian_to_is_cartesian_sfib.
      exact (pr22 c).
  Defined.
End CleavingToStreetFib.

(** Morphisms between Street fibrations *)
Definition preserves_cartesian
           {B₁ B₂ E₁ E₂ : category}
           (P₁ : E₁ ⟶ B₁)
           (P₂ : E₂ ⟶ B₂)
           (FE : E₁ ⟶ E₂)
  : UU
  := ∏ (e₁ e₂ : E₁)
       (f : e₁ --> e₂),
     is_cartesian_sfib P₁ f
     →
     is_cartesian_sfib P₂ (#FE f).

Definition identity_preserves_cartesian
           {B E : category}
           (P : E ⟶ B)
  : preserves_cartesian P P (functor_identity E).
Proof.
  intros ? ? ? H.
  exact H.
Qed.

Definition composition_preserves_cartesian
           {B₁ B₂ B₃ E₁ E₂ E₃ : category}
           {P₁ : E₁ ⟶ B₁}
           {P₂ : E₂ ⟶ B₂}
           {P₃ : E₃ ⟶ B₃}
           {FE₁ : E₁ ⟶ E₂}
           {FE₂ : E₂ ⟶ E₃}
           (HFE₁ : preserves_cartesian P₁ P₂ FE₁)
           (HFE₂ : preserves_cartesian P₂ P₃ FE₂)
  : preserves_cartesian P₁ P₃ (FE₁ ∙ FE₂).
Proof.
  intros ? ? ? H.
  apply HFE₂.
  apply HFE₁.
  exact H.
Qed.

Definition isaprop_preserves_cartesian
           {B₁ B₂ E₁ E₂ : category}
           (P₁ : E₁ ⟶ B₁)
           (P₂ : E₂ ⟶ B₂)
           (FE : E₁ ⟶ E₂)
  : isaprop (preserves_cartesian P₁ P₂ FE).
Proof.
  do 4 (use impred ; intro).
  apply isaprop_is_cartesian_sfib.
Qed.

Definition mor_of_street_fib
           {B₁ B₂ E₁ E₂ : category}
           (P₁ : E₁ ⟶ B₁)
           (P₂ : E₂ ⟶ B₂)
  : UU
  := ∑ (FB : B₁ ⟶ B₂)
       (FE : E₁ ⟶ E₂),
     preserves_cartesian P₁ P₂ FE
     ×
     nat_iso (P₁ ∙ FB) (FE ∙ P₂).

Definition mor_of_street_fib_base
           {B₁ B₂ E₁ E₂ : category}
           {P₁ : E₁ ⟶ B₁}
           {P₂ : E₂ ⟶ B₂}
           (F : mor_of_street_fib P₁ P₂)
  : B₁ ⟶ B₂
  := pr1 F.

Definition mor_of_street_fib_total
           {B₁ B₂ E₁ E₂ : category}
           {P₁ : E₁ ⟶ B₁}
           {P₂ : E₂ ⟶ B₂}
           (F : mor_of_street_fib P₁ P₂)
  : E₁ ⟶ E₂
  := pr12 F.

Definition mor_of_street_fib_preserves_cartesian
           {B₁ B₂ E₁ E₂ : category}
           {P₁ : E₁ ⟶ B₁}
           {P₂ : E₂ ⟶ B₂}
           (F : mor_of_street_fib P₁ P₂)
  : preserves_cartesian P₁ P₂ (mor_of_street_fib_total F)
  := pr122 F.

Definition mor_of_street_fib_preserves_nat_iso
           {B₁ B₂ E₁ E₂ : category}
           {P₁ : E₁ ⟶ B₁}
           {P₂ : E₂ ⟶ B₂}
           (F : mor_of_street_fib P₁ P₂)
  : nat_iso
      (P₁ ∙ mor_of_street_fib_base F)
      (mor_of_street_fib_total F ∙ P₂)
  := pr222 F.

Definition id_mor_of_street_fib_nat_trans
           {B E : category}
           (P : E ⟶ B)
  : P ∙ functor_identity B ⟹ functor_identity E ∙ P.
Proof.
  use make_nat_trans.
  - exact (λ _, identity _).
  - abstract
      (intros ? ? ? ;
       cbn ;
       rewrite id_left, id_right ;
       apply idpath).
Defined.

Definition id_mor_of_street_fib_nat_iso
           {B E : category}
           (P : E ⟶ B)
  : nat_iso (P ∙ functor_identity B) (functor_identity E ∙ P).
Proof.
  use make_nat_iso.
  - exact (id_mor_of_street_fib_nat_trans P).
  - intro x.
    cbn.
    apply identity_is_iso.
Defined.

Definition id_mor_of_street_fib
           {B E : category}
           (P : E ⟶ B)
  : mor_of_street_fib P P
  := functor_identity _
     ,,
     functor_identity _
     ,,
     identity_preserves_cartesian _
     ,,
     id_mor_of_street_fib_nat_iso P.

Definition comp_mor_of_street_fib_nat_trans
           {B₁ B₂ B₃ E₁ E₂ E₃ : category}
           {P₁ : E₁ ⟶ B₁}
           {P₂ : E₂ ⟶ B₂}
           {P₃ : E₃ ⟶ B₃}
           (F₁ : mor_of_street_fib P₁ P₂)
           (F₂ : mor_of_street_fib P₂ P₃)
  : P₁ ∙ (mor_of_street_fib_base F₁ ∙ mor_of_street_fib_base F₂)
    ⟹
    (mor_of_street_fib_total F₁ ∙ mor_of_street_fib_total F₂) ∙ P₃.
Proof.
  use make_nat_trans.
  - exact (λ x, #(mor_of_street_fib_base F₂) (mor_of_street_fib_preserves_nat_iso F₁ x)
                ·
                mor_of_street_fib_preserves_nat_iso F₂ _).
  - abstract
      (intros x y f ;
       cbn ;
       rewrite !assoc ;
       rewrite <- functor_comp ;
       etrans ;
         [ apply maponpaths_2 ;
           apply maponpaths ;
           exact (nat_trans_ax (mor_of_street_fib_preserves_nat_iso F₁) _ _ f)
         | ] ;
       rewrite functor_comp ;
       rewrite !assoc' ;
       apply maponpaths ;
       apply (nat_trans_ax (mor_of_street_fib_preserves_nat_iso F₂))).
Defined.

Definition comp_mor_of_street_fib_nat_iso
           {B₁ B₂ B₃ E₁ E₂ E₃ : category}
           {P₁ : E₁ ⟶ B₁}
           {P₂ : E₂ ⟶ B₂}
           {P₃ : E₃ ⟶ B₃}
           (F₁ : mor_of_street_fib P₁ P₂)
           (F₂ : mor_of_street_fib P₂ P₃)
  : nat_iso
      (P₁ ∙ (mor_of_street_fib_base F₁ ∙ mor_of_street_fib_base F₂))
      ((mor_of_street_fib_total F₁ ∙ mor_of_street_fib_total F₂) ∙ P₃).
Proof.
  use make_nat_iso.
  - exact (comp_mor_of_street_fib_nat_trans F₁ F₂).
  - intro x.
    cbn.
    apply is_iso_comp_of_is_isos.
    + apply functor_on_is_iso_is_iso.
      apply (mor_of_street_fib_preserves_nat_iso F₁).
    + apply (mor_of_street_fib_preserves_nat_iso F₂).
Defined.

Definition comp_mor_of_street_fib
           {B₁ B₂ B₃ E₁ E₂ E₃ : category}
           {P₁ : E₁ ⟶ B₁}
           {P₂ : E₂ ⟶ B₂}
           {P₃ : E₃ ⟶ B₃}
           (F₁ : mor_of_street_fib P₁ P₂)
           (F₂ : mor_of_street_fib P₂ P₃)
  : mor_of_street_fib P₁ P₃
  := mor_of_street_fib_base F₁ ∙ mor_of_street_fib_base F₂
     ,,
     mor_of_street_fib_total F₁ ∙ mor_of_street_fib_total F₂
     ,,
     composition_preserves_cartesian
       (mor_of_street_fib_preserves_cartesian F₁)
       (mor_of_street_fib_preserves_cartesian F₂)
     ,,
     comp_mor_of_street_fib_nat_iso F₁ F₂.
