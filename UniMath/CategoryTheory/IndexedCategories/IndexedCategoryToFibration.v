(*************************************************************************

 Indexed categories give rise to fibrations

 In this file, we show that every indexed category over `C` gives rise to
 a fibration over `C`. To prove that, we take the following steps.

 First, we show that every indexed category gives rise to a displayed
 category over `C`. This is also known as the Grothendieck construction
 (see https://ncatlab.org/nlab/show/Grothendieck+construction#Definition).
 The only difference arises from the fact that we used displayed
 categories: whereas one usually would define objects and morphisms to be
 pairs, the displayed objects and morphisms are not. The total category
 of the displayed category that we define, corresponds to the usual
 definition of the Grothendieck construction.

 After that, we prove some properties of this displayed categories. We
 first classify the isomorphisms, and with that, we prove that this
 displayed category is univalent. We also characterize cartesian morphisms
 as certain isomorphisms, and using that, we construct a cleaving for the
 displayed category.

 Contents
 1. The displayed category arising from an indexed category
 2. Isomorphisms in the displayed category from an indexed category
 3. The univalence of that displayed category
 4. Cartesian morphisms are the same as certain isomorphisms
 5. The cleaving from an indexed category

 *************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.IndexedCategories.IndexedCategory.

Local Open Scope cat.

Section IndexedCatToFibration.
  Context {C : category}
          (Φ : indexed_cat (C^opp)).

  (**
   1. The displayed category arising from an indexed category
   *)
  Definition indexed_cat_to_disp_cat_ob_mor
    : disp_cat_ob_mor C.
  Proof.
    simple refine (_ ,, _).
    - exact (λ x, Φ x).
    - exact (λ x y xx yy f, xx --> (Φ $ f) yy).
  Defined.

  Definition indexed_cat_to_disp_cat_id_comp
    : disp_cat_id_comp C indexed_cat_to_disp_cat_ob_mor.
  Proof.
    split.
    - exact (λ x xx, indexed_cat_id Φ x xx).
    - exact (λ x y z f g xx yy zz ff gg,
             ff
             · #(Φ $ f) gg
             · indexed_cat_comp Φ g f zz).
  Defined.

  Definition indexed_cat_to_disp_cat_data
    : disp_cat_data C.
  Proof.
    simple refine (_ ,, _).
    - exact indexed_cat_to_disp_cat_ob_mor.
    - exact indexed_cat_to_disp_cat_id_comp.
  Defined.

  Proposition transportf_indexed_cat_to_disp_cat
              {x y : C}
              {xx : indexed_cat_to_disp_cat_data x}
              {yy : indexed_cat_to_disp_cat_data y}
              {f g : x --> y}
              (p : f = g)
              (ff : xx --> (Φ $ f) yy)
    : transportf
        (λ z, xx -->[ z ] yy)
        p
        ff
      =
      ff · idtoiso (maponpaths (λ h, (Φ $ h) yy) p).
  Proof.
    induction p ; cbn.
    rewrite id_right.
    apply idpath.
  Qed.

  Proposition indexed_cat_to_disp_cat_axioms
    : disp_cat_axioms C indexed_cat_to_disp_cat_data.
  Proof.
    repeat split.
    - intros x y f xx yy ff ; cbn in *.
      etrans.
      {
        apply maponpaths_2.
        exact (!(nat_trans_ax (indexed_cat_id Φ x) _ _ ff)).
      }
      cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply (indexed_cat_runitor_alt Φ).
      }
      unfold transportb.
      rewrite transportf_indexed_cat_to_disp_cat.
      apply idpath.
    - intros x y f xx yy ff ; cbn in *.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        apply (indexed_cat_lunitor_alt Φ).
      }
      unfold transportb.
      rewrite transportf_indexed_cat_to_disp_cat.
      apply idpath.
    - intros w x y z f g h ww xx yy zz ff gg hh ; cbn in *.
      rewrite !functor_comp.
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        refine (!_).
        apply (indexed_cat_lassociator Φ h g f zz).
      }
      unfold transportb.
      rewrite transportf_indexed_cat_to_disp_cat.
      rewrite !assoc'.
      cbn.
      do 2 apply maponpaths.
      etrans.
      {
        do 2 refine (assoc _ _ _ @ _).
        etrans.
        {
          do 2 apply maponpaths_2.
          apply (nat_trans_ax (indexed_cat_comp Φ g f)).
        }
        do 2 refine (assoc' _ _ _ @ _).
        apply idpath.
      }
      do 6 apply maponpaths.
      apply homset_property.
    - intros x y f xx yy ; cbn in *.
      apply homset_property.
  Qed.

  Definition indexed_cat_to_disp_cat
    : disp_cat C.
  Proof.
    simple refine (_ ,, _).
    - exact indexed_cat_to_disp_cat_data.
    - exact indexed_cat_to_disp_cat_axioms.
  Defined.

  (**
   2. Isomorphisms in the displayed category from an indexed category
   *)
  Definition indexed_cat_to_disp_cat_z_iso_weq_base
             {x : C}
             (xx₁ xx₂ : Φ x)
    : (xx₁ --> xx₂) ≃ (xx₁ --> (Φ $ identity x) xx₂).
  Proof.
    use weq_iso.
    - exact (λ f, f · indexed_cat_id Φ x xx₂).
    - exact (λ f, f · inv_from_z_iso (indexed_cat_id_z_iso Φ xx₂)).
    - abstract
        (intro f ; cbn ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         exact (z_iso_inv_after_z_iso (indexed_cat_id_z_iso Φ xx₂))).
    - abstract
        (intro f ; cbn ;
         rewrite !assoc' ;
         refine (_ @ id_right _) ;
         apply maponpaths ;
         exact (z_iso_after_z_iso_inv (indexed_cat_id_z_iso Φ xx₂))).
  Defined.

  Section IsoWeqDispIso.
    Context {x : C}
            (xx₁ xx₂ : Φ x)
            (f : xx₁ --> xx₂).

    Section IsoToDispIso.
      Context (Hf : is_z_isomorphism f).

      Let f_iso := (f ,, Hf) : z_iso xx₁ xx₂.

      Definition indexed_cat_to_disp_cat_to_disp_iso_inv
        : xx₂ --> (Φ $ identity x) xx₁
        := inv_from_z_iso f_iso · indexed_cat_id Φ x xx₁.

      Proposition indexed_cat_to_disp_cat_to_disp_iso_inv_right
        : indexed_cat_to_disp_cat_to_disp_iso_inv
          · # (Φ $ identity x) (f · indexed_cat_id Φ x xx₂)
          · indexed_cat_comp Φ (identity x) (identity x) xx₂
          =
          indexed_cat_id Φ x xx₂
          · idtoiso (maponpaths (λ h, (Φ $ h) xx₂) (!(id_left _))).
      Proof.
        unfold indexed_cat_to_disp_cat_to_disp_iso_inv.
        rewrite functor_comp.
        rewrite !assoc'.
        etrans.
        {
          do 3 apply maponpaths.
          apply (indexed_cat_lunitor_alt Φ).
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          refine (!_).
          apply (nat_trans_ax (indexed_cat_id Φ x)).
        }
        cbn.
        rewrite !assoc.
        rewrite z_iso_after_z_iso_inv.
        refine (maponpaths (λ z, z · _) (id_left _) @ _).
        do 4 apply maponpaths.
        apply homset_property.
      Qed.

      Proposition indexed_cat_to_disp_cat_to_disp_iso_inv_left
        : f
          · indexed_cat_id Φ x xx₂
          · # (Φ $ identity x) indexed_cat_to_disp_cat_to_disp_iso_inv
          · indexed_cat_comp Φ (identity x) (identity x) xx₁
          =
          indexed_cat_id Φ x xx₁
          · idtoiso (maponpaths (λ h, (Φ $ h) xx₁) (!(id_left _))).
      Proof.
        unfold indexed_cat_to_disp_cat_to_disp_iso_inv.
        rewrite functor_comp.
        rewrite !assoc'.
        etrans.
        {
          do 3 apply maponpaths.
          apply (indexed_cat_lunitor_alt Φ).
        }
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          apply maponpaths_2.
          refine (!_).
          apply (nat_trans_ax (indexed_cat_id Φ x)).
        }
        cbn.
        rewrite !assoc.
        etrans.
        {
          do 2 apply maponpaths_2.
          apply (z_iso_inv_after_z_iso f_iso).
        }
        refine (maponpaths (λ z, z · _) (id_left _) @ _).
        do 4 apply maponpaths.
        apply homset_property.
      Qed.

      Definition indexed_cat_to_disp_cat_to_disp_iso
        : @is_z_iso_disp
             _
             indexed_cat_to_disp_cat
             _ _
             (identity_z_iso x)
             _ _
             (indexed_cat_to_disp_cat_z_iso_weq_base xx₁ xx₂ f).
      Proof.
        simple refine (_ ,, _ ,, _).
        - exact indexed_cat_to_disp_cat_to_disp_iso_inv.
        - abstract
            (cbn ;
             unfold transportb ;
             rewrite transportf_indexed_cat_to_disp_cat ;
             refine (indexed_cat_to_disp_cat_to_disp_iso_inv_right @ _) ;
             do 4 apply maponpaths ;
             apply homset_property).
        - abstract
            (cbn ;
             unfold transportb ;
             rewrite transportf_indexed_cat_to_disp_cat ;
             refine (indexed_cat_to_disp_cat_to_disp_iso_inv_left @ _) ;
             do 4 apply maponpaths ;
             apply homset_property).
      Defined.
    End IsoToDispIso.

    Section DispIsoToIso.
      Context (Hf : @is_z_iso_disp
                       _
                       indexed_cat_to_disp_cat
                       _ _
                       (identity_z_iso x)
                       _ _
                       (indexed_cat_to_disp_cat_z_iso_weq_base xx₁ xx₂ f)).

      Definition indexed_cat_to_disp_cat_from_disp_iso_inv
        : xx₂ --> xx₁
        := inv_mor_disp_from_z_iso Hf · inv_from_z_iso (indexed_cat_id_z_iso Φ xx₁).

      Proposition indexed_cat_to_disp_cat_from_disp_iso_inv_right
        : f · indexed_cat_to_disp_cat_from_disp_iso_inv = identity _.
      Proof.
        unfold indexed_cat_to_disp_cat_from_disp_iso_inv.
        rewrite !assoc.
        refine (!_).
        use z_iso_inv_on_left.
        rewrite id_left.
        pose (inv_mor_after_z_iso_disp Hf) as p.
        cbn in p.
        unfold transportb in p.
        rewrite transportf_indexed_cat_to_disp_cat in p.
        use (cancel_z_iso
                 _ _
                 (idtoiso (maponpaths (λ h, (Φ $ h) xx₁) (!(id_left (identity x)))))).
        refine (_ @ p) ; clear p.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        refine (!_).
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (nat_trans_ax (indexed_cat_id Φ x)).
        }
        cbn.
        rewrite !assoc'.
        apply maponpaths.
        apply (indexed_cat_runitor_alt Φ).
      Qed.

      Proposition indexed_cat_to_disp_cat_from_disp_iso_inv_left
        : indexed_cat_to_disp_cat_from_disp_iso_inv · f = identity _.
      Proof.
        unfold indexed_cat_to_disp_cat_from_disp_iso_inv.
        rewrite !assoc'.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (nat_trans_ax (nat_z_iso_inv (indexed_cat_id_nat_z_iso Φ x)) _ _ _
                  : _ · inv_from_z_iso (indexed_cat_id_z_iso Φ xx₂)
                    =
                    inv_from_z_iso (indexed_cat_id_z_iso Φ xx₁) · f).
        }
        rewrite !assoc.
        refine (!_).
        use z_iso_inv_on_left.
        rewrite id_left.
        use (cancel_z_iso
                 _ _
                 (idtoiso (maponpaths (λ h, (Φ $ h) xx₂) (!(id_left (identity x)))))).
        pose (z_iso_disp_after_inv_mor Hf) as p.
        cbn in p.
        unfold transportb in p.
        rewrite transportf_indexed_cat_to_disp_cat in p.
        refine (_ @ p) ; clear p.
        rewrite !functor_comp.
        rewrite !assoc'.
        do 2 apply maponpaths.
        refine (!_).
        refine (indexed_cat_lunitor_alt Φ _ _ @ _).
        do 3 apply maponpaths.
        apply homset_property.
      Qed.

      Definition indexed_cat_to_disp_cat_from_disp_iso
        : is_z_isomorphism f.
      Proof.
        simple refine (_ ,, _ ,, _).
        - exact indexed_cat_to_disp_cat_from_disp_iso_inv.
        - exact indexed_cat_to_disp_cat_from_disp_iso_inv_right.
        - exact indexed_cat_to_disp_cat_from_disp_iso_inv_left.
      Defined.
    End DispIsoToIso.

    Definition indexed_cat_to_disp_cat_z_iso_weq_fiber
      : is_z_isomorphism f
        ≃
        @is_z_iso_disp
           _
           indexed_cat_to_disp_cat
           _ _
           (identity_z_iso x)
           _ _
           (indexed_cat_to_disp_cat_z_iso_weq_base xx₁ xx₂ f).
    Proof.
      use weqimplimpl.
      - exact indexed_cat_to_disp_cat_to_disp_iso.
      - exact indexed_cat_to_disp_cat_from_disp_iso.
      - apply isaprop_is_z_isomorphism.
      - apply isaprop_is_z_iso_disp.
    Defined.
  End IsoWeqDispIso.

  Definition indexed_cat_to_disp_cat_z_iso_weq
             {x : C}
             (xx₁ xx₂ : Φ x)
    : z_iso xx₁ xx₂
      ≃
      @z_iso_disp _ indexed_cat_to_disp_cat _ _ (identity_z_iso _) xx₁ xx₂.
  Proof.
    use weqbandf.
    - exact (indexed_cat_to_disp_cat_z_iso_weq_base xx₁ xx₂).
    - exact (indexed_cat_to_disp_cat_z_iso_weq_fiber xx₁ xx₂).
  Defined.

  Definition is_z_iso_disp_indexed_cat_to_disp_cat
             {x : C}
             (xx₁ xx₂ : Φ x)
             (f : xx₁ --> (Φ $ identity x) xx₂)
             (Hf : is_z_isomorphism f)
    : @is_z_iso_disp
        _
        indexed_cat_to_disp_cat
        _ _
        (identity_z_iso x)
        xx₁ xx₂
        f.
  Proof.
    pose (f' := f · inv_from_z_iso (indexed_cat_id_z_iso Φ xx₂)).
    refine (transportf
              (λ z, is_z_iso_disp _ z)
              _
              (indexed_cat_to_disp_cat_to_disp_iso xx₁ xx₂ f' _)).
    - cbn ; unfold f'.
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      apply z_iso_after_z_iso_inv.
    - use is_z_isomorphism_comp.
      + exact Hf.
      + apply is_z_iso_inv_from_z_iso.
  Defined.

  (**
   3. The univalence of that displayed category
   *)
  Proposition is_univalent_disp_indexed_cat_to_disp_cat
    : is_univalent_disp indexed_cat_to_disp_cat.
  Proof.
    use is_univalent_disp_from_fibers.
    intros x xx₁ xx₂.
    use weqhomot.
    - exact (indexed_cat_to_disp_cat_z_iso_weq xx₁ xx₂
             ∘ make_weq idtoiso (pr2 (Φ x) _ _))%weq.
    - abstract
        (intro p ;
         induction p ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         cbn ;
         apply id_left).
  Defined.

  (**
   4. Cartesian morphisms are the same as certain isomorphisms
   *)
  Section Cartesians.
    Context {x y : C}
            {f : x --> y}
            {xx : Φ x}
            {yy : Φ y}
            {ff : xx --> (Φ $ f) yy}
            (Hff : is_z_isomorphism ff)
            {w : C}
            (g : w --> x)
            {ww : Φ w}
            (hh : ww --> (Φ $ g · f) yy).

    Let ff_iso : z_iso xx ((Φ $ f) yy) := ff ,, Hff.

    Proposition is_cartesian_indexed_cat_factorisation_unique
      : isaprop (∑ gg, gg · # (Φ $ g) ff · indexed_cat_comp Φ f g yy = hh).
    Proof.
      use invproofirrelevance.
      intros φ₁ φ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use (cancel_z_iso _ _ (functor_on_z_iso (Φ $ g) ff_iso)).
      use (cancel_z_iso _ _ (indexed_cat_comp_z_iso Φ f g yy)).
      exact (pr2 φ₁ @ ! (pr2 φ₂)).
    Qed.

    Definition is_cartesian_indexed_cat_factorisation
      : ww --> (Φ $ g) xx
      := hh
         · inv_from_z_iso (indexed_cat_comp_z_iso Φ f g yy)
         · # (Φ $ g) (inv_from_z_iso ff_iso).

    Proposition is_cartesian_indexed_cat_factorisation_commutes
      : is_cartesian_indexed_cat_factorisation
        · # (Φ $ g) ff
        · indexed_cat_comp Φ f g yy
        =
        hh.
    Proof.
      unfold is_cartesian_indexed_cat_factorisation.
      rewrite !assoc'.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- functor_comp.
        rewrite z_iso_after_z_iso_inv.
        rewrite functor_id.
        apply idpath.
      }
      rewrite id_left.
      rewrite z_iso_after_z_iso_inv.
      apply id_right.
    Qed.
  End Cartesians.

  Proposition is_cartesian_indexed_cat
              {x y : C}
              {f : x --> y}
              {xx : Φ x}
              {yy : Φ y}
              (ff : xx --> (Φ $ f) yy)
              (Hff : is_z_isomorphism ff)
    : @is_cartesian
        _
        indexed_cat_to_disp_cat
        y x
        f
        yy xx
        ff.
  Proof.
    intros w g ww hh ; cbn in *.
    use iscontraprop1.
    - exact (is_cartesian_indexed_cat_factorisation_unique Hff g hh).
    - simple refine (_ ,, _).
      + exact (is_cartesian_indexed_cat_factorisation Hff g hh).
      + exact (is_cartesian_indexed_cat_factorisation_commutes Hff g hh).
  Defined.

  Section CartesianAreIsos.
    Context {x y : C}
            {f : x --> y}
            {xx : Φ x}
            {yy : Φ y}
            (ff : xx --> (Φ $ f) yy)
            (Hff : @is_cartesian
                     _
                     indexed_cat_to_disp_cat
                     y x
                     f
                     yy xx
                     ff).

    Let ζ : (Φ $ f) yy --> (Φ $ identity x · f) yy
      := indexed_cat_id Φ x ((Φ $ f) yy) · indexed_cat_comp Φ f (identity x) yy.

    Let φ : (Φ $ f) yy --> (Φ $ identity x) xx
      := cartesian_factorisation
           Hff
           (identity _)
           ζ.

    Definition is_cartesian_to_iso_indexed_cat_inv
      : (Φ $ f) yy --> xx
      := φ · inv_from_z_iso (indexed_cat_id_z_iso Φ xx).

    Proposition is_cartesian_to_iso_indexed_cat_left
      : ff · is_cartesian_to_iso_indexed_cat_inv = identity xx.
    Proof.
      unfold is_cartesian_to_iso_indexed_cat_inv, φ.
      rewrite !assoc.
      refine (!_).
      use z_iso_inv_on_left.
      use (cartesian_factorisation_unique Hff) ; cbn.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        exact (cartesian_factorisation_commutes Hff (identity _) ζ).
      }
      unfold ζ.
      rewrite !assoc.
      apply maponpaths_2.
      etrans.
      {
        apply (nat_trans_ax (indexed_cat_id Φ x)).
      }
      apply maponpaths_2.
      refine (!_).
      apply id_left.
    Qed.

    Proposition is_cartesian_to_iso_indexed_cat_right
      : is_cartesian_to_iso_indexed_cat_inv · ff = identity ((Φ $ f) yy).
    Proof.
      unfold is_cartesian_to_iso_indexed_cat_inv, φ.
      rewrite !assoc'.
      etrans.
      {
        apply maponpaths.
        exact (!(nat_trans_ax (nat_z_iso_inv (indexed_cat_id_nat_z_iso Φ x)) _ _ ff)
               : inv_from_z_iso (indexed_cat_id_z_iso Φ xx)
                 · ff
                 =
                 # (Φ $ identity x) ff
                 · inv_from_z_iso (indexed_cat_id_z_iso Φ ((Φ $ f) yy))).
      }
      cbn.
      rewrite !assoc.
      refine (!_).
      use z_iso_inv_on_left.
      rewrite id_left.
      use (cancel_z_iso _ _ (indexed_cat_comp_z_iso Φ f (identity x) yy)).
      exact (cartesian_factorisation_commutes Hff (identity _) ζ).
    Qed.

    Definition is_cartesian_to_iso_indexed_cat
      : is_z_isomorphism ff.
    Proof.
      simple refine (_ ,, _ ,, _).
      - exact is_cartesian_to_iso_indexed_cat_inv.
      - exact is_cartesian_to_iso_indexed_cat_left.
      - exact is_cartesian_to_iso_indexed_cat_right.
    Defined.
  End CartesianAreIsos.

  (**
   5. The cleaving from an indexed category
   *)
  Definition indexed_cat_to_cleaving
    : cleaving indexed_cat_to_disp_cat.
  Proof.
    intros y x f yy ; cbn in *.
    refine ((Φ $ f) yy ,, identity _ ,, _).
    use is_cartesian_indexed_cat.
    apply is_z_isomorphism_identity.
  Defined.
End IndexedCatToFibration.
