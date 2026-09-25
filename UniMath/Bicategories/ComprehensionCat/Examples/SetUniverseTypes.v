(**

 Closure conditions for universes of sets

 One can construct a universe in the comprehension category of sets by providing
 a set `u : hSet` together with a map `el : u → hSet`, and we denote this universe
 by `u^`. We show that closure conditions of the universe `u` induce analogous
 closure conditions of the universe `u^`. For instance, if `u` contains the natural
 numbers, then so does `u^`. Note that the closure conditions for `u^` are not exactly
 the same as for `u`: since `u^` is a universe in a comprehension category, the closure
 conditions talk about arbitrary contexts, while the closure conditions for `u` do not.

 Content
 1. The unit type
 2. The natural numbers
 3. The type of propositions
 4. Propositional resizing
 5. ∑-types
 6. ∏-types
 7. Strictifying using a universe of sets

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.SetUniverses.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentSums.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiberwise.DependentProducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.SetFams.
Require Import UniMath.CategoryTheory.Arithmetic.ParameterizedNNO.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.SubobjectClassifier.SubobjectClassifier.
Require Import UniMath.CategoryTheory.CategoriesWithFamilies.CatsWithFams.
Require Import UniMath.Bicategories.ComprehensionCat.BicatOfCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.CompCatNotations.
Require Import UniMath.Bicategories.ComprehensionCat.DFLCompCat.
Require Import UniMath.Bicategories.ComprehensionCat.HPropMono.
Require Import UniMath.Bicategories.ComprehensionCat.PiTypeNotations.
Require Import UniMath.Bicategories.ComprehensionCat.Strictify.
Require Import UniMath.Bicategories.ComprehensionCat.Examples.SetModel.
Require Import UniMath.Bicategories.ComprehensionCat.Examples.SetModelUniverse.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.SigmaTypes.
Require Import UniMath.Bicategories.ComprehensionCat.TypeFormers.PiTypes.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.LocalProperties.
Require Import UniMath.Bicategories.ComprehensionCat.LocalProperty.Examples.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.CompCatOb.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.UniverseType.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUniv.DFLCompCatUniv.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatUnivProps.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatTypes.Constant.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatTypes.Resizing.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatTypes.Sigma.
Require Import UniMath.Bicategories.ComprehensionCat.Universes.CompCatTypes.Pi.

Local Open Scope cat.
Local Open Scope comp_cat.

(** The following is useful to make the goals more readable *)
#[local] Opaque set_comp_cat_tm_to_sec set_comp_cat_sec_to_tm.

(** * 1. The unit type *)
Definition set_comp_cat_univ_contains_unit
           (u : set_universe)
           (un : set_universe_contains_unit u)
  : unit_in_comp_cat_univ
      (set_dfl_full_comp_cat_with_univ u).
Proof.
  use make_type_in_comp_cat_univ.
  - use set_comp_cat_sec_to_tm.
    exact (λ _, set_universe_unit_code un).
  - use hset_equiv_weq_z_iso.
    use weqfibtototal ; cbn.
    refine (λ z, _).
    refine (set_universe_unit_weq un ∘ set_universe_eq_weq _)%weq.
    abstract
      (rewrite set_comp_cat_sec_to_tm_to_sec ;
       apply idpath).
Defined.

(** * 2. The natural numbers *)
Definition set_comp_cat_univ_contains_pnno
           (u : set_universe)
           (n : set_universe_contains_nat u)
  : pnno_in_comp_cat_univ
      (set_dfl_full_comp_cat_with_univ u)
      pnno_set_comp_cat.
Proof.
  use make_type_in_comp_cat_univ.
  - use set_comp_cat_sec_to_tm.
    exact (λ _, set_universe_nat_code n).
  - use hset_equiv_weq_z_iso.
    use weqfibtototal ; cbn.
    refine (λ z, _).
    refine (set_universe_nat_weq n ∘ set_universe_eq_weq _)%weq.
    abstract
      (rewrite set_comp_cat_sec_to_tm_to_sec ;
       apply idpath).
Defined.

(** * 3. The type of propositions *)
Definition set_comp_cat_univ_contains_hProp
           (u : set_universe)
           (ω : set_universe_contains_hProp u)
  : subobject_classifier_in_comp_cat_univ
      (set_dfl_full_comp_cat_with_univ u)
      subobject_classifier_set_comp_cat.
Proof.
  use make_type_in_comp_cat_univ.
  - use set_comp_cat_sec_to_tm.
    exact (λ _, set_universe_hProp_code ω).
  - use hset_equiv_weq_z_iso.
    use weqfibtototal ; cbn.
    refine (λ z, _).
    refine (set_universe_hProp_weq ω ∘ set_universe_eq_weq _)%weq.
    abstract
      (rewrite set_comp_cat_sec_to_tm_to_sec ;
       apply idpath).
Defined.

(** * 4. Propositional resizing *)
Definition set_comp_cat_univ_resizing_data
           (u : set_universe)
           (r : set_universe_resizing u)
  : resizing_in_comp_cat_univ
      (set_dfl_full_comp_cat_with_univ u).
Proof.
  use make_resizing_in_comp_cat_univ.
  - cbn.
    refine (λ Γ A HA, _).
    use set_comp_cat_sec_to_tm.
    refine (λ γ, _).
    exact (set_universe_resizing_code' r (A γ) (set_comp_cat_hprop_ty_inv A HA γ)).
  - cbn.
    refine (λ Γ A HA, _).
    use hset_equiv_weq_z_iso.
    use weqfibtototal ; cbn.
    refine (λ γ, _).
    refine (set_universe_resizing_weq' r _ _ ∘ set_universe_eq_weq _)%weq.
    abstract
      (rewrite set_comp_cat_sec_to_tm_to_sec ;
       apply idpath).
  - abstract
      (cbn ;
       intros ;
       apply idpath).
Defined.

Proposition set_comp_cat_univ_resizing_laws
            (u : set_universe)
            (r : set_universe_resizing u)
  : resizing_in_comp_cat_univ_is_stable
      (set_dfl_full_comp_cat_with_univ u)
      (set_comp_cat_univ_resizing_data u r).
Proof.
  intros Γ Δ s A HA.
  refine (set_univ_tm_subst_eq _ _ _ @ _).
  refine (maponpaths set_comp_cat_sec_to_tm _).
  use funextsec.
  intro γ.
  refine (maponpaths (λ z, z (s γ)) (set_comp_cat_sec_to_tm_to_sec _) @ _).
  apply set_universe_resizing_code_eq.
Qed.

Definition set_comp_cat_univ_resizing
           (u : set_universe)
           (r : set_universe_resizing u)
  : stable_resizing_in_comp_cat_univ
      (set_dfl_full_comp_cat_with_univ u).
Proof.
  use make_stable_resizing_in_comp_cat_univ.
  - exact (set_comp_cat_univ_resizing_data u r).
  - exact (set_comp_cat_univ_resizing_laws u r).
Defined.

Definition set_comp_cat_univ_unit
           (u : set_universe)
           (r : set_universe_resizing u)
  : unit_in_comp_cat_univ
      (set_dfl_full_comp_cat_with_univ u)
  := unit_in_comp_cat_univ_from_resizing
       (set_dfl_full_comp_cat_with_univ u)
       (set_comp_cat_univ_resizing_data u r).

(** * 5. ∑-types *)
Definition set_comp_cat_univ_sigma_data
           (u : set_universe)
           (sig : set_universe_contains_sigma u)
  : sigma_in_comp_cat_univ
      (set_dfl_full_comp_cat_with_univ u).
Proof.
  use make_sigma_in_comp_cat_univ.
  - cbn.
    refine (λ Γ a b, _).
    use set_comp_cat_sec_to_tm.
    refine (λ γ, _).
    use (set_universe_sigma_code sig).
    + exact (set_comp_cat_tm_to_sec a γ).
    + exact (λ a, set_comp_cat_tm_to_sec b (γ ,, a)).
  - cbn.
    refine (λ Γ a b, _).
    use hset_equiv_weq_z_iso.
    cbn.
    refine (weqtotal2asstol _ _ ∘ _)%weq.
    use weqfibtototal ; cbn.
    refine (λ γ, _).
    refine (set_universe_sigma_weq sig _ _ ∘ set_universe_eq_weq _)%weq.
    abstract
      (rewrite set_comp_cat_sec_to_tm_to_sec ;
       apply idpath).
  - abstract
      (cbn ;
       intros Γ a b ;
       apply idpath).
Defined.

Proposition set_sigma_in_comp_cat_univ_z_iso
            (u : set_universe)
            (sig : set_universe_contains_sigma u)
            {Γ : set_dfl_full_comp_cat_with_univ u}
            (a : tm Γ (dfl_full_comp_cat_univ Γ))
            (b : tm _ (dfl_full_comp_cat_univ
                         (Γ & comp_cat_univ_el
                                (dfl_full_comp_cat_el (set_dfl_full_comp_cat_with_univ u))
                                a)))
            (x : ∑ (γ : (Γ : hSet)),
                 comp_cat_univ_el
                   (dfl_full_comp_cat_el (set_dfl_full_comp_cat_with_univ u))
                   (sigma_in_comp_cat_univ_code (set_comp_cat_univ_sigma_data u sig) a b)
                   γ)
  : pr1 (sigma_in_comp_cat_univ_z_iso (set_comp_cat_univ_sigma_data u sig) a b) x
    =
    total2asstol
      _ _
      (pr1 x
       ,,
       set_universe_sigma_weq sig
         (set_comp_cat_tm_to_sec a (pr1 x))
         (λ y, set_comp_cat_tm_to_sec b (pr1 x ,, y))
         (set_universe_eq
            (maponpaths (λ z, z (pr1 x)) (set_comp_cat_sec_to_tm_to_sec _))
            (pr2 x))).
Proof.
  cbn -[sub_comp_cat_univ fiber_category comp_subst_ty_inv].
  apply maponpaths.
  unfold totalfun.
  apply maponpaths.
  apply maponpaths.
  apply set_universe_eq_path.
Qed.

Proposition set_comp_cat_univ_sigma_laws_code
            {u : set_universe}
            (sig : set_universe_contains_sigma u)
            {Γ Δ : set_dfl_full_comp_cat_with_univ u}
            (s : Γ --> Δ)
            (a : tm Δ (dfl_full_comp_cat_univ Δ))
            (b : tm _ (dfl_full_comp_cat_univ
                         (Δ & comp_cat_univ_el
                                (dfl_full_comp_cat_el (set_dfl_full_comp_cat_with_univ u))
                                a)))
  : sigma_in_comp_cat_univ_code
      (set_comp_cat_univ_sigma_data u sig) a b [[ s ]]tm
    ↑ sub_dfl_comp_cat_univ s
    =
    sigma_in_comp_cat_univ_code
      (set_comp_cat_univ_sigma_data u sig)
      (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
      (b [[ extend_sub_univ
              (dfl_full_comp_cat_el (set_dfl_full_comp_cat_with_univ u))
              s a ]]tm
       ↑ sub_dfl_comp_cat_univ
           (C := set_dfl_full_comp_cat_with_univ u)
           (extend_sub_univ
              (dfl_full_comp_cat_el (set_dfl_full_comp_cat_with_univ u))
              s a)).
Proof.
  refine (set_univ_tm_subst_eq _ _ _ @ _).
  refine (maponpaths set_comp_cat_sec_to_tm _).
  use funextsec.
  intro γ.
  refine (maponpaths (λ z, z (s γ)) (set_comp_cat_sec_to_tm_to_sec _) @ _).
  use set_universe_sigma_code_eq.
  - abstract
      (refine (!_) ;
       refine (maponpaths
                 (λ z, set_comp_cat_tm_to_sec z γ)
                 (set_univ_tm_subst_eq _ _ _)
               @ _) ;
       rewrite set_comp_cat_sec_to_tm_to_sec ;
       apply idpath).
  - intros x.
    refine (!_).
    etrans.
    {
      refine (maponpaths (λ z, set_comp_cat_tm_to_sec z _) _).
      exact (set_univ_tm_subst_eq _ _ _).
    }
    rewrite set_comp_cat_sec_to_tm_to_sec.
    apply maponpaths.
    cbn.
    rewrite set_universe_eq_comp.
    rewrite set_universe_eq_idpath.
    apply idpath.
Qed.

(** The following makes the goals more readable for the next proof *)
Local Arguments set_universe_eq {u a₁ a₂ p} x.

Proposition set_comp_cat_univ_sigma_laws
            (u : set_universe)
            (sig : set_universe_contains_sigma u)
  : sigma_in_comp_cat_univ_is_stable
      (set_dfl_full_comp_cat_with_univ u)
      (set_comp_cat_univ_sigma_data u sig).
Proof.
  intros Γ Δ s a b.
  refine (set_comp_cat_univ_sigma_laws_code sig s a b ,, _).
  use funextsec.
  intro γ.
  rewrite !hset_category_comp.
  etrans.
  {
    apply maponpaths.
    refine (maponpaths (comp_cat_comp_mor_over_sub (C := set_dfl_full_comp_cat) _ _) _).
    refine (set_sigma_in_comp_cat_univ_z_iso _ _ _ _ _ @ _).
    do 2 apply maponpaths.
    use (set_universe_sigma_weq_eq
           sig
           (set_comp_cat_univ_el_stable_inv_path _ _ _ _)).
    {
      exact (λ z, set_comp_cat_tm_to_sec b (s (pr1 γ) ,, z)).
    }
    intro z.
    refine (set_comp_cat_univ_el_stable_inv_path _ _ _ _ @ _).
    apply maponpaths.
    cbn.
    apply maponpaths.
    apply set_universe_eq_path.
  }
  refine (_ @ !(set_sigma_in_comp_cat_univ_z_iso _ _ _ _ _)).
  refine (eqtohomot (set_comp_cat_extend_over _ _) _ @ _).
  use (invmaponpathsweq (weqtotal2asstor _ _) _ _).
  refine (_ @ !(homotweqinvweq (weqtotal2asstor _ _) _)).
  refine (maponpaths (λ z, _ ,, z) _).
  cbn -[sub_comp_cat_univ fiber_category comp_subst_ty_inv].
  refine (!_).
  etrans.
  {
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      rewrite fam_disp_cat_fiber_comp.
      etrans.
      {
        apply maponpaths.
        apply set_comp_cat_el_map_on_eq.
      }
      apply set_universe_eq_comp.
    }
    apply set_universe_eq_comp.
  }
  refine (!_).
  rewrite fam_disp_cat_fiber_comp.
  use set_universe_sigma_el_eq.
  - cbn -[sub_comp_cat_univ fiber_category comp_subst_ty_inv].
    rewrite !set_universe_eq_comp.
    rewrite set_universe_eq_idpath.
    apply maponpaths.
    apply maponpaths.
    apply set_universe_eq_path.
  - cbn -[sub_comp_cat_univ fiber_category comp_subst_ty_inv].
    etrans.
    {
      exact (set_comp_cat_comp_subst_ty_inv
               _ _
               (set_comp_cat_el_map u (∑ x, set_comp_cat_el_map u Δ a x)%set b)
               _).
    }
    refine (set_universe_eq_comp _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      refine (set_universe_sigma_weq_eq_on_el sig _ _ (set_universe_eq_comp _ _ _ @ _)).
      apply set_universe_eq_path.
    }
    refine (set_universe_eq_comp _ _ _ @ _).
    use set_universe_eq_path.
Qed.

Definition set_comp_cat_univ_sigma
           (u : set_universe)
           (sig : set_universe_contains_sigma u)
  : stable_sigma_in_comp_cat_univ
      (set_dfl_full_comp_cat_with_univ u).
Proof.
  use make_stable_sigma_in_comp_cat_univ.
  - exact (set_comp_cat_univ_sigma_data u sig).
  - exact (set_comp_cat_univ_sigma_laws u sig).
Defined.

(** * 6. ∏-types *)
Definition set_comp_cat_univ_pi_data
           (u : set_universe)
           (pi : set_universe_contains_pi u)
  : pi_in_comp_cat_univ
      (set_dfl_full_comp_cat_with_univ u)
      dependent_prod_set_comp_cat.
Proof.
  use make_pi_in_comp_cat_univ.
  - cbn.
    refine (λ Γ a b, _).
    use set_comp_cat_sec_to_tm.
    refine (λ γ, _).
    use (set_universe_pi_code pi).
    + exact (set_comp_cat_tm_to_sec a γ).
    + exact (λ a, set_comp_cat_tm_to_sec b (γ ,, a)).
  - cbn.
    refine (λ Γ a b, _).
    use hset_equiv_weq_z_iso.
    use weqfibtototal ; cbn.
    refine (λ γ, _).
    refine (set_universe_pi_weq pi _ _ ∘ set_universe_eq_weq _)%weq.
    abstract
      (rewrite set_comp_cat_sec_to_tm_to_sec ;
       apply idpath).
  - abstract
      (cbn ;
       intros Γ a b ;
       apply idpath).
Defined.

Proposition set_comp_cat_univ_pi_laws_code
            {u : set_universe}
            (pi : set_universe_contains_pi u)
            {Γ Δ : set_dfl_full_comp_cat_with_univ u}
            (s : Γ --> Δ)
            (a : tm Δ (dfl_full_comp_cat_univ Δ))
            (b : tm _ (dfl_full_comp_cat_univ
                         (Δ & comp_cat_univ_el
                                (dfl_full_comp_cat_el (set_dfl_full_comp_cat_with_univ u))
                                a)))
  : pi_in_comp_cat_univ_code
      (set_comp_cat_univ_pi_data u pi) a b [[ s ]]tm
    ↑ sub_dfl_comp_cat_univ s
    =
    pi_in_comp_cat_univ_code
      (set_comp_cat_univ_pi_data u pi)
      (a [[ s ]]tm ↑ sub_dfl_comp_cat_univ s)
      (b [[ extend_sub_univ
              (dfl_full_comp_cat_el (set_dfl_full_comp_cat_with_univ u))
              s a ]]tm
       ↑ sub_dfl_comp_cat_univ
           (C := set_dfl_full_comp_cat_with_univ u)
           (extend_sub_univ
              (dfl_full_comp_cat_el (set_dfl_full_comp_cat_with_univ u))
              s a)).
Proof.
  refine (set_univ_tm_subst_eq _ _ _ @ _).
  refine (maponpaths set_comp_cat_sec_to_tm _).
  use funextsec.
  intro γ.
  refine (maponpaths (λ z, z (s γ)) (set_comp_cat_sec_to_tm_to_sec _) @ _).
  use set_universe_pi_code_eq.
  - abstract
      (refine (!_) ;
       refine (maponpaths
                 (λ z, set_comp_cat_tm_to_sec z γ)
                 (set_univ_tm_subst_eq _ _ _)
               @ _) ;
       rewrite set_comp_cat_sec_to_tm_to_sec ;
       apply idpath).
  - intros x.
    refine (!_).
    etrans.
    {
      refine (maponpaths (λ z, set_comp_cat_tm_to_sec z _) _).
      exact (set_univ_tm_subst_eq _ _ _).
    }
    rewrite set_comp_cat_sec_to_tm_to_sec.
    apply maponpaths.
    cbn.
    rewrite set_universe_eq_comp.
    rewrite set_universe_eq_idpath.
    apply idpath.
Qed.

(* This is useful in the next proof, because it prevents certain unfoldings *)
#[local] Opaque fiber_category.

Proposition set_comp_cat_univ_pi_laws
            (u : set_universe)
            (pi : set_universe_contains_pi u)
  : pi_in_comp_cat_univ_is_stable
      (set_dfl_full_comp_cat_with_univ u)
      dependent_prod_set_comp_cat
      (set_comp_cat_univ_pi_data u pi).
Proof.
  intros Γ Δ s a b.
  refine (set_comp_cat_univ_pi_laws_code pi s a b ,, _).
  use funextsec.
  intro γ.
  rewrite !hset_category_comp.
  refine (maponpaths (λ z, _ ,, z) _).
  simpl.
  rewrite !set_comp_cat_subst.
  refine (!_).
  refine (set_comp_cat_pi_subst_coerce_inv _ _ _ _ @ _).
  use funextsec.
  intro φ.
  rewrite set_comp_cat_pi_coerce.
  rewrite !fam_disp_cat_fiber_comp. (* Here we use that `fiber_category` is opaque *)
  etrans.
  {
    apply maponpaths.
    refine (set_comp_cat_el_map_on_eq _ _ _ @ _).
    etrans.
    {
      apply maponpaths.
      exact (eqtohomot (set_comp_cat_univ_el_stable_mor _ _ _ _) _).
    }
    apply set_universe_eq_comp.
  }
  etrans.
  {
    exact (eqtohomot
             (eqtohomot
                (set_comp_cat_univ_el_stable_inv
                   u
                   (comp_cat_extend_over
                      (comp_cat_univ_el
                         (dfl_full_comp_cat_el (set_dfl_full_comp_cat_with_univ u))
                         a)
                      s)
                   b)
                (pr1 γ ,, φ))
             _).
  }
  rewrite set_universe_eq_comp.
  etrans.
  {
    apply maponpaths.
    use (eqtohomot
           (set_universe_pi_weq_eq
              pi
              (set_comp_cat_univ_el_stable_inv_path u s a (pr1 γ))
              _ _)
           _).
    {
      exact (λ z, set_comp_cat_tm_to_sec b (s (pr1 γ) ,, z)).
    }
    intro z.
    refine (set_comp_cat_univ_el_stable_inv_path _ _ _ _ @ _).
    apply maponpaths.
    cbn.
    apply maponpaths.
    apply set_universe_eq_path.
  }
  rewrite set_universe_eq_comp.
  refine (set_universe_eq_path _ _ _ @ !(set_universe_pi_weq_eq_el _ _ _ _ _)).
  - etrans.
    {
      refine (maponpaths set_universe_eq _).
      exact (eqtohomot
               (eqtohomot
                  (set_comp_cat_univ_el_stable_inv
                     u
                     s
                     _)
                  _)
               _).
    }
    rewrite set_universe_eq_comp.
    etrans.
    {
      refine (maponpaths set_universe_eq _).
      exact (set_comp_cat_el_map_on_eq _ _ _).
    }
    rewrite !set_universe_eq_comp.
    apply set_universe_eq_path.
  - rewrite set_comp_cat_subst.
    refine (!_).
    cbn.
    rewrite set_universe_eq_comp.
    apply set_universe_eq_idpath.
Qed.

Definition set_comp_cat_univ_pi
           (u : set_universe)
           (pi : set_universe_contains_pi u)
  : stable_pi_in_comp_cat_univ
      (set_dfl_full_comp_cat_with_univ u)
      dependent_prod_set_comp_cat.
Proof.
  use make_stable_pi_in_comp_cat_univ.
  - exact (set_comp_cat_univ_pi_data u pi).
  - exact (set_comp_cat_univ_pi_laws u pi).
Defined.

(** * 7. Strictifying using a universe of sets *)
Section StrictifySetUniverses.
  Context (u : set_universe)
          (un : set_universe_contains_unit u)
          (sig : set_universe_contains_sigma u).

  Definition strictify_set_universe
    : cwf
    := strictify_dfl_full_comp_cat_univ
         (set_dfl_full_comp_cat_with_univ u)
         (set_comp_cat_univ_contains_unit u un)
         (set_comp_cat_univ_sigma u sig).

  Let C : dfl_full_comp_cat_with_univ := set_dfl_full_comp_cat_with_univ u.
  Let CC : cwf := strictify_set_universe.

  Definition strictify_set_universe_ctx
    : (CC : UU) ≃ u.
  Proof.
    exact (weqfunfromunit _ ∘ set_comp_cat_tm_weq (dfl_full_comp_cat_univ (C := C) []))%weq.
  Defined.

  Definition strictify_set_universe_ty
             (Γ : CC)
    : cwf_ty Γ
      ≃
      (set_universe_el (strictify_set_universe_ctx Γ) → u).
  Proof.
    refine (_ ∘ set_comp_cat_tm_weq _)%weq.
    cbn.
    use weqbfun.
    use invweq.
    exact (weqtotal2overunit _).
  Defined.

  Definition strictify_set_universe_tm
             (Γ : CC)
             (A : cwf_ty Γ)
    : cwf_tm A
      ≃
      ∏ (x : set_universe_el (strictify_set_universe_ctx Γ)),
      set_universe_el (strictify_set_universe_ty Γ A x).
  Proof.
    refine (_ ∘ set_comp_cat_tm_weq _)%weq.
    cbn.
    use invweq.
    use weqonsec.
    - exact (invweq (weqtotal2overunit _)).
    - intros x ; cbn.
      exact (idweq _).
  Defined.
End StrictifySetUniverses.
