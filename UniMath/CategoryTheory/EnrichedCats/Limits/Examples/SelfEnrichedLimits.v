(*****************************************************************

 Limits in self enriched categories

 Self enriched categories inherit their limits from the
 underlying category. In addition, self enriched categories always
 have powers, and these are given by the internal hom.

 Contents
 1. Terminal object
 2. Binary products
 3. Equalizers
 4. Powers
 5. Type indexed products

 *****************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.EnrichedCats.Enrichment.
Require Import UniMath.CategoryTheory.EnrichedCats.Examples.SelfEnriched.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedTerminal.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedBinaryProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedProducts.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedEqualizers.
Require Import UniMath.CategoryTheory.EnrichedCats.Limits.EnrichedPowers.
Require Import UniMath.CategoryTheory.Monoidal.Categories.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Symmetric.
Require Import UniMath.CategoryTheory.Monoidal.Structure.Closed.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Equalizers.
Require Import UniMath.CategoryTheory.Limits.Products.

Local Open Scope cat.
Local Open Scope moncat.
Import MonoidalNotations.

Opaque sym_mon_braiding.

Section SelfEnrichmentLimits.
  Context (V : sym_mon_closed_cat).

  (**
   1. Terminal object
   *)
  Section SelfEnrichmentTerminal.
    Context (v : V)
            (Hv : isTerminal V v).

    Definition self_enrichment_is_terminal_enriched
      : is_terminal_enriched (self_enrichment V) v.
    Proof.
      use make_is_terminal_enriched.
      - exact (λ _ _, internal_lam (TerminalArrow (_ ,, Hv) _)).
      - abstract
          (cbn ;
           intros w y f g ;
           use internal_funext ;
           intros a h ;
           apply (@TerminalArrowEq _ (v ,, Hv))).
    Defined.
  End SelfEnrichmentTerminal.

  Definition self_enrichment_terminal
             (HV : Terminal V)
    : terminal_enriched (self_enrichment V)
    := pr1 HV ,, self_enrichment_is_terminal_enriched _ (pr2 HV).

  (**
   2. Binary products
   *)
  Section SelfEnrichmentProduct.
    Context {v₁ v₂ w : V}
            (π₁ : w --> v₁)
            (π₂ : w --> v₂)
            (H : isBinProduct _ _ _ _ π₁ π₂).

    Let prod : BinProduct V v₁ v₂ := make_BinProduct _ _ _ _ _ _ H.

    Definition self_enrichment_binary_product_pr1
      : I_{V} --> w ⊸ v₁
      := internal_lam (mon_lunitor _ · π₁).

    Definition self_enrichment_binary_product_pr2
      : I_{V} --> w ⊸ v₂
      := internal_lam (mon_lunitor _ · π₂).

    Definition self_enrichment_binary_products_cone
      : enriched_binary_prod_cone (self_enrichment V) v₁ v₂.
    Proof.
      use make_enriched_binary_prod_cone.
      - exact w.
      - exact self_enrichment_binary_product_pr1.
      - exact self_enrichment_binary_product_pr2.
    Defined.

    Definition self_enrichment_pair
               {a b : V}
               (f : a --> b ⊸ v₁)
               (g : a --> b ⊸ v₂)
      : a --> b ⊸ w
      := internal_lam
           (BinProductArrow
              V
              prod
              (f #⊗ identity _ · internal_eval _ _)
              (g #⊗ identity _ · internal_eval _ _)).

    Proposition self_enrichment_pair_pr1
                {a b : V}
                (f : a --> b ⊸ v₁)
                (g : a --> b ⊸ v₂)
      : self_enrichment_pair f g
        · postcomp_arr
            (self_enrichment V)
            _
            (internal_to_arr self_enrichment_binary_product_pr1)
        =
        f.
    Proof.
      rewrite self_enrichment_postcomp.
      use internal_funext.
      intros c h ; cbn.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      etrans.
      {
        rewrite tensor_split.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        unfold self_enrichment_pair.
        rewrite internal_beta.
        unfold internal_to_arr.
        unfold self_enrichment_binary_product_pr1.
        rewrite !assoc'.
        rewrite internal_beta.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite mon_linvunitor_lunitor.
          apply id_left.
        }
        apply (BinProductPr1Commutes _ _ _ prod).
      }
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
    Qed.

    Proposition self_enrichment_pair_pr2
                {a b : V}
                (f : a --> b ⊸ v₁)
                (g : a --> b ⊸ v₂)
      : self_enrichment_pair f g
        · postcomp_arr
            (self_enrichment V)
            _
            (internal_to_arr self_enrichment_binary_product_pr2)
        =
        g.
    Proof.
      rewrite self_enrichment_postcomp.
      use internal_funext.
      intros c h ; cbn.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      etrans.
      {
        rewrite tensor_split.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        unfold self_enrichment_pair.
        rewrite internal_beta.
        unfold internal_to_arr.
        unfold self_enrichment_binary_product_pr2.
        rewrite !assoc'.
        rewrite internal_beta.
        etrans.
        {
          apply maponpaths.
          rewrite !assoc.
          rewrite mon_linvunitor_lunitor.
          apply id_left.
        }
        apply (BinProductPr2Commutes _ _ _ prod).
      }
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
    Qed.

    Definition pair_fun_pr1
               {a b : V}
               (φ : a --> b ⊸ w)
      : a --> b ⊸ v₁
      := φ · postcomp_arr
               (self_enrichment V)
               _
               (internal_to_arr self_enrichment_binary_product_pr1).

    Definition pair_fun_pr2
               {a b : V}
               (φ : a --> b ⊸ w)
      : a --> b ⊸ v₂
      := φ · postcomp_arr
               (self_enrichment V)
               _
               (internal_to_arr self_enrichment_binary_product_pr2).

    Proposition pair_eq_pr1
                {a b c : V}
                (φ : a --> b ⊸ w)
                (h : c --> b)
      : φ #⊗ h · internal_eval b w · BinProductPr1 V prod
        =
        pair_fun_pr1 φ #⊗ h · internal_eval _ _.
    Proof.
      unfold pair_fun_pr1 ; cbn.
      rewrite self_enrichment_postcomp.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      apply maponpaths.
      rewrite internal_beta.
      apply maponpaths.
      unfold internal_to_arr.
      unfold self_enrichment_binary_product_pr1.
      rewrite !assoc'.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite mon_linvunitor_lunitor.
      rewrite id_left.
      apply idpath.
    Qed.

    Proposition pair_eq_pr2
                {a b c : V}
                (φ : a --> b ⊸ w)
                (h : c --> b)
      : φ #⊗ h · internal_eval b w · BinProductPr2 V prod
        =
        pair_fun_pr2 φ #⊗ h · internal_eval _ _.
    Proof.
      unfold pair_fun_pr2 ; cbn.
      rewrite self_enrichment_postcomp.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      apply maponpaths.
      rewrite internal_beta.
      apply maponpaths.
      unfold internal_to_arr.
      unfold self_enrichment_binary_product_pr2.
      rewrite !assoc'.
      rewrite internal_beta.
      rewrite !assoc.
      rewrite mon_linvunitor_lunitor.
      rewrite id_left.
      apply idpath.
    Qed.

    Proposition self_enrichment_pair_eq
                {a b : V}
                (φ ψ : a --> b ⊸ w)
                (p₁ : pair_fun_pr1 φ = pair_fun_pr1 ψ)
                (p₂ : pair_fun_pr2 φ = pair_fun_pr2 ψ)
        : φ = ψ.
    Proof.
      use internal_funext.
      intros c h.
      use (BinProductArrowsEq _ _ _ prod).
      - rewrite !pair_eq_pr1.
        rewrite p₁.
        apply idpath.
      - rewrite !pair_eq_pr2.
        rewrite p₂.
        apply idpath.
    Qed.
  End SelfEnrichmentProduct.

  Definition self_enrichment_binary_products
             (PV : BinProducts V)
    : enrichment_binary_prod (self_enrichment V).
  Proof.
    intros v₁ v₂.
    pose (w := PV v₁ v₂ : V).
    pose (π₁ := BinProductPr1 _ (PV v₁ v₂) : w --> v₁).
    pose (π₂ := BinProductPr2 _ (PV v₁ v₂) : w --> v₂).
    pose (H := pr2 (PV v₁ v₂) : isBinProduct V v₁ v₂ w π₁ π₂).
    simple refine (_ ,, _).
    - exact (self_enrichment_binary_products_cone π₁ π₂).
    - use make_is_binary_prod_enriched.
      + exact (λ _ _ f g, self_enrichment_pair π₁ π₂ H f g).
      + exact (λ _ _ f g, self_enrichment_pair_pr1 π₁ π₂ H f g).
      + exact (λ _ _ f g, self_enrichment_pair_pr2 π₁ π₂ H f g).
      + exact (λ _ _ f g, self_enrichment_pair_eq π₁ π₂ H f g).
  Defined.

  (**
   3. Equalizers
   *)
  Section SelfEnrichmentEqualizer.
    Context {v₁ v₂ e : V}
            {f g : v₁ --> v₂}
            (p : e --> v₁)
            (pfg : p · f = p · g)
            (H : isEqualizer f g p pfg).

    Let Eq : Equalizer f g := make_Equalizer _ _ _ _ H.

    Proposition self_enrichment_equalizer_cone_eq
      : internal_to_arr (internal_lam (mon_lunitor e · p)) · f
        =
        internal_to_arr (internal_lam (mon_lunitor e · p)) · g.
    Proof.
      unfold internal_to_arr.
      rewrite !assoc'.
      rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)).
      rewrite internal_beta.
      rewrite !assoc.
      rewrite !mon_linvunitor_lunitor.
      rewrite !id_left.
      exact pfg.
    Qed.

    Definition self_enrichment_equalizer_cone
      : enriched_equalizer_cone (self_enrichment V) f g.
    Proof.
      use make_enriched_equalizer_cone.
      - exact e.
      - exact (internal_lam (mon_lunitor _ · p)).
      - exact self_enrichment_equalizer_cone_eq.
    Defined.

    Proposition self_enrichment_equalizer_eq
                {a b : V}
                (φ₁ φ₂ : b --> a ⊸ e)
                (q : φ₁ · postcomp_arr
                            (self_enrichment V)
                            a
                            (internal_to_arr (internal_lam (mon_lunitor e · p)))
                     =
                     φ₂ · postcomp_arr
                            (self_enrichment V)
                            a
                            (internal_to_arr (internal_lam (mon_lunitor e · p))))
      : φ₁ = φ₂.
    Proof.
      use internal_funext.
      intros w h.
      use (EqualizerInsEq Eq) ; cbn.
      rewrite !self_enrichment_postcomp in q.
      pose (maponpaths (λ z, z #⊗ identity _ · internal_eval _ _) q)
        as q'.
      cbn in q'.
      rewrite !tensor_comp_id_r in q'.
      rewrite !assoc' in q'.
      rewrite !internal_beta in q'.
      unfold internal_to_arr in q'.
      rewrite !assoc' in q'.
      rewrite !internal_beta in q'.
      rewrite !(maponpaths (λ z, _ · (_ · z)) (assoc _ _ _)) in q'.
      rewrite !mon_linvunitor_lunitor in q'.
      rewrite id_left in q'.
      rewrite tensor_split.
      rewrite !assoc'.
      rewrite q'.
      rewrite !assoc.
      rewrite <- tensor_split.
      apply idpath.
    Qed.

    Proposition self_enrichment_equalizer_arr_eq
                {a b : V}
                (h : b --> a ⊸ v₁)
                (q : h · postcomp_arr (self_enrichment V) _ f
                     =
                     h · postcomp_arr (self_enrichment V) _ g)
      : h #⊗ identity a · internal_eval a v₁ · f
        =
        h #⊗ identity a · internal_eval a v₁ · g.
    Proof.
      rewrite !self_enrichment_postcomp in q.
      pose (maponpaths (λ z, z #⊗ identity _ · internal_eval _ _) q)
        as q'.
      cbn in q'.
      rewrite !tensor_comp_id_r in q'.
      rewrite !assoc' in q'.
      rewrite !internal_beta in q'.
      rewrite !assoc in q'.
      exact q'.
    Qed.

    Definition self_enrichment_equalizer_arr
               {a b : V}
               (h : b --> a ⊸ v₁)
               (q : h · postcomp_arr (self_enrichment V) _ f
                    =
                    h · postcomp_arr (self_enrichment V) _ g)
      : b --> a ⊸ e.
    Proof.
      use internal_lam.
      use (EqualizerIn Eq).
      - exact (h #⊗ identity _ · internal_eval _ _).
      - exact (self_enrichment_equalizer_arr_eq h q).
    Defined.

    Definition self_enrichment_equalizer_arr_pr
               {a b : V}
               (h : b --> a ⊸ v₁)
               (q : h · postcomp_arr (self_enrichment V) _ f
                    =
                    h · postcomp_arr (self_enrichment V) _ g)
      : self_enrichment_equalizer_arr h q
        · postcomp_arr
            (self_enrichment V)
            _
            (internal_to_arr (internal_lam (mon_lunitor e · p)))
        =
        h.
    Proof.
      rewrite self_enrichment_postcomp ; cbn.
      use internal_funext.
      intros c k.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      unfold internal_to_arr.
      rewrite !assoc'.
      rewrite internal_beta.
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite mon_linvunitor_lunitor.
        apply id_left.
      }
      unfold self_enrichment_equalizer_arr.
      etrans.
      {
        rewrite tensor_split.
        rewrite !assoc.
        etrans.
        {
          apply maponpaths_2.
          rewrite !assoc'.
          rewrite internal_beta.
          apply idpath.
        }
        rewrite !assoc'.
        rewrite (EqualizerCommutes Eq).
        rewrite !assoc.
        rewrite <- tensor_split.
        apply idpath.
      }
      apply idpath.
    Qed.

    Definition self_enrichment_equalizer_is_equalizer
      : is_equalizer_enriched
          (self_enrichment V)
          f g
          self_enrichment_equalizer_cone.
    Proof.
      use make_is_equalizer_enriched.
      - exact (λ _ _ h₁ h₂ q, self_enrichment_equalizer_eq h₁ h₂ q).
      - exact (λ _ _ h q, self_enrichment_equalizer_arr h q).
      - exact (λ _ _ h q, self_enrichment_equalizer_arr_pr h q).
    Defined.
  End SelfEnrichmentEqualizer.

  Definition self_enrichment_equalizers
             (EV : Equalizers V)
    : enrichment_equalizers (self_enrichment V).
  Proof.
    intros v₁ v₂ f g.
    pose (e := EV _ _ f g : V).
    pose (p := EqualizerArrow (EV _ _ f g) : e --> v₁).
    pose (pfg := EqualizerEqAr (EV _ _ f g) : p · f = p · g).
    pose (H := pr22 (EV _ _ f g) : isEqualizer f g p pfg).
    exact (self_enrichment_equalizer_cone p pfg
           ,,
           self_enrichment_equalizer_is_equalizer p pfg H).
  Defined.

  (**
   4. Powers
   *)
  Section SelfEnrichmentPower.
    Context (v₁ v₂ : V).

    Definition self_enrichment_power_cone
      : power_cone (self_enrichment V) v₁ v₂.
    Proof.
      use make_power_cone.
      - exact (v₁ ⊸ v₂).
      - exact (internal_lam (sym_mon_braiding _ _ _ · internal_eval v₁ v₂)).
    Defined.

    Proposition is_power_self_enrichment_power_cone_eq_1
                (w : V)
      : is_power_enriched_map _ _ _ self_enrichment_power_cone w
        · internal_swap_arg v₁ v₂ w
        =
        identity _.
    Proof.
      use internal_funext.
      intros a₁ h₁.
      unfold internal_swap_arg.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      use internal_funext.
      intros a₂ h₂.
      rewrite tensor_comp_r_id_r.
      rewrite !assoc'.
      rewrite internal_beta.
      etrans.
      {
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite tensor_sym_mon_braiding.
        rewrite tensor_comp_l_id_l.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_rassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        do 2 apply maponpaths_2.
        rewrite tensor_split.
        rewrite !assoc'.
        apply maponpaths.
        unfold is_power_enriched_map.
        rewrite internal_beta.
        apply idpath.
      }
      cbn.
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        apply maponpaths.
        unfold internal_comp.
        rewrite internal_beta.
        apply idpath.
      }
      rewrite !assoc'.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_sym_mon_braiding.
        rewrite tensor_comp_r_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_id_id.
        rewrite !assoc.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply idpath.
      }
      rewrite !assoc.
      apply maponpaths_2.
      rewrite !assoc'.
      etrans.
      {
        rewrite !assoc.
        do 4 apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_rassociator.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_comp_id_l.
        rewrite <- tensor_sym_mon_braiding.
        rewrite tensor_comp_id_l.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- tensor_lassociator.
        rewrite tensor_split'.
        apply idpath.
      }
      rewrite !assoc'.
      refine (_ @ !(tensor_comp_r_id_l _ _ _)).
      apply maponpaths.
      etrans.
      {
        do 4 apply maponpaths.
        rewrite tensor_sym_mon_braiding.
        apply idpath.
      }
      refine (_ @ !(tensor_split _ _)).
      apply maponpaths.
      refine (_ @ id_left _).
      rewrite !assoc.
      apply maponpaths_2.
      refine (!(id_right _) @ _).
      rewrite !assoc'.
      rewrite <- mon_lassociator_rassociator.
      apply maponpaths.
      etrans.
      {
        do 3 apply maponpaths.
        rewrite !assoc.
        apply maponpaths_2.
        apply sym_mon_hexagon_lassociator.
      }
      etrans.
      {
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_id_r.
        rewrite sym_mon_braiding_inv.
        rewrite tensor_id_id.
        rewrite id_left.
        apply idpath.
      }
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite mon_rassociator_lassociator.
        rewrite id_left.
        apply idpath.
      }
      rewrite !assoc.
      rewrite <- tensor_comp_id_l.
      rewrite sym_mon_braiding_inv.
      rewrite tensor_id_id.
      apply id_left.
    Qed.

    Proposition is_power_self_enrichment_power_cone_eq_2
                (w : V)
      : internal_swap_arg v₁ v₂ w
        · is_power_enriched_map (self_enrichment V) v₁ v₂ self_enrichment_power_cone w
        =
        identity _.
    Proof.
      use internal_funext.
      intros a₁ h₁.
      rewrite tensor_comp_r_id_r.
      unfold is_power_enriched_map.
      rewrite !assoc'.
      rewrite internal_beta ; cbn.
      use internal_funext.
      intros a₂ h₂.
      rewrite !tensor_comp_r_id_r.
      rewrite !assoc'.
      unfold internal_comp.
      rewrite internal_beta.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_left.
        rewrite tensor_sym_mon_braiding.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite tensor_id_id.
        rewrite !assoc.
        rewrite <- tensor_split'.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply idpath.
      }
      etrans.
      {
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        rewrite tensor_sym_mon_braiding.
        rewrite tensor_split.
        rewrite tensor_comp_id_r.
        rewrite !assoc'.
        do 2 apply maponpaths.
        rewrite !assoc.
        rewrite tensor_lassociator.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite tensor_sym_mon_braiding.
        rewrite !assoc'.
        apply maponpaths.
        rewrite !assoc.
        rewrite <- tensor_comp_mor.
        rewrite id_right.
        unfold internal_swap_arg.
        rewrite internal_beta.
        rewrite tensor_split.
        rewrite !assoc'.
        rewrite internal_beta.
        apply idpath.
      }
      rewrite !assoc.
      do 2 apply maponpaths_2.
      etrans.
      {
        do 3 apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_sym_mon_braiding.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite <- tensor_id_id.
          rewrite <- tensor_lassociator.
          apply idpath.
        }
        rewrite !assoc.
        apply maponpaths_2.
        rewrite !assoc'.
        rewrite <- tensor_comp_id_r.
        rewrite <- tensor_sym_mon_braiding.
        rewrite tensor_comp_id_r.
        rewrite !assoc.
        apply maponpaths_2.
        rewrite <- !tensor_comp_mor.
        rewrite !id_right, id_left.
        apply idpath.
      }
      rewrite !assoc'.
      refine (_ @ id_right _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !assoc.
        rewrite sym_mon_hexagon_lassociator.
        rewrite !assoc'.
        etrans.
        {
          do 2 apply maponpaths.
          rewrite !assoc.
          rewrite <- tensor_comp_id_l.
          rewrite sym_mon_braiding_inv.
          rewrite tensor_id_id.
          apply id_left.
        }
        rewrite mon_lassociator_rassociator.
        apply id_right.
      }
      rewrite <- tensor_comp_id_r.
      rewrite sym_mon_braiding_inv.
      apply tensor_id_id.
    Qed.

    Definition is_power_self_enrichment_power_cone
      : is_power_enriched (self_enrichment V) v₁ v₂ self_enrichment_power_cone.
    Proof.
      use make_is_power_enriched.
      - exact (λ w, internal_swap_arg v₁ v₂ w).
      - exact is_power_self_enrichment_power_cone_eq_1.
      - exact is_power_self_enrichment_power_cone_eq_2.
    Defined.
  End SelfEnrichmentPower.

  Definition self_enrichment_powers
    : enrichment_power (self_enrichment V)
    := λ v₁ v₂,
      self_enrichment_power_cone v₁ v₂
      ,,
      is_power_self_enrichment_power_cone v₁ v₂.

  (**
   5. Type indexed products
   *)
  Section SelfEnrichmentProduct.
    Context {J : UU}
            {D : J → V}
            (prod : Product J V D).

    Definition self_enrichment_prod_cone
      : enriched_prod_cone (self_enrichment V) D.
    Proof.
      use make_enriched_prod_cone.
      - exact prod.
      - exact (λ j,
               enriched_from_arr
                 (self_enrichment V)
                 (ProductPr _ _ prod j)).
    Defined.

    Definition self_enrichment_is_product
      : is_prod_enriched
          (self_enrichment V)
          D
          self_enrichment_prod_cone.
    Proof.
      use make_is_prod_enriched.
      - exact (λ v₁ v₂ f,
               internal_lam
                 (ProductArrow
                    _ _
                    prod
                    (λ j, f j #⊗ identity _ · internal_eval _ _))).
      - abstract
          (intros v₁ v₂ f j ; cbn ;
           rewrite self_enrichment_postcomp ;
           use internal_funext ;
           intros a h ;
           rewrite tensor_comp_r_id_r ;
           rewrite !assoc' ;
           rewrite internal_beta ;
           rewrite tensor_split ;
           rewrite !assoc' ;
           rewrite !(maponpaths (λ z, _ · z) (assoc _ _ _)) ;
           rewrite internal_beta ;
           rewrite internal_to_from_arr ;
           rewrite ProductPrCommutes ;
           rewrite !assoc ;
           rewrite <- tensor_split ;
           apply idpath).
      - abstract
          (intros v₁ v₂ φ₁ φ₂ p ; cbn in * ;
           use internal_funext ;
           intros a h ;
           use (ProductArrow_eq _ _ _ prod) ;
           intro j ;
           pose (q := maponpaths (λ z, z #⊗ identity _ · internal_eval _ _) (p j)) ;
           cbn in q ;
           rewrite !self_enrichment_postcomp in q ;
           rewrite !tensor_comp_id_r in q ;
           rewrite !assoc' in q ;
           rewrite !internal_beta in q ;
           rewrite !internal_to_from_arr in q ;
           rewrite (tensor_split φ₁ h) ;
           rewrite (tensor_split φ₂ h) ;
           rewrite !assoc' ;
           rewrite q ;
           apply idpath).
    Defined.
  End SelfEnrichmentProduct.

  Definition self_enrichment_prod
             (J : UU)
             (PV : Products J V)
    : enrichment_prod (self_enrichment V) J
    := λ D,
       self_enrichment_prod_cone (PV D)
       ,,
       self_enrichment_is_product (PV D).
End SelfEnrichmentLimits.
