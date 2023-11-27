(**************************************************************************************************

  The category of algebraic theory presheaves

  Defines the category of presheaves for an algebraic theory. First, the category of dependent pairs
  of theories and presheaves is formalized as a stack of displayed categories, then the category of
  presheaves is a fiber of a (repeated) sigma category of this. It is shown that presheaves are
  fibered over algebraic theories. The displayed category structure is then leveraged to show that
  the category is univalent and has all limits. To facilitate computation, concrete definitions of
  the terminal object, binary product and product are given.

  Contents
  1. The dependent product category of theories and presheaves [presheaf_full_cat]
  2. The category of presheaves [presheaf_cat]
  3. Univalence [is_univalent_presheaf_cat]
  4. Fibration [presheaf_fibration]
  5. Limits [limits_presheaf_cat]
  6. Terminal object [terminal_presheaf_cat]
  7. Binary products [bin_products_presheaf_cat]
  8. Products [products_presheaf_cat]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Univalence.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Reindexing.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Limits.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.FiniteSetSkeleton.
Require Import UniMath.AlgebraicTheories.PresheafMorphisms.
Require Import UniMath.AlgebraicTheories.Presheaves.

Local Open Scope algebraic_theories.
Local Open Scope cat.
Local Open Scope mor_disp.

(** * 1. The dependent product category of theories and presheaves *)

Definition presheaf_data_disp_cat
  : disp_cat (cartesian algebraic_theory_cat base_functor_category).
Proof.
  use disp_struct.
  - intro X.
    pose (T := pr1 X : algebraic_theory).
    pose (A := pr2 X : finite_set_skeleton_category ⟶ HSET).
    exact (∏ m n, (A m : hSet) → (stn m → (T n : hSet)) → (A n : hSet)).
  - intros X X' action action' Y.
    pose (A := pr2 X : finite_set_skeleton_category ⟶ HSET).
    pose (A' := pr2 X' : finite_set_skeleton_category ⟶ HSET).
    pose (F := pr1 Y : algebraic_theory_morphism _ _).
    pose (G := pr2 Y : nat_trans A A').
    exact (∏ m n a f, G n (action m n a f) = action' m n (G m a) (λ i, F n (f i))).
  - abstract (
      intros;
      do 4 (apply impred_isaprop; intro);
      apply setproperty
    ).
  - abstract (
      intros X action n m f a;
      refine (maponpaths (λ x, _ (x _) _ _) (transportf_const _ _) @ !_);
      exact (maponpaths (λ x, _ (_ (x _) _ _) _) (transportf_const _ _))
    ).
  - abstract (
      intros X X' X'' action action' action'' y y' Gcommutes G'commutes m n a f;
      refine (maponpaths (λ x, _ (x _) _ _) (transportf_const _ _) @ !_);
      refine (maponpaths (λ x, _ (_ (x _) _ _) _) (transportf_const _ _) @ !_);
      exact (maponpaths _ (Gcommutes _ _ _ _) @ (G'commutes _ _ _ _))
    ).
Defined.

Definition presheaf_data_cat
  : category
  := total_category presheaf_data_disp_cat.

Definition presheaf_full_disp_cat
  : disp_cat presheaf_data_cat
  := disp_full_sub presheaf_data_cat
    (λ X, is_presheaf (make_presheaf_data (pr21 X) (pr2 X))).

Definition presheaf_full_cat
  : category
  := total_category presheaf_full_disp_cat.

(** * 2. The category of presheaves *)

Definition presheaf_disp_cat
  : disp_cat algebraic_theory_cat
  := sigma_disp_cat (sigma_disp_cat presheaf_full_disp_cat).

Lemma displayed_presheaf_morphism_eq
  {T T' : algebraic_theory}
  {F : algebraic_theory_morphism T T'}
  {P : presheaf T}
  {P' : presheaf T'}
  (G G' : (P : presheaf_disp_cat _) -->[F] P')
  (H : pr1 G = pr1 G')
  : G = G'.
Proof.
  refine (subtypePath _ H).
  intro.
  use (isapropdirprod _ _ _ isapropunit).
  do 4 (apply impred_isaprop; intro).
  apply setproperty.
Qed.

Definition presheaf_cat
  (T : algebraic_theory)
  : category
  := fiber_category presheaf_disp_cat T.

Section Test.
  Goal ∏ T, ob (presheaf_cat T) = presheaf T.
    exact (λ _, idpath _).
  Qed.
  Goal ∏ (T : algebraic_theory) (P P' : presheaf T),
    presheaf_cat T ⟦P, P'⟧ = presheaf_morphism P P'.
    intros.
    apply idpath.
  Qed.
End Test.

Lemma presheaf_mor_comp
  {T : algebraic_theory}
  {P P' P'' : presheaf_cat T}
  (F : presheaf_cat T⟦P, P'⟧)
  (F' : presheaf_cat T⟦P', P''⟧)
  (n : nat)
  : pr11 (F · F') n = (pr11 F n) · (pr11 F' n).
Proof.
  refine (maponpaths (λ z, pr1 z _) (pr1_transportf (B := λ _, _ ⟹ _) _ _) @ _).
  refine (maponpaths (λ z, pr1 (z _) _) (transportf_const _ _) @ _).
  exact (maponpaths (λ z, pr1 (z _) _) (transportf_const _ _)).
Qed.

Lemma presheaf_identity_on_element
  {T : algebraic_theory}
  {n : nat}
  (P : presheaf T)
  (x : (P n : hSet))
  : pr11 (identity (P : presheaf_cat T)) n x = x.
Proof.
  exact (maponpaths (λ x, pr1 (x _) _ _) (transportb_const _ (P ⟹ P))).
Qed.

(** * 3. Univalence *)

Lemma is_univalent_disp_presheaf_data_disp_cat
  : is_univalent_disp presheaf_data_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  intros TA action action'.
  use isweq_iso.
  - intro F.
    do 4 (apply funextsec; intro).
    refine (maponpaths (λ x, _ (x _) _ _) (!transportf_const _ _) @ pr1 F _ _ _ _ @ _).
    exact (maponpaths (λ x, _ (_ (x _) _ _) _) (transportf_const _ _)).
  - intro.
    do 4 (apply impred_isaset; intro).
    apply setproperty.
  - intro.
    apply z_iso_eq.
    do 4 (apply impred_isaprop; intro).
    apply setproperty.
Qed.

Lemma is_univalent_presheaf_data_cat
  : is_univalent presheaf_data_cat.
Proof.
  apply is_univalent_total_category.
  - rewrite cartesian_is_binproduct.
    use is_univalent_category_binproduct.
    + exact is_univalent_algebraic_theory_cat.
    + exact (is_univalent_functor_category _ _ is_univalent_HSET).
  - exact is_univalent_disp_presheaf_data_disp_cat.
Qed.

Lemma is_univalent_disp_presheaf_full_disp_cat
  : is_univalent_disp presheaf_full_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  exact (λ _, isaprop_is_presheaf _).
Qed.

Lemma is_univalent_presheaf_full_cat
  : is_univalent presheaf_full_cat.
Proof.
  apply is_univalent_total_category.
  - exact is_univalent_presheaf_data_cat.
  - exact is_univalent_disp_presheaf_full_disp_cat.
Qed.

Lemma is_univalent_disp_presheaf_disp_cat
  : is_univalent_disp presheaf_disp_cat.
Proof.
  repeat use is_univalent_sigma_disp.
  - apply is_univalent_reindex_disp_cat.
    apply is_univalent_disp_disp_over_unit.
    apply is_univalent_functor_category.
    exact is_univalent_HSET.
  - exact is_univalent_disp_presheaf_data_disp_cat.
  - exact is_univalent_disp_presheaf_full_disp_cat.
Qed.

Lemma is_univalent_presheaf_cat
  (T : algebraic_theory)
  : is_univalent (presheaf_cat T).
Proof.
  refine (is_univalent_fiber_cat _ _ _).
  exact is_univalent_disp_presheaf_disp_cat.
Qed.

(** * 4. Fibration *)

Section fibration.

  Section lift.

    Context {c c' : algebraic_theory}.
    Context (f : algebraic_theory_morphism c' c).
    Context (d : presheaf c).

    Definition lifted_presheaf_data
      : presheaf_data c'.
    Proof.
      use make_presheaf_data.
      - exact (pr1 d).
      - intros m n s t.
        exact (action (P := d) s (λ i, f _ (t i))).
    Defined.

    Definition lifted_is_presheaf
      : is_presheaf lifted_presheaf_data.
    Proof.
      use make_is_presheaf.
      - do 6 intro.
        refine (presheaf_is_assoc d _ _ _ _ _ _ @ _).
        apply (maponpaths (pr12 d l n a)).
        apply funextfun.
        intro.
        symmetry.
        apply algebraic_theory_morphism_preserves_composition.
      - do 2 intro.
        refine (_ @ presheaf_identity_projections d _ _).
        apply (maponpaths (pr12 d n n a)).
        apply funextfun.
        intro.
        apply algebraic_theory_morphism_preserves_projections.
      - do 6 intro.
        apply presheaf_action_is_natural.
    Qed.

    Definition lifted_presheaf
      : presheaf c'
      := make_presheaf _ lifted_is_presheaf.

    Definition lifted_presheaf_morphism
      : (lifted_presheaf : presheaf_disp_cat c') -->[f] d.
    Proof.
      use tpair.
      - apply nat_trans_id.
      - refine (_ ,, tt).
        now do 4 intro.
    Defined.

    Section cartesian.

      Context {c'': algebraic_theory}.
      Context {g: algebraic_theory_morphism c'' c'}.
      Context {d'': presheaf c''}.
      Context (hh: (d'' : presheaf_disp_cat c'') -->[(g : algebraic_theory_cat ⟦ _, _ ⟧) · f] d).

      Definition induced_morphism
        : (d'' : presheaf_disp_cat c'') -->[ g] lifted_presheaf.
      Proof.
        use tpair.
        - exact (pr1 hh).
        - refine (_ ,, tt).
          do 4 intro.
          exact (pr12 hh _ _ _ _).
      Defined.

      Lemma induced_morphism_commutes
        : (induced_morphism ;; lifted_presheaf_morphism) = hh.
      Proof.
        apply displayed_presheaf_morphism_eq.
        refine (comp_disp_cartesian _ _ _ _ @ _).
        apply (nat_trans_eq (homset_property HSET)).
        intro.
        apply funextfun.
        now intro.
      Qed.

      Lemma induced_morphism_unique
        (t : ∑ induced_morphism', (induced_morphism' ;; lifted_presheaf_morphism) = hh)
        : t = induced_morphism ,, induced_morphism_commutes.
      Proof.
        apply subtypePairEquality.
        {
          intro.
          apply homsets_disp.
        }
        apply displayed_presheaf_morphism_eq.
        refine (
          nat_trans_eq (homset_property HSET) _ _ _ _ _ @
          !comp_disp_cartesian _ _ (pr11 t) _ @
          maponpaths _ (pr2 t)
        ).
        intro.
        apply funextfun.
        now intro.
      Qed.

    End cartesian.

    Definition lifted_presheaf_morphism_is_cartesian
      : is_cartesian lifted_presheaf_morphism.
    Proof.
      intros c'' g d'' hh.
      use ((_ ,, _) ,, _).
      - exact (induced_morphism hh).
      - exact (induced_morphism_commutes hh).
      - exact (induced_morphism_unique hh).
    Defined.

  End lift.

  Definition presheaf_cleaving
    : cleaving presheaf_disp_cat
    := λ c c' f d,
      (lifted_presheaf f d) ,,
      (lifted_presheaf_morphism f d) ,,
      (lifted_presheaf_morphism_is_cartesian f d).

  Definition presheaf_fibration
    : fibration algebraic_theory_cat
    := presheaf_disp_cat ,, presheaf_cleaving.

End fibration.

(** * 5. Limits *)

Definition creates_limits_presheaf_base_disp
  : creates_limits (disp_cartesian algebraic_theory_cat base_functor_category).
Proof.
  intros J d L.
  use creates_limits_disp_cartesian.
  apply limits_base_functor_category.
Defined.

Definition limits_presheaf_base
  : Lims (cartesian algebraic_theory_cat base_functor_category).
Proof.
  intros J d.
  use total_limit.
  - apply limits_algebraic_theory_cat.
  - apply creates_limits_presheaf_base_disp.
Defined.

Section DataLimits.
  Context (D := presheaf_data_disp_cat).
  Context {J : graph}.
  Context (d : diagram J (total_category D)).
  Context (L := limits_presheaf_base J (mapdiagram (pr1_category _) d)).

  Definition tip_presheaf_data_disp_cat
    : D (lim L).
  Proof.
    intros m n a f.
    use tpair.
    - intro u.
      exact (pr2 (dob d u) m n (pr1 a u) (λ i, pr1 (f i) u)).
    - abstract (
        intros u v e;
        refine (pr2 (dmor d e) _ _ _ _ @ _);
        refine (maponpaths (λ x, _ x _) _ @ maponpaths _ _);
        [ exact (pr2 a u v e)
        | apply funextfun;
          intro;
          exact (pr2 (f _) u v e) ]
      ).
  Defined.

  Lemma cone_presheaf_data_disp_cat
    (j : vertex J)
    : tip_presheaf_data_disp_cat -->[limOut L j] pr2 (dob d j).
  Proof.
    easy.
  Qed.

  Lemma uniqueness_presheaf_data_disp_cat
    (d' : D (lim L))
    (cone_out : ∏ j, d' -->[limOut L j] (pr2 (dob d j)))
    : d' = tip_presheaf_data_disp_cat.
  Proof.
    do 4 (apply funextsec; intro).
    apply subtypePairEquality.
    {
      intro.
      repeat (apply impred_isaprop; intro).
      apply setproperty.
    }
    apply funextsec.
    intro.
    apply (cone_out _ _ _ _ _).
  Qed.

  Lemma is_limit_presheaf_data_disp_cat
    (d' : total_category D)
    (cone_out : ∏ u, d' --> (dob d u))
    (is_cone : ∏ u v e, cone_out u · (dmor d e) = cone_out v)
    : pr2 d' -->[limArrow L _ (make_cone
        (d := (mapdiagram (pr1_category D) d)) _
        (λ u v e, (maponpaths pr1 (is_cone u v e))))
      ] tip_presheaf_data_disp_cat.
  Proof.
    intros m n f g.
    apply subtypePairEquality.
    {
      intro.
      repeat (apply impred_isaprop; intro).
      exact (setproperty _ _ _).
    }
    apply funextsec.
    intro i.
    exact (pr2 (cone_out i) m n f g).
  Qed.

End DataLimits.

Definition creates_limits_presheaf_data_disp_cat
  {J : graph}
  (d : diagram J (total_category presheaf_data_disp_cat))
  : creates_limit d (limits_presheaf_base _ _)
  := creates_limit_disp_struct _
    (tip_presheaf_data_disp_cat _)
    (cone_presheaf_data_disp_cat _)
    (is_limit_presheaf_data_disp_cat _).

Definition creates_limits_unique_presheaf_data_disp_cat
  {J : graph}
  (d : diagram J (total_category presheaf_data_disp_cat))
  : creates_limit_unique d (limits_presheaf_base _ _)
  := creates_limit_unique_disp_struct
    (creates_limits_presheaf_data_disp_cat _)
    (uniqueness_presheaf_data_disp_cat _).

Definition limits_presheaf_data_cat
  : Lims presheaf_data_cat
  := λ _ _, total_limit _ (creates_limits_presheaf_data_disp_cat _).

Definition creates_limits_presheaf_full_disp_cat
  {J : graph}
  (d : diagram J (total_category presheaf_full_disp_cat))
  : creates_limit d (limits_presheaf_data_cat _ _).
Proof.
  apply creates_limit_disp_full_sub.
  - intro.
    apply isaprop_is_presheaf.
  - abstract (
      use make_is_presheaf;
        repeat intro;
        (use total2_paths_f;
        [ apply funextsec;
          intro
        | do 3 (apply impred_isaprop; intro);
          apply setproperty ]);
      [ apply (pr1 (pr2 (dob d _)))
      | apply (pr12 (pr2 (dob d _)))
      | apply (pr22 (pr2 (dob d _))) ]
    ).
Defined.

Definition creates_limits_unique_presheaf_full_disp_cat
  {J : graph}
  (d : diagram J (total_category presheaf_full_disp_cat))
  : creates_limit_unique d (limits_presheaf_data_cat _ _)
  := creates_limit_unique_disp_full_sub
    (λ _, isaprop_is_presheaf _)
    _
    (creates_limits_presheaf_full_disp_cat _).

Definition limits_presheaf_full_cat
  : Lims presheaf_full_cat
  := λ _ _, total_limit _ (creates_limits_presheaf_full_disp_cat _).

Definition creates_limits_presheaf_disp_cat
  {J : graph}
  (d : diagram J (total_category presheaf_disp_cat))
  : creates_limit d (limits_algebraic_theory_cat _ _).
Proof.
  repeat use creates_limits_sigma_disp_cat.
  - exact (creates_limits_presheaf_base_disp _ _ _).
  - exact (creates_limits_presheaf_data_disp_cat _).
  - exact (creates_limits_presheaf_full_disp_cat _).
Defined.

Definition limits_presheaf_cat
  (T : algebraic_theory)
  : Lims (presheaf_cat T).
Proof.
  intros J d.
  use fiber_limit.
  - apply limits_algebraic_theory_cat.
  - apply creates_limits_presheaf_disp_cat.
  - apply presheaf_cleaving.
Defined.

(** * 6. Terminal object *)

Section Terminal.

  Context (T : algebraic_theory).

  Definition terminal_presheaf'_data
    : presheaf'_data T.
  Proof.
    use make_presheaf'_data.
    - exact (λ _, unitset).
    - exact (λ _ _ _ _, tt).
  Defined.

  Lemma terminal_is_presheaf'
    : is_presheaf' terminal_presheaf'_data.
  Proof.
    use make_is_presheaf';
      repeat intro.
    - apply idpath.
    - symmetry.
      apply iscontrunit.
  Qed.

  Definition terminal_presheaf
    : presheaf T
    := make_presheaf'
      terminal_presheaf'_data
      terminal_is_presheaf'.

  Section TerminalMorphism.

    Context (P : presheaf T).

    Definition terminal_presheaf_morphism
      : presheaf_morphism P terminal_presheaf.
    Proof.
      use make_presheaf_morphism'.
      - intros.
        exact tt.
      - abstract trivial.
    Defined.

    Lemma terminal_presheaf_morphism_unique
      (f : presheaf_morphism P terminal_presheaf)
      : f = terminal_presheaf_morphism.
    Proof.
      apply (presheaf_morphism_eq).
      intro.
      apply funextfun.
      intro.
      apply iscontrunit.
    Qed.

  End TerminalMorphism.

Definition terminal_presheaf_cat
  : Terminal (presheaf_cat T).
Proof.
  use tpair.
  - exact (make_presheaf' terminal_presheaf'_data terminal_is_presheaf').
  - intro P.
    use make_iscontr.
    + exact (terminal_presheaf_morphism P).
    + exact (terminal_presheaf_morphism_unique P).
Defined.

End Terminal.

(** * 7. Binary products *)

Section BinProduct.

  Context (T : algebraic_theory).
  Context (P P': presheaf T).

  Definition binproduct_presheaf'_data
    : presheaf'_data T.
  Proof.
    use make_presheaf'_data.
    - exact (λ n, dirprod_hSet (P n) (P' n)).
    - exact (λ m n t f, (action (pr1 t) f ,, action (pr2 t) f)).
  Defined.

  Lemma binproduct_is_presheaf'
    : is_presheaf' binproduct_presheaf'_data.
  Proof.
    split.
    - do 6 intro.
      apply pathsdirprod;
      apply presheaf_is_assoc.
    - do 2 intro.
      apply pathsdirprod;
      apply presheaf_identity_projections.
  Qed.

  Definition binproduct_presheaf
    : presheaf T
    := make_presheaf'
      binproduct_presheaf'_data
      binproduct_is_presheaf'.

  Definition binproduct_presheaf_pr1
    : presheaf_morphism binproduct_presheaf P.
  Proof.
    use make_presheaf_morphism'.
    - intro n.
      exact pr1.
    - abstract trivial.
  Defined.

  Definition binproduct_presheaf_pr2
    : presheaf_morphism binproduct_presheaf P'.
  Proof.
    use make_presheaf_morphism'.
    - intro n.
      exact pr2.
    - abstract trivial.
  Defined.

  Section UniversalProperty.

    Context (Q : presheaf T).
    Context (F: presheaf_morphism Q P).
    Context (F' : presheaf_morphism Q P').

    Definition binproduct_presheaf_induced_morphism'_data
      (n : nat)
      (q : (Q n : hSet))
      : (binproduct_presheaf n : hSet).
    Proof.
      exact (F _ q ,, F' _ q).
    Defined.

    Lemma binproduct_presheaf_induced_is_morphism'
      (m n : nat)
      (a : Q m : hSet)
      (f : (⟦ m ⟧)%stn → T n : hSet)
      : binproduct_presheaf_induced_morphism'_data n (action a f) =
        action (binproduct_presheaf_induced_morphism'_data m a) f.
    Proof.
      apply pathsdirprod;
        apply presheaf_morphism_commutes_with_action.
    Qed.

    Definition binproduct_presheaf_induced_morphism
      : presheaf_morphism Q binproduct_presheaf
      := make_presheaf_morphism'
        binproduct_presheaf_induced_morphism'_data
        binproduct_presheaf_induced_is_morphism'.

    Lemma binproduct_presheaf_induced_morphism_commutes
      : (binproduct_presheaf_induced_morphism : presheaf_cat T⟦Q, binproduct_presheaf⟧) ·
          binproduct_presheaf_pr1 = F ×
        (binproduct_presheaf_induced_morphism : presheaf_cat T⟦Q, binproduct_presheaf⟧) ·
          binproduct_presheaf_pr2 = F'.
    Proof.
      split;
      apply displayed_presheaf_morphism_eq;
      apply (nat_trans_eq (homset_property HSET));
      intro n;
      exact (presheaf_mor_comp _ _ _).
    Qed.

    Lemma binproduct_presheaf_induced_morphism_unique
      (t : ∑ k : presheaf_cat T ⟦ Q, binproduct_presheaf ⟧,
        k · binproduct_presheaf_pr1 = F × k · binproduct_presheaf_pr2 = F')
      : t = binproduct_presheaf_induced_morphism ,, binproduct_presheaf_induced_morphism_commutes.
    Proof.
      use subtypePairEquality.
      {
        intro.
        apply isapropdirprod;
          apply homset_property.
      }
      apply displayed_presheaf_morphism_eq.
      apply (nat_trans_eq (homset_property HSET)).
      intro n.
      apply funextfun.
      intro s.
      apply pathsdirprod.
      - refine (!_ @ maponpaths (λ x, pr11 x _ _) (pr12 t)).
        exact (maponpaths (λ x, x _) (presheaf_mor_comp _ _ _)).
      - refine (!_ @ maponpaths (λ x, pr11 x _ _) (pr22 t)).
        exact (maponpaths (λ x, x _) (presheaf_mor_comp _ _ _)).
    Qed.

  End UniversalProperty.

  Definition bin_product_presheaf_cat
    : BinProduct (presheaf_cat T) P P'.
  Proof.
    use make_BinProduct.
    - exact binproduct_presheaf.
    - exact binproduct_presheaf_pr1.
    - exact binproduct_presheaf_pr2.
    - use make_isBinProduct.
      intros Q F F'.
      use make_iscontr.
      + use tpair.
        * exact (binproduct_presheaf_induced_morphism Q F F').
        * exact (binproduct_presheaf_induced_morphism_commutes Q F F').
      + exact (binproduct_presheaf_induced_morphism_unique Q F F').
  Defined.

End BinProduct.

Definition bin_products_presheaf_cat
  (T : algebraic_theory)
  : BinProducts (presheaf_cat T)
  := bin_product_presheaf_cat T.

(** * 8. Products *)

Section Product.

  Context (T : algebraic_theory).
  Context (I : UU).
  Context (P : I → presheaf T).

  Definition product_presheaf'_data
    : presheaf'_data T.
  Proof.
    use make_presheaf'_data.
    - intro n.
      exact (forall_hSet (λ i, P i n)).
    - exact (λ m n t f i, action (t i) f).
  Defined.

  Lemma product_is_presheaf'
    : is_presheaf' product_presheaf'_data.
  Proof.
    split.
    - do 6 intro.
      apply funextsec.
      intro.
      apply presheaf_is_assoc.
    - do 2 intro.
      apply funextsec.
      intro.
      apply presheaf_identity_projections.
  Qed.

  Definition product_presheaf
    : presheaf T
    := make_presheaf'
      product_presheaf'_data
      product_is_presheaf'.

  Definition product_presheaf_pr
    (i : I)
    : presheaf_morphism product_presheaf (P i).
  Proof.
    use (make_presheaf_morphism' (P := make_presheaf' _ _)).
    - exact (λ n t, t i).
    - abstract trivial.
  Defined.

  Section UniversalProperty.

    Context (Q : presheaf T).
    Context (F : ∏ i, presheaf_morphism Q (P i)).

    Definition product_presheaf_induced_morphism'_data
      (n : nat)
      (q : (Q n : hSet))
      : (product_presheaf n : hSet).
    Proof.
      intro i.
      exact (F i n q).
    Defined.

    Lemma product_presheaf_induced_is_morphism'
      (m n : nat)
      (a : Q m : hSet)
      (f : (⟦ m ⟧)%stn → T n : hSet)
      : product_presheaf_induced_morphism'_data n (action a f) =
        action (product_presheaf_induced_morphism'_data m a) f.
    Proof.
      intros.
      apply funextsec.
      intro.
      apply presheaf_morphism_commutes_with_action.
    Qed.

    Definition product_presheaf_induced_morphism
      : presheaf_morphism Q product_presheaf
      := make_presheaf_morphism'
        product_presheaf_induced_morphism'_data
        product_presheaf_induced_is_morphism'.

    Lemma product_presheaf_induced_morphism_commutes
      (i : I)
      : (product_presheaf_induced_morphism : presheaf_cat T⟦Q, product_presheaf⟧) ·
          product_presheaf_pr i = F i.
    Proof.
      apply displayed_presheaf_morphism_eq.
      apply (nat_trans_eq (homset_property HSET)).
      intro n.
      apply presheaf_mor_comp.
    Qed.

    Lemma product_presheaf_induced_morphism_unique
      (t : ∑ k : presheaf_cat T ⟦ Q, product_presheaf ⟧,
        ∏ i, k · product_presheaf_pr i = F i)
      : t = product_presheaf_induced_morphism ,, product_presheaf_induced_morphism_commutes.
    Proof.
      use subtypePairEquality.
      {
        intro.
        apply impred_isaprop.
        intro.
        apply homset_property.
      }
      apply displayed_presheaf_morphism_eq.
      apply (nat_trans_eq (homset_property HSET)).
      intro n.
      apply funextfun.
      intro s.
      apply funextsec.
      intro i.
      refine (!_ @ maponpaths (λ x, pr11 x _ _) (pr2 t i)).
      exact (maponpaths (λ x, x _) (presheaf_mor_comp _ _ _)).
    Qed.

  End UniversalProperty.

  Definition product_presheaf_cat
    : Product I (presheaf_cat T) P.
  Proof.
    use make_Product.
    - exact product_presheaf.
    - exact product_presheaf_pr.
    - use (make_isProduct _ _ (homset_property _)).
      intros Q F.
      use make_iscontr.
      + use tpair.
        * exact (product_presheaf_induced_morphism Q F).
        * exact (product_presheaf_induced_morphism_commutes Q F).
      + exact (product_presheaf_induced_morphism_unique Q F).
  Defined.

End Product.

Definition products_presheaf_cat
  (T : algebraic_theory)
  (I : UU)
  : Products I (presheaf_cat T)
  := product_presheaf_cat T I.
