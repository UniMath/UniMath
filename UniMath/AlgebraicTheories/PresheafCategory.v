(**************************************************************************************************

  Properties of the category of algebraic theory presheaves

  Shows that presheaves are fibered over algebraic theories. The displayed category structure is
  then leveraged to show that the category is univalent and has all limits. To facilitate
  computation, concrete definitions of the terminal object, binary product and product are given.

  Contents
  1. Univalence [is_univalent_presheaf_cat]
  2. Fibration [presheaf_fibration]
  3. Limits [limits_presheaf_cat]
  4. Terminal object [terminal_presheaf_cat]
  5. Binary products [bin_products_presheaf_cat]
  6. Products [products_presheaf_cat]

 **************************************************************************************************)
Require Export UniMath.AlgebraicTheories.PresheafCategoryCore.

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Limits.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.Combinatorics.StandardFiniteSets.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.IndexedSetCategory.
Require Import UniMath.AlgebraicTheories.PresheafMorphisms.
Require Import UniMath.AlgebraicTheories.Presheaves.

Local Open Scope cat.
Local Open Scope mor_disp.

(** * 1. Univalence *)

Lemma is_univalent_disp_presheaf_data_disp_cat
  : is_univalent_disp presheaf_data_disp_cat.
Proof.
  apply is_univalent_disp_iff_fibers_are_univalent.
  intros TA op op'.
  use isweq_iso.
  - intro F.
    do 4 (apply funextsec; intro).
    apply (pr1 F _).
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
  - apply is_univalent_cartesian'.
    + exact is_univalent_algebraic_theory_cat.
    + apply is_univalent_indexed_set_cat.
  - exact is_univalent_disp_presheaf_data_disp_cat.
Qed.

Lemma is_univalent_disp_presheaf_full_disp_cat
  : is_univalent_disp presheaf_full_disp_cat.
Proof.
  apply disp_full_sub_univalent.
  intro.
  apply isaprop_full_is_presheaf.
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
  - apply is_univalent_disp_cartesian'.
    apply is_univalent_indexed_set_cat.
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

(** * 2. Fibration *)

Section fibration.

  Section lift.

    Context {T T' : algebraic_theory}.
    Context (F : algebraic_theory_morphism T' T).
    Context (P : presheaf T).

    Definition lifted_presheaf_data
      : presheaf_data T'.
    Proof.
      use make_presheaf_data.
      - exact (pr1 P).
      - intros m n s t.
        exact (op (P := P) s (λ i, F _ (t i))).
    Defined.

    Definition lifted_is_presheaf
      : is_presheaf lifted_presheaf_data.
    Proof.
      use make_is_presheaf.
      - do 6 intro.
        refine (op_op _ a _ _ @ _).
        apply (maponpaths (op (P := P) a)).
        apply funextfun.
        intro.
        symmetry.
        apply mor_subst.
      - do 2 intro.
        refine (_ @ op_var P _).
        apply (maponpaths (op (P := P) f)).
        apply funextfun.
        intro.
        apply mor_var.
    Qed.

    Definition lifted_presheaf
      : presheaf T'
      := make_presheaf _ lifted_is_presheaf.

    Definition lifted_presheaf_morphism
      : (lifted_presheaf : presheaf_disp_cat T') -->[F] P.
    Proof.
      use tpair.
      - exact (λ _, idfun _).
      - abstract exact ((λ _ _ _ _, idpath _) ,, tt).
    Defined.

    Section cartesian.

      Context {T'': algebraic_theory}.
      Context {F': algebraic_theory_morphism T'' T'}.
      Context {P'': presheaf T''}.
      Context (G: (P'' : presheaf_disp_cat T'') -->[(F' : algebraic_theory_cat ⟦ _, _ ⟧) · F] P).

      Definition induced_morphism
        : (P'' : presheaf_disp_cat T'') -->[F'] lifted_presheaf.
      Proof.
        use tpair.
        - exact (pr1 G).
        - abstract exact ((λ _ _ _ _, pr12 G _ _ _ _) ,, tt).
      Defined.

      Lemma induced_morphism_commutes
        : (induced_morphism ;; lifted_presheaf_morphism) = G.
      Proof.
        now apply displayed_presheaf_morphism_eq.
      Qed.

      Lemma induced_morphism_unique
        (induced_morphism' : (P'' : presheaf_disp_cat T'') -->[F'] lifted_presheaf)
        (H : (induced_morphism' ;; lifted_presheaf_morphism) = G)
        : induced_morphism' = induced_morphism.
      Proof.
        apply displayed_presheaf_morphism_eq.
        exact (maponpaths _ H).
      Qed.

    End cartesian.

    Definition lifted_presheaf_morphism_is_cartesian
      : is_cartesian lifted_presheaf_morphism.
    Proof.
      intros T'' F' P'' G.
      use unique_exists.
      - exact (induced_morphism G).
      - exact (induced_morphism_commutes G).
      - abstract (intro; apply homsets_disp).
      - exact (induced_morphism_unique G).
    Defined.

  End lift.

  Definition presheaf_cleaving
    : cleaving presheaf_disp_cat
    := λ T T' F P,
      (lifted_presheaf F P) ,,
      (lifted_presheaf_morphism F P) ,,
      (lifted_presheaf_morphism_is_cartesian F P).

  Definition presheaf_fibration
    : fibration algebraic_theory_cat
    := presheaf_disp_cat ,, presheaf_cleaving.

End fibration.

(** * 3. Limits *)

Definition creates_limits_presheaf_base_disp
  : creates_limits (disp_cartesian' algebraic_theory_cat (indexed_set_cat nat)).
Proof.
  intros J d L.
  use creates_limits_disp_cartesian'.
  apply limits_indexed_set_cat.
Defined.

Definition limits_presheaf_base
  : Lims (cartesian' algebraic_theory_cat (indexed_set_cat nat)).
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
    apply isaprop_full_is_presheaf.
  - abstract (
      split;
        repeat intro;
        (use total2_paths_f;
        [ apply funextsec;
          intro u
        | do 3 (apply impred_isaprop; intro);
          apply setproperty ]);
      [ apply (pr1 (pr2 (dob d _)))
      | apply (pr2 (pr2 (dob d _))) ]
    ).
Defined.

Definition creates_limits_unique_presheaf_full_disp_cat
  {J : graph}
  (d : diagram J (total_category presheaf_full_disp_cat))
  : creates_limit_unique d (limits_presheaf_data_cat _ _)
  := creates_limit_unique_disp_full_sub
    (λ _, isaprop_full_is_presheaf _)
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

(** * 4. Terminal object *)

Section Terminal.

  Context (T : algebraic_theory).

  Definition terminal_presheaf_data
    : presheaf_data T.
  Proof.
    use make_presheaf_data.
    - exact (λ _, unitset).
    - exact (λ _ _ _ _, tt).
  Defined.

  Lemma terminal_is_presheaf
    : is_presheaf terminal_presheaf_data.
  Proof.
    use make_is_presheaf;
      repeat intro.
    - apply idpath.
    - refine (!pr2 iscontrunit _).
  Qed.

  Definition terminal_presheaf
    : presheaf T
    := make_presheaf
      terminal_presheaf_data
      terminal_is_presheaf.

  Section TerminalMorphism.

    Context (P : presheaf T).

    Definition terminal_presheaf_morphism
      : presheaf_morphism P terminal_presheaf.
    Proof.
      use make_presheaf_morphism.
      - exact (λ _ _, tt).
      - abstract easy.
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
  - exact (make_presheaf terminal_presheaf_data terminal_is_presheaf).
  - intro P.
    use make_iscontr.
    + exact (terminal_presheaf_morphism P).
    + exact (terminal_presheaf_morphism_unique P).
Defined.

End Terminal.

(** * 5. Binary products *)

Section BinProduct.

  Context (T : algebraic_theory).
  Context (P P': presheaf T).

  Definition binproduct_presheaf_data
    : presheaf_data T.
  Proof.
    use make_presheaf_data.
    - exact (λ n, dirprod_hSet (P n) (P' n)).
    - exact (λ m n t f, (op (pr1 t) f ,, op (pr2 t) f)).
  Defined.

  Lemma binproduct_is_presheaf
    : is_presheaf binproduct_presheaf_data.
  Proof.
    split.
    - do 6 intro.
      apply pathsdirprod;
      apply op_op.
    - do 2 intro.
      apply pathsdirprod;
      apply op_var.
  Qed.

  Definition binproduct_presheaf
    : presheaf T
    := make_presheaf
      binproduct_presheaf_data
      binproduct_is_presheaf.

  Definition binproduct_presheaf_pr1
    : presheaf_morphism binproduct_presheaf P.
  Proof.
    use make_presheaf_morphism.
    - intro n.
      exact pr1.
    - abstract easy.
  Defined.

  Definition binproduct_presheaf_pr2
    : presheaf_morphism binproduct_presheaf P'.
  Proof.
    use make_presheaf_morphism.
    - intro n.
      exact pr2.
    - abstract easy.
  Defined.

  Section UniversalProperty.

    Context (Q : presheaf T).
    Context (F: presheaf_morphism Q P).
    Context (F' : presheaf_morphism Q P').

    Definition binproduct_presheaf_induced_morphism_data
      (n : nat)
      (q : Q n)
      : binproduct_presheaf n.
    Proof.
      exact (F _ q ,, F' _ q).
    Defined.

    Lemma binproduct_presheaf_induced_is_morphism
      (m n : nat)
      (a : Q m)
      (f : stn m → T n)
      : mor_op_ax (identity T) binproduct_presheaf_induced_morphism_data (@op T Q) (@op T binproduct_presheaf) m n a f.
    Proof.
      apply pathsdirprod;
        apply mor_op.
    Qed.

    Definition binproduct_presheaf_induced_morphism
      : presheaf_morphism Q binproduct_presheaf
      := make_presheaf_morphism
        binproduct_presheaf_induced_morphism_data
        binproduct_presheaf_induced_is_morphism.

    Lemma binproduct_presheaf_induced_morphism_commutes
      : (binproduct_presheaf_induced_morphism : presheaf_cat T⟦Q, binproduct_presheaf⟧) ·
          binproduct_presheaf_pr1 = F ×
        (binproduct_presheaf_induced_morphism : presheaf_cat T⟦Q, binproduct_presheaf⟧) ·
          binproduct_presheaf_pr2 = F'.
    Proof.
      split;
        apply displayed_presheaf_morphism_eq;
        apply funextsec;
        intro n;
        apply presheaf_mor_comp.
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
      apply funextsec.
      intro n.
      apply funextfun.
      intro s.
      apply pathsdirprod.
      - refine (!_ @ maponpaths (λ x, pr1 x _ _) (pr12 t)).
        exact (maponpaths (λ x, x _) (presheaf_mor_comp _ _ _)).
      - refine (!_ @ maponpaths (λ x, pr1 x _ _) (pr22 t)).
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

(** * 6. Products *)

Section Product.

  Context (T : algebraic_theory).
  Context (I : UU).
  Context (P : I → presheaf T).

  Definition product_presheaf_data
    : presheaf_data T.
  Proof.
    use make_presheaf_data.
    - intro n.
      exact (forall_hSet (λ i, P i n)).
    - exact (λ m n t f i, op (t i) f).
  Defined.

  Lemma product_is_presheaf
    : is_presheaf product_presheaf_data.
  Proof.
    split.
    - do 6 intro.
      apply funextsec.
      intro.
      apply op_op.
    - do 2 intro.
      apply funextsec.
      intro.
      apply op_var.
  Qed.

  Definition product_presheaf
    : presheaf T
    := make_presheaf
      product_presheaf_data
      product_is_presheaf.

  Definition product_presheaf_pr
    (i : I)
    : presheaf_morphism product_presheaf (P i).
  Proof.
    use (make_presheaf_morphism (P := make_presheaf _ _)).
    - exact (λ n t, t i).
    - abstract easy.
  Defined.

  Section UniversalProperty.

    Context (Q : presheaf T).
    Context (F : ∏ i, presheaf_morphism Q (P i)).

    Definition product_presheaf_induced_morphism_data
      (n : nat)
      (q : Q n)
      : product_presheaf n.
    Proof.
      intro i.
      exact (F i n q).
    Defined.

    Lemma product_presheaf_induced_is_morphism
      (m n : nat)
      (a : Q m)
      (f : stn m → T n)
      : mor_op_ax (identity T) product_presheaf_induced_morphism_data (@op T Q) (@op T product_presheaf) m n a f.
    Proof.
      intros.
      apply funextsec.
      intro.
      apply mor_op.
    Qed.

    Definition product_presheaf_induced_morphism
      : presheaf_morphism Q product_presheaf
      := make_presheaf_morphism
        product_presheaf_induced_morphism_data
        product_presheaf_induced_is_morphism.

    Lemma product_presheaf_induced_morphism_commutes
      (i : I)
      : (product_presheaf_induced_morphism : presheaf_cat T⟦Q, product_presheaf⟧) ·
          product_presheaf_pr i = F i.
    Proof.
      apply displayed_presheaf_morphism_eq.
      apply funextsec.
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
      apply funextsec.
      intro n.
      apply funextfun.
      intro s.
      apply funextsec.
      intro i.
      refine (!_ @ maponpaths (λ x, pr1 x _ _) (pr2 t i)).
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
