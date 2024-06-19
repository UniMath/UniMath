 (**************************************************************************************************

  Scott's representation theorem

  A proof of the representation theorem for the λ-calculus, first proven by Dana Scott in 1980.
  It shows that any model for the λ-calculus can be viewed as the set of endomorphisms of some
  (reflexive) object in some category.

  Contents
  1. A proof that the object (theory_presheaf) can be exponentiated [theory_presheaf_exponentiable]
  2. A construction of the lambda endomorphism theory of theory_presheaf [presheaf_lambda_theory]
  3. An isomorphism between the two λ-theories [presheaf_lambda_theory_iso]

 **************************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Cartesian.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Sigma.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.Limits.Products.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Tuples.

Require Import UniMath.AlgebraicTheories.AlgebraicTheories.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryCategory.
Require Import UniMath.AlgebraicTheories.AlgebraicTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.Examples.EndomorphismTheory.
Require Import UniMath.AlgebraicTheories.Examples.Plus1Presheaf.
Require Import UniMath.AlgebraicTheories.LambdaTheories.
Require Import UniMath.AlgebraicTheories.LambdaTheoryCategory.
Require Import UniMath.AlgebraicTheories.LambdaTheoryMorphisms.
Require Import UniMath.AlgebraicTheories.PresheafCategory.
Require Import UniMath.AlgebraicTheories.PresheafMorphisms.
Require Import UniMath.AlgebraicTheories.Presheaves.

Local Open Scope algebraic_theories.
Local Open Scope cat.
Local Open Scope mor_disp.

(** * 1. A proof that the object (theory_presheaf) can be exponentiated *)

Section RepresentationTheorem.

  Context (L : lambda_theory).

  Let pow
    (n : nat)
    : Product (stn n) (presheaf_cat L) (λ _, theory_presheaf L)
    := bin_product_power (presheaf_cat L) (theory_presheaf L) (terminal_presheaf_cat _) (bin_products_presheaf_cat _) n.

  Let PO
    (n : nat)
    : presheaf L
    := ProductObject _ _ (pow n).

  Let pow'
    (n : nat)
    : Product (stn n) (presheaf_cat L) (λ _, theory_presheaf L)
    := products_presheaf_cat L (stn n) (λ _, (theory_presheaf L)).

  Let PO'
    (n : nat)
    : presheaf L
    := ProductObject _ _ (pow' n).

  Let pow_iso
    (n : nat)
    : z_iso (pow n) (pow' n)
    := z_iso_between_Product (pow n) (pow' n).

  Let pow_f
    (n : nat)
    : presheaf_morphism (PO n) (PO' n)
    := morphism_from_z_iso _ _ (pow_iso n).

  Let pow_f_inv
    (n : nat)
    : presheaf_morphism (PO' n) (PO n)
    := inv_from_z_iso (pow_iso n).

  Local Definition BPO
    (P P' : presheaf L)
    : presheaf L
    := BinProductObject _ (bin_products_presheaf_cat _ P P').

  Section Exponentiable.

    Definition presheaf_exponent_morphism_data
      (P : presheaf L)
      (n : nat)
      (t : (BPO (theory_presheaf L) (plus_1_presheaf P) n : hSet))
      : (P n : hSet).
    Proof.
      refine (op (P := P) (pr2 t) _).
      intro i.
      induction (invmap stnweq i) as [i' | i'].
      - exact (var i').
      - exact (pr1 t).
    Defined.

    Lemma presheaf_exponent_is_morphism
      (P : presheaf L)
      (m n : nat)
      (a : (BPO (theory_presheaf L) (plus_1_presheaf P) m : hSet))
      (f : stn m → L n)
      : presheaf_exponent_morphism_data P n (op a f)
      = op (presheaf_exponent_morphism_data P m a) f.
    Proof.
      refine (op_op P (pr2 a) _ _ @ !_).
      refine (op_op P (l := S m) (m := m) _ _ _ @ !_).
      apply (maponpaths (op (pr2 a : (P _ : hSet)))).
      apply funextfun.
      intro i.
      induction (invmap stnweq i) as [i' | i'].
      - refine (subst_subst _ (f i') _ _ @ !_).
        refine (var_subst _ _ _ @ _).
        refine (!subst_var _ _ @ !_).
        apply maponpaths.
        apply funextfun.
        intro j.
        refine (var_subst _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
      - refine (var_subst _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
    Qed.

    Definition presheaf_exponent_morphism
      (P : presheaf L)
      : presheaf_morphism (BPO (theory_presheaf L) (plus_1_presheaf P)) P
      := make_presheaf_morphism _ (presheaf_exponent_is_morphism P).

    Definition presheaf_exponent_induced_morphism_data
      {P P' : presheaf L}
      (F : presheaf_morphism (BPO (theory_presheaf L) P') P)
      (n : nat)
      (t : (P' n : hSet))
      : plus_1_presheaf P n : hSet.
    Proof.
      refine (F (1 + n) _).
      split.
      - exact (var (stnweq (inr tt))).
      - apply (op t).
        intro i.
        exact (var (stnweq (inl i))).
    Defined.

    Lemma presheaf_exponent_induced_is_morphism
      {P P' : presheaf L}
      (F : presheaf_morphism (BPO (theory_presheaf L) P') P)
      (m n : nat)
      (a : P' m : hSet)
      (f : (⟦ m ⟧)%stn → L n : hSet)
      : presheaf_exponent_induced_morphism_data F n (op a f)
      = op (presheaf_exponent_induced_morphism_data F m a) f.
    Proof.
      cbn -[extend_tuple stnweq].
      refine (!_ @ mor_op F _ _).
      refine (maponpaths (F (1 + n)) _).
      apply pathsdirprod.
      - refine (var_subst _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq (inr tt))).
      - refine (op_op P' a _ _ @ !_).
        refine (op_op P' a f _ @ !_).
        apply maponpaths.
        apply funextfun.
        intro i.
        refine (var_subst _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq (inl i))).
    Qed.

    Definition presheaf_exponent_induced_morphism
      {P P' : presheaf L}
      (F : presheaf_morphism (BPO (theory_presheaf L) P') P)
      : presheaf_morphism P' (plus_1_presheaf P)
      := make_presheaf_morphism _ (presheaf_exponent_induced_is_morphism F).

    Lemma presheaf_exponent_induced_morphism_commutes
      {P P' : presheaf L}
      (F : presheaf_morphism (BPO (theory_presheaf L) P') P)
      : F
      = # (constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L))
        (presheaf_exponent_induced_morphism F : presheaf_cat L⟦P', plus_1_presheaf P⟧)
        · presheaf_exponent_morphism P.
    Proof.
      apply (presheaf_morphism_eq F _).
      intro n.
      refine (!(presheaf_mor_comp (P := BPO _ _) _ _ _ @ _)).
      apply funextfun.
      intro t.
      refine (maponpaths
        (λ x, op (P := P) (x t) _)
        (presheaf_mor_comp (P := BPO _ _) (P'' := plus_1_presheaf P) _ _ _)
      @ _).
      refine (!mor_op F _ _ @ _).
      apply maponpaths.
      apply pathsdirprod.
      - refine (var_subst _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq stnweq _) @ _).
        exact (maponpaths
          (λ x, pr1 x n t)
          (id_right (BinProductPr1 _ ((bin_products_presheaf_cat L) _ _)))
        ).
      - refine (op_op P' (pr2 t) _ _ @ _).
        refine (_ @ op_var _ _).
        apply maponpaths.
        apply funextfun.
        intro i.
        refine (var_subst _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
    Qed.

    Lemma presheaf_exponent_induced_morphism_unique
      {P P' : presheaf L}
      (F : presheaf_morphism (BPO (theory_presheaf L) P') P)
      (F' : ∑ (f' : presheaf_morphism P' (plus_1_presheaf P)),
        F
        = # (constprod_functor1 (bin_products_presheaf_cat _) (theory_presheaf L))
        (f' : presheaf_cat L ⟦P', plus_1_presheaf P⟧)
        · presheaf_exponent_morphism P
      )
      : F'
      = presheaf_exponent_induced_morphism F,, presheaf_exponent_induced_morphism_commutes F.
    Proof.
      apply subtypePairEquality.
      {
        intro.
        apply (homset_property (presheaf_cat L)).
      }
      apply (presheaf_morphism_eq (pr1 F') _).
      intro n.
      apply funextfun.
      intro t.
      refine (_ @ maponpaths (λ x, pr1 x _ _) (!pr2 F')).
      refine (!(maponpaths (λ x, x _) (presheaf_mor_comp (P := BPO _ _) _ _ _) @ _)).
      refine (maponpaths
        (λ x, op (x _ : P _ : hSet) _)
        (presheaf_mor_comp _ (pr1 F' : presheaf_cat L ⟦P', plus_1_presheaf P⟧) _)
      @ _).
      refine (maponpaths
        (λ x, (pr12 P) _ _ (x : P _ : hSet) _)
        (mor_op (pr1 F') _ _)
      @ _).
      refine (op_op P (pr1 F' n t) _ _ @ _).
      refine (_ @ op_var _ _).
      apply maponpaths.
      apply funextfun.
      intro i.
      refine (_ @ maponpaths var (homotweqinvweq stnweq i)).
      induction (invmap stnweq i) as [i' | i'].
      - refine (subst_subst L (var _) _ _ @ _).
        refine (var_subst _ _ _ @ _).
        refine (var_subst L (stnweq (inl (dni lastelement i'))) _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
      - refine (var_subst _ _ _ @ _).
        refine (maponpaths _ (homotinvweqweq stnweq _) @ _).
        refine (maponpaths
          (λ x, pr1 x _ _)
          (id_right (BinProductPr1 _ ((bin_products_presheaf_cat _) (theory_presheaf L) P')))
        @ _).
        apply (maponpaths (λ x, (var (stnweq (inr x))))).
        exact (!pr2 iscontrunit i').
    Qed.

    Definition theory_presheaf_exponentiable
      : is_exponentiable (bin_products_presheaf_cat _) (theory_presheaf L).
    Proof.
      use left_adjoint_from_partial.
      - exact plus_1_presheaf.
      - exact presheaf_exponent_morphism.
      - intros P P' F.
        use make_iscontr.
        + use tpair.
          * exact (presheaf_exponent_induced_morphism F).
          * exact (presheaf_exponent_induced_morphism_commutes F).
        + exact (presheaf_exponent_induced_morphism_unique F).
    Defined.

    Lemma invmap_hom_weq_eq
      {m n : nat}
      (G : presheaf_cat L ⟦pow n, pr1 theory_presheaf_exponentiable (theory_presheaf L)⟧)
      (l : ((PO (S n)) m : hSet))
      : pr1 (φ_adj_inv (pr2 theory_presheaf_exponentiable) G) m l
      = pr1 G m (pr2 l) • (extend_tuple var (pr1 l)).
    Proof.
      refine (maponpaths (λ x, x _) (presheaf_mor_comp (P'' := theory_presheaf L) _ _ _) @ _).
      refine (maponpaths (λ x, x • _) _ @ maponpaths (λ x, (pr1 G) m (pr2 l) • x) _).
      - exact (maponpaths (λ x, x _) (presheaf_mor_comp _ G _)).
      - refine (!extend_tuple_eq _ _).
        + intro i.
          exact (!maponpaths _ (homotinvweqweq _ (inl i))).
        + refine (!_ @ !maponpaths _ (homotinvweqweq _ (inr tt))).
          exact (maponpaths
            (λ x, pr1 x _ _)
            (id_right (BinProductPr1 _ (bin_products_presheaf_cat _ (theory_presheaf L) _)))
          ).
    Qed.

    Lemma hom_weq_eq
      {m n : nat}
      (G : presheaf_cat L ⟦pow (S n), theory_presheaf L⟧)
      (l : ((PO n) m : hSet))
      : pr1 (φ_adj (pr2 theory_presheaf_exponentiable) G) m l
      = pr1 G (S m) (var (stnweq (inr tt)) ,, op l (λ i, var (stnweq (inl i)))).
    Proof.
      refine (maponpaths
        (λ x, x _)
        (presheaf_mor_comp (P'' := plus_1_presheaf (theory_presheaf L)) _ _ _)
      @ _).
      refine (maponpaths
        (λ x, x _)
        (presheaf_mor_comp (P := BPO _ _) (P'' := theory_presheaf L) _ G _)
      @ _).
      refine (maponpaths (pr1 G (S m)) _).
      apply pathsdirprod.
      - refine (subst_subst L (var _) _ _ @ _).
        refine (var_subst _ _ _ @ _).
        refine (maponpaths (λ x, _ x • _) (homotinvweqweq stnweq _) @ _).
        refine (var_subst _ _ _ @ _).
        exact (maponpaths (λ x, _ x) (homotinvweqweq stnweq _)).
      - refine (op_op (l := S m) (m := S (S m)) _ _ _ _ @ _).
        refine (op_op (l := m) (m := S m) _ _ _ _ @ _).
        apply maponpaths.
        apply funextfun.
        intro i.
        refine (var_subst _ _ _ @ _).
        refine (maponpaths (λ x, _ x • _) (homotinvweqweq stnweq _) @ _).
        refine (maponpaths (λ x, x • _) (var_subst _ _ _) @ _).
        refine (var_subst _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq stnweq _)).
    Qed.

  End Exponentiable.

  (** * 2. A construction of the lambda endomorphism theory of theory_presheaf *)

  Lemma presheaf_lambda_theory_aux
    {m n : nat}
    (f : stn m → (L _ : hSet))
    : extend_tuple (λ i : stn m, f i • (λ j, var (dni lastelement j))) (var lastelement)
    = (λ i, let c := invmap (stnweq) i in
        coprod_rect (λ _, (L (1 + n) : hSet))
          (λ i', f i' • (λ j, var (stnweq (inl j))))
          (λ i', var (stnweq (inr i'))) c).
  Proof.
    apply extend_tuple_eq.
    - intro i.
      symmetry.
      exact (maponpaths _ (homotinvweqweq _ _)).
    - exact (!maponpaths (λ x, let c := x in _) (homotinvweqweq _ _)).
  Qed.

  Definition presheaf_lambda_theory : lambda_theory.
  Proof.
    pose (exponential_object := pr1 theory_presheaf_exponentiable (theory_presheaf L) : presheaf L).
    use endomorphism_lambda_theory.
    - exact (presheaf_cat L).
    - exact (terminal_presheaf_cat _).
    - exact (bin_products_presheaf_cat _).
    - exact (theory_presheaf L).
    - exact theory_presheaf_exponentiable.
    - use (make_presheaf_morphism (P := exponential_object) (P' := theory_presheaf L)).
      + intro.
        apply abs.
      + abstract (
          intros m n a f;
          refine (_ @ abs_subst _ _ _);
          apply (maponpaths (λ x, abs (a • x)));
          symmetry;
          apply presheaf_lambda_theory_aux
        ).
    - use (make_presheaf_morphism (P := theory_presheaf L) (P' := exponential_object)).
      + intros n.
        apply appx.
      + abstract (
          intros m n a f;
          refine (app_subst _ _ _ @ _);
          apply (maponpaths (λ x, appx a • x));
          apply presheaf_lambda_theory_aux
        ).
  Defined.

  (** * 3. An isomorphism between the two λ-theories *)

  Section Iso.

    Definition presheaf_to_L
      : algebraic_theory_morphism_data presheaf_lambda_theory L.
    Proof.
      intros n f.
      refine ((f : presheaf_morphism (PO n) (theory_presheaf L)) n _).
      refine (pow_f_inv n n _).
      exact var.
    Defined.

    Definition L_to_presheaf
      : algebraic_theory_morphism_data L presheaf_lambda_theory.
    Proof.
      intros n s.
      unfold presheaf_lambda_theory.
      use (make_presheaf_morphism (P := PO n) (P' := (theory_presheaf L))).
      - intros n' t.
        refine (s • _).
        intro i.
        exact (pow_f n n' t i).
      - abstract (
          intros;
          refine (_ @ !subst_subst _ s _ _);
          apply maponpaths;
          apply funextfun;
          intro;
          now rewrite mor_op
        ).
    Defined.

    Lemma L_to_presheaf_to_L
      (n : nat)
      (l : (L n : hSet))
      : presheaf_to_L n (L_to_presheaf n l) = l.
    Proof.
      refine (_ @ subst_var _ _).
      apply (maponpaths (subst l)).
      apply funextfun.
      intro i.
      refine (maponpaths
        (λ x, x _ _)
        (!presheaf_mor_comp _ (pow_f n : presheaf_cat L⟦PO n, PO' n⟧) _)
      @ _).
      exact (maponpaths (λ x, pr1 x _ _ _) (z_iso_after_z_iso_inv (pow_iso n))).
    Qed.

    Lemma presheaf_to_L_to_presheaf
      (n : nat)
      (l : (presheaf_lambda_theory n : hSet))
      : L_to_presheaf n (presheaf_to_L n l) = l.
    Proof.
      apply (presheaf_morphism_eq _ (l : presheaf_morphism (PO n) ((theory_presheaf L)))).
      intro m.
      apply funextfun.
      intro x.
      refine (!mor_op _ _ _ @ _).
      apply maponpaths.
      refine (!mor_op _ _ _ @ _).
      refine (!_ @ maponpaths (λ x, pr1 x _ _) (z_iso_inv_after_z_iso (pow_iso n))).
      refine (maponpaths (λ x, x _) (presheaf_mor_comp _ _ _) @ _).
      apply (maponpaths (pow_f_inv n _)).
      apply funextsec.
      intro.
      exact (!var_subst _ _ _).
    Qed.

    Lemma L_to_presheaf_preserves_var
      (n : nat)
      (i : stn n)
      : mor_var_ax L_to_presheaf n i.
    Proof.
      apply (presheaf_morphism_eq (P := PO n) (P' := theory_presheaf L)).
      intro m.
      apply funextfun.
      intro t.
      apply var_subst.
    Qed.

    Lemma L_to_presheaf_preserves_subst
      (m n : nat)
      (f : (L m : hSet))
      (g : stn m → (L n : hSet))
      : mor_subst_ax L_to_presheaf m n f g.
    Proof.
      apply (presheaf_morphism_eq (P := PO n) (P' := theory_presheaf L)).
      intro l.
      refine (_ @ !presheaf_mor_comp (P'' := theory_presheaf L) _ _ _).
      apply funextfun.
      intro t.
      refine (subst_subst _ f g _ @ !_).
      apply (maponpaths (subst f)).
      apply funextfun.
      intro i.
      exact (maponpaths (λ x, x t) (!presheaf_mor_comp _ _ _) @
          maponpaths (λ x, pr1 x l t) (ProductPrCommutes _ _ _ (pow m) _ _ i)).
    Qed.

    Local Lemma aux2
      (n : nat)
      : pr2 (pow_f_inv (S n) (S n) var)
      = op (P := PO n) (pow_f_inv n n var) (λ i, var (stnweq (inl i))).
    Proof.
      do 2 refine (maponpaths (λ x, pr1 x _ _) (!z_iso_inv_after_z_iso (pow_iso n)) @ !_).
      do 2 refine (maponpaths (λ x, x _) (presheaf_mor_comp _ _ _) @ !_).
      apply (maponpaths (pr11 _ (S n))).
      apply funextsec.
      intro i.
      refine (maponpaths
        (λ x, x var)
        (!presheaf_mor_comp (P := PO' (S n)) (P'' := theory_presheaf L) _ _ _)
      @ _).
      refine (maponpaths (λ x, pr1 x _ _) (ProductPrCommutes _ _ _ (pow n) (pow' (S n)) _ i) @ !_).
      refine (eqtohomot (mor_op (pow_f n) _ _) i @ _).
      refine (maponpaths
        (λ x, op (P := PO' n) (x var) _ _)
        (!presheaf_mor_comp (P := PO' n) (P'' := PO' n) _ (pow_f _) _)
      @ _).
      refine (maponpaths
        (λ (x : presheaf_morphism (PO' n : presheaf L) (PO' n : presheaf L)), op (P := PO' n) (pr1 x n var) _ _)
        (z_iso_after_z_iso_inv (pow_iso n))
      @ _).
      exact (var_subst _ _ _).
    Qed.

    Lemma presheaf_to_L_preserves_app
      (n : nat)
      (s : (presheaf_lambda_theory n : hSet))
      : presheaf_to_L (S n) (appx s) = appx (presheaf_to_L n s).
    Proof.
      refine (invmap_hom_weq_eq _ _ @ _).
      match goal with
      | [ |- pr1 ?x1 _ _ • _ = _ ] => pose (x1' := x1)
      end.
      refine (maponpaths (λ x, pr1 x1' _ x • _) (aux2 n) @ _).
      refine (maponpaths (λ x, x • _) (mor_op
        (x1' : presheaf_morphism (PO n) (pr1 theory_presheaf_exponentiable _ : presheaf L))
      _ _) @ _).
      refine (subst_subst L (l := S n) (m := S (S n)) _ _ _ @ _).
      refine (maponpaths
        (λ x, x _ • _)
        (presheaf_mor_comp (P'' := plus_1_presheaf (theory_presheaf L)) _ _ _)
      @ _).
      refine (_ @ subst_var _ _).
      apply maponpaths.
      apply funextfun.
      intro i.
      refine (_ @ maponpaths _ (homotweqinvweq stnweq i)).
      induction (invmap stnweq i) as [i' | i'].
      - refine (maponpaths (λ x, x • _) (var_subst _ _ _) @ _).
        refine (var_subst _ _ _ @ _).
        refine (extend_tuple_i _ _ _ _ (dni_last_lt _) @ _).
        apply maponpaths.
        apply stn_eq.
        apply di_eq1.
        exact (stnlt (dni lastelement i')).
      - refine (var_subst _ _ _ @ _).
        exact (maponpaths _ (homotinvweqweq _ _)).
    Qed.

    Lemma presheaf_to_L_preserves_abs
      (n : nat)
      (s : (presheaf_lambda_theory (S n) : hSet))
      : presheaf_to_L n (abs s) = abs (presheaf_to_L (S n) s).
    Proof.
      refine (maponpaths (λ x, x _) (presheaf_mor_comp (P'' := theory_presheaf L) _ _ _) @ _).
      apply (maponpaths abs).
      refine (hom_weq_eq _ _ @ _).
      apply (maponpaths (λ x, pr1 s _ x)).
      refine (maponpaths (λ x, pr1 x _ _) (!z_iso_inv_after_z_iso (pow_iso _)) @ _).
      refine (maponpaths (λ x, x _) (presheaf_mor_comp (P'' := PO (S n)) _ _ _) @ _).
      apply (maponpaths (pow_f_inv (S n) _)).
      apply funextsec.
      intro i.
      do 2 refine (!_ @ maponpaths _ (homotweqinvweq stnweq i)).
      induction (invmap stnweq i) as [i' | i'];
        refine (maponpaths (λ x, (_ x : presheaf_morphism _ _) _ _) (homotinvweqweq stnweq _) @ _).
      - refine (maponpaths (λ x, x _) (presheaf_mor_comp (P'' := theory_presheaf L) _ _ _) @ _).
        refine (mor_op
          (ProductPr _ _ (pow n) _ : presheaf_morphism (PO _) (theory_presheaf L))
        _ _ @ _).
        refine (maponpaths
          (λ x, x _ • _)
          (!presheaf_mor_comp (P'' := theory_presheaf L) _ _ _)
        @ _).
        refine (maponpaths (λ x, pr1 x _ _ • _) (ProductPrCommutes _ _ _ (pow _) _ _ _) @ _).
        apply var_subst.
      - apply idpath.
    Qed.

    Definition presheaf_lambda_theory_iso
      : z_iso (C := lambda_theory_cat) presheaf_lambda_theory L.
    Proof.
      use make_lambda_theory_z_iso.
      - apply z_iso_inv.
        use make_algebraic_theory_z_iso.
        + intro n.
          use make_z_iso.
          * exact (λ l, L_to_presheaf n l).
          * exact (λ l, presheaf_to_L n l).
          * abstract (
              split;
              apply funextfun;
              intro l;
              [ exact (L_to_presheaf_to_L n l)
              | exact (presheaf_to_L_to_presheaf n l) ]
            ).
        + exact L_to_presheaf_preserves_var.
        + exact L_to_presheaf_preserves_subst.
      - exact presheaf_to_L_preserves_app.
      - exact presheaf_to_L_preserves_abs.
    Defined.

  End Iso.

End RepresentationTheorem.
