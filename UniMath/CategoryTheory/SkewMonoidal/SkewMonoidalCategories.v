(**
  Skew-Monoidal categories


Ambroise LAFONT 2020
*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Local Notation "'id' X" := (identity X) (at level 30).

Local Notation "C ⊠ D" := (precategory_binproduct C D) (at level 38).
Local Notation "( c , d )" := (make_precatbinprod c d).
Local Notation "( f #, g )" := (precatbinprodmor f g).



Local Notation φ₁ := (functor_fix_fst_arg _ _ _).
Local Notation φ₂ := (functor_fix_snd_arg _ _ _).

Local Declare Scope functor_scope.
Local Infix "×" := pair_functor  : functor_scope .
Delimit Scope functor_scope with F.

Definition skewmonoidal_data : UU :=
  ∑ (V : precategory)(tensor : V ⊠ V ⟶ V) (I : V),
        (* left unitor *) φ₁ tensor I   ⟹ functor_identity V ×
        (* right unitor *) functor_identity V ⟹ φ₂ tensor I ×
        (* associator *) (tensor × (functor_identity _))%F ∙ tensor ⟹
                             (precategory_binproduct_unassoc _ _ _)
                             ∙ (functor_identity V × tensor)%F ∙ tensor .

Coercion precat_from_skewmonoidal (V : skewmonoidal_data) : precategory := pr1 V.

Definition skewmonoidal_tensor (V : skewmonoidal_data) :
   V ⊠ V ⟶ V := pr1 (pr2 V).

Definition skewmonoidal_I (V : skewmonoidal_data) :
    V := pr1 (pr2 (pr2 V)).

Local Notation tensor := (skewmonoidal_tensor _).
Local Notation I := (skewmonoidal_I _).

Local Notation "X ⊗ Y" := (tensor (X, Y)).
Notation "f #⊗ g" :=
   (functor_on_morphisms (functor_data_from_functor _ _ tensor) (f #, g))
                         (at level 31).

Local Notation nts := (pr2 (pr2 (_ : skewmonoidal_data))) .

Definition skewmonoidal_unitl_nt (V : skewmonoidal_data) :
  φ₁ tensor I  ⟹ functor_identity V :=
  pr1 (pr2 nts).


Definition skewmonoidal_unitl (V : skewmonoidal_data) (x : V) :
  I ⊗ x --> x := skewmonoidal_unitl_nt V x.

Local Notation λ' := (skewmonoidal_unitl _).

Definition skewmonoidal_unitl_ax (V : skewmonoidal_data) {x y : V} (f : x --> y) :
  (identity I) #⊗ f · λ' y = λ' x · f
  := nat_trans_ax (skewmonoidal_unitl_nt V) _ _ f.


Definition skewmonoidal_unitr_nt (V : skewmonoidal_data) :
         functor_identity V ⟹ φ₂ tensor I := pr1 (pr2 (pr2 nts)).

Definition skewmonoidal_unitr (V : skewmonoidal_data) (x : V) :
  x --> x ⊗ I := skewmonoidal_unitr_nt V x.

Local Notation ρ' := (skewmonoidal_unitr _).

Definition skewmonoidal_unitr_ax (V : skewmonoidal_data) {x y : V} (f : x --> y) :
  f · ρ' y = ρ' x · f #⊗ identity I
  := nat_trans_ax (skewmonoidal_unitr_nt V) _ _ f.



Definition skewmonoidal_assoc_nt (V : skewmonoidal_data) :
         (tensor × (functor_identity _))%F ∙ tensor ⟹
                             (precategory_binproduct_unassoc _ _ _)
                             ∙ (functor_identity V × tensor)%F ∙ tensor
                             := pr2 (pr2 (pr2 nts)).

Definition skewmonoidal_assoc (V : skewmonoidal_data) (x y z : V) :
  x ⊗ y ⊗ z --> x ⊗ (y ⊗ z) := skewmonoidal_assoc_nt V ((x , y) , z).

Local Notation α' := (skewmonoidal_assoc _).

Definition skewmonoidal_assoc_ax (V : skewmonoidal_data)
           {x x' y y' z z' : V} (f : x --> x')(g : y --> y')(h : z --> z') :
  ((f #⊗ g) #⊗ h) · α' x' y' z' = α' x y z · (f #⊗ (g #⊗ h))
  := nat_trans_ax (skewmonoidal_assoc_nt V) _ _ ((f #, g) #, h).


Definition skewmonoidal_precategory : UU :=
  ∑ (V : skewmonoidal_data),
  ρ' I · λ' I = identity (C := V) I ×
   (∏ (a b : V), ρ' a #⊗ id b  · α' a I b · id a #⊗  λ' b = id (a ⊗ b)) ×
   (∏ (a b : V), α' I a b · λ' (a ⊗ b) = λ' a #⊗ id b) ×
   (∏ (a b : V), ρ' (a⊗b) · α' a b I = id a #⊗ ρ' b) ×
   (∏ (a b c d : V), α' (a ⊗ b) c d · α' a b (c ⊗ d) =
                     α' a b c #⊗ id d · α' a (b ⊗ c)  d ·
                         id a #⊗ α' b c d).

Coercion data_from_skewmonoidal (V : skewmonoidal_precategory) : skewmonoidal_data := pr1 V.

Local Notation eq := (pr2 (_ : skewmonoidal_precategory)).

Definition skewmonoidal_rho_lambda_eq (V : skewmonoidal_precategory) : ρ' I · λ' I = identity (C := V) I :=
   pr1 eq.
Definition skewmonoidal_triangle_eq (V : skewmonoidal_precategory) :
  ∏ (a b : V), ρ' a #⊗ id b  · α' a I b · id a #⊗  λ' b = id (a ⊗ b)
  := pr1 (pr2 eq).
Definition skewmonoidal_alpha_lambda_eq (V : skewmonoidal_precategory) :
  ∏ (a b : V), α' I a b · λ' (a ⊗ b) = λ' a #⊗ id b := pr1 (pr2 (pr2 eq)).

Definition skewmonoidal_rho_alpha_eq (V : skewmonoidal_precategory) :
  ∏ (a b : V), ρ' (a⊗b) · α' a b I = id a #⊗ ρ' b := pr1 (pr2 (pr2 (pr2 eq))).
Definition skewmonoidal_pentagon_eq (V : skewmonoidal_precategory) :
  ∏ (a b c d : V), α' (a ⊗ b) c d · α' a b (c ⊗ d) =
                     α' a b c #⊗ id d · α' a (b ⊗ c)  d ·
                         id a #⊗ α' b c d
  :=  (pr2 (pr2 (pr2 (pr2 eq)))).

Lemma I_mult_laws (V : skewmonoidal_precategory) (X : V) : α' I I X · identity (C := V) I #⊗ λ' X · λ' X = λ' I #⊗ identity X · λ' X.
Proof.
   etrans.
    {
      etrans;[apply pathsinv0,assoc|].
      apply cancel_precomposition.
      apply skewmonoidal_unitl_ax.
    }
    rewrite assoc.
    apply cancel_postcomposition.
    apply skewmonoidal_alpha_lambda_eq.
Qed.
