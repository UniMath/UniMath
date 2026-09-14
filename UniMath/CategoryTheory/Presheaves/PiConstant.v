(**

 ∏-types of constant presheaves

 Each set `X` induces a constant presheaf on `C`, which maps every object in `C`
 to the set `X`. We show that the dependent product of constant presheaves is
 again a constant presheaf given by the function type. We instantiate this fact
 to sequences of natural numbers (aka the Baire space).

 Content
 1. ∏-types of constant presheaves
 2. The presheaf of sequences of natural numbers (the Baire space)

 *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Fiber.
Require Import UniMath.CategoryTheory.Presheaves.DependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.DisplayedCatOfDependentPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.TotalPresheaf.
Require Import UniMath.CategoryTheory.Presheaves.Constructions.
Require Import UniMath.CategoryTheory.Presheaves.PiTypes.
Require Import UniMath.CategoryTheory.Presheaves.NaturalNumbers.

Local Open Scope cat.

Section PiOfConstant.
  Context {C : category}.

  (** * 1. ∏-types of constant presheaves *)
  Definition pi_dep_psh_of_constant_mor
             (Γ : C^op ⟶ HSET)
             (X Y : hSet)
    : dep_psh_nat_trans
        (pi_dep_psh
           (constant_dep_psh Γ X)
           (constant_dep_psh (total_psh (constant_dep_psh Γ X)) Y))
        (constant_dep_psh _ (funset X Y))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - intros x xx φ a ; cbn in *.
      exact (φ x (identity _) a).
    - abstract
        (intros x y xx yy f p q φ ;
         use funextsec ;
         intro a ; cbn ;
         refine (_ @ !(dep_pi_psh_function_natural _ _ φ f (identity _) a)) ;
         cbn ;
         rewrite id_left, id_right ;
         apply idpath).
  Defined.

  Definition pi_dep_psh_of_constant_inv
             (Γ : C^op ⟶ HSET)
             (X Y : hSet)
    : dep_psh_nat_trans
        (constant_dep_psh _ (funset X Y))
        (pi_dep_psh
           (constant_dep_psh Γ X)
           (constant_dep_psh (total_psh (constant_dep_psh Γ X)) Y))
        (nat_trans_id _).
  Proof.
    use make_dep_psh_nat_trans.
    - intros x xx φ ; cbn in *.
      use make_dep_pi_psh_function.
      + intros y f a.
        exact (φ a).
      + abstract
          (intros y₁ y₂ f₁ f₂ a ; cbn ;
           apply idpath).
    - abstract
        (intros x y xx yy f p q φ ;
         use dep_pi_psh_function_eq ;
         intros z g a ;
         cbn ;
         apply idpath).
  Defined.

  Definition pi_dep_psh_of_constant
             (Γ : C^op ⟶ HSET)
             (X Y : hSet)
    : z_iso
        (C := (disp_cat_dep_psh C)[{Γ}])
        (pi_dep_psh
           (constant_dep_psh Γ X)
           (constant_dep_psh (total_psh (constant_dep_psh Γ X)) Y))
        (constant_dep_psh Γ (funset X Y)).
  Proof.
    use make_z_iso.
    - exact (pi_dep_psh_of_constant_mor Γ X Y).
    - exact (pi_dep_psh_of_constant_inv Γ X Y).
    - abstract
        (split ;
         use dep_psh_nat_trans_eq ;
         intros x xx φ ;
         refine (dep_psh_fiber_comp _ _ _ _ @ _) ;
         [ | apply idpath ] ;
         use dep_pi_psh_function_eq ;
         intros y f a ;
         refine (dep_pi_psh_function_natural _ _ φ f (identity _) a @ _) ;
         cbn in * ;
         rewrite id_right ;
         apply idpath).
  Defined.

  (** * 2. The presheaf of sequences of natural numbers (the Baire space) *)
  Definition dep_psh_baire_space
             (Γ : C^op ⟶ HSET)
    : z_iso
        (C := (disp_cat_dep_psh C)[{Γ}])
        (pi_dep_psh
           (nno_dep_psh Γ)
           (nno_dep_psh (total_psh (nno_dep_psh Γ))))
        (constant_dep_psh Γ (funset natset natset))
    := pi_dep_psh_of_constant Γ natset natset.
End PiOfConstant.
