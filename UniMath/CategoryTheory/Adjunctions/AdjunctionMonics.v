(********************************************************************************************

 Right adjoints preserve monomorphisms

 We show that right adjoints preserve monomorphisms.

 ********************************************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Local Open Scope cat.

Definition right_adjoint_preserves_monics
           {C D : category}
           (R : C ⟶ D)
           (HR : is_right_adjoint R)
           (L := left_adjoint HR)
           (η := unit_from_right_adjoint HR)
           (ε := counit_from_right_adjoint HR)
           {x y : C}
           {f : x --> y}
           (Hf : isMonic f)
  : isMonic (#R f).
Proof.
  intros w g h p.
  assert (# L g · ε x · f = # L h · ε x · f) as q.
  {
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      exact (!(nat_trans_ax ε _ _ f)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!(nat_trans_ax ε _ _ f)).
    }
    refine (!_).
    rewrite !assoc.
    apply maponpaths_2.
    refine (!(functor_comp _ _ _) @ _ @ functor_comp _ _ _).
    apply maponpaths.
    exact p.
  }
  assert (# L g · ε x = # L h · ε x) as r.
  {
    use Hf.
    exact q.
  }
  pose (maponpaths (λ z, η _ · #R z) r) as r'.
  cbn in r'.
  rewrite !functor_comp in r'.
  rewrite !assoc in r'.
  assert (g · η _ · #R(ε _) = h · η _ · #R(ε _)) as r''.
  {
    etrans.
    {
      apply maponpaths_2.
      apply (nat_trans_ax η).
    }
    refine (r' @ _).
    apply maponpaths_2.
    refine (!_).
    apply (nat_trans_ax η).
  }
  refine (_ @ r'' @ _).
  - refine (!(id_right _) @ _).
    refine (!_).
    rewrite !assoc'.
    apply maponpaths.
    exact (triangle_2_statement_from_adjunction (right_adjoint_to_adjunction HR) x).
  - refine (_ @ id_right _).
    rewrite !assoc'.
    apply maponpaths.
    exact (triangle_2_statement_from_adjunction (right_adjoint_to_adjunction HR) x).
Qed.
