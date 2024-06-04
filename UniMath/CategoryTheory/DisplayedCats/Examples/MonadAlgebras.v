Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Monads.MonadAlgebras.
Require Import UniMath.CategoryTheory.Monads.Comonads.
Require Import UniMath.CategoryTheory.Monads.ComonadCoalgebras.
Require Import UniMath.CategoryTheory.catiso.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp.

Definition make_Algebra_data {C : category} (T : Monad C) (X : C) (α : T X --> X) : Algebra_data T.
Proof.
  use tpair.
  - exact X.
  - exact α.
Defined.

Definition MonadAlg_disp_ob_mor {C : category} (T : Monad C) : disp_cat_ob_mor C.
Proof.
  use make_disp_cat_ob_mor.
  - intro X.
    exact (∑ (α : (T X) --> X), Algebra_laws _ (make_Algebra_data T X α)).
  - intros X Y αX αY f.
    (* simpl in αX, αY. *)
    set (X' := make_Algebra_data T X (pr1 αX),, pr2 αX : Algebra T).
    set (Y' := make_Algebra_data T Y (pr1 αY),, pr2 αY : Algebra T).
    exact (is_Algebra_mor T (X:=X') (Y:=Y') f).
Defined.

#[reversible=no] Coercion Algebra_from_MonadAlg_disp {C : category} {T : Monad C} {x : C}
    (X : MonadAlg_disp_ob_mor T x) : Algebra T :=
  (make_Algebra_data T x (pr1 X),, pr2 X).

#[reversible=no] Coercion Algebra_mor_from_Algebra_mor_disp {C : category} {T : Monad C}
    {x y : C} (X : MonadAlg_disp_ob_mor T x) (Y : MonadAlg_disp_ob_mor T y)
    {f : x --> y} (F : X -->[f] Y) : Algebra_mor T X Y := (f,, F).

Definition MonadAlg_disp_id_comp {C : category} (T : Monad C) : disp_cat_id_comp C (MonadAlg_disp_ob_mor T).
Proof.
  split.
  - intros x xx.
    abstract (
      exact (Algebra_mor_commutes T (Algebra_mor_id T xx))
    ).
  - intros x y z f g xx yy zz ff gg.
    abstract (
      exact (Algebra_mor_commutes T (Algebra_mor_comp T xx yy zz ff gg))
    ).
Qed.

Definition MonadAlg_disp_data {C : category} (T : Monad C) : disp_cat_data C.
Proof.
  use tpair.
  - exact (MonadAlg_disp_ob_mor T).
  - exact (MonadAlg_disp_id_comp T).
Defined.

Definition MonadAlg_disp {C : category} (T : Monad C) : disp_cat C.
Proof.
  use tpair.
  - exact (MonadAlg_disp_data T).
  - abstract (
      repeat split; intros; try (apply homset_property);
      apply isasetaprop;
      apply homset_property
    ).
Defined.

Definition MonadAlg_tot {C : category} (T : Monad C) : category :=
    total_category (MonadAlg_disp T).

Definition MonadAlg_disp_Algebra_functor {C : category} (T : Monad C) :
    MonadAlg_tot T ⟶ (MonadAlg T).
Proof.
  use make_functor.
  - use make_functor_data.
    * intro X.
      exact (Algebra_from_MonadAlg_disp (pr2 X)).
    * intros.
      exact (Algebra_mor_from_Algebra_mor_disp (pr2 a) (pr2 b) (pr2 X)).
  - abstract (
      split; [intro|intros a b c f g];
        (apply subtypePath; [intro; apply homset_property|]; reflexivity)
    ).
Defined.

Lemma MonadAlg_disp_is_Algebra {C : category} (T : Monad C) :
    MonadAlg_tot T = MonadAlg T.
Proof.
  apply catiso_to_category_path.
  use tpair.
  - exact (MonadAlg_disp_Algebra_functor T).
  - split.
    * intros a b.
      use isweq_iso.
      + exact (idfun _).
      + intros. apply idpath.
      + intros. apply idpath.
    * use isweq_iso.
      + intros [[x α] laws].
        use tpair.
        -- exact x.
        -- exact (α,, laws).
      + intro. apply idpath.
      + intro. apply idpath.
Qed.


Definition make_Coalgebra_data {C : category} (T : Comonad C) (X : C) (α : X --> T X) : Coalgebra_data T.
Proof.
  use tpair.
  - exact X.
  - exact α.
Defined.

Definition ComonadCoalg_disp_ob_mor {C : category} (T : Comonad C) : disp_cat_ob_mor C.
Proof.
  use make_disp_cat_ob_mor.
  - intro X.
    exact (∑ (α : X --> T X), Coalgebra_laws _ (make_Coalgebra_data T X α)).
  - intros X Y αX αY f.
    (* simpl in αX, αY. *)
    set (X' := make_Coalgebra_data T X (pr1 αX),, pr2 αX : Coalgebra T).
    set (Y' := make_Coalgebra_data T Y (pr1 αY),, pr2 αY : Coalgebra T).
    exact (is_Coalgebra_mor T (X:=X') (Y:=Y') f).
Defined.

#[reversible=no] Coercion Coalgebra_from_ComonadCoalg_disp {C : category} {T : Comonad C} {x : C}
    (X : ComonadCoalg_disp_ob_mor T x) : Coalgebra T :=
  (make_Coalgebra_data T x (pr1 X),, pr2 X).

#[reversible=no] Coercion Coalgebra_mor_from_Coalgebra_mor_disp {C : category} {T : Comonad C}
    {x y : C} (X : ComonadCoalg_disp_ob_mor T x) (Y : ComonadCoalg_disp_ob_mor T y)
    {f : x --> y} (F : X -->[f] Y) : Coalgebra_mor T X Y := (f,, F).

Definition ComonadCoalg_disp_id_comp {C : category} (T : Comonad C) : disp_cat_id_comp C (ComonadCoalg_disp_ob_mor T).
Proof.
  split.
  - intros x xx.
    abstract (
      exact (Coalgebra_mor_commutes T (Coalgebra_mor_id T xx))
    ).
  - intros x y z f g xx yy zz ff gg.
    abstract (
      exact (Coalgebra_mor_commutes T (Coalgebra_mor_comp T xx yy zz ff gg))
    ).
Qed.

Definition ComonadCoalg_disp_data {C : category} (T : Comonad C) : disp_cat_data C.
Proof.
  use tpair.
  - exact (ComonadCoalg_disp_ob_mor T).
  - exact (ComonadCoalg_disp_id_comp T).
Defined.

Definition ComonadCoalg_disp {C : category} (T : Comonad C) : disp_cat C.
Proof.
  use tpair.
  - exact (ComonadCoalg_disp_data T).
  - abstract (
      repeat split; intros; try (apply homset_property);
      apply isasetaprop;
      apply homset_property
    ).
Defined.

Definition ComonadCoalg_tot {C : category} (T : Comonad C) : category :=
    total_category (ComonadCoalg_disp T).

Definition ComonadCoalg_disp_Coalgebra_functor {C : category} (T : Comonad C) :
    ComonadCoalg_tot T ⟶ (ComonadCoalg T).
Proof.
  use make_functor.
  - use make_functor_data.
    * intro X.
      exact (Coalgebra_from_ComonadCoalg_disp (pr2 X)).
    * intros.
      exact (Coalgebra_mor_from_Coalgebra_mor_disp (pr2 a) (pr2 b) (pr2 X)).
  - abstract (
      split; [intro|intros a b c f g];
        (apply subtypePath; [intro; apply homset_property|]; reflexivity)
    ).
Defined.

Lemma ComonadCoalg_disp_is_Coalgebra {C : category} (T : Comonad C) :
    ComonadCoalg_tot T = ComonadCoalg T.
Proof.
  apply catiso_to_category_path.
  use tpair.
  - exact (ComonadCoalg_disp_Coalgebra_functor T).
  - split.
    * intros a b.
      use isweq_iso.
      + exact (idfun _).
      + intros. apply idpath.
      + intros. apply idpath.
    * use isweq_iso.
      + intros [[x α] laws].
        use tpair.
        -- exact x.
        -- exact (α,, laws).
      + intro. apply idpath.
      + intro. apply idpath.
Qed.
