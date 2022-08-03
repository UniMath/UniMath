Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.Dialgebras.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategoriesWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.WhiskeredDisplayedBifunctors.
Require Import UniMath.CategoryTheory.Monoidal.DisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.TotalDisplayedMonoidalWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorsWhiskered.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalSectionsWhiskered.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section TheDefinition.

  Import BifunctorNotations.
  Import MonoidalNotations.
  Import DisplayedBifunctorNotations.
  Import DisplayedMonoidalNotations.

  Context {A B : category}
          {V : monoidal A} {W : monoidal B}
          {F G : A ⟶ B}
          (Fm : fmonoidal V W F) (Gm : fmonoidal_lax V W G).

  Local Definition base_disp : disp_cat A := dialgebra_disp_cat F G.

  Local Lemma base_disp_cells_isaprop (x y : A) (f : A⟦ x, y ⟧)
        (xx : base_disp x) (yy : base_disp y): isaprop (xx -->[ f] yy).
  Proof.
    intros Hyp Hyp'.
    apply B.
  Qed.

  Definition dialgebra_disp_tensor_op {a a' : A} (f : base_disp a) (f' : base_disp a') : base_disp (a ⊗_{ V} a').
  Proof.
    refine (_ · fmonoidal_preservestensordata Gm a a').
    refine (pr1 (fmonoidal_preservestensorstrongly Fm a a') · _).
    exact (f ⊗^{W} f').
  Defined.

  (** we do not follow the division into the two whiskerings here *)
  Lemma dialgebra_disp_tensor_comp_aux {a1 a2 a1' a2' : A} {h: a1 --> a1'} {h': a2 --> a2'}
    (f : base_disp a1) (f' : base_disp a2) (g : base_disp a1') (g' : base_disp a2')
    : f -->[h] g -> f'-->[h'] g' -> dialgebra_disp_tensor_op f f' -->[ h ⊗^{V} h' ] dialgebra_disp_tensor_op g g'.
  Proof.
    intros Hyp Hyp'.
    hnf in Hyp, Hyp' |- *.
    unfold dialgebra_disp_tensor_op.
  Admitted.

  Definition dialgebra_disp_tensor : disp_tensor base_disp V.
  Proof.
    use make_disp_bifunctor.
    - use make_disp_bifunctor_data.
      + intros a a' f f'. exact (dialgebra_disp_tensor_op f f').
      + intros a a1 a2 g f f1 f2 Hyp'. cbn. rewrite <- when_bifunctor_becomes_leftwhiskering.
        apply dialgebra_disp_tensor_comp_aux.
        * apply id_disp.
        * assumption.
      + intros a1 a2 a f g1 g2 g Hyp. cbn. rewrite <- when_bifunctor_becomes_rightwhiskering.
        apply dialgebra_disp_tensor_comp_aux.
        * assumption.
        * apply id_disp.
    - red. repeat split; red; intros; apply base_disp_cells_isaprop.
  Defined.

  Definition dialgebra_disp_unit: base_disp I_{ V}
    := pr1 (fmonoidal_preservesunitstrongly Fm) · fmonoidal_preservesunit Gm.

  Lemma dialgebra_disp_leftunitor_data : disp_leftunitor_data dialgebra_disp_tensor dialgebra_disp_unit.
  Proof.
    intros a f.
    cbn. unfold dialgebra_disp_unit, dialgebra_disp_tensor_op.
  Admitted.

  Lemma dialgebra_disp_leftunitorinv_data : disp_leftunitorinv_data dialgebra_disp_tensor dialgebra_disp_unit.
  Proof.
  Admitted.

  Lemma dialgebra_disp_rightunitor_data : disp_rightunitor_data dialgebra_disp_tensor dialgebra_disp_unit.
  Proof.
  Admitted.

  Lemma dialgebra_disp_rightunitorinv_data : disp_rightunitorinv_data dialgebra_disp_tensor dialgebra_disp_unit.
  Proof.
  Admitted.

  Lemma dialgebra_disp_associator_data : disp_associator_data dialgebra_disp_tensor.
  Proof.
  Admitted.

  Lemma dialgebra_disp_associatorinv_data : disp_associatorinv_data dialgebra_disp_tensor.
  Proof.
  Admitted.

  Definition dialgebra_disp_monoidal_data : disp_monoidal_data base_disp V.
  Proof.
    exists dialgebra_disp_tensor.
    exists dialgebra_disp_unit.
    exists dialgebra_disp_leftunitor_data.
    exists dialgebra_disp_leftunitorinv_data.
    exists dialgebra_disp_rightunitor_data.
    exists dialgebra_disp_rightunitorinv_data.
    exists dialgebra_disp_associator_data.
    exact dialgebra_disp_associatorinv_data.
  Defined.

  Lemma dialgebra_disp_leftunitor_law :
    disp_leftunitor_law dlu^{ dialgebra_disp_monoidal_data} dluinv^{ dialgebra_disp_monoidal_data}.
  Proof.
    repeat (split; try (red; intros; apply base_disp_cells_isaprop)); try apply base_disp_cells_isaprop.
  Qed.

  Lemma dialgebra_disp_rightunitor_law :
    disp_rightunitor_law dru^{ dialgebra_disp_monoidal_data} druinv^{ dialgebra_disp_monoidal_data}.
  Proof.
    repeat (split; try (red; intros; apply base_disp_cells_isaprop)); try apply base_disp_cells_isaprop.
  Qed.

  Lemma dialgebra_disp_associator_law :
    disp_associator_law dα^{ dialgebra_disp_monoidal_data} dαinv^{ dialgebra_disp_monoidal_data}.
  Proof.
    repeat (split; try (red; intros; apply base_disp_cells_isaprop)); try apply base_disp_cells_isaprop.
  Qed.

  Definition dialgebra_disp_monoidal : disp_monoidal base_disp V.
  Proof.
    exists dialgebra_disp_monoidal_data.
    split.
    exact dialgebra_disp_leftunitor_law.
    split; [ exact dialgebra_disp_rightunitor_law |].
    split; [ exact dialgebra_disp_associator_law |].
    (** now we benefit from working in a displayed monoidal category *)
    split; red; intros; apply base_disp_cells_isaprop.
  Defined.

  Definition dialgebra_monoidal : monoidal (dialgebra F G) := total_monoidal dialgebra_disp_monoidal.

End TheDefinition.
