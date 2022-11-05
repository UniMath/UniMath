(** ** Fibered algebras

  Described in "Homotopy-initial algebras in type theory" by Steve Awodey,
  Nicola Gambino, Kristina Sojakova (arXiv:1504.05531v1).

  Ideas and proofs adapted from original code at
  https://github.com/kristinas/hinitiality by Langston Barrett (@siddharthist).
 *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.MoreFoundations.Univalence.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Induction.FunctorAlgebras_legacy.
Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.W.Core.

Local Open Scope Cat.

Section Fibered.
  Context {A : UU} {B : A -> UU}.

  Local Notation "X ⇒ Y" := (algebra_mor (polynomial_functor _ _) X Y).
  Local Notation F := (polynomial_functor A B).

  (** A fibered P-algebra.

      (Definition 4.5 in Awodey, Gambino, and Sojakova)
  *)
  Definition fibered_alg (X : algebra_ob F) : UU :=
    (∑ (E : (alg_carrier _ X) -> UU),
    ∏ (x : F (alg_carrier _ X)), (* ∑ (a : A), B a → X *)
    (∏ (b : B (pr1 x)), E ((pr2 x) b)) -> E ((pr2 X) x)).

  (** Any P-algebra can be made into a fibered P-algebra. *)
  Definition alg2fibered_alg {X : algebra_ob F} :
    algebra_ob F -> fibered_alg X.
  Proof.
    intro Alg.
    split with (fun _ => pr1 Alg).
    intros f.
    exact (fun g => (pr2 Alg) (pr1 f,, g)).
  Defined.

  (** Any fibered P-algebra can be made into a 'total' P-algebra. *)
  Definition fibered_alg2alg {X : algebra_ob F} :
    fibered_alg X -> algebra_ob F.
  Proof.
    intro E.
    pose (supx := pr2 X).
    pose (supe := pr2 E).
    split with (∑ x : pr1 X, pr1 E x).
    intro z; cbn in z; unfold polynomial_functor_obj in *.
    pose (z' := ((pr1 z),, pr1 ∘ (pr2 z)) : (∑ a : A, B a → pr1 X)).
    refine (supx z',, supe z' (λ b, (pr2 (pr2 z b)))).
  Defined.

  (** A P-algebra section.

      (Definition 4.6 in Awodey, Gambino, and Sojakova)
    *)
  Definition algebra_section {X : algebra_ob F} : ∏ (Y : fibered_alg X), UU.
  Proof.
    intro E.
    pose (supx := pr2 X).
    pose (supe := pr2 E).
    exact ((∑ (f : ∏ x : pr1 X, pr1 E x),
            ∏ a, f (supx a) = supe a (f ∘ (pr2 a)))).
  Defined.

  (** A P-algebra section homotopy.

      (Definition 4.7 in Awodey, Gambino, and Sojakova)
  *)
  Definition algebra_sec_homot {X : algebra_ob F} :
    ∏ {Y : fibered_alg X} (i j : algebra_section Y), UU.
  Proof.
    intros E.
    pose (supx := pr2 X).
    pose (supe := pr2 E).
    intros f g.
    refine (∑ (n : pr1 f ~ pr1 g), ∏ x, pr2 f x @ maponpaths (supe x) _ = n (supx x) @ pr2 g x).
    exact (funextsec _ _ _ (@funhomotsec _ _ _ (pr2 x) (pr1 f) (pr1 g) n)).
  Defined.

  Definition algebra_mor_to_algsec {X Y : algebra_ob F}
            (f : X ⇒ Y) : @algebra_section X (alg2fibered_alg Y).
  Proof.
    unfold algebra_section; cbn.
    refine (pr1 f,, _).
    exact (eqtohomot (pr2 f)).
  Defined.

  (** A P-algebra homotopy.

      (Definition 4.7 in Awodey, Gambino, and Sojakova)
   *)
  Definition algebra_mor_homot {X Y : algebra_ob F} (i j : X ⇒ Y) : UU :=
    algebra_sec_homot (algebra_mor_to_algsec i) (algebra_mor_to_algsec j).

  (** The identity homotopy on a P-algebra section. *)
  Definition algebra_sec_homot_id {X : algebra_ob F} {Y : fibered_alg X}
             {f : algebra_section Y} : algebra_sec_homot f f.
  Proof.
    pose (supx := pr2 X).
    pose (supy := pr2 Y).
    split with (fun _ => idpath _).
    intro x.
    transitivity (pr2 f x @ maponpaths (supy x) (idpath _)).
    - do 2 (apply maponpaths).
      unfold funhomotsec; cbn.
      assert (H : (λ x0 : B (pr1 x), idpath (pr1 f (pr2 x x0))) =
                  (toforallpaths _ (pr1 f ∘ pr2 x) (pr1 f ∘ pr2 x) (idpath _))).
      reflexivity.
      refine ((maponpaths _ H) @ _).
      apply funextsec_toforallpaths.
    - cbn; apply pathscomp0rid.
  Defined.

  (** The canonical function from the path space between two P-algebra sections
      to the type of P-algebra section homotopies. *)
  Definition algebra_section_path_to_homot {X : algebra_ob _} {Y : fibered_alg X}
             (i j : algebra_section Y) (p : i = j) : algebra_sec_homot i j.
  Proof.
    induction p.
    exact algebra_sec_homot_id.
  Defined.

  (** The identity homotopy on a P-algebra morphism. *)
  Definition algebra_mor_homot_id {X Y : algebra_ob F}
             {i : algebra_mor _ X Y} : algebra_mor_homot i i
    := @algebra_sec_homot_id _ (alg2fibered_alg Y) (algebra_mor_to_algsec i).

  (** A "(homotopy) uniqueness principle" for a P-algebra X: there exists a
      homotopy (and hence a path) between any two P-algebra morphisms into any
      other P-algebra Y.

      This is a little different than in Awodey, Gambino, and Sojakova.
      The main difference is that here we relate arbitrary two morphisms i,j
      whereas the rules in 5.8 relate an arbitrary morphism i to the canonical
      morphism given by the first two rules in 5.8. Our formulation has the
      advantage that it does not require the canonical morphism to exist, i.e.,
      the type X does not have to satisfy the recursion princple for the
      uniqueness principle to make sense.

      (Loosely corresponds to the last two rules in Proposition 5.8
       in Awodey, Gambino, and Sojakova)
   *)
  Definition homotopy_uniqueness_principle (X : algebra_ob F) : UU :=
    ∏ (Y : algebra_ob F) (i j : algebra_mor F X Y), algebra_mor_homot i j.

  (** The "induction principle" for a P-algebra X: any fibered P-algebra Y has a
      section.

      (Definition 5.1 in Awodey, Gambino, and Sojakova)
   *)
  Definition is_preinitial_sec (X : algebra_ob F) : UU :=
    ∏ (Y : fibered_alg X), algebra_section Y.

  (** A "fibered uniqueness principle": there exists a homotopy (and hence a
      path) between any two P-algebra sections of any fibered algebra.

      (Loosely corresponds to the rules in Proposition 5.3 in Awodey, Gambino,
       and Sojakova)
   *)
  Definition fibered_uniqueness (X : algebra_ob F) : UU :=
    ∏ (Y : fibered_alg X) (i j : algebra_section Y), algebra_sec_homot i j.
End Fibered.
