(** ** Uniqueness of M-types

    M-types are unique up to propositional equality.

    Author: Langston Barrett (@siddharthist)
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.
Require Import UniMath.CategoryTheory.categories.Types.
Require Import UniMath.Induction.PolynomialFunctors.
Require Import UniMath.Induction.M.Core.

Section Uniqueness.

  Local Open Scope functions.
  Local Open Scope cat.

  Context (A : UU).
  Context (B : A → UU).

  (** Following the paper, we have [X ⇒ Y] = Hom(X, Y) *)
  Local Notation F := (polynomial_functor A B). (* can be coerced to a function *)
  Local Notation "F*" := (polynomial_functor_arr A B).
  Local Notation "X ⇒ Y" := (coalgebra_homo F X Y).

  (** Since we can't use the standard categorical proof, we must re-prove that
      final coalgebras are unique up to isomorphism.

      (Lemma 5 in Ahrens, Capriotti, and Spadotti)
   *)

  (** We prove that their carriers (first projections) are isomorphic, and hence
      equal (by univalence).

      This is standard categorical reasoning: each has exactly one arrow to the
      other, which, composing, gives an endormorphism. However, each has exactly
      one endomorphism, the identity map. Therefore, they are isomorphic. *)

  Lemma M_carriers_iso : ∏ X Y : M B, (coalgebra_ob _ X) ≃
                                      (coalgebra_ob _ Y).
  Proof.
    intros X Y.

    (** Get the coalgebra morphisms X → Y and Y → X via finality *)
    pose (X_mor_Y := iscontrpr1 (pr2 Y X)).
    pose (Y_mor_X := iscontrpr1 (pr2 X Y)).

    apply (weq_iso
             (mor_from_coalgebra_homo _ _ _ X_mor_Y)
             (mor_from_coalgebra_homo _ _ _ Y_mor_X)).
    - intro x.
      apply (@eqtohomot _ _ (Y_mor_X ∘ X_mor_Y) (idfun _)).
      refine (base_paths (coalgebra_homo_comp _ _ _ _ X_mor_Y Y_mor_X)
                         (coalgebra_homo_id F X) _).
      apply (proofirrelevancecontr (pr2 X X)).
    - intro y.
      apply (@eqtohomot _ _ (X_mor_Y ∘ Y_mor_X) (idfun _)).
      refine (base_paths (coalgebra_homo_comp _ _ _ _ Y_mor_X X_mor_Y)
                         (coalgebra_homo_id F Y) _).
      apply (proofirrelevancecontr (pr2 Y Y)).
  Defined.

  (** Note the crucial use of univalence *)
  Lemma M_carriers_eq : ∏ X Y : M B, (coalgebra_ob _ X) = (coalgebra_ob _ Y).
  Proof.
    exact (fun X Y => weqtopaths (M_carriers_iso X Y)).
  Defined.

  (** Now we must prove that the coalgebra morphisms, when transported along
      the path M_carriers_eq, will be equal.

      (≅⇒≡ in HoTT/M-types)
   *)

  (* We use "refine (x @ _)" instead of "rewrite" for more predictable proof terms. *)
  Lemma M_coalg_eq : ∏ X Y : M B, M_coalgebra B X = M_coalgebra B Y.
  Proof.
    intros X Y.
    pose (π1eq := (M_carriers_eq X Y)).
    pose (f := pr1 ((pr2 Y) (M_coalgebra B X))).
    apply (total2_paths_f π1eq).

    (** Some shorthands for items we'll use *)
    pose (is_final_X := pr2 X).
    pose (is_final_Y := pr2 Y).
    pose (θ := pr2 (pr1 X)).
    pose (ψ := pr2 (pr1 Y)).

    (** substⁱ-lemma in HoTT/M-types *)
    assert (trans_fun : forall {X Y : UU} {F : UU → UU} {f : X → F X} {g : Y → F Y}
                          (p : X = Y),
               (forall (x : X), transportf F p (f x) = g (transportf (idfun UU) p x)) →
               transportf (λ X, X → F X) p f = g).
    {
      intros ? ? ? ? ? p H.
      induction p.
      unfold transportf.
      apply funextfun.
      exact H.
    }

    apply trans_fun.
    intro x.

    (** imap-subst in HoTT/M-types *)
    assert (arr_transport :
              forall {X Y : UU} (p : X = Y),
                F* (transportf (idfun _) p) = transportf F p).
    {
      intros ? ? p.
      induction p.
      reflexivity.
    }

    (** In HoTT/M-types: lemma₁ : ∀ i x → subst (λ Z → Z i) π₁≡ x ≡ proj₁ f i x *)
    assert (lemma1 : forall x : pr1 (pr1 X), transportf (idfun UU) π1eq x = (pr1 f) x).
    {
      intro.
      refine (toforallpaths _ _ _ _ x0).
      refine ((weqpath_transport (M_carriers_iso _ Y)) @ _).
      reflexivity.
    }

    (** lemma₂ in HoTT/M-types *)
    assert (lemma2 : transportf F π1eq = F* (pr1 f)).
    {
      refine (!(arr_transport _ _ π1eq) @ _).
      apply maponpaths.
      unfold π1eq, M_carriers_eq.
      refine ((weqpath_transport (M_carriers_iso _ _)) @ _).
      reflexivity.
    }

    refine (_ @ !(maponpaths ψ (lemma1 x))).
    refine (toforallpaths _ (transportf F π1eq) (F* (pr1 f)) lemma2 (θ x) @ _).

    (** Now our goal is simply the condition that f is a coalgebra morphism *)
    apply (toforallpaths _ (F* (pr1 f) ∘ θ) (ψ ∘ pr1 f)).
    exact (pr2 f).
  Defined.

  Lemma isaprop_M : isaprop (M B).
    apply invproofirrelevance.
    intros X Y.
    apply subtypeEquality.
    - exact isaprop_is_final.
    - exact (M_coalg_eq X Y).
  Defined.
End Uniqueness.
