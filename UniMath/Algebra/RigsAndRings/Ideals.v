(** * Ideals

Author: Langston Barrett (@siddharthist)
*)

(** ** Contents

- Definitions
  - Left ideals ([lideal])
  - Right ideals ([rideal])
  - Two-sided ideals ([ideal])
  - The above notions coincide for commutative rigs
- Kernel ideal
- Unit ideal
- Prime ideal
- Localization at a prime ideal
 *)

Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.MoreFoundations.Notations.

Local Open Scope logic.
Local Open Scope ring.
Local Open Scope rig.

Section Definitions.
  Context {R : rig}.

  (** *** Left ideals ([lideal]) *)

  Definition is_lideal (S : subabmonoid (rigaddabmonoid R)) : hProp :=
    ∀ r s : R, S s ⇒ S (r * s).

  Definition lideal : UU := ∑ S : subabmonoid (rigaddabmonoid R), is_lideal S.

  Definition make_lideal :
    ∏ (S : subabmonoid (rigaddabmonoid R)), is_lideal S → lideal := tpair _.

  (** *** Right ideals ([rideal]) *)

  Definition is_rideal (S : subabmonoid (rigaddabmonoid R)) : hProp :=
    ∀ r s : R, S s ⇒ S (s * r).

  Definition rideal : UU := ∑ S : subabmonoid (rigaddabmonoid R), is_rideal S.

  Definition make_rideal :
    ∏ (S : subabmonoid (rigaddabmonoid R)), is_rideal S → rideal := tpair _.

  (** *** Two-sided ideals ([ideal]) *)

  Definition is_ideal (S : subabmonoid (rigaddabmonoid R)) : hProp :=
    hconj (is_lideal S) (is_rideal S).

  Definition ideal : UU := ∑ S : subabmonoid (rigaddabmonoid R), is_ideal S.

  Definition make_ideal (S : subabmonoid (rigaddabmonoid R))
             (isl : is_lideal S) (isr : is_rideal S) : ideal :=
    tpair _ S (make_dirprod isl isr).

  Definition ideal_subabmonoid (I : ideal) : subabmonoid (rigaddabmonoid R) :=
    pr1 I.
  Coercion ideal_subabmonoid : ideal >-> subabmonoid.

  Definition ideal_isl (I : ideal) : is_lideal I := pr12 I.

  Definition ideal_isr (I : ideal) : is_rideal I := pr22 I.
End Definitions.

Arguments lideal _ : clear implicits.
Arguments rideal _ : clear implicits.
Arguments ideal _ : clear implicits.

(** *** The above notions for commutative rigs *)

Lemma commrig_ideals (R : commrig) (S : subabmonoid (rigaddabmonoid  R)) :
  is_lideal S ≃ is_rideal S.
Proof.
  apply weqimplimpl.
  - intros islid r s ss.
    use transportf.
    + exact (S (r * s)).
    + exact (maponpaths S (rigcomm2 _ _ _)).
    + apply (islid r s ss).
  - intros isrid r s ss.
    use transportf.
    + exact (S (s * r)).
    + exact (maponpaths S (rigcomm2 _ _ _)).
    + apply (isrid r s ss).
  - apply propproperty.
  - apply propproperty.
Defined.

Corollary commrig_ideals' (R : commrig) : lideal R ≃ rideal R.
Proof.
  apply weqfibtototal; intro; apply commrig_ideals.
Defined.

(** ** Kernel ideal *)

(** The kernel of a rig homomorphism is a two-sided ideal. *)
Definition kernel_ideal {R S : rig} (f : rigfun R S) : @ideal R.
Proof.
  use make_ideal.
  - use make_submonoid.
    + exact (@monoid_kernel_hsubtype (rigaddabmonoid R) (rigaddabmonoid S)
                                      (rigaddfun f)).
    + (** This does, in fact, describe a submonoid *)
      apply kernel_issubmonoid.
  - (** It's closed under × from the left *)
    intros r s ss; cbn in *.
    refine (monoidfunmul (rigmultfun f) _ _ @ _); cbn.
    refine (maponpaths _ ss @ _).
    refine (rigmultx0 _ (pr1 f r) @ _).
    reflexivity.
  - intros r s ss; cbn in *.
    refine (monoidfunmul (rigmultfun f) _ _ @ _); cbn.
    abstract (rewrite ss; refine (rigmult0x _ (pr1 f r) @ _); reflexivity).
Defined.

(** ** Unit ideal *)

Lemma ideal_rigunel2 {R : rig} (I : ideal R) : I 1 -> forall x, I x.
Proof.
  intros H x.
  apply (transportf (λ x, I x) (rigrunax2 _ x)).
  exact (ideal_isl _ _ _ H).
Qed.

(** ** Prime ideal *)

Section prime.
  Context {R : commring}.

  Definition is_prime (I : ideal R) : hProp :=
    (∀ a b, I (a * b) ⇒ I a ∨ I b) ∧ (¬ I 1).

  Definition prime_ideal : UU := ∑ p : ideal R, is_prime p.

  Definition make_prime_ideal (p : ideal R) (H1 : ∀ a b, p (a * b) ⇒ p a ∨ p b) (H2 : ¬ p 1) :
    prime_ideal := p ,, H1 ,, H2.

  Definition prime_ideal_ideal (p : prime_ideal) : ideal R := pr1 p.
  Coercion prime_ideal_ideal : prime_ideal >-> ideal.

  Definition prime_ideal_ax1 (p : prime_ideal) : ∀ a b, p (a * b) ⇒ p a ∨ p b := pr12 p.

  Definition prime_ideal_ax2 (p : prime_ideal) : ¬ p 1 := pr22 p.
End prime.

Arguments prime_ideal _ : clear implicits.

Section prime_facts.
  Context {R : commring} (p : prime_ideal R).

  Definition prime_ideal_ax1_contraposition :
    ∀ a b : R, ¬ p a ⇒ ¬ p b ⇒ ¬ p (a * b).
  Proof.
    intros a b Ha Hb.
    apply (negf (prime_ideal_ax1 p a b)), toneghdisj.
    exact (make_dirprod Ha Hb).
  Qed.
End prime_facts.

(** ** Localization at a prime ideal *)

Section localization.
  Context {R : commring}.

  Definition prime_ideal_complement (p : prime_ideal R) :
    subabmonoid (ringmultabmonoid R).
  Proof.
    use make_submonoid.
    - intro x. exact (¬ p x).
    - use make_issubmonoid.
      + intros a b.
        exact (prime_ideal_ax1_contraposition _ _ _ (pr2 a) (pr2 b)).
      + exact (prime_ideal_ax2 p).
  Defined.

  Definition localization_at (p : prime_ideal R) : commring :=
    commringfrac _ (prime_ideal_complement p).

  Definition quotient {p : prime_ideal R} (a : R) (b : prime_ideal_complement p) :
    localization_at p := prcommringfrac _ _ a b.
End localization.
