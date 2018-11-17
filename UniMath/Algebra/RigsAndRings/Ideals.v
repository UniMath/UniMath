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
 *)

Require Import UniMath.Algebra.RigsAndRings.

Local Open Scope ring.
Local Open Scope rig.

Section Definitions.
  Context {R : rig}.

  (** *** Left ideals ([lideal]) *)

  Definition is_lideal (S : subabmonoid (rigaddabmonoid R)) : hProp.
  Proof.
    use hProppair.
    - exact (∏ (r : R) (s : R), S s → S (r * s)).
    - do 3 (apply impred; intro).
      apply propproperty.
  Defined.

  Definition lideal : UU := ∑ S : subabmonoid (rigaddabmonoid R), is_lideal S.

  Definition mk_lideal :
    ∏ (S : subabmonoid (rigaddabmonoid R)), is_lideal S → lideal := tpair _.

  (** *** Right ideals ([rideal]) *)

  Definition is_rideal (S : subabmonoid (rigaddabmonoid R)) : hProp.
  Proof.
    use hProppair.
    - exact (∏ (r : R) (s : R), S s → S (s * r)).
    - do 3 (apply impred; intro).
      apply propproperty.
  Defined.

  Definition rideal : UU := ∑ S : subabmonoid (rigaddabmonoid R), is_rideal S.

  Definition mk_rideal :
    ∏ (S : subabmonoid (rigaddabmonoid R)), is_rideal S → rideal := tpair _.

  (** *** Two-sided ideals ([ideal]) *)

  Definition is_ideal (S : subabmonoid (rigaddabmonoid R)) : hProp :=
    hconj (is_lideal S) (is_rideal S).

  Definition ideal : UU := ∑ S : subabmonoid (rigaddabmonoid R), is_ideal S.

  Definition mk_ideal (S : subabmonoid (rigaddabmonoid R))
             (isl : is_lideal S) (isr : is_rideal S) : ideal :=
    tpair _ S (dirprodpair isl isr).
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
  use mk_ideal.
  - use submonoidpair.
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
