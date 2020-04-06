Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.Algebra.Universal.

Section dispcat.

  Context (sigma : signature).

  Definition disp_alg :disp_cat SET.
  Proof.
    use disp_struct.
    - exact (λ A:hSet, ∏ (nm : names sigma),  Vector A (arity nm) → A).
    - cbn. intros. exact (@ishom sigma (make_algebra x X) (make_algebra y X0) X1).
    - cbn. intros A B opA opB f prpt1 prpt2.
      use iscontraprop1.
      + assert (T : isaset (@ishom sigma (make_algebra A opA)(make_algebra B opB) f)).
        { apply isasetaprop. use isaprop_ishom.
        }
        apply T.
      + apply isaprop_ishom.
    - cbn. intros. apply ishomidfun.
    - cbn. intros A B C opA opB opC. intros f g ishomf ishomg.
      exact (ishomcomp (make_hom ishomf) (make_hom ishomg)).
  Defined.

  Lemma is_univalent_disp_alg : is_univalent_disp disp_alg.
  Proof.
    use is_univalent_disp_from_SIP_data.
    - intro A. cbn. use impred_isaset. intro nm. cbn.
      use isaset_set_fun_space.
    - cbn. intros A op1 op2 ishomid1 ishomid2. use funextsec. intro nm. use funextfun. intro vec.
      unfold ishom in *. cbn in *. set (H1:= ishomid1 nm vec). rewrite vector_map_id in H1.
      apply H1.
  Qed.

  Definition alg_tot_cat : category := total_category disp_alg.

  Lemma is_univalent_alg_tot_cat : is_univalent alg_tot_cat.
  Proof.
    exact (@is_univalent_total_category SET disp_alg (is_univalent_HSET) is_univalent_disp_alg).
  Defined.

  End dispcat.
