(********************************************************************************************

 Properties of regular epimorphisms

 In this file, we establish several properties of regular epimorphisms. More specifically, we
 compare the notion of regular epimorphisms with the following notions:
 - Effective epimorphisms (morphisms that are the coequalizer of their kernel pair)
 - Strong epimorphisms (morphisms with the left lifting property with respect to all
   monomorphisms).
 - Extremal epimorphisms (`f : x --> y` is an extremal epimorphism if for all factorizations
   `f = g · m` with `m` a monomorphism, we have that `m` is an isomorphism).
 We prove these properties under suitable assumptions for the category `C`. More specifically,
 regular epimorphisms coincide with effective epimorphisms if `C` is univalent and has
 pullbacks, and regular epimorphisms coincide with strong and extremal epimorphisms if `C` is
 regular. Note that in order to prove that regular epimorphisms are effective, we need that
 being an effective epimorphism is a proposition. This would be the case if `C` is univalent,
 because that guarantees that the kernel pair is unique.

 Contents
 1. Isomorphisms are regular epimorphisms
 2. Regular epimorphisms versus effective epimorphisms
 3. Regular epimorphisms versus strong epimorphisms
 4. Strong epimorphisms versus extremal epimorphisms
 5. Regular epimorphisms versus extremal epimorphisms

 ********************************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Coequalizers.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Epis.
Require Import UniMath.CategoryTheory.EpiFacts.
Require Import UniMath.CategoryTheory.Monics.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularEpi.
Require Import UniMath.CategoryTheory.RegularAndExact.RegularCategory.

Local Open Scope cat.

(** * 1. Isomorphisms are regular epimorphisms *)
Proposition z_iso_is_regular_epi
            {C : category}
            {x y : C}
            (f : z_iso x y)
  : is_regular_epi f.
Proof.
  use hinhpr.
  refine (y ,, inv_from_z_iso f ,, inv_from_z_iso f ,, idpath _ ,, _).
  intros z h q.
  use iscontraprop1.
  - use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro.
      apply homset_property.
    }
    use (cancel_z_iso' f).
    exact (pr2 φ₁ @ !(pr2 φ₂)).
  - simple refine (_ ,, _).
    + exact (inv_from_z_iso f · h).
    + cbn.
      rewrite !assoc.
      rewrite z_iso_inv_after_z_iso.
      apply id_left.
Qed.

Proposition is_z_isomorphism_is_regular_epi
            {C : category}
            {x y : C}
            (f : x --> y)
            (Hf : is_z_isomorphism f)
  : is_regular_epi f.
Proof.
  exact (z_iso_is_regular_epi (f ,, Hf)).
Qed.

(** * 2. Regular epimorphisms versus effective epimorphisms *)
Section RegularVersusEffective.
  Context {C : category}
          {x y : C}
          (f : x --> y)
          (PB : Pullbacks C).

  Let K : Pullback f f := PB y x x f f.

  Section CoeqKernelPair.
    Context {w : C}
            {g₁ g₂ : w --> x}
            (p : g₁ · f = g₂ · f)
            (H : isCoequalizer g₁ g₂ f p)
            (Coeq := make_Coequalizer g₁ g₂ f p H)
            {a : C}
            {h : x --> a}
            (q : PullbackPr1 K · h = PullbackPr2 K· h).

    Let φ : w --> K := PullbackArrow K _ g₁ g₂ p.
    Let pg₁ : φ · PullbackPr1 K = g₁
      := PullbackArrow_PullbackPr1 K _ g₁ g₂ p.
    Let pg₂ : φ · PullbackPr2 K = g₂
      := PullbackArrow_PullbackPr2 K _ g₁ g₂ p.

    Lemma is_regular_to_isEffective_mor_eq
      : g₁ · h = g₂ · h.
    Proof.
      rewrite <- pg₁, <- pg₂.
      rewrite !assoc'.
      rewrite q.
      apply idpath.
    Qed.

    Proposition is_regular_to_isEffective_unique
      : isaprop (∑ ζ, f · ζ = h).
    Proof.
      use invproofirrelevance.
      intros ζ₁ ζ₂.
      use subtypePath.
      {
        intro.
        apply homset_property.
      }
      use (CoequalizerOutsEq Coeq).
      cbn.
      exact (pr2 ζ₁ @ !(pr2 ζ₂)).
    Qed.

    Definition is_regular_to_isEffective_mor
      : y --> a.
    Proof.
      use (CoequalizerOut Coeq _ h).
      exact is_regular_to_isEffective_mor_eq.
    Defined.

    Proposition is_regular_to_isEffective_comm
      : f · is_regular_to_isEffective_mor = h.
    Proof.
      apply (CoequalizerCommutes Coeq).
    Qed.
  End CoeqKernelPair.

  Definition is_regular_to_isEffective
             (HC : is_univalent C)
             (H : is_regular_epi f)
    : isEffective f.
  Proof.
    revert H.
    use factor_through_squash.
    {
      apply isaprop_isEffective.
      exact HC.
    }
    intros H.
    induction H as ( w & g₁ & g₂ & p & H ).
    pose (Coeq := make_Coequalizer _ _ _ _ H).
    simple refine (_ ,, _).
    - exact (PB _ _ _ f f).
    - intros a h q.
      use iscontraprop1.
      + exact (is_regular_to_isEffective_unique p H).
      + simple refine (_ ,, _).
        * exact (is_regular_to_isEffective_mor p H q).
        * apply is_regular_to_isEffective_comm.
  Qed.

  Definition isEffective_to_is_regular
             (H : isEffective f)
    : is_regular_epi f.
  Proof.
    use hinhpr.
    pose (P := pr1 H : Pullback f f).
    refine (_ ,, _ ,, _ ,, PullbackSqrCommutes P ,, _).
    exact (pr2 H).
  Qed.

  Definition isEffective_weq_is_regular
             (HC : is_univalent C)
    : isEffective f ≃ is_regular_epi f.
  Proof.
    use weqimplimpl.
    - exact isEffective_to_is_regular.
    - exact (is_regular_to_isEffective HC).
    - apply isaprop_isEffective.
      exact HC.
    - apply isaprop_is_regular_epi.
  Defined.
End RegularVersusEffective.

(** * 3. Regular epimorphisms versus strong epimorphisms *)
Definition is_strong_epi
           {C : category}
           {w x : C}
           (e : w --> x)
  : UU
  := ∏ (y z : C)
       (m : y --> z)
       (f : w --> y)
       (g : x --> z)
       (p : e · g = f · m)
       (Hm : isMonic m),
     ∃! (l : x --> y),
     (l · m = g)
     ×
     (e · l = f).

Proposition isaprop_is_strong_epi
            {C : category}
            {w x : C}
            (e : w --> x)
  : isaprop (is_strong_epi e).
Proof.
  do 7 (use impred ; intro).
  apply isapropiscontr.
Qed.

Proposition is_strong_epi_regular_epi
            {C : category}
            {x y : C}
            {e : x --> y}
  : is_regular_epi e → is_strong_epi e.
Proof.
  use factor_through_squash.
  {
    apply isaprop_is_strong_epi.
  }
  intros (w & p₁ & p₂ & p & H) a b m f g q Hm.
  pose (Coeq := make_Coequalizer _ _ _ _ H).
  use iscontraprop1.
  - use invproofirrelevance.
    intros l₁ l₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply homset_property.
    }
    use Hm.
    exact (pr12 l₁ @ !(pr12 l₂)).
  - simple refine (_ ,, _ ,, _).
    + use (CoequalizerOut Coeq).
      * exact f.
      * use Hm.
        rewrite !assoc'.
        rewrite <- !q.
        rewrite !assoc.
        rewrite p.
        apply idpath.
    + use (CoequalizerOutsEq Coeq).
      refine (assoc _ _ _ @ _).
      rewrite CoequalizerCommutes ; cbn.
      exact (!q).
    + cbn.
      use Hm.
      refine (_ @ q).
      refine (assoc' _ _ _ @ _).
      apply maponpaths.
      use (CoequalizerOutsEq Coeq).
      refine (assoc _ _ _ @ _).
      rewrite CoequalizerCommutes ; cbn.
      exact (!q).
Qed.

Section RegularAndStrong.
  Context {C : category}
          (PB : Pullbacks C)
          (EC : coeqs_of_kernel_pair C)
          (HC : regular_epi_pb_stable C)
          {x y : C}
          {e : x --> y}
          (He : is_strong_epi e).

  Let fact := regular_epi_mono_factorization PB EC HC e.
  Let im : C := pr1 fact.
  Let e' : x --> im := pr12 fact.
  Let m : im --> y := pr122 fact.
  Let He' : is_regular_epi e' := pr1 (pr222 fact).
  Let Hm : isMonic m := pr12 (pr222 fact).
  Let p : e = e' · m := pr22 (pr222 fact).

  Local Lemma is_regular_epi_strong_epi_eq
    : e · identity y = e' · m.
  Proof.
    rewrite id_right.
    exact p.
  Qed.

  Let l : y --> im
    := pr11 (He _ _ m e' (identity _) is_regular_epi_strong_epi_eq Hm).
  Let ql : l · m = identity _
    := pr121 (He _ _ m e' (identity _) is_regular_epi_strong_epi_eq Hm).
  Let rl : e · l = e'
    := pr221 (He _ _ m e' (identity _) is_regular_epi_strong_epi_eq Hm).

  Proposition is_regular_epi_strong_epi
    : is_regular_epi e.
  Proof.
    use (is_regular_epi_arrow_z_iso_f _ _ _ _ _ He').
    - apply identity_z_iso.
    - use make_z_iso.
      + exact m.
      + exact l.
      + split.
        * use Hm.
          rewrite !assoc'.
          rewrite ql.
          rewrite id_left, id_right.
          apply idpath.
        * exact ql.
    - simpl.
      rewrite id_left.
      exact (!p).
  Qed.
End RegularAndStrong.

Definition regular_epi_weq_strong_epi
           {C : category}
           (PB : Pullbacks C)
           (EC : coeqs_of_kernel_pair C)
           (HC : regular_epi_pb_stable C)
           {x y : C}
           (e : x --> y)
  : is_strong_epi e ≃ is_regular_epi e.
Proof.
  use weqimplimpl.
  - apply (is_regular_epi_strong_epi PB EC HC).
  - apply is_strong_epi_regular_epi.
  - apply isaprop_is_strong_epi.
  - apply isaprop_is_regular_epi.
Defined.

(** * 4. Strong epimorphisms versus extremal epimorphisms *)
Definition is_extremal_epi
           {C : category}
           {x y : C}
           (e : x --> y)
  : UU
  := ∏ (z : C)
       (f : x --> z)
       (g : z --> y),
     e = f · g
     →
     isMonic g
     →
     is_z_isomorphism g.

Proposition isaprop_is_extremal_epi
            {C : category}
            {x y : C}
            (e : x --> y)
  : isaprop (is_extremal_epi e).
Proof.
  do 5 (use impred ; intro).
  apply isaprop_is_z_isomorphism.
Qed.

Proposition is_extremal_epi_strong_epi
            {C : category}
            {x y : C}
            {e : x --> y}
            (He : is_strong_epi e)
  : is_extremal_epi e.
Proof.
  intros z f g p Hg.
  assert (e · identity y = f · g) as q.
  {
    rewrite id_right.
    exact p.
  }
  pose (fact := He _ _ g f (identity _) q Hg).
  pose (l := pr11 fact).
  pose (r := pr121 fact : l · g = identity _).
  use make_is_z_isomorphism.
  - exact l.
  - split.
    + use Hg.
      rewrite !assoc'.
      rewrite r.
      rewrite id_left, id_right.
      apply idpath.
    + exact r.
Qed.

Section StrongToExtremal.
  Context {C : category}
          (PB : Pullbacks C)
          {w x y z : C}
          (e : w --> x)
          (m : y --> z)
          (f : w --> y)
          (g : x --> z)
          (p : e · g = f · m)
          (He : is_extremal_epi e)
          (Hm : isMonic m).

  Let P : Pullback g m := PB _ _ _ g m.
  Let H : isMonic (PullbackPr1 P) := MonicPullbackisMonic' _ _ (m ,, Hm) P.

  Definition is_strong_epi_extremal_epi_pb_mor
    : w --> P.
  Proof.
    use PullbackArrow.
    - exact e.
    - exact f.
    - exact p.
  Defined.

  Lemma is_strong_epi_extremal_epi_pb_eq
    : e = is_strong_epi_extremal_epi_pb_mor · PullbackPr1 P.
  Proof.
    refine (!_).
    apply PullbackArrow_PullbackPr1.
  Qed.

  Let π : z_iso P x
    := PullbackPr1 P ,, He _ _ _ is_strong_epi_extremal_epi_pb_eq H.

  Definition is_strong_epi_extremal_epi_lift
    : x --> y
    := inv_from_z_iso π · PullbackPr2 P.

  Proposition is_strong_epi_extremal_epi_comm₁
    : is_strong_epi_extremal_epi_lift · m = g.
  Proof.
    unfold is_strong_epi_extremal_epi_lift.
    rewrite !assoc'.
    etrans.
    {
      apply maponpaths.
      exact (!(PullbackSqrCommutes P)).
    }
    rewrite !assoc.
    etrans.
    {
      apply maponpaths_2.
      apply z_iso_after_z_iso_inv.
    }
    apply id_left.
  Qed.

  Proposition is_strong_epi_extremal_epi_comm₂
    : e · is_strong_epi_extremal_epi_lift = f.
  Proof.
    use Hm.
    rewrite !assoc'.
    rewrite is_strong_epi_extremal_epi_comm₁.
    exact p.
  Qed.

  Proposition is_strong_epi_extremal_epi_unique
    : isaprop (∑ l, l · m = g × e · l = f).
  Proof.
    use invproofirrelevance.
    intros l₁ l₂.
    use subtypePath.
    {
      intro.
      apply isapropdirprod ; apply homset_property.
    }
    use Hm.
    exact (pr12 l₁ @ !(pr12 l₂)).
  Qed.
End StrongToExtremal.

Proposition is_strong_epi_extremal_epi
            {C : category}
            (PB : Pullbacks C)
            {w x : C}
            {e : w --> x}
            (He : is_extremal_epi e)
  : is_strong_epi e.
Proof.
  intros y z m f g p Hm.
  use iscontraprop1.
  - apply is_strong_epi_extremal_epi_unique.
    exact Hm.
  - simple refine (_ ,, _ ,, _).
    + exact (is_strong_epi_extremal_epi_lift PB e m f g p He Hm).
    + apply is_strong_epi_extremal_epi_comm₁.
    + apply is_strong_epi_extremal_epi_comm₂.
Defined.

Definition extremal_epi_weq_strong_epi
           {C : category}
           (PB : Pullbacks C)
           {x y : C}
           (e : x --> y)
  : is_extremal_epi e ≃ is_strong_epi e.
Proof.
  use weqimplimpl.
  - apply (is_strong_epi_extremal_epi PB).
  - apply is_extremal_epi_strong_epi.
  - apply isaprop_is_extremal_epi.
  - apply isaprop_is_strong_epi.
Defined.

(** * 5. Regular epimorphisms versus extremal epimorphisms *)
Definition regular_epi_weq_extremal_epi
           {C : category}
           (PB : Pullbacks C)
           (EC : coeqs_of_kernel_pair C)
           (HC : regular_epi_pb_stable C)
           {x y : C}
           (e : x --> y)
  : is_extremal_epi e ≃ is_regular_epi e
  := (regular_epi_weq_strong_epi PB EC HC e ∘ extremal_epi_weq_strong_epi PB e)%weq.
