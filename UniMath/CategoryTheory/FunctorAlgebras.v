(** ****************************************************************

Benedikt Ahrens
started March 2015

Extended by: Anders Mörtberg. October 2015

Rewritten using displayed categories by: Kobe Wullaert. October 2022

*******************************************************************)

(** ***************************************************************

Contents :

- Category of algebras of an endofunctor

- This category is saturated if base precategory is

- Lambek's lemma: if (A,a) is an inital F-algebra then a is an iso

- The natural numbers are initial for X ↦ 1 + X

******************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.initial.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.

Require Import UniMath.CategoryTheory.categories.Dialgebras.

(* The following are used for examples *)
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.NNO.

Local Open Scope cat.

(** ** Category of algebras of an endofunctor *)

Section Algebra_Definition.

  Context {C : category} (F : functor C C).

  Definition algebra_disp_cat_ob_mor : disp_cat_ob_mor C.
  Proof.
    use tpair.
    - exact (λ x, F x --> x).
    - exact (λ x y hx hy f, hx · f = #F f · hy).
  Defined.

  Definition algebra_disp_cat_id_comp
    : disp_cat_id_comp C algebra_disp_cat_ob_mor.
  Proof.
    split.
    - intros x hx ; cbn.
      rewrite !functor_id.
      rewrite id_left, id_right.
      apply idpath.
    - intros x y z f g hx hy hz hf hg ; cbn in *.
      rewrite !functor_comp.
      rewrite !assoc.
      rewrite hf.
      rewrite !assoc'.
      rewrite hg.
      apply idpath.
  Qed.

  Definition algebra_disp_cat_data : disp_cat_data C
    := algebra_disp_cat_ob_mor ,, algebra_disp_cat_id_comp.

  Definition algebra_disp_cat_axioms
    : disp_cat_axioms C algebra_disp_cat_data.
  Proof.
    repeat split ; intros ; try (apply homset_property).
    apply isasetaprop.
    apply homset_property.
  Qed.

  Definition algebra_disp_cat : disp_cat C
    := algebra_disp_cat_data ,, algebra_disp_cat_axioms.

  Definition category_FunctorAlg : category
    := total_category algebra_disp_cat.

  Notation FunctorAlg := category_FunctorAlg.

  Definition algebra_ob : UU := ob FunctorAlg.

  (* this coercion causes confusion, and it is not inserted when parsing most of the time
   thus removing coercion globally
   *)
  Definition alg_carrier (X : algebra_ob) : C := pr1 X.
  Local Coercion alg_carrier : algebra_ob >-> ob.

  Definition alg_map (X : algebra_ob) : F X --> X := pr2 X.

  (** A morphism of an F-algebras (F X, g : F X --> X) and (F Y, h : F Y --> Y)
      is a morphism f : X --> Y such that the following diagram commutes:

    <<
         F f
    F x ----> F y
    |         |
    | g       | h
    V         V
    x ------> y
         f
    >>
   *)
  Definition is_algebra_mor (X Y : algebra_ob) (f : alg_carrier X --> alg_carrier Y) : UU
    := alg_map X · f = #F f · alg_map Y.

  Definition algebra_mor (X Y : algebra_ob) : UU := FunctorAlg⟦X,Y⟧.
  Coercion mor_from_algebra_mor (X Y : algebra_ob) (f : algebra_mor X Y) : C⟦X, Y⟧ := pr1 f.

  Lemma algebra_mor_commutes (X Y : algebra_ob) (f : algebra_mor X Y)
    : alg_map X · f = #F f · alg_map Y.
  Proof.
    exact (pr2 f).
  Qed.

(*Definition algebra_mor_id (X : algebra_ob) : algebra_mor X X.
Proof.
  exists (identity _ ).
  abstract (unfold is_algebra_mor;
            rewrite id_right ;
            rewrite functor_id;
            rewrite id_left;
            apply idpath).
Defined.

Definition algebra_mor_comp (X Y Z : algebra_ob) (f : algebra_mor X Y) (g : algebra_mor Y Z)
  : algebra_mor X Z.
Proof.
  exists (f · g).
  abstract (unfold is_algebra_mor;
            rewrite assoc;
            rewrite algebra_mor_commutes;
            rewrite <- assoc;
            rewrite algebra_mor_commutes;
            rewrite functor_comp, assoc;
            apply idpath).
Defined.

Definition precategory_alg_ob_mor : precategory_ob_mor.
Proof.
  exists algebra_ob.
  exact algebra_mor.
Defined.

Definition precategory_alg_data : precategory_data.
Proof.
  exists precategory_alg_ob_mor.
  exists algebra_mor_id.
  exact algebra_mor_comp.
Defined.*)


End Algebra_Definition.

(* Definition isaset_algebra_mor {C : category} (F : functor C C) (X Y : algebra_ob F) : isaset (algebra_mor F X Y).
Proof.
  apply (isofhleveltotal2 2).
  - apply C.
  - intro f.
    apply isasetaprop.
    apply C.
Qed.*)

Definition algebra_mor_eq {C : category} (F : functor C C) {X Y : algebra_ob F} {f g : algebra_mor F X Y}
  : (f : alg_carrier F X --> alg_carrier F Y) = g ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro a. apply C.
Defined.

(* Lemma is_precategory_precategory_alg_data {C : category} (F : functor C C)
  : is_precategory (precategory_alg_data F).
Proof.
  repeat split; intros; simpl.
  - apply algebra_mor_eq.
    apply id_left.
  - apply algebra_mor_eq.
    apply id_right.
  - apply algebra_mor_eq.
    apply assoc.
  - apply algebra_mor_eq.
    apply assoc'.
Qed.

Definition precategory_FunctorAlg {C : category} (F : functor C C)
  : precategory := tpair _ _ (is_precategory_precategory_alg_data F).

Lemma has_homsets_FunctorAlg {C : category} (F : functor C C)
  : has_homsets (precategory_FunctorAlg F).
Proof.
  intros f g.
  apply isaset_algebra_mor.
Qed.

Definition category_FunctorAlg {C : category} (F : functor C C) : category
  := make_category  (precategory_FunctorAlg F) (has_homsets_FunctorAlg F).

Notation FunctorAlg := category_FunctorAlg.*)


Section fixacategory.

  Context {C : category}
          (F : functor C C).


(** forgetful functor from FunctorAlg to its underlying category *)

(* first step of definition *)
(* Definition forget_algebras_data : functor_data (FunctorAlg F) C.
Proof.
  set (onobs := fun alg : FunctorAlg F => dialgebra_carrier alg).
  apply (make_functor_data onobs).
  intros alg1 alg2 m.
  exact (mor_from_dialgebra_mor m).
Defined. *)

(* the forgetful functor *)
Definition forget_algebras : functor (category_FunctorAlg F) C := pr1_category (algebra_disp_cat F).
(*Proof.
  Check dialgebra_pr1.

  apply (make_functor forget_algebras_data).
  abstract ( split; [intro alg; apply idpath | intros alg1 alg2 alg3 m n; apply idpath] ).
Defined.*)

End fixacategory.


(** ** This category is saturated if the base category is  *)

Section FunctorAlg_saturated.

  Context {C : category}
          (H : is_univalent C)
          (F : functor C C).

  Definition algebra_eq_type (X Y : FunctorAlg F) : UU
    := ∑ p : z_iso (pr1 X) (pr1 Y), is_algebra_mor F X Y p.

Definition algebra_ob_eq (X Y : FunctorAlg F) :
  (X = Y) ≃ algebra_eq_type X Y.
Proof.
  eapply weqcomp.
  - apply total2_paths_equiv.
  - set (H1 := make_weq _ (H (pr1 X) (pr1 Y))).
    apply (weqbandf H1).
    simpl.
    intro p.
    destruct X as [X α].
    destruct Y as [Y β]; simpl in *.
    destruct p.
    rewrite idpath_transportf.
    unfold is_algebra_mor; simpl.
    rewrite functor_id.
    rewrite id_left, id_right.
    apply idweq.
Defined.

Definition is_z_iso_from_is_algebra_iso (X Y : FunctorAlg F) (f : X --> Y)
  : is_z_isomorphism f → is_z_isomorphism (pr1 f).
Proof.
  intro p.
  set (H' := z_iso_inv_after_z_iso (make_z_iso' f p)).
  set (H'':= z_iso_after_z_iso_inv (make_z_iso' f p)).
  exists (pr1 (inv_from_z_iso (make_z_iso' f p))).
  split; simpl.
  - apply (maponpaths pr1 H').
  - apply (maponpaths pr1 H'').
Defined.

Definition inv_algebra_mor_from_is_z_iso {X Y : FunctorAlg F} (f : X --> Y)
  : is_z_isomorphism (pr1 f) → (Y --> X).
Proof.
  intro T.
  set (fiso:=make_z_iso' (pr1 f) T).
  set (finv:=inv_from_z_iso fiso).
  exists finv.
  unfold finv.
  apply pathsinv0.
  apply z_iso_inv_on_left.
  simpl.
  rewrite functor_on_inv_from_z_iso.
  rewrite <- assoc.
  apply pathsinv0.
  apply z_iso_inv_on_right.
  simpl.
  apply (pr2 f).
Defined.

Definition is_algebra_iso_from_is_z_iso {X Y : FunctorAlg F} (f : X --> Y)
  : is_z_isomorphism (pr1 f) → is_z_isomorphism f.
Proof.
  intro T.
  exists (inv_algebra_mor_from_is_z_iso f T).
  split; simpl.
  - apply algebra_mor_eq.
    apply (z_iso_inv_after_z_iso (make_z_iso' (pr1 f) T)).
  - apply algebra_mor_eq.
    apply (z_iso_after_z_iso_inv (make_z_iso' (pr1 f) T)).
Defined.

Definition algebra_iso_first_z_iso {X Y : FunctorAlg F}
  : z_iso X Y ≃ ∑ f : X --> Y, is_z_isomorphism (pr1 f).
Proof.
  apply (weqbandf (idweq _ )).
  unfold idweq. simpl.
  intro f.
  apply weqimplimpl.
  - apply is_z_iso_from_is_algebra_iso.
  - apply is_algebra_iso_from_is_z_iso.
  - apply (isaprop_is_z_isomorphism (C:=FunctorAlg F) f).
  - apply (isaprop_is_z_isomorphism (pr1 f)).
Defined.

Definition swap (A B : UU) : A × B → B × A.
Proof.
  intro ab.
  exists (pr2 ab).
  exact (pr1 ab).
Defined.

Definition swapweq (A B : UU) : (A × B) ≃ (B × A).
Proof.
  exists (swap A B).
  apply (isweq_iso _ (swap B A)).
  - abstract ( intro ab; destruct ab; apply idpath ).
  - abstract ( intro ba; destruct ba; apply idpath ).
Defined.

Definition algebra_z_iso_rearrange {X Y : FunctorAlg F}
  : (∑ f : X --> Y, is_z_isomorphism (pr1 f)) ≃ algebra_eq_type X Y.
Proof.
  eapply weqcomp.
  - apply weqtotal2asstor.
  - simpl. unfold algebra_eq_type.
    apply invweq.
    eapply weqcomp.
    + apply weqtotal2asstor.
    + simpl. apply (weqbandf (idweq _ )).
      unfold idweq. simpl.
      intro f; apply swapweq.
Defined.

Definition algebra_idtoiso (X Y : FunctorAlg F) :
  (X = Y) ≃ z_iso X Y.
Proof.
  eapply weqcomp.
  - apply algebra_ob_eq.
  - eapply weqcomp.
    + apply (invweq (algebra_z_iso_rearrange)).
    + apply (invweq algebra_iso_first_z_iso).
Defined.

Lemma isweq_idtoiso_FunctorAlg (X Y : FunctorAlg F)
  : isweq (@idtoiso _ X Y).
Proof.
  apply (isweqhomot (algebra_idtoiso X Y)).
  - intro p. induction p.
    simpl.
    apply (z_iso_eq(C:=FunctorAlg F)). apply algebra_mor_eq.
    apply idpath.
  - apply (pr2 _ ).
Defined.

Lemma is_univalent_FunctorAlg : is_univalent (FunctorAlg F).
Proof.
  intros X Y.
  apply isweq_idtoiso_FunctorAlg.
Defined.

Lemma idtomor_FunctorAlg_commutes (X Y: FunctorAlg F) (e: X = Y)
  : mor_from_dialgebra_mor (idtomor _ _ e) = idtomor _ _ (maponpaths dialgebra_carrier e).
Proof.
  induction e.
  apply idpath.
Qed.

Corollary idtoiso_FunctorAlg_commutes (X Y: FunctorAlg F) (e: X = Y)
  : mor_from_dialgebra_mor (morphism_from_z_iso _ _ (idtoiso e))
    = idtoiso (maponpaths dialgebra_carrier e).
Proof.
  unfold morphism_from_z_iso.
  rewrite eq_idtoiso_idtomor.
  etrans.
  2: { apply pathsinv0, eq_idtoiso_idtomor. }
  apply idtomor_FunctorAlg_commutes.
Qed.


End FunctorAlg_saturated.

(** ** Lambek's lemma: If (A,a) is an initial F-algebra then a is an iso *)

Section Lambeks_lemma.

Variables (C : category) (F : functor C C).
Variables (Aa : FunctorAlg F) (AaIsInitial : isInitial (FunctorAlg F) Aa).

Local Definition AaInitial : Initial (FunctorAlg F) :=
  make_Initial _ AaIsInitial.

Local Notation A := (dialgebra_carrier Aa).
Local Notation a := (dialgebra_map Aa).

(* (FA,Fa) is an F-algebra *)
Local Definition FAa : FunctorAlg F := tpair (λ X, C ⟦F X,X⟧) (F A) (# F a).
Local Definition Fa' := InitialArrow AaInitial FAa.
Local Definition a' : C⟦A,F A⟧ := mor_from_dialgebra_mor Fa'.
Local Definition Ha' := dialgebra_mor_commutes Fa'.

Lemma initialAlg_is_iso_subproof : is_inverse_in_precat a a'.
Proof.
  assert (Ha'a : a' · a = identity A).
  { assert (algMor_a'a : is_algebra_mor _ _ _ (a' · a)).
    { unfold is_algebra_mor, a'; rewrite functor_comp.
      eapply pathscomp0; [|eapply cancel_postcomposition; apply Ha'].
      apply assoc. }
    apply pathsinv0; set (X := tpair _ _ algMor_a'a).
    apply (maponpaths pr1 (!@InitialEndo_is_identity _ AaInitial X)).
  }
  split; trivial.
  eapply pathscomp0; [apply Ha'|]; cbn.
  rewrite <- functor_comp.
  eapply pathscomp0; [eapply maponpaths; apply Ha'a|].
  apply functor_id.
Qed.

Lemma initialAlg_is_z_iso : is_z_isomorphism a.
Proof.
  exists a'.
  exact initialAlg_is_iso_subproof.
Defined.

End Lambeks_lemma.


(** ** The natural numbers are intial for X ↦ 1 + X *)

(** This can be used as a definition of a natural numbers object (NNO) in
    any category with binary coproducts and a terminal object. We prove
    the universal property of NNOs below. *)

Section Nats.
  Context (C : category).
  Context (bc :  BinCoproducts C).
  Context (hsC :  has_homsets C).
  Context (T : Terminal C).

  Local Notation "1" := T.
  Local Notation "f + g" := (BinCoproductOfArrows _ _ _ f g).
  Local Notation "[ f , g ]" := (BinCoproductArrow _ _ f g).

  Let F : functor C C := BinCoproduct_of_functors _ _ bc
                                                  (constant_functor _ _ 1)
                                                  (functor_identity _).

  (** F on objects: X ↦ 1 + X *)
  Definition F_compute1 : ∏ c : C, F c = BinCoproductObject (bc 1 c) :=
    fun c => (idpath _).

  (** F on arrows: f ↦ [identity 1, f] *)
  Definition F_compute2 {x y : C} : ∏ f : x --> y, # F f = (identity 1) + f :=
    fun c => (idpath _).

  Definition nat_ob : UU := Initial (FunctorAlg F).

  Definition nat_ob_carrier (N : nat_ob) : ob C :=
    alg_carrier _ (InitialObject N).
  Local Coercion nat_ob_carrier : nat_ob >-> ob.

  (** We have an arrow alg_map : (F N = 1 + N) --> N,
      so by the η-rule (UMP) for the coproduct, we can assume that it
      arises from a pair of maps [nat_ob_z,nat_ob_s] by composing with
      coproduct injections.

      <<
                  in1         in2
               1 ----> 1 + N <---- N
               |         |         |
      nat_ob_z |         | alg_map | nat_ob_s
               |         V         |
               +-------> N <-------+
      >>
   *)
  Definition nat_ob_z (N : nat_ob) : (1 --> N) :=
    BinCoproductIn1 (bc 1 (alg_carrier F (pr1 N))) · (alg_map _ (pr1 N)).

  Definition nat_ob_s (N : nat_ob) : (N --> N) :=
    BinCoproductIn2 (bc 1 (alg_carrier F (pr1 N))) · (alg_map _ (pr1 N)).

  Local Notation "0" := (nat_ob_z _).

  (** Use the universal property of the coproduct to make any object with a
      point and an endomorphism into an F-algebra *)
  Definition make_F_alg {X : ob C} (f : 1 --> X) (g : X --> X) : ob (FunctorAlg F).
  Proof.
    refine (X,, _).
    exact (BinCoproductArrow _ f g).
  Defined.

  (** Using make_F_alg, X will be an F-algebra, and by initiality of N, there will
      be a unique morphism of F-algebras N --> X, which can be projected to a
      morphism in C. *)
  Definition nat_ob_rec (N : nat_ob) {X : ob C} :
    ∏ (f : 1 --> X) (g : X --> X), (N --> X) :=
    fun f g => mor_from_algebra_mor _ _ _ (InitialArrow N (make_F_alg f g)).

  (** When calling the recursor on 0, you get the base case.
      Specifically,

        nat_ob_z · nat_ob_rec = f
   *)
  Lemma nat_ob_rec_z (N : nat_ob) {X : ob C} :
    ∏ (f : 1 --> X) (g : X --> X), nat_ob_z N · nat_ob_rec N f g = f.
  Proof.
    intros f g.

    pose (inlN := BinCoproductIn1 (bc 1 N)).
    pose (succ := nat_ob_s N).

    (** By initiality of N, there is a unique morphism making the following
        diagram commute:

        <<
               inlN         identity 1 + nat_ob_rec
            1 -----> 1 + N -------------------------> 1 + X
                       |                                |
             alg_map N |                                | alg_map X
                       V                                V
                       N   -------------------------->  X
                                   nat_ob_rec
        >>

        This proof uses somewhat idiosyncratic "forward reasoning", transforming
        the term "diagram" rather than the goal.
     *)
    pose
      (diagram :=
         maponpaths
           (fun x => inlN · x)
           (algebra_mor_commutes F (pr1 N) _ (InitialArrow N (make_F_alg f g)))).
    rewrite (F_compute2 _) in diagram.

    (** Using the η-rules for coproducts, we can assume that alg_map X = [f,g]
        for f : 1 --> X, g : X --> X. *)
    rewrite (BinCoproductArrowEta C 1 X (bc _ _) _ _) in diagram.

    (** Using the β-rules for coproducts, we can simplify some of the terms *)
    (** (identity 1 + _) · [f, g] --β--> [identity 1 · f, _ · g] *)
    rewrite (precompWithBinCoproductArrow C (bc 1 N) (bc 1 X)
                                          (identity 1) _ _ _) in diagram.

    (** inl · [identity 1 · f, _ · g] --β--> identity 1 · f *)
    rewrite (BinCoproductIn1Commutes C 1 N (bc 1 _) _ _ _) in diagram.

    (** We can dispense with the identity *)
    rewrite (id_left _) in diagram.

    rewrite assoc in diagram.
    rewrite (BinCoproductArrowEta C 1 N (bc _ _) _ _) in diagram.

    refine (_ @ (BinCoproductIn1Commutes C _ _ (bc 1 _) _ f g)).
    rewrite (!BinCoproductIn1Commutes C _ _ (bc 1 _) _ 0 succ).
    unfold nat_ob_rec in *.
    exact diagram.
  Defined.

  Opaque nat_ob_rec_z.

  (** The succesor case:

        nat_ob_s · nat_ob_rec = nat_ob_rec · g

      The proof is very similar.
   *)
  Lemma nat_ob_rec_s (N : nat_ob) {X : ob C} :
    ∏ (f : 1 --> X) (g : X --> X),
    nat_ob_s N · nat_ob_rec N f g = nat_ob_rec N f g · g.
  Proof.
    intros f g.

    pose (inrN := BinCoproductIn2 (bc 1 N)).
    pose (succ := nat_ob_s N).

    (** By initiality of N, there is a unique morphism making the same diagram
        commute as above, but with "inrN" in place of "inlN". *)
    pose
      (diagram :=
         maponpaths
           (fun x => inrN · x)
           (algebra_mor_commutes F (pr1 N) _ (InitialArrow N (make_F_alg f g)))).
    rewrite (F_compute2 _) in diagram.

    rewrite (BinCoproductArrowEta C 1 X (bc _ _) _ _) in diagram.

    (** Using the β-rules for coproducts, we can simplify some of the terms *)
    (** (identity 1 + _) · [f, g] --β--> [identity 1 · f, _ · g] *)
    rewrite (precompWithBinCoproductArrow C (bc 1 N) (bc 1 X)
                                          (identity 1) _ _ _) in diagram.

    (** inl · [identity 1 · f, _ · g] --β--> identity 1 · f *)
    rewrite (BinCoproductIn2Commutes C 1 N (bc 1 _) _ _ _) in diagram.

    rewrite assoc in diagram.
    rewrite (BinCoproductArrowEta C 1 N (bc _ _) _ _) in diagram.

    refine
      (_ @ maponpaths (fun x => nat_ob_rec N f g · x)
         (BinCoproductIn2Commutes C _ _ (bc 1 _) _ f g)).
    rewrite (!BinCoproductIn2Commutes C _ _ (bc 1 _) _ 0 (nat_ob_s N)).
    unfold nat_ob_rec in *.
    exact diagram.
  Defined.

  Opaque nat_ob_rec_s.

End Nats.

(** nat_ob implies NNO *)
Lemma nat_ob_NNO {C : category} (BC : BinCoproducts C) (hsC : has_homsets C) (TC : Terminal C) :
  nat_ob _ BC TC → NNO TC.
Proof.
intros N.
use make_NNO.
- exact (nat_ob_carrier _ _ _  N).
- apply nat_ob_z.
- apply nat_ob_s.
- intros n z s.
  use unique_exists.
  + apply (nat_ob_rec _ _ _ _ z s).
  + split; [ apply nat_ob_rec_z | apply nat_ob_rec_s ].
  + intros x; apply isapropdirprod; apply hsC.
  + intros x [H1 H2].
    transparent assert (xalg : (FunctorAlg (BinCoproduct_of_functors C C BC
                                              (constant_functor C C TC)
                                              (functor_identity C))
                                              ⟦ InitialObject N, make_F_alg C BC TC z s ⟧)).
    { refine (x,,_).
      abstract (apply pathsinv0; etrans; [apply precompWithBinCoproductArrow |];
                rewrite id_left, <- H1;
                etrans; [eapply maponpaths, pathsinv0, H2|];
                now apply pathsinv0, BinCoproductArrowUnique; rewrite assoc;
                apply maponpaths).
    }
    exact (maponpaths pr1 (InitialArrowUnique N (make_F_alg C BC TC z s) xalg)).
Defined.
