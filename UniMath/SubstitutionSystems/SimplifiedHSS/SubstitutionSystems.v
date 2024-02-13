
(** **********************************************************

Benedikt Ahrens, Ralph Matthes

SubstitutionSystems

2015


************************************************************)


(** **********************************************************

Contents :

-    Definition of heterogeneous substitution systems
-    Various lemmas about the substitution ("bracket") operation
-    Definition of precategory of substitution systems


simplified notion of HSS by Ralph Matthes (2022, 2023)
the file is very close to the homonymous file in the parent directory
basically, the changes start with [bracket_property] and are then propagated throughout

************************************************************)


Require Import UniMath.Foundations.PartD.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.FunctorCategory.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.PointedFunctors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.PointedFunctorsComposition.
Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.Notation.
Local Open Scope subsys.

Section fix_a_category.

(** ** Some variables and assumptions *)


Context (C : category) (CP : BinCoproducts C).

Local Notation "'EndC'":= ([C, C]) .
Let CPEndC : BinCoproducts EndC := BinCoproducts_functor_precat _ _ CP.

(** The category of pointed endofunctors on [C] *)
Local Notation "'Ptd'" := (category_Ptd C).
(** The category of endofunctors on [C] *)
Local Notation "'EndC'":= ([C, C]) .

(** preparations for the definition of hss based on a functor [H] *)
Section prep_hss.

Context (H : functor [C, C] [C, C]).

Definition Id_H
: functor EndC EndC
  := BinCoproduct_of_functors _ _ CPEndC
                       (constant_functor _ _ (functor_identity _ : EndC))
                       H.

(* An Id_H algebra is a pointed functor *)

Definition eta_from_alg (T : algebra_ob Id_H) : EndC ⟦ functor_identity _,  `T ⟧.
Proof.
  exact (BinCoproductIn1 (CPEndC _ _) · alg_map _ T).
Defined.

Local Notation η := eta_from_alg.

Definition ptd_from_alg (T : algebra_ob Id_H) : Ptd.
Proof.
  exists (pr1 T).
  exact (η T).
Defined.

Definition tau_from_alg (T : algebra_ob Id_H) : EndC ⟦H `T, `T⟧.
Proof.
  exact (BinCoproductIn2 (CPEndC _ _) · alg_map _ T).
Defined.
Local Notation τ := tau_from_alg.

(*
Coercion functor_from_algebra_ob (X : algebra_ob _ Id_H) : functor C C  := pr1 X.
*)

Local Notation "f ⊕ g" := (BinCoproductOfArrows _ (CPEndC _ _ ) (CPEndC _ _ ) f g).

(** analysis of the "bracket operation" individually for each pointed functor *)
Section fix_a_pointed_functor.

  Context {Z: Ptd}.
  Context (θ : @PrestrengthForSignatureAtPoint C C C H Z).


Definition bracket_property (T : algebra_ob Id_H) (f : U Z --> `T)
           (h : `T • (U Z)  --> `T) : UU
  :=
    alg_map _ T •• (U Z) · h =
          (identity (U Z) ⊕ θ `T) ·
          (identity (U Z) ⊕ #H h) ·
          (BinCoproductArrow  (CPEndC _ _ ) f (tau_from_alg T)).

Definition bracket_at (T : algebra_ob Id_H) (f : U Z --> `T): UU :=
  ∃! h : `T • (U Z)  --> `T, bracket_property T f h.


Definition bracket_property_parts (T : algebra_ob Id_H) (f : U Z --> `T)
           (h : `T • (U Z)  --> `T) : UU
  :=
    (f = η T •• (U Z) · h) ×
     (θ `T · #H h · τ T  = τ T •• (U Z) ·  h).

Definition bracket_parts_at (T : algebra_ob Id_H) (f : U Z --> `T) : UU :=
   ∃! h : `T • (U Z)  --> `T, bracket_property_parts T f h.

(* show that for any h of suitable type, the following are equivalent *)

Lemma parts_from_whole (T : algebra_ob Id_H) (f : U Z --> `T)
      (h :  `T • (U Z)  --> `T) :
  bracket_property T f h → bracket_property_parts T f h.
Proof.
  intro Hyp.
  split.
  + unfold eta_from_alg.
    apply nat_trans_eq_alt.
    intro c.
    simpl.
    unfold coproduct_nat_trans_in1_data.
    assert (Hyp_inst := nat_trans_eq_pointwise Hyp c); clear Hyp.
    apply (maponpaths (λ m, BinCoproductIn1 (CP _ _)· m)) in Hyp_inst.
    match goal with |[ H1 : _  = ?f |- _ = _   ] =>
         intermediate_path (f) end.
    * clear Hyp_inst.
      rewrite <- assoc.
      apply BinCoproductIn1Commutes_right_in_ctx_dir.
      rewrite id_left.
      apply BinCoproductIn1Commutes_right_in_ctx_dir.
      rewrite id_left.
      apply BinCoproductIn1Commutes_right_dir.
      apply idpath.
    * rewrite <- Hyp_inst; clear Hyp_inst.
      rewrite <- assoc.
      apply idpath.
  + unfold tau_from_alg.
    apply nat_trans_eq_alt.
    intro c.
    simpl.
    unfold coproduct_nat_trans_in2_data.
    assert (Hyp_inst := nat_trans_eq_pointwise Hyp c); clear Hyp.
    apply (maponpaths (λ m,  BinCoproductIn2 (CP _ _)· m)) in Hyp_inst.
    match goal with |[ H1 : _  = ?f |- _ = _   ] =>
         intermediate_path (f) end.
    * clear Hyp_inst.
      do 2 rewrite <- assoc.
      apply BinCoproductIn2Commutes_right_in_ctx_dir.
      simpl.
      rewrite <- assoc.
      apply maponpaths.
      apply BinCoproductIn2Commutes_right_in_ctx_dir.
      simpl.
      rewrite <- assoc.
      apply maponpaths.
      unfold tau_from_alg.
      apply BinCoproductIn2Commutes_right_dir.
      apply idpath.
    * rewrite <- Hyp_inst; clear Hyp_inst.
      rewrite <- assoc.
      apply idpath.
Qed.

Lemma whole_from_parts (T : algebra_ob Id_H) (f : U Z --> `T)
      (h :  `T • (U Z)  --> `T) :
  bracket_property_parts T f h → bracket_property T f h.
Proof.
  intros [Hyp1 Hyp2].
  apply nat_trans_eq_alt.
  intro c.
  apply BinCoproductArrow_eq_cor.
  + clear Hyp2.
    assert (Hyp1_inst := nat_trans_eq_pointwise Hyp1 c); clear Hyp1.
    rewrite <- assoc.
    apply BinCoproductIn1Commutes_right_in_ctx_dir.
    rewrite id_left.
    apply BinCoproductIn1Commutes_right_in_ctx_dir.
    rewrite id_left.
    apply BinCoproductIn1Commutes_right_dir.
    simpl. simpl in Hyp1_inst.
    rewrite Hyp1_inst.
    simpl.
    apply assoc.
  + clear Hyp1.
    assert (Hyp2_inst := nat_trans_eq_pointwise Hyp2 c); clear Hyp2.
    rewrite <- assoc.
    apply BinCoproductIn2Commutes_right_in_ctx_dir.
    simpl.
    rewrite assoc.
    eapply pathscomp0.
    * eapply pathsinv0.
      exact Hyp2_inst.
    * clear Hyp2_inst.
      simpl.
      do 2 rewrite <- assoc.
      apply maponpaths.
      apply BinCoproductIn2Commutes_right_in_ctx_dir.
      simpl.
      rewrite <- assoc.
      apply maponpaths.
      apply BinCoproductIn2Commutes_right_dir.
      apply idpath.
Qed.


(* show bracket_parts_point is logically equivalent to bracket_point, then
   use it to show that bracket_parts is equivalent to bracket using [weqonsecfibers:
  ∏ (X : UU) (P Q : X → UU),
  (∏ x : X, P x ≃ Q x) → (∏ x : X, P x) ≃ (∏ x : X, Q x)] *)

End fix_a_pointed_functor.

Section instantiate_with_identity.

    Context (T : algebra_ob Id_H).
    Context (θ : @PrestrengthForSignatureAtPoint C C C H (ptd_from_alg T)).

Definition bracket_property_parts_identity_nicer (h : `T • `T  --> `T) : UU
  := (identity `T = η T •• `T · h) × (θ `T · #H h · τ T  = τ T •• `T ·  h).

Lemma bracket_property_parts_identity_nicer_impl1 (h : `T • `T  --> `T):
  bracket_property_parts θ T (identity _) h -> bracket_property_parts_identity_nicer h.
Proof.
  intro Hyp. induction Hyp as [Hyp1 Hyp2].
  split.
  - etrans.
    2: { exact Hyp1. }
    apply nat_trans_eq_alt.
    intro c.
    apply idpath.
  - etrans.
    { exact Hyp2. }
    apply idpath.
Qed.

(** basically the same proof *)
Lemma bracket_property_parts_identity_nicer_impl2 (h : `T • `T  --> `T):
  bracket_property_parts_identity_nicer h -> bracket_property_parts θ T (identity _) h.
  intro Hyp. induction Hyp as [Hyp1 Hyp2].
  split.
  - etrans.
    2: { exact Hyp1. }
    apply nat_trans_eq_alt.
    intro c.
    apply idpath.
  - etrans.
    { exact Hyp2. }
    apply idpath.
Qed.

End instantiate_with_identity.

(** the notion one would be looking for: an algebra and a substitution operation that does lookup on
variables and behaves homomorphically elsewhere, as instructed by the pre-strength at that point *)
Definition heterogeneous_substitution : UU := ∑ (T: algebra_ob Id_H),
  ∑ (θ : @PrestrengthForSignatureAtPoint C C C H (ptd_from_alg T)), bracket_at θ T (identity _).

Coercion alg_from_hetsubst (T : heterogeneous_substitution) : algebra_ob Id_H := pr1 T.
Definition θ_from_hetsubst (T : heterogeneous_substitution) : @PrestrengthForSignatureAtPoint C C C H (ptd_from_alg T)
  := pr1 (pr2 T).

(** we write prejoin as a warning that the monad laws are not necessarily fulfilled *)
Definition prejoin_from_hetsubst (T : heterogeneous_substitution) : `T • `T --> `T
  := pr1 (pr1 (pr2 (pr2 T))).

Lemma prejoin_from_hetsubst_η (T : heterogeneous_substitution) :
  identity `T = η T •• `T · (prejoin_from_hetsubst T).
Proof.
  refine (pr1 (bracket_property_parts_identity_nicer_impl1 T (θ_from_hetsubst T) _ _)).
  apply parts_from_whole.
  exact (pr2 (pr1 (pr2 (pr2 T)))).
Qed.

Lemma prejoin_from_hetsubst_τ (T : heterogeneous_substitution) :
  θ_from_hetsubst T `T · #H (prejoin_from_hetsubst T) · τ T  = τ T •• `T ·  (prejoin_from_hetsubst T).
Proof.
  refine (pr2 (bracket_property_parts_identity_nicer_impl1 T (θ_from_hetsubst T) _ _)).
  apply parts_from_whole.
  exact (pr2 (pr1 (pr2 (pr2 T)))).
Qed.

Section fix_a_prestrength.

  Context (θ :  @PrestrengthForSignature C C C H).

Definition bracket (T : algebra_ob Id_H) : UU
  := ∏ (Z : Ptd) (f : U Z --> `T), bracket_at (nat_trans_fix_snd_arg _ _ _ _ _ θ Z) T f.

Lemma isaprop_bracket (T : algebra_ob Id_H) : isaprop (bracket T).
Proof.
  apply impred_isaprop; intro Z.
  apply impred_isaprop; intro f.
  apply isapropiscontr.
Qed.

Definition bracket_parts (T : algebra_ob Id_H) : UU
  := ∏ (Z : Ptd) (f : U Z --> `T), bracket_parts_at (nat_trans_fix_snd_arg _ _ _ _ _ θ Z) T f.

End fix_a_prestrength.

End prep_hss.

Arguments ptd_from_alg {_} _ .
Arguments prejoin_from_hetsubst {_} _ .
Arguments prejoin_from_hetsubst_η {_} _ .
Arguments prejoin_from_hetsubst_τ {_} _ .
Arguments bracket_parts {_} _ _ .

  Section def_hss.

  Context (H : Presignature C C C).

  Local Notation η := (eta_from_alg H).
  Local Notation τ := (tau_from_alg H).

  Let θ : PrestrengthForSignature H := theta H.
  Let Id_H := Id_H H.

(** the notion of a heterogeneous substitution system that asks for more operations to uniquely exist *)
Definition hss : UU := ∑ (T: algebra_ob Id_H), bracket H θ T.

Coercion hetsubst_from_hss (T : hss) : heterogeneous_substitution H.
Proof.
  exists (pr1 T).
  use tpair.
  - apply (nat_trans_fix_snd_arg _ _ _ _ _ θ).
  - apply (pr2 T).
Defined.

Definition fbracket (T : hss) (Z : Ptd) (f : U Z --> `T)
  : `T • (U Z) --> `T
  := pr1 (pr1 (pr2 T Z f)).

Notation "⦃ f ⦄_{ Z }" := (fbracket _ Z f)(at level 0).

(** The bracket operation [fbracket] is unique *)

Definition fbracket_unique_pointwise (T : hss) {Z : Ptd} (f : U Z --> `T)
  : ∏ (α : functor_composite (U Z) `T ⟹ pr1 `T),
     (∏ c : C, pr1 f c = pr1 (η T) (pr1 (U Z) c) · α c) →
     (∏ c : C, pr1 (θ (`T ⊗ Z))  c · pr1 (#H α) c · pr1 (τ T) c =
        pr1 (τ T) (pr1 (U Z) c) · α c)
     →
     α = ⦃f⦄_{Z}.
Proof.
  intros α H1 H2.
  apply path_to_ctr.
  apply whole_from_parts.
  split.
  - apply nat_trans_eq_alt; assumption.
  - apply nat_trans_eq_alt; assumption.
Qed.

Definition fbracket_unique (T : hss) {Z : Ptd} (f : U Z --> `T)
: ∏ α : (*functor_composite (C:=C)*) `T • (U Z)  --> `T,
    bracket_property_parts H (nat_trans_fix_snd_arg _ _ _ _ _ θ Z) T f α
   →
   α = ⦃f⦄_{Z}.
Proof.
  intros α [H1 H2].
  apply path_to_ctr.
  apply whole_from_parts.
  split;  assumption.
Qed.

Definition fbracket_unique_target_pointwise (T : hss) {Z : Ptd} (f : U Z --> `T)
  : ∏ α : `T • U Z --> `T,
        bracket_property_parts H (nat_trans_fix_snd_arg _ _ _ _ _ θ Z) T f α
   →
   ∏ c, pr1 α c =  pr1 ⦃f⦄_{Z} c.
Proof.
  intros α H12.
  set (t:= fbracket_unique _ _ α H12).
  apply (nat_trans_eq_weq (homset_property C) _ _ t).
Qed.

(** Properties of [fbracket] by definition: commutative diagrams *)

Lemma fbracket_η (T : hss) : ∏ {Z : Ptd} (f : U Z --> `T),
   f = η T •• U Z · ⦃f⦄_{Z}.
Proof.
  intros Z f.
  (* assert (H' := parts_from_whole T Z f (fbracket _ f)) . *)
  exact (pr1 (parts_from_whole _ _ _ _ _ (pr2 (pr1 (pr2 T Z f))))).
Qed.

Lemma fbracket_τ (T : hss) : ∏ {Z : Ptd} (f : U Z --> `T),
    θ (`T ⊗ Z) · #H ⦃f⦄_{Z} · τ T
    =
    τ T •• U Z · ⦃f⦄_{Z}.
Proof.
  intros Z f.
  exact (pr2 (parts_from_whole _ _ _ _ _ (pr2 (pr1 (pr2 T Z f))))).
Qed.

(** [fbracket] is also natural *)

Lemma fbracket_natural (T : hss) {Z Z' : Ptd} (f : Z --> Z') (g : U Z' --> `T)
:  (`T ∘ #U f : EndC⟦ `T • U Z , `T • U Z' ⟧) · ⦃g⦄_{Z'} = ⦃#U f · g⦄_{Z}.
Proof.
  apply fbracket_unique_pointwise.
  - simpl. intro c.
    rewrite assoc.
    pose proof (nat_trans_ax (η T)) as H'.
    simpl in H'.
    rewrite <- H'; clear H'.
    rewrite <- assoc.
    apply maponpaths.
    pose proof (nat_trans_eq_weq (homset_property C) _ _  (fbracket_η T g)) as X.
    simpl in X. exact (X _ ).
  - intro c; simpl.
    assert (H':=nat_trans_ax (τ T)).
    simpl in H'.
    eapply pathscomp0. 2: apply assoc'.
    eapply pathscomp0.
    2: { apply cancel_postcomposition. apply H'. }
    clear H'.
    set (H':=fbracket_τ T g).
    simpl in H'.
    assert (X:= nat_trans_eq_pointwise H' c).
    simpl in X.
    rewrite  <- assoc.
    rewrite  <- assoc.
    transitivity (  # (pr1 (H ((`T)))) (pr1 f c) ·
                     (pr1 (θ ((`T) ⊗ Z')) c)· pr1 (# H ⦃g⦄_{Z'}) c· pr1 (τ T) c).
    2: { rewrite <- assoc.
         rewrite <- assoc.
         apply maponpaths.
         repeat rewrite assoc.
         apply X.
    }
    clear X.
    set (A:=θ_nat_2_pointwise).
    simpl in *.
    set (A':= A C C C H θ (`T) Z Z').
    simpl in A'.
    set (A2:= A' f).
    clearbody A2; clear A'; clear A.
    rewrite A2; clear A2.
    repeat rewrite <- assoc.
    apply maponpaths.
    simpl.
    repeat rewrite assoc.
    apply cancel_postcomposition.
    rewrite (functor_comp H).
    apply cancel_postcomposition.
    clear H'.
    set (A:=horcomp_id_postwhisker C C C).
    rewrite A; try apply homset_property.
    apply idpath.
Qed.

(** As a consequence of naturality, we can compute [fbracket f] from [fbracket identity] *)

Lemma compute_fbracket (T : hss) : ∏ {Z : Ptd} (f : Z --> ptd_from_alg T),
    ⦃#U f⦄_{Z} = (`T ∘ # U f : EndC⟦`T • U Z , `T • U (ptd_from_alg T)⟧) · ⦃identity (U (ptd_from_alg T))⦄_{ptd_from_alg T}.
Proof.
  intros Z f.
  assert (A : f = f · identity _ ).
  { rewrite id_right; apply idpath. }
  rewrite A.
  rewrite functor_comp.
  rewrite <- fbracket_natural.
  rewrite id_right.
  apply idpath.
Qed.

Section from_identity_to_hss.
(** the operations of an hss can be obtained through this formula from
    just a heterogeneous substitution *)

  Context (T : algebra_ob Id_H).
  Context (prejoin : bracket_at H (nat_trans_fix_snd_arg _ _ _ _ _ θ (ptd_from_alg T)) T (identity _)).

  Let T0 : heterogeneous_substitution H :=
    T ,, (nat_trans_fix_snd_arg _ _ _ _ _ θ (ptd_from_alg T) ,, prejoin).

Lemma heterogeneous_substitution_into_bracket {Z : Ptd} (f : Z --> ptd_from_alg T0) :
  bracket_property H (nat_trans_fix_snd_arg _ _ _ _ _ θ Z) T0 (#U f)
    ((` T0 ∘ #U f : EndC ⟦ `T0 • U Z , `T0 • U (ptd_from_alg T0) ⟧) · prejoin_from_hetsubst T0).
Proof.
  apply whole_from_parts.
  split.
  - apply nat_trans_eq_alt.
    intro c.
    induction f as [f pt].
    simpl.
    assert (alg_map_nat := nat_trans_ax (alg_map Id_H T0) _ _ (pr1 f c)).
    etrans.
    2: { rewrite <- assoc. apply maponpaths. rewrite assoc.
         apply cancel_postcomposition.
         exact alg_map_nat.
    }
    clear alg_map_nat.
    etrans.
    2: { do 2 rewrite assoc. do 2 apply cancel_postcomposition.
         apply pathsinv0. unfold Id_H. simpl. apply BinCoproductIn1Commutes. }
    simpl.
    etrans.
    { apply pathsinv0.
      apply id_right.
    }
    do 2 rewrite <- assoc.
    apply maponpaths.
    rewrite assoc.
    assert (prejoin_ok := prejoin_from_hetsubst_η T0).
    apply (maponpaths pr1) in prejoin_ok.
    apply toforallpaths in prejoin_ok.
    apply prejoin_ok.
  - rewrite functor_comp.
    apply nat_trans_eq_alt.
    intro c.
    induction f as [f pt].
    simpl.
    assert (alg_map_nat := nat_trans_ax (alg_map Id_H T0) _ _ (pr1 f c)).
    etrans.
    2: { rewrite <- assoc. apply maponpaths. rewrite assoc.
         apply cancel_postcomposition.
         exact alg_map_nat.
    }
    etrans.
    2: { do 2 rewrite assoc. do 2 apply cancel_postcomposition.
         apply pathsinv0. unfold Id_H. simpl. apply BinCoproductIn2Commutes. }
    assert (prejoin_ok := prejoin_from_hetsubst_τ T0).
    apply (maponpaths pr1) in prejoin_ok.
    apply toforallpaths in prejoin_ok.
    assert (prejoin_ok_inst := prejoin_ok c).
    simpl in prejoin_ok_inst.
    etrans.
    { repeat rewrite assoc. do 3 apply cancel_postcomposition.
      apply pathsinv0.
      assert (theta_nat_2 := θ_nat_2_pointwise _ _ _ H θ `T0 _ _ (f,,pt) c).
      rewrite horcomp_id_postwhisker in theta_nat_2; try apply homset_property.
      apply theta_nat_2.
    }
    etrans.
    { repeat rewrite <- assoc. apply maponpaths.
      rewrite assoc.
      exact prejoin_ok_inst.
    }
    clear prejoin_ok prejoin_ok_inst.
    repeat rewrite assoc.
    apply idpath.
Qed.

End from_identity_to_hss.

(** ** Morphisms of heterogeneous substitution systems *)


(** A morphism [f] of pointed functors is an algebra morphism when... *)
(*
Definition isAlgMor {T T' : Alg} (f : T --> T') : UU :=
  #H (# U f) · τ T' = compose (C:=EndC) (τ T) (#U f).

Lemma isaprop_isAlgMor (T T' : Alg) (f : T --> T') : isaprop (isAlgMor f).
Proof.
  apply isaset_nat_trans.
  apply hs.
Qed.
*)

(** a little preparation for much later *)
Lemma τ_part_of_alg_mor  (T T' : @algebra_ob [C, C] Id_H)
  (β : @algebra_mor [C, C] Id_H T T'): #H β · τ T' = compose (C:=EndC) (τ T) β.
Proof.
  assert (β_is_alg_mor := pr2 β).
  simpl in β_is_alg_mor.
  assert (β_is_alg_mor_inst := maponpaths (fun m:EndC⟦_,_⟧ => (BinCoproductIn2 (CPEndC _ _))· m)
                                          β_is_alg_mor); clear β_is_alg_mor.
  simpl in β_is_alg_mor_inst.
  apply nat_trans_eq_alt.
  intro c.
  assert (β_is_alg_mor_inst':= nat_trans_eq_pointwise β_is_alg_mor_inst c); clear β_is_alg_mor_inst.
  simpl in β_is_alg_mor_inst'.
  rewrite assoc in β_is_alg_mor_inst'.
  eapply pathscomp0.
  2: { eapply pathsinv0.
       exact β_is_alg_mor_inst'. }
  clear β_is_alg_mor_inst'.
  apply BinCoproductIn2Commutes_right_in_ctx_dir.
  simpl.
  rewrite <- assoc.
  apply idpath.
Qed.


(** A morphism [β] of pointed functors is a bracket morphism when... *)

Lemma is_ptd_mor_alg_mor (T T' : @algebra_ob [C, C] Id_H)
  (β : @algebra_mor [C, C] Id_H T T') :
  @is_ptd_mor C (ptd_from_alg T) (ptd_from_alg T') (pr1 β).
Proof.
  simpl.
  unfold is_ptd_mor. simpl.
  intro c.
  rewrite <- assoc.
  assert (X:=pr2 β).
  assert (X':= nat_trans_eq_pointwise X c).
  simpl in *.
  etrans. { apply maponpaths. apply X'. }
  unfold coproduct_nat_trans_in1_data.
  repeat rewrite assoc.
  unfold coproduct_nat_trans_data.
  etrans.
  { apply cancel_postcomposition.
    apply BinCoproductIn1Commutes. }
  simpl.
  repeat rewrite <- assoc.
  apply id_left.
Qed.

Definition ptd_from_alg_mor {T T' : algebra_ob Id_H} (β : algebra_mor _ T T')
: ptd_from_alg T --> ptd_from_alg T'.
Proof.
  exists (pr1 β).
  apply is_ptd_mor_alg_mor.
Defined.

(** show functor laws for [ptd_from_alg] and [ptd_from_alg_mor] *)

Definition ptd_from_alg_functor_data : functor_data (category_FunctorAlg Id_H) Ptd.
Proof.
  exists ptd_from_alg.
  intros T T' β.
  apply ptd_from_alg_mor.
  exact β.
Defined.

Lemma is_functor_ptd_from_alg_functor_data : is_functor ptd_from_alg_functor_data.
Proof.
  split; simpl; intros.
  + unfold functor_idax.
    intro T.
    (* match goal with | [ |- ?l = _ ] => let ty:= (type of l) in idtac ty end. *)
    apply (invmap (eq_ptd_mor_cat _ _ _)).
    apply (invmap (eq_ptd_mor  _ _)).
    (* match goal with | [ |- ?l = _ ] => let ty:= (type of l) in idtac ty end. *)
    apply idpath.
  + unfold functor_compax.
    intros T T' T'' β β'.
    apply (invmap (eq_ptd_mor_cat _ _ _)).
    apply (invmap (eq_ptd_mor _ _)).
    apply idpath.
Qed.

Definition ptd_from_alg_functor: functor (category_FunctorAlg Id_H) Ptd :=
  tpair _ _ is_functor_ptd_from_alg_functor_data.


Definition isbracketMor {T T' : hss} (β : algebra_mor _ T T') : UU :=
    ∏ (Z : Ptd) (f : U Z --> `T),
      ⦃f⦄_{Z} · β = β •• U Z · ⦃f · #U (# ptd_from_alg_functor β)⦄_{Z}.


Lemma isaprop_isbracketMor (T T' : hss) (β : algebra_mor _ T T') : isaprop (isbracketMor β).
Proof.
  do 2 (apply impred; intro).
  apply isaset_nat_trans.
  apply homset_property.
Qed.

(** A morphism of hss is a pointed morphism that is compatible with both
    [τ] and [fbracket] *)

Definition ishssMor {T T' : hss} (β : algebra_mor _ T T') : UU
  :=   isbracketMor β.

Definition hssMor (T T' : hss) : UU
  := ∑ β : algebra_mor _ T T', ishssMor β.

Coercion ptd_mor_from_hssMor (T T' : hss) (β : hssMor T T') : algebra_mor _ T T' := pr1 β.

(*
Definition isAlgMor_hssMor {T T' : hss} (β : hssMor T T')
  : isAlgMor β := pr1 (pr2 β).
*)
Definition isbracketMor_hssMor {T T' : hss} (β : hssMor T T')
  : isbracketMor β := pr2 β.

(** **** Equality of morphisms of hss *)

Section hssMor_equality.

(** Show that equality of hssMor is equality of underlying nat. transformations *)

Context (T T' : hss) (β β' : hssMor T T').

Definition hssMor_eq1 : β = β' ≃ (pr1 β = pr1 β').
Proof.
  apply subtypeInjectivity.
  intro γ.
  apply isaprop_isbracketMor.
Defined.


Definition hssMor_eq : β = β' ≃ (β : EndC ⟦ _ , _ ⟧) = β'.
Proof.
  eapply weqcomp.
  - apply hssMor_eq1.
  - apply subtypeInjectivity.
    intro.
    apply isaset_nat_trans.
    apply homset_property.
Defined.

End hssMor_equality.

Lemma isaset_hssMor (T T' : hss) : isaset (hssMor T T').
Proof.
  intros β β'.
  apply (isofhlevelweqb _ (hssMor_eq _ _ β β')).
  apply isaset_nat_trans.
  apply homset_property.
Qed.

(** ** The precategory of hss *)

(** *** Identity morphism of hss *)

Lemma ishssMor_id (T : hss) : ishssMor (identity (C:=category_FunctorAlg _) (pr1 T)).
Proof.
  unfold ishssMor.
  unfold isbracketMor.
  intros Z f.
  rewrite id_right.
  rewrite functor_id.
  rewrite id_right.
  apply pathsinv0.
  set (H2:=pre_composition_functor _ _ C (U Z)).
  set (H2' := functor_id H2). simpl in H2'.
  simpl.
  rewrite H2'.
  rewrite (@id_left EndC).
  apply idpath.
Qed.

Definition hssMor_id (T : hss) : hssMor _ _ := tpair _ _ (ishssMor_id T).

(** *** Composition of morphisms of hss *)

Lemma ishssMor_comp {T T' T'' : hss} (β : hssMor T T') (γ : hssMor T' T'')
  : ishssMor (compose (C:=category_FunctorAlg _) (pr1 β)  (pr1 γ)).
Proof.
  unfold ishssMor.
  unfold isbracketMor.
  intros Z f.
  eapply pathscomp0; [apply assoc|].
  (* match goal with | [|- ?l = _ ] => assert (Hyp : l = fbracket T f· pr1 β· pr1 γ) end. *)
  etrans.
  { apply cancel_postcomposition.
    apply isbracketMor_hssMor. }
  rewrite <- assoc.
  etrans.
  { apply maponpaths.
    apply isbracketMor_hssMor. }
  rewrite assoc.
  do 2 rewrite functor_comp.
  rewrite assoc.
  apply cancel_postcomposition.
  apply pathsinv0, (functor_comp (pre_composition_functor _ _ C (U Z)) ).
Qed.

Definition hssMor_comp {T T' T'' : hss} (β : hssMor T T') (γ : hssMor T' T'')
  : hssMor T T'' := tpair _ _ (ishssMor_comp β γ).

Definition hss_obmor : precategory_ob_mor.
Proof.
  exists hss.
  exact hssMor.
Defined.

Definition hss_precategory_data : precategory_data.
Proof.
  exists hss_obmor.
  split.
  - exact hssMor_id.
  - exact @hssMor_comp.
Defined.

Lemma is_precategory_hss : is_precategory hss_precategory_data.
Proof.
  apply is_precategory_one_assoc_to_two.
  repeat split; intros.
  - apply (invmap (hssMor_eq _ _ _ _ )).
    apply (@id_left EndC).
  - apply (invmap (hssMor_eq _ _ _ _ )).
    apply (@id_right EndC).
  - apply (invmap (hssMor_eq _ _ _ _ )).
    apply (@assoc EndC).
Qed.

Definition hss_precategory : precategory := tpair _ _ is_precategory_hss.

Lemma has_homsets_precategory_hss : has_homsets hss_precategory.
Proof.
  red.
  intros T T'.
  apply isaset_hssMor.
Qed.

Definition hss_category : category := hss_precategory ,, has_homsets_precategory_hss.

End def_hss.

End fix_a_category.

Arguments hss {_} _ _ .
Arguments hssMor {_ _ _ } _ _ .
Arguments fbracket {_ _ _} _ _ _ .
Arguments fbracket_η {_ _ _} _ {_} _ .
Arguments fbracket_τ {_ _ _} _ {_} _ .
Arguments fbracket_unique_target_pointwise {_ _ _ } _ {_ _ _} _ _.
Arguments fbracket_unique {_ _ _ } _ {_} _ {_} _ .
(* Arguments Alg {_ _} _. *)
Arguments hss_precategory {_} _ _ .
Arguments hss_category {_} _ _ .
Arguments eta_from_alg {_ _ _} _.
Arguments tau_from_alg {_ _ _} _.
Arguments ptd_from_alg {_ _ _} _.
Arguments ptd_from_alg_functor {_} _ _ .
Arguments bracket_property {_ _ _ _ } _ _ _ _ .
Arguments bracket_property_parts {_ _ _ _} _ _ _ _ .
Arguments bracket {_ _ _} _ _.
Arguments prejoin_from_hetsubst {_ _ _} _ .
Arguments prejoin_from_hetsubst_η {_ _ _} _ .
Arguments prejoin_from_hetsubst_τ {_ _ _} _ .

Notation τ := tau_from_alg.
Notation η := eta_from_alg.
