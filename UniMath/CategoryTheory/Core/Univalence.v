(** * Univalent categories (AKA saturated categories) *)

(** ** Contents

  - Univalent categories: [idtoiso] is an equivalence ([univalent_category])
  - Definition of [isotoid]
  - Properties of [idtoiso] and [isotoid]
  - Univalent categories have groupoid as objects
    [univalent_category_has_groupoid_ob]
  - Many lemmas about [idtoiso], [isotoid],
    interplay with composition, transport etc.
 *)

Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.

Local Open Scope cat.

(** ** Univalent categories: [idtoiso] is an equivalence *)

Definition idtoiso {C : precategory} {a b : ob C}:
      a = b -> z_iso a b.
Proof.
  intro H.
  induction H.
  exact (identity_z_iso a).
Defined.

(* use eta expanded version to force printing of object arguments *)
Definition is_univalent (C : category) :=
  ∏ (a b : ob C), isweq (fun p : a = b => idtoiso p).

(*
Definition make_is_univalent {C : precategory} (H1 : ∏ (a b : ob C), isweq (fun p : a = b => idtoiso p))
           (H2 : has_homsets C) : is_univalent C := make_dirprod H1 H2.
 *)

Lemma eq_idtoiso_idtomor {C:precategory} (a b:ob C) (e:a = b) :
    pr1 (idtoiso e) = idtomor _ _ e.
Proof.
  destruct e; reflexivity.
Defined.

Lemma isaprop_is_univalent (C : category) : isaprop (is_univalent C).
Proof.
  apply impred.
  intro a.
  apply impred.
  intro b.
  apply isapropisweq.
Qed.

Definition univalent_category : UU := ∑ C : category, is_univalent C.

Definition make_univalent_category (C : category) (H : is_univalent C) : univalent_category
  := tpair _ C H.

Coercion univalent_category_to_category (C : univalent_category) : category := pr1 C.

Coercion univalent_category_has_homsets (C : univalent_category)
  : has_homsets C
  := pr2 (pr1 C).

Definition univalent_category_is_univalent (C : univalent_category) : is_univalent C := pr2 C.

Lemma univalent_category_has_groupoid_ob (C : univalent_category): isofhlevel 3 (ob C).
Proof.
  change (isofhlevel 3 C) with
        (∏ a b : C, isofhlevel 2 (a = b)).
  intros a b.
  apply (isofhlevelweqb _ (tpair _ _ (pr2 C a b))).
  apply isaset_z_iso.
Qed.

(** ** Definition of [isotoid] *)

Definition isotoid (C : category) (H : is_univalent C) {a b : ob C}:
      z_iso a b -> a = b := invmap (make_weq _ (H a b)).

Lemma idtoiso_isotoid (C : category) (H : is_univalent C) (a b : ob C)
    (f : z_iso a b) : idtoiso (isotoid _ H f) = f.
Proof.
  unfold isotoid.
  set (Hw := homotweqinvweq (make_weq idtoiso (H a b))).
  simpl in Hw.
  apply Hw.
Qed.

Lemma isotoid_idtoiso (C : category) (H : is_univalent C) (a b : ob C)
    (p : a = b) : isotoid _ H (idtoiso p) = p.
Proof.
  unfold isotoid.
  set (Hw := homotinvweqweq (make_weq idtoiso (H a b))).
  simpl in Hw.
  apply Hw.
Qed.

(** ** Properties of [idtoiso] and [isotoid] *)

Definition double_transport {C : precategory_ob_mor} {a a' b b' : ob C}
   (p : a = a') (q : b = b') (f : a --> b) : a' --> b' :=
  transportf (λ c, a' --> c) q (transportf (λ c, c --> b) p f).

Lemma idtoiso_postcompose (C : precategory) (a b b' : ob C)
  (p : b = b') (f : a --> b) :
      f · idtoiso p = transportf (λ b, a --> b) p f.
Proof.
  destruct p.
  apply id_right.
Qed.

Lemma idtoiso_postcompose_iso (C : category) (a b b' : ob C)
  (p : b = b') (f : z_iso a b) :
    z_iso_comp f (idtoiso p) = transportf (λ b, z_iso a b) p f.
Proof.
  destruct p.
  apply z_iso_eq.
  apply id_right.
Qed.

Lemma idtoiso_precompose (C : precategory) (a a' b : ob C)
  (p : a = a') (f : a --> b) :
      (idtoiso (!p)) · f = transportf (λ a, a --> b) p f.
Proof.
  destruct p.
  apply id_left.
Qed.

Lemma idtoiso_precompose_iso (C : category) (a a' b : ob C)
  (p : a = a') (f : z_iso a b) :
      z_iso_comp (idtoiso (!p)) f = transportf (λ a, z_iso a b) p f.
Proof.
  destruct p.
  apply z_iso_eq.
  apply id_left.
Qed.

Lemma double_transport_idtoiso (C : precategory) (a a' b b' : ob C)
  (p : a = a') (q : b = b')  (f : a --> b) :
  double_transport p q f = inv_from_z_iso (idtoiso p) · f · idtoiso q.
Proof.
  destruct p.
  destruct q.
  intermediate_path (identity _ · f).
  - apply pathsinv0; apply id_left.
  - apply pathsinv0; apply id_right.
Defined.

Lemma idtoiso_inv (C : category) (a a' : ob C)
  (p : a = a') : idtoiso (!p) = z_iso_inv_from_z_iso (idtoiso p).
Proof.
  destruct p.
  simpl. apply z_iso_eq.
  apply idpath.
Defined.

Lemma idtoiso_concat (C : category) (a a' a'' : ob C)
  (p : a = a') (q : a' = a'') :
  idtoiso (p @ q) = z_iso_comp (idtoiso p) (idtoiso q).
Proof.
  destruct p.
  destruct q.
  apply z_iso_eq.
  simpl; apply pathsinv0, id_left.
Qed.

Lemma idtoiso_inj (C : category) (H : is_univalent C) (a a' : ob C)
   (p p' : a = a') : idtoiso p = idtoiso p' -> p = p'.
Proof.
  apply invmaponpathsincl.
  apply isinclweq.
  apply H.
Qed.

Lemma isotoid_inj (C : category) (H : is_univalent C) (a a' : ob C)
   (f f' : z_iso a a') : isotoid _ H f = isotoid _ H f' -> f = f'.
Proof.
  apply invmaponpathsincl.
  apply isinclweq.
  apply isweqinvmap.
Qed.

Lemma isotoid_comp (C : category) (H : is_univalent C) (a b c : ob C)
  (e : z_iso a b) (f : z_iso b c) :
  isotoid _ H (z_iso_comp e f) = isotoid _ H e @ isotoid _ H f.
Proof.
  apply idtoiso_inj.
    assumption.
  rewrite idtoiso_concat.
  repeat rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma isotoid_identity_iso (C : category) (H : is_univalent C) (a : C) :
  isotoid _ H (identity_z_iso a) = idpath _ .
Proof.
  apply idtoiso_inj; try assumption.
  rewrite idtoiso_isotoid;
  apply idpath.
Qed.

Lemma inv_isotoid (C : category) (H : is_univalent C) (a b : C)
    (f : z_iso a b) : ! isotoid _ H f = isotoid _ H (z_iso_inv_from_z_iso f).
Proof.
  apply idtoiso_inj; try assumption.
  rewrite idtoiso_isotoid.
  rewrite idtoiso_inv.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma transportf_isotoid (C : category) (H : is_univalent C)
   (a a' b : ob C) (p : z_iso a a') (f : a --> b) :
 transportf (λ a0 : C, a0 --> b) (isotoid C H p) f = inv_from_z_iso p · f.
Proof.
  rewrite <- idtoiso_precompose.
  rewrite idtoiso_inv.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma transportf_isotoid' (C : category) (H : is_univalent C)
   (a b b' : ob C) (p : z_iso b b') (f : a --> b) :
 transportf (λ a0 : C, a --> a0) (isotoid C H p) f = f · p.
Proof.
  rewrite <- idtoiso_postcompose.
  apply maponpaths.
  rewrite idtoiso_isotoid.
  apply idpath.
Qed.

Lemma transportf_isotoid_dep (C : precategory)
   (a a' : C) (p : a = a') (f : ∏ c, a --> c) :
 transportf (λ x : C, ∏ c, x --> c) p f = λ c, idtoiso (!p) · f c.
Proof.
  destruct p.
  simpl.
  apply funextsec.
  intro.
  rewrite id_left.
  apply idpath.
Qed.

Lemma forall_isotoid (A : category) (a_is : is_univalent A)
      (a a' : A) (P : z_iso a a' -> UU) :
  (∏ e, P (idtoiso e)) → ∏ i, P i.
Proof.
  intros H i.
  rewrite <- (idtoiso_isotoid _ a_is).
  apply H.
Defined.

Lemma transportf_isotoid_dep' (J : UU) (C : precategory) (F : J -> C)
  (a a' : C) (p : a = a') (f : ∏ c, a --> F c) :
  transportf (λ x : C, ∏ c, x --> F c) p f = λ c, idtoiso (!p) · f c.
Proof.
  now destruct p; apply funextsec; intro x; rewrite id_left.
Defined.

(* This and the above name is not very good... *)
 Lemma transportf_isotoid_dep'' (J : UU) (C : precategory) (F : J -> C)
   (a a' : C) (p : a = a') (f : ∏ c, F c --> a) :
   transportf (λ x : C, ∏ c, F c --> x) p f = λ c, f c · idtoiso p.
Proof.
  now destruct p; apply funextsec; intro x; rewrite id_right.
Defined.
