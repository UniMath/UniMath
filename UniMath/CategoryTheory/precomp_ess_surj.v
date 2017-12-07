
(** **********************************************************

Benedikt Ahrens, Chris Kapulkin, Mike Shulman

january 2013


************************************************************)


(** **********************************************************

Contents : Precomposition with a fully faithful and
           essentially surjective functor yields
           an essentially surjective functor

************************************************************)


Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Local Notation "FF ^-1" := (fully_faithful_inv_hom FF _ _ ) (at level 20).
Local Notation "F '^-i'" := (iso_from_fully_faithful_reflection F) (at level 20).
Local Notation "G 'O' F" := (functor_compose _ _ _ F G) (at level 25).

Ltac inv_functor HF x y :=
   let H:=fresh in
   set (H:= homotweqinvweq (weq_from_fully_faithful HF x y));
     simpl in H;
     unfold fully_faithful_inv_hom; simpl;
     rewrite H; clear H.


(** * Lengthy preparation for the main result of this file *)

Section precomp_w_ess_surj_ff_is_ess_surj.

(** ** Section variables *)

Variables A B C : precategory.
Hypothesis Ccat : is_univalent C.
Variable H : functor A B.
Hypothesis p : essentially_surjective H.
Hypothesis fH : fully_faithful H.

(**  We prove that precomposition with a [H] yields an essentially surjective functor *)

Section essentially_surjective.


(** ** Specification of preimage [G] of a functor [F] *)

(** Given a functor [F] from [A] to [C], we construct [G] such that
       [F = G O H] *)

Variable F : functor A C.

Section preimage.

(** The type [X b] will be contractible, and [G] is defined as
     the first component of its center. *)

Local Definition X (b : B) := total2 (
 fun ck :
  total2 (λ c : C,
                ∏ a : A,
                     iso (H a) b -> iso (F a) c) =>
    ∏ t t' : total2 (λ a : A, iso (H a) b),
          ∏ f : pr1 t --> pr1 t',
             (#H f · pr2 t' = pr2 t ->
                    #F f · pr2 ck (pr1 t') (pr2 t') = pr2 ck (pr1 t) (pr2 t))).

Local Definition kX {b : B} (t : X b) := (pr2 (pr1 t)).

(** The following is the third component of the center of [X b] *)

Lemma X_aux_type_center_of_contr_proof (b : B) (anot : A) (hnot : iso (H anot) b) :
  ∏ (t t' : total2 (λ a :  A, iso (H a) b))
    (f : pr1 t --> pr1 t'),
  #H f· pr2 t' = pr2 t ->
  #F f·
  #F (fH^-1 (pr2 t'· inv_from_iso hnot)) =
  #F (fH^-1 (pr2 t· inv_from_iso hnot)).
Proof.
  intros t t' f.
  destruct t as [a h].
  destruct t' as [a' h'].
  simpl in *.
  intro star.
  rewrite <- functor_comp.
  apply maponpaths.
  apply (invmaponpathsweq
          (weq_from_fully_faithful fH a anot)).
  simpl.
  rewrite functor_comp.
  inv_functor fH a' anot.
  rewrite assoc.
  inv_functor fH a anot.
  rewrite <- star.
  apply idpath.
Qed.

(** The center of [X b] *)

Definition X_aux_type_center_of_contr (b : B)
    (anot : A)(hnot : iso (H anot) b) : X b.
Proof.
  set (cnot := F anot).
  set (g := fun (a : A)(h : iso (H a) b) =>
              (fH^-i (iso_comp h (iso_inv_from_iso hnot)))).
  set (knot := fun (a : A)(h : iso (H a) b) =>
                    functor_on_iso F (g a h)).
  simpl in *.
  exists (tpair _ (F anot) knot).
  simpl.
  apply X_aux_type_center_of_contr_proof.
Defined.

(** Any inhabitant of [X b] is equal to the center of [X b]. *)

Lemma X_aux_type_contr_eq (b : B) (anot : A) (hnot : iso (H anot) b) :
   ∏ t : X b, t = X_aux_type_center_of_contr b anot hnot.
Proof.
  intro t.
  assert (Hpr1 : pr1 (X_aux_type_center_of_contr b anot hnot) = pr1 t).
  set (w := isotoid _ Ccat ((pr2 (pr1 t)) anot hnot) :
          pr1 (pr1 (X_aux_type_center_of_contr b anot hnot)) = pr1 (pr1 t)).
  apply (total2_paths_f w).
  simpl.
  destruct t as [[c1 k1] q1].
  simpl in *.
  apply funextsec; intro a.
  apply funextsec; intro h.
  set (gah := fH^-i (iso_comp h (iso_inv_from_iso hnot))).
  set (qhelp := q1 (tpair _ a h)(tpair _ anot hnot) gah).
  simpl in *.

  assert (feedtoqhelp :
        #H (fH^-1 (h· inv_from_iso hnot))· hnot = h).
    inv_functor fH a anot.
    rewrite <- assoc.
    rewrite iso_after_iso_inv.
    apply id_right.
  assert (quack := qhelp feedtoqhelp).
  simpl in *.
  intermediate_path (iso_comp  (functor_on_iso F
       (fH^-i (iso_comp h (iso_inv_from_iso hnot)))) (idtoiso w) ).
  generalize w; intro w0.
  induction w0.
  simpl. apply eq_iso. simpl.
  simpl. rewrite id_right.
  apply idpath.

  apply eq_iso.
  simpl.
  unfold w.
  rewrite idtoiso_isotoid.
  apply quack.

  apply pathsinv0.
  apply (total2_paths_f Hpr1).
  apply proofirrelevance.

  repeat (apply impred; intro).
  apply (pr2 Ccat).
Qed.


(** Putting everything together: [X b] is contractible. *)

Definition iscontr_X : ∏ b : B, iscontr (X b).
Proof.
  intro b.
  assert (HH : isaprop (iscontr (X b))).
  apply isapropiscontr.
  apply (p b (tpair (λ x, isaprop x) (iscontr (X b)) HH)).
  intro t.
  exists (X_aux_type_center_of_contr b (pr1 t) (pr2 t)).
  apply (X_aux_type_contr_eq b (pr1 t) (pr2 t)).
Defined.

(** The object part of [G], [Go b], is defined as the first component of
    the center of [X b]. *)

(** *** [G] on objects *)

Definition Go : B -> C :=
   λ b : B, pr1 (pr1 (pr1 (iscontr_X b))).

Local Definition k (b : B) :
     ∏ a : A, iso (H a) b -> iso (F a) (Go b) :=
              pr2 (pr1 (pr1 (iscontr_X b))).

Local Definition q (b : B) := pr2 (pr1 (iscontr_X b)).


(** Given any inhabitant of [X b], its first component is equal to [Go b]. *)

Definition Xphi (b : B) (t : X b) : pr1 (pr1 t) = Go b.
Proof.
  set (p1 := pr2 (iscontr_X b) t).
  exact (base_paths _ _ (base_paths _ _ p1)).
Defined.

(** Given any inhabitant [t : X b], its second component is equal to [k b],
       modulo transport along [Xphi b t]. *)

Definition Xkphi_transp (b : B) (t : X b) :
     ∏ a : A, ∏ h : iso (H a) b,
  transportf _ (Xphi b t) (kX t) a h =  k b a h.
Proof.
  unfold k.
  rewrite <- (fiber_paths (base_paths _ _ (pr2 (iscontr_X b) t))).
  intros ? ?.
  apply maponpaths, idpath.
Qed.

(** Similarly to the lemma before, the second component of [t] is the same
    as [k b], modulo postcomposition with an isomorphism. *)

Definition Xkphi_idtoiso (b : B) (t : X b) :
    ∏ a : A, ∏ h : iso (H a) b,
   k b a h · idtoiso (!Xphi b t) = kX t a h.
Proof.
  intros a h.
  rewrite <- (Xkphi_transp _ t).
  generalize (Xphi b t).
  intro i; destruct i.
  apply id_right.
Qed.


(*
Lemma k_transport (b : ob B) (*t : X b*) (c : ob C)
   (p : pr1 (pr1 t) = c) (a : ob A) (h : iso (pr1 H a) b):
transportf (λ c' : ob C, ∏ a : ob A, iso (pr1 H a) b ->
                          iso ((pr1 F) a) c')
   p (k) a h = (k b) b a h · idtoiso p .
*)


(** *** Preparation for [G] on morphisms *)

(** [G f] will be defined as the first component of the center of
     contraction of [Y f]. *)

Local Definition Y {b b' : B} (f : b --> b') :=
  total2 (fun g : Go b --> Go b' =>
      ∏ a : A,
        ∏ h : iso (H a) b,
          ∏ a' : A,
            ∏ h' : iso (H a') b',
              ∏ l : a --> a',
                #H l · h' = h · f -> #F l · k b' a' h' = k b a h · g).

Lemma Y_inhab_proof (b b' : B) (f : b --> b') (a0 : A) (h0 : iso (H a0) b)
    (a0' : A) (h0' : iso (H a0') b') :
  ∏ (a : A) (h : iso (H a) b) (a' : A) (h' : iso (H a') b')
    (l : a --> a'),
  #H l· h' = h· f ->
  #F l· k b' a' h' =
    k b a h· ((inv_from_iso (k b a0 h0)·
  #F (fH^-1 ((h0· f)· inv_from_iso h0')))· k b' a0' h0').
Proof.
  intros a h a' h' l alpha.
  set (m := fH^-i (iso_comp h0 (iso_inv_from_iso h))).
  set (m' := fH^-i (iso_comp h0' (iso_inv_from_iso h'))).
  assert (sss : iso_comp (functor_on_iso F m) (k b a h) =
                   k b a0 h0).
    apply eq_iso.
    apply (q b (tpair _ a0 h0) (tpair _ a h) m).
    simpl.
    inv_functor fH a0 a.
    rewrite <- assoc.
    rewrite iso_after_iso_inv.
    apply id_right.
  assert (ssss : iso_comp (functor_on_iso F m') (k b' a' h') =
                   k b' a0' h0').
    apply eq_iso.
    apply (q b' (tpair _ a0' h0') (tpair _ a' h') m').
    simpl;
    inv_functor fH a0' a'.
    rewrite <- assoc.
    rewrite iso_after_iso_inv.
    apply id_right.

  set (hfh := h0 · f · inv_from_iso h0').
  set (l0 := fH^-1 hfh).
  set (g0 := inv_from_iso (k b a0 h0) · #F l0  · k b' a0' h0').

  assert (sssss : #H (l0 · m') = #H (m · l)).
    rewrite functor_comp .
    unfold m'. simpl.
    inv_functor fH a0' a'.
    unfold l0.
    inv_functor fH a0 a0'.
    unfold hfh.
    intermediate_path (h0 · f · (inv_from_iso h0' · h0') · inv_from_iso h').
      repeat rewrite assoc; apply idpath.
    rewrite iso_after_iso_inv, id_right, functor_comp.
    inv_functor fH a0 a.
    repeat rewrite <- assoc.
    apply maponpaths, pathsinv0, iso_inv_on_right.
    rewrite assoc.
    apply iso_inv_on_left, pathsinv0, alpha.

  assert (star5 : inv_from_iso m · l0 = l · inv_from_iso m').
    apply iso_inv_on_right.
    rewrite assoc.
    apply iso_inv_on_left,
          (invmaponpathsweq (weq_from_fully_faithful fH a0 a' )),
          pathsinv0,
          sssss.
  clear sssss.
  unfold g0.
  assert (sss'' : k b a h · inv_from_iso (k b a0 h0) =
             inv_from_iso (functor_on_iso F m)).
    apply pathsinv0, iso_inv_on_left, pathsinv0.
    apply iso_inv_on_right.
    unfold m; simpl.
    apply pathsinv0, (base_paths _ _ sss).
  repeat rewrite assoc.
  rewrite sss''. clear sss'' sss.

  rewrite <- functor_on_inv_from_iso.
  rewrite <- functor_comp.
  rewrite star5; clear star5 .
  rewrite functor_comp, functor_on_inv_from_iso.
  assert (star4 :
        inv_from_iso (functor_on_iso F m')· k b' a0' h0'
           = k b' a' h' ).
    apply iso_inv_on_right.
    apply pathsinv0, (base_paths _ _ ssss).
  rewrite <- assoc.
  rewrite star4.
  apply idpath.
Qed.

(** The center of [Y b b' f]. *)

Definition Y_inhab (b b' : B) (f : b --> b')
      (a0 : A) (h0 : iso (H a0) b) (a0' : A) (h0' : iso (H a0') b') : Y f.
Proof.
  set (hfh := h0 · f · inv_from_iso h0').
  set (l0 := fH^-1 hfh).
  set (g0 := inv_from_iso (k b a0 h0) · #F l0  · k b' a0' h0').
  exists g0.
  apply Y_inhab_proof.
Defined.

(** Any inhabitant of [Y b b' f] is equal to the center. *)

Lemma Y_contr_eq (b b' : B) (f : b --> b')
     (a0 : A) (h0 : iso (H a0) b)
     (a0' : A) (h0' : iso (H a0') b') :
  ∏ t : Y f, t = Y_inhab b b' f a0 h0 a0' h0'.
Proof.
  intro t.
  apply pathsinv0.
  assert (Hpr : pr1 (Y_inhab b b' f a0 h0 a0' h0') = pr1 t).
    destruct t as [g1 r1]; simpl in *.
    rewrite <- assoc.
    apply iso_inv_on_right.
    set (hfh := h0 · f · inv_from_iso h0').
    set (l0 := fH^-1 hfh).
    apply (r1 a0 h0 a0' h0' l0).
    unfold l0.
    inv_functor fH a0 a0' .
    unfold hfh.
    repeat rewrite <- assoc.
    rewrite iso_after_iso_inv, id_right.
    apply idpath.
  apply (total2_paths_f Hpr).
  apply proofirrelevance.
  repeat (apply impred; intro).
  apply (pr2 Ccat).
Qed.

(** The type [Y b b' f] is contractible. *)

Definition Y_iscontr  (b b' : B) (f : b --> b') :
   iscontr (Y f).
Proof.
  assert (HH : isaprop (iscontr (Y f))).
    apply isapropiscontr.
  apply (p b (tpair (λ x, isaprop x) (iscontr (Y f)) HH)).
  intros [a0 h0].
  apply (p b' (tpair (λ x, isaprop x) (iscontr (Y f)) HH)).
  intros [a0' h0'].
  exists (Y_inhab b b' f a0 h0 a0' h0').
  apply Y_contr_eq.
Defined.

(** *** [G] on morphisms *)

(** We now have the data necessary to define the functor [G]. *)

Definition preimage_functor_data : functor_data B C.
Proof.
  exists Go.
  intros b b' f.
  exact (pr1 (pr1 (Y_iscontr b b' f))).
Defined.


Local Notation "'G' f" := (pr1 (pr1 (Y_iscontr _ _ f))) (at level 3).

(** The above data is indeed functorial. *)

Lemma is_functor_preimage_functor_data : is_functor preimage_functor_data.
Proof.
  split. unfold functor_idax. simpl.
  intro b.

  assert (PR2 : ∏ (a : A) (h : iso (H a) b) (a' : A)
          (h' : iso (H a') b)
    (l : a --> a'),
  #H l· h' = h· identity b ->
  #F l· k b a' h' = k b a h· identity (Go b)).
    intros a h a' h' l LL.
    rewrite id_right.
    apply (q b (tpair _ a h) (tpair _ a' h') l).
    rewrite id_right in LL.
    apply LL.
    set (Gbrtilde :=
           tpair _ (identity (Go b)) PR2 : Y (identity b)).

    set (H' := pr2 (Y_iscontr b b (identity b)) Gbrtilde).
    set (H'' := base_paths _ _ H').
    simpl in H'.
    rewrite <- H'.
    apply idpath.


  (** composition *)

  intros b b' b'' f f'.

  assert (HHHH : isaprop (pr1 (pr1 (Y_iscontr b b'' (f· f'))) =
                        pr1 (pr1 (Y_iscontr b b' f))· pr1 (pr1 (Y_iscontr b' b'' f')))).
    apply (pr2 Ccat).
  apply (p b (tpair (λ x, isaprop x) (pr1 (pr1 (Y_iscontr b b'' (f· f'))) =
           pr1 (pr1 (Y_iscontr b b' f))· pr1 (pr1 (Y_iscontr b' b'' f'))) HHHH)).
  intros [a0 h0]; simpl.
  apply (p b' (tpair (λ x, isaprop x) (pr1 (pr1 (Y_iscontr b b'' (f· f'))) =
           pr1 (pr1 (Y_iscontr b b' f))· pr1 (pr1 (Y_iscontr b' b'' f'))) HHHH)).
  intros [a0' h0']; simpl.
  apply (p b'' (tpair (λ x, isaprop x) (pr1 (pr1 (Y_iscontr b b'' (f· f'))) =
           pr1 (pr1 (Y_iscontr b b' f))· pr1 (pr1 (Y_iscontr b' b'' f'))) HHHH)).
  intros [a0'' h0''].
  simpl; clear HHHH.

  set (l0 := fH^-1 (h0 · f · inv_from_iso h0')).
  set (l0' := fH^-1 (h0' · f' · inv_from_iso h0'')).
  set (l0'' := fH^-1 (h0 · (f· f') · inv_from_iso h0'')).

  assert (L : l0 · l0' = l0'').
    apply (invmaponpathsweq (weq_from_fully_faithful fH a0 a0'')).
    simpl; rewrite functor_comp.
    unfold l0'.
    inv_functor fH a0' a0''.
    unfold l0.
    inv_functor fH a0 a0'.
    intermediate_path (h0 · f · (inv_from_iso h0' · h0') · f' · inv_from_iso h0'').
      repeat rewrite assoc; apply idpath.
    rewrite iso_after_iso_inv, id_right.
    unfold l0''.
    inv_functor fH a0 a0''.
    repeat rewrite assoc; apply idpath.


  assert (PR2 : ∏ (a : A) (h : iso (H a) b)(a' : A)
          (h' : iso (H a') b') (l : a --> a'),
           #H l· h' = h· f ->
           #F l· k b' a' h' =
            k b a h· ((inv_from_iso (k b a0 h0)· #F l0)· k b' a0' h0') ).
    intros a h a' h' l.
    intro alpha.
    set (m := fH^-i (iso_comp h0 (iso_inv_from_iso h))).
    set (m' := fH^-i (iso_comp h0' (iso_inv_from_iso h'))).
    assert (sss : iso_comp (functor_on_iso F m) (k b a h) =
                   k b a0 h0).
      apply eq_iso; simpl.
      apply (q b (tpair _ a0 h0) (tpair _ a h) m).
      simpl.
      inv_functor fH a0 a.
      rewrite <- assoc.
      rewrite iso_after_iso_inv.
      apply id_right.
    assert (ssss : iso_comp (functor_on_iso F m') (k b' a' h') =
                   k b' a0' h0').
      apply eq_iso; simpl.
      apply (q b' (tpair _ a0' h0') (tpair _ a' h') m'); simpl.
      inv_functor fH a0' a'.
      rewrite <- assoc.
      rewrite iso_after_iso_inv.
      apply id_right.
    assert (sssss : #H (l0 · m') = #H (m · l)).
      rewrite functor_comp.
      unfold m'; simpl.
      inv_functor fH a0' a'.
      unfold l0.
      inv_functor fH a0 a0'.
      intermediate_path (h0 · f · (inv_from_iso h0' · h0') · inv_from_iso h').
        repeat rewrite assoc; apply idpath.
      rewrite iso_after_iso_inv, id_right, functor_comp.
      inv_functor fH a0 a.
      repeat rewrite <- assoc.
      apply maponpaths.
      apply pathsinv0.
      apply iso_inv_on_right.
      rewrite assoc.
      apply iso_inv_on_left.
      apply pathsinv0.
      apply alpha.
    assert (star5 : inv_from_iso m · l0 = l · inv_from_iso m').
      apply iso_inv_on_right.
      rewrite assoc.
      apply iso_inv_on_left.
      apply (invmaponpathsweq (weq_from_fully_faithful fH a0 a' )).
      apply pathsinv0.
      apply sssss.
    clear sssss.
    set (sss':= base_paths _ _ sss); simpl in sss'.
    assert (sss'' : k b a h · inv_from_iso (k b a0 h0) =
             inv_from_iso (functor_on_iso F m)).
      apply pathsinv0.
      apply iso_inv_on_left.
      apply pathsinv0.
      apply iso_inv_on_right.
      unfold m; simpl.
      apply pathsinv0.
      apply sss'.
    repeat rewrite assoc.
    rewrite sss''. clear sss'' sss' sss.
    rewrite <- functor_on_inv_from_iso.
    rewrite <- functor_comp.
    rewrite star5, functor_comp, functor_on_inv_from_iso.
    clear star5.
    assert (star4 :
        inv_from_iso (functor_on_iso F m')· k b' a0' h0'
           = k b' a' h' ).
      apply iso_inv_on_right.
      set (ssss' := base_paths _ _ ssss).
      apply pathsinv0.
      simpl in ssss'. simpl.
      apply ssss'; clear ssss'.
    rewrite <- assoc.
    rewrite star4.
    apply idpath.

  assert (HGf : G f = inv_from_iso (k b a0 h0) · #F l0 · k b' a0' h0').
    set (Gbrtilde :=
           tpair _ (inv_from_iso (k b a0 h0) · #F l0 · k b' a0' h0') PR2 : Y f).
    set (H' := pr2 (Y_iscontr b b' f) Gbrtilde).
    set (H'' := base_paths _ _ H').
    simpl in H'.
    rewrite <- H'.
    apply idpath.

  clear PR2.
  assert (PR2 : ∏ (a : A) (h : iso (H a) b') (a' : A)
            (h' : iso (H a') b'') (l : a --> a'),
         #H l· h' = h· f' ->
           #F l· k b'' a' h' =
         k b' a h· ((inv_from_iso (k b' a0' h0')· #F l0')· k b'' a0'' h0'')).
    intros a' h' a'' h'' l'.
    intro alpha.
    set (m := fH^-i (iso_comp h0' (iso_inv_from_iso h'))).
    set (m' := fH^-i (iso_comp h0'' (iso_inv_from_iso h''))).
    assert (sss : iso_comp (functor_on_iso F m) (k b' a' h') =
                   k b' a0' h0').
      apply eq_iso; simpl.
      apply (q b' (tpair _ a0' h0') (tpair _ a' h') m); simpl.
      inv_functor fH a0' a'.
      rewrite <- assoc.
      rewrite iso_after_iso_inv.
      apply id_right.
    assert (ssss : iso_comp (functor_on_iso F m') (k b'' a'' h'') =
                   k b'' a0'' h0'').
      apply eq_iso; simpl.
      apply (q b'' (tpair _ a0'' h0'') (tpair _ a'' h'') m'); simpl.
      inv_functor fH a0'' a''.
      rewrite <- assoc.
      rewrite iso_after_iso_inv.
      apply id_right.
    assert (sssss : #H (l0' · m') = #H (m · l')).
      rewrite functor_comp.
      unfold m'. simpl.
      inv_functor fH a0'' a''.
      unfold l0'.
      inv_functor fH a0' a0''.
      intermediate_path (h0' · f' · (inv_from_iso h0'' · h0'') · inv_from_iso h'').
        repeat rewrite assoc; apply idpath.
      rewrite iso_after_iso_inv, id_right, functor_comp.
      inv_functor fH a0' a'.
      repeat rewrite <- assoc.
      apply maponpaths, pathsinv0, iso_inv_on_right.
      rewrite assoc.
      apply iso_inv_on_left, pathsinv0, alpha.
    assert (star5 : inv_from_iso m · l0' = l' · inv_from_iso m').
      apply iso_inv_on_right.
      rewrite assoc.
      apply iso_inv_on_left,
        (invmaponpathsweq (weq_from_fully_faithful fH a0' a'' )),
        pathsinv0,
        sssss.
    set (sss':= base_paths _ _ sss); simpl in sss'.
    assert (sss'' : k b' a' h' · inv_from_iso (k b' a0' h0') =
             inv_from_iso (functor_on_iso F m)).
      apply pathsinv0, iso_inv_on_left, pathsinv0, iso_inv_on_right.
      unfold m; simpl;
      apply pathsinv0, sss'.
    repeat rewrite assoc.
    rewrite sss''. clear sss'' sss' sss.
    rewrite <- functor_on_inv_from_iso.
    rewrite <- functor_comp.
    rewrite star5. clear star5 sssss.
    rewrite functor_comp, functor_on_inv_from_iso.
    assert (star4 :
        inv_from_iso (functor_on_iso F m')· k b'' a0'' h0''
           = k b'' a'' h'' ).
      apply iso_inv_on_right.
      set (ssss' := base_paths _ _ ssss).
      apply pathsinv0.
      simpl in *; apply ssss'.
    rewrite <- assoc.
    rewrite star4.
    apply idpath.
  assert (HGf' : G f' = inv_from_iso (k b' a0' h0') · #F l0' · k b'' a0'' h0'').
    set (Gbrtilde :=
       tpair _ (inv_from_iso (k b' a0' h0') · #F l0' · k b'' a0'' h0'') PR2 :
                      Y f').
    set (H' := pr2 (Y_iscontr b' b'' f') Gbrtilde).
    rewrite <-(base_paths _ _ H').
    apply idpath.

  clear PR2.
  assert (PR2 : ∏ (a : A) (h : iso (H a) b) (a' : A)
             (h' : iso (H a') b'') (l : a --> a'),
          #H l· h' = h· (f· f') ->
          #F l· k b'' a' h' =
           k b a h· ((inv_from_iso (k b a0 h0)· #F l0'')· k b'' a0'' h0'')).
    intros a h a'' h'' l.
    intro alpha.
    set (m := fH^-i (iso_comp h0 (iso_inv_from_iso h))).
    set (m' := fH^-i (iso_comp h0'' (iso_inv_from_iso h''))).
    assert (sss : iso_comp (functor_on_iso F m) (k b a h) = k b a0 h0).
      apply eq_iso.
      apply (q b (tpair _ a0 h0) (tpair _ a h) m); simpl.
      inv_functor fH a0 a.
      rewrite <- assoc.
      rewrite iso_after_iso_inv.
      apply id_right.
    assert (ssss : iso_comp (functor_on_iso F m') (k b'' a'' h'') =
                   k b'' a0'' h0'').
      apply eq_iso.
      apply (q b'' (tpair _ a0'' h0'') (tpair _ a'' h'') m').
      simpl; inv_functor fH a0'' a''.
      rewrite <- assoc.
      rewrite iso_after_iso_inv.
      apply id_right.
    assert (sssss : #H (l0'' · m') = #H (m · l)).
      rewrite functor_comp.
      unfold m'. simpl.
      inv_functor fH a0'' a''.
      unfold l0''.
      inv_functor fH a0 a0''.
      intermediate_path (h0 · (f · f') · (inv_from_iso h0'' · h0'') · inv_from_iso h'').
        repeat rewrite assoc; apply idpath.
      rewrite iso_after_iso_inv, id_right, functor_comp.
      inv_functor fH a0 a.
      repeat rewrite <- assoc.
      apply maponpaths, pathsinv0, iso_inv_on_right.
      repeat rewrite assoc.
      apply iso_inv_on_left, pathsinv0.
      repeat rewrite <- assoc.
      apply alpha.
    assert (star5 : inv_from_iso m · l0'' = l · inv_from_iso m').
      apply iso_inv_on_right.
      rewrite assoc.
      apply iso_inv_on_left.
      apply (invmaponpathsweq (weq_from_fully_faithful fH a0 a'' )).
      apply pathsinv0, sssss.
    set (sss':= base_paths _ _ sss); simpl in sss'.
    assert (sss'' : k b a h · inv_from_iso (k b a0 h0) =
             inv_from_iso (functor_on_iso F m)).
      apply pathsinv0, iso_inv_on_left, pathsinv0, iso_inv_on_right.
      unfold m; simpl.
      apply pathsinv0, sss'.
    repeat rewrite assoc.
    rewrite sss''. clear sss'' sss' sss.
    rewrite <- functor_on_inv_from_iso.
    rewrite <- functor_comp.
    rewrite star5. clear star5 sssss.
    rewrite functor_comp, functor_on_inv_from_iso.
    assert (star4 :
        inv_from_iso (functor_on_iso F m')· k b'' a0'' h0''
           = k b'' a'' h'' ).
      apply iso_inv_on_right, pathsinv0, (base_paths _ _ ssss).
    rewrite <- assoc.
    rewrite star4.
    apply idpath.
  assert (HGff' : G (f · f') =
       inv_from_iso (k b a0 h0) · #F l0'' · k b'' a0'' h0'').
    set (Gbrtilde :=
           tpair _ (inv_from_iso (k b a0 h0) · #F l0'' · k b'' a0'' h0'') PR2 :
               Y (f · f')).
    rewrite <- (pr2 (Y_iscontr b b'' (f · f')) Gbrtilde).
    apply idpath.
  clear PR2.
  rewrite HGf, HGf'.
  intermediate_path (inv_from_iso (k b a0 h0)· #F l0· (k b' a0' h0'·
              inv_from_iso (k b' a0' h0'))· #F l0'· k b'' a0'' h0'').
    rewrite iso_inv_after_iso, id_right.
    rewrite HGff'.
    repeat rewrite <- assoc.
    apply maponpaths.
    rewrite <- L.
    rewrite functor_comp.
    repeat rewrite <- assoc.
    apply idpath.
  repeat rewrite <- assoc.
  apply idpath.
Qed.


(** We call the functor [GG] ... *)

Definition GG : [B, C, pr2 Ccat] := tpair _ preimage_functor_data
                    is_functor_preimage_functor_data.

(** ** [G] is the preimage of [F] under [ _ O H] *)

(** Given any [a : A], we produce an element in [X (H a)], whose
     first component is [F a].
   This allows to prove [G (H a) = F a]. *)

Lemma qF (a0 : A) :
  ∏ (t t' : total2 (λ a :  A, iso (H a) (H a0)))
    (f : pr1 t --> pr1 t'),
  #H f· pr2 t' = pr2 t ->
  #F f· #F (fH^-1 (pr2 t')) =
  #F (fH^-1  (pr2 t)).
Proof.
  simpl.
  intros [a h] [a' h'] f L.
  simpl in L; simpl.
  rewrite <- functor_comp.
  apply maponpaths.
  apply (invmaponpathsweq (weq_from_fully_faithful fH a a0)
                 (f· fH^-1 h') (fH^-1 h)  ).
  inv_functor fH a a0.
  rewrite functor_comp.
  inv_functor fH a' a0.
  apply L.
Qed.


Definition kFa (a0 : A) : ∏ a : A,
  iso (H a) (H a0) -> iso (F a) (F a0) :=
 fun (a : A) (h : iso (H a) (H a0)) =>
   functor_on_iso F
                  (iso_from_fully_faithful_reflection fH h).

Definition XtripleF (a0 : A) : X (H a0) :=
   tpair _ (tpair _ (F a0) (kFa a0)) (qF a0).


Lemma phi (a0 : A) : pr1 (pr1 (functor_composite H GG)) a0 = pr1 (pr1 F) a0.
Proof.
  exact (!Xphi _ (XtripleF a0)).
Defined.

Lemma extphi : pr1 (pr1 (functor_composite H GG)) = pr1 (pr1 F).
Proof.
  apply funextsec.
  unfold homot.
  apply phi.
Defined.

(** Now for the functor as a whole. It remains to prove
    equality on morphisms, modulo transport. *)

Lemma is_preimage_for_pre_composition : functor_composite H GG = F.
Proof.
  apply (functor_eq _ _  (pr2 Ccat) (functor_composite H GG) F).
  apply (total2_paths_f extphi).
  apply funextsec; intro a0;
  apply funextsec; intro a0';
  apply funextsec; intro f.
  rewrite transport_of_functor_map_is_pointwise.
  unfold extphi.
  rewrite toforallpaths_funextsec.
  rewrite <- idtoiso_postcompose.
  rewrite <- idtoiso_precompose.
  rewrite idtoiso_inv.
  rewrite <- assoc.
  assert (PSIf : ∏ (a : A) (h : iso (H a) (H a0)) (a' : A)
  (h' : iso (H a') (H a0')) (l : a --> a'),
         #H l· h' = h· #H f ->
         #F l· k (H a0') a' h' =
         k (H a0) a h·
         ((idtoiso (phi a0)· #F f)· inv_from_iso (idtoiso (phi a0')))).
    intros a h a' h' l alpha.
    rewrite assoc.
    apply iso_inv_on_left.
    unfold phi.
    repeat rewrite assoc.
    rewrite (Xkphi_idtoiso (H a0) (XtripleF a0)).
    repeat rewrite <- assoc.
    rewrite (Xkphi_idtoiso (H a0') (XtripleF a0')).
    simpl.
    assert (HH4 : fH^-1 h · f = l · fH^-1 h').
      apply (invmaponpathsweq (weq_from_fully_faithful fH a a0')).
      simpl; repeat rewrite functor_comp.
      inv_functor fH a a0.
      inv_functor fH a' a0'.
      apply pathsinv0, alpha.
    intermediate_path (#F (fH^-1 h· f)).
      rewrite functor_comp.
      apply idpath.
    rewrite HH4.
    rewrite functor_comp.
    apply idpath.
  set (Ybla := tpair _ (idtoiso (phi a0) · #F f · inv_from_iso (idtoiso (phi a0')))
                    PSIf : Y (#H f)).
  set (Ycontr := pr2 (Y_iscontr _ _ (#(pr1 H) f)) Ybla).
  set (Ycontr2 := base_paths _ _ Ycontr); simpl in *.
  change (G (#H f)) with (G (#(pr1 H) f)).
  rewrite <- Ycontr2.
  repeat rewrite assoc.
  rewrite iso_after_iso_inv, id_left.
  repeat rewrite <- assoc.
  rewrite iso_after_iso_inv, id_right.
  apply idpath.
Qed.




End preimage.

End essentially_surjective.


(** * Precomposition with an ess. surj. and f. f. functor is ess. surj. *)
(** Abstracting from [F] by closing the previous section,
    we can prove essential surjectivity of [_ O H]. *)

Lemma pre_composition_essentially_surjective (hsB: has_homsets B) :
       essentially_surjective (pre_composition_functor A B C hsB (pr2 Ccat) H).
Proof.
  intros F p' f.
  apply f.
  exists (GG F).
  apply idtoiso.
  apply is_preimage_for_pre_composition.
Qed.

End precomp_w_ess_surj_ff_is_ess_surj.
