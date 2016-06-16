Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.
Require Import UniMath.Foundations.Basics.UnivalenceAxiom.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.

Local Notation "a --> b" := (precategory_morphisms a b)(at level 50).
Local Notation "f ;; g" := (compose f g) (at level 50, format "f  ;;  g").
Local Notation "[ C , D , hs ]" := (functor_precategory C D hs).
Local Notation "# F" := (functor_on_morphisms F)(at level 3).

(* General lemmas that should probably go somewhere else *)

Lemma eqweq_twice_is_eqweq_of_comp {A B C : UU}
      (p : A = B) (q : B = C)
  : weqcomp (eqweqmap p) (eqweqmap q)
    = eqweqmap (pathscomp0 p q).
Proof.
  induction p.
  eapply total2_paths.
    apply isapropisweq.
    Unshelve.
  reflexivity.
Defined.

Lemma eqweqfun_twice_is_eqweqfun_of_comp {A B C : UU}
      (p : A = B) (q : B = C) (a : A)
  : (eqweqmap q) ((eqweqmap p) a)
    = eqweqmap (pathscomp0 p q) a.
Proof.
  induction p.
  reflexivity.
Defined.

Lemma inv_idweq_is_idweq {A : UU} :
  idweq A = invweq (idweq A).
Proof.
  eapply total2_paths.
  apply isapropisweq.
  Unshelve.
  reflexivity.
Defined.

Lemma eqweq_of_inverse {A B : UU} (p : A = B)
  : eqweqmap (!p) = invweq (eqweqmap p).
Proof.
  induction p.
  exact inv_idweq_is_idweq.
Defined.

Lemma total2_paths2_b {A : UU} {B : A -> UU} {a1 : A} {b1 : B a1}
  {a2 : A} {b2 : B a2} (p : a1 = a2)
  (q : b1 = transportb B p b2) : a1,,b1 = a2,,b2.
Proof.
  intros.
  apply (@total2_paths_b _ _
    (tpair (fun x => B x) a1 b1) (tpair (fun x => B x) a2 b2) p q).
Defined.

Definition transportb_dirprod (A : UU) (B B' : A -> UU)
  (x x' : Σ a,  B a × B' a)  (p : pr1 x = pr1 x') :
  transportb (fun a => dirprod (B a) (B' a)) p (pr2 x') =
    dirprodpair (transportb (fun a => B a) p (pr1 (pr2 x')))
                (transportb (fun a => B' a) p (pr2 (pr2 x'))).
Proof.
  apply transportf_dirprod.
Defined.

(******************************************************************************)
(** * Isomorphism of (pre)categories *)
(* (as defined in the paper) *)

Definition is_catiso {A B : precategory_data}
  (F : functor A B)
  := (fully_faithful F) × (isweq (functor_on_objects F)).

Lemma isaprop_is_catiso
  {A B : precategory_data}
  {F : functor A B}
  : isaprop (is_catiso F).
Proof.
  apply isapropdirprod.
  - apply isaprop_fully_faithful.
  - apply isapropisweq.
Defined.

Definition catiso (A B : precategory_data)
  := total2 (fun F : functor A B => is_catiso F).

Definition functor_from_catiso (A B : precategory_data)
  (F : catiso A B)
  : functor A B := pr1 F.
Coercion functor_from_catiso :
  catiso >-> functor.

Definition catiso_ob_weq {A B : precategory_data}
  (F : catiso A B)
  : weq (ob A) (ob B)
  := weqpair (functor_on_objects F) (pr2 (pr2 F)).

Definition catiso_to_precategory_ob_path {A B : precategory_data}
  (F : catiso A B)
  : ob A = ob B
  := (invmap (univalence _ _) (catiso_ob_weq F)).

Definition catiso_fully_faithful_weq {A B : precategory_data}
  (F : catiso A B)
  : forall a a' : A, weq (a --> a') (F a --> F a')
  := fun a a' => (weqpair (functor_on_morphisms F) (pr1 (pr2 F) a a')).

Lemma catiso_fully_faithful_path {A B : precategory_data}
  (F : catiso A B)
  : forall a a' : A, (a --> a') = (F a --> F a').
Proof.
  intros a a'.
  apply (invmap (univalence _ _)).
  apply (catiso_fully_faithful_weq F).
Defined.

(******************************************************************************)
(** * Construction of a map (catiso A B) -> (A = B) *)

Lemma eqweq_ob_path_is_functor_app {A B : precategory_data}
  (F : catiso A B)
  : forall a : A, eqweqmap (catiso_to_precategory_ob_path F) a = F a.
Proof.
  intros a.
  unfold catiso_to_precategory_ob_path.

  set (W := (@homotweqinvweq _ _  (univalence (ob A) (ob B)))).
  simpl in W.
  rewrite W.

  reflexivity.
Defined.

Lemma correct_hom_weq {A B : precategory}
  (F : catiso A B)
  : forall a a' : A,
      weq (F a --> F a')
          ((eqweqmap (catiso_to_precategory_ob_path F) a) -->
           (eqweqmap (catiso_to_precategory_ob_path F) a')).
Proof.
  intros a a'.

  apply (weqcomp (Y := F a --> (eqweqmap (catiso_to_precategory_ob_path F)) a')).
  apply iso_comp_left_weq.
  apply idtoiso.
  apply pathsinv0.
  apply eqweq_ob_path_is_functor_app.
  apply iso_comp_right_weq.
  apply idtoiso.
  apply eqweq_ob_path_is_functor_app.
Defined.

Lemma transport_mor {A B : UU} (B1 : B -> B -> UU) (p : A = B) :
  forall a a' : A, B1 (eqweqmap p a) (eqweqmap p a') = (transportb (fun T => T -> T -> UU) p B1) a a'.
Proof.
  induction p.
  reflexivity.
Defined.

Lemma catiso_to_precategory_mor_path {A B : precategory}
  (F : catiso A B)
  : forall a a',  (precategory_morphisms (C:=A)) a a'
  = transportb (fun T => T -> T -> UU) (catiso_to_precategory_ob_path F)
    (precategory_morphisms (C:=B)) a a'.
Proof.
  intros a.
  intros a'.

  eapply pathscomp0.
    apply (invmap (univalence _ ((eqweqmap (catiso_to_precategory_ob_path F) a) -->
           (eqweqmap (catiso_to_precategory_ob_path F) a')))).
    apply (weqcomp (Y:= (F a --> F a'))).
    apply (catiso_fully_faithful_weq F).
    apply correct_hom_weq.
  eapply pathscomp0. apply transport_mor.

  reflexivity.
Defined.

Lemma catiso_to_precategory_mor_path_funext {A B : precategory}
  (F : catiso A B)
  : (precategory_morphisms (C:=A))
  = transportb (fun T => T -> T -> UU) (catiso_to_precategory_ob_path F)
    (precategory_morphisms (C:=B)).
Proof.
  apply funextsec.
  intros a.
  apply funextsec.
  intros a'.
  apply (catiso_to_precategory_mor_path F).
Defined.

Definition catiso_to_precategory_ob_mor_path {A B : precategory}
  (F : catiso A B)
  : precategory_ob_mor_from_precategory_data A = precategory_ob_mor_from_precategory_data B
  := total2_paths_b (catiso_to_precategory_ob_path F) (catiso_to_precategory_mor_path_funext F).

Lemma transport_id {A0 B0 : UU} (p0 : A0 = B0)
  (A1 : A0 -> A0 -> UU) (B1 : B0 -> B0 -> UU) (p1 : A1 = transportb _ p0 B1)
  (idB : forall b : B0, B1 b b)
  : forall a : A0, (transportb (X := total2 (fun T => T -> T -> UU)) (fun T => forall a, (pr2 T) a a) (total2_paths2_b p0 p1) idB) a
              = (eqweqmap ((transport_mor B1 p0 _ _) @ !weqtoforallpaths _ _ _ (weqtoforallpaths _ _ _ p1 a) a)) (idB (eqweqmap p0 a)).
Proof.
  induction p0.
  rewrite p1.
  reflexivity.
Defined.

Lemma catiso_to_precategory_id_path {A B : precategory}
  (F : catiso A B)
  : forall a : A,
    (transportb (X := total2 (fun T => T -> T -> UU)) (fun T => forall a, (pr2 T) a a) (total2_paths2_b (catiso_to_precategory_ob_path F) (catiso_to_precategory_mor_path_funext F))
     identity) a
   = identity a.
Proof.
  intros a.

  eapply pathscomp0. apply transport_id.

  unfold catiso_to_precategory_mor_path_funext.
  unfold catiso_to_precategory_mor_path.
  unfold funextsec.
  rewrite !(homotweqinvweq (weqtoforallpaths _ _ _)).

  rewrite pathscomp_inv.
  rewrite pathscomp_inv.
  rewrite path_assoc.
  rewrite path_assoc.
  simpl.
  rewrite pathscomp0rid.
  rewrite pathsinv0r.
  simpl.

  apply pathsweq1'.
  rewrite eqweq_of_inverse.
  rewrite invinv.

  set (W := (@homotweqinvweq _ _  (univalence (a --> a)
            ((eqweqmap (catiso_to_precategory_ob_path F)) a -->
             (eqweqmap (catiso_to_precategory_ob_path F)) a)))).
  simpl in W.
  rewrite W.
  clear W.

  unfold weqcomp.
  simpl.

  rewrite functor_id.

  rewrite !id_left.
  rewrite idtoiso_inv.
  simpl.
  rewrite iso_inv_after_iso.
  reflexivity.
Defined.

Lemma transport_comp_thing {A0 B0 : UU} (p0 : A0 = B0)
  (A1 : A0 -> A0 -> UU) (B1 : B0 -> B0 -> UU) (p1 : A1 = transportb (fun T => T -> T -> UU) p0 B1)
  : forall a a' a'' : A0,
    ( B1 (eqweqmap p0 a) (eqweqmap p0 a') -> B1 (eqweqmap p0 a') (eqweqmap p0 a'') -> B1 (eqweqmap p0 a) (eqweqmap p0 a''))
  -> ( A1 a a' -> A1 a' a'' -> A1 a a'').
Proof.
  intros a a' a''.
  intros Bhom.
  intros f g.

  set (X := fun a a' => (transport_mor B1 p0 a a') @ (! weqtoforallpaths _ _ _ (weqtoforallpaths _ _ _ p1 a) a') ).

  apply (eqweqmap (X a a'')).
  apply Bhom.

  apply (eqweqmap (! X a a')).
  exact f.

  apply (eqweqmap (! X a' a'')).
  exact g.
Defined.

Lemma transport_comp {A0 B0 : UU} (p0 : A0 = B0)
  (A1 : A0 -> A0 -> UU) (B1 : B0 -> B0 -> UU) (p1 : A1 = transportb _ p0 B1)
  (compB : forall b b' b'' : B0, B1 b b' -> B1 b' b'' -> B1 b b'')
  : forall a a' a'' : A0,
      (transportb (X := total2 (fun T => T -> T -> UU)) (fun T => forall a b c, (pr2 T) a b -> (pr2 T) b c -> (pr2 T) a c) (total2_paths2_b p0 p1) compB) a a' a''
    = transport_comp_thing p0 A1 B1 p1 a a' a'' (compB (eqweqmap p0 a) (eqweqmap p0 a') (eqweqmap p0 a'') ).
Proof.
  induction p0.
  rewrite p1.
  reflexivity.
Defined.

Lemma catiso_to_precategory_comp_path {A B : precategory}
  (F : catiso A B)
  : forall a a' a'' : A,
    (transportb (X := total2 (fun T => T -> T -> UU)) (fun T => forall a b c : (pr1 T), (pr2 T) a b -> (pr2 T) b c -> (pr2 T) a c) (total2_paths2_b (catiso_to_precategory_ob_path F) (catiso_to_precategory_mor_path_funext F))
     (@compose B)) a a' a''
   = (@compose A a a' a'').
Proof.
  intros a a' a''.

  eapply pathscomp0. apply transport_comp.
  apply funextsec. intros f.
  apply funextsec. intros g.

  unfold transport_comp_thing.

  unfold catiso_to_precategory_mor_path_funext.
  unfold funextsec.
  rewrite !(homotweqinvweq (weqtoforallpaths _ _ _)).

  unfold catiso_to_precategory_mor_path.

  (* Cancel as much as possible *)
  rewrite !pathscomp0rid.
  rewrite !pathscomp_inv.
  rewrite !pathsinv0inv0.
  rewrite path_assoc.
  rewrite pathsinv0r.
  simpl.
  rewrite <- path_assoc.
  rewrite pathsinv0r.
  rewrite pathscomp0rid.

  rewrite <- path_assoc.

  rewrite pathsinv0r.
  rewrite pathscomp0rid.

  apply pathsweq1'.
  rewrite eqweq_of_inverse.
  rewrite invinv.

  set (W := fun a a' => (@homotweqinvweq _ _  (univalence (a --> a')
            ((eqweqmap (catiso_to_precategory_ob_path F)) a -->
             (eqweqmap (catiso_to_precategory_ob_path F)) a')))).
  simpl in W.
  rewrite (W a a').
  rewrite (W a' a'').
  rewrite (W a a'').
  clear W.

  simpl.

  rewrite functor_comp.

  rewrite idtoiso_inv.
  simpl.

  rewrite assoc.
  rewrite assoc4.
  rewrite assoc.
  rewrite assoc4.
  rewrite assoc4.

  rewrite iso_after_iso_inv.
  rewrite id_right.

  rewrite !assoc.
  reflexivity.
Defined.

Lemma catiso_to_precategory_data_path {A B : precategory}
  (F : catiso A B)
  : precategory_data_from_precategory A
    = precategory_data_from_precategory B.
Proof.
  destruct A as [[[Ao Am] [Ai Ac]] Aax].
  destruct B as [[[Bo Bm] [Bi Bc]] Bax].

  eapply total2_paths_b. Unshelve. Focus 2. simpl.
  - exact (catiso_to_precategory_ob_mor_path F).
  - apply pathsinv0.
    eapply pathscomp0.
    apply (transportb_dirprod _ _ _ _ _ (catiso_to_precategory_ob_mor_path F)).
    apply dirprodeq.
    + apply funextsec.
      apply (catiso_to_precategory_id_path F).
    + apply funextsec.
      intro.
      apply funextsec.
      intro.
      apply funextsec.
      intro.
      apply (catiso_to_precategory_comp_path F).
Defined.

Lemma catiso_to_precategory_path {A B : precategory}
  (hs : has_homsets A)
  (F : catiso A B)
  : A = B.
Proof.
  eapply total2_paths_b. Unshelve. Focus 2. simpl.
  - exact (catiso_to_precategory_data_path F).
  - apply proofirrelevance.
    apply isaprop_is_precategory.
    apply hs.
Defined.
