Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Local Open Scope cat.
Require Import UniMath.CategoryTheory.whiskering.

(******************************************************************************)
(** * Isomorphism of (pre)categories *)
(* (as defined in the paper) *)

Definition is_catiso {A B : precategory_data}
  (F : functor A B)
  := (fully_faithful F) × (isweq (functor_on_objects F)).

Definition catiso (A B : precategory_data)
  := total2 (λ F : functor A B, is_catiso F).

Lemma isaprop_is_catiso
  {A B : precategory_data}
  {F : functor A B}
  : isaprop (is_catiso F).
Proof.
  apply isapropdirprod.
  - apply isaprop_fully_faithful.
  - apply isapropisweq.
Defined.

Definition functor_from_catiso (A B : precategory_data)
  (F : catiso A B)
  : functor A B := pr1 F.
Coercion functor_from_catiso :
  catiso >-> functor.

Definition identity_catiso (A : precategory_data)
  : catiso A A.
Proof.
  use tpair.
  - exact (functor_identity A).
  - use tpair.
    + apply identity_functor_is_fully_faithful.
    + apply idisweq.
Defined.

Definition catiso_ob_weq {A B : precategory_data}
  (F : catiso A B)
  : (ob A) ≃ (ob B)
  := weqpair (functor_on_objects F) (pr2 (pr2 F)).

Definition catiso_to_precategory_ob_path {A B : precategory_data}
  (F : catiso A B)
  : ob A = ob B
  := (invmap (univalence _ _) (catiso_ob_weq F)).

Definition catiso_fully_faithful_weq {A B : precategory_data}
  (F : catiso A B)
  : forall a a' : A, (a --> a') ≃ (F a --> F a')
  := λ a a', (weqpair (functor_on_morphisms F) (pr1 (pr2 F) a a')).

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

(* The path "p : ob A = ob B" is clear. The next task is to construct a path
   "A a a' = (transportb p B) a a'" for all a, a' : A. We transport backwards
   because the fully faithfulness of the functor applies more naturally this way  *)

(* Let "w (= eqweqmap) : (X = Y) -> (X -> Y)" be the canonical map *)
(* The path "A a a' = (transportb p B) a a'" is constructed in three pieces. *)
(*     a --> a *)
(*   = F a --> F a' *)
(*   = w(p) a --> w(p) a' *)
(*   = (transportb p B) a a' *)

Lemma correct_hom {A B : precategory_data}
  (F : catiso A B)
  : forall a a' : A,
      F a --> F a'
      = (eqweqmap (catiso_to_precategory_ob_path F) a) -->
        (eqweqmap (catiso_to_precategory_ob_path F) a').
Proof.
  intros a a'.
  set (W := (!(homotweqinvweq (univalence _ _)) (catiso_ob_weq F))).
  exact (maponpaths (λ T, (pr1weq T) a --> (pr1weq T) a') W ).
Defined.

(* w(p) a = F a *)
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

Lemma eqweq_maponpaths_mor {A B : precategory}
  (F G : A ≃ B) (p : F = G) (a a' : A) (f : F a --> F a')
  : eqweqmap (maponpaths (λ T : A ≃ B, (pr1 T) a --> (pr1 T) a') p) f
    =    (idtomor _ _ (!toforallpaths _ _ _ (maponpaths pr1 p) a))
      · f
      · (idtomor _ _ (toforallpaths _ _ _ (maponpaths pr1 p) a')).
Proof.
  induction p.
  rewrite id_left.
  rewrite id_right.
  reflexivity.
Defined.

Lemma eqweq_correct_hom_is_comp {A B : precategory}
  (F : catiso A B)
  : forall a a' : A, forall f : F a --> F a',
      eqweqmap (correct_hom F _ _) f
    =    (idtomor _ _ (eqweq_ob_path_is_functor_app F a))
      · f
      · (idtomor _ _ (!eqweq_ob_path_is_functor_app F a')).
Proof.
  intros a a' f.
  unfold correct_hom.

  rewrite (eqweq_maponpaths_mor
             _
             _
             (! homotweqinvweq (univalence A B) (catiso_ob_weq F))
             a a').

  unfold catiso_to_precategory_ob_path.
  unfold eqweq_ob_path_is_functor_app.
  simpl.

  set (W := (@homotweqinvweq _ _  (univalence (ob A) (ob B)))(catiso_ob_weq F)).
  simpl in W.
  rewrite W.

  reflexivity.
Defined.

Lemma eqweq_fully_faithful_is_functor_app {A B : precategory_data}
  (F : catiso A B)
  : forall a a' : A,
    eqweqmap (catiso_fully_faithful_path F a a')
    = catiso_fully_faithful_weq F _ _.
Proof.
  intros a a'.
  unfold catiso_fully_faithful_path.

  set (W := (@homotweqinvweq _ _  (univalence (a --> a') (F a --> F a')))).
  simpl in W.
  rewrite W.

  reflexivity.
Defined.

Lemma transport_mor {A B : UU} (B1 : B -> B -> UU) (p : A = B) :
  forall a a' : A,
    B1 (eqweqmap p a) (eqweqmap p a')
  = (transportb (λ T, T -> T -> UU) p B1) a a'.
Proof.
  induction p.
  reflexivity.
Defined.

Lemma catiso_to_precategory_mor_path {A B : precategory_data}
  (F : catiso A B)
  : forall a a',  (precategory_morphisms (C:=A)) a a'
  = transportb (λ T, T -> T -> UU) (catiso_to_precategory_ob_path F)
    (precategory_morphisms (C:=B)) a a'.
Proof.
  intros a.
  intros a'.

  eapply pathscomp0. apply (catiso_fully_faithful_path F).
  eapply pathscomp0. apply correct_hom.
  eapply pathscomp0. apply transport_mor.

  reflexivity.
Defined.

Lemma catiso_to_precategory_mor_path_funext {A B : precategory_data}
  (F : catiso A B)
  : (precategory_morphisms (C:=A))
  = transportb (λ T, T -> T -> UU) (catiso_to_precategory_ob_path F)
    (precategory_morphisms (C:=B)).
Proof.
  apply (pr1 (weqfunextsec _ _ _)).
  intros a.
  apply (pr1 (weqfunextsec _ _ _)).
  intros a'.
  apply (catiso_to_precategory_mor_path F).
Defined.

Definition catiso_to_precategory_ob_mor_path {A B : precategory_data}
  (F : catiso A B)
  : precategory_ob_mor_from_precategory_data A = precategory_ob_mor_from_precategory_data B
  := total2_paths_b (catiso_to_precategory_ob_path F) (catiso_to_precategory_mor_path_funext F).

(* Remains to show that identity and composition transport correctly. *)

Lemma transport_id {A0 B0 : UU} (p0 : A0 = B0)
  (A1 : A0 -> A0 -> UU) (B1 : B0 -> B0 -> UU) (p1 : A1 = transportb _ p0 B1)
  (idB : forall b : B0, B1 b b)
  : forall a : A0,
    (transportb (X := total2 (λ T, T -> T -> UU))
                (λ T, forall a, (pr2 T) a a)
                (total2_paths2_b p0 p1) idB) a
  = (eqweqmap (  (transport_mor B1 p0 _ _)
               @ !weqtoforallpaths _ _ _ (weqtoforallpaths _ _ _ p1 a) a))
    (idB (eqweqmap p0 a)).
Proof.
  induction p0.
  rewrite p1.
  reflexivity.
Defined.

Lemma correct_hom_on_id {A B : precategory}
  (F : catiso A B)
  : forall a,
    identity ((eqweqmap (catiso_to_precategory_ob_path F)) a) =
    (eqweqmap (correct_hom F a a)) (identity (F a)).
Proof.
  intros a.

  apply pathsinv0.
  eapply pathscomp0. apply eqweq_correct_hom_is_comp.

  rewrite (eqweq_ob_path_is_functor_app F).
  rewrite !id_left.

  reflexivity.
Defined.

Lemma catiso_to_precategory_id_path {A B : precategory}
  (F : catiso A B)
  : forall a : A,
    (transportb (X := total2 (λ T, T -> T -> UU))
                (λ T, forall a, (pr2 T) a a)
                (total2_paths2_b (catiso_to_precategory_ob_path F)
                                 (catiso_to_precategory_mor_path_funext F))
     identity) a
   = identity a.
Proof.
  intros a.

  eapply pathscomp0. apply transport_id.

  (* Cancel funext *)
  unfold catiso_to_precategory_mor_path_funext.
  unfold catiso_to_precategory_mor_path.
  unfold weqfunextsec.
  simpl (pr1 _).
  rewrite !(homotweqinvweq (weqtoforallpaths _ _ _)).

  (* Cancel transport_mor with its inverse *)
  rewrite pathscomp_inv.
  rewrite pathscomp_inv.
  rewrite path_assoc.
  rewrite path_assoc.
  rewrite pathscomp0rid.
  rewrite pathsinv0r.
  simpl.

  (* Get into a form we can apply correct_hom_on_id *)
  apply pathsweq1'.
  rewrite <- pathscomp_inv.
  rewrite eqweqmap_pathsinv0.
  rewrite invinv.

  rewrite <- eqweqmap_pathscomp0.

  rewrite (eqweq_fully_faithful_is_functor_app F a a).
  simpl.

  rewrite functor_id.
  apply correct_hom_on_id.
Defined.

(* We want to prove a similar lemma to transport_mor. The following is
   the type on the RHS of the path. *)
Lemma transport_comp_target {A0 B0 : UU} (p0 : A0 = B0)
  (A1 : A0 -> A0 -> UU) (B1 : B0 -> B0 -> UU) (p1 : A1 = transportb (λ T, T -> T -> UU) p0 B1)
  : forall a a' a'' : A0,
    (   B1 (eqweqmap p0 a) (eqweqmap p0 a')
      -> B1 (eqweqmap p0 a') (eqweqmap p0 a'')
      -> B1 (eqweqmap p0 a) (eqweqmap p0 a''))
  -> ( A1 a a' -> A1 a' a'' -> A1 a a'').
Proof.
  intros a a' a''.
  intros Bhom.
  intros f g.

  set (X := λ a a', (transport_mor B1 p0 a a')
                    @ (! weqtoforallpaths _ _ _ (weqtoforallpaths _ _ _ p1 a) a') ).

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
      (transportb (X := total2 (λ T, T -> T -> UU))
                  (λ T, forall a b c, (pr2 T) a b -> (pr2 T) b c -> (pr2 T) a c)
                  (total2_paths2_b p0 p1) compB)
        a a' a''
    = transport_comp_target p0 A1 B1 p1 a a' a''
        (compB (eqweqmap p0 a) (eqweqmap p0 a') (eqweqmap p0 a'')).
Proof.
  induction p0.
  rewrite p1.
  reflexivity.
Defined.

Lemma correct_hom_on_comp {A B : precategory}
  (F : catiso A B)
  : forall a a' a'', forall f : F a --> F a', forall g : F a' --> F a'',
       (eqweqmap (correct_hom F _ _)) f
    · (eqweqmap (correct_hom F _ _)) g
    =  (eqweqmap (correct_hom F _ _)) (f · g).
Proof.
  intros a a' a'' f g.

  rewrite !eqweq_correct_hom_is_comp.
  rewrite !(eqweq_ob_path_is_functor_app F).
  rewrite !id_left.
  rewrite !id_right.

  reflexivity.
Defined.

Lemma catiso_to_precategory_comp_path {A B : precategory}
  (F : catiso A B)
  : forall a a' a'' : A,
    (transportb (X := total2 (λ T, T -> T -> UU))
                (λ T, forall a b c : (pr1 T), (pr2 T) a b -> (pr2 T) b c -> (pr2 T) a c)
                (total2_paths2_b (catiso_to_precategory_ob_path F)
                                 (catiso_to_precategory_mor_path_funext F))
     (@compose B)) a a' a''
   = (@compose A a a' a'').
Proof.
  intros a a' a''.

  eapply pathscomp0. apply transport_comp.
  apply funextsec. intros f.
  apply funextsec. intros g.

  unfold transport_comp_target.

  (* Cancel funext *)
  unfold catiso_to_precategory_mor_path_funext.
  simpl.

  set (W := homotweqinvweq
              (weqtoforallpaths (λ _ : A, A -> UU)
                                precategory_morphisms
                                (transportb (λ T, T -> T -> UU)
                                            (catiso_to_precategory_ob_path F)
                                            precategory_morphisms))).
  simpl in W. rewrite !W. clear W.

  set (W := homotweqinvweq
              (weqtoforallpaths (λ _ : A, UU)
                                (precategory_morphisms a)
                                (transportb (λ T, T -> T -> UU)
                                            (catiso_to_precategory_ob_path F)
                                            precategory_morphisms a))).
  simpl in W. rewrite !W. clear W.

  set (W := homotweqinvweq
              (weqtoforallpaths (λ _ : A, UU)
                                (precategory_morphisms a')
                                (transportb (λ T, T -> T -> UU)
                                            (catiso_to_precategory_ob_path F)
                                            precategory_morphisms a'))).
  simpl in W. rewrite !W. clear W.

  (* Cancel as much as possible *)
  unfold catiso_to_precategory_mor_path.
  rewrite !pathscomp0rid.
  rewrite !pathscomp_inv.
  rewrite !pathsinv0inv0.
  rewrite path_assoc.
  rewrite path_assoc.
  rewrite pathsinv0r.
  simpl.
  rewrite <- path_assoc.
  rewrite <- path_assoc.
  rewrite pathsinv0r.
  rewrite pathscomp0rid.
  rewrite <- path_assoc.
  rewrite <- path_assoc.
  rewrite pathsinv0r.
  rewrite pathscomp0rid.
  rewrite <- pathscomp_inv.

  (* Rearrange to get into a form to apply correct_hom_on_comp *)
  apply pathsweq1'.
  rewrite eqweqmap_pathsinv0.
  rewrite invinv.

  rewrite <- !eqweqmap_pathscomp0.
  rewrite !eqweq_fully_faithful_is_functor_app.
  simpl.
  rewrite functor_comp.

  apply (correct_hom_on_comp F).
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
      intros a.
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
