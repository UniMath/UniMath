(** * Isomorphism of (pre)categories

    As in "Univalent categories and the Rezk completion" by
    Benedikt Ahrens, Chris Kapulkin, Michael Shulman (arXiv:1303.0584).
 *)

(** ** Contents

- Definitions
- Construction of a map (catiso A B) -> (A = B)
- Univalence for categories (catiso A B ≃ A = B)
  - Characterization of paths for [precategory_ob_mor]
  - Characterization of paths for [precategory_data] (not yet complete)
  - Characterization of paths for [category]:
    categories are equal just when their [precategory_data] are
  - Characterization of paths for [univalent_category]:
    similar to the case of [category].
  - Univalence for categories (not yet complete)
 *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.whiskering.

(* The following are used in the characterization of paths *)
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.MoreFoundations.Univalence.
Require Import UniMath.MoreFoundations.WeakEquivalences.

Local Open Scope cat.

(** ** Definitions *)

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

(** ** Construction of a map (catiso A B) -> (A = B) *)

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
  assert (W := (!(homotweqinvweq (univalence _ _)) (catiso_ob_weq F))).
  exact (maponpaths (λ T, (pr1weq T) a --> (pr1weq T) a') W ).
Defined.

(* w(p) a = F a *)
Lemma eqweq_ob_path_is_functor_app {A B : precategory_data}
  (F : catiso A B)
  : forall a : A, eqweqmap (catiso_to_precategory_ob_path F) a = F a.
Proof.
  intros a.
  exact (! toforallpaths (λ _ : A, B) F
    (pr1 (eqweqmap (invmap (univalence A B) (catiso_ob_weq F))))
    (maponpaths pr1 (! homotweqinvweq (univalence A B) (catiso_ob_weq F))) a).
Defined.

Lemma eqweq_ob_path_is_functor_app_compute
  (A B : precategory)
  (F : catiso A B)
  (a a' : A)
  (f : B ⟦ F a, F a' ⟧):
  eqweq_ob_path_is_functor_app F a =
  ! toforallpaths (λ _ : A, B) F
      (pr1weq (eqweqmap (invmap (univalence A B) (catiso_ob_weq F))))
      (maponpaths pr1weq (! homotweqinvweq (univalence A B) (catiso_ob_weq F))) a.
Proof.
  unfold eqweq_ob_path_is_functor_app.
Abort.

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
  rewrite (eqweq_maponpaths_mor _ _
             (! homotweqinvweq (univalence A B) (catiso_ob_weq F))
             a a').
  apply maponpaths. apply maponpaths.
  unfold eqweq_ob_path_is_functor_app.
  rewrite pathsinv0inv0.
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

  assert (W := (@homotweqinvweq _ _  (univalence (a --> a') (F a --> F a')))).
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
  intro.
  induction p0.
  change (transportb _ _ _) with B1 in p1.
  induction p1.
  simpl.
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

  induction (eqweq_ob_path_is_functor_app F a).
  simpl.
  rewrite 2 id_right.
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
  intros.
  induction p0.
  change (A1 = B1) in p1.
  induction p1.
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
  induction (eqweq_ob_path_is_functor_app F a).
  induction (eqweq_ob_path_is_functor_app F a').
  induction (eqweq_ob_path_is_functor_app F a'').
  rewrite 3 id_left.
  simpl.
  rewrite 3 id_right.
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

(** ** Univalence for categories (catiso A B ≃ A = B) (not yet complete) *)

Local Tactic Notation "≃" constr(H) "by" tactic(t) := intermediate_weq H; [t|].
Local Tactic Notation "≃'" constr(H) "by" tactic(t) := intermediate_weq H; [|t].
Local Tactic Notation "≃" constr(H) := intermediate_weq H.
Local Tactic Notation "≃'" constr(H) := apply invweq; intermediate_weq H.

(** *** Characterization of paths for [precategory_ob_mor] *)

(** This requires a lot of preliminary lemmas*)

Lemma weqtoforallpaths2 {X Y Z : UU} (f g : X → Y → Z) :
  f = g ≃ ∏ x y, f x y = g x y.
Proof.
  intermediate_weq (∏ x, f x = g x).
  - apply weqtoforallpaths.
  - apply weqonsecfibers; intro.
    apply weqtoforallpaths.
Defined.

Lemma isweq_uncurry {X Y Z : UU} : isweq (@uncurry X (λ _, Y) (λ _, Z)).
  use isweq_iso.
  - apply curry.
  - reflexivity.
  - reflexivity.
Defined.

Lemma transportf_uncurry {X Y : UU} (f : X → X → UU) (g : Y → Y → UU) (p : X = Y) :
      (transportf (λ Z : UU, Z → Z → UU) p f = g) ≃
      (transportf (λ Z : UU, Z × Z → UU) p (uncurry f) = (uncurry g)).
Proof.
  intermediate_weq
    (uncurry (Z := λ _, UU) (transportf (λ Z : UU, Z → Z → UU) p f) =
      uncurry (Z := λ _, UU) g).
  apply Injectivity, incl_injectivity, isinclweq, isweq_uncurry.
  apply transitive_paths_weq.
  abstract (induction p; reflexivity).
Defined.

Lemma transportb_uncurry {X Y : UU} (f : X → X → UU) (g : Y → Y → UU) (p : X = Y) :
      (transportb (λ Z : UU, Z → Z → UU) p g = f) ≃
      (transportb (λ Z : UU, Z × Z → UU) p (uncurry g) = (uncurry f)).
Proof.
  induction p; cbn; unfold idfun.
  apply Injectivity, incl_injectivity, isinclweq, isweq_uncurry.
Defined.

Lemma transportf_transpose_weq {X : UU} {P : X → UU} {x x' : X}
      (e : x = x') (y : P x) (y' : P x') :
      transportb P e y' = y ≃ y' = transportf P e y.
Proof.
  induction e; apply idweq.
Defined.

Definition pr1_eqweqmap2 { X Y } ( e: X = Y ) :
  pr1 (eqweqmap e) = transportf (λ T:Type, T) e.
Proof. intros. induction e. reflexivity. Defined.

Definition weqpath_transport {X Y} (w : X ≃ Y) :
  transportf (idfun UU) (weqtopaths w) = pr1 w.
Proof. intros. exact (!pr1_eqweqmap2 _ @ maponpaths pr1 (weqpathsweq w)). Defined.

(** Compare to [pr1_transportf]. *)
Lemma dirprod_pr2_transportf (A : UU) (B C : A -> UU)
  (a a' : A) (e : a = a') (xs : B a × C a):
  dirprod_pr2 (transportf (λ x, B x × C x) e xs) =
    transportf (λ x, C x) e (dirprod_pr2 xs).
Proof.
  destruct e; apply idpath.
Defined.

(** Equality between [precategory_ob_mor]s [(A,B)] is equivalent to a pair
    [(w1, w2)] of equivalences where
    - [w1] is an equivalence between their object types
    - for each pair [(a1, a2)] of objects, [w2] is an equivalence between their
      hom-type in [A] and the hom-type of their images under [w1] in [B].
    *)
Lemma precategory_ob_mor_paths_weq {A B : precategory_ob_mor} :
  A = B ≃ ∑ w : pr1 A ≃ pr1 B, ∏ a1 a2 : A, A ⟦ a1, a2 ⟧ ≃ B ⟦ w a1, w a2 ⟧.
Proof.
  ≃ (∑ w : pr1 A ≃ pr1 B, transportf _ (weqtopaths w) (pr2 A) = pr2 B)
    by apply (total2_paths_UU_equiv A B).
  apply weqfibtototal; intro w.

  ≃ (pr2 B = transportf (λ ob : UU, ob → ob → UU) (weqtopaths w) (pr2 A)).
  apply (weqpair _ (isweqpathsinv0 _ _)).
  ≃ (transportb (λ ob : UU, ob → ob → UU) (weqtopaths w) (pr2 B) = pr2 A).
  apply invweq, (transportf_transpose_weq (weqtopaths w) (pr2 A) (pr2 B)).

  ≃ (∏ a1 a2, transportb _ (weqtopaths w) (pr2 B) a1 a2 = pr2 A a1 a2) by
    apply weqtoforallpaths2.
  apply weqonsecfibers; intros a1.
  apply weqonsecfibers; intros a2.

  ≃' (A ⟦ a1, a2 ⟧ = B ⟦ w a1, w a2 ⟧) by apply univalence.
  ≃' (B ⟦ w a1, w a2 ⟧ = A ⟦ a1, a2 ⟧) by apply (weqpair _ (isweqpathsinv0 _ _)).
  apply transitive_paths_weq.

  generalize a2; apply toforallpaths.
  generalize a1; apply toforallpaths.
  eapply invweq.
  apply (transportb_uncurry (λ a1 a2, pr2 B (w a1) (w a2)) (pr2 B) (weqtopaths w)).

  apply funextsec; intros pair.
  refine (!@transportb_fun' _ _ UU (pr1 A) (pr1 B) (uncurry (pr2 B)) _ pair @ _).

  unfold uncurry; apply two_arg_paths.
  + refine (pr1_transportf UU _ _ _ _ _ pair @ _).
    refine (toforallpaths _ _ _ _ _).
    refine (weqpath_transport w @ _); reflexivity.
  + refine (dirprod_pr2_transportf UU _ _ _ _ _ _ @ _).
    refine (toforallpaths _ _ _ _ _).
    refine (weqpath_transport w @ _); reflexivity.
Defined.

(** *** Characterization of paths for [precategory_data] *)

Lemma precategory_id_comp_paths {C : precategory_ob_mor}
      (id1 id2 : precategory_id_comp C) :
  id1 = id2 ≃
  (∏ a : C, pr1 id1 a = pr1 id2 a) ×                 (* identities *)
  ∏ (a b c : C) (f : C ⟦ a, b ⟧) (g : C ⟦ b, c ⟧),   (* composition *)
    pr2 id1 a b c f g = pr2 id2 a b c f g.
Abort.

(** This is much harder than e.g univalence for rigs because it's a
    more deeply nested ∑-type. *)

Local Lemma precategory_data_rearrange :
  precategory_data ≃
  ∑ X : UU, ∑ Y : X → X → UU, precategory_id_comp (X ,, Y).
Proof.
  unfold precategory_data, precategory_ob_mor.
  apply weqtotal2asstor.
Defined.

Lemma precategory_data_paths_weq {A B : precategory_data} :
  A = B ≃
  ∑ w1 : pr1 A ≃ pr1 B,                                    (* objects *)
  ∑ w2 : ∏ a1 a2 : A, A ⟦ a1, a2 ⟧ ≃ B ⟦ w1 a1, w1 a2 ⟧,   (* hom-types *)
  ∏ a : A, w2 a a (identity a) = identity (w1 a) ×         (* identities *)
  ∏ (a b c : A) (f : A ⟦ a, b ⟧) (g : A ⟦ b, c ⟧),         (* composition *)
    w2 a c (f · g) = w2 a b f · w2 b c g.
Proof.
  (** Extract the underlying equivalence w1 *)
  ≃ (precategory_data_rearrange A = precategory_data_rearrange B) by
    (apply Injectivity, incl_injectivity, isinclweq, weqproperty).
  ≃ (∑ w : pr1 _ ≃ pr1 _,
      transportf _ (weqtopaths w) (pr2 (precategory_data_rearrange A)) =
      pr2 (precategory_data_rearrange B)) by
    apply (total2_paths_UU_equiv (precategory_data_rearrange A) _).
  apply weqfibtototal; intro w; cbn in w.
Abort.

(** *** Characterization of paths for [category]:
        categories are equal just when their [precategory_data] are *)

(** This helps us to apply [Injectivity] in [category_paths_weq].
    The reason is that [isaprop_is_precategory] relies on access to the hypothesis
    of hom-sets. *)
Local Lemma category_rearrange :
  category ≃ ∑ x : precategory_data, has_homsets x × is_precategory x.
Proof.
  unfold category, precategory.
  intermediate_weq (∑ x : precategory_data, is_precategory x × has_homsets x).
  - apply weqtotal2asstor.
  - apply weqfibtototal; intro.
    apply weqdirprodcomm.
Defined.

(** Again, we need the hypothesis of hom-sets to utilize [isaprop_is_precategory] *)
Local Lemma isapropdirprod' (X Y : UU) : isaprop X -> (X → isaprop Y) -> isaprop (X × Y).
Proof.
  intros isx isxy.
  apply invproofirrelevance; intros x y.
  apply pathsdirprod.
  apply isx.
  apply (isxy (dirprod_pr1 x)).
Defined.

(** Two categories are equal just when their data are. *)
Lemma category_paths_weq {A B : category} :
  (A = B) ≃
  (precategory_data_from_precategory A = precategory_data_from_precategory B).
  intermediate_weq (category_rearrange A = category_rearrange B).
  - apply Injectivity, incl_injectivity, isinclweq, weqproperty.
  - apply subtypeInjectivity; intro.
    apply isapropdirprod'.
    apply isaprop_has_homsets.
    intros ?; apply isaprop_is_precategory; assumption.
Defined.

(** *** Characterization of paths for [univalent_category]:
        similar to the case of [category]. *)

Lemma univalent_category_weq1 :
  univalent_category ≃
  ∑ C : precategory,
        has_homsets C × ∏ (a b : ob C), isweq (fun p : a = b => idtoiso p).
Proof.
  unfold univalent_category, is_univalent, category.
  apply weqfibtototal; intro.
  apply weqdirprodcomm.
Defined.

Lemma univalent_category_weq2 :
  univalent_category ≃
  ∑ C : category, ∏ (a b : ob C), isweq (fun p : a = b => idtoiso p).
Proof.
  unfold univalent_category, is_univalent, category.
  intermediate_weq
    (∑ C : precategory, has_homsets C × ∏ a b : C, isweq (λ p : a = b, idtoiso p)).
  - apply univalent_category_weq1.
  - apply invweq, weqtotal2asstor.
Defined.

(** Two univalent categories are equal just when their data are. *)
Lemma univalent_category_paths_weq (A B : univalent_category) :
  (A = B) ≃
  (precategory_data_from_precategory A = precategory_data_from_precategory B).
  (* It may be helpful to use the following to see implicit coercions: *)
  (* Set Printing Coercions. *)
  intermediate_weq
    (univalent_category_weq2 A = univalent_category_weq2 B).
  - apply Injectivity, incl_injectivity, isinclweq, weqproperty.
  - intermediate_weq (univalent_category_to_category A =
                      univalent_category_to_category B).
    apply subtypeInjectivity; intro.
    + do 2 (apply impred; intro); apply isapropisweq.
    + apply category_paths_weq.
Defined.

(** *** Univalence for categories *)

Lemma category_univalence1 {A B : category} :
  (precategory_data_from_precategory A = precategory_data_from_precategory B) ≃
  (catiso A B).
Abort.

Theorem category_univalence {A B : category} : (A = B) ≃ (catiso A B).
Abort.
