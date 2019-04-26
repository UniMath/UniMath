(** Univalent FOLDS

    Benedikt Ahrens, following notes by Michael Shulman

Contents of this file:

  - Definition: FOLDS pre-3-category
    - objects [ob] coerced, morphisms denoted by infix [⇒]
    - predicates for identity [I], composition [T], equality [E]
    - [E] is a congruence for [T] and [I], and [E] is an equivalence relation
    - usual categorical axioms

  - Definition: FOLDS pre-2-categoy
    - the fibers of [I], [T] and [E] are hProps

  - Isomorphism between morphisms in a FOLDS pre-2-category
    - Definition: given by a family of equivalences
    - Lemma: Type of isos [folds_2_iso f g] is a proposition (because [I], [T], [E] are)
    - Definition: Map [idtoiso2] from paths to isos

  - Lemma: In a FOLDS pre-2-category, [folds_2_iso f g] is equivalent to [E f g]
    - [E_implies_folds_iso]
    - [folds_iso_implies_E]

  - Definition: univalent FOLDS pre-2-category as special FOLDS pre-2-category
    - [idtoiso2] is an equivalence
    - [is_univalent_folds_2_precat] is an hProp

  - Definition: FOLDS precategory as special FOLDS pre-2-category
    - predicate [is_folds_precategory] defined as
      - hom-types are sets
      - axioms of category modul [=] rather than [E]

  - Lemma: Logical equivalence between being a FOLDS precategory and being univalent
    - since both are hProps, this entails equivalence between the types of
      - univalent FOLDS pre-2-cats
      - FOLDS precats
    - Implications are called
      - [is_univalent_implies_is_folds_precat] and
      - [is_folds_precat_implies_is_univalent]

*)

Require Import UniMath.Folds.UnicodeNotations.

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.


(* Require Import FOLDS.aux_lemmas. *)


Local Notation "p ## a" := (transportf _ p a) (at level 3, only parsing).


(** * The definition of a FOLDS pre-3-category *)

(** ** Objects and a dependent type of morphisms *)

Definition folds_3_ob_mor := ∑ a : UU, a → a → UU.
Definition make_folds_3_ob_mor (ob : UU)(mor : ob → ob → UU) : folds_3_ob_mor
  := tpair _ ob mor.

Definition ob (C : folds_3_ob_mor) : UU := @pr1 _ _ C.
Coercion ob : folds_3_ob_mor >-> UU.

Definition folds_3_morphisms {C : folds_3_ob_mor} : C → C → UU := pr2 C.
Local Notation "a ⇒ b" := (folds_3_morphisms a b).

Definition folds_double_transport {C : folds_3_ob_mor} {a a' b b' : ob C}
   (p : a = a') (q : b = b') (f : a ⇒ b) : a' ⇒ b' :=
  transportf (λ c, a' ⇒ c) q (transportf (λ c, c ⇒ b) p f).

(** ** Identity, composition, and equality, given through predicates *)
(** We do not assume those to be propositions.  *)

Definition folds_3_id_comp_eq := ∑ C : folds_3_ob_mor,
 ( (∏ a : C, a ⇒ a → UU)
 × (∏ (a b c : C), (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → UU))
 × ∏ a b : C, a ⇒ b → a ⇒ b → UU.


Definition folds_ob_mor_from_folds_id_comp (C : folds_3_id_comp_eq) : folds_3_ob_mor := pr1 C.
Coercion folds_ob_mor_from_folds_id_comp : folds_3_id_comp_eq >-> folds_3_ob_mor.

Definition I {C : folds_3_id_comp_eq} : ∏ {a : C}, a ⇒ a → UU := pr1 (pr1 (pr2 C)).
Definition T {C : folds_3_id_comp_eq} :
      ∏ {a b c : C}, (a ⇒ b) → (b ⇒ c) → (a ⇒ c) → UU := pr2 (pr1 (pr2 C)).
Definition E {C : folds_3_id_comp_eq} :
      ∏ {a b : C}, a ⇒ b → a ⇒ b → UU := pr2 (pr2 C).

(** ** E is an "equality", i.e. a congruence and equivalence *)

Definition E_is_good_to_I_and_T (C : folds_3_id_comp_eq) : UU :=
  (((∏ (a b : C) (f : a ⇒ b), E f f) (* refl *)
 ×  (∏ (a b : C) (f g : a ⇒ b), E f g → E g f)) (* sym *)
×   (∏ (a b : C) (f g h : a ⇒ b), E f g → E g h → E f h))
×  ((∏ (a : C) (f g : a ⇒ a), E f g → I f → I g)
×   (∏ (a b c : C) (f f' : a ⇒ b) (g g' : b ⇒ c) (h h' : a ⇒ c),
                      E f f' → E g g' → E h h' → T f g h → T f' g' h')).

(** **  The axioms for identity *)

Definition folds_ax_id (C : folds_3_id_comp_eq) :=
     (∏ a : C, ∥ ∑ f : a ⇒ a, I f ∥ )  (* there is a thing satisfying I *)
 ×  ((∏ (a b : C) (f : a ⇒ b)(i : b ⇒ b), I i → T f i f) (* I is post neutral *)
  ×  (∏ (a b : C) (f : a ⇒ b)(i : a ⇒ a), I i → T i f f)). (* I is pre neutral *)

(** ** The axioms for composition *)

Definition folds_ax_comp (C : folds_3_id_comp_eq) :=
     (∏ {a b c : C} (f : a ⇒ b) (g : b ⇒ c), ∥ ∑ h : a ⇒ c, T f g h ∥ )
                                                        (* there is a composite *)
 × ( (∏ {a b c : C} {f : a ⇒ b} {g : b ⇒ c} {h k : a ⇒ c}, T f g h → T f g k → E h k )
                                                        (* composite is unique mod E *)
  ×  (∏ {a b c d : C} (f : a ⇒ b) (g : b ⇒ c) (h : c ⇒ d) (fg : a ⇒ c)
                      (gh : b ⇒ d) (fg_h : a ⇒ d) (f_gh : a ⇒ d),
       T f g fg → T g h gh → T fg h fg_h → T f gh f_gh → E f_gh fg_h)).
                                                        (* composition is assoc mod E *)

(** ** A FOLDS pre-3-category is a package of
  - identity [I]
  - composition [T]
  - equality [E]
  satisfying the categorical axioms modulo [E] and [E] is an "equality"
*)

Definition folds_pre_3_cat := ∑ C : folds_3_id_comp_eq,
     (folds_ax_id C
    × folds_ax_comp C)
    × E_is_good_to_I_and_T C.
Definition folds_id_comp_from_folds_precat (C : folds_pre_3_cat) : folds_3_id_comp_eq := pr1 C.
Coercion folds_id_comp_from_folds_precat : folds_pre_3_cat >-> folds_3_id_comp_eq.


(** * FOLDS-2-precategories *)
(** they are 3-precategories such that T, I and E are hProps *)

Definition is_folds_pre_2_cat (C : folds_pre_3_cat) :=
   ( (∏ (a : C) (i : a ⇒ a), isaprop (I i))
  ×  (∏ (a b c : C) (f : a ⇒ b) (g : b ⇒ c) (h : a ⇒ c), isaprop (T f g h)))
 ×   (∏ (a b : C) (f g : a ⇒ b), isaprop (E f g)).

Definition folds_pre_2_cat : UU := ∑ C, is_folds_pre_2_cat C.

Ltac folds_pre_2_cat_props C :=
     try apply (pr2 (pr1 (pr2 C)));
     try apply (pr1 (pr1 (pr2 C)));
     try apply (pr2 (pr2 C)).


Definition folds_3_from_folds_2 (C : folds_pre_2_cat) : folds_pre_3_cat := pr1 C.
Coercion folds_3_from_folds_2 : folds_pre_2_cat >-> folds_pre_3_cat.


(** * FOLDS-2-isomorphisms *)

Definition folds_iso {C: folds_pre_3_cat} {a b : C} (f g : a ⇒ b) : UU :=
(((∏ (x : C) (u : x ⇒ a) (v : x ⇒ b), T u f v ≃ T u g v)
  × (∏ (x : C) (u : a ⇒ x) (v : x ⇒ b), T u v f ≃ T u v g))
 × (∏ (x : C) (u : b ⇒ x) (v : a ⇒ x), T f u v ≃ T g u v))
× ((((∏ (u : a ⇒ b) (p : b = a), T p ## f f u ≃ T p ## g g u)
     × (∏ (u : b ⇒ b) (p : a = a), T (transportf (λ a, a ⇒ b) p f) u f ≃
                                   T (transportf (λ a, a ⇒ b) p g) u g))
    × ((∏ (u : a ⇒ a) (p : b = b), T u p ## f f ≃ T u p ## g g)
       × (∏ (p : a = a) (q : b = a) (r : b = b),
          T (folds_double_transport p q f) r ## f f
          ≃ T (folds_double_transport p q g) r ## g g)))
   × (((∏ p : b = a, I p ## f ≃ I p ## g) × (∏ u : a ⇒ b, E f u ≃ E g u))
      × ((∏ u : a ⇒ b, E u f ≃ E u g)
         × (∏ (p : a = a) (q : b = b),
            E (folds_double_transport p q f) f ≃ E (folds_double_transport p q g) g)))).

Lemma isaprop_folds_2_iso (C : folds_pre_2_cat) (a b : C) (f g : a ⇒ b) :
  isaprop (folds_iso f g).
Proof.
  repeat (apply isofhleveldirprod);
  repeat (apply impred; intro);
  apply isofhlevelsnweqtohlevelsn;
  folds_pre_2_cat_props C.
Qed.


Definition folds_2_iso_id (C : folds_pre_3_cat) (a b : C) (f : a ⇒ b) : folds_iso f f.
Proof.
  repeat split;
    intros; apply idweq.
Defined.


(** * In FOLDS-2-precats, [folds_iso f g <-> E f g] *)

Lemma E_transport_source : ∏ (C : folds_pre_2_cat) (a a' b : C) (f g : a ⇒ b) (p : a = a'),
          E f g → E (transportf (λ c, c ⇒ b) p f) (transportf (λ c, c ⇒ b) p g).
Proof.
  intros. destruct p.
  assumption.
Defined.

Lemma E_transport_target : ∏ (C : folds_pre_2_cat) (a b b' : C) (f g : a ⇒ b) (p : b = b'),
          E f g → E (transportf (λ c, a ⇒ c) p f) (transportf (λ c, a ⇒ c) p g).
Proof.
  intros. destruct p.
  assumption.
Defined.

Lemma E_implies_folds_iso (C : folds_pre_2_cat) (a b : C) (f g : a ⇒ b) : E f g → folds_iso f g.
Proof.
  set (H' := pr2 (pr2 (pr1 C))). simpl in H'.
  destruct H' as [[[Erefl Esym] Etrans] [EI ET]].
  intro Efg.
  repeat split; intros; apply weqimplimpl; intro; folds_pre_2_cat_props C.
  - apply (ET _ _ _  u u f g v v); auto.
  - apply (ET _ _ _ u u g f v v) ; auto.
  - apply (ET _ _ _ u u v v f g); auto.
  - apply (ET _ _ _ u u v v g f); auto.
  - apply (ET _ _ _ f g u u v v); auto.
  - apply (ET _ _ _ g f u u v v); auto.
  - destruct p;
    apply (ET _ _ _ f g f g u u); auto.
  - destruct p;
    apply (ET _ _ _ g f g f u u); auto.
  - apply (ET _ _ _ (transportf (λ c, c ⇒ b) p f) (p ## g) u u f g);
    try apply E_transport_source; auto.
  - apply (ET _ _ _ (transportf (λ c, c ⇒ b) p g) (p ## f) u u g f);
    try apply E_transport_source; auto.
  - apply (ET _ _ _ u u (transportf (λ c, a ⇒ c) p f) (p ## g) f g);
    try apply E_transport_target; auto.
  - apply (ET _ _ _ u u (transportf (λ c, a ⇒ c) p g) (p ## f) g f);
    try apply E_transport_target; auto.
  - apply (ET _ _ _ (folds_double_transport p q f) (folds_double_transport p q g)
                          (transportf (λ c, a ⇒ c) r f) (r ## g) f g);
    try apply E_transport_target; try apply E_transport_source; auto.
  - apply (ET _ _ _ (folds_double_transport p q g) (folds_double_transport p q f)
                          (transportf (λ c, a ⇒ c) r g) (r ## f) g f);
    try apply E_transport_target; try apply E_transport_source; auto.
  - destruct p. apply (EI _ f); auto.
  - destruct p; apply (EI _ g); auto.
  - apply (Etrans _ _ g f u).
    + apply Esym; auto.
    + auto.
  - apply (Etrans _ _ f g u); auto.
  - apply (Etrans _ _ u f g); auto.
  - apply (Etrans _ _ u g f).
    + auto.
    + apply Esym; auto.
  - apply (Etrans _ _ (folds_double_transport p q g) (folds_double_transport p q f) g).
    + apply E_transport_target. apply E_transport_source. apply Esym; auto.
    + apply (Etrans _ _ (folds_double_transport p q f) f g); auto.
  - apply (Etrans _ _ (folds_double_transport p q f) (folds_double_transport p q g) f).
    + apply E_transport_target. apply E_transport_source. auto.
    + apply (Etrans _ _ (folds_double_transport p q g) g f); auto.
Qed.

Lemma folds_iso_implies_E (C : folds_pre_2_cat) (a b : C) (f g : a ⇒ b) : folds_iso f g → E f g.
Proof.
  intro Isofg.
  set (keytojoy := pr1 (pr2 (pr2 (pr2 Isofg)))).
  apply (keytojoy f).
  set (H' := pr2 (pr2 (pr1 C))). simpl in H'.
  destruct H' as [[[Erefl Esym] Etrans] [EI ET]].
  apply Erefl.
Qed.


(** * Univalent FOLDS-2-precategory *)
(** satisfies [isweq (idtoiso2 f g)] for any [f] and [g] *)

Definition idtoiso2 {C : folds_pre_2_cat} {a b : C} {f g : a ⇒ b} : f = g → folds_iso f g.
Proof.
  destruct 1.
  exact (folds_2_iso_id _ _ _ f).
Defined.


Definition is_univalent_folds_pre_2_cat (C : folds_pre_2_cat) : UU :=
   ∏ (a b : C) (f g : a ⇒ b), isweq (@idtoiso2 _ _ _ f g).

Lemma isaprop_is_univalent_folds_2_precat (C : folds_pre_2_cat) :
   isaprop (is_univalent_folds_pre_2_cat C).
Proof.
  do 4 (apply impred; intro);
  apply isapropisweq.
Qed.

Definition isotoid2 (C : folds_pre_2_cat) (H : is_univalent_folds_pre_2_cat C)
  (a b : C) (f g : a ⇒ b) : folds_iso f g → f = g :=
  invmap (make_weq _ (H a b f g)).

(** * FOLDS precategories *)
(** We define them as special FOLDS pre-2-categories, namely such that
   - hom-types are sets
   - axioms of precategory modulo identity (rather than E)
 *)

Definition is_folds_precategory (C : folds_pre_2_cat) : UU :=
     (∏ a b : C, isaset (a ⇒ b))
 ×  ((∏ {a b c : C} {f : a ⇒ b} {g : b ⇒ c} {h k : a ⇒ c},
                  T f g h → T f g k → h = k )       (* T is unique mod identity *)
  ×  (∏ {a b c d : C} (f : a ⇒ b) (g : b ⇒ c) (h : c ⇒ d)
                  (fg : a ⇒ c) (gh : b ⇒ d) (fg_h : a ⇒ d) (f_gh : a ⇒ d),
               T f g fg → T g h gh →
                  T fg h fg_h → T f gh f_gh → f_gh = fg_h)). (* T is assoc mod identity *)

Lemma isaprop_is_folds_precategory (C : folds_pre_2_cat) : isaprop (is_folds_precategory C).
Proof.
  apply isofhlevelsn. intro H.
  repeat (apply isofhleveldirprod).
  - do 2 (apply impred; intro).
    apply isapropisaset.
  - do 9 (apply impred; intro).
    apply (pr1 H).
  - do 15 (apply impred; intro).
    apply H.
(* alternatively by hand
  apply invproofirrelevance.
  intros [p q] [p' q'].
  apply pathsdirprod.
  - apply proofirrelevance.
    do 2 (apply impred; intro).
    apply isapropisaset.
  - destruct q as [q1 q2].
    destruct q' as [q'1 q'2].
    apply pathsdirprod.
    + apply proofirrelevance;
      do 9 (apply impred; intro); apply p.
    + apply proofirrelevance.
      do 15 (apply impred; intro); apply p.
*)
Qed.



(** * Univalent FOLDS pre-2-category is a FOLDS precategory *)


Section is_univalent_implies_folds_precat.

Variable C : folds_pre_2_cat.
Hypothesis H : is_univalent_folds_pre_2_cat C.

Lemma is_univalent_implies_is_folds_precat : is_folds_precategory C.
Proof.
  apply make_dirprod.
  - intros a b f g.
    apply (isofhlevelweqb _ (make_weq _ (H a b f g))).
    apply isaprop_folds_2_iso.
  - apply make_dirprod.
    + intros. apply (isotoid2 _ H).
      apply E_implies_folds_iso.
      set (T_unique := pr1 (pr2 (pr2 (pr1 (pr2 (pr1 C)))))).
      apply (T_unique _ _ _ f g); auto.
    + intros. apply (isotoid2 _ H).
      apply E_implies_folds_iso.
      set (T_assoc := pr2 (pr2 (pr2 (pr1 (pr2 (pr1 C)))))). simpl in T_assoc.
      apply (T_assoc _ _ _ _ f g h fg gh fg_h f_gh); auto.
Qed.

End is_univalent_implies_folds_precat.

(** * FOLDS precategory implies univalence *)

Section folds_precat_implies_univalent.

Variable C : folds_pre_2_cat.

Hypothesis H : is_folds_precategory C.
Hypothesis standardness : ∏ (a b : C) (f g : a ⇒ b), E f g → f = g.

Lemma folds_2_iso_implies_identity (a b : C) (f g : a ⇒ b) : folds_iso f g → f = g.
Proof.
  intro Isofg.
  apply standardness.
  apply folds_iso_implies_E.
  apply Isofg.
Qed.

Lemma is_folds_precat_implies_is_univalent : is_univalent_folds_pre_2_cat C.
Proof.
  intros a b f g.
  apply isweqimplimpl.
  - apply folds_2_iso_implies_identity.
  - apply (pr1 H).
  - apply isaprop_folds_2_iso.
Qed.

End folds_precat_implies_univalent.
