(** Grothendieck groups of exact categories  *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Ktheory.ExactCategories.
Require Import UniMath.Algebra.Free_Monoids_and_Groups.
Import AddNotation.
Local Open Scope addmonoid.

Section setquot.
  Definition setquot_universal_property (X:Type) (R:eqrel X) (Y:hSet) :
    (setquot R -> Y) ≃ (∑ f : X -> Y, iscomprelfun R f).
  Proof.
    use weqpair.
    - intros h. exists (h ∘ setquotpr R).
      intros x x' r. unfold funcomp. apply maponpaths. apply iscompsetquotpr. exact r.
    - intros f. apply iscontraprop1.
      + apply isaproptotal2.
        * intros h. apply isaset_total2.
          { apply impred_isaset. intros x. apply setproperty. }
          intros f'. apply isasetaprop. apply isapropiscomprelfun.
        * intros h h' e e'. apply funextsec; intros w.
          apply (surjectionisepitosets _ _ _ (issurjsetquotpr R)).
          { apply setproperty. }
          exact (λ x, maponpaths (adjev x) (maponpaths pr1 e @ ! maponpaths pr1 e')).
      + exists (setquotuniv R Y (pr1 f) (pr2 f)). apply subtypeEquality.
        * intros f'. apply isapropiscomprelfun.
        * reflexivity.
  Defined.
  Goal ∏ (X:Type) (R:eqrel X) (Y:hSet) (h : setquot R -> Y),
    pr1 (setquot_universal_property X R Y h) = h ∘ setquotpr R.
  Proof.
    reflexivity.
  Defined.
  Goal ∏ (X:Type) (R:eqrel X) (Y:hSet) (q : ∑ f : X -> Y, iscomprelfun R f),
    invmap (setquot_universal_property X R Y) q = setquotuniv R Y (pr1 q) (pr2 q).
  Proof.
    reflexivity.
  Defined.
End setquot.

Section Pi0.
  (* move upstream *)
  Definition π₀ := pi0.
  Definition component {X:Type} : X -> π₀ X := setquotpr (pathseqrel X).
  Definition π₀_map {X Y:Type} : (X -> Y) -> (π₀ X -> π₀ Y)
    := λ f, setquotfun (pathseqrel X) (pathseqrel Y) f (λ x x', hinhfun (maponpaths f)).
  Definition π₀_universal_property (X:Type) (Y:hSet) : (π₀ X -> Y) ≃ (X -> Y).
  Proof.
    exists (λ h, h ∘ component). intros f.
    apply iscontraprop1.
    - apply isaproptotal2.
      + intros h. use (_ : isaset _). apply impred_isaset. intros x. apply setproperty.
      + intros h h' e e'. apply funextsec. intro w.
        { apply (surjectionisepitosets component).
          - apply issurjsetquotpr.
          - apply setproperty.
          - intros x.
            exact (maponpaths (λ k, k x) (e @ ! e')). }
    - use tpair.
      + exact (setquotuniv _ _ f (λ x y e, squash_to_prop e (setproperty Y (f x) (f y)) (maponpaths f))).
      + cbn beta. reflexivity.
  Defined.
  Definition π₀_universal_map {X:Type} {Y:hSet} : (X -> Y) -> (π₀ X -> Y)
    := invmap (π₀_universal_property X Y).
  Lemma π₀_universal_map_eqn {X:Type} {Y:hSet} (f : X -> Y) :
    ∏ (x:X), π₀_universal_map f (component x) = f x.
  Proof.
    reflexivity.
  Defined.
  Lemma π₀_universal_map_uniq {X:Type} {Y:hSet} (h h' : π₀ X -> Y) :
    (∏ x, h (component x) = h' (component x)) -> h ~ h'.
  Proof.
    intros e x. apply (surjectionisepitosets component).
    - apply issurjsetquotpr.
    - apply setproperty.
    - exact e.
  Defined.
End Pi0.

(* new stuff *)
Definition K_0_hrel (M:ExactCategory) : hrel (free_abgr (π₀ (ob M)))
  := λ g h, ∃ E : ShortExactSequence M,
      g = free_abgr_unit (component (Ob2 E)) ×
      h = free_abgr_unit (component (Ob1 E)) + free_abgr_unit (component (Ob3 E)).
Definition K_0_related {M:ExactCategory} (E : ShortExactSequence M)
  : K_0_hrel M (free_abgr_unit (component (Ob2 E)))
               (free_abgr_unit (component (Ob1 E)) + free_abgr_unit (component (Ob3 E)))
  := hinhpr ( E ,, idpath _ ,, idpath _).
Definition K_0 (M:ExactCategory) : abgr
  := presented_abgr (π₀ (ob M)) (K_0_hrel M).
Definition K_0_map {M N:ExactCategory} (F:ExactFunctor M N) : monoidfun (K_0 M) (K_0 N).
Proof.
  use (presented_abgrfun (π₀_map (functor_on_objects F))). intros g h.
  use hinhfun. intros [E [e e']]. exists (applyFunctorToShortExactSequence F E).
  now induction (!e), (!e').
Defined.
Definition K_0_class {M:ExactCategory} : ob M -> K_0 M
  := λ A, @presented_abgr_intro (π₀ M) _ (pi0pr _ A).
Lemma K_0_eqn {M:ExactCategory} (E : ShortExactSequence M) :
  K_0_class (Ob2 E) = K_0_class (Ob1 E) + K_0_class (Ob3 E).
Proof.
  apply iscompsetquotpr. apply generated_binopeqrel_intro. apply hinhpr.
  exists E. split; reflexivity.
Defined.
Lemma K_0_map_universal_property {M:ExactCategory} {G:abgr} :
  monoidfun (K_0 M) G
  ≃
  ∑ f : ob M -> G, ∏ E:ShortExactSequence M, f(Ob2 E) = f(Ob1 E) + f(Ob3 E).
Proof.
  apply (weqcomp (presented_abgr_universal_property (K_0_hrel M) G)).
  intermediate_weq (∑ f : π₀ M → G, ∏ E : ShortExactSequence M, f (component (Ob2 E)) = f (component (Ob1 E)) + f (component (Ob3 E))).
  - apply weqfibtototal. intros h. apply weqiff.
    + split.
      * intros i E. exact (i _ _ (K_0_related E)).
      * intros k w w' r. apply (squash_to_prop r).
        { apply setproperty. }
        clear r; intros [E [e e']]. induction (!e), (!e'); clear e e'. exact (k E).
    + apply isapropiscomprelfun.
    + apply impred_isaprop; intros E. apply setproperty.
  - exact (weqfp (π₀_universal_property (ob M) G) _).
Defined.
Definition K_0_universal_map {M:ExactCategory} {G:abgr} (f : ob M -> G) :
  (∏ E:ShortExactSequence M, f(Ob2 E) = f(Ob1 E) + f(Ob3 E)) -> monoidfun (K_0 M) G.
Proof.
  intros c. exact (invmap K_0_map_universal_property (f,,c)).
Defined.
Goal ∏ (M:ExactCategory) (G:abgr) (f : ob M -> G)
      (add : ∏ E:ShortExactSequence M, f(Ob2 E) = f(Ob1 E) + f(Ob3 E)) (A:M),
  K_0_universal_map f add (K_0_class A) = f A.
Proof.
  reflexivity.
Qed.
Goal ∏ (M:ExactCategory) (G:abgr) (h : monoidfun (K_0 M) G),
  pr1 (K_0_map_universal_property h) = h ∘ K_0_class.
Proof.
  reflexivity.
Qed.
Goal ∏ (M:ExactCategory) (G:abgr)
     (f : ob M -> G) (add : ∏ E:ShortExactSequence M, f(Ob2 E) = f(Ob1 E) + f(Ob3 E)),
  invmap K_0_map_universal_property (f,,add) = K_0_universal_map f add.
Proof.
  intros.
  apply pathsinv0.              (* omit this and it is slow! *)
  reflexivity.
Qed.

Section Try.
  (* maybe try a different way to speed it up: *)
  Definition K_0_universal_map' {M:ExactCategory} {G:abgr} (f : ob M -> G) :
    (∏ E:ShortExactSequence M, f(Ob2 E) = f(Ob1 E) + f(Ob3 E)) -> monoidfun (K_0 M) G.
  Proof.
    intros c. use presented_abgr_extend.
    - exact (π₀_universal_map f).
    - intros x y Rxy. apply (squash_to_prop Rxy).
      + apply setproperty.
      + clear Rxy; intros [E [r s]]. induction (!r), (!s); clear r s.
        change (f (Ob2 E) = f (Ob1 E) + f (Ob3 E)). exact (c E).
  Defined.
  Goal ∏ (M:ExactCategory) (G:abgr) (f : ob M -> G)
        (add : ∏ E:ShortExactSequence M, f(Ob2 E) = f(Ob1 E) + f(Ob3 E)) (A:M),
    K_0_universal_map' f add (K_0_class A) = f A.
  Proof.
    reflexivity.
  Qed.
  Lemma K_0_map_universal_property' {M:ExactCategory} {G:abgr} :
    monoidfun (K_0 M) G
    ≃
    ∑ f : ob M -> G, ∏ E:ShortExactSequence M, f(Ob2 E) = f(Ob1 E) + f(Ob3 E).
  Proof.
    use weq_iso.
    - intros h. exists (h ∘ K_0_class). intros E. unfold funcomp.
      intermediate_path (h (K_0_class (Ob1 E) + K_0_class (Ob3 E))).
      + apply (maponpaths h). apply K_0_eqn.
      + apply h.
    - intros [f add]. exact (K_0_universal_map' f add).
    - cbn beta. intros h. admit.
    - cbn beta.
  Abort.
End Try.
