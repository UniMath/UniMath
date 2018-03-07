Require Export UniMath.Foundations.PartD.
Require Export UniMath.Foundations.UnivalenceAxiom.
Require Export UniMath.Inductives.functors.


Definition iscontr_based_paths {A : UU} (x : A) :
  iscontr (∑ y, x = y).
Proof.
  use iscontrpair.
  - exact (x,, idpath x).
  - induction 0 as [y p].
    induction p.
    reflexivity.
Defined.

Definition isaprop_uniqueness {X} (is_prop : isaprop X) :
    ∏ x1 x2 : X, x1 = x2 :=
    λ x1 x2, iscontrpr1 (is_prop x1 x2).



(*** Paths ***)

Definition transportf_paths_FlFr {A B : UU} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1)
  : transportf (λ x, f x = g x) p q = !maponpaths f p @ q @ maponpaths g p.
Proof.
  induction p; cbn.
  symmetry.
  apply pathscomp0rid.
Defined.

Definition transportf_sec_constant
  {A B : UU} {C : A -> B -> UU}
  {x1 x2 : A} (p : x1 = x2) (f : ∏ y : B, C x1 y)
  : (transportf (λ x, ∏ y : B, C x y) p f)
    = (λ y, transportf (λ x, C x y) p (f y)).
Proof.
  induction p; cbn; unfold idfun.
  reflexivity.
Defined.

Definition transportb_sec_constant
  {A B : UU} (C : A -> B -> UU)
  {x1 x2 : A} (p : x1 = x2) (f : ∏ y : B, C x2 y)
  : (transportb (λ x, ∏ y : B, C x y) p f)
    = (λ y, transportb (λ x, C x y) p (f y)).
Proof.
  induction p; cbn; unfold idfun.
  reflexivity.
Defined.

Definition transportf_total2_const :
    ∏ (A B : UU) (C : A -> B -> UU) (a : A) (b1 b2 : B) (p : b1 = b2) (c : C a b1),
    transportf (λ b, ∑ a : A, C a b) p (a,, c) =
    a,, transportf (C a) p c.
  Proof.
    intros.
    induction p.
    reflexivity.
  Defined.

Definition maponpaths_funextsec {A : UU} {B : A -> UU}
           (f g : ∏ x, B x) (x : A) (p : f ~ g) :
  maponpaths (λ h, h x) (funextsec _ f g p) = p x.
Proof.
  intermediate_path (toforallpaths _ _ _ (funextsec _ f g p) x). {
    generalize (funextsec _ f g p); intros q.
    induction q.
    reflexivity.
  }
  intermediate_path (weqcomp (invweq (weqtoforallpaths B f g))
                             (weqtoforallpaths B f g)
                             p
                             x). {
    reflexivity.
  }
  intermediate_path (p x). {
  rewrite weqcompinvl.
  reflexivity.
  }
  reflexivity.
Defined.

Definition transportf_weqtopaths :
    ∏ (A B : UU) (e : A ≃ B) (a : A),
    transportf (idfun _) (weqtopaths e) a = e a.
  Proof.
    intros.
    unfold weqtopaths.
    intermediate_path (univalence _ _ (invmap (univalence _ _) e) a). {
      generalize (invmap (univalence _ _) e); intros p.
      induction p.
      reflexivity.
    }
    rewrite homotweqinvweq.
    reflexivity.
  Defined.

  Definition transportb_weqtopaths :
    ∏ (A B : UU) (e : A ≃ B) (b : B),
    transportb (idfun _) (weqtopaths e) b = invmap e b.
  Proof.
    intros.
    unfold weqtopaths.
    intermediate_path (invmap (univalence _ _ (invmap (univalence _ _) e)) b). {
      generalize (invmap (univalence _ _) e); intros p.
      induction p.
      reflexivity.
    }
    rewrite homotweqinvweq.
    reflexivity.
  Defined.



(*** Equivalences with ∏ ***)

Lemma weq_functor_sec_id (A : UU) (B C : A -> UU) :
  (∏ a, B a ≃ C a) ->
  (∏ a, B a) ≃ (∏ a, C a).
Proof.
  intros e.
  use weqgradth.
  - exact (λ f a, e a (f a)).
  - exact (λ f a, invmap (e a) (f a)).
  - cbn.
    intros f.
    apply funextsec; intros a.
    apply homotinvweqweq.
  - cbn.
    intros f.
    apply funextsec; intros a.
    apply homotweqinvweq.
  (* apply weqonsecfibers. *)
Defined.

Lemma sec_symmetry (A B : UU) (C : A -> B -> UU) :
  (∏ a b, C a b)
    ≃ (∏ b a, C a b).
Proof.
  use weqgradth.
  - exact (λ f b a, f a b).
  - exact (λ f a b, f b a).
  - reflexivity.
  - reflexivity.
Defined.

Lemma func_total2_distributivity (A B : UU) (C : B -> UU) :
  (A -> ∑ b : B, C b)
    ≃ (∑ b : A -> B, ∏ a, C (b a)).
Proof.
  apply weqfuntototaltototal.
Defined.

Lemma sec_total2_distributivity (A : UU) (B : A -> UU) (C : ∏ a, B a -> UU) :
  (∏ a : A, ∑ b : B a, C a b)
    ≃ (∑ b : ∏ a : A, B a, ∏ a, C a (b a)).
Proof.
  use weqgradth.
  - intros f.
    exists (λ a, pr1 (f a)).
    exact (λ a, pr2 (f a)).
  - intros fg; induction fg as [f g].
    exact (λ a, f a,, g a).
  - reflexivity.
  - reflexivity.
Defined.


(*** Equivalences with ∑ ***)

Lemma weq_functor_total2 {A B : UU} (C : A -> UU) (D : B -> UU) :
  ∏ e : A ≃ B,
        (∏ x, C x ≃ D (e x)) ->
        (∑ x, C x) ≃ (∑ x, D x).
Proof.
  intros e f.
  exact (weqbandf e C D f).
Defined.

Lemma weq_functor_total2_id {A : UU} (B C : A -> UU) :
  (∏ x, B x ≃ C x) ->
  (∑ x, B x) ≃ (∑ x, C x).
Proof.
  intros e.
  apply (weqfibtototal B C e).
Defined.

Lemma total2_symmetry (A B : UU) (C : A -> B -> UU) :
  (∑ a b, C a b)
    ≃ (∑ b a, C a b).
Proof.
  use weqgradth.
  - intros abc; induction abc as [a [b c]].
    exact (b,, a,, c).
  - intros bac; induction bac as [b [a c]].
    exact (a,, b,, c).
  - reflexivity.
  - reflexivity.
Defined.

Lemma total2_associativity (A : UU) (B : A -> UU) (C : (∑ a, B a) -> UU) :
  (∑ ab : ∑ a : A, B a, C ab)
    ≃ (∑ a : A, ∑ b : B a, C (a,, b)).
Proof.
  use weqgradth.
  - induction 1 as [ab c].
    induction ab as [a b].
    exact (a,, b,, c).
  - induction 1 as [a bc].
    induction bc as [b c].
    exact ((a,, b),, c).
  - induction 0 as [ab c].
    induction ab as [a b].
    reflexivity.
  - induction 0 as [a bc].
    induction bc as [b c].
    reflexivity.
Defined.

Lemma weq_prod_contr_l (A B : UU) :
  iscontr A ->
  A × B ≃ B.
Proof.
  induction 1 as [a0 a0_unique].
  use weqgradth.
  - exact pr2.
  - exact (λ b, a0,, b).
  - induction 0 as [a b]; cbn.
    apply pathsdirprod.
    + symmetry.
      apply a0_unique.
    + reflexivity.
  - intros b; cbn.
    reflexivity.
Defined.


(*** Other equivalences ***)

Lemma weq_total2_paths_f (A : UU) (B : A -> UU)
      (a1 a2 : A) (b1 : B a1) (b2 : B a2) :
  (∑ p : a1 = a2, transportf B p b1 = b2)
    ≃ (a1,, b1 = a2,, b2).
Proof.
  use weqgradth.
  - induction 1 as [p q].
    use (total2_paths2_f p q).
  - intros p.
    exists (base_paths _ _ p).
    exact (fiber_paths p).
  - induction 0 as [p q].
    use total2_paths2_f.
    + exact (@base_total2_paths _ _ (a1,, b1) (a2,, b2) p q).
    + cbn.
      exact (transportf_fiber_total2_paths B (a1,, b1) (a2,, b2) p q).
  - intros p. cbn.
    apply (total2_fiber_paths p).
Defined.

Lemma weq_sequence_cons (A : nat -> UU) :
  (A 0 × ∏ n, A (1 + n)) ≃ ∏ n, A n.
Proof.
  use weqgradth.
  - intros [xO xS] n; induction n.
    + exact xO.
    + exact (xS n).
  - exact (λ x, x 0,, x ∘ S).
  - reflexivity.
  - intros x; cbn.
    apply funextsec; intros n; induction n; reflexivity.
Defined.

Lemma weq_comp_lⁱ {I : UU} (A B C : Fam I) :
  B ≃ⁱ C ->
  (A ->ⁱ B) ≃ (A ->ⁱ C).
Proof.
  intros f.
  use weqgradth.
  - exact (λ g, f ∘ⁱ g).
  - exact (λ g, invweqⁱ f ∘ⁱ g).
  - intros g. cbn.
    apply funextsec; intros i.
    apply funextfun; intros a.
    change (invmap (f i) (f i (g i a)) = g i a). rewrite homotinvweqweq.
    reflexivity.
  - intros g. cbn.
    apply funextsec; intros i.
    apply funextfun; intros a.
    change (f i (invmap (f i) (g i a)) = g i a). rewrite homotweqinvweq.
    reflexivity.
Defined.

Lemma weq_comp0_l {A : UU} (a b c : A) :
  b = a ->
  (a = c) ≃ (b = c).
Proof.
  induction 1.
  apply idweq.
Defined.

Lemma weq_comp0_r {A : UU} (a b c : A) :
  b = c ->
  (a = b) ≃ (a = c).
Proof.
  induction 1.
  apply idweq.
Defined.
