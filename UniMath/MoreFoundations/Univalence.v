(** * Additional results about univalence *)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.MoreFoundations.PartA.

(** Funextsec and toforallpaths are mutually inverses *)
Lemma funextsec_toforallpaths {T : UU} {P : T -> UU} {f g : ∏ t : T, P t} :
  ∏ (h : f = g), funextsec _  _ _ (toforallpaths _ _ _ h) = h.
Proof.
  intro h; exact (!homotinvweqweq0 (weqtoforallpaths _ _ _) h).
Defined.

Lemma toforallpaths_funextsec {T : UU} {P : T -> UU} {f g : ∏ t : T, P t} :
  ∏ (h : ∏ t : T, f t = g t), toforallpaths _  _ _ (funextsec _ _ _ h) = h.
Proof.
  intro h; exact (homotweqinvweq (weqtoforallpaths _ _ _) h).
Defined.

Definition toforallpaths_funextsec_comp {T : UU} {P : T -> UU} (f g : ∏ t, P t) :
  toforallpaths P f g ∘ funextsec P f g = idfun _.
Proof.
  apply funextsec; intro. simpl.
  apply toforallpaths_funextsec.
Defined.

Lemma maponpaths_funextsec {T : UU} {P : T -> UU}
          (f g : ∏ t, P t) (t : T) (p : f ~ g) :
 maponpaths (λ h, h t) (funextsec _ f g p) = p t.
Proof.
 intermediate_path (toforallpaths _ _ _ (funextsec _ f g p) t).
 - generalize (funextsec _ f g p); intros q.
   induction q.
   reflexivity.
 - apply (eqtohomot (eqtohomot (toforallpaths_funextsec_comp f g) p) t).
Qed.


Definition weqonsec {X Y} (P:X->Type) (Q:Y->Type)
           (f:X ≃ Y) (g:∏ x, weq (P x) (Q (f x))) :
  (∏ x:X, P x) ≃ (∏ y:Y, Q y).
Proof.
  intros.
  exact (weqcomp (weqonsecfibers P (λ x, Q(f x)) g)
                 (invweq (weqonsecbase Q f))).
Defined.

Definition weq_transportf {X} (P:X->Type) {x y:X} (p:x = y) : (P x) ≃ (P y).
Proof.
  intros. induction p. apply idweq.
Defined.

Definition weq_transportf_comp {X} (P:X->Type) {x y:X} (p:x = y) (f:∏ x, P x) :
  weq_transportf P p (f x) = f y.
Proof.
  intros. induction p. reflexivity.
Defined.

Definition weqonpaths2 {X Y} (w:X ≃ Y) {x x':X} {y y':Y} :
  w x = y -> w x' = y' -> (x = x') ≃ (y = y').
Proof.
  intros p q. induction p,q. apply weqonpaths.
Defined.

Definition eqweqmap_ap {T} (P:T->Type) {t t':T} (e:t = t') (f:∏ t:T, P t) :
  eqweqmap (maponpaths P e) (f t) = f t'. (* move near eqweqmap *)
Proof.
  intros. induction e. reflexivity.
Defined.

Definition eqweqmap_ap' {T} (P:T->Type) {t t':T} (e:t = t') (f:∏ t:T, P t) :
  invmap (eqweqmap (maponpaths P e)) (f t') = f t. (* move near eqweqmap *)
Proof.
  intros. induction e. reflexivity.
Defined.

(** weak equivalences *)

Definition pr1_eqweqmap { X Y } ( e: X = Y ) : cast e = pr1 (eqweqmap e).
Proof.
  intros. induction e. reflexivity.
Defined.

Definition path_to_fun {X Y} : X=Y -> X->Y.
Proof.
  intros p. induction p. exact (idfun _).
Defined.

Definition pr1_eqweqmap2 { X Y } ( e: X = Y ) :
  pr1 (eqweqmap e) = transportf (λ T:Type, T) e.
Proof.
  intros. induction e. reflexivity.
Defined.

Definition weqpath_transport {X Y} (w : X ≃ Y) :
  transportf (idfun UU) (weqtopaths w) = pr1 w.
Proof.
  intros. exact (!pr1_eqweqmap2 _ @ maponpaths pr1 (weqpathsweq w)).
Defined.

Definition weqpath_cast {X Y} (w : X ≃ Y) : cast (weqtopaths w) = w.
Proof.
  intros. exact (pr1_eqweqmap _ @ maponpaths pr1 (weqpathsweq w)).
Defined.

Definition switch_weq {X Y} (f:X ≃ Y) {x y} : y = f x -> invweq f y = x.
Proof.
  intros p. exact (maponpaths (invweq f) p @ homotinvweqweq f x).
Defined.

Definition switch_weq' {X Y} (f:X ≃ Y) {x y} : invweq f y = x -> y = f x.
Proof.
  intros p. exact (! homotweqinvweq f y @ maponpaths f p).
Defined.

Local Open Scope transport.

Definition weq_over_sections {S T} (w:S ≃ T)
           {s0:S} {t0:T} (k:w s0 = t0)
           {P:T->Type}
           (p0:P t0) (pw0:P(w s0)) (l:k#pw0 = p0)
           (H:(∏ t, P t) -> UU)
           (J:(∏ s, P(w s)) -> UU)
           (g:∏ f:(∏ t, P t), weq (H f) (J (maponsec1 P w f))) :
  weq (hfiber (λ fh:total2 H, pr1 fh t0) p0 )
      (hfiber (λ fh:total2 J, pr1 fh s0) pw0).
Proof.
  intros. simple refine (weqbandf _ _ _ _).
  { simple refine (weqbandf _ _ _ _).
    { exact (weqonsecbase P w). }
    { unfold weqonsecbase; simpl. exact g. } }
  { intros [f h]. simpl. unfold maponsec1; simpl.
    induction k, l; simpl. unfold transportf; simpl.
    apply idweq. }
Defined.
