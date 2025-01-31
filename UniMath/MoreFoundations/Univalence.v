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

(*TODO: improve the proof*)
Definition weqpath_transportb {X Y} (w : X ≃ Y) :
  transportb (idfun UU) (weqtopaths (invweq w)) = pr1 w.
Proof.
  intros.
  eapply pathscomp0.
  { use (! pr1_eqweqmap2 _). }
  use (maponpaths pr1).
  eapply pathscomp0.
  { use eqweqmap_pathsinv0. }
  use (transportb (λ arg, invweq arg = w) (weqpathsweq (invweq w))).
  simpl.
  use subtypePath.
  - use isapropisweq.
  - use funextsec.
    intro.
    use invinv.
Defined.

Definition weqpath_transportb' {X Y} (w : X ≃ Y) :
  transportb (idfun UU) (weqtopaths w) = invmap w.
Proof.
  use (transportf (λ arg, transportb (idfun UU) (weqtopaths w) = invmap arg) (weqpathsweq w)).
  simpl.
  change (weqtopathsUAH univalenceAxiom X Y w) with (weqtopaths w).
  induction (weqtopaths w).
  use (maponpaths pr1 inv_idweq_is_idweq).
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



Definition maponpaths_app_homot
           {X Y₁ Y₂ : UU}
           {f g : Y₁ → X → Y₂}
           (p : ∏ (z : Y₁ × X), f (pr1 z) (pr2 z) = g (pr1 z) (pr2 z))
           (x : X)
           (y : Y₁)
  : maponpaths (λ f, f x) (app_homot p y)
    =
    p (y ,, x).
Proof.
  apply (maponpaths_funextsec (f y)).
Defined.

Definition path_path_fun
           {X Y : UU}
           {f g : X → Y}
           {e₁ e₂ : f = g}
           (h : ∏ (x : X), eqtohomot e₁ x = eqtohomot e₂ x)
  : e₁ = e₂.
Proof.
  refine (!(@funextsec_toforallpaths X (λ _, Y) f g e₁) @ _).
  refine (_ @ @funextsec_toforallpaths X (λ _, Y) f g e₂).
  apply maponpaths.
  use funextsec.
  intro x.
  apply h.
Defined.

Definition funextsec_inv {T:UU} (P : T → UU)
  (f g : ∏ t : T, P t)
  (H : f ~ g)
  : (! funextsec P f g H)
  = funextsec P g f (λ t, ! (H t)).
Proof.
  use (transportb (λ h, ! funextsec P f g h = funextsec P g f (λ t : T, ! h t)) (!toforallpaths_funextsec _) _).
    use (invmap ((weqonpaths (weqtoforallpaths _ _ _)) _ _)).
  induction (funextsec P f g H).
  cbn.
  rewrite funextsec_toforallpaths, toforallpaths_funextsec.
  apply idpath.
Qed.

(*[toforallpaths_induction'] is the same as [toforallpaths_induction] in [Foundations/UnivalenceAxiom.v] but with f and g dependent functions*)
Lemma toforallpaths_induction' (X : UU) (Y: X -> UU) (f g : ∏ (x:X), Y x)
  (P : (∏ x, f x = g x) -> UU)
  (H : ∏ e : f = g, P (toforallpaths _ _ _ e)) : ∏ i : (∏ x, f x = g x), P i.
Proof.
  intros i. rewrite <- (homotweqinvweq (weqtoforallpaths _ f g)). apply H.
Defined.

Definition transportf_funextsec
  {X: UU} {Y : X -> UU} (P : ∏ (x:X), Y x -> UU)
  (F F' : ∏ (x:X), Y x)
  (H : ∏ (x : X), F x = F' x)
  (x : X) (f : P x (F x))
  :
  transportf (λ (x0 : ∏(x:X), Y x), P x (x0 x)) (funextsec _ F F' H) f = transportf (λ x0 : Y x, P x x0) (H x) f.
Proof.
  use (toforallpaths_induction' X Y F F'
    (λ H',  transportf  (λ x0 : ∏ x0 : X, Y x0, P x (x0 x))
                        (funextsec Y F F' H')
                        f =
            transportf  (λ x0 : Y x, P x x0)
                        (H' x)
                        f) _ H).
  intro e. clear H.
  set (XR := homotinvweqweq (weqtoforallpaths _ F F') e).
  set (H := funextsec Y F F' (toforallpaths Y F F' e)).
  set (P' := λ (F0 : ∏ (x:X), Y x) , P x (F0 x)).
  use pathscomp0.
  - exact (transportf P' e f).
  - use transportf_paths. exact XR.
  - induction e. apply idpath.
Defined.

Definition transportb_funextfun {X Y : UU} (P : Y -> UU) (F F' : X -> Y) (H : ∏ (x : X), F x = F' x)
           (x : X) (f : P (F' x)) :
  transportb (λ x0 : X → Y, P (x0 x)) (funextsec _ F F' H) f = transportb (λ x0 : Y, P x0) (H x) f.
Proof.
  apply (toforallpaths_induction
           _ _ F F' (λ H', transportb (λ x0 : X → Y, P (x0 x))
                                       (funextsec (λ _ : X, Y) F F' (λ x0 : X, H' x0)) f =
                            transportb (λ x0 : Y, P x0) (H' x) f)).
  intro e. clear H.
  set (XR := homotinvweqweq (weqtoforallpaths _ F F') e).
  set (H := funextsec (λ _ : X, Y) F F' (λ x0 : X, toforallpaths (λ _ : X, Y) F F' e x0)).
  set (P' := λ x0 : X → Y, P (x0 x)).
  use pathscomp0.
  - exact (transportb P' e f).
  - use transportf_paths.
    use invrot.
    eapply pathscomp0.
    { use pathsinv0inv0. }
    exact XR.
  - induction e. cbn. apply idpath.
Defined.