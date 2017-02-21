(** * Utilities concerning paths, hlevel, and logic *)

Global Unset Automatic Introduction.
Require Export UniMath.Foundations.PartD.
Require Export UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Export UniMath.Ktheory.Tactics.

(** ** Null homotopies, an aid for proving things about propositional truncation *)

Open Scope transport.

(* some jargon reminders: *)
Goal ∏ X (i:isaprop X) (x x':X), x = x'.
Proof. intros. now apply proofirrelevance. Defined.

Goal ∏ X (i:iscontr X) (x x':X), x = x'.
Proof. intros. now apply proofirrelevancecontr. Defined.

Goal ∏ X Y (f:X->Y) (x x':X), isincl f -> f x = f x' -> x = x'.
Proof. intros ? ? ? ? ? inj. now apply invmaponpathsincl. Defined.

(** ** Transport *)

  (** *** Transport a pair *)

(** ** h-levels and paths *)

Lemma isaprop_wma_inhab X : (X -> isaprop X) -> isaprop X.
Proof. intros ? f. apply invproofirrelevance. intros x y. apply (f x). Qed.

Lemma isaprop_wma_inhab' X : (X -> iscontr X) -> isaprop X.
Proof. intros ? f. apply isaprop_wma_inhab. intro x. apply isapropifcontr.
       apply (f x). Qed.

Goal ∏ (X:hSet) (x y:X) (p q:x = y), p = q.
Proof. intros. apply setproperty. Defined.

Goal ∏ (X:Type) (x y:X) (p q:x = y), isaset X -> p = q.
Proof. intros ? ? ? ? ? is. apply is. Defined.

Definition funset X (Y:hSet) : hSet
  := hSetpair (X->Y) (impredfun 2 _ _ (setproperty Y)).

(** ** Connected types *)

Definition isconnected X := ∏ (x y:X), nonempty (x = y).

Lemma base_connected {X} (t:X) : (∏ y:X, nonempty (t = y)) -> isconnected X.
Proof. intros ? ? p x y. assert (a := p x). assert (b := p y). clear p.
       apply (squash_to_prop a). apply propproperty. clear a. intros a.
       apply (squash_to_prop b). apply propproperty. clear b. intros b.
       apply hinhpr. exact (!a@b). Defined.

(** ** Applications of univalence *)

(** Compare the following two definitions with [transport_type_path]. *)

Require Import UniMath.Foundations.UnivalenceAxiom.

Definition pr1_eqweqmap { X Y } ( e: X = Y ) : cast e = pr1 (eqweqmap e).
Proof. intros. induction e. reflexivity. Defined.

Definition pr1_eqweqmap2 { X Y } ( e: X = Y ) :
  pr1 (eqweqmap e) = transportf (fun T:Type => T) e.
Proof. intros. induction e. reflexivity. Defined.

Definition weqonsec {X Y} (P:X->Type) (Q:Y->Type)
           (f:X ≃ Y) (g:∏ x, weq (P x) (Q (f x))) :
  weq (∏ x:X, P x) (∏ y:Y, Q y).
Proof. intros.
       exact (weqcomp (weqonsecfibers P (fun x => Q(f x)) g)
                      (invweq (weqonsecbase Q f))). Defined.

Definition weq_transportf {X} (P:X->Type) {x y:X} (p:x = y) : weq (P x) (P y).
Proof. intros. induction p. apply idweq. Defined.

Definition weq_transportf_comp {X} (P:X->Type) {x y:X} (p:x = y) (f:∏ x, P x) :
  weq_transportf P p (f x) = f y.
Proof. intros. induction p. reflexivity. Defined.

Definition weqonpaths2 {X Y} (w:X ≃ Y) {x x':X} {y y':Y} :
  w x = y -> w x' = y' -> weq (x = x') (y = y').
Proof. intros ? ? ? ? ? ? ? p q. induction p,q. apply weqonpaths. Defined.

Definition eqweqmap_ap {T} (P:T->Type) {t t':T} (e:t = t') (f:∏ t:T, P t) :
  eqweqmap (maponpaths P e) (f t) = f t'. (* move near eqweqmap *)
Proof. intros. induction e. reflexivity. Defined.

Definition eqweqmap_ap' {T} (P:T->Type) {t t':T} (e:t = t') (f:∏ t:T, P t) :
  invmap (eqweqmap (maponpaths P e)) (f t') = f t. (* move near eqweqmap *)
Proof. intros. induction e. reflexivity. Defined.

Definition weqpath_transport {X Y} (w:X ≃ Y) (x:X) :
  transportf (fun T => T) (weqtopaths w) = pr1 w.
Proof. intros. exact (!pr1_eqweqmap2 _ @ maponpaths pr1 (weqpathsweq w)). Defined.

Definition weqpath_cast {X Y} (w:X ≃ Y) (x:X) : cast (weqtopaths w) = w.
Proof. intros. exact (pr1_eqweqmap _ @ maponpaths pr1 (weqpathsweq w)). Defined.

Definition switch_weq {X Y} (f:X ≃ Y) {x y} : y = f x -> invweq f y = x.
Proof. intros ? ? ? ? ? p. exact (maponpaths (invweq f) p @ homotinvweqweq f x). Defined.

Definition switch_weq' {X Y} (f:X ≃ Y) {x y} : invweq f y = x -> y = f x.
Proof. intros ? ? ? ? ? p. exact (! homotweqinvweq f y @ maponpaths f p). Defined.

Definition weqbandfrel {X Y T}
           (e:Y->T) (t:T) (f : X ≃ Y)
           (P:X -> Type) (Q: Y -> Type)
           (g:∏ x:X, weq (P x) (Q (f x))) :
  weq (hfiber (fun xp:total2 P => e(f(pr1 xp))) t)
      (hfiber (fun yq:total2 Q => e(  pr1 yq )) t).
Proof. intros. refine (weqbandf (weqbandf f _ _ g) _ _ _).
       intros [x p]. simpl. apply idweq. Defined.

Definition weq_over_sections {S T} (w:S ≃ T)
           {s0:S} {t0:T} (k:w s0 = t0)
           {P:T->Type}
           (p0:P t0) (pw0:P(w s0)) (l:k#pw0 = p0)
           (H:(∏ t, P t) -> UU)
           (J:(∏ s, P(w s)) -> UU)
           (g:∏ f:(∏ t, P t), weq (H f) (J (maponsec1 P w f))) :
  weq (hfiber (fun fh:total2 H => pr1 fh t0) p0 )
      (hfiber (fun fh:total2 J => pr1 fh s0) pw0).
Proof. intros. simple refine (weqbandf _ _ _ _).
       { simple refine (weqbandf _ _ _ _).
         { exact (weqonsecbase P w). }
         { unfold weqonsecbase; simpl. exact g. } }
       { intros [f h]. simpl. unfold maponsec1; simpl.
         induction k, l; simpl. unfold transportf; simpl.
         unfold idfun; simpl. apply idweq. } Defined.

Definition weq_total2_prod {X Y} (Z:Y->Type) : (∑ y, X × Z y) ≃ (X × ∑ y, Z y).
Proof.                          (* move upstream *)
       intros. simple refine (weqpair _ (gradth _ _ _ _)).
       { intros [y [x z]]. exact (x,,y,,z). }
       { intros [x [y z]]. exact (y,,x,,z). }
       { intros [y [x z]]. reflexivity. }
       { intros [x [y z]]. reflexivity. } Defined.

(* associativity of ∑ *)
Definition totalAssociativity {X:UU} {Y: ∏ (x:X), UU} (Z: ∏ (x:X) (y:Y x), UU) : (∑ (x:X) (y:Y x), Z x y) ≃ (∑ (p:∑ (x:X), Y x), Z (pr1 p) (pr2 p)).
Proof.                          (* move upstream *)
  intros. simple refine (_,,gradth _ _ _ _).
  { intros [x [y z]]. exact ((x,,y),,z). }
  { intros [[x y] z]. exact (x,,(y,,z)). }
  { intros [x [y z]]. reflexivity. }
  { intros [[x y] z]. reflexivity. } Defined.

(** ** Pointed types *)

Definition PointedType := ∑ X, X.

Definition pointedType X x := X,,x : PointedType.

Definition underlyingType (X:PointedType) := pr1 X.

Coercion underlyingType : PointedType >-> Sortclass.

Definition basepoint (X:PointedType) := pr2 X.

Definition loopSpace (X:PointedType) :=
  pointedType (basepoint X = basepoint X) (idpath _).

Definition underlyingLoop {X:PointedType} (l:loopSpace X) : basepoint X = basepoint X.
Proof. intros. exact l. Defined.

Definition Ω := loopSpace.

(** ** Direct products with several factors *)

Definition paths3 {X Y Z} {x x':X} {y y':Y} {z z':Z} :
  x = x' -> y = y' -> z = z' -> @paths (_×_×_) (x,,y,,z) (x',,y',,z').
Proof. intros ? ? ? ? ? ? ? ? ? p q r. induction p, q, r. reflexivity.
Defined.

Definition paths4 {W X Y Z} {w w':W} {x x':X} {y y':Y} {z z':Z} :
  w = w' -> x = x' -> y = y' -> z = z' -> @paths (_×_×_×_) (w,,x,,y,,z) (w',,x',,y',,z').
Proof. intros ? ? ? ? ? ? ? ? ? ? ? ? o p q r. induction o, p, q, r. reflexivity.
Defined.

(*
Local Variables:
compile-command: "make -C ../.. TAGS UniMath/Ktheory/Utilities.vo"
End:
*)
