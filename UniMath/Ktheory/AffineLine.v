
Unset Kernel Term Sharing.

(** * Construction of affine lines 

 We show that the propositional truncation of a ℤ-torsor, where ℤ
 is the additive group of the integers, behaves like an affine line.
 It's a contractible type, but maps from it to another type Y are determined
 by specifying where the points of T should go, and where the paths
 joining consecutive points of T should go. *)

(** ** Preliminaries *)

Require UniMath.Ktheory.Nat.
Require Export Foundations.hlevel2.hSet.
Require Import Ktheory.Utilities
               Foundations.hlevel2.algebra1b
               Foundations.Proof_of_Extensionality.funextfun
               Ktheory.GroupAction
               Foundations.hlevel2.hz
               Ktheory.Integers
               Ktheory.Nat
               UniMath.Ktheory.Equivalences.
Import Ktheory.Utilities.Notation
       Ktheory.Utilities.NatNotation.

Local Notation "g * x" := (ac_mult _ g x) : action_scope.
Open Scope hz_scope.

(** ** Recursion for ℤ *)

Definition ℤRecursionData0 (P:ℤ->Type) (p0:P zero) 
      (IH :forall n, P(  toℤ n) -> P(  toℤ (S n)))
      (IH':forall n, P(- toℤ n) -> P(- toℤ (S n))) := fun 
          f:forall i, P i => 
            (f zero = p0) **
            (forall n, f(  toℤ (S n)) = IH  n (f (  toℤ n))) **
            (forall n, f(- toℤ (S n)) = IH' n (f (- toℤ n))).

Definition ℤRecursionData (P:ℤ->Type)
      (IH :forall n, P(  toℤ n) -> P(  toℤ (S n)))
      (IH':forall n, P(- toℤ n) -> P(- toℤ (S n))) := fun 
             f:forall i, P i => 
               (forall n, f(  toℤ (S n)) = IH  n (f (  toℤ n))) **
               (forall n, f(- toℤ (S n)) = IH' n (f (- toℤ n))).

Lemma ℤRecursionUniq (P:ℤ->Type) (p0:P zero) 
      (IH :forall n, P(  toℤ n) -> P(  toℤ (S n)))
      (IH':forall n, P(- toℤ n) -> P(- toℤ (S n))) :
  iscontr (total2 (ℤRecursionData0 P p0 IH IH')).
Proof. intros.
       unfold ℤRecursionData0.
       (* use hNatRecursionEquiv *)
       apply (iscontrweqb (Y := { 
            f:forall w, P (negpos w) & 
              (f (ii2 O) = p0) **
              (forall n : nat, f (ii2 (S n)) = IH n (f (ii2 n))) **
              (f (ii1 O) = IH' O (f (ii2 O))) **
              (forall n : nat, f (ii1 (S n)) = IH' (S n) (f (ii1 n)))})).
       { apply (weqbandf (weqonsecbase _ negpos)). intro f.
         refine (weqpair _ (gradth _ _ _ _)).
         { intros [h0 [hp hn]]. refine (tuple4 _ _ _ _). 
           { exact h0. } { exact hp. } 
           { exact (hn O). } { intro n. exact (hn (S n)). } }
         { intros [h0 [hp [h1' hn]]]. refine (tuple3 _ _ _).
           { exact h0. } { exact hp. }
           { intros [|n']. { exact h1'. } { exact (hn n'). } } }
         { intros [h0 [hp hn]]. simpl. apply paths3. 
           { reflexivity. } { reflexivity. }
           { apply funextsec; intros [|n']; reflexivity; reflexivity. } }
         { intros [h0 [h1' [hp hn]]]. reflexivity. } }
       intermediate_iscontr ({
             f : (forall n, P (negpos (ii1 n))) **
                 (forall n, P (negpos (ii2 n))) & 
                (pr2 f O = p0) **
                (forall n : nat, pr2 f (S n) = IH n (pr2 f n)) **
                (pr1 f O = IH' O (pr2 f O)) **
                (forall n : nat, pr1 f (S n) = IH' (S n) (pr1 f n))}).
       { apply (weqbandf (weqsecovercoprodtoprod (fun w => P (negpos w)))). 
         intro f. apply idweq. }
       intermediate_iscontr ({
              f : (forall n, P (negpos (ii2 n))) **
                  (forall n, P (negpos (ii1 n))) & 
                (pr1 f O = p0) **
                (forall n : nat, pr1 f (S n) = IH n (pr1 f n)) **
                (pr2 f O = IH' O (pr1 f O)) **
                (forall n : nat, pr2 f (S n) = IH' (S n) (pr2 f n))}).
       { apply (weqbandf (weqdirprodcomm _ _)). intro f. apply idweq. }
       intermediate_iscontr ({
                f2 : forall n : nat, P (negpos (ii2 n)) & {
                f1 : forall n : nat, P (negpos (ii1 n)) & 
                     (f2 O = p0) **
                     (forall n : nat, f2 (S n) = IH n (f2 n)) **
                     (f1 O = IH' O (f2 O)) **
                     (forall n : nat, f1 (S n) = IH' (S n) (f1 n))}}).
       { apply weqtotal2asstor. }
       intermediate_iscontr ({
            f2 : forall n : nat, P (negpos (ii2 n)) & 
                 (f2 O = p0) ** {
            f1 : forall n : nat, P (negpos (ii1 n)) & 
                 (forall n : nat, f2 (S n) = IH n (f2 n)) **
                 (f1 O = IH' O (f2 O)) **
                 (forall n : nat, f1 (S n) = IH' (S n) (f1 n))}}).
       { apply weqfibtototal; intro f2. apply weq_total2_prod. }
       intermediate_iscontr ({
            f2 : forall n : nat, P (negpos (ii2 n)) & 
                 (f2 O = p0) **
                 (forall n : nat, f2 (S n) = IH n (f2 n)) ** {
            f1 : forall n : nat, P (negpos (ii1 n)) & dirprod
                 (f1 O = IH' O (f2 O))
                 (forall n : nat, f1 (S n) = IH' (S n) (f1 n))}}).
       { apply weqfibtototal; intro f2. apply weqfibtototal; intro.
         apply weq_total2_prod. }
       intermediate_iscontr ({
            f2 : forall n : nat, P (negpos (ii2 n)) & 
                 (f2 O = p0) **
                 (forall n : nat, f2 (S n) = IH n (f2 n))}).
       { apply weqfibtototal; intro f2. apply weqfibtototal; intro h0.
         apply weqpr1; intro ih2. 
         exact (Nat.Uniqueness.hNatRecursionUniq
                   (fun n => P (negpos (ii1 n))) 
                   (IH' O (f2 O))
                   (fun n => IH' (S n))). }
       apply Nat.Uniqueness.hNatRecursionUniq.
Defined.

Lemma A (P:ℤ->Type) (p0:P zero) 
      (IH :forall n, P(  toℤ n) -> P(  toℤ (S n)))
      (IH':forall n, P(- toℤ n) -> P(- toℤ (S n))) :
  weq (total2 (ℤRecursionData0 P p0 IH IH'))
      (@hfiber
         (total2 (ℤRecursionData P IH IH'))
         (P zero)
         (fun fh => pr1 fh zero)
         p0).
Proof. intros.
       refine (weqpair _ (gradth _ _ _ _)).
       { intros [f [h0 h]]. exact ((f,,h),,h0). }
       { intros [[f h] h0]. exact (f,,(h0,,h)). }
       { intros [f [h0 h]]. reflexivity. }
       { intros [[f h] h0]. reflexivity. } Defined.

Lemma ℤRecursionEquiv (P:ℤ->Type) 
      (IH :forall n, P(  toℤ n) -> P(  toℤ (S n)))
      (IH':forall n, P(- toℤ n) -> P(- toℤ (S n))) :
  weq (total2 (ℤRecursionData P IH IH')) (P 0).
Proof. intros. exists (fun f => pr1 f zero). intro p0.
       apply (iscontrweqf (A _ _ _ _)). apply ℤRecursionUniq. Defined.

Lemma ℤRecursionEquiv_compute (P:ℤ->Type) 
      (IH :forall n, P(  toℤ n) -> P(  toℤ (S n)))
      (IH':forall n, P(- toℤ n) -> P(- toℤ (S n))) 
      (fh : total2 (ℤRecursionData P IH IH')) :
  ℤRecursionEquiv P IH IH' fh = pr1 fh zero.
Proof. reflexivity.             (* don't change the proof *)
Defined.

(** ** Bidirectional recursion for ℤ *)

Definition ℤBiRecursionData (P:ℤ->Type) (IH :forall i, P(i) -> P(1+i)) := 
  fun f:forall i, P i => forall i, f(1+i)=IH i (f i).

Definition ℤBiRecursionEquiv (P:ℤ->Type) (IH :forall i, weq (P i) (P(1+i))) :
  weq (total2 (ℤBiRecursionData P IH)) (P 0).
Proof. intros.
       assert (k : forall n, one + toℤ n = toℤ (S n)).
       { intro. rewrite nattohzandS. reflexivity. }
       set (l := fun n : nat => weq_transportf P (k n)).
       assert (k' : forall n, - toℤ n = one + (- toℤ (S n))).
       { intros. unfold one, toℤ. rewrite nattohzand1.
         rewrite nattohzandS. rewrite hzminusplus. rewrite <- (hzplusassoc one).
         rewrite (hzpluscomm one). rewrite hzlminus. rewrite hzplusl0.
         reflexivity. }
       set (l' := fun n => weq_transportf P (k' n)).
       set (ih := fun n => weqcomp (IH (toℤ n)) (l n)).
       set (ih':= fun n => (weqcomp (l' n) (invweq (IH (- toℤ (S n)))))).
       set (G := ℤRecursionEquiv P ih ih'). refine (weqcomp _ G).
       apply weqfibtototal. intro f. unfold ℤRecursionData, ℤBiRecursionData.
       refine (weqcomp (weqonsecbase _ negpos) _).
       refine (weqcomp (weqsecovercoprodtoprod _) _).
       refine (weqcomp (weqdirprodcomm _ _) _). apply weqdirprodf.
       { apply weqonsecfibers; intro n. refine (weqonpaths2 _ _ _).
         { change (negpos (ii2 n)) with (toℤ n). exact (l n). }
         { unfold l. apply weq_transportf_comp. }
         { reflexivity. } }
       { apply weqonsecfibers; intro n. simpl.
         refine (weqcomp (weqpair _ (isweqpathsinv0 _ _)) _).
         refine (weqonpaths2 _ _ _).
         { apply invweq. apply IH. }
         { simpl. rewrite homotinvweqweq. reflexivity. }
         { simpl. change (natnattohz 0 (S n)) with (- toℤ (S n)).
           unfold l'. rewrite weq_transportf_comp.
           reflexivity. } } Defined.

Definition ℤBiRecursionEquiv_compute (P:ℤ->Type)
           (IH :forall i, weq (P i) (P(1+i))) 
      (fh : total2 (ℤBiRecursionData P IH)) :
  ℤBiRecursionEquiv P IH fh = pr1 fh 0.
Proof. reflexivity.             (* don't change the proof *)
Defined.

Notation "n + x" := (ac_mult _ n x) : action_scope.
Notation "n - m" := (quotient _ n m) : action_scope.
Open Scope action_scope.

(** ** Bidirectional recursion for ℤ-torsors *)

Definition GuidedSection {T:Torsor ℤ} 
           (P:T->Type) (IH:forall t, weq (P t) (P (one + t))) := fun 
     f:Section P => 
       forall t, f (one + t) = IH t (f t).

Definition ℤTorsorRecursionEquiv {T:Torsor ℤ} (P:T->Type) 
      (IH:forall t, weq (P t) (P (one + t))) (t0:T) :
  weq (total2 (GuidedSection P IH)) (P t0).
Proof. intros. exists (fun fh => pr1 fh t0). intro q.
       set (w := triviality_isomorphism T t0).
       assert (k0 : forall i, one + w i = w (1+i)%hz).
       { intros. simpl. unfold right_mult, ac_mult. rewrite act_assoc.
         reflexivity. }
       set (l0 := (fun i => eqweqmap (ap P (k0 i))) 
               : forall i, weq (P(one + w i)) (P(w(1+i)%hz))).
       assert( e : right_mult t0 zero = t0 ). { apply act_unit. }
       set (H := fun f => forall t : T, f (one + t) = (IH t) (f t)).
       set ( IH' := (fun i => weqcomp (IH (w i)) (l0 i))
                    : forall i:ℤ, weq (P (w i)) (P (w(1+i)%hz))).
       set (J := fun f => forall i : ℤ, f (1 + i)%hz = (IH' i) (f i)).
       refine (iscontrweqb (@weq_over_sections ℤ T w 0 t0 e P q (e#'q) _ H J _) _).
       { apply transportfbinv. }
       { intro. apply invweq. unfold H,J,maponsec1. refine (weqonsec _ _ w _).
         intro i. refine (weqonpaths2 _ _ _).
         { exact (invweq (l0 i)). }
         { unfold l0. rewrite (k0 i). reflexivity. }
         { unfold IH'. unfold weqcomp; simpl.
           rewrite (homotinvweqweq (l0 i)). reflexivity. } }
       exact (pr2 (ℤBiRecursionEquiv (fun i => P(w i)) IH') (e #' q)).
Defined.

Definition ℤTorsorRecursion_compute {T:Torsor ℤ} (P:T->Type) 
      (IH:forall t, weq (P t) (P (one + t))) t h :
  ℤTorsorRecursionEquiv P IH t h = pr1 h t.
Proof. reflexivity.             (* don't change the proof *)
Defined.

Definition ℤTorsorRecursion_inv_compute {T:Torsor ℤ} (P:T->Type) 
      (IH:forall t, weq (P t) (P (one + t)))
      (t0:T) (h0:P t0) :
  pr1 (invmap (ℤTorsorRecursionEquiv P IH t0) h0) t0 = h0.
Proof. intros.
       exact (! ℤTorsorRecursion_compute P IH t0 
                (invmap (ℤTorsorRecursionEquiv P IH t0) h0) 
                @ 
                homotweqinvweq (ℤTorsorRecursionEquiv P IH t0) h0). Defined.

Definition ℤTorsorRecursion_transition {T:Torsor ℤ} (P:T->Type) 
      (IH:forall t, weq (P t) (P (one + t)))
      (t:T)
      (h:total2 (GuidedSection P IH)) :
  ℤTorsorRecursionEquiv P IH (one+t) h
  = 
  IH t (ℤTorsorRecursionEquiv P IH t h).
Proof. intros. rewrite 2!ℤTorsorRecursion_compute. exact (pr2 h t). Defined.

Definition ℤTorsorRecursion_transition_inv {T:Torsor ℤ} (P:T->Type) 
      (IH:forall t, weq (P t) (P (one + t)))
      (t:T) :
  forall h0,
  invmap (ℤTorsorRecursionEquiv P IH t) h0
  = 
  invmap (ℤTorsorRecursionEquiv P IH (one+t)) (IH t h0).
Proof. intros.
       assert (a := ℤTorsorRecursion_transition P IH t
                    (invmap (ℤTorsorRecursionEquiv P IH t) h0)).
       rewrite homotweqinvweq in a. rewrite <- a.
       rewrite homotinvweqweq. reflexivity. Defined.

Definition ℤTorsorRecursion {T:Torsor ℤ} (P:T->Type) 
      (IH:forall t, weq (P t) (P (one + t)))
      (t t':T) :
  weq (P t) (P t').
Proof. intros.
       exact (weqcomp (invweq (ℤTorsorRecursionEquiv P IH t))
                      (ℤTorsorRecursionEquiv P IH t')). Defined.  

(** ** Guided null-homotopies from ℤ-torsors 

 Let f be a map from a ℤ-torsor T to a type Y, and let s be a collection
 of target paths, connecting the images under f of consecutive points of T.
 
 A null-homotopy for f is a point y of Y, together with paths from
 y to each point in the image of f.  We say that it is "guided" by s
 if all the consecutive triangles commute.

 The main fact is that the type of guided null-homotopies for f is
 contractible.

 *)

Definition target_paths {Y} {T:Torsor ℤ} (f:T->Y) := forall t, f t=f(one + t).

Definition GHomotopy {Y} {T:Torsor ℤ} (f:T->Y) (s:target_paths f) := fun 
        y:Y => {
        h:nullHomotopyFrom f y &
          forall n, h(one + n) = h n @ s n}.

Definition GuidedHomotopy {Y} {T:Torsor ℤ} (f:T->Y) (s:target_paths f) := 
  total2 (GHomotopy f s).

Definition GH_to_cone {Y} {T:Torsor ℤ}
           {f:T->Y} {s:target_paths f} (t:T)  :
  GuidedHomotopy f s -> coconustot Y (f t).
Proof. intros ? ? ? ? ? [y hp]. exact (y,,pr1 hp t). Defined.

Definition GH_point {Y} {T:Torsor ℤ} {f:T->Y} {s:target_paths f} 
           (yhp : GuidedHomotopy f s) := pr1 yhp : Y.

Definition GH_homotopy {Y} {T:Torsor ℤ} {f:T->Y} {s:target_paths f}
           (yhp : GuidedHomotopy f s) 
     := pr1 (pr2 yhp) 
     : nullHomotopyFrom f (GH_point yhp).

Definition GH_equations {Y} {T:Torsor ℤ} (f:T->Y) (s:target_paths f) 
           (yhp : GuidedHomotopy f s) 
     := pr2 (pr2 yhp) 
     : let h := GH_homotopy yhp in
       forall n, h(one + n) = h n @ s n.

Theorem iscontrGuidedHomotopy {Y} (T:Torsor ℤ) (f:T->Y) (s:target_paths f) :
  iscontr (GuidedHomotopy f s).
Proof. intros. apply (squash_to_prop (torsor_nonempty T)).
       { apply isapropiscontr. } intro t0. 
       (* A better proof would construct the center explicitly now
          using [makeGuidedHomotopy] below.  Or we could replace this theorem
          by a corollary of it, with the new center. *)
       apply ( iscontrweqb (Y := {y:Y & y = f t0})).
       { apply weqfibtototal; intro y.
         exact (ℤTorsorRecursionEquiv _ (fun t => weq_pathscomp0r _ _) t0). }
       apply iscontrcoconustot. Defined.

Corollary proofirrGuidedHomotopy {Y} (T:Torsor ℤ) (f:T->Y) (s:target_paths f) :
  forall v w : GuidedHomotopy f s, v=w.
Proof. (* later give a more direct proof *)
       intros. apply proofirrelevancecontr. apply iscontrGuidedHomotopy. Defined.

Definition iscontrGuidedHomotopy_comp_1 {Y} :
  let T := trivialTorsor ℤ in 
  let t0 := 0 : T in
    forall (f:T->Y) (s:target_paths f),
      GH_point (the (iscontrGuidedHomotopy T f s)) = f t0.
Proof. reflexivity.             (* don't change the proof *)
Defined.

Definition iscontrGuidedHomotopy_comp_2 {Y} :
  let T := trivialTorsor ℤ in 
  let t0 := 0 : T in
    forall (f:T->Y) (s:target_paths f),
        (GH_homotopy (the (iscontrGuidedHomotopy T f s)) t0) =
        (idpath (f t0)).
Proof. intros.
       assert (a2 := ap_pr2 (iscontrweqb_compute 
                      (weqfibtototal (GHomotopy f s) (fun y : Y => y = f t0)
                                     (fun y : Y =>
                                        ℤTorsorRecursionEquiv (fun t : T => y = f t)
                                                              (fun t : T => weq_pathscomp0r y (s t)) t0))
                      (iscontrcoconustot Y (f t0))) 
                : @paths (GHomotopy f s (f t0)) _ _).
       refine (apevalat t0 (ap pr1 ((idpath _ :
                         (pr2
                            (the
                               (iscontrweqb
                                  (weqfibtototal (GHomotopy f s) (fun y : Y => y = f t0)
                                                 (fun y : Y =>
                                                    ℤTorsorRecursionEquiv (fun t : T => y = f t)
                                                                          (fun t : T => weq_pathscomp0r y (s t)) t0))
                                  (iscontrcoconustot Y (f t0)))))
                           =
                         (path_start a2)) @ a2)) @ _).
       refine (apevalat t0
                 (ap pr1
                     (compute_pr2_invmap_weqfibtototal
                        (fun y : Y =>
                           ℤTorsorRecursionEquiv
                             (fun t : T => y = f t)
                             (fun t : T => weq_pathscomp0r y (s t)) t0)
                        (f t0,, idpath (f t0)))) @ _).
       exact (ℤTorsorRecursion_inv_compute _ _ _ _).
Defined.

(* Definition iscontrGuidedHomotopy_comp_3 {Y} : *)
(*   let T := trivialTorsor ℤ in  *)
(*   let t0 := 0 : T in *)
(*     forall (f:T->Y) (s:target_paths f), *)
(*       GH_to_cone t0 (the (iscontrGuidedHomotopy T f s)) = f t0,, idpath (f t0). *)
(* Proof. intros. *)
       

(*        admit. *)
(* Defined.        *)

Definition makeGuidedHomotopy {T:Torsor ℤ} {Y} (f:T->Y)
           (s:target_paths f) {y:Y} t0 (h0:y=f t0) : 
  GuidedHomotopy f s.
Proof. intros. exact (y ,, invweq (ℤTorsorRecursionEquiv 
               (fun t : T => y = f t)
               (fun t => weq_pathscomp0r y (s t))
               t0) h0). Defined.

Definition makeGuidedHomotopy1 {T:Torsor ℤ} {Y} (f:T->Y)
           (s:target_paths f) (t0:T) : GuidedHomotopy f s.
Proof. intros. exact (makeGuidedHomotopy f s t0 (idpath (f t0))). Defined.

Definition makeGuidedHomotopy_localPath {T:Torsor ℤ} {Y} (f:T->Y)
           (s:target_paths f) {y:Y} t0 (h0 h0':y=f t0) (q:h0=h0') :
  makeGuidedHomotopy f s t0 h0 = makeGuidedHomotopy f s t0 h0'.
Proof. intros. destruct q. reflexivity. Defined.

Definition makeGuidedHomotopy_localPath_comp {T:Torsor ℤ} {Y} (f:T->Y)
           (s:target_paths f) {y:Y} t0 (h0 h0':y=f t0) (q:h0=h0') :
  ap pr1 (makeGuidedHomotopy_localPath f s t0 h0 h0' q) = idpath y.
Proof. intros. destruct q. reflexivity. Defined.

Definition makeGuidedHomotopy_verticalPath {T:Torsor ℤ} {Y} (f:T->Y)
           (s:target_paths f) {y:Y} t0 (h0:y=f t0)
           {y':Y} (p:y' = y) :
  makeGuidedHomotopy f s t0 (p@h0) = makeGuidedHomotopy f s t0 h0.
Proof. intros. apply (total2_paths2 p). destruct p. reflexivity. Defined.

Definition makeGuidedHomotopy_verticalPath_comp {T:Torsor ℤ} {Y} (f:T->Y)
           (s:target_paths f) {y:Y} t0 (h0:y=f t0)
           {y':Y} (p:y' = y) :
  ap pr1 (makeGuidedHomotopy_verticalPath f s t0 h0 p) = p.
Proof. intros. apply total2_paths2_comp1. Defined.

Definition makeGuidedHomotopy_transPath {T:Torsor ℤ} {Y} (f:T->Y)
           (s:target_paths f) {y:Y} t0 (h0:y=f t0) :
  makeGuidedHomotopy f s t0 h0 = makeGuidedHomotopy f s (one+t0) (h0 @ s t0).
Proof. intros. apply pair_path_in2.
       exact (ℤTorsorRecursion_transition_inv 
                _ (fun t => weq_pathscomp0r y (s t)) _ _). Defined.

Definition makeGuidedHomotopy_transPath_comp {T:Torsor ℤ} {Y} (f:T->Y)
           (s:target_paths f) {y:Y} t0 (h0:y=f t0) :
  ap pr1 (makeGuidedHomotopy_transPath f s t0 h0) = idpath y.
Proof. intros. 
       unfold makeGuidedHomotopy_transPath.
       exact (pair_path_in2_comp1 _
                (ℤTorsorRecursion_transition_inv 
                   _ (fun t => weq_pathscomp0r y (s t)) _ _)). Defined.

Definition makeGuidedHomotopy_diagonalPath {T:Torsor ℤ} {Y} (f:T->Y)
           (s:target_paths f) (t0:T) :
  makeGuidedHomotopy1 f s t0 = makeGuidedHomotopy1 f s (one + t0).
Proof. intros.
  assert (b := makeGuidedHomotopy_transPath f s t0 (idpath(f t0))); simpl in b.
  assert (c := makeGuidedHomotopy_localPath f s (one + t0) 
                 (s t0)
                 (s t0 @ idpath (f (one + t0)))
                 (! pathscomp0rid (s t0))).
  assert (a := makeGuidedHomotopy_verticalPath f s (one+t0) (idpath(f(one + t0))) (s t0)) .
  exact (b @ c @ a).
Defined.

Definition makeGuidedHomotopy_diagonalPath_comp {T:Torsor ℤ} {Y} (f:T->Y)
           (s:target_paths f) (t0:T) : 
  ap pr1 (makeGuidedHomotopy_diagonalPath f s t0) = s t0.
Proof. intros.
       unfold makeGuidedHomotopy_diagonalPath.
       refine (ap_natl (makeGuidedHomotopy_transPath_comp _ _ _ _) _).
       refine (ap_natl (makeGuidedHomotopy_localPath_comp _ _ _ _ _ _) _).
       exact (makeGuidedHomotopy_verticalPath_comp _ _ _ _ _).
Defined.

Definition map {T:Torsor ℤ} {Y} (f:T->Y) (s:target_paths f) : 
  squash T -> GuidedHomotopy f s.
Proof. intros ? ? ? ? t'. 
       (* try to use transport as in Halfline.map *)
       apply (squash_to_prop t').
       { apply isapropifcontr. apply iscontrGuidedHomotopy. }
       intro t; clear t'.
       exact (makeGuidedHomotopy1 f s t). Defined.

Definition map_path {T:Torsor ℤ} {Y} (f:T->Y) (s:target_paths f) : 
  forall t, map f s (squash_element t) = map f s (squash_element (one + t)).
Proof. intros. exact (makeGuidedHomotopy_diagonalPath f s t). Defined.

Definition map_path_check {T:Torsor ℤ} {Y} (f:T->Y) (s:target_paths f) :
  forall t, forall p : map f s (squash_element t) =
                       map f s (squash_element (one + t)),
    ap pr1 p = s t.
Proof. intros. set (q := map_path f s t). assert (k : q=p). 
       { apply (hlevelntosn 1). apply (hlevelntosn 0). 
         apply iscontrGuidedHomotopy. }
       destruct k. exact (makeGuidedHomotopy_diagonalPath_comp f s t). Defined.

(** ** From each torsor we get a guided homotopy *)

Definition makeGuidedHomotopy2 (T:Torsor ℤ) {Y} (f:T->Y) (s:target_paths f) : 
  GuidedHomotopy f s.
Proof. intros. exact (map f s (torsor_nonempty T)). Defined.

(** ** The construction of the affine line *)

Definition affine_line (T:Torsor ℤ) := squash T.

Definition affine_line_point (T:Torsor ℤ) : affine_line T.
Proof. intros. exact (torsor_nonempty T). Defined.

Lemma iscontr_affine_line (T:Torsor ℤ) : iscontr (affine_line T).
Proof. intros. apply iscontraprop1. { apply isaprop_squash. }
       exact (torsor_nonempty T). Defined.

Lemma affine_line_path {T:Torsor ℤ} (t u:affine_line T) : t = u.
Proof. intros. apply proofirrelevance. exact (iscontr_affine_line _). Defined.

Definition affine_line_map {T:Torsor ℤ} {Y} (f:T->Y) (s:target_paths f) : 
  affine_line T -> Y.
Proof. intros ? ? ? ? t'. exact (pr1 (map f s t')). Defined.

Definition check_values {T:Torsor ℤ} {Y} (f:T->Y) (s:target_paths f) t :
  affine_line_map f s (squash_element t) = f t.
Proof. reflexivity.              (* don't change the proof *)
Defined.

Definition check_paths {T:Torsor ℤ} {Y} (f:T->Y) (s:target_paths f) (t:T) :
  ap (affine_line_map f s) (squash_path t (one + t)) = s t.
Proof. intros. refine (_ @ map_path_check f s t _).
       apply pathsinv0. apply maponpathscomp. Defined.

Definition check_paths_any {T:Torsor ℤ} {Y} (f:T->Y) (s:target_paths f) (t:T)
           (p : squash_element t = squash_element (one + t)) :
  ap (affine_line_map f s) p = s t.
Proof. intros. set (p' := squash_path t (one + t)).
       assert (e : p' = p). { apply (hlevelntosn 1). apply isaprop_squash. }
       destruct e. apply check_paths. Defined.

Definition add_one {T:Torsor ℤ} : affine_line T -> affine_line T.
Proof. intros ?. exact (squash_fun (fun t => one + t)). Defined.

(** ** The image of the mere point in an affine line 

 A torsor is nonempty, so it merely has a point, as does the
 corresponding affine line.  Here we name its image in Y. *)

Definition affine_line_value {T:Torsor ℤ} {Y} (f:T->Y) (s:target_paths f) : Y.
Proof. intros. exact (affine_line_map f s (affine_line_point T)). Defined.

(*
Local Variables:
compile-command: "make -C ../.. UniMath/Ktheory/AffineLine.vo"
End:
*)
