(** * Equivalences *)

Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Ktheory.Utilities
               UniMath.Foundations.funextfun.

Section A.

  Local Notation "p @' q" := (pathscomp0 p q)
                             (only parsing, at level 61, left associativity).
  Local Arguments idpath {_ _}.

  Lemma other_adjoint {X Y} (f : X -> Y) (g : Y -> X)
        (p : forall y : Y, f (g y) = y)
        (q : forall x : X, g (f x) = x)
        (h : forall x : X, ap f (q x) = p (f x)) :
   forall y : Y, ap g (p y) = q (g y).
  Proof. intros. apply pathsinv0. 
         intermediate_path (
              !(ap g (p (f (g y))))
              @' ap g (p (f (g y)))
              @' q (g y)).
         { rewrite pathsinv0l. reflexivity. }
         intermediate_path (
              !(ap g (ap f (q (g y))))
              @' ap g (p (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. apply (ap pathsinv0). apply (ap (ap g)).
           set (y' := g y). apply pathsinv0. exact (h y'). }
         intermediate_path (
              !(ap g (ap f (q (g y))))
              @' ap g (p (f (g y)))
              @' ((!q (g (f (g y))))
                  @' q (g (f (g y)))
                  @' q (g y))).
         { rewrite pathsinv0l. reflexivity. }
         intermediate_path (
              !(ap g (ap f (q (g y))))
              @' ap g (p (f (g y)))
              @' ((!q (g (f (g y))))
                  @' (ap g (p (f (g y)))
                      @' !(ap g (p (f (g y))))
                      @' q (g (f (g y))))
                  @' q (g y))).
         { ap_pre_post_cat. apply path_inv_rotate_rr. reflexivity. }
         apply path_inverse_from_right.
         repeat rewrite path_assoc.
         intermediate_path (
              !(ap g (p y))
              @' !(ap g (ap f (q (g y))))
              @' !(q (g (f (g (f (g y))))))
              @' ap (funcomp f g) (ap g (p (f (g y))))
              @' ap g (p (f (g y)))
              @' !(ap g (p (f (g y))))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. 
           apply path_inv_rotate_lr. rewrite <- path_assoc.
           apply path_inv_rotate_rl. apply pathsinv0.
           rewrite <- (maponpathscomp f g). set (y' := f (g y)).
           assert (r := ap_fun_fun_fun_natl p g q y'). simpl in r.
           rewrite (maponpathscomp f). rewrite (maponpathscomp g).
           rewrite (maponpathscomp g (fun x : X => g (f x))) in r.
           rewrite maponpathsidfun in r. exact r. }
         intermediate_path (
              !(ap g (p y))
              @' !(ap g (ap f (q (g y))))
              @' !(q (g (f (g (f (g y))))))
              @' ap g (ap f (ap g (p (f (g y)))))
              @' ap g (p (f (g y)))
              @' !(ap g (p (f (g y))))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. rewrite <- (maponpathscomp f g). reflexivity. }
         intermediate_path (
              !(ap g (p y))
              @' !(ap g (ap f (q (g y))))
              @' !(q (g (f (g (f (g y))))))
              @' ap g (ap f (ap g (p (f (g y)))) @' p (f (g y)))
              @' !(ap g (p (f (g y))))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. rewrite <- (maponpathscomp0 g).  reflexivity. }
         intermediate_path (
              !(ap g (p y))
              @' !(ap g (ap f (q (g y))))
              @' !(q (g (f (g (f (g y))))))
              @' ap g (ap (funcomp g f) (p (f (g y))) @' p (f (g y)))
              @' !(ap g (p (f (g y))))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. rewrite <- (maponpathscomp g f). reflexivity. }
         intermediate_path (
              !(ap g (p y))
              @' !(ap g (ap f (q (g y))))
              @' !(q (g (f (g (f (g y))))))
              @' ap g (p (f (g (f (g y)))) @' p (f (g y)))
              @' !(ap g (p (f (g y))))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. rewrite <- (maponpathscomp g f). 
           apply (ap (ap g)). generalize (f (g y)); clear y; intro y.
           assert (r := ap_fun_fun_natl p p y); simpl in r.
           assert (s := maponpathsidfun (p y)); unfold idfun in s.
           rewrite s in r; clear s. rewrite (maponpathscomp g). exact r. }
         intermediate_path (
              !(ap g (p y))
              @' !(ap g (ap f (q (g y))))
              @' !(q (g (f (g (f (g y))))))
              @' ap g (p (f (g (f (g y)))))
              @' ap g (p (f (g y)))
              @' !(ap g (p (f (g y))))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. rewrite <- (maponpathscomp0 g). reflexivity. }
         intermediate_path (
              !(ap g (p y))
              @' !(ap g (ap f (q (g y))))
              @' !(q (g (f (g (f (g y))))))
              @' ap g (p (f (g (f (g y)))))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. repeat rewrite <- path_assoc. 
           rewrite pathsinv0r. rewrite pathscomp0rid. reflexivity. }
         intermediate_path (
              ap g ((!p y) @' ap f (!q (g y)))
              @' !(q (g (f (g (f (g y))))))
              @' ap g (p (f (g (f (g y)))))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. repeat rewrite <- maponpathsinv0.
           rewrite <- (maponpathscomp0 g). reflexivity. }
         intermediate_path (
              !(q (g y))
              @' ap (funcomp f g) (ap g ((!p y) @' ap f (!q (g y))))
              @' ap g (p (f (g (f (g y)))))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. repeat rewrite maponpathscomp0.
           repeat rewrite <- (maponpathscomp f g).
           repeat rewrite maponpathsinv0. repeat rewrite path_comp_inv_inv.
           apply (ap pathsinv0).
           assert (r := ! ap_fun_fun_fun_natl q (funcomp f g) q (g y)); simpl in r.
           rewrite maponpathsidfun in r. repeat rewrite <- (maponpathscomp f g) in r.
           unfold funcomp in r; simpl in r. repeat rewrite path_assoc.
           rewrite r. ap_pre_post_cat. clear r.
           assert (r := ! ap_fun_fun_fun_natl p g q y); simpl in r.
           rewrite maponpathsidfun in r. rewrite (maponpathscomp f). 
           rewrite (maponpathscomp g). rewrite (maponpathscomp g) in r.
           exact r. }
         intermediate_path (
              !(q (g y))
              @' ap g (ap (funcomp g f) ((!p y) @' ap f (!q (g y))))
              @' ap g (p (f (g (f (g y)))))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. rewrite <- (maponpathscomp g f).
           rewrite <- (maponpathscomp f g). reflexivity. }
         intermediate_path (
              !(q (g y))
              @' ap g (ap (funcomp g f) ((!p y) @' ap f (!q (g y)))
                    @' p (f (g (f (g y)))))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. rewrite <- maponpathscomp0. apply (ap (ap g)). 
           reflexivity. }
         intermediate_path (
              !(q (g y))
              @' ap g (p y @' ((!p y) @' ap f (!q (g y))))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. rewrite <- (maponpathscomp g f).
           repeat rewrite maponpathscomp0. repeat rewrite maponpathsinv0.
           repeat rewrite <- path_assoc. repeat apply path_inv_rotate_ll.
           repeat rewrite path_assoc. repeat apply path_inv_rotate_rr.
           apply pathsinv0. repeat rewrite <- (maponpathscomp0 g).
           apply (ap (ap g)). rewrite h.
           assert (r := ! ap_fun_fun_natl p p (f (g y))); simpl in r.
           rewrite maponpathsidfun in r. unfold funcomp in *; simpl in *.
           repeat rewrite <- (maponpathscomp g f) in r.
           repeat rewrite (path_assoc _ _ (p y)). rewrite r.
           repeat rewrite <- (path_assoc _ _ (p y)). apply (ap pre_cat). clear r.
           assert (r := ap_fun_fun_natl p p y); simpl in r.
           rewrite maponpathsidfun in r.
           repeat rewrite <- (maponpathscomp g f) in r. exact r. }
         intermediate_path (
              (!q (g y))
              @' ap g (ap f (!q (g y)))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. repeat rewrite <- maponpathsinv0.
           apply (ap (ap g)). rewrite pathsinv0r. reflexivity. }
         intermediate_path (
              (!q (g y))
              @' ap (funcomp f g) (!q (g y))
              @' q (g (f (g y)))
              @' q (g y)).
         { ap_pre_post_cat. rewrite <- (maponpathscomp f g). 
           reflexivity. }
         intermediate_path ((!q (g y)) @' q (g y) @' (!q (g y)) @' q (g y)).
         { ap_pre_post_cat. rewrite <- (maponpathscomp f g). 
           apply path_inv_rotate_ll. repeat rewrite path_assoc.
           apply path_inv_rotate_rr. 
           assert (r := ! ap_fun_fun_natl q q (g y)); simpl in r.
           rewrite maponpathsidfun in r. rewrite (maponpathscomp f g).
           exact r. }
         rewrite pathsinv0l. simpl. rewrite pathsinv0l. reflexivity. Qed.

End A.

Definition Equiv X Y :=
  { f:X->Y & 
  { g:Y->X &
  { p:forall y, f(g y) = y & 
  { q:forall x, g(f x) = x &
      forall x, ap f (q x) = p(f x)}}}}.

Definition makeEquiv X Y f g p q h := (f,,(g,,(p,,(q,,h)))) : Equiv X Y.

Definition mapEquiv {X Y} (f:Equiv X Y) : X->Y := pr1 f.

Coercion mapEquiv : Equiv >-> Funclass.

Definition invMap {X Y} : Equiv X Y -> Y->X.
Proof. intros ? ? f. exact (pr1 (pr2 f)). Defined.

Definition homotEquivInvequiv {X Y} (f:Equiv X Y) : forall y, f (invMap f y) = y
  := pr1 (pr2 (pr2 f)).

Definition homotInvequivEquiv {X Y} (f:Equiv X Y) : forall y, invMap f (f y) = y
  := pr1 (pr2 (pr2 (pr2 f))).

Definition EquivAdjointness {X Y} (f:Equiv X Y)
  : forall x, ap f (homotInvequivEquiv f x) = homotEquivInvequiv f (f x)
  := pr2 (pr2 (pr2 (pr2 f))).

Definition invEquiv {X Y} : Equiv X Y -> Equiv Y X.
Proof. intros ? ? [f [g [p [q h]]]]. refine (makeEquiv Y X g f q p _).
       intro y. apply other_adjoint. assumption. Defined.

Definition weq_to_Equiv X Y : weq X Y -> Equiv X Y.
  intros ? ? [f r].
  unfold isweq in r.
  set (g := fun y => hfiberpr1 f y (the (r y))).
  set (p := fun y => pr2 (pr1 (r y))).
  simpl in p.
  set (L := fun x => pr2 (r (f x)) (hfiberpair f x (idpath (f x)))).
  set (q := fun x => ap pr1 (L x)).
  set (q' := fun x => !q x).  
  refine (makeEquiv X Y f g p q' 
             (fun x => 
                 ! transportf_fun_idpath x (pr1 (pr1 (r (f x)))) (q x) (idpath (f x))
                 @ (ap_pr2 (L x)))).
Defined.

Definition weq_to_Equiv_inv X Y : weq X Y -> Equiv Y X.
  intros ? ? [f r].
  unfold isweq in r.
  set (g := fun y => hfiberpr1 f y (the (r y))).
  set (p := fun y => pr2 (pr1 (r y))).
  simpl in p.
  set (L := fun x => pr2 (r (f x)) (hfiberpair f x (idpath (f x)))).
  set (q := fun x => ap pr1 (L x)).
  set (q' := fun x => !q x).  
  refine (makeEquiv Y X g f q' p _).
  intro y.
  admit.
Admitted.

Definition Equiv_to_weq X Y : Equiv X Y -> weq X Y.
Proof. intros ? ? [f [g [p [q h]]]]. exists f. unfold isweq. intro y.
       exists (g y,,p y). intros [x []]. apply (total2_paths2 (!q x)). 
       refine (_ @ h x). destruct (q x). reflexivity. Defined.

Definition Equiv_to_invweq X Y : Equiv X Y -> weq Y X.
Proof. intros ? ? [f [g [p [q h]]]]. exists g. unfold isweq. intro x.
       exists (f x,,q x). intros [y []]. apply (total2_paths2 (!p y)). 
       admit.
Admitted.

Module Equiv'.
  Record data X Y := make {
         f :> X -> Y; g : Y -> X;
         p : forall y, f(g y) = y;
         q : forall x, g(f x) = x;
         h : forall x y (r:f x = y), 
             transportf (fun x':X => f x' = y) (! q x @ ap g r) r = p y }.
End Equiv'.

Definition Equiv'_to_weq X Y : Equiv'.data X Y -> weq X Y.
Proof. intros ? ? a. destruct a. exists f. unfold isweq. intro y.
       exists (g y,,p y). intros [x r]. 
       exact (total2_paths2 (! q x @ ap g r) (h x y r)). Defined.

Goal (* weq_to_Equiv' *) forall X Y, weq X Y -> Equiv'.data X Y.
Proof. intros ? ? [f iw].
       set (g := fun y => hfiberpr1 f y (the (iw y))).
       set (p := fun y => pr2 (pr1 (iw y))).
       simpl in p.
       set (L := fun x => pr2 (iw (f x)) (hfiberpair f x (idpath (f x)))).
       set (q := fun x => ap pr1 (L x)).
       set (q' := fun x => !q x).  
       refine (Equiv'.make X Y f g p q' _).
       intros.
       unfold isweq in iw.
       assert (a := pr2 (iw y) (hfiberpair f x r)).
       assert (b := ap_pr2 a).
       change (pr2 (pr1 (iw y))) with (p y) in b.
       refine (_@b).
       destruct r.
       rewrite ap_idpath.
       rewrite pathscomp0rid.
       rewrite transportf_fun_idpath.
       { rewrite pathsinv0inv0. admit. } reflexivity. Admitted.

Goal (* invequiv' *) forall X Y, Equiv'.data X Y -> Equiv'.data Y X.
Proof. intros ? ? [f g p q h].
       refine (Equiv'.make Y X g f (fun y => q y) (fun x => p x) _).
       intros. destruct r. rewrite ap_idpath. rewrite pathscomp0rid.
       admit. Admitted.

Definition weqcompidl {X Y} (f:weq X Y) : weqcomp (idweq X) f = f.
Proof. intros. apply (invmaponpathsincl _ (isinclpr1weq _ _)).
       apply funextsec; intro x; simpl. reflexivity. Defined.

Definition weqcompidr {X Y} (f:weq X Y) : weqcomp f (idweq Y) = f.
Proof. intros. apply (invmaponpathsincl _ (isinclpr1weq _ _)).
       apply funextsec; intro x; simpl. reflexivity. Defined.

Definition weqcompinvl {X Y} (f:weq X Y) : weqcomp (invweq f) f = idweq Y.
Proof. intros. apply (invmaponpathsincl _ (isinclpr1weq _ _)).
       apply funextsec; intro y; simpl. apply homotweqinvweq. Defined.

Definition weqcompinvr {X Y} (f:weq X Y) : weqcomp f (invweq f) = idweq X.
Proof. intros. apply (invmaponpathsincl _ (isinclpr1weq _ _)).
       apply funextsec; intro x; simpl. apply homotinvweqweq. Defined.

Definition weqcompassoc {X Y Z W} (f:weq X Y) (g:weq Y Z) (h:weq Z W) :
  weqcomp (weqcomp f g) h = weqcomp f (weqcomp g h).
Proof. intros. apply (invmaponpathsincl _ (isinclpr1weq _ _)).
       apply funextsec; intro x; simpl. reflexivity. Defined.

Definition weqcompweql {X Y Z} (f:weq X Y) :
  isweq (fun g:weq Y Z => weqcomp f g).
Proof. intros. refine (gradth _ _ _ _).
       { intro h. exact (weqcomp (invweq f) h). }
       { intro g. simpl. rewrite <- weqcompassoc. rewrite weqcompinvl.
         apply weqcompidl. }
       { intro h. simpl. rewrite <- weqcompassoc. rewrite weqcompinvr.
         apply weqcompidl. } Defined.

Definition weqcompweqr {X Y Z} (g:weq Y Z) :
  isweq (fun f:weq X Y => weqcomp f g).
Proof. intros. refine (gradth _ _ _ _).
       { intro h. exact (weqcomp h (invweq g)). }
       { intro f. simpl. rewrite weqcompassoc. rewrite weqcompinvr.
         apply weqcompidr. }
       { intro h. simpl. rewrite weqcompassoc. rewrite weqcompinvl.
         apply weqcompidr. } Defined.

Definition weqcompinjr {X Y Z} {f f':weq X Y} (g:weq Y Z) :
  weqcomp f g = weqcomp f' g -> f = f'.
Proof. intros ? ? ? ? ? ?.
       apply (invmaponpathsincl _ (isinclweq _ _ _ (weqcompweqr g))).
Defined.

Definition weqcompinjl {X Y Z} (f:weq X Y) {g g':weq Y Z} :
  weqcomp f g = weqcomp f g' -> g = g'.
Proof. intros ? ? ? ? ? ?.
       apply (invmaponpathsincl _ (isinclweq _ _ _ (weqcompweql f))).
Defined.

Definition invweqcomp {X Y Z} (f:weq X Y) (g:weq Y Z) :
  invweq (weqcomp f g) = weqcomp (invweq g) (invweq f).
Proof. intros. apply (weqcompinjr (weqcomp f g)). rewrite weqcompinvl.
       rewrite weqcompassoc. rewrite <- (weqcompassoc (invweq f)).
       rewrite weqcompinvl. rewrite weqcompidl. rewrite weqcompinvl. reflexivity.
Defined.

Definition weq_pathscomp0r {X} x {y z:X} (p:y = z) : weq (x = y) (x = z).
Proof. intros. exact (weqpair _ (isweqpathscomp0r _ p)). Defined.

Definition iscontrretract_compute {X Y} (p:X->Y) (s:Y->X) 
           (eps:forall y : Y, p (s y) = y) (is:iscontr X) : 
  the (iscontrretract p s eps is) = p (the is).
Proof. intros. unfold iscontrretract. destruct is as [ctr uni].
       simpl. reflexivity. Defined.

Definition iscontrweqb_compute {X Y} (w:weq X Y) (is:iscontr Y) :
  the (iscontrweqb w is) = invmap w (the is).
Proof. intros. unfold iscontrweqb. rewrite iscontrretract_compute.
       reflexivity. Defined.

Definition compute_iscontrweqb_weqfibtototal_1 {T} {P Q:T->Type}
           (f:forall t, weq (P t) (Q t)) 
           (is:iscontr (total2 Q)) :
  pr1 (the (iscontrweqb (weqfibtototal P Q f) is)) = pr1 (the is).
Proof. intros. destruct is as [ctr uni]. reflexivity. Defined.

Definition compute_pr1_invmap_weqfibtototal {T} {P Q:T->Type}
           (f:forall t, weq (P t) (Q t)) 
           (w:total2 Q) :
  pr1 (invmap (weqfibtototal P Q f) w) = pr1 w.
Proof. intros. reflexivity. Defined.

Definition compute_pr2_invmap_weqfibtototal {T} {P Q:T->Type}
           (f:forall t, weq (P t) (Q t)) 
           (w:total2 Q) :
  pr2 (invmap (weqfibtototal P Q f) w) = invmap (f (pr1 w)) (pr2 w).
Proof. intros. reflexivity. Defined.

Definition compute_iscontrweqb_weqfibtototal_3 {T} {P Q:T->Type}
           (f:forall t, weq (P t) (Q t)) 
           (is:iscontr (total2 Q)) :
  ap pr1 (iscontrweqb_compute (weqfibtototal P Q f) is) 
  =
  compute_iscontrweqb_weqfibtototal_1 f is.
Proof. intros. destruct is as [ctr uni]. reflexivity. Defined.

Definition iscontrcoconustot_comp {X} {x:X} :
  the (iscontrcoconustot X x) = tpair _ x (idpath x).
Proof. reflexivity. Defined.

Definition funfibtototal {X} (P Q:X->Type) (f:forall x:X, P x -> Q x) :
  total2 P -> total2 Q.
Proof. intros ? ? ? ? [x p]. exact (x,,f x p). Defined.

Definition weqfibtototal_comp {X} (P Q:X->Type) (f:forall x:X, weq (P x) (Q x)) :
  invmap (weqfibtototal P Q f) = funfibtototal Q P (fun x => invmap (f x)).
Proof. intros. apply funextsec; intros [x q]. reflexivity. Defined.

Definition eqweqmapap_inv {T} (P:T->Type) {t u:T} (e:t = u) (p:P u) :
  (eqweqmap (ap P e)) ((eqweqmap (ap P (!e))) p) = p.
Proof. intros. destruct e. reflexivity. Defined.

Definition eqweqmapap_inv' {T} (P:T->Type) {t u:T} (e:t = u) (p:P t) :
  (eqweqmap (ap P (!e))) ((eqweqmap (ap P e)) p) = p.
Proof. intros. destruct e. reflexivity. Defined.

Definition invmapweqcomp {X Y Z} (f:weq X Y) (g:weq Y Z) :
  invmap (weqcomp f g) = weqcomp (invweq g) (invweq f).
Proof. intros. exact (ap pr1weq (invweqcomp f g)). Defined.

Definition pr1hSet_injectivity (X Y:hSet) : weq (X = Y) (pr1hSet X = pr1hSet Y).
Proof. intros. apply weqonpathsincl. apply isinclpr1; intro T.
       apply isapropisaset. Defined.

Definition weqpr1_irr_sec {X} {P:X->Type}
           (irr:forall x (p q:P x), p = q) (sec:Section P) : weq (total2 P) X.
Proof. intros.
       set (isc := fun x => iscontraprop1 (invproofirrelevance _ (irr x)) (sec x)).
       apply Equiv_to_weq.
       refine (makeEquiv _ _ _ _ _ _ _).
       { exact pr1. } { intro x. exact (x,,sec x). } { intro x. reflexivity. }
       { intros [x p]. simpl. apply pair_path_in2. apply irr. }
       { intros [x p]. simpl. apply pair_path_in2_comp1. } Defined.

Definition invweqpr1_irr_sec {X} {P:X->Type}
           (irr:forall x (p q:P x), p = q) (sec:Section P) : weq X (total2 P).
Proof. intros.
       set (isc := fun x => iscontraprop1 (invproofirrelevance _ (irr x)) (sec x)).
       apply Equiv_to_weq.
       refine (makeEquiv _ _ _ _ _ _ _).
       { intro x. exact (x,,sec x). } { exact pr1. }
       { intros [x p]. simpl. apply pair_path_in2. apply irr. }
       { intro x. reflexivity. }
       { intro x'. simpl. rewrite (irrel_paths (irr _) (irr _ _ _) (idpath (sec x'))).
         reflexivity. } Defined.

Definition homotinvweqweq' {X} {P:X->Type} 
           (irr:forall x (p q:P x), p = q) (s:Section P) (w:total2 P) :
  invmap (weqpr1_irr_sec irr s) (weqpr1_irr_sec irr s w) = w.
Proof. intros ? ? ? ? [x p]. apply pair_path_in2. apply irr. Defined.

Definition homotinvweqweq'_comp {X} {P:X->Type}
           (irr:forall x (p q:P x), p = q) (sec:Section P) 
           (x:X) (p:P x) : 
  let f := weqpr1_irr_sec irr sec in
  let w := x,,p in
  let w' := invweq f x in
  @identity (w' = w)
            (homotinvweqweq' irr sec w)
            (pair_path_in2 P (irr x (sec x) (pr2 w))).
Proof. reflexivity.             (* don't change the proof *)
Defined.

Definition homotinvweqweq_comp {X} {P:X->Type}
           (irr:forall x (p q:P x), p = q) (sec:Section P) 
           (x:X) (p:P x) : 
  let f := weqpr1_irr_sec irr sec in
  let w := x,,p in
  let w' := invweq f x in
  @identity (w' = w)
            (homotinvweqweq f w)
            (pair_path_in2 P (irr x (sec x) (pr2 w))).
Proof. admit.
(*
       reflexivity.             (* don't change the proof *)
*)
Admitted.

Definition homotinvweqweq_comp_3 {X} {P:X->Type}
           (irr:forall x (p q:P x), p = q) (sec:Section P) 
           (x:X) (p:P x) : 
  let f := weqpr1_irr_sec irr sec in
  let g := invweqpr1_irr_sec irr sec in
  let w := x,,p in
  let w' := g x in
  @identity (w' = w)
            (homotweqinvweq g w)    (* !! *)
            (pair_path_in2 P (irr x (sec x) (pr2 w))).
Proof. reflexivity. Defined.

Definition loop_correspondence {T X Y}
           (f:weq T X) (g:T->Y)
           {t t':T} {l:t = t'}
           {m:f t = f t'} (mi:ap f l = m)
           {n:g t = g t'} (ni:ap g l = n) : 
     ap (funcomp (invmap f) g) m @ ap g (homotinvweqweq f t') 
  = ap g (homotinvweqweq f t) @ n.
Proof. intros. destruct ni, mi, l. simpl. rewrite pathscomp0rid. reflexivity.
Defined.

Definition loop_correspondence' {X Y} {P:X->Type} 
           (irr:forall x (p q:P x), p = q) (sec:Section P)
           (g:total2 P->Y)
           {w w':total2 P} {l:w = w'}
           {m:weqpr1_irr_sec irr sec w = weqpr1_irr_sec irr sec w'} (mi:ap (weqpr1_irr_sec irr sec) l = m)
           {n:g w = g w'} (ni:ap g l = n) : 
     ap (funcomp (invmap (weqpr1_irr_sec irr sec)) g) m @ ap g (homotinvweqweq' irr sec w') 
  = ap g (homotinvweqweq' irr sec w) @ n.
Proof. intros. destruct ni, mi, l. simpl. rewrite pathscomp0rid. reflexivity.
Defined.

(*
Local Variables:
compile-command: "make -C ../.. TAGS UniMath/Ktheory/Equivalences.vo"
End:
*)
