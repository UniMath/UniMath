(** * Equivalences *)

Require Import UniMath.Foundations.Basics.All.
Require Import UniMath.Ktheory.Utilities.
Require Import UniMath.Foundations.FunctionalExtensionality.
Require Import UniMath.Ktheory.Equivalences.

Definition weq_to_InverseEquivalence X Y : X ≃ Y -> Equivalence Y X.
  intros ? ? [f r].
  unfold isweq in r.
  set (g := fun y => hfiberpr1 f y (thePoint (r y))).
  set (p := fun y => pr2 (pr1 (r y))).
  simpl in p.
  set (L := fun x => pr2 (r (f x)) (hfiberpair f x (idpath (f x)))).
  set (q := fun x => ap pr1 (L x)).
  set (q' := fun x => !q x).  
  refine (makeEquivalence Y X g f q' p _).
  intro y.
  admit.
Admitted.

Definition Equivalence_to_invweq X Y : Equivalence X Y -> Y ≃ X.
Proof. intros ? ? [f [g [p [q h]]]]. exists g. unfold isweq. intro x.
       exists (f x,,q x). intros [y []]. apply (total2_paths2 (!p y)). 
       admit.
Admitted.

Module Equivalence'.
  Record data X Y := make {
         f :> X -> Y; g : Y -> X;
         p : ∀ y, f(g y) = y;
         q : ∀ x, g(f x) = x;
         h : ∀ x y (r:f x = y), 
             transportf (fun x':X => f x' = y) (! q x @ ap g r) r = p y }.
End Equivalence'.

Definition Equivalence'_to_weq X Y : Equivalence'.data X Y -> X ≃ Y.
Proof. intros ? ? a. destruct a. exists f. unfold isweq. intro y.
       exists (g y,,p y). intros [x r]. 
       exact (total2_paths2 (! q x @ ap g r) (h x y r)). Defined.

Goal (* weq_to_Equivalence' *) ∀ X Y, X ≃ Y -> Equivalence'.data X Y.
Proof. intros ? ? [f iw].
       set (g := fun y => hfiberpr1 f y (thePoint (iw y))).
       set (p := fun y => pr2 (pr1 (iw y))).
       simpl in p.
       set (L := fun x => pr2 (iw (f x)) (hfiberpair f x (idpath (f x)))).
       set (q := fun x => ap pr1 (L x)).
       set (q' := fun x => !q x).  
       refine (Equivalence'.make X Y f g p q' _).
       intros.
       unfold isweq in iw.
       assert (a := pr2 (iw y) (hfiberpair f x r)).
       assert (b := fiber_paths a).
       change (pr2 (pr1 (iw y))) with (p y) in b.
       refine (_@b).
       destruct r.
       rewrite maponpaths_idpath.
       rewrite pathscomp0rid.
       rewrite transportf_fun_idpath.
       { rewrite pathsinv0inv0. admit. } reflexivity. Admitted.

Goal (* invequiv' *) ∀ X Y, Equivalence'.data X Y -> Equivalence'.data Y X.
Proof. intros ? ? [f g p q h].
       refine (Equivalence'.make Y X g f (fun y => q y) (fun x => p x) _).
       intros. destruct r. rewrite maponpaths_idpath. rewrite pathscomp0rid.
       admit. Admitted.

Definition weq_pathscomp0r {X} x {y z:X} (p:y = z) : weq (x = y) (x = z).
Proof. intros. exact (weqpair _ (isweqpathscomp0r _ p)). Defined.

Definition iscontrretract_compute {X Y} (p:X->Y) (s:Y->X) 
           (eps:∀ y : Y, p (s y) = y) (is:iscontr X) : 
  thePoint (iscontrretract p s eps is) = p (thePoint is).
Proof. intros. unfold iscontrretract. destruct is as [ctr uni].
       simpl. reflexivity. Defined.

Definition iscontrweqb_compute {X Y} (w:X ≃ Y) (is:iscontr Y) :
  thePoint (iscontrweqb w is) = invmap w (thePoint is).
Proof. intros. unfold iscontrweqb. rewrite iscontrretract_compute.
       reflexivity. Defined.

Definition compute_iscontrweqb_weqfibtototal_1 {T} {P Q:T->Type}
           (f:∀ t, weq (P t) (Q t)) 
           (is:iscontr (totalSpace Q)) :
  pr1 (thePoint (iscontrweqb (weqfibtototal P Q f) is)) = pr1 (thePoint is).
Proof. intros. destruct is as [ctr uni]. reflexivity. Defined.

Definition compute_pr1_invmap_weqfibtototal {T} {P Q:T->Type}
           (f:∀ t, weq (P t) (Q t)) 
           (w:totalSpace Q) :
  pr1 (invmap (weqfibtototal P Q f) w) = pr1 w.
Proof. intros. reflexivity. Defined.

Definition compute_pr2_invmap_weqfibtototal {T} {P Q:T->Type}
           (f:∀ t, weq (P t) (Q t)) 
           (w:totalSpace Q) :
  pr2 (invmap (weqfibtototal P Q f) w) = invmap (f (pr1 w)) (pr2 w).
Proof. intros. reflexivity. Defined.

Definition compute_iscontrweqb_weqfibtototal_3 {T} {P Q:T->Type}
           (f:∀ t, weq (P t) (Q t)) 
           (is:iscontr (totalSpace Q)) :
  ap pr1 (iscontrweqb_compute (weqfibtototal P Q f) is) 
  =
  compute_iscontrweqb_weqfibtototal_1 f is.
Proof. intros. destruct is as [ctr uni]. reflexivity. Defined.

Definition iscontrcoconustot_comp {X} {x:X} :
  thePoint (iscontrcoconustot X x) = x,,idpath x.
Proof. reflexivity. Defined.

Definition funfibtototal {X} (P Q:X->Type) (f:∀ x:X, P x -> Q x) :
  totalSpace P -> totalSpace Q.
Proof. intros ? ? ? ? [x p]. exact (x,,f x p). Defined.

Definition weqfibtototal_comp {X} (P Q:X->Type) (f:∀ x:X, weq (P x) (Q x)) :
  invmap (weqfibtototal P Q f) = funfibtototal Q P (fun x => invmap (f x)).
Proof. intros. apply funextsec; intros [x q]. reflexivity. Defined.

Definition eqweqmapap_inv {T} (P:T->Type) {t u:T} (e:t = u) (p:P u) :
  (eqweqmap (ap P e)) ((eqweqmap (ap P (!e))) p) = p.
Proof. intros. destruct e. reflexivity. Defined.

Definition eqweqmapap_inv' {T} (P:T->Type) {t u:T} (e:t = u) (p:P t) :
  (eqweqmap (ap P (!e))) ((eqweqmap (ap P e)) p) = p.
Proof. intros. destruct e. reflexivity. Defined.

Definition weqpr1_irr_sec {X} {P:X->Type}
           (irr:∀ x (p q:P x), p = q) (sec:Section P) : weq (totalSpace P) X.
(* compare with weqpr1 *)
Proof. intros.
       set (isc := fun x => iscontraprop1 (invproofirrelevance _ (irr x)) (sec x)).
       apply Equivalence_to_weq.
       refine (makeEquivalence _ _ _ _ _ _ _).
       { exact pr1. } { intro x. exact (x,,sec x). } { intro x. reflexivity. }
       { intros [x p]. simpl. apply pair_path_in2. apply irr. }
       { intros [x p]. simpl. apply pair_path_in2_comp1. } Defined.

Definition invweqpr1_irr_sec {X} {P:X->Type}
           (irr:∀ x (p q:P x), p = q) (sec:Section P) : X ≃ (totalSpace P).
(* compare with weqpr1 *)
Proof. intros.
       set (isc := fun x => iscontraprop1 (invproofirrelevance _ (irr x)) (sec x)).
       apply Equivalence_to_weq.
       refine (makeEquivalence _ _ _ _ _ _ _).
       { intro x. exact (x,,sec x). } { exact pr1. }
       { intros [x p]. simpl. apply pair_path_in2. apply irr. }
       { intro x. reflexivity. }
       { intro x'. simpl. rewrite (irrel_paths (irr _) (irr _ _ _) (idpath (sec x'))).
         reflexivity. } Defined.

Definition homotinvweqweq' {X} {P:X->Type} 
           (irr:∀ x (p q:P x), p = q) (s:Section P) (w:totalSpace P) :
  invmap (weqpr1_irr_sec irr s) (weqpr1_irr_sec irr s w) = w.
Proof. intros ? ? ? ? [x p]. apply pair_path_in2. apply irr. Defined.

Definition homotinvweqweq'_comp {X} {P:X->Type}
           (irr:∀ x (p q:P x), p = q) (sec:Section P) 
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
           (irr:∀ x (p q:P x), p = q) (sec:Section P) 
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
           (irr:∀ x (p q:P x), p = q) (sec:Section P) 
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
           (f:T ≃ X) (g:T->Y)
           {t t':T} {l:t = t'}
           {m:f t = f t'} (mi:ap f l = m)
           {n:g t = g t'} (ni:ap g l = n) : 
     ap (funcomp (invmap f) g) m @ ap g (homotinvweqweq f t') 
  = ap g (homotinvweqweq f t) @ n.
Proof. intros. destruct ni, mi, l. simpl. rewrite pathscomp0rid. reflexivity.
Defined.

Definition loop_correspondence' {X Y} {P:X->Type} 
           (irr:∀ x (p q:P x), p = q) (sec:Section P)
           (g:totalSpace P->Y)
           {w w':totalSpace P} {l:w = w'}
           {m:weqpr1_irr_sec irr sec w = weqpr1_irr_sec irr sec w'} (mi:ap (weqpr1_irr_sec irr sec) l = m)
           {n:g w = g w'} (ni:ap g l = n) : 
     ap (funcomp (invmap (weqpr1_irr_sec irr sec)) g) m @ ap g (homotinvweqweq' irr sec w') 
  = ap g (homotinvweqweq' irr sec w) @ n.
Proof. intros. destruct ni, mi, l. simpl. rewrite pathscomp0rid. reflexivity.
Defined.

(*
Local Variables:
compile-command: "make -C ../.. TAGS TAGS-Ktheory UniMath/Ktheory/Equivalences.vo"
End:
*)

