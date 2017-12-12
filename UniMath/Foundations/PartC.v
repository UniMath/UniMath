(** * Univalent Foundations. Vladimir Voevodsky. Feb. 2010 - Sep. 2011. Port to coq
     trunk (8.4-8.5) in March 2014. The third part of the original uu0 file,
     created on Dec. 3, 2014.

   Only one universe is used, and it is never used as a type.

   The only axiom we use is [ funextemptyAxiom ], which is the functional
   extensionality axiom for functions with values in the empty type.  Any
   results that don't depend on axioms should be in an earlier file.

*)

(** ** Contents
- More results on propositions
- Isolated points and types with decidable equality
 - Basic results on complements to a point
 - Basic results on types with an isolated point
 - Weak equivalences and isolated points
 - Recomplement on functions
 - Standard weak equivalences between [compl T t1] and [compl T t2]
   for isolated t1 and t2
 - Transposition of two isolated points
 - Types with decidable equality
  - unit
  - bool
  - coprod
 - Splitting of X into a coproduct by X -> bool
- Semi-boolean hfiber of functions over isolated points
 - hfibers of ii1 and ii2
 - ii1 and ii2 map isolated points to isolated points
 - hfibers of coprodf of two functions
 - Coproduct of two functions of h-level n is of h-level n
 - h-levels of coproducts and their component types
 - h-fibers of the sum of two functions sumofmaps f g
 - The sum of two functions of h-level (S (S n)) is of h-level
   (S (S n))
 - The sum of two functions of h-level n with non-intersecting images
   is of h-level n
 - Coproducts and complements
- Decidable propositions and decidable inclusions
 - Decidable propositions
 - Paths to and from an isolated point form a decidable proposition
 - Decidable inclusions
 - Decidable inclusions and isolated points
 - Decidable inclusions and coprojections
 *)

(** ** Preamble *)

(** Settings *)

(* The following line has to be removed for the file to compile with Coq8.2 *)
Unset Automatic Introduction.

(** Imports *)

Require Export UniMath.Foundations.PartB.
Require Export UniMath.Foundations.UnivalenceAxiom.

(** *** More results on propositions *)


Theorem isapropneg (X : UU) : isaprop (neg X).
Proof.
  intro. apply invproofirrelevance.
  intros x x'. apply (funextempty X x x').
Defined.

Lemma isaprop_isProofIrrelevant X : isaprop (isProofIrrelevant X).
Proof.
  intros. apply invproofirrelevance. intros i j.
  apply funextsec; intro x; apply funextsec; intro y.
  generalize (i x y) as p; generalize (j x y) as q; intros.
  apply isProofIrrelevant_paths. assumption.
Defined.

(** See also [ isapropneg2 ] *)


Corollary isapropdneg (X : UU) : isaprop (dneg X).
Proof.
  intro. apply (isapropneg (neg X)).
Defined.


Definition isaninvprop (X : UU) := isweq (todneg X).

Definition invimpl (X : UU) (is : isaninvprop X) : (dneg X) -> X
  := invmap (weqpair (todneg X) is).


Lemma isapropaninvprop (X : UU) : isaninvprop X -> isaprop X.
Proof.
  intros X X0.
  apply (isofhlevelweqb (S O) (weqpair (todneg X) X0) (isapropdneg X)).
Defined.


Theorem isaninvpropneg (X : UU) : isaninvprop (neg X).
Proof.
  intros.
  set (f := todneg (neg X)).
  set (g := negf (todneg X)).
  set (is1 := isapropneg X).
  set (is2 := isapropneg (dneg X)).
  apply (isweqimplimpl f g is1 is2).
Defined.


Theorem isapropdec (X : UU) : isaprop X -> isaprop (decidable X).
(* uses [funextemptyAxiom] *)
Proof.
  intros ? i. apply isapropcoprod.
  - exact i.
  - apply isapropneg.
  - exact (λ x n, n x).
Defined.

(** ** Isolated points and types with decidable equality. *)


(** *** Basic results on complements to a point *)


Definition compl (X : UU) (x : X) := ∑ x', x != x'.
Definition complpair (X : UU) (x : X) := tpair (λ x' : X, x != x').
Definition pr1compl (X : UU) (x : X) := @pr1 _ (λ x' : X, x != x').


Lemma isinclpr1compl (X : UU) (x : X) : isincl (pr1compl X x).
Proof.
  intros. apply (isinclpr1 _ (λ x' : X, isapropneg _)).
Defined.

Definition compl_ne (X:UU) (x:X) (neq_x : neqPred x) := ∑ y, neq_x y.

Definition compl_ne_pair (X : UU) (x : X) (neq_x : neqPred x) (y : X)
           (ne :neq_x y) :
  compl_ne X x neq_x := (y,,ne).

Definition pr1compl_ne (X : UU) (x : X) (neq_x : neqPred x)
           (c : compl_ne X x neq_x) :
  X := pr1 c.

Definition make_negProp {P : UU} : negProp P.
Proof.
  intros. exists (¬ P). split.
       - apply isapropneg.  (* uses [funextemptyAxiom] *)
       - apply isrefl_logeq.
Defined.

Definition make_neqProp {X : UU} (x y : X) : neqProp x y.
Proof.
  intros. apply make_negProp.
Defined.

Lemma isinclpr1compl_ne (X : UU) (x : X) (neq_x : neqPred x) :
  isincl (pr1compl_ne X x neq_x).
Proof.
  intros. apply isinclpr1. intro y. apply negProp_to_isaprop.
Defined.

Lemma compl_ne_weq_compl (X : UU) (x : X) (neq_x : neqPred x) :
  compl X x ≃ compl_ne X x neq_x.
Proof.
  (* uses [funextemptyAxiom] *)
  intros. apply weqfibtototal; intro y. apply weqiff.
  - apply negProp_to_iff.
  - apply isapropneg.
  - apply negProp_to_isaprop.
Defined.

Lemma compl_weq_compl_ne (X : UU) (x : X) (neq_x : neqPred x) :
  compl_ne X x neq_x ≃ compl X x.
Proof.
  (* uses [funextemptyAxiom] *)
  intros. apply weqfibtototal; intro y. apply weqiff.
  - apply issymm_logeq. apply negProp_to_iff.
  - apply negProp_to_isaprop.
  - apply isapropneg.
Defined.

Definition recompl (X : UU) (x : X) : compl X x ⨿ unit -> X
  := λ u : _,
       match u with
       | ii1 x0 => pr1compl _ _ x0
       | ii2 t => x
       end.

Definition recompl_ne (X : UU) (x : X) (neq_x:neqPred x) :
  compl_ne X x neq_x ⨿ unit -> X.
Proof.
  intros ? ? ? w.
  induction w as [c|t].
  - exact (pr1compl_ne _ _ _ c).
  - exact x.
Defined.

Definition maponcomplincl {X Y : UU} (f : X -> Y) (is : isincl f) (x : X) :
  compl X x -> compl Y (f x)
  := λ x0' : _,
       match x0' with
         tpair _ x' neqx => tpair _ (f x')
                                 (negf (invmaponpathsincl  _ is x x') neqx)
       end.

Definition maponcomplincl_ne {X Y : UU} (f : X -> Y) (is : isincl f) (x : X)
           (neq_x : neqPred x) (neq_fx : neqPred (f x))
  : compl_ne X x neq_x -> compl_ne Y (f x) neq_fx.
Proof.
  intros ? ? ? ? ? ? ? c.
  set (x' := pr1 c).
  set (neqx := pr2 c).
  exact (f x',,neg_to_negProp (nP := neq_fx (f x'))
           (negf (invmaponpathsincl _ is x x') (negProp_to_neg neqx))).
Defined.

Definition weqoncompl {X Y : UU} (w : X ≃ Y) x : compl X x ≃ compl Y (w x).
Proof.
  (* uses [funextemptyAxiom] *)
  intros. intermediate_weq (∑ x', w x != w x').
  - apply weqfibtototal; intro x'. apply weqiff.
    {apply logeqnegs. apply weq_to_iff. apply weqonpaths. }
    {apply isapropneg. }
    {apply isapropneg. }
  - refine (weqfp _ _).
Defined.

Definition weqoncompl_ne {X Y : UU} (w : X ≃ Y) (x : X) (neq_x : neqPred x)
           (neq_wx : neqPred (w x))
  : compl_ne X x neq_x ≃ compl_ne Y (w x) neq_wx.
Proof.
  intros. intermediate_weq (∑ x', neq_wx (w x')).
  - apply weqfibtototal; intro x'.
    apply weqiff.
    {apply (logeq_trans (Y := x != x')).
     {apply issymm_logeq, negProp_to_iff. }
     apply (logeq_trans (Y := w x != w x')).
     {apply logeqnegs. apply weq_to_iff. apply weqonpaths. }
     apply negProp_to_iff. }
    {apply negProp_to_isaprop. }
    {apply negProp_to_isaprop. }
  - refine (weqfp _ _).
Defined.

Definition weqoncompl_compute {X Y : UU} (w : X ≃ Y) (x : X) :
  ∏ x', pr1 (weqoncompl w x x') = w (pr1 x').
Proof.
  intros. induction x' as [x' b]. apply idpath.
Defined.

Definition weqoncompl_ne_compute {X Y : UU}
           (w : X ≃ Y) (x : X) (neq_x : neqPred x) (neq_wx : neqPred (w x)) x' :
  pr1 (weqoncompl_ne w x neq_x neq_wx x') = w (pr1 x').
Proof.
  intros. apply idpath.
Defined.

Definition homotweqoncomplcomp {X Y Z : UU} (f : X ≃ Y) (g : Y ≃ Z)
           (x : X) : homot (weqcomp (weqoncompl f x) (weqoncompl g (f x)))
                           (weqoncompl (weqcomp f g) x).
Proof.
  intros. intro x'. induction x' as [ x' nexx' ].
  apply (invmaponpathsincl _ (isinclpr1compl Z _) _ _).
  simpl. apply idpath.
Defined.

(** *** Decomposition of a type with an isolated point into two parts [ weqrecompl ] *)

Definition invrecompl (X : UU) (x : X) (is : isisolated X x) :
  X -> coprod (compl X x) unit
  := λ x' : X, match (is x') with
                | ii1 e => ii2 tt
                | ii2 phi => ii1 (complpair _ _ x' phi)
                end.

Definition invrecompl_ne (X : UU) (x : X) (neq_x : neqPred x)
           (is : isisolated X x) : X -> compl_ne X x neq_x ⨿ unit.
Proof.
  intros ? ? ? ? y. induction (is y) as [k|k].
  - exact (ii2 tt).
  - exact (ii1 (compl_ne_pair X x neq_x y (neg_to_negProp k))).
Defined.

Theorem isweqrecompl_ne (X : UU) (x : X) (is : isisolated X x)
        (neq_x : neqPred x) : isweq (recompl_ne _ x neq_x).
Proof.
  (* does not use [funextemptyAxiom] *)
  intros.
  set (f := recompl_ne X x neq_x). set (g := invrecompl_ne X x neq_x is).
  refine (gradth f g _ _).
  {intro u. induction (is (f u)) as [ eq | ne ].
   - induction u as [ c | u].
     + simpl. induction c as [ t neq ]; simpl; simpl in eq.
       contradicts (negProp_to_neg neq) eq.
     + induction u.
       intermediate_path (g x).
       {apply maponpaths. exact (pathsinv0 eq). }
       {unfold g, invrecompl_ne. induction (is x) as [ i | e ].
        {apply idpath. }
        {simpl. contradicts e (idpath x). }}
   - induction u as [ c | u ]. simpl.
     + induction c as [ y neq ]; simpl. unfold g, invrecompl_ne.
       induction (is y) as [ eq' | ne' ].
       {contradicts (negProp_to_neg neq) eq'. }
       {induction (ii2 ne') as [eq|neq'].
        {simpl. contradicts eq ne'. }
        {simpl. apply maponpaths. unfold compl_ne_pair. apply maponpaths.
         apply proofirrelevance. exact (pr1 (pr2 (neq_x y))). }}
     + induction u. unfold f,g,invrecompl_ne;simpl.
       induction (is x) as [eq|neq].
       {simpl. apply idpath. }
       {apply fromempty. apply neq. apply idpath. }}
  {intro y. unfold f,g,invrecompl_ne;simpl.
   induction (is y) as [eq|neq].
   - induction eq. apply idpath.
   - simpl. apply idpath. }
Defined.

Theorem isweqrecompl_ne' (X : UU) (x : X) (is : isisolated X x)
        (neq_x : neqPred x) : isweq (recompl_ne _ x neq_x).
Proof.
  (* an alternative proof *)
  intros. set (f := recompl_ne X x neq_x). intro y.
  unfold neqPred,negProp in neq_x; unfold isisolated in is.
  apply (iscontrweqb (weqtotal2overcoprod _)). induction (is y) as [eq|ne].
  {induction eq. refine (iscontrweqf (weqii2withneg _ _) _).
   {intros z; induction z as [z e]; induction z as [z neq]; simpl in *.
    contradicts (!e) (negProp_to_neg neq). }
   {change x with (f (ii2 tt)). simple refine ((_,,_),,_).
    {exact tt. }
    {apply idpath. }
    {intro w. induction w as [t e]. unfold f in *; simpl in *. induction t.
     apply maponpaths. apply isaproppathsfromisolated. exact is. }}}
  {refine (iscontrweqf (weqii1withneg _ _) _).
   {intros z; induction z as [z e]; simpl in *. contradicts ne e. }
   {simple refine ((_,,_),,_).
    {exists y. apply neg_to_negProp. assumption. }
    {simpl. apply idpath. }
    intros z; induction z as [z e]; induction z as [z neq];
      induction e; simpl in *.
    induction (proofirrelevance _ (pr1 (pr2 (neq_x z))) neq
                                (neg_to_negProp ne)).
    apply idpath.
  }}
Defined.

Definition weqrecompl_ne (X : UU) (x : X) (is : isisolated X x)
           (neq_x : neqPred x) : compl_ne X x neq_x ⨿ unit ≃ X
  := weqpair _ (isweqrecompl_ne X x is neq_x).

Theorem isweqrecompl (X : UU) (x : X) (is : isisolated X x) :
  isweq (recompl _ x).
Proof.
  intros. set (f := recompl _ x). set (g := invrecompl X x is).
  unfold invrecompl in g. simpl in g.
  assert (efg: ∏ x' : X, paths (f (g x')) x').
  {
    intro. induction (is x') as [ x0 | e ].
    - induction x0. unfold f. unfold g. simpl. unfold recompl. simpl.
      induction (is x) as [ x0 | e ].
      + simpl. apply idpath.
      + induction (e (idpath x)).
    - unfold f. unfold g. simpl. unfold recompl. simpl.
      induction (is x') as [ x0 | e0 ].
      + induction (e x0).
      + simpl. apply idpath.
  }
  assert (egf : ∏ u : coprod (compl X x) unit, paths (g (f u)) u).
  {
    unfold isisolated in is. intro. induction (is (f u)) as [ p | e ].
    - induction u as [ c | u].
      + simpl. induction c as [ t x0 ]. simpl in p. induction (x0 p).
      + induction u. assert (e1 : paths (g (f (ii2 tt))) (g x)).
        apply (maponpaths g p).
        assert (e2 : paths (g x) (ii2 tt)).
        {
          unfold g. induction (is x) as [ i | e ].
          apply idpath.
          induction (e (idpath x)).
        }
        apply (pathscomp0 e1 e2).
    - induction u as [ c | u ]. simpl. induction c as [ t x0 ].
      simpl. unfold isisolated in is. unfold g. induction (is t) as [ p | e0 ].
      induction (x0 p). simpl in g.  unfold f. unfold recompl. simpl in e.
      assert (ee : e0 = x0)
        by apply (proofirrelevance _ (isapropneg (x = t))).
      induction ee. apply idpath.
      unfold f. unfold g. simpl. induction u. induction (is x).
      + apply idpath.
      + induction (e (idpath x)).
  }
  apply (gradth f g egf efg).
Defined.

Theorem isweqrecompl' (X : UU) (x : X) (is : isisolated X x) :
  isweq (recompl _ x).
Proof.
  (* alternative proof, spoils a computation below if used in [weqrecompl],
     so unused *)
  intros. set (neq_x := λ y, make_neqProp x y).
  apply (isweqhomot (weqrecompl_ne X x is neq_x
                                   ∘ weqcoprodf (compl_ne_weq_compl X x neq_x)
                                   (idweq unit))%weq).
  {intro y. induction y as [y|t]; apply idpath. }
  apply weqproperty.
Defined.

Definition weqrecompl (X : UU) (x : X) (is : isisolated _ x) :
  compl X x ⨿ unit ≃ X := weqpair _ (isweqrecompl X x is).

(** *** Theorem saying that [ recompl ] commutes up to homotopy with [ maponcomplweq ] *)

Theorem homotrecomplnat {X Y : UU} (w : X ≃ Y) (x : X) (a : compl X x ⨿ unit) :
  recompl Y (w x) (coprodf (weqoncompl w x) (idfun unit) a)
  = w (recompl X x a).
Proof.
  intros. induction a as [ ane | t ]. induction ane as [ a ne ]. simpl.
  apply idpath. induction t. simpl. apply idpath.
Defined.



(** *** Recomplement on functions *)


Definition recomplf {X Y : UU} (x : X) (y : Y) (isx : isisolated X x)
           (f : compl X x -> compl Y y) : X -> Y
  := funcomp (funcomp (invmap (weqrecompl X x isx)) (coprodf f (idfun unit)))
             (recompl Y y).

Definition weqrecomplf {X Y : UU} (x : X) (y : Y) (isx : isisolated X x)
           (isy : isisolated Y y) (w : (compl X x) ≃ (compl Y y)) : X ≃ Y
  := weqcomp (weqcomp (invweq (weqrecompl X x isx)) (weqcoprodf w (idweq unit)))
             (weqrecompl Y y isy).

Definition homotrecomplfhomot {X Y : UU} (x : X) (y : Y) (isx : isisolated X x)
           (f f' : compl X x -> compl Y y) (h : homot f f') :
  homot (recomplf x y isx f) (recomplf x y isx f').
Proof.
  intros. intro a. unfold recomplf.
  apply (maponpaths (recompl Y y)
                    (homotcoprodfhomot _ _ _ _ h (λ t : unit, idpath t)
                                       (invmap (weqrecompl X x isx) a))).
Defined.

Lemma pathsrecomplfxtoy {X Y : UU} (x : X) (y : Y) (isx : isisolated X x)
      (f : compl X x -> compl Y y) : (recomplf x y isx f x) = y.
Proof.
  intros. unfold recomplf. unfold weqrecompl. unfold invmap. simpl.
  unfold invrecompl. unfold funcomp. induction (isx x) as [ i1 | i2 ].
  - simpl. apply idpath.
  - induction (i2 (idpath _)).
Defined.

Definition homotrecomplfcomp {X Y Z : UU} (x : X) (y : Y) (z : Z)
           (isx : isisolated X x) (isy : isisolated Y y)
           (f : compl X x -> compl Y y) (g : compl Y y -> compl Z z) :
  homot (funcomp (recomplf x y isx f) (recomplf y z isy g))
        (recomplf x z isx (funcomp f g)).
Proof.
  intros. intro x'. unfold recomplf.
  set (e := homotinvweqweq (weqrecompl Y y isy)
                           (coprodf f (idfun unit)
                                    (invmap (weqrecompl X x isx) x'))).
  unfold funcomp. simpl in e. simpl. rewrite e.
  set (e' := homotcoprodfcomp f (idfun unit) g (idfun unit)
                              (invmap (weqrecompl X x isx) x')).
  unfold funcomp in e'. rewrite e'. apply idpath.
Defined.


Definition homotrecomplfidfun {X : UU} (x : X) (isx : isisolated X x) :
  homot (recomplf x x isx (idfun (compl X x))) (idfun _).
Proof.
  intros. intro x'. unfold recomplf. unfold weqrecompl. unfold invmap. simpl.
  unfold invrecompl. unfold funcomp. induction (isx x') as [ e | ne ].
  - simpl. apply e.
  - simpl. apply idpath.
Defined.



Lemma ishomotinclrecomplf {X Y : UU} (x : X) (y : Y) (isx : isisolated X x)
      (f : compl X x -> compl Y y) (x'n : compl X x) (y'n : compl Y y)
      (e : paths (recomplf x y isx f (pr1 x'n)) (pr1 y'n)) : (f x'n) = y'n.
Proof.
  intros. induction x'n as [ x' nexx' ]. induction y'n as [ y' neyy' ].
  simpl in e . apply (invmaponpathsincl _ (isinclpr1compl _ _)). simpl.
  rewrite (pathsinv0 e). unfold recomplf. unfold invmap. unfold coprodf.
  simpl. unfold funcomp. unfold invrecompl.
  induction (isx x') as [ exx' | nexx'' ].
  - induction (nexx' exx').
  - simpl. assert (ee : nexx' = nexx'').
    apply (proofirrelevance _ (isapropneg _)).
    rewrite ee. apply idpath.
Defined.





(** *** Equivalence between [ compl T t1 ] and [ compl T t2 ] for isolated [ t1 t2 ] *)

Definition funtranspos0 {T: UU} (t1 t2 : T) (is2 : isisolated T t2)
           (x : compl T t1) : compl T t2
  := match (is2 (pr1 x)) with
     | ii1 e =>
       match (is2 t1) with
       | ii1 e' => fromempty (pr2 x (pathscomp0 (pathsinv0 e') e))
       | ii2 ne' => complpair T t2 t1 ne' end
     | ii2 ne => complpair T t2 (pr1 x) ne end.

Definition homottranspos0t2t1t1t2 {T : UU} (t1 t2 : T)
           (is1 : isisolated T t1) (is2 : isisolated T t2) :
  funtranspos0 t2 t1 is1 ∘ funtranspos0 t1 t2 is2 ~ idfun _.
Proof.
  intros. intro x. unfold funtranspos0. unfold funcomp.
       induction x as [ t net1 ]; simpl.
       induction (is2 t) as [ et2 | net2 ].
       - induction (is2 t1) as [ et2t1 | net2t1 ].
         + induction (net1 (pathscomp0 (pathsinv0 et2t1) et2)).
         + simpl. induction (is1 t1) as [ e | ne ].
           * induction (is1 t2) as [ et1t2 | net1t2 ].
             {induction (net2t1 (pathscomp0 (pathsinv0 et1t2) e)). }
             {apply (invmaponpathsincl _ (isinclpr1compl _ _)).
              simpl. exact et2. }
           * induction (ne (idpath _)).
       - simpl. induction (is1 t) as [ et1t | net1t ].
         + induction (net1 et1t).
         + apply (invmaponpathsincl _ (isinclpr1compl _ _)). simpl.
           apply idpath.
Defined.

Definition weqtranspos0 {T : UU} (t1 t2 : T) :
  isisolated T t1 -> isisolated T t2 -> compl T t1 ≃ compl T t2.
Proof.
  intros ? ? ? is1 is2.
  simple refine (weqgradth (funtranspos0 t1 t2 is2)
                           (funtranspos0 t2 t1 is1) _ _).
  - intro x. apply (homottranspos0t2t1t1t2 t1 t2 is1 is2).
  - intro x. apply (homottranspos0t2t1t1t2 t2 t1 is2 is1).
Defined.

(** *** Transposition of two isolated points *)


Definition funtranspos {T : UU} (t1 t2 : isolated T) : T -> T
  := recomplf (pr1 t1) (pr1 t2) (pr2 t1)
              (funtranspos0 (pr1 t1) (pr1 t2) (pr2 t2)).

Definition homottranspost2t1t1t2  {T : UU} (t1 t2 : T) (is1 : isisolated T t1)
           (is2 : isisolated T t2) :
  homot (funcomp (funtranspos (tpair _ t1 is1) (tpair _ t2 is2))
                 (funtranspos (tpair _ t2 is2) (tpair _ t1 is1))) (idfun _).
Proof.
  intros. intro t. unfold funtranspos.
  rewrite (homotrecomplfcomp t1 t2 t1 is1 is2 _ _  t).
  set (e := homotrecomplfhomot t1 t1 is1 _ (idfun _)
                               (homottranspos0t2t1t1t2 t1 t2 is1 is2) t).
  set (e' := homotrecomplfidfun t1 is1 t).
  apply (pathscomp0 e e').
Defined.


Theorem weqtranspos {T : UU} (t1 t2 : T) (is1 : isisolated T t1)
        (is2 : isisolated T t2) : T ≃ T.
Proof.
  intros.
  set (f := funtranspos (tpair _ t1 is1) (tpair _ t2 is2)).
  set (g := funtranspos (tpair _ t2 is2) (tpair _ t1 is1)).
  split with f.
  assert (egf : ∏ t : T, paths (g (f t)) t)
    by (intro; refine (homottranspost2t1t1t2 _ _ _ _ _)).
  assert (efg : ∏ t : T, paths (f (g t)) t)
    by (intro; refine (homottranspost2t1t1t2 _ _ _ _ _)).
  apply (gradth _ _ egf efg).
Defined.


Lemma pathsfuntransposoft1 {T : UU} (t1 t2 : T) (is1 : isisolated T t1)
      (is2 : isisolated T t2) :
  paths (funtranspos (tpair _ t1 is1) (tpair _ t2 is2) t1) t2.
Proof.
  intros. unfold funtranspos. rewrite (pathsrecomplfxtoy t1 t2 is1 _).
  apply idpath.
Defined.

Lemma pathsfuntransposoft2 {T : UU} (t1 t2 : T) (is1 : isisolated T t1)
      (is2 : isisolated T t2) :
  paths (funtranspos (tpair _ t1 is1) (tpair _ t2 is2) t2) t1.
Proof.
  intros. unfold funtranspos. simpl. unfold funtranspos0.
  unfold recomplf. unfold funcomp. unfold coprodf. unfold invmap.
  unfold weqrecompl. unfold recompl. simpl. unfold invrecompl.
  induction (is1 t2) as [ et1t2 | net1t2 ].
  - apply (pathsinv0 et1t2).
  - simpl. induction (is2 t2) as [ et2t2 | net2t2 ].
    + induction (is2 t1) as [ et2t1 | net2t1 ].
      * induction (net1t2 (pathscomp0 (pathsinv0 et2t1) et2t2)).
      * simpl. apply idpath.
    + induction (net2t2 (idpath _)).
Defined.

Lemma pathsfuntransposofnet1t2 {T : UU} (t1 t2 : T) (is1 : isisolated T t1)
      (is2 : isisolated T t2) (t : T) (net1t : t1 != t)
      (net2t : t2 != t) :
  paths (funtranspos (tpair _ t1 is1) (tpair _ t2 is2) t) t.
Proof.
  intros. unfold funtranspos. simpl. unfold funtranspos0. unfold recomplf.
  unfold funcomp. unfold coprodf. unfold invmap. unfold weqrecompl.
  unfold recompl. simpl. unfold invrecompl.
  induction (is1 t) as [ et1t | net1t' ].
  - induction (net1t et1t).
  - simpl. induction (is2 t) as [ et2t | net2t' ]. induction (net2t et2t).
    simpl. apply idpath.
Defined.

Lemma homotfuntranspos2 {T : UU} (t1 t2 : T) (is1 : isisolated T t1)
      (is2 : isisolated T t2) :
  homot (funcomp (funtranspos (tpair _ t1 is1) (tpair _ t2 is2))
                 (funtranspos (tpair _ t1 is1) (tpair _ t2 is2))) (idfun _).
Proof.
  intros. intro t. unfold funcomp. unfold idfun.
  induction (is1 t) as [ et1t | net1t ].
  - rewrite (pathsinv0 et1t). rewrite (pathsfuntransposoft1 _ _).
    rewrite (pathsfuntransposoft2 _ _). apply idpath.
  - induction (is2 t) as [ et2t | net2t ].
    + rewrite (pathsinv0 et2t).
      rewrite (pathsfuntransposoft2 _ _). rewrite (pathsfuntransposoft1 _ _).
      apply idpath.
    + rewrite (pathsfuntransposofnet1t2 _ _ _ _ _ net1t net2t).
      rewrite (pathsfuntransposofnet1t2 _ _ _ _ _ net1t net2t).
      apply idpath.
Defined.


(** ** Semi-boolean hfiber of functions over isolated points *)


Definition eqbx (X : UU) (x : X) (is : isisolated X x) : X -> bool.
Proof.
  intros X x is x'. induction (is x'). apply true. apply false.
Defined.

Lemma iscontrhfibereqbx (X : UU) (x : X) (is : isisolated X x) :
  iscontr (hfiber (eqbx X x is) true).
Proof.
  intros.
  assert (b : (eqbx X x is x) = true).
  {
    unfold eqbx. induction (is x) as [ e | ne ].
    - apply idpath.
    - induction (ne (idpath _)).
  }
  set (i := hfiberpair (eqbx X x is) x b). split with i.
  unfold eqbx. induction (boolchoice (eqbx X x is x)) as [ b' | nb' ].
  - intro t. induction t as [ x' e ].
    assert (e' : x' = x).
    {
      induction (is x') as [ ee | nee ]. apply (pathsinv0 ee).
      induction (nopathsfalsetotrue e) .
    }
    apply (invmaponpathsincl _ (isinclfromhfiber (eqbx X x is) isasetbool true)
                             (hfiberpair _ x' e) i e').
  - induction (nopathstruetofalse (pathscomp0 (pathsinv0 b) nb')).
Defined.

Definition bhfiber {X Y : UU} (f : X -> Y) (y : Y) (is : isisolated Y y)
  := hfiber (λ x : X, eqbx Y y is (f x)) true.

Lemma weqhfibertobhfiber {X Y : UU} (f : X -> Y) (y : Y) (is : isisolated Y y) :
  (hfiber f y) ≃ (bhfiber f y is).
Proof.
  intros. set (g := eqbx Y y is). set (ye := pr1 (iscontrhfibereqbx Y y is)).
  split with (hfibersftogf f g true ye).
  apply (isofhlevelfffromZ 0 _ _ ye (fibseqhf f g true ye)).
  apply (isapropifcontr).
  apply (iscontrhfibereqbx _ y is).
Defined.















(** *** h-fibers of [ ii1 ] and [ ii2 ] *)


Theorem isinclii1 (X Y : UU) : isincl (@ii1 X Y).
Proof.
  intros.
  set (f := @ii1 X Y). set (g := coprodtoboolsum X Y).
  set (gf := λ x : X, (g (f x))).
  set (gf' := λ x : X, tpair (boolsumfun X Y) true x).
  assert (h : ∏ x : X, paths (gf' x) (gf x))
    by (intro; apply idpath).
  assert (is1 : isofhlevelf (S O) gf')
    by apply (isofhlevelfsnfib O (boolsumfun X Y) true (isasetbool true true)).
  assert (is2 : isofhlevelf (S O) gf)
    by apply (isofhlevelfhomot (S O) gf' gf h is1).
  apply (isofhlevelff (S O) _ _ is2 (isofhlevelfweq (S (S O))
                                                    (weqcoprodtoboolsum X Y))).
Defined.


Corollary iscontrhfiberii1x (X Y : UU) (x : X) :
  iscontr (hfiber (@ii1 X Y) (ii1 x)).
Proof.
  intros.
  set (xe1 := hfiberpair (@ii1 _ _) x (idpath (@ii1 X Y x))).
  apply (iscontraprop1 (isinclii1 X Y (ii1 x)) xe1).
Defined.

Corollary neghfiberii1y (X Y : UU) (y : Y) : neg (hfiber (@ii1 X Y) (ii2 y)).
Proof.
  intros. intro xe. induction xe as [ x e ]. apply (negpathsii1ii2 _ _ e).
Defined.





Theorem isinclii2 (X Y : UU) : isincl (@ii2 X Y).
Proof.
  intros.
  set (f := @ii2 X Y). set (g := coprodtoboolsum X Y).
  set (gf := λ y : Y, (g (f y))).
  set (gf' := λ y : Y, tpair (boolsumfun X Y) false y).
  assert (h : ∏ y : Y, paths (gf' y) (gf y))
    by (intro; apply idpath).
  assert (is1 : isofhlevelf (S O) gf')
    by apply (isofhlevelfsnfib O (boolsumfun X Y) false
                               (isasetbool false false)).
  assert (is2 : isofhlevelf (S O) gf)
    by apply (isofhlevelfhomot (S O) gf' gf h is1).
  apply (isofhlevelff (S O)  _ _ is2
                      (isofhlevelfweq (S (S O)) (weqcoprodtoboolsum X Y))).
Defined.


Corollary iscontrhfiberii2y (X Y : UU) (y : Y) :
  iscontr (hfiber (@ii2 X Y) (ii2 y)).
Proof.
  intros. set (xe1 := hfiberpair (@ii2 _ _) y (idpath (@ii2 X Y y))).
  apply (iscontraprop1 (isinclii2 X Y (ii2 y)) xe1).
Defined.

Corollary neghfiberii2x (X Y : UU) (x : X) : neg (hfiber (@ii2 X Y) (ii1 x)).
Proof.
  intros. intro ye. induction ye as [ y e ]. apply (negpathsii2ii1 _ _ e).
Defined.




Lemma negintersectii1ii2 {X Y : UU} (z : coprod X Y) :
  hfiber (@ii1 X Y) z -> hfiber (@ii2 _ _) z -> empty.
Proof.
  intros X Y z X0 X1. induction X0 as [ t x ]. induction X1 as [ t0 x0 ].
  set (e := pathscomp0 x (pathsinv0 x0)).
  apply (negpathsii1ii2 _ _  e).
Defined.


(** *** [ ii1 ] and [ ii2 ] map isolated points to isolated points *)

Lemma isolatedtoisolatedii1 (X Y : UU) (x : X) (is : isisolated _ x) :
  isisolated (coprod X Y) (ii1 x).
Proof.
  intros. unfold isisolated. intro x'. induction x' as [ x0 | y ].
  - induction (is x0) as [ p | e ].
    + apply (ii1 (maponpaths (@ii1 X Y) p)).
    + apply (ii2 (negf (invmaponpathsincl (@ii1 X Y) (isinclii1 X Y) _ _) e)).
  - apply (ii2 (negpathsii1ii2 x y)).
Defined.


Lemma isolatedtoisolatedii2 (X Y : UU) (y : Y) (is : isisolated _ y) :
  isisolated (coprod X Y) (ii2 y).
Proof.
  intros. intro x'. induction x' as [ x | y0 ].
  - apply (ii2 (negpathsii2ii1 x y)).
  - induction (is y0) as [ p | e ].
    + apply (ii1 (maponpaths (@ii2 X Y) p)).
    + apply (ii2 (negf (invmaponpathsincl (@ii2 X Y) (isinclii2 X Y) _ _) e)).
Defined.























(** *** h-fibers of [ coprodf ] of two functions *)


Theorem weqhfibercoprodf1 {X Y X' Y' : UU} (f : X -> X') (g : Y -> Y')
        (x' : X') : weq (hfiber f x') (hfiber (coprodf f g) (ii1 x')).
Proof.
  intros.
  set (ix := @ii1 X Y). set (ix' := @ii1 X' Y').
  set (fpg := coprodf f g). set (fpgix := λ x : X, (fpg (ix x))).
  assert (w1 : weq (hfiber f x') (hfiber fpgix (ix' x')))
    by apply (samehfibers f ix' (isinclii1 _ _) x').
  assert (w2 : weq (hfiber fpgix (ix' x')) (hfiber fpg (ix' x'))).
  {
    split with (hfibersgftog ix fpg (ix' x')). unfold isweq. intro y.

    set (u := invezmaphf ix fpg (ix' x') y).
    assert (is : isweq u) by apply isweqinvezmaphf.

    apply (iscontrweqb (weqpair u is)).
    induction y as [ xy e ]. induction xy as [ x0 | y0 ].
    - simpl. apply iscontrhfiberofincl. apply (isinclii1 X Y).
    - apply (fromempty ((negpathsii2ii1 x' (g y0)) e)).
  }
  apply (weqcomp w1 w2).
Defined.


Theorem weqhfibercoprodf2 {X Y X' Y' : UU} (f : X -> X') (g : Y -> Y') (y' : Y') :
  weq (hfiber g y') (hfiber (coprodf f g) (ii2 y')).
Proof.
  intros.
  set (iy := @ii2 X Y). set (iy' := @ii2 X' Y').
  set (fpg := coprodf f g). set (fpgiy := λ y : Y, (fpg (iy y))).
  assert (w1 : weq (hfiber g y') (hfiber fpgiy (iy' y')))
    by apply (samehfibers g iy' (isinclii2 _ _) y').
  assert (w2 : weq (hfiber fpgiy (iy' y')) (hfiber fpg (iy' y'))).
  {
    split with (hfibersgftog iy fpg (iy' y')). unfold isweq. intro y.

    set (u:= invezmaphf iy fpg (iy' y') y).
    assert (is : isweq u) by apply isweqinvezmaphf.

    apply (iscontrweqb (weqpair u is)).
    induction y as [ xy e ]. induction xy as [ x0 | y0 ].
    simpl. apply (fromempty ((negpathsii1ii2 (f x0) y') e)). simpl.
    apply iscontrhfiberofincl. apply (isinclii2 X Y).
  }
  apply (weqcomp w1 w2).
Defined.





(** *** Theorem saying that coproduct of two functions of h-level n is of h-level n *)



Theorem isofhlevelfcoprodf (n : nat) {X Y Z T : UU} (f : X -> Z) (g : Y -> T)
        (is1 : isofhlevelf n f) (is2 : isofhlevelf n g) :
  isofhlevelf n (coprodf f g).
Proof.
  intros. unfold isofhlevelf. intro y. induction y as [ z | t ].
  apply (isofhlevelweqf n (weqhfibercoprodf1 f g z)). apply (is1 z).
  apply (isofhlevelweqf n (weqhfibercoprodf2 f g t)). apply (is2 t).
Defined.





(** *** Theorems about h-levels of coproducts and their component types *)


Theorem isofhlevelsnsummand1 (n : nat) (X Y : UU) :
  isofhlevel (S n) (coprod X Y) -> isofhlevel (S n) X.
Proof.
  intros n X Y is.
  apply (isofhlevelXfromfY (S n) (@ii1 X Y)
                           (isofhlevelfsnincl n _ (isinclii1 _ _)) is).
Defined.


Theorem isofhlevelsnsummand2 (n : nat) (X Y : UU) :
  isofhlevel (S n) (coprod X Y) -> isofhlevel (S n) Y.
Proof.
  intros n X Y is.
  apply (isofhlevelXfromfY (S n) (@ii2 X Y)
                           (isofhlevelfsnincl n _ (isinclii2 _ _)) is).
Defined.


Theorem isofhlevelssncoprod (n : nat) (X Y : UU) (isx : isofhlevel (S (S n)) X)
        (isy : isofhlevel (S (S n)) Y) : isofhlevel (S (S n)) (coprod X Y).
Proof.
  intros. apply isofhlevelfromfun.
  set (f := coprodf (λ x : X, tt) (λ y : Y, tt)).
  assert (is1 : isofhlevelf (S (S n)) f)
    by apply (isofhlevelfcoprodf (S (S n)) _ _ (isofhleveltofun _ X isx)
                                 (isofhleveltofun _ Y isy)).
  assert (is2 : isofhlevel (S (S n)) (coprod unit unit))
    by apply (isofhlevelweqb (S (S n)) boolascoprod
                             (isofhlevelssnset n _ (isasetbool))).
  apply (isofhlevelfgf (S (S n)) _ _ is1 (isofhleveltofun _ _ is2)).
Defined.


Lemma isasetcoprod (X Y : UU) (isx : isaset X) (isy : isaset Y) :
  isaset (coprod X Y).
Proof.
  intros. apply (isofhlevelssncoprod 0 _ _ isx isy).
Defined.



(** *** h-fibers of the sum of two functions [ sumofmaps f g ] *)


Lemma coprodofhfiberstohfiber {X Y Z : UU} (f : X -> Z) (g : Y -> Z) (z : Z) :
  (hfiber f z) ⨿ (hfiber g z) -> hfiber (sumofmaps f g) z.
Proof.
  intros X Y Z f g z hfg.
  induction hfg as [ hf | hg ].
  - induction hf as [ x fe ]. split with (ii1 x). simpl. assumption.
  - induction hg as [ y ge ]. split with (ii2 y). simpl. assumption.
Defined.

Lemma hfibertocoprodofhfibers {X Y Z : UU} (f : X -> Z) (g : Y -> Z) (z : Z) :
  hfiber (sumofmaps f g) z -> (hfiber f z) ⨿ (hfiber g z).
Proof.
  intros X Y Z f g z hsfg.
  induction hsfg as [ xy e ]. induction xy as [ x | y ].
  - simpl in e. apply (ii1 (hfiberpair _ x e)).
  - simpl in e. apply (ii2 (hfiberpair _ y e)).
Defined.

Theorem weqhfibersofsumofmaps {X Y Z : UU} (f : X -> Z) (g : Y -> Z) (z : Z) :
  weq ((hfiber f z) ⨿ (hfiber g z)) (hfiber (sumofmaps f g) z).
Proof.
  intros.
  set (ff := coprodofhfiberstohfiber f g z).
  set (gg := hfibertocoprodofhfibers f g z).
  split with ff.
  assert (effgg : ∏ hsfg : _, paths (ff (gg hsfg)) hsfg).
  {
    intro. induction hsfg as [ xy e ]. induction xy as [ x | y ].
    - simpl. apply idpath.
    - simpl. apply idpath.
  }
  assert (eggff : ∏ hfg : _, paths (gg (ff hfg)) hfg).
  {
    intro. induction hfg as [ hf | hg ]. induction hf as [ x fe ].
    - simpl. apply idpath.
    - induction hg as [ y ge ]. simpl. apply idpath.
  }
  apply (gradth _ _ eggff effgg).
Defined.




(** *** Theorem saying that the sum of two functions of h-level (S (S n)) is of hlevel (S (S n)) *)


Theorem isofhlevelfssnsumofmaps (n : nat) {X Y Z : UU} (f : X -> Z) (g : Y -> Z)
        (isf : isofhlevelf (S (S n)) f) (isg : isofhlevelf (S (S n)) g) :
  isofhlevelf (S (S n)) (sumofmaps f g).
Proof.
  intros. intro z.
  set (w := weqhfibersofsumofmaps f g z).
  set (is := isofhlevelssncoprod n _ _ (isf z) (isg z)).
  apply (isofhlevelweqf _ w is).
Defined.



(** *** The sum of two functions of h-level n with non-intersecting images is of h-level n *)


Lemma noil1 {X Y Z : UU} (f : X -> Z) (g : Y -> Z)
      (noi : ∏ (x : X) (y : Y), neg (paths (f x) (g y))) (z : Z) :
  hfiber f z -> hfiber g z -> empty.
Proof.
  intros X Y Z f g noi z hfz hgz.
  induction hfz as [ x fe ]. induction hgz as [ y ge ].
  apply (noi x y (pathscomp0 fe (pathsinv0 ge))).
Defined.


Lemma weqhfibernoi1 {X Y Z : UU} (f : X -> Z) (g : Y -> Z)
      (noi : ∏ (x : X) (y : Y), neg (paths (f x) (g y))) (z : Z)
      (xe : hfiber f z) : (hfiber (sumofmaps f g) z) ≃ (hfiber f z).
Proof.
  intros.
  set (w1 := invweq (weqhfibersofsumofmaps f g z)).
  assert (a : neg (hfiber g z)) by (intro ye; apply (noil1 f g noi z xe ye)).
  set (w2 := invweq (weqii1withneg (hfiber f z) a)). apply (weqcomp w1 w2).
Defined.

Lemma weqhfibernoi2 {X Y Z : UU} (f : X -> Z) (g : Y -> Z)
      (noi : ∏ (x : X) (y : Y), neg (paths (f x) (g y))) (z : Z)
      (ye : hfiber g z) : (hfiber (sumofmaps f g) z) ≃ (hfiber g z).
Proof.
  intros. set (w1 := invweq (weqhfibersofsumofmaps f g z)).
  assert (a : neg (hfiber f z)). intro xe. apply (noil1 f g noi z xe ye).
  set (w2 := invweq (weqii2withneg (hfiber g z) a)).
  apply (weqcomp w1 w2).
Defined.



Theorem isofhlevelfsumofmapsnoi (n : nat) {X Y Z : UU} (f : X -> Z) (g : Y -> Z)
        (isf : isofhlevelf n f) (isg : isofhlevelf n g)
        (noi : ∏ (x : X) (y : Y), neg (paths (f x) (g y))) :
  isofhlevelf n (sumofmaps f g).
Proof.
  intros. intro z. induction n as [ | n ].
  - set (zinx := invweq (weqpair _ isf) z).
    set (ziny := invweq (weqpair _ isg) z).
    assert (ex : (f zinx) = z) by apply (homotweqinvweq (weqpair _ isf) z).
    assert (ey : (g ziny) = z) by apply (homotweqinvweq (weqpair _ isg) z).
    induction ((noi zinx ziny) (pathscomp0 ex (pathsinv0 ey))).
  - apply isofhlevelsn. intro hfgz.
    induction ((invweq (weqhfibersofsumofmaps f g z) hfgz)) as [ xe | ye ].
    + apply (isofhlevelweqb _ (weqhfibernoi1 f g noi z xe) (isf z)).
    + apply (isofhlevelweqb _ (weqhfibernoi2 f g noi z ye) (isg z)).
Defined.







(** *** Coproducts and complements *)


Definition tocompltoii1x (X Y : UU) (x : X) :
  coprod (compl X x) Y -> compl (coprod X Y) (ii1 x).
Proof.
  intros X Y x X0. induction X0 as [ c | y ].
  - split with (ii1 (pr1 c)).
    assert (e : neg (x = (pr1 c))) by apply (pr2 c).
    apply (negf (invmaponpathsincl (@ii1 _ _) (isinclii1 X Y) _ _) e).
  - split with (ii2 y). apply (negf (pathsinv0) (negpathsii2ii1 x y)).
Defined.


Definition fromcompltoii1x (X Y : UU) (x : X) :
  compl (coprod X Y) (ii1 x) -> coprod (compl X x) Y.
Proof.
  intros X Y x X0. induction X0 as [ t x0 ]. induction t as [ x1 | y ].
  - assert (ne : x != x1) by apply (negf  (maponpaths (@ii1 _ _)) x0).
    apply (ii1 (complpair _ _ x1 ne)).
  - apply (ii2 y).
Defined.


Theorem isweqtocompltoii1x (X Y : UU) (x : X) : isweq (tocompltoii1x X Y x).
Proof.
  intros.
  set (f := tocompltoii1x X Y x). set (g := fromcompltoii1x X Y x).
  assert (egf : ∏ nexy : _, paths (g (f nexy)) nexy).
  {
    intro. induction nexy as [ c | y ].
    - induction c as [ t x0 ]. simpl.
      assert (e : paths (negf (maponpaths (@ii1 X Y))
                              (negf (invmaponpathsincl (@ii1 X Y)
                                                       (isinclii1 X Y) x t) x0))
                        x0) by apply (isapropneg (x = t)).
      apply (maponpaths (fun ee : x != t => ii1 (complpair X x t ee)) e).
    - apply idpath.
  }
  assert (efg: ∏ neii1x : _, paths (f (g neii1x)) neii1x).
  {
    intro. induction neii1x as [ t x0 ]. induction t as [ x1 | y ].
    - simpl.
      assert (e : paths (negf (invmaponpathsincl (@ii1 X Y)
                                                 (isinclii1 X Y) x x1)
                              (negf (maponpaths (@ii1 X Y)) x0)) x0)
        by apply (isapropneg (paths _ _)).
      apply (maponpaths (fun ee : (neg (paths (ii1 x) (ii1 x1)))
                         => (complpair _ _ (ii1 x1) ee)) e).
    - simpl.
      assert (e : paths (negf pathsinv0 (negpathsii2ii1 x y)) x0)
        by apply (isapropneg (paths _ _)).
      apply (maponpaths (fun ee : (neg (paths (ii1 x) (ii2 y)))
                         => (complpair _ _ (ii2 y) ee)) e).
  }
  apply (gradth f g egf efg).
Defined.


Definition tocompltoii2y (X Y : UU) (y : Y) :
  coprod X (compl Y y) -> compl (coprod X Y) (ii2 y).
Proof.
  intros X Y y X0. induction X0 as [ x | c ].
  - split with (ii1 x). apply (negpathsii2ii1 x y).
  - split with (ii2 (pr1 c)).
    assert (e : neg(y = (pr1 c))) by apply (pr2  c).
    apply (negf (invmaponpathsincl (@ii2 _ _) (isinclii2 X Y) _ _) e).
Defined.



Definition fromcompltoii2y (X Y : UU) (y : Y) :
  compl (coprod X Y) (ii2 y) ->  coprod X (compl Y y).
Proof.
  intros X Y y X0. induction X0 as [ t x ]. induction t as [ x0 | y0 ].
  - apply (ii1 x0).
  - assert (ne : y != y0) by apply (negf (maponpaths (@ii2 _ _)) x).
    apply (ii2 (complpair _ _ y0 ne)).
Defined.


Theorem isweqtocompltoii2y (X Y : UU) (y : Y) : isweq (tocompltoii2y X Y y).
Proof.
  intros.
  set (f := tocompltoii2y X Y y). set (g := fromcompltoii2y X Y y).
  assert (egf : ∏ nexy : _, paths (g (f nexy)) nexy).
  {
    intro. induction nexy as [ x | c ].
    - apply idpath.
    - induction c as [ t x ]. simpl.

      assert (e : paths (negf (maponpaths (@ii2 X Y))
                              (negf (invmaponpathsincl (@ii2 X Y)
                                                       (isinclii2 X Y) y t) x))
                        x) by apply (isapropneg (y = t)).

      apply (maponpaths (fun ee : y != t => ii2 (complpair _ y t ee)) e).
  }
  assert (efg : ∏ neii2x : _, paths (f (g neii2x)) neii2x).
  {
    intro. induction neii2x as [ t x ]. induction t as [ x0 | y0 ].
    - simpl.
      assert (e : (negpathsii2ii1 x0 y) = x)
        by apply (isapropneg (paths _ _)).
      apply (maponpaths (fun ee : (neg (paths (ii2 y) (ii1 x0)))
                         => (complpair _ _ (ii1 x0) ee)) e).
    - simpl.
      assert (e : paths (negf (invmaponpathsincl _ (isinclii2 X Y) y y0)
                              (negf (maponpaths (@ii2 X Y)) x)) x)
        by apply (isapropneg (paths _ _)).
      apply (maponpaths (fun ee : (neg (paths (ii2 y) (ii2 y0)))
                         => (complpair _ _ (ii2 y0) ee)) e).
  }
  apply (gradth f g egf efg).
Defined.







Definition tocompltodisjoint (X : UU) : X -> compl (coprod X unit) (ii2 tt)
  := λ x : _, complpair _ _ (ii1 x) (negpathsii2ii1 x tt).

Definition fromcompltodisjoint (X : UU) : compl (coprod X unit) (ii2 tt) -> X.
Proof.
  intros X X0. induction X0 as [ t x ]. induction t as [ x0 | u ].
  - assumption.
  - induction u. apply (fromempty (x (idpath (ii2 tt)))).
Defined.


Lemma isweqtocompltodisjoint (X : UU) : isweq (tocompltodisjoint X).
Proof.
  intros.
  set (ff := tocompltodisjoint X). set (gg := fromcompltodisjoint X).
  assert (egf : ∏ x : X, paths (gg (ff x)) x) by (intro; apply idpath).
  assert (efg : ∏ xx : _, paths (ff (gg xx)) xx).
  {
    intro. induction xx as [ t x ]. induction t as [ x0 | u ].
    - simpl. unfold ff. unfold tocompltodisjoint. simpl.
      assert (ee : (negpathsii2ii1 x0 tt) = x)
        by apply (proofirrelevance _ (isapropneg _)).
      induction ee. apply idpath.
    - induction u. simpl. apply (fromempty (x (idpath _))).
  }
  apply (gradth ff gg egf efg).
Defined.


Definition weqtocompltodisjoint (X : UU) : X ≃ compl (X ⨿ unit) (ii2 tt)
  := weqpair _ (isweqtocompltodisjoint X).

Corollary isweqfromcompltodisjoint (X : UU) : isweq (fromcompltodisjoint X).
Proof.
  intros. apply (isweqinvmap (weqtocompltodisjoint X)).
Defined.

(** ** Decidable propositions and decidable inclusions *)

(** *** Decidable propositions [ isdecprop ] *)

Lemma isdecpropif' (X : UU) : isaprop X -> X ⨿ ¬ X -> iscontr (X ⨿ ¬ X).
(* This contractibility was the old definition of isdecpropif.  We can probably
  do without it. *)
Proof.
  intros X is a.
  assert (is1 : isaprop (coprod X (neg X))) by (apply isapropdec; assumption).
  apply (iscontraprop1 is1 a).
Defined.

Lemma isdecproppaths {X : UU} (is : isdeceq X) (x x' : X) :
  isdecprop (x = x').
Proof.
  intros. apply (isdecpropif _ (isasetifdeceq _ is x x') (is x x')).
Defined.

Lemma isdeceqif {X : UU} (is : ∏ x x' : X, isdecprop (x = x')) : isdeceq X.
Proof.
  intros. intros x x'. apply (pr1 (is x x')).
Defined.

Lemma isaninv1 (X : UU) : isdecprop X -> isaninvprop X.
Proof.
  intros X is1. unfold isaninvprop.
  assert (is2 := pr1 is1); simpl in is2.
  assert (adjevinv: dneg X -> X).
  {intro X0. induction is2 as [ a | b ].
   - assumption.
   - contradicts X0 b. }
  assert (is3: isaprop (dneg X)).
  {apply (isapropneg (X -> empty)). }
  apply (isweqimplimpl (todneg X) adjevinv is1 is3).
Defined.

Theorem isdecpropfibseq1 {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
        (fs : fibseqstr f g z) : isdecprop X -> isaprop Z -> isdecprop Y.
Proof.
  intros X Y Z f g z fs isx isz.
  assert (isc : iscontr Z) by apply (iscontraprop1 isz z).
  assert (X0 : isweq f) by apply (isweqfinfibseq f g z fs isc).
  apply (isdecpropweqf (weqpair _ X0) isx).
Defined.

Theorem isdecpropfibseq0 {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (z : Z)
        (fs : fibseqstr f g z) : isdecprop Y -> isdeceq Z -> isdecprop X.
Proof.
  intros X Y Z f g z fs isy isz.
  assert (isg : isofhlevelf 1 g)
    by apply (isofhlevelffromXY 1 g (isdecproptoisaprop _ isy)
                                (isasetifdeceq _ isz)).
  assert (isp : isaprop X) by apply (isofhlevelXfromg 1 f g z fs isg).
  induction (pr1 isy) as [ y | ny ].
  - apply (isdecpropfibseq1 _ _ y (fibseq1 f g z fs y)
                            (isdecproppaths isz (g y) z)
                            (isdecproptoisaprop _ isy)).
  - apply (isdecpropif _ isp (ii2 (negf f ny))).
Defined.

Theorem isdecpropdirprod {X Y : UU} (isx : isdecprop X) (isy : isdecprop Y) :
  isdecprop (X × Y).
Proof.
  intros.
  assert (isp : isaprop (X × Y))
    by apply (isofhleveldirprod 1 _ _ (isdecproptoisaprop _ isx)
                                (isdecproptoisaprop _ isy)).
  induction (pr1 isx) as [ x | nx ].
  - induction (pr1 isy) as [ y | ny ].
    + apply (isdecpropif _ isp (ii1 (dirprodpair x y))).
    + assert (nxy : neg (X × Y)).
      {
        intro xy. induction xy as [ x0  y0 ]. apply (ny y0).
      }
      apply (isdecpropif _ isp (ii2 nxy)).
  - assert (nxy : neg (X × Y)).
    {
      intro xy. induction xy as [ x0  y0 ]. apply (nx x0).
    }
    apply (isdecpropif _ isp (ii2 nxy)).
Defined.

Lemma fromneganddecx {X Y : UU} : isdecprop X -> ¬ (X × Y) -> ¬X ⨿ ¬Y.
Proof.
  intros ? ? isx nf.
  induction (pr1 isx) as [ x | nx ].
  - assert (ny := negf (λ y : Y, dirprodpair x y) nf).
    exact (ii2 ny).
  - exact (ii1 nx).
Defined.

Lemma fromneganddecy {X Y : UU} : isdecprop Y -> ¬ (X × Y) -> ¬X ⨿ ¬Y.
Proof.
  intros ? ? isy nf. induction (pr1 isy) as [ y | ny ].
  - assert (nx := negf (λ x : X, dirprodpair x y) nf).
    exact (ii1 nx).
  - exact (ii2 ny).
Defined.


(** *** Paths to and from an isolated point form a decidable proposition *)

Lemma isdecproppathsfromisolated (X : UU) (x : X) (is : isisolated X x)
      (x' : X) : isdecprop (x = x').
Proof.
  intros. apply isdecpropif.
  - apply isaproppathsfromisolated. assumption.
  - apply (is x').
Defined.

Lemma isdecproppathstoisolated  (X : UU) (x : X) (is : isisolated X x)
      (x' : X) : isdecprop (x' = x).
Proof.
  intros.
  apply (isdecpropweqf (weqpathsinv0 x x')
                       (isdecproppathsfromisolated X x is x')).
Defined.


(** *** Decidable inclusions *)



Definition isdecincl {X Y : UU} (f : X -> Y) := ∏ y : Y, isdecprop (hfiber f y).
Lemma isdecincltoisincl {X Y : UU} (f : X -> Y) : isdecincl f -> isincl f.
Proof.
  intros X Y f is. intro y. apply (isdecproptoisaprop _ (is y)).
Defined.
Coercion isdecincltoisincl : isdecincl >-> isincl.

Lemma isdecinclfromisweq {X Y : UU} (f : X -> Y) : isweq f -> isdecincl f.
Proof.
  intros X Y f iswf. intro y. apply (isdecpropfromiscontr (iswf y)).
Defined.

Lemma isdecpropfromdecincl {X Y : UU} (f : X -> Y) :
  isdecincl f -> isdecprop Y -> isdecprop X.
Proof.
  intros X Y f isf isy.
  induction (pr1 isy) as [ y | n ].
  - assert (w : weq (hfiber f y) X)
      by apply (weqhfibertocontr
                  f y (iscontraprop1 (isdecproptoisaprop _ isy) y)).
    apply (isdecpropweqf w (isf y)).
  - apply isdecpropif. apply (isapropinclb _ isf isy). apply (ii2 (negf f n)).
Defined.


Lemma isdecinclii1 (X Y : UU) : isdecincl (@ii1 X Y).
Proof.
  intros. intro y. induction y as [ x | y ].
  - apply (isdecpropif _ (isinclii1 X Y (ii1 x))
                       (ii1 (hfiberpair (@ii1 _ _) x (idpath _)))).
  - apply (isdecpropif _ (isinclii1 X Y (ii2 y))
                       (ii2 (neghfiberii1y X Y y))).
Defined.


Lemma isdecinclii2 (X Y : UU) : isdecincl (@ii2 X Y).
Proof.
  intros. intro y. induction y as [ x | y ].
  - apply (isdecpropif _ (isinclii2 X Y (ii1 x)) (ii2 (neghfiberii2x X Y x))).
  - apply (isdecpropif _ (isinclii2 X Y (ii2 y))
                       (ii1 (hfiberpair (@ii2 _ _) y (idpath _)))).
Defined.


Lemma isdecinclpr1 {X : UU} (P : X -> UU) (is : ∏ x : X, isdecprop (P x)) :
  isdecincl (@pr1 _ P).
Proof.
  intros. intro x.
  assert (w : weq (P x) (hfiber (@pr1 _ P) x)) by apply ezweqpr1.
  apply (isdecpropweqf w (is x)).
Defined.


Theorem isdecinclhomot {X Y : UU} (f g : X -> Y)
        (h : ∏ x : X, paths (f x) (g x)) (is : isdecincl f) : isdecincl g.
Proof.
  intros. intro y.
  apply (isdecpropweqf (weqhfibershomot f g h y) (is y)).
Defined.


Theorem isdecinclcomp {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
        (isf : isdecincl f) (isg : isdecincl g) : isdecincl (λ x : X, g (f x)).
Proof.
  intros. intro z.
  set (gf := λ x : X, g (f x)).
  assert (wy : ∏ ye : hfiber g z, weq (hfiber f (pr1 ye))
                                      (hfiber (hfibersgftog f g z) ye))
    by apply ezweqhf.
  assert (ww : ∏ y : Y, weq (hfiber f y) (hfiber gf (g y))).
  {
    intro. apply (samehfibers f g). apply (isdecincltoisincl _ isg).
  }
  induction (pr1 (isg z)) as [ ye | nye ].
  - induction ye as [ y e ]. induction e. apply (isdecpropweqf (ww y) (isf y)).
  - assert (wz : (hfiber gf z) ≃ (hfiber g z)).
    {
      split with (hfibersgftog f g z). intro ye. induction (nye ye).
    }
    apply (isdecpropweqb wz (isg z)).
Defined.

(** The conditions of the following theorem can be weakened by assuming only
  that the h-fibers of g satisfy [ isdeceq ] i.e. are "sets with decidable
  equality". *)

Theorem isdecinclf {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (isg : isincl g)
        (isgf : isdecincl (λ x : X, g (f x))) : isdecincl f.
Proof.
  intros. intro y. set (gf := λ x : _, g (f x)).
  assert (ww : weq (hfiber f y) (hfiber gf (g y)))
    by (apply (samehfibers f g); assumption).
  apply (isdecpropweqb ww (isgf (g y))).
Defined.

(** *)


Theorem isdecinclg {X Y Z : UU} (f : X -> Y) (g : Y -> Z) (isf : isweq f)
        (isgf : isdecincl (λ x : X, g (f x))) : isdecincl g.
Proof.
  intros. intro z.
  set (gf := λ x : X, g (f x)).
  assert (w : (hfiber gf z) ≃ (hfiber g z)).
  {
    split with (hfibersgftog f g z). intro ye.
    assert (ww : weq (hfiber f (pr1 ye)) (hfiber (hfibersgftog f g z) ye))
      by apply ezweqhf.
    apply (iscontrweqf ww (isf (pr1 ye))).
  }
  apply (isdecpropweqf w (isgf z)).
Defined.



(** *** Decidable inclusions and isolated points *)

Theorem isisolateddecinclf {X Y : UU} (f : X -> Y) (x : X) :
  isdecincl f -> isisolated X x -> isisolated Y (f x).
Proof.
  intros X Y f x isf isx.
  assert (is' : ∏ y : Y, isdecincl (d1g f y x)).
  {
    intro y. intro xe. set (w := ezweq2g f x xe).
    apply (isdecpropweqf w (isdecproppathstoisolated X x isx _)).
  }
  assert (is'' : ∏ y : Y, isdecprop ((f x) = y))
    by (intro; apply (isdecpropfromdecincl _ (is' y) (isf y))).
  intro y'.
  apply (pr1 (is'' y')).
Defined.



(** *** Decidable inclusions and coprojections *)


Definition negimage {X Y : UU} (f : X -> Y) : UU
  := total2 (λ y : Y, neg (hfiber f y)).
Definition negimagepair {X Y : UU} (f : X -> Y) :
  ∏ t : Y, ¬ hfiber f t → ∑ y : Y, ¬ hfiber f y
  := tpair (λ y : Y, neg (hfiber f y)).

Lemma isinclfromcoprodwithnegimage {X Y : UU} (f : X -> Y) (is : isincl f) :
  isincl (sumofmaps f (@pr1 _ (λ y : Y, neg (hfiber f y)))).
Proof.
  intros.
  assert (noi : ∏ (x : X) (nx : negimage f), neg (paths (f x) (pr1 nx))).
  {
    intros x nx e. induction nx as [ y nhf ]. simpl in e.
    apply (nhf (hfiberpair _ x e)).
  }
  assert (is' : isincl (@pr1 _ (λ y : Y, neg (hfiber f y)))).
  {
    apply isinclpr1. intro y. apply isapropneg.
  }
  apply (isofhlevelfsumofmapsnoi 1 f _ is is' noi).
Defined.


Definition iscoproj {X Y : UU} (f : X -> Y) : UU
  := isweq (sumofmaps f (@pr1 _ (λ y : Y, neg (hfiber f y)))).

Definition weqcoproj {X Y : UU} (f : X -> Y) (is : iscoproj f) :
  weq (coprod X (negimage f)) Y := weqpair _ is.

Theorem iscoprojfromisdecincl {X Y : UU} (f : X -> Y) (is : isdecincl f) :
  iscoproj f.
Proof.
  intros.
  set (p := sumofmaps f (@pr1 _ (λ y : Y, neg (hfiber f y)))).
  assert (is' : isincl p).
  {
    apply isinclfromcoprodwithnegimage. apply (isdecincltoisincl _ is).
  }
  unfold iscoproj. intro y. induction (pr1 (is y)) as [ h | nh ].
  - induction h as [ x e ]. induction e. change (f x) with (p (ii1 x)).
    apply iscontrhfiberofincl. assumption.
  - change y with (p (ii2 (negimagepair _ y nh))). apply iscontrhfiberofincl.
    assumption.
Defined.

Theorem isdecinclfromiscoproj {X Y : UU} (f : X -> Y) (is : iscoproj f) :
  isdecincl f.
Proof.
  intros.
  set (g := (sumofmaps f (@pr1 _ (λ y : Y, neg (hfiber f y))))).
  set (f' :=  λ x : X, g (ii1 x)).
  assert (is' : isdecincl f')
    by apply (isdecinclcomp _ _ (isdecinclii1 _ _) (isdecinclfromisweq _ is)).
  assumption.
Defined.

(* End of the file uu0c.v *)
