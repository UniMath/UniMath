(** * Terms for a given signature. *)
(**
This file contains a formalization of terms over a signature, implemented as a sequence of
operation symbols. This sequence is though to be executed by a stack machine: each
symbol of arity _n_ virtually pops _n_ elements from the stack and pushes a new element.
A sequence of function symbols is a term when the result of the execution is a stack
with a single element and no stack underflow or type errors occur.

Here we only define ground terms, while terms with variables will be defined in <<VTerms.v>>.
*)

Require Import UniMath.MoreFoundations.Notations.

Require Import UniMath.Algebra.Universal.Maybe.
Require Import UniMath.Algebra.Universal.SortedTypes.
Require Export UniMath.Algebra.Universal.Signatures.

Local Open Scope sorted.
Local Open Scope hvec.
Local Open Scope list.

(** ** Definition of [oplist] (operations list). *)
(**
An [oplist] is a list of operation symbols, interpreted as commands to be executed by a stack
machine. Elements of the stack are sorts. When an operation symbol is executed  its arity is
popped out from the stack and replaced by its range. When a stack underflow occurs,
or when the sorts present in the stack are not the ones expected by the operator, the stack goes into an
error condition which is propagated by successive operations. A term is an [oplist] that produces
a stack of length one, when execution starts from the empty stack. Operation symbols are executed in
order from the last element of the [oplist] to the first.
*)

Local Definition oplist (σ: signature):= list (names σ).

Bind Scope list_scope with oplist.

Identity Coercion oplistislist: oplist >-> list.

Local Corollary isasetoplist (σ: signature): isaset (oplist σ).
Proof.
  apply isofhlevellist.
  apply setproperty.
Defined.

Local Definition stack (σ: signature): UU := maybe (list (sorts σ)).

Local Lemma isasetstack (σ: signature): isaset (stack σ).
Proof.
  apply isasetmaybe.
  apply isofhlevellist.
  apply isasetifdeceq.
  apply decproperty.
Defined.

Section Oplists.

  Context {σ: signature}.

  (** *** The [opexec] and [oplistexec] functions. *)
  (**
     The function [opexec nm] is the stack transformation corresponding to the execution of
     the operation symbol [nm], while [oplistexec l] returns the stack corresponding to the
     execution of the entire oplist [l] starting from the empty stack. The list is executed from the last
     to the first operation symbol. Finally [isaterm l] holds when the result of [oplistexec l]
     is a stack of length one.
   *)

  Local Definition opexec (nm: names σ): stack σ → stack σ
    := flatmap (λ ss, just (sort nm :: ss)) ∘ flatmap (λ ss, prefix_remove (arity nm) ss).

  Local Definition oplistexec (l: oplist σ): stack σ := foldr opexec (just []) l.

  Local Definition isaterm (s: sorts σ) (l: oplist σ): UU := oplistexec l = just ([s]).

  Local Lemma isapropisaterm (s: sorts σ) (l: oplist σ): isaprop (isaterm s l).
  Proof.
    apply isasetstack.
  Defined.

  Local Lemma opexec_dec (nm: names σ) (ss: list (sorts σ))
    : ((opexec nm (just ss) = nothing) × (prefix_remove (arity nm) ss = nothing))
              ⨿  ∑ (ss': list (sorts σ)), (opexec nm (just ss) = just ((sort nm) :: ss')) × (prefix_remove (arity nm) ss = just ss').
  Proof.
    unfold opexec, funcomp, just.
    simpl.
    induction (prefix_remove (arity nm) ss) as [ ss' | error ].
    - apply ii2.
      exists ss'.
      split; apply idpath.
    - apply ii1.
      split.
      + apply idpath.
      + induction error.
        apply idpath.
  Defined.

  Local Lemma opexec_just_f (nm: names σ) (ss: list (sorts σ)) (arityok: isprefix (arity nm) ss)
    : ∑ ss': list (sorts σ), opexec nm (just ss) = just ((sort nm) :: ss') ×  prefix_remove (arity nm) ss = just ss'.
  Proof.
    induction (opexec_dec nm ss) as [err | ok].
    - induction err as [_  err].
      contradicts arityok err.
    - assumption.
  Defined.

  Local Lemma opexec_just_b (nm: names σ) (st: stack σ) (ss: list (sorts σ))
    : opexec nm st = just ss → ∑ ss', ss = sort nm :: ss' × st = just ((arity nm) ++ ss').
  Proof.
    intro scons.
    induction st as [stok | sterror].
    - induction (opexec_dec nm stok) as [scons_err | scons_ok].
      + induction scons_err as [scons_err _].
        set (H := ! scons @ scons_err).
        contradiction (negpathsii1ii2 _ _ H).
      + induction scons_ok as [ss' [X1 X2]].
        exists ss'.
        split.
        * apply just_injectivity.
          exact (!scons @ X1).
        * apply maponpaths.
          apply prefix_remove_back.
          assumption.
   -  contradiction (negpathsii2ii1 _ _ scons).
  Defined.

  Local Lemma opexec_zero_b (nm: names σ) (st: stack σ)
    : ¬ (opexec nm st = just nil).
  Proof.
    induction st as [stok | sterror].
    - induction (opexec_dec nm stok) as [scons_err| scons_ok].
      + induction scons_err as [scons_err _].
        intro H.
        set (H' :=  (!! scons_err @ H)).
        apply negpathsii1ii2 in H'.
        assumption.
      + induction scons_ok as [p [proofp _]].
        intro H.
        set (H' :=  (!proofp @ H)).
        apply ii1_injectivity in H'.
        apply negpathsconsnil in H'.
        assumption.
    - apply negpathsii2ii1.
  Defined.

  Local Lemma oplistexec_nil
    : oplistexec (nil: oplist σ) = just nil.
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistexec_cons (nm: names σ) (l: oplist σ)
    : oplistexec (nm :: l) = opexec nm (oplistexec l).
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistexec_zero_b (l: oplist σ): oplistexec l = just nil → l = nil.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - reflexivity.
    - intros x xs _ lstack.
      apply opexec_zero_b in lstack.
      contradiction.
  Defined.

  Local Lemma oplistexec_positive_b (l: oplist σ) (s: sorts σ) (ss: list (sorts σ))
    : oplistexec l = just (s :: ss) → ∑ (x: names σ) (xs: oplist σ), l = x :: xs.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - intro nilstack.
      cbn in nilstack.
      apply ii1_injectivity in nilstack.
      apply negpathsnilcons in nilstack.
      contradiction.
    - intros x xs _ lstack.
      exists x.
      exists xs.
      apply idpath.
  Defined.

  (** *** The [stackconcatenate] function. *)

  (**
  [stackconcatenate] simply appends the two lists which make the stacks, possibly propagating
  erroneous states.
  *)

  Local Definition stackconcatenate (st1 st2: stack σ): stack σ
    := flatmap (λ st2', flatmap (λ st1', just (st1' ++ st2')) st1) st2.

  Local Lemma stackconcatenate_opexec (nm: names σ) (st1 st2: stack σ)
    : opexec nm st1 != nothing
       → stackconcatenate (opexec nm st1) st2 = opexec nm (stackconcatenate st1 st2).
  Proof.
    induction st1 as [ss1 | ].
    2: contradiction.
    induction st2 as [ss2| ].
    2: reflexivity.
    intro H.
    induction (opexec_dec nm ss1) as [Xerr | Xok].
    - contradicts H (pr1 Xerr).
    - induction Xok as [tl [scons pref]].
      unfold just in scons.
      rewrite scons.
      simpl.
      rewrite concatenateStep.
      unfold opexec, funcomp.
      simpl.
      erewrite prefix_remove_concatenate.
      * apply idpath.
      * assumption.
  Defined.

 Local Lemma oplistexec_concatenate (l1 l2: oplist σ)
    : oplistexec l1 != nothing
      → oplistexec (concatenate l1 l2)
        = stackconcatenate (oplistexec l1) (oplistexec l2).
  Proof.
    revert l1.
    refine (list_ind _ _ _).
    - intros.
      change ([] ++ l2) with (l2).
      induction (oplistexec l2) as [l2ok | l2error].
      + apply idpath.
      + induction l2error.
        apply idpath.
    - intros x xs IHxs noerror.
      change (oplistexec (x :: xs)) with (opexec x (oplistexec xs))  in *.
      rewrite stackconcatenate_opexec by (assumption).
      rewrite <- IHxs.
      + apply idpath.
      + intro error.
        rewrite error in noerror.
        contradiction.
  Defined.

  (** *** The [oplistsplit] function. *)

  (**
     [oplistsplit] splits an oplist into an oplist of up to [n] terms and an oplist of the remaining
     terms.
   *)

  Local Definition oplistsplit (l: oplist σ) (n: nat): oplist σ × oplist σ.
  Proof.
    revert l n.
    refine (list_ind _ _ _).
    - intros.
      exact (nil ,, nil).
    - intros x xs IHxs n.
      induction n.
      + exact (nil,, (x :: xs)).
      + induction (IHxs (length (arity x) + n)) as [IHfirst IHsecond].
        exact ((x :: IHfirst) ,, IHsecond).
  Defined.

  Local Lemma oplistsplit_zero (l: oplist σ): oplistsplit l 0 = nil,, l.
  Proof.
    revert l.
    refine (list_ind _ _ _) ; reflexivity.
  Defined.

  Local Lemma oplistsplit_nil (n: nat): oplistsplit nil n = nil,, nil.
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistsplit_cons (x: names σ) (xs: oplist σ) (n: nat)
    : oplistsplit (x :: xs) (S n)
      = (x :: (pr1 (oplistsplit xs (length (arity x) + n)))) ,, (pr2 (oplistsplit xs (length (arity x) + n))).
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistsplit_concatenate (l1 l2: oplist σ) (n: nat) (ss: list (sorts σ))
    : oplistexec l1 = just ss → n ≤ length ss
      → oplistsplit (l1 ++ l2) n
        = make_dirprod (pr1 (oplistsplit l1 n)) (pr2 (oplistsplit l1 n) ++ l2).
  Proof.
    revert l1 ss n.
    refine (list_ind _ _ _).
    - intros ss n l1stack nlehss.
      apply ii1_injectivity in l1stack.
      rewrite <- l1stack in nlehss.
      apply natleh0tois0 in nlehss.
      rewrite nlehss.
      rewrite oplistsplit_zero.
      apply idpath.
    - intros x1 xs1 IHxs1 ss n l1stack nlehss.
      change ((x1 :: xs1) ++ l2) with (x1 :: (xs1 ++ l2)).
      induction n.
      + apply idpath.
      + change (oplistexec (x1 :: xs1)) with (opexec x1 (oplistexec xs1)) in l1stack.
        apply opexec_just_b in l1stack.
        induction l1stack as [sstail [ssdef xs1stack]].
        eset (IHinst := IHxs1 (arity x1 ++ sstail) (length (arity x1) + n) xs1stack _).
        do 2 rewrite oplistsplit_cons.
        apply pathsdirprod.
        * cbn.
          apply maponpaths.
          apply (maponpaths pr1) in IHinst.
          cbn in IHinst.
          assumption.
        * apply (maponpaths dirprod_pr2) in IHinst.
          assumption.
     Unshelve.
     rewrite length_concatenate.
     apply natlehandplusl.
     rewrite ssdef in nlehss.
     assumption.
  Defined.

  Local Lemma concatenate_oplistsplit (l: oplist σ) (n: nat): pr1 (oplistsplit l n) ++ pr2 (oplistsplit l n) = l.
  Proof.
    revert l n.
    refine (list_ind _ _ _).
    - reflexivity.
    - intros x xs IHxs n.
      induction n.
      + apply idpath.
      + rewrite oplistsplit_cons.
        simpl.
        rewrite concatenateStep.
        apply maponpaths.
        apply IHxs.
  Defined.

  Local Lemma oplistexec_oplistsplit (l: oplist σ) {ss: list (sorts σ)} (n: nat)
    : oplistexec l = just ss → n ≤ length ss
      → ∑ t1 t2: list (sorts σ),
          ss = t1 ++ t2
          × oplistexec (pr1 (oplistsplit l n)) = just t1
          × oplistexec (pr2 (oplistsplit l n)) = just t2
          × length t1 = n.
  Proof.
    revert l ss n.
    refine (list_ind _ _ _).
    - intros m ss nilstack nlehss.
      cbn.
      apply ii1_injectivity in nilstack.
      rewrite <- nilstack in *.
      apply natleh0tois0 in nlehss.
      rewrite nlehss.
      exists nil.
      exists nil.
      repeat split.
    - intros x xs IHxs ss n lstack nlehss.
      induction n.
      + rewrite oplistsplit_zero.
        exists nil.
        exists ss.
        repeat split.
        assumption.
      + rewrite oplistsplit_cons.
        simpl.
        change (oplistexec (x :: xs)) with (opexec x (oplistexec xs)) in lstack.
        apply opexec_just_b in lstack.
        induction lstack as [sstail [ssdef xsstack]].
        eset (IHinst := IHxs (arity x ++ sstail) (length (arity x) + n) xsstack _).
        induction IHinst as  [t1 [ t2 [ t1t2concat [ t1def [ t2def t1len ] ] ] ] ].
        exists ((sort x) :: MoreLists.drop t1 (length (arity x))).
        exists t2.
        repeat split.
        * rewrite concatenateStep.
          rewrite <- drop_concatenate.
          -- rewrite <- t1t2concat.
             rewrite drop_concatenate.
             2: apply isreflnatleh.
             rewrite drop_full.
             assumption.
          -- rewrite t1len.
             apply natlehnplusnm.
        * rewrite oplistexec_cons.
          rewrite t1def.
          unfold opexec, funcomp.
          simpl.
          rewrite prefix_remove_drop.
          -- simpl.
             apply maponpaths.
             apply idpath.
          -- intro H.
             apply (prefix_remove_concatenate2 _ _ t2) in H.
             ++ rewrite <- t1t2concat in H.
                rewrite prefix_remove_prefix in H.
                exact (negpathsii1ii2 _ _ H).
             ++ rewrite t1len.
                apply natlehnplusnm.
        * apply t2def.
        * rewrite length_cons.
          apply maponpaths.
          rewrite length_drop.
          rewrite t1len.
          rewrite natpluscomm.
          apply plusminusnmm.
   Unshelve.
   rewrite length_concatenate.
   apply natlehandplusl.
   rewrite ssdef in nlehss.
   assumption.
  Defined.

  Local Corollary oplistsplit_self {l: oplist σ} {ss: list (sorts σ)}
    : oplistexec l = just ss → oplistsplit l (length ss) = l ,, nil.
  Proof.
    intro lstack.
    set (H := oplistexec_oplistsplit l (length ss) lstack (isreflnatleh (length ss))).
    induction H as [t1 [t2 [t1t2 [t1def [t2def t1len]]]]].
    set (normalization := concatenate_oplistsplit l (length ss)).
    apply (maponpaths length) in t1t2.
    rewrite length_concatenate in t1t2.
    rewrite t1len in t1t2.
    apply pathsinv0 in t1t2.
    rewrite natpluscomm in t1t2.
    apply (maponpaths (λ a, a - length ss)) in t1t2.
    rewrite plusminusnmm in t1t2.
    rewrite minuseq0' in t1t2.
    apply length_zero_back in t1t2.
    rewrite t1t2 in t2def.
    apply oplistexec_zero_b in t2def.
    rewrite t2def in normalization.
    rewrite concatenate_nil in normalization.
    induction (oplistsplit l (length ss)) as [l1 l2].
    simpl in *.
    rewrite t2def.
    rewrite normalization.
    apply idpath.
  Defined.

End Oplists.

Section Term.

  (** ** Terms and related constructors and destructors. *)

  (**  A [term] is an oplist together with the proof it is a term. *)

  Local Definition term (σ: signature) (s: sorts σ): UU
    := ∑ t: oplist σ, isaterm s t.

  Definition make_term {σ: signature} {s: sorts σ} {l: oplist σ} (lstack: isaterm s l)
    : term σ s := l ,, lstack.

  Coercion term2oplist {σ: signature} {s: sorts σ}: term σ s → oplist σ := pr1.

  Definition term2proof {σ: signature} {s: sorts σ}: ∏ t: term σ s, isaterm s t := pr2.

  Lemma isasetterm {σ: signature} (s: sorts σ): isaset (term σ s).
  Proof.
    apply isaset_total2.
    - apply isasetoplist.
    - intros.
      apply isasetaprop.
      apply isasetstack.
  Defined.

  Local Definition termset (σ: signature) (s: sorts σ): hSet
    := make_hSet (term σ s) (isasetterm s).

  Context {σ: signature}.

  Lemma term_extens {s: sorts σ} {t1 t2 : term σ s} (p : term2oplist t1 = term2oplist t2)
    : t1 = t2.
  Proof.
    apply subtypePairEquality'.
    2: apply isapropisaterm.
    assumption.
  Defined.

  (** *** The [vecoplist2oplist] and [oplist2vecoplist] functions *)
  (**
  These functions transform a vector of [n] oplists into an oplists of stack [n]
  ([vecoplist2oplist]) and viceversa ([oplist2vecoplist]).
  *)

  Local Definition vecoplist2oplist {n: nat} (v: Vector (oplist σ) n): oplist σ
    := vector_foldr concatenate nil v.

  Local Lemma vecoplist2oplist_vcons {n: nat} (x: oplist σ) (v: Vector (oplist σ) n)
    : vecoplist2oplist (x ::: v) = concatenate x (vecoplist2oplist v).
  Proof.
    apply idpath.
  Defined.

  Local Lemma vecoplist2oplist_inj {n: nat} {ar: Vector (sorts σ) n} {v1 v2: HVec (vector_map (term σ) ar)}
    : vecoplist2oplist (h1map_vector (λ _, term2oplist) v1) = vecoplist2oplist (h1map_vector (λ _, term2oplist) v2)
      → v1 = v2.
  Proof.
    revert n ar v1 v2.
    refine (vector_ind _ _ _).
    - intros.
      induction v1.
      induction v2.
      apply idpath.
    - intros x n xs IHxs v1 v2 eq.
      induction v1 as [v1x v1xs].
      induction v2 as [v2x v2xs].
      simpl in eq.
      apply (maponpaths (λ l, oplistsplit l 1)) in eq.
      rewrite (oplistsplit_concatenate _ _ 1 [x] (term2proof v1x) (isreflnatleh _)) in eq.
      rewrite (oplistsplit_concatenate _ _ 1 [x] (term2proof v2x) (isreflnatleh _)) in eq.
      do 2 change 1 with (length (hd (x ::: xs) :: [])) in eq at 1.
      do 2 change 1 with (length (hd (x ::: xs) :: [])) in eq at 1.
      rewrite (oplistsplit_self (term2proof v1x)) in eq.
      rewrite (oplistsplit_self (term2proof v2x)) in eq.
      cbn in eq.
      simpl.
      apply map_on_two_paths.
      + apply subtypePairEquality'.
        * apply (maponpaths pr1 eq).
        * apply isapropisaterm.
      + apply IHxs.
        apply (maponpaths (λ l, pr2 l: oplist σ) eq).
  Defined.

  Local Lemma oplistexec_vecoplist2oplist {n: nat} {ar: Vector (sorts σ) n} {v: HVec (vector_map (term σ) ar)}
    : oplistexec (vecoplist2oplist (h1map_vector (λ _, term2oplist) v)) = just (n ,, ar).
  Proof.
    revert n ar v.
    refine (vector_ind _ _ _).
    - induction v.
      reflexivity.
    - intros x n xs IHxs v.
      induction v as [vx vxs].
      simpl in *.
      rewrite oplistexec_concatenate.
      unfold h1map_vector in IHxs.
      + rewrite IHxs.
        rewrite (term2proof vx).
        apply idpath.
      + rewrite (term2proof vx).
        apply negpathsii1ii2.
  Defined.

  Local Definition oplist2vecoplist {n: nat} {ar: Vector (sorts σ) n} (l: oplist σ) (lstack: oplistexec l = just (n,, ar))
    : ∑ (v: HVec (vector_map (term σ) ar))
        , (HVec (h1map_vector (λ _ t, hProptoType (length (term2oplist t) ≤ length l)) v))
          × vecoplist2oplist (h1map_vector (λ _, term2oplist) v) = l.
  Proof.
    revert n ar l lstack.
    refine (vector_ind _ _ _).
    - intros.
      exists [()].
      exists [()].
      apply oplistexec_zero_b in lstack.
      rewrite lstack.
      apply idpath.
    - intros x n xs IHxs l lstack.
      induction (oplistexec_oplistsplit l 1 lstack (natleh0n 0))
         as [firststack [reststack [concstack [firststackp [reststackp firstlen]]]]].
      change (S n,, (x ::: xs)%vector) with (x :: (n ,, xs)) in concstack.
      set (first := pr1 (oplistsplit l 1)) in *.
      set (rest := pr2 (oplistsplit l 1)) in *.
      apply length_one_back in firstlen.
      induction firstlen as [a firststack'].
      induction (!firststack').
      change ((a :: []) ++ reststack) with (a :: reststack) in concstack.
      pose (concstack' := concstack).
      apply cons_inj1 in concstack'.
      apply cons_inj2 in concstack.
      induction (!concstack).
      induction (!concstack').
      induction (IHxs rest reststackp) as [v [vlen vflatten]].
      exists ((make_term firststackp) ::: v).
      repeat split.
      + change (length first ≤ length l).
        rewrite <- (concatenate_oplistsplit l 1).
        apply length_sublist1.
      + change (HVec (h1map_vector (λ (s: sorts σ) (t: term σ s), hProptoType (length (term2oplist t) ≤ length l)) v)).
        eapply (h2map (λ _ _ p, istransnatleh p _) vlen).
        Unshelve.
        rewrite <- (concatenate_oplistsplit l 1).
        apply length_sublist2.
      + simpl.
        unfold h1map_vector in vflatten.
        rewrite vflatten.
        apply concatenate_oplistsplit.
  Defined.

  (** ** Constructors and destuctors. *)

  (** [build_term] builds a term starting from principal operation symbol and subterms, while
  [princop] and [subterms] are the corresponding destructors. *)

  Local Definition oplist_build (nm: names σ) (v: Vector (oplist σ) (length (arity nm)))
    : oplist σ := cons nm (vecoplist2oplist v).

  Local Lemma oplist_build_isaterm (nm: names σ) (v: (term σ)⋆ (arity nm))
    : isaterm (sort nm) (oplist_build nm (h1map_vector (λ _, term2oplist) v)).
  Proof.
    unfold oplist_build, isaterm.
    rewrite oplistexec_cons.
    rewrite oplistexec_vecoplist2oplist.
    change (length (arity nm),, pr2 (arity nm)) with (arity nm).
    induction (opexec_just_f nm (arity nm) (isprefix_self _)) as [rest [p1 p2]].
    rewrite prefix_remove_self in p2.
    apply just_injectivity in p2.
    induction p2.
    assumption.
  Defined.

  Local Definition build_term (nm: names σ) (v: (term σ)⋆ (arity nm)): term σ (sort nm).
  Proof.
    exists (oplist_build nm (h1map_vector (λ _, term2oplist) v)).
    apply oplist_build_isaterm.
  Defined.

  Local Definition term_decompose {s: sorts σ} (t: term  σ s):
    ∑ (nm:names σ) (v: (term σ)⋆ (arity nm))
      , (HVec (h1map_vector (λ _ t', hProptoType (length (term2oplist t') < length t)) v))
         × sort nm = s
         × oplist_build nm (h1map_vector (λ _, term2oplist) v) = t.
  Proof.
    induction t as [l lstack].
    cbv [pr1 term2oplist].
    revert l lstack.
    refine (list_ind _ _ _).
    - intro lstack.
      apply ii1_injectivity in lstack.
      apply (maponpaths length) in lstack.
      apply negpaths0sx in lstack.
      contradiction.
    - intros x xs IHxs lstack.
      exists x.
      unfold isaterm in lstack.
      rewrite oplistexec_cons in lstack.
      apply opexec_just_b in lstack.
      induction lstack as [xssort [xsdef stackxs]].
      pose (xsdef' := xsdef).
      apply cons_inj1 in xsdef'.
      apply cons_inj2 in xsdef.
      induction xsdef'.
      induction xsdef.
      rewrite concatenate_nil in stackxs.
      induction (oplist2vecoplist xs stackxs) as [vtail [vlen vflatten]].
      exists vtail.
      repeat split.
      + exact (h2map (λ _ _ p, natlehtolthsn _ _ p) vlen).
      + unfold oplist_build.
        rewrite <- vflatten.
        apply idpath.
  Defined.

  Definition princop {s: sorts σ} (t: term σ s): names σ
    := pr1 (term_decompose t).

  Definition subterms {s: sorts σ} (t: term σ s): (term σ)⋆ (arity (princop t))
    := pr12 (term_decompose t).

  Local Definition subterms_length {s: sorts σ} (t: term σ s)
    : HVec (h1map_vector (λ _ t', hProptoType (length (term2oplist t') < length t)) (subterms t))
    := pr122 (term_decompose t).

  Local Definition princop_sorteq {s: sorts σ} (t: term σ s): sort (princop t) = s
    := pr122 (pr2 (term_decompose t)).

  Local Definition oplist_normalization {s: sorts σ} (t: term σ s)
     : term2oplist (build_term (princop t) (subterms t)) = t
     := pr222 (pr2 (term_decompose t)).

  (** *** Term normalization *)
  (**
    We prove that [princop (build_term nm v) = nm], [subterms (build_term nm v) = v] and
    [build_term (princop t) (subterms t))] is equal to [t] modulo [transport].
  *)

  Local Lemma term_normalization {s: sorts σ} (t: term σ s)
     : transportf (term σ) (princop_sorteq t) (build_term (princop t) (subterms t)) = t.
  Proof.
    unfold princop, subterms, princop_sorteq.
    induction (term_decompose t) as [nm [v [vlen [nmsort normalization]]]].
    induction nmsort.
    change (build_term nm v = t).
    apply subtypePairEquality'.
    - apply normalization.
    - apply isapropisaterm.
  Defined.

  Local Lemma princop_build_term (nm: names σ) (v: (term σ)⋆ (arity nm))
    : princop (build_term nm v) = nm.
  Proof.
    apply idpath.
  Defined.

  Local Lemma subterms_build_term (nm: names σ) (v: (term σ)⋆ (arity nm))
    : subterms (build_term nm v) = v.
  Proof.
    set (t := build_term nm v).
    set (tnorm := term_normalization t).
    assert (princop_sorteq_idpath: princop_sorteq t = idpath (sort nm)).
    {
      apply proofirrelevance.
      apply isasetifdeceq.
      apply decproperty.
    }
    rewrite princop_sorteq_idpath in tnorm.
    change (transportb (term σ) (idpath (sort nm)) t) with t in tnorm.
    set (tnorm_list := maponpaths pr1 tnorm).
    apply cons_inj2 in tnorm_list.
    apply vecoplist2oplist_inj in tnorm_list.
    exact tnorm_list.
  Defined.

  (** *** Miscellanea properties for terms. *)

  Local Lemma length_term {s: sorts σ} (t: term σ s): length t > 0.
  Proof.
    induction t as [l stackl].
    induction (oplistexec_positive_b _ _ _ stackl) as [x [xs lstruct]].
    induction (! lstruct).
    apply idpath.
  Defined.

  Local Lemma term_notnil {X: UU} {s: sorts σ} {t: term σ s}: length t ≤ 0 → X.
  Proof.
    intro tlen.
    apply natlehneggth in tlen.
    contradicts tlen (length_term t).
  Defined.

End Term.

(** ** Term induction. *)

(**
If [P] is a map from terms to properties, then [term_ind_HP P] is the inductive hypothesis for terms:
given an operation symbol [nm], a sequence of terms of type specified by the arity of [nm], a proof of
the property [P] for eache of the terms in [v], we need a proof of [P] for the term built from [nm] and [v].
*)

Section TermInduction.

  Context {σ: signature}.

  Definition term_ind_HP (P: ∏ (s: sorts σ), term σ s → UU) :=
    ∏ (nm: names σ)
      (v: (term σ)⋆ (arity nm))
      (IH: HVec (h1map_vector P v))
    , P (sort nm) (build_term nm v).

  (**
  The proof of the induction principle [term_ind] for terms proceeds by induction on the lenght of
  the oplist forming the terms in [term_ind_onlength].
  *)

  Local Lemma term_ind_onlength (P: ∏ (s: sorts σ), term σ s → UU) (R: term_ind_HP P)
    : ∏ (n: nat) (s: sorts σ) (t: term σ s), length t ≤ n →  P s t.
  Proof.
    induction n.
    - intros s t tlen.
      exact (term_notnil tlen).
    - intros s t tlen.
      apply (transportf (P s) (term_normalization t)).
      induction (princop_sorteq t).
      change (P (sort (princop t)) (build_term (princop t) (subterms t))).
      apply (R (princop t) (subterms t)).
      refine (h2map _ (subterms_length t)).
      intros.
      apply IHn.
      apply natlthsntoleh.
      eapply natlthlehtrans.
      + exact X.
      + exact tlen.
  Defined.

(*
  I would like to prove something like the following:

  Lemma term_ind_onlength_step (P: ∏ (s: sorts σ), term σ s → UU) (R: term_ind_HP P) (nm: names σ) (v: (term σ)⋆ (arity nm))
    : ∏ (n: nat) (tlehn:  length (build_term nm v) ≤ n),
        term_ind_onlength P R n _ _ tlehn
        =  R nm v (transportf (λ x, HVec (hmap_vector P x))
                              (subterms_build_term nm v)
                              (hhmap (subterms_length (build_term nm v)) (λ s t p, term_ind_onlength P R n s t (istransnatleh (natlthtoleh _ _ p) tlehn)))).
*)

  Theorem term_ind (P: ∏ (s: sorts σ), term σ s → UU) (R: term_ind_HP P) {s: sorts σ} (t: term σ s)
    : P s t.
  Proof.
    exact (term_ind_onlength P R (length t) s t (isreflnatleh _)).
  Defined.

  (** *** Term induction step *)

  (** In order to use term_induction, we need to prove an unfolding property. For example, for natural
  number induction the unfolding property is [nat_rect P a IH (S n) = IH n (nat_rect P a IH n)], in our
  case is given by [term_ind_step].
  *)

  Local Lemma term_ind_onlength_nirrelevant (P: ∏ (s: sorts σ), term σ s → UU) (R: term_ind_HP P)
    : ∏ (n m1 m2: nat)
        (m1lehn: m1 ≤ n) (m2lehn: m2 ≤ n)
        (s: sorts σ) (t: term σ s)
        (lenm1: length t ≤ m1) (lenm2: length t ≤ m2)
      , term_ind_onlength P R m1 s t lenm1 = term_ind_onlength P R m2 s t lenm2.
  Proof.
    induction n.
    - intros.
      exact (term_notnil (istransnatleh lenm1 m1lehn)).
    - intros.
      induction m1.
      + exact (term_notnil lenm1).
      + induction m2.
        * exact (term_notnil lenm2).
        * simpl.
          apply maponpaths.
          set (f := paths_rect _ _ _).
          apply (maponpaths (λ x, f x _ _)).
          apply maponpaths.
          apply (maponpaths (λ x, h2map x _)).
          do 3 (apply funextsec; intro).
          apply IHn.
          -- apply m1lehn.
          -- apply m2lehn.
  Defined.

  Local Lemma nat_rect_step {P: nat → UU} (a: P 0) (IH: ∏ n: nat, P n → P (S n)) (n: nat):
    nat_rect P a IH (S n) = IH n (nat_rect P a IH n).
  Proof. apply idpath. Defined.

  Local Lemma paths_rect_step (A : UU) (a : A) (P : ∏ a0 : A, a = a0 → UU) (x: P a (idpath a))
     : paths_rect A a P x a (idpath a) = x.
  Proof. apply idpath. Defined.

  Lemma term_ind_step (P: ∏ (s: sorts σ), term σ s → UU) (R: term_ind_HP P) (nm: names σ) (v: (term σ)⋆ (arity nm))
    : term_ind P R (build_term nm v) = R nm v (h2map (λ s t q, term_ind P R t) (h1lift v)).
  Proof.
    unfold term_ind.
    set (t := build_term nm v).
    simpl (length t).
    unfold term_ind_onlength at 1.
    rewrite nat_rect_step.
    set (v0len := subterms_length t).
    set (v0norm := term_normalization t).
    clearbody v0len v0norm.  (* Needed to make induction work *)
    change (princop t) with nm in *.
    induction (! (subterms_build_term nm v: subterms t = v)).
    assert (princop_sorteq_idpath: princop_sorteq t = idpath (sort nm)).
    {
      apply proofirrelevance.
      apply isasetifdeceq.
      apply decproperty.
    }
    induction (! princop_sorteq_idpath).
    change (build_term nm v = t) in v0norm.
    assert (v0normisid: v0norm = idpath _).
    {
      apply proofirrelevance.
      apply isasetterm.
    }
    induction (! v0normisid).
    rewrite idpath_transportf.
    rewrite paths_rect_step.
    apply maponpaths.
    rewrite (h1map_h1lift_as_h2map v v0len).
    apply (maponpaths (λ x, h2map x _)).
    repeat (apply funextsec; intro).
    apply (term_ind_onlength_nirrelevant P R  (pr1 (vecoplist2oplist (h1map_vector (λ x2 : sorts σ, term2oplist) v)))).
    - apply isreflnatleh.
    - apply natlthsntoleh.
      apply x1.
  Defined.

  (** *** Immediate applications of term induction *)

  (**
  [depth] returns the depth of a term, while [fromterm] is the evaluation map from terms
  to an algebra. Finally, [fromtermstep] is the unfolding property for [fromterm].
  *)

  Definition depth {s: sorts σ}: term σ s → nat
    := term_ind (λ _ _, nat)
                (λ (nm: names σ) (v: (term σ)⋆ (arity nm)) (depths: HVec (h1map_vector (λ _ _, nat) v)),
                   1 + h2foldr (λ _ _, max) 0 depths).

  Local Definition fromterm {A: sUU (sorts σ)} (op : ∏ (nm : names σ), A⋆ (arity nm) → A (sort nm)) {s: sorts σ}
    : term σ s → A s
    := term_ind (λ s _, A s) (λ nm v rec, op nm (h2lower rec)).

  Lemma fromtermstep {A: sUU (sorts σ)} (nm: names σ)
                     (op : ∏ (nm : names σ), A⋆ (arity nm) → A (sort nm))
                     (v: (term σ)⋆ (arity nm))
    : fromterm op (build_term nm v) = op nm (h1map (@fromterm A op) v).
  Proof.
    unfold fromterm.
    rewrite term_ind_step.
    rewrite h2lower_h1map_h1lift.
    apply idpath.
  Defined.

End TermInduction.

(** ** Notations for ground terms. *)
(**
Since [term], [termset], [fromterm] and [fromtermstep]  will be redefined in
[UniMath.Algebra.Universal.VTerms] in their more general form with variables, we introduce
here notations [gterm], [make_gterm] and similar to make the ground version publically
available with special names.
*)

Notation gterm := term.

Notation gtermset := termset.

Notation fromgterm := fromterm.

Notation fromgtermstep := fromtermstep.

Notation build_gterm := build_term.

(** * Curried version of [build_term] *)

(** Defines a curried version of [build_term] which is easier to use in practice. **)

Section iterbuild.

  (**
    If [v] is a vector of types of length [n], [iterfun v B] is the curried version of [v → B], i.e.
    [iterfun v B] =  [(el v 1) → ((el v 2) → ...... → ((el v n) → B)].
  *)

  Definition iterfun {n: nat} (v: Vector UU n) (B: UU): UU.
  Proof.
    revert n v.
    refine (vector_ind _ _ _).
    - exact B.
    - intros x n xs IHxs.
      exact (x → IHxs).
  Defined.

  (**
     If  [f: HVec v → B], then [itercurry f] is the curried version of [f], which has type
     [iterfun v B].
  *)

  Definition itercurry {n: nat} {v: Vector UU n} {B: UU} (f: HVec v → B): iterfun v B.
  Proof.
    revert n v f.
    refine (vector_ind _ _ _).
    - intros.
      exact (f tt).
    - intros x n xs IHxs f.
      simpl in f.
      simpl.
      intro a.
      exact (IHxs (λ l, f (a,, l))).
  Defined.

  (**
    [build_term_curried nm t1 ... tn] builds a term from the operation symbol [nm] and terms (of the
    correct sort) [t1] ... [tn].
  *)

  Definition build_gterm_curried {σ: signature} (nm: names σ)
    : iterfun (vector_map (term σ) (pr2 (arity nm))) (term σ (sort nm))
    := itercurry (build_term nm).

End iterbuild.
