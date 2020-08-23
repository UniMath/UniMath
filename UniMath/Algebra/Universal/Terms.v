(** * Terms for a given signature *)

(**
   This file contains a formalization of terms over a signature, implemneted as a sequence of
   function symbols. This sequence is though to be executed by a stack machine: each
   symbol of arity n pops n elements from the stack and pushes a new element.
   A sequence of function symbols is a term when the result of the execution is a stack
   with a single element and no stack underflow or type errors occur.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.DecSet.
Require Import UniMath.Algebra.Universal.Maybe.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.HVectors.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.SortedTypes.

Local Open Scope sorted.
Local Open Scope list.

  
(** ** Definition of oplist (operation list) *)
(**
   An oplist is a list of function symbols, interpreted as commands to be executed by a stack
   machine: each symbol of arity n pops n elements from the stack and pushes a new element.
   Therefore, to each oplist is associated a status, which may be either a list of sorts, giving
   the sorts of elements in the stack after the list is executed, or an error condition, when
   executing the oplist generates a stack underflow or a type error. A term is an oplist whose status
   is a list of length one.
 *)

Section Oplist.

  Local Definition oplist (σ: signature):= list (names σ).
  
  Identity Coercion oplistislist: oplist >-> list.

  Local Corollary isasetoplist (σ: signature): isaset (oplist σ).
  Proof.
    apply isofhlevellist.
    apply setproperty.
  Defined.

  Local Definition status (σ: signature): UU := maybe (list (sorts σ)).

  Local Definition statusok {σ: signature}: list (sorts σ) → status σ := just.

  Local Definition statuserror {σ: signature}: status σ := nothing.

  Local Lemma isasetstatus (σ: signature): isaset (status σ).
  Proof.
    apply isasetmaybe.
    apply isofhlevellist.
    apply isasetifdeceq.
    apply decproperty.
  Defined.

  Context {σ: signature}.

  (** *** The [statuscons] and [oplist2status] functions *)
  (**
     [statuscons] returns the status of executing the function symbol [nm] when the current
     stack status is a list [s]. The [statuserror] status is propagated by [statuscons]. Building
     over [statuscons], [oplist2status] returns the status corresponding to an oplist.
   *)
  Local Definition statuscons (nm: names σ): status σ → status σ
    := flatmap (λ ss, statusok (sort nm :: ss)) ∘ flatmap (λ ss, prefix_remove (arity nm) ss).

  Local Definition oplist2status (l: oplist σ): status σ := foldr statuscons (statusok []) l.

  Local Definition isaterm (s: sorts σ) (l: oplist σ): UU := oplist2status l = statusok ([s]).

  Local Lemma isapropisaterm (s: sorts σ) (l: oplist σ): isaprop (isaterm s l).
  Proof.
    apply isasetstatus.
  Defined.

End Oplist.

Bind Scope list_scope with oplist.

Section OplistProps.

  Context {σ: signature}.

  (** **** Properties of [statuscons] and [oplist2status] *)

  Local Lemma statuscons_dec (nm: names σ) (ss: list (sorts σ))
    : ((statuscons nm (statusok ss) = statuserror) × (prefix_remove (arity nm) ss = nothing))
              ⨿  ∑ (ss': list (sorts σ)), (statuscons nm (statusok ss) = statusok ((sort nm) :: ss')) × (prefix_remove (arity nm) ss = statusok ss').
  Proof.
    unfold statuscons, funcomp, statusok.
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

 Local Lemma statuscons_statusok_f (nm: names σ) (ss: list (sorts σ)) (arityok: isprefix (arity nm) ss)
    : ∑ ss': list (sorts σ), statuscons nm (statusok ss) = statusok ((sort nm) :: ss') ×  prefix_remove (arity nm) ss = just ss'.
  Proof.
    induction (statuscons_dec nm ss) as [err | ok].
    - induction err as [_  err].
      contradicts arityok err.
    - assumption.
  Defined.

  Local Lemma statuscons_statusok_b (nm: names σ) (st: status σ) (ss: list (sorts σ))
    : statuscons nm st = statusok ss → ∑ ss', ss = sort nm :: ss' × st = statusok ((arity nm) ++ ss').
  Proof.
    intro scons.
    induction st as [stok | sterror].
    - induction (statuscons_dec nm stok) as [scons_err | scons_ok].
      + induction scons_err as [scons_err _].
        unfold statusok, just in scons_err.
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
  
  Local Lemma statuscons_zero_b (nm: names σ) (st: status σ)
    : ¬ (statuscons nm st = statusok nil).
  Proof.
    induction st as [stok | sterror].
    - induction (statuscons_dec nm stok) as [scons_err| scons_ok].
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
  
  Local Lemma oplist2status_nil
    : oplist2status (nil: oplist σ) = statusok nil.
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplist2status_cons (nm: names σ) (l: oplist σ)
    : oplist2status (nm :: l) = statuscons nm (oplist2status l).
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplist2status_zero_b (l: oplist σ): oplist2status l = statusok nil → l = nil.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - reflexivity.
    - intros x xs _ lstatus.
      apply statuscons_zero_b in lstatus.
      contradiction.
  Defined.

  Local Lemma oplist2status_positive_b (l: oplist σ) (s: sorts σ) (ss: list (sorts σ))
    : oplist2status l = statusok (s :: ss) → ∑ (x: names σ) (xs: oplist σ), l = x :: xs.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - intro nilstatus.
      cbn in nilstatus.
      apply ii1_injectivity in nilstatus.
      apply negpathsnilcons in nilstatus.
      contradiction.
    - intros x xs _ lstatus.
      exists x.
      exists xs.
      apply idpath.
  Defined.

  Local Definition statusconcatenate (st1 st2: status σ): status σ
    := flatmap (λ st2', flatmap (λ st1', statusok (st1' ++ st2')) st1) st2.

  Local Lemma statusconcatenate_statuscons (nm: names σ) (st1 st2: status σ)
    : statuscons nm st1 != statuserror
       → statusconcatenate (statuscons nm st1) st2 = statuscons nm (statusconcatenate st1 st2).
  Proof.
    induction st1 as [ss1 | ].
    2: contradiction.
    induction st2 as [ss2| ].
    2: reflexivity.
    intro H.
    induction (statuscons_dec nm ss1) as [Xerr | Xok].
    - contradicts H (pr1 Xerr).
    - induction Xok as [tl [scons pref]].
      unfold statusok, just in scons.
      rewrite scons.
      simpl.
      rewrite concatenateStep.
      unfold statuscons, funcomp.
      simpl.
      erewrite prefix_remove_concatenate.
      * apply idpath.
      * assumption.
  Defined.

 Local Lemma oplist2status_concatenate (l1 l2: oplist σ)
    : oplist2status l1 != statuserror
      → oplist2status (concatenate l1 l2)
        = statusconcatenate (oplist2status l1) (oplist2status l2).
  Proof.
    revert l1.
    refine (list_ind _ _ _).
    - intros.
      change ([] ++ l2) with (l2).
      induction (oplist2status l2) as [l2ok | l2error].
      + apply idpath.
      + induction l2error.
        apply idpath.
    - intros x xs IHxs noerror.
      change (oplist2status (x :: xs)) with (statuscons x (oplist2status xs))  in *.
      rewrite statusconcatenate_statuscons by (assumption).
      rewrite <- IHxs.
      + apply idpath.
      + intro error.
        rewrite error in noerror.
        contradiction.
  Defined.

  (** *** The [oplistsplit] function *)
  (**
     [oplistsplit] splits an oplist in an oplist of up to [n] terms and an oplist of the remaining
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
    : oplist2status l1 = statusok ss → n ≤ length ss
      → oplistsplit (l1 ++ l2) n
        = make_dirprod (pr1 (oplistsplit l1 n)) (pr2 (oplistsplit l1 n) ++ l2).
  Proof.
    revert l1 ss n.
    refine (list_ind _ _ _).
    - intros ss n l1status nlehss.
      apply ii1_injectivity in l1status.
      rewrite <- l1status in nlehss.
      apply natleh0tois0 in nlehss.
      rewrite nlehss.
      rewrite oplistsplit_zero.
      apply idpath.
    - intros x1 xs1 IHxs1 ss n l1status nlehss.
      change ((x1 :: xs1) ++ l2) with (x1 :: (xs1 ++ l2)).
      induction n.
      + apply idpath.
      + change (oplist2status (x1 :: xs1)) with (statuscons x1 (oplist2status xs1)) in l1status.
        apply statuscons_statusok_b in l1status.
        induction l1status as [sstail [ssdef xs1status]].
        eset (IHinst := IHxs1 (arity x1 ++ sstail) (length (arity x1) + n) xs1status _).
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

  Local Lemma oplist2status_oplistsplit (l: oplist σ) {ss: list (sorts σ)} (n: nat)
    : oplist2status l = statusok ss → n ≤ length ss
      → ∑ t1 t2: list (sorts σ), 
          ss = t1 ++ t2 
          × oplist2status (pr1 (oplistsplit l n)) = statusok t1 
          × oplist2status (pr2 (oplistsplit l n)) = statusok t2
          × length t1 = n.
  Proof.
    revert l ss n.
    refine (list_ind _ _ _).
    - intros m ss nilstatus nlehss.
      cbn.
      apply ii1_injectivity in nilstatus.
      rewrite <- nilstatus in *.
      apply natleh0tois0 in nlehss.
      rewrite nlehss.
      exists nil.
      exists nil.
      repeat split.
    - intros x xs IHxs ss n lstatus nlehss.
      induction n.
      + rewrite oplistsplit_zero.
        exists nil.
        exists ss.
        repeat split.
        assumption.
      + rewrite oplistsplit_cons.
        simpl.
        change (oplist2status (x :: xs)) with (statuscons x (oplist2status xs)) in lstatus.
        apply statuscons_statusok_b in lstatus.
        induction lstatus as [sstail [ssdef xsstatus]].
        eset (IHinst := IHxs (arity x ++ sstail) (length (arity x) + n) xsstatus _).
        induction IHinst as  [t1 [ t2 [ t1t2concat [ t1def [ t2def t1len ] ] ] ] ].
        exists ((sort x) :: drop t1 (length (arity x))).
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
        * rewrite oplist2status_cons.
          rewrite t1def.
          unfold statuscons.
          unfold statusok, just, funcomp.
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
    : oplist2status l = statusok ss → oplistsplit l (length ss) = l ,, nil.
  Proof.
    intro lstatus.
    set (H := oplist2status_oplistsplit l (length ss) lstatus (isreflnatleh (length ss))).
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
    apply oplist2status_zero_b in t2def.
    rewrite t2def in normalization.
    rewrite concatenate_nil in normalization.
    induction (oplistsplit l (length ss)) as [l1 l2].
    simpl in *.
    rewrite t2def.
    rewrite normalization.
    apply idpath.
  Defined.

End OplistProps.

(** ** Terms and related constructors and destructors *)

Section Term.

  (** A term is an oplist together with the proof it is a term *)

  Definition term (σ: signature) (s: sorts σ)
    := ∑ t: oplist σ, isaterm s t.

  Definition make_term {σ: signature} {s: sorts σ} {l: oplist σ} (lstatus: isaterm s l)
    : term σ s := l ,, lstatus.

  Coercion term2oplist {σ: signature} {s: sorts σ}: term σ s → oplist σ := pr1.

  Definition term2proof {σ: signature} {s: sorts σ}: ∏ t: term σ s, isaterm s t := pr2.

  Lemma isasetterm {σ: signature} (s: sorts σ): isaset (term σ s).
  Proof.
    apply isaset_total2.
    - apply isasetoplist.
    - intros.
      apply isasetaprop.
      apply isasetstatus.
  Defined.

  Definition termset {σ: signature} (s: sorts σ): hSet
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
     These functions transform a vector of [n] oplists into an oplists of status [n]
     ([vecoplist2oplist]) and viceversa ([oplist2vecoplist]).
   *)

  Local Definition vecoplist2oplist {n: nat} (v: Vector (oplist σ) n): oplist σ
    := vector_foldr concatenate nil v.

  Local Lemma vecoplist2oplist_vcons {n: nat} (x: oplist σ) (v: Vector (oplist σ) n)
    : vecoplist2oplist (x ::: v) = concatenate x (vecoplist2oplist v).
  Proof.  
    apply idpath.
  Defined.

  Local Lemma oplist2status_vecoplist2oplist {n: nat} {ar: Vector (sorts σ) n} {v: HVec (vector_map (term σ) ar)}
    : oplist2status (vecoplist2oplist (hmap_vector (λ _, term2oplist) v)) = statusok (n ,, ar).
  Proof.
    revert n ar v.
    refine (vector_ind _ _ _).
    - induction v.
      reflexivity.
    - intros x n xs IHxs v.
      induction v as [vx vxs].
      simpl in *.
      rewrite oplist2status_concatenate.
      + rewrite IHxs.
        rewrite (term2proof vx).
        apply idpath.
      + rewrite (term2proof vx).
        apply negpathsii1ii2.
  Defined.

  Local Definition oplist2vecoplist {n: nat} {ar: Vector (sorts σ) n} (l: oplist σ) (lstatus: oplist2status l = statusok (n,, ar))
    : ∑ (v: HVec (vector_map (term σ) ar))
        , (HVec (hmap_vector (λ _ t, hProptoType (length (term2oplist t) ≤ length l)) v))
          × vecoplist2oplist (hmap_vector (λ _, term2oplist) v) = l.
  Proof.
    revert n ar l lstatus.
    refine (vector_ind _ _ _).
    - intros.
      exists hvnil.
      exists hvnil.
      apply oplist2status_zero_b in lstatus.
      rewrite lstatus.
      apply idpath.
    - intros x n xs IHxs l lstatus.
      induction (oplist2status_oplistsplit l 1 lstatus (natleh0n 0)) 
         as [firststatus [reststatus [concstatus [firststatusp [reststatusp firstlen]]]]].
      change (S n,, (x ::: xs)%vector) with (x :: (n ,, xs)) in concstatus.
      set (first := pr1 (oplistsplit l 1)) in *.
      set (rest := pr2 (oplistsplit l 1)) in *.
      apply length_one_back in firstlen.
      induction firstlen as [a firststatus'].
      induction (!firststatus').
      change ((a :: []) ++ reststatus) with (a :: reststatus) in concstatus.
      pose (concstatus' := concstatus).
      apply cons_inj1 in concstatus'.
      apply cons_inj2 in concstatus.
      induction (!concstatus).
      induction (!concstatus').
      induction (IHxs rest reststatusp) as [v [vlen vflatten]].
      exists (hvcons (make_term firststatusp) v).
      repeat split.
      + change (length first ≤ length l).
        rewrite <- (concatenate_oplistsplit l 1).
        apply length_sublist1.
      + change (HVec (hmap_vector (λ (s: sorts σ) (t: term σ s), hProptoType (length (term2oplist t) ≤ length l)) v)).
        eapply (hhmap (λ _ _ p, istransnatleh p _) vlen).
        Unshelve.
        rewrite <- (concatenate_oplistsplit l 1).
        apply length_sublist2.
      + simpl.
        rewrite vflatten.
        apply concatenate_oplistsplit.
  Defined.

  Local Definition oplist_build_term (nm: names σ) (v: Vector (oplist σ) (length (arity nm)))
    : oplist σ := cons nm (vecoplist2oplist v).

  Local Lemma oplist_build_term_status (nm: names σ) (v: term σ ↑ (arity nm))
    : isaterm (sort nm) (oplist_build_term nm (hmap_vector (λ _, term2oplist) v)).
  Proof.
    unfold oplist_build_term, isaterm.
    rewrite oplist2status_cons.
    rewrite oplist2status_vecoplist2oplist.
    change (length (arity nm),, pr2 (arity nm)) with (arity nm).
    induction (statuscons_statusok_f nm (arity nm) (isprefix_self _)) as [rest [p1 p2]].
    rewrite prefix_remove_self in p2.
    apply just_injectivity in p2.
    induction p2.
    assumption.
  Defined.

  Local Definition term_decompose {s: sorts σ} (t: term  σ s):
    ∑ (nm:names σ) (v: term σ ↑ (arity nm))
      , (HVec (hmap_vector (λ _ t', hProptoType (length (term2oplist t') < length t)) v))
         × sort nm = s
         × oplist_build_term nm (hmap_vector (λ _, term2oplist) v) = t.
  Proof.
    induction t as [l lstatus].
    cbv [pr1 term2oplist].
    revert l lstatus.
    refine (list_ind _ _ _).
    - intro lstatus.
      apply ii1_injectivity in lstatus.
      apply (maponpaths length) in lstatus.
      apply negpaths0sx in lstatus.
      contradiction.
    - intros x xs IHxs lstatus.
      exists x.
      unfold isaterm in lstatus.
      rewrite oplist2status_cons in lstatus.
      apply statuscons_statusok_b in lstatus.
      induction lstatus as [xssort [xsdef statusxs]].
      pose (xsdef' := xsdef).
      apply cons_inj1 in xsdef'.
      apply cons_inj2 in xsdef.
      induction xsdef'.
      induction xsdef.
      rewrite concatenate_nil in statusxs.
      induction (oplist2vecoplist xs statusxs) as [vtail [vlen vflatten]].
      exists vtail.
      repeat split.
      + exact (hhmap (λ _ _ p, natlehtolthsn _ _ p) vlen).
      + unfold oplist_build_term.
        rewrite <- vflatten.
        apply idpath.
  Defined.

  (* [build_term] builds a term starting from its principal function symbols and its subterms *)

  Definition build_term (nm: names σ) (v: term σ ↑ (arity nm)): term σ (sort nm).
  Proof.
    exists (oplist_build_term nm (hmap_vector (λ _, term2oplist) v)).
    apply oplist_build_term_status.
  Defined.

  (** [princop] returns the principal function symbol of a term *)

  Definition princop {s: sorts σ} (t: term σ s): names σ
    := pr1 (term_decompose t).

  Definition princop_sort {s: sorts σ} (t: term σ s): sort (princop t) = s.
  Proof.
    unfold princop.
    induction (term_decompose t) as [nm [v [vlen [nmsort normalization]]]].
    exact nmsort.
  Defined.

  Definition subterms {s: sorts σ} (t: term σ s):  term σ ↑ (arity (princop t)).
  Proof.
    unfold princop.
    induction (term_decompose t) as [nm [v X]].
    exact v.
  Defined.

  (** [subterms] retusn the subterms of a term term *)

  Local Lemma subterms_length {s: sorts σ} (t: term σ s)
    : HVec (hmap_vector (λ _ t', hProptoType (length (term2oplist t') < length t)) (subterms t)).
  Proof.
    unfold subterms, princop.
    induction (term_decompose t) as [nm [v [vlen X]]].
    exact vlen.
  Defined.
  
  Local Lemma oplist_normalization {s: sorts σ} (t: term σ s)
     : term2oplist (build_term (princop t) (subterms t)) = t.
  Proof.
    unfold princop, subterms, princop_sort.
    induction (term_decompose t) as [nm [v [vlen [nmsort normalization]]]].
    assumption.
  Defined.

  Local Lemma term_normalization {s: sorts σ} (t: term σ s)
     : transportf (term σ) (princop_sort t) (build_term (princop t) (subterms t)) = t.
  Proof.
    unfold princop, subterms, princop_sort.
    induction (term_decompose t) as [nm [v [vlen [nmsort normalization]]]].
    induction nmsort.
    change (build_term nm v = t). 
    apply subtypePairEquality'.
    - apply normalization.
    - apply isapropisaterm.
  Defined.

  Local Lemma princop_build_term (nm: names σ) (v: term σ ↑ (arity nm))
    : princop (build_term nm v) = nm.
  Proof.
    apply idpath.
  Defined.

  Local Lemma vecoplist2oplist_inj {n: nat} {ar: Vector (sorts σ) n} {v1 v2: HVec (vector_map (term σ) ar)}
    : vecoplist2oplist (hmap_vector (λ _, term2oplist) v1) = vecoplist2oplist (hmap_vector (λ _, term2oplist) v2) 
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

  Local Lemma subterms_build_term (nm: names σ) (v:  term σ ↑ (arity nm))
    : subterms (build_term nm v) = v.
  Proof.
    set (t := build_term nm v).
    set (tnorm := term_normalization t).
    assert (princop_sort_idpath: princop_sort t = idpath (sort nm)).
    {
      apply proofirrelevance.
      apply isasetifdeceq.
      apply decproperty. 
    }
    rewrite princop_sort_idpath in tnorm.
    change (transportb (term σ) (idpath (sort nm)) t) with t in tnorm.
    set (tnorm_list := maponpaths pr1 tnorm).
    apply cons_inj2 in tnorm_list.
    apply vecoplist2oplist_inj in tnorm_list.
    exact tnorm_list.
  Defined.

  Local Lemma length_term {s: sorts σ} (t: term σ s): length t > 0.
  Proof.
    induction t as [l statusl].
    induction (oplist2status_positive_b _ _ _ statusl) as [x [xs lstruct]].
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

(** ** Term induction and recursion *)

Section TermInduction.

  Context {σ: signature}.

  Definition term_ind_HP (P: ∏ (s: sorts σ), term σ s → UU) :=
    ∏ (nm: names σ)
      (v: term σ ↑ (arity nm))
      (IH: HVec (hmap_vector P v))
    , P (sort nm) (build_term nm v).

  Local Lemma term_ind_onlength (P: ∏ (s: sorts σ), term σ s → UU) (R: term_ind_HP P)
    : ∏ (n: nat) (s: sorts σ) (t: term σ s), length t ≤ n →  P s t.
  Proof.
    induction n.
    - intros s t tlen.
      exact (term_notnil tlen).
    - intros s t tlen.
      apply (transportf (P s) (term_normalization t)).
      induction (princop_sort t).
      change (P (sort (princop t)) (build_term (princop t) (subterms t))).
      apply (R (princop t) (subterms t)).
      refine (hhmap _ (subterms_length t)).
      intros.
      apply IHn.
      apply natlthsntoleh.
      eapply natlthlehtrans.
      + exact q.
      + exact tlen.
  Defined.

(*
  I would like to prove something like the following:
  
  Lemma term_ind_onlength_step (P: ∏ (s: sorts σ), term σ s → UU) (R: term_ind_HP P) (nm: names σ) (v:  term σ ↑ (arity nm))
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
          apply (maponpaths (λ x, hhmap x _)).
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

  Lemma term_ind_step (P: ∏ (s: sorts σ), term σ s → UU) (R: term_ind_HP P) (nm: names σ) (v: term σ ↑ (arity nm))
    : term_ind P R (build_term nm v) = R nm v (hmap_lift (λ s, term_ind P R) v).
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
    assert (princop_sort_idpath: princop_sort t = idpath (sort nm)).
    {
      apply proofirrelevance.
      apply isasetifdeceq.
      apply decproperty. 
    }
    induction (! princop_sort_idpath).
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
    rewrite (hmap_lift_as_hhmap v v0len).
    apply (maponpaths (λ x, hhmap x _)).
    repeat (apply funextsec; intro).
    apply (term_ind_onlength_nirrelevant P R  (pr1 (vecoplist2oplist (hmap_vector (λ x2 : sorts σ, term2oplist) v)))).
    - apply isreflnatleh.
    - apply natlthsntoleh. 
      apply x1.
  Defined.

  Definition depth {s: sorts σ}: term σ s → nat
    := term_ind (λ _ _, nat) 
                (λ (nm: names σ) (v: term σ ↑ (arity nm)) (depths: HVec (hmap_vector (λ _ _, nat) v)),
                   1 + hhfoldr (λ _ _, max) 0 depths).

  Definition fromterm {A: sUU (sorts σ)} (op : ∏ (nm : names σ), A ↑ (arity nm) → A (sort nm)) {s: sorts σ}
    : term σ s → A s
    := term_ind (λ s _, A s) (λ nm v rec, op nm (hvec_lower rec)).

  Lemma fromtermstep {A: sUU (sorts σ)} (nm: names σ)
                     (op : ∏ (nm : names σ), A ↑ (arity nm) → A (sort nm))
                     (v: term σ ↑ (arity nm))
    : fromterm op (build_term nm v) = op nm (hmap (@fromterm A op) v).
  Proof.
    unfold fromterm.
    rewrite term_ind_step.
    rewrite hvec_lower_hmap_lift.
    apply idpath.
  Defined.

End TermInduction.

(** * Iterated version of [build_term] *)
(**
   Defines a curried version of [build_term] which is easier to use in practice.
 **)

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

  Definition build_term_curried {σ: signature} (nm: names σ)
    : iterfun (vector_map (term σ) (pr2 (arity nm))) (term σ (sort nm))
    := itercurry (build_term nm).

End iterbuild.
