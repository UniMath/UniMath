(** * Terms for a given signature *)

(**
   This file contains a formalization of terms over a signature, defined as a sequence of
   function symbols. This sequence is though to be executed by a stack machine: each
   symbol of arity n pops n elements from the stack and pushes a new element.
   A sequence of function symbols is a term when the result of the execution is a stack
   with a single element and no stack underflow occurs.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.Maybe.
Require Import UniMath.Algebra.Universal.DecSet.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.HVectors.
Require Import UniMath.Algebra.Universal.Signatures.
Require Import UniMath.Algebra.Universal.SortedTypes.

Local Open Scope list.

(** ** Lemmas on natural numbers that are used in the rest of the file. *)

Section NatLemmas.

  Local Lemma oplistsplit_arith1 {n1 n2: nat}: S n1 + n2 - 1 = n1 + n2.
  Proof.
    change (S n1) with (1 + n1).
    rewrite natplusassoc.
    rewrite (natpluscomm 1 (n1 + n2)).
    rewrite plusminusnmm.
    apply idpath.
  Defined.
  
  Local Lemma oplistsplit_arith2 {n1 n2 n3: nat}: S n1 ≤ n2 → n1 + n3 ≤ n2 + n3 - 1.
  Proof.
    intro nlehm.
    apply (natlehandplusr  _ _  n3) in nlehm.
    apply (natgehandminusl _ _  1) in nlehm.
    change (S n1) with (1 + n1) in nlehm.
    rewrite natplusassoc in nlehm.
    rewrite (natpluscomm 1 (n1 + n3)) in nlehm.
    rewrite plusminusnmm in nlehm.
    assumption.
  Defined.

  Local Lemma oplistsplit_arith3 {a b: nat}: S a + b - 1 = a + b.
  Proof.
    change (S a) with (1 + a).
    rewrite natplusassoc.
    rewrite natpluscomm.
    rewrite plusminusnmm.
    apply idpath.
  Defined.

  Local Lemma natleh_add (a b c: nat): b = a + c → a ≤ b.
  Proof.
   set (X := isreflnatleh a).
   set (Y := natleh0n c).
   set (Z := natlehandplus _ _ _ _ X Y).
   intro H.
   rewrite <- H in Z.
   rewrite natplusr0 in Z.
   assumption.
 Defined.

  Local Lemma nat_movplusright {a b c: nat}: a + c = b → a = b - c.
  Proof.
    intros hp.
    apply (maponpaths (λ n: nat, n - c)) in hp.
    rewrite plusminusnmm in hp.
    assumption.
  Defined.

End NatLemmas.


(** ** Definition of oplist (operation list) *)
(**
   An oplist is a list of function symbols, interpreted as commands to be executed by a stack
   machine: each symbol of arity n pops n elements from the stack and pushes a new element.
   Therefore, to each oplist is associated a status, which may be either a natural number, giving
   the number of elements in the stack after the list is ececuted, or an error condition, when
   executing the oplist generates a stack underflow. A term is an oplist with status one.
 *)

Section Oplist.

  Local Definition oplist (σ: signature):= list σ.
  
  Identity Coercion oplistislist: oplist >-> list.

  Local Corollary isasetoplist (σ: signature): isaset (oplist σ).
  Proof.
    apply isofhlevellist.
    induction σ as [ S  [ O  ar ] ].
    apply setproperty.
  Defined.

  Local Definition status (σ: signature): UU := maybe (list (sorts σ)).

  Local Definition statusok {σ: signature}: list (sorts σ) → status σ := just.

  Local Definition statuserror {σ: signature}: status σ := nothing.

  Local Lemma isasetstatus (σ: signature): isaset (status σ).
  Proof.
    apply isasetmaybe.
    apply isofhlevellist.
    induction σ as [ S  [ O  ar ] ].
    apply isasetifdeceq.
    apply decproperty.
  Defined.

  Context {σ: signature}.

  (** *** The [statuscons] and [oplist2status] functions *)
  (**
     [statuscons] returns the status of executing the function symbol [nm] when the current
     stack status is [s]. The [statuserror] status is propagated by [statuscons]. Building
     over [statuscons], [oplist2status] returns the status corresponding to an oplist.
   *)
 
  Local Definition statuscons (nm: σ) (s: status σ): status σ :=
    flatmap (λ tl, (statusok ((sort nm) :: tl))) (flatmap (λ s, prefix_remove (arity nm) s) s).

  (*
  Local Definition statuscons (nm: σ) (s: status σ): status σ.
  Proof.
    induction s as [s | serror].
    - induction (prefix_remove (deceqnames σ) (arity nm) s) as [tail | _].
      + exact (statusok ((sort nm) :: tail) ).
      + exact statuserror.
    - exact statuserror.
  Defined.
  *)

  Local Definition oplist2status (l: oplist σ): status σ := foldr statuscons (statusok nil) l.

  Local Definition isaterm (s: sorts σ) (l: oplist σ) := oplist2status l = statusok ([s]).

  (** TODO: Quite complex... make it shorter *)
  Local Lemma isapropisaterm (s: sorts σ) (l: oplist σ): isaprop (isaterm s l).
  Proof.
    unfold isaterm.
    apply isasetmaybe.
    apply isofhlevellist.
    apply isasetifdeceq.
    apply decproperty.
  Defined.

End Oplist.

Section OplistProps.

  Context {σ: signature}.

  (** **** Properties of [statuscons] and [oplist2status] *)

  Local Lemma statuscons_dec (nm: names σ) (l: list (sorts σ))
    : ((statuscons nm (ii1 l) = statuserror) × (prefix_remove (arity nm) l = nothing))
              ⨿  ∑ (p: list (sorts σ)), (statuscons nm (ii1 l) = statusok ((sort nm) :: p)) × (prefix_remove (arity nm) l = statusok p).
  Proof.
    unfold statuscons.
    rewrite flatmap_just.
    induction (prefix_remove (arity nm) l) as [ p | error ].
    - apply ii2.
      exists p.
      split; apply idpath.
    - apply ii1.
      split.
      + apply idpath.
      + induction error.
        apply idpath.
  Defined.

 Local Lemma statuscons_statusok_f {nm: names σ} (l: list (sorts σ)) (arityok: isprefix (arity nm) l)
    : ∑ p: list (sorts σ), statuscons nm (statusok l) = statusok ((sort nm) :: p) ×  prefix_remove (arity nm) l = just p.
  Proof.
    set (X := statuscons_dec nm l).
    induction X as [err | ok].
    - induction err as [_  err].
      contradicts arityok err.
    - assumption.
  Defined.

  Local Lemma statuscons_statusok_b {nm: names σ} {s: status σ} {l: list (sorts σ)}
  : statuscons nm s = statusok l → ∑ x xs, l = x :: xs × x = sort nm × s = statusok ((arity nm) ++ xs).
  Proof.
    intro scons.
    induction s as [sok | serror].
    - set (X := statuscons_dec nm sok).
      induction X as [Xerr | Xok].
      + induction Xerr as [X1 _].
        rewrite X1 in scons.
        contradiction (negpathsii2ii1 _ _ scons).
      + induction Xok as [p [X1 X2]].
        set (ldef := !scons @ X1).
        apply just_injectivity in ldef.
        rewrite ldef.
        exists (sort nm).
        exists p.
        repeat split.
        change (tail (sort nm :: p)) with (just p).
        apply maponpaths.
        apply prefix_remove_back in X2.
        assumption.
   -  contradiction (negpathsii2ii1 _ _ scons).
  Defined.
  
  Local Lemma statuscons_zero_b {nm: names σ} {s: status σ}
    : ¬ (statuscons nm s = statusok nil).
  Proof.
    induction s as [l | error].
    - induction (statuscons_dec nm l) as [scons_err| scons_ok].
      + apply pr1 in scons_err.
        intro H'.
        set (H'' :=  (!! scons_err @ H')).
        apply negpathsii1ii2 in H''.
        assumption.
      + induction scons_ok as [p [proofp _]].
        intro H'.
        set (H'' :=  (!proofp @ H')).
        apply ii1_injectivity in H''.
        apply negpathsconsnil in H''.
        assumption.
    - apply negpathsii2ii1.
  Defined.
  
  Local Lemma oplist2status_nil
    : oplist2status (nil: oplist σ) = statusok nil.
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplist2status_cons {nm: names σ} {l: oplist σ}
    : oplist2status (nm :: l) = statuscons nm (oplist2status l).
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplist2status_zero_b {l: oplist σ}
    : oplist2status l = statusok nil → l = nil.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - reflexivity.
    - intros x xs _ lstatus.
      rewrite oplist2status_cons in lstatus.
      apply statuscons_zero_b in lstatus.
      contradiction.
  Defined.

  Local Lemma oplist2status_positive_b {l: oplist σ} (so: sorts σ) (sos: list (sorts σ))
    : oplist2status l = statusok (cons so sos)
      → ∑ (x: names σ) (xs: oplist σ), l = cons x xs.
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

  Local Definition statusconcatenate (s1 s2: status σ): status σ
    := flatmap (λ s2', flatmap (λ s1', statusok (s1' ++ s2')) s1) s2.

  Local Lemma statusconcatenate_statuscons {nm: names σ} {s1 s2: status σ}
    : (statuscons nm s1 != statuserror)
      → statusconcatenate (statuscons nm s1) s2 = statuscons nm (statusconcatenate s1 s2).
  Proof.
    induction s1 as [s1' | ].
    2: contradiction.
    induction s2 as [s2'| ].
    2: reflexivity.
    intro H.
    set (X := statuscons_dec nm s1').
    induction X as [Xerr | Xok].
    - contradicts H (pr1 Xerr).
    - induction Xok as [tl [scons pref]].
      rewrite scons.
      simpl.
      rewrite concatenateStep.
      unfold statuscons.
      simpl.
      erewrite prefix_remove_concatenate.
      + rewrite flatmap_just.
        apply idpath.
      + assumption.
  Defined.

 Local Lemma oplist2status_concatenate {l1 l2: oplist σ}
    : oplist2status l1 != statuserror
      → oplist2status (concatenate l1 l2)
        = statusconcatenate (oplist2status l1) (oplist2status l2).
  Proof.
    revert l1.
    refine (list_ind _ _ _).
    - intros.
      change (concatenate nil l2) with (l2).
      induction (oplist2status l2) as [s2 | s2error].
      + apply idpath.
      + induction s2error.
        apply idpath.
    - intros x xs IH noerror.
      rewrite oplist2status_cons.
      rewrite statusconcatenate_statuscons by (assumption).
      rewrite <- IH.
      + apply idpath.
      + intro error.
        rewrite oplist2status_cons in noerror.
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
      exact (nil,, nil).
    - intros x xs IH n.
      induction n.
      + exact (nil,, (cons x xs)).
      + induction (IH (n + length (arity x))) as [IHfirst IHsecond].
        exact (cons x IHfirst ,, IHsecond).
  Defined.

  Local Lemma oplistsplit_zero {l: oplist σ}: oplistsplit l 0 = nil,, l.
  Proof.
    revert l.
    refine (list_ind _ _ _).
    - apply idpath.
    - reflexivity.
  Defined.

  Local Lemma oplistsplit_nil {n: nat}: oplistsplit nil n = nil,, nil.
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistsplit_cons {x: names σ} {xs: oplist σ} {n: nat}
    : oplistsplit (cons x xs) (S n)
      = cons x (pr1 (oplistsplit xs (n + length (arity x)))) ,, (pr2 (oplistsplit xs (n + length (arity x)))).
  Proof.
    apply idpath.
  Defined.

  Local Lemma oplistsplit_concatenate (l1 l2: oplist σ) (n: nat) (m: list (sorts σ))
    : oplist2status l1 = statusok m → n ≤ length m
      → oplistsplit (concatenate l1 l2) n
        = pr1 (oplistsplit l1 n) ,, concatenate (pr2 (oplistsplit l1 n)) l2.
  Proof.
    revert l1 m n.
    refine (list_ind _ _ _).
    - intros m n l1status nlehm.
      apply ii1_injectivity in l1status.
      rewrite <- l1status in *.
      apply natleh0tois0 in nlehm.
      rewrite nlehm.
      rewrite oplistsplit_zero.
      apply idpath.
    - intros x1 xs1 IH m n l1status nlehm.
      rewrite concatenateStep.
      induction n.
      + apply idpath.
      + rewrite oplist2status_cons in l1status.
        apply statuscons_statusok_b in l1status.
        induction l1status as [m_head [m_tail [mdef [mheaddef xs1status]]]].
        assert (newnok: S n + length (arity x1) - 1 ≤  length (arity x1 ++ m_tail)).
        {
          rewrite length_concatenate.
          rewrite mdef in nlehm.
          rewrite length_cons in nlehm.
          change (S n) with (1 + n).
          rewrite natplusassoc.
          rewrite natpluscomm.
          rewrite <- natplusminusle.
          2: apply isreflnatleh.
          rewrite natpluscomm.
          change (n + length (arity x1) ≤ length (arity x1) + length m_tail).
          rewrite (natpluscomm (length (arity x1)) _).
          apply natlehandplusr.
          assumption.
        }
        set (IHinst := IH (arity x1 ++ m_tail) (S n + length (arity x1) - 1) xs1status newnok).
        rewrite oplistsplit_arith1 in IHinst.
        do 2 rewrite oplistsplit_cons.
        apply pathsdirprod.
        * cbn.
          apply maponpaths.
          apply (maponpaths pr1) in IHinst.
          cbn in IHinst.
          assumption.
        * apply (maponpaths dirprod_pr2) in IHinst.
          assumption.
  Defined.

  Local Lemma concatenate_oplistsplit (l: oplist σ) (n: nat)
    : concatenate (pr1 (oplistsplit l n)) (pr2 (oplistsplit l n)) = l.
  Proof.
    revert l n.
    refine (list_ind _ _ _).
    - reflexivity.
    - intros x xs IH n.
      induction n.
      + apply idpath.
      + rewrite oplistsplit_cons.
        cbn - [concatenate].
        rewrite concatenateStep.
        rewrite IH.
        apply idpath.
  Defined.

  Local Lemma oplist2status_oplistsplit (l: oplist σ) {m: list (sorts σ)} (n: nat)
    : oplist2status l = statusok m → n ≤ length m
      → ∑ t1 t2: list (sorts σ), 
          m = t1 ++ t2 
          × oplist2status (pr1 (oplistsplit l n)) = statusok t1 
          × oplist2status (pr2 (oplistsplit l n)) = statusok t2
          × length t1 = n.
  Proof.
    revert l m n.
    refine (list_ind _ _ _).
    - intros m n nilstatus nlehm.
      cbn.
      apply ii1_injectivity in nilstatus.
      rewrite <- nilstatus in *.
      apply natleh0tois0 in nlehm.
      rewrite nlehm.
      exists nil.
      exists nil.
      repeat split ; apply idpath.
    - intros x xs IH m n lstatus nlehm.
      induction n.
      + rewrite oplistsplit_zero.
        exists nil.
        exists m.
        repeat split ; trivial.
      + rewrite oplistsplit_cons.
        cbn - [oplist2status].
        rewrite oplist2status_cons in lstatus.
        apply statuscons_statusok_b in lstatus.
        induction lstatus as [mhead [ mtail [mdef [mheaddef xsstatus]]]].
        assert (newok: n + length (arity x) ≤ length (arity x ++ mtail)).
        {
           apply (oplistsplit_arith2(n3 := length (arity x))) in nlehm.
           rewrite mdef in nlehm.
           rewrite length_cons in nlehm.
           rewrite oplistsplit_arith3 in  nlehm.
           rewrite (natpluscomm (length mtail) _) in nlehm.
           rewrite <- length_concatenate in nlehm.
           assumption.
        }
        induction (IH (arity x ++ mtail) (n + length (arity x)) xsstatus newok) 
           as [t1 [ t2 [ t1t2concat [ t1def [ t2def t1len ] ] ] ] ].
        exists (mhead :: drop t1 (length (arity x))).
        exists t2.
        repeat split.
        * rewrite  concatenateStep.
          rewrite <- drop_concatenate.
          -- rewrite <- t1t2concat.
             rewrite drop_concatenate.
             2: apply isreflnatleh.
             rewrite drop_full.
             assumption.
          -- rewrite natpluscomm in t1len.
             apply natleh_add in t1len.
             assumption.
        * rewrite oplist2status_cons.
          rewrite t1def.
          unfold statuscons.
          unfold statusok, just.
          rewrite flatmap_just.
          rewrite prefix_remove_drop.
          -- unfold just.
             rewrite flatmap_just.
             apply maponpaths.
             rewrite mheaddef.
              apply idpath.
          -- intro H.
             apply (prefix_remove_concatenate2 _ _ t2) in H.
             ++ rewrite <- t1t2concat in H.
                rewrite prefix_remove_prefix in H.
                exact (negpathsii1ii2 _ _ H).
             ++ rewrite natpluscomm in t1len.
                apply natleh_add in t1len.
                assumption.
        * apply t2def.
        * rewrite length_cons.
          apply maponpaths.
          rewrite length_drop.
          rewrite t1len.
          apply plusminusnmm.
  Defined.

  Local Corollary oplistsplit_self {l: oplist σ} {n: list (sorts σ)}
    : oplist2status l = statusok n → oplistsplit l (length n) = l ,, nil.
  Proof.
    intro lstatus.
    set (H := oplist2status_oplistsplit l (length n) lstatus (isreflnatleh (length n))).
    induction H as [t1 [t2 [t1t2 [t1def [t2def t1len]]]]].
    set (normalization := concatenate_oplistsplit l (length n)).
    apply (maponpaths length) in t1t2.
    rewrite length_concatenate in t1t2.
    rewrite t1len in t1t2.
    apply pathsinv0 in t1t2.
    rewrite natpluscomm in t1t2.
    apply nat_movplusright in t1t2.
    rewrite minuseq0' in t1t2.
    apply length_zero_back in t1t2.
    induction (! t1t2).
    apply oplist2status_zero_b in t2def.
    rewrite t2def in normalization.
    rewrite concatenate_nil in normalization.
    induction (oplistsplit l (length n)) as [l1 l2].
    cbn in t2def, normalization.
    rewrite t2def.
    rewrite normalization.
    apply idpath.
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
    exact p.
  Defined.

  Local Lemma vecoplist2oplist_inj {n: nat} {ar: Vector (sorts σ) n} {v1 v2: HVec (vector_map (λ s, term σ s) ar)}
    : vecoplist2oplist (hmap_vector (λ _, term2oplist) v1) = vecoplist2oplist (hmap_vector (λ _, term2oplist) v2) 
      → v1 = v2.
  Proof.
    revert n ar v1 v2.
    refine (vector_ind _ _ _).
    - intros.
      induction v1.
      induction v2.
      apply idpath.
    - intros x n xs IH v1 v2 eq.
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
      apply map_on_two_paths.
      + apply subtypePairEquality'.
        * apply (maponpaths pr1 eq).
        * apply isapropisaterm.
      + apply IH.
        apply (maponpaths (λ l, pr2 l: oplist σ)) in eq.
        assumption.
  Defined.

  Local Lemma oplist2status_vecoplist2oplist {n: nat} {ar: Vector (sorts σ) n} {v: HVec (vector_map (λ s, term σ s) ar)}
    : oplist2status (vecoplist2oplist (hmap_vector (λ _, term2oplist) v)) = statusok (n ,, ar).
  Proof.
    revert n  ar v.
    refine (vector_ind _ _ _).
    - induction v.
      reflexivity.
    - intros x n xs IH v.
      induction v as [vx vxs].
      simpl.
      simpl in vx.
      rewrite oplist2status_concatenate.
      + rewrite IH.
        rewrite (term2proof vx).
        apply idpath.
      + rewrite (term2proof vx).
        apply negpathsii1ii2.
  Defined.

  Local Definition oplist2vecoplist {n: nat} {ar: Vector (sorts σ) n} (l: oplist σ) (lstatus: oplist2status l = statusok (n,, ar))
    : ∑ (v: HVec (vector_map (λ s, term σ s) ar))
        , (HVec (hmap_vector (λ _ t, hProptoType (length (term2oplist t) ≤ length l)) v))
          × vecoplist2oplist (hmap_vector (λ _, term2oplist) v) = l.
  Proof.
    revert n ar l lstatus.
    refine (vector_ind _ _ _).
    - intros.
      exists hvnil.
      split.
      + exact hvnil.
      + apply oplist2status_zero_b in lstatus.
        rewrite lstatus.
        apply idpath.
    - intros x n xs IH l lstatus.
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
      induction (IH rest reststatusp) as [v [vlen vflatten]].
      exists (hvcons (make_term firststatusp) v).
      repeat split.
      + change (length first ≤ length l).
        rewrite <- (concatenate_oplistsplit l 1).
        apply length_sublist1.
      + change (HVec (hmap_vector (λ (s: sorts σ) (t: term σ s), hProptoType (length (term2oplist t) ≤ length l)) v)).
        assert (length rest ≤ length l).
        {
        rewrite <- (concatenate_oplistsplit l 1).
        apply length_sublist2.
        }
        exact (hmap'' vlen (λ _ _ p, istransnatleh p X)).
      + simpl.
        rewrite vflatten.
        apply concatenate_oplistsplit.
  Defined.

  Local Definition oplist_build_term (nm: names σ) (v: Vector (oplist σ) (length (arity nm)))
    : oplist σ := cons nm (vecoplist2oplist v).

  Local Lemma oplist_build_term_status (nm: names σ) (v: HVec (vector_map (λ s, term σ s) (pr2 (arity nm))))
    : isaterm (sort nm) (oplist_build_term nm (hmap_vector (λ _, term2oplist) v)).
  Proof.
    unfold oplist_build_term, isaterm.
    rewrite oplist2status_cons.
    rewrite oplist2status_vecoplist2oplist.
    induction (statuscons_statusok_f (arity nm) (isprefix_self _)) as [rest [p1 p2]].
    rewrite prefix_remove_self in p2.
    apply just_injectivity in p2.
    induction p2.
    assumption.
  Defined.

  Local Definition oplist_decompose (l: oplist σ) (s: sorts σ) (l1status: isaterm s l):
    ∑ (nm:names σ) (v: HVec (vector_map (λ s, term σ s) (pr2 (arity nm))))
      , (HVec (hmap_vector (λ _ t, hProptoType (length (term2oplist t) < length l)) v))
         × sort nm = s
         × oplist_build_term nm (hmap_vector (λ _, term2oplist) v) = l.
  Proof.
    revert l l1status.
    refine (list_ind _ _ _).
    - intro l1status.
      apply ii1_injectivity in l1status.
      apply (maponpaths length) in l1status.
      apply negpaths0sx in l1status.
      contradiction.
    - intros x xs IH l1status.
      exists x.
      unfold isaterm in l1status.
      rewrite oplist2status_cons in l1status.
      apply statuscons_statusok_b in l1status.
      induction l1status as [xsort [xssort [ a [b statusxs]]]].
      pose (a' := a).
      apply cons_inj1 in a'.
      apply cons_inj2 in a.
      induction a'.
      induction a.
      rewrite concatenate_nil in statusxs.
      induction (oplist2vecoplist xs statusxs) as [vtail [vlen vflatten]].
      exists vtail.
      repeat split.
      + exact (hmap'' vlen (λ _ _ p, natlehtolthsn _ _ p)).
      + exact (! b).
      + unfold oplist_build_term.
        rewrite <- vflatten.
        apply idpath.
  Defined.

  (* [build_term] builds a term starting from its principal function symbols and its subterms *)

  Definition build_term (nm: names σ) (v: HVec (vector_map (λ s, term σ s) (pr2 (arity nm)))): term σ (sort nm).
  Proof.
    exists (oplist_build_term nm ((hmap_vector (λ x, term2oplist) v))).
    apply oplist_build_term_status.
  Defined.

  (** [princop] returns the principal function symbol of a term *)

  Definition princop {s: sorts σ} (t: term σ s): names σ
    := pr1 (oplist_decompose t s (term2proof t)).
    
  Definition princop_sort {s: sorts σ} (t: term σ s): sort (princop t) = s.
  Proof.
    unfold princop.
    induction (oplist_decompose t s (term2proof t)) as [nm [v [vlen [nmsort normalization]]]].
    exact nmsort.
  Defined.

  Definition subterms {s: sorts σ} (t: term σ s): HVec (vector_map (λ s, term σ s) (pr2 (arity (princop t)))).
  Proof.
    unfold princop.
    induction (oplist_decompose t s (term2proof t)) as [nm [v [vlen normalization]]].
    exact v.
  Defined.

  (** [subterms] retusn the subterms of a term term *)

  Local Lemma subterms_length {s: sorts σ} (t: term σ s)
    : HVec (hmap_vector (λ _ t', hProptoType (length (term2oplist t') < length t)) (subterms t)).
  Proof.
    unfold subterms, princop.
    induction (oplist_decompose t s (term2proof t)) as [nm [v [vlen normalization]]].
    exact vlen.
  Defined.

  Local Lemma term_normalization {s: sorts σ} (t: term σ s)
     : build_term (princop t) (subterms t) = transportb (λ s, term σ s) (princop_sort t) t.
  Proof.
    unfold princop, subterms, princop_sort.
    induction (oplist_decompose t s (term2proof t)) as [nm [v [vlen [nmsort normalization]]]].
    induction nmsort.
    use total2_paths_f.
    - simpl.
      rewrite normalization.
      change (term2oplist t = pr1 (transportf (λ s : pr1decSet (sorts σ), term σ s) (idpath (sort nm)) t)).
      apply idpath_transportf.
    - apply isapropisaterm.
  Defined.

  Local Lemma princop_build_term (nm: names σ) (v: HVec (vector_map (λ s, term σ s) (pr2 (arity nm))))
    : princop (build_term nm v) = nm.
  Proof.
    apply idpath.
  Defined.

  Local Lemma subterms_build_term (nm: names σ) (v: HVec (vector_map (λ s, term σ s) (pr2 (arity nm))))
    : subterms (build_term nm v) = v.
  Proof.
    set (t := build_term nm v).
    set (v0norm := term_normalization t).
    unfold build_term, oplist_build_term in v0norm.
    set (X := princop_sort t).
    assert (princop_sort_idpath: princop_sort t = idpath (sort nm)).
    {
    apply proofirrelevance.
    apply isasetifdeceq.
    apply decproperty. 
    }
    rewrite princop_sort_idpath in v0norm.
    change (transportb (λ s : sorts σ, term σ s) (idpath (sort nm)) t)  with t in v0norm.
    set (v0norm_list := maponpaths pr1 v0norm).
    apply cons_inj2 in v0norm_list.
    apply vecoplist2oplist_inj in v0norm_list.
    exact v0norm_list.
  Defined.

  Local Lemma length_term {s: sorts σ} (t: term σ s): length t > 0.
  Proof.
    induction t as [l statusl].
    induction (oplist2status_positive_b _ _ statusl) as [x [xs lstruct]].
    induction (! lstruct).
    cbn.
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
      (v: HVec (vector_map (λ s, term σ s) (pr2 (arity nm))))
      (IH: HVec (hmap_vector (λ s t, P s t) v))
    , P _ (build_term nm v).

  Local Lemma term_ind_onlength (P: ∏ (s: sorts σ), term σ s → UU) (R: term_ind_HP P)
    : ∏ (n: nat) (s: sorts σ) (t: term σ s), length t ≤ n →  P s t.
  Proof.
    induction n.
    - intros s t tlen.
      exact (term_notnil tlen).
    - intros s t tlen.
      set (X := term_normalization t).
      apply (maponpaths (transportf (λ s : sorts σ, term σ s) (princop_sort t))) in X.
      rewrite transportfbinv in X.
      apply (transportf (λ t, P s t) X).
      clear X.
      induction (princop_sort t).
      rewrite idpath_transportf.
      (* rewrite <- (term_normalization t).  *)
      (* induction (term_normalization t). *)
      apply (R (princop t) (subterms t)).
      set (stlen := subterms_length t).
      refine (hmap'' stlen _).
      intros.
      apply IHn.
      apply natlthsntoleh.
      eapply natlthlehtrans.
      + exact q.
      + exact tlen.
  Defined.

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
      set (tlen := istransnatleh lenm1 m1lehn).
      exact (term_notnil tlen).
    - intros.
      induction m1.
      + exact (term_notnil lenm1).
      + induction m2.
        * exact (term_notnil lenm2).
        * simpl.
          apply maponpaths.
          set (f := paths_rect (sorts σ) (sort (princop t))
                    (λ (a : sorts σ) (p0 : sort (princop t) = a),
                     P a (transportf (λ s0 : sorts σ, term σ s0) p0 (build_term (princop t) (subterms t))))).
          apply (maponpaths (λ x, f x s (princop_sort t))).
          apply maponpaths. 
          apply (maponpaths (λ x, hmap'' (subterms_length t) x)).
          apply funextsec.
          intro.
          apply funextsec.
          intro.
          apply funextsec.
          intro.
          apply IHn.
          -- apply m1lehn.
          -- apply m2lehn.
  Defined.
  
  Lemma nat_rect_step {P: nat → UU} (a: P 0) (IH: ∏ n: nat, P n → P (S n)) (n: nat): 
    nat_rect P a IH (S n) = IH n (nat_rect P a IH n).
  Proof. apply idpath. Defined.

  Lemma term_ind_step (P: ∏ (s: sorts σ), term σ s → UU) (R: term_ind_HP P)
        (nm: names σ) (v: HVec (vector_map (λ s, term σ s) (pr2 (arity nm))))
    : term_ind P R (build_term nm v) = R nm v (hmap' (λ s t, term_ind P R t) v).
  Proof.
    unfold term_ind.
    set (t := build_term nm v).
    simpl (length (term2oplist _)).
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
    rewrite v0normisid.
    simpl.
    rewrite idpath_transportf.
    apply maponpaths.
    unfold t in *.
    clear t v0norm v0normisid princop_sort_idpath.
    rewrite (hmap12 v  v0len).
    apply maponpaths.
    repeat (apply funextsec; intro).
    apply (term_ind_onlength_nirrelevant P R  (pr1 (vecoplist2oplist (hmap_vector (λ x2 : sorts σ, term2oplist) v)))).
    - apply isreflnatleh.
    - apply natlthsntoleh. 
      apply x1.
  Defined.

  Definition depth {s: sorts σ}: term σ s → nat
    := term_ind (λ _ _, nat) 
                (λ (nm: names σ) (v: HVec (vector_map (λ s, term σ s) (pr2 (arity nm))))
                   (levels: HVec (hmap_vector (λ _ _, nat) v)),
                   1 + hvec_foldr' levels (λ _ _, max) 0).

  Definition fromterm {A: sUU (sorts σ)}
             (op : ∏ (nm : names σ), HVec (vector_map (λ s, A s) (pr2 (arity nm))) → A (sort nm)) {s: sorts σ}
    : term σ s → A s
    := term_ind (λ s _, A s)
                 (λ nm v rec, op nm (hmap_vector_flat rec)).

  Lemma fromtermstep {A: sUU (sorts σ)} (nm: names σ)
                     (op : ∏ (nm : names σ), HVec (vector_map (λ s, A s) (pr2 (arity nm)))  → A (sort nm))
                     (v: HVec (vector_map (λ s, term σ s) (pr2 (arity nm))))
    : fromterm op (build_term nm v) = op nm (hmap (λ s t, @fromterm A op s t) v).
  Proof.
    unfold fromterm.
    rewrite term_ind_step.
    rewrite hmap_vector_flat_hmap'.
    apply idpath.
  Defined.

End TermInduction.

(** * Iterated version of [build_term] *)
(**
   Defines a curried version of [build_term] which is easier to use in practice.
 **)

Section iterbuild.

  (**
     [iterfun A B n] is the curried version of [Vector A n → B], i.e.
     [iterfun A B n] =  [A → (A → ...... → (A → B)] with A repeated n times
   *)
  
  Definition iterfun {n: nat} (v: Vector UU n) (B: UU): UU.
  Proof.
    revert n v.
    refine (vector_ind _ _ _).
    - exact B.
    - intros x n xs IH.
      exact (x → IH).
  Defined.

  Definition itercurry {n: nat} {v: Vector UU n} {B: UU} (f: HVec v → B): iterfun v B.
  Proof.
    revert n v f.
    refine (vector_ind _ _ _).
    - intros.
      exact (f tt).
    - intros x n xs IH f.
      simpl in f.
      simpl.
      intro a.
      exact (IH (λ l, f (a,, l))).
  Defined.

  Definition build_term_curried {σ: signature} (nm: names σ)
    : iterfun (vector_map (λ s, term σ s) (pr2 (arity nm))) (term σ (sort nm))
    := itercurry (build_term nm).

End iterbuild.
