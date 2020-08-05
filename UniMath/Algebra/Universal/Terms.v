(** * Terms for a given signature *)

(**
   This file contains a formalization of terms over a signature, defined as a sequence of
   function symbols. This sequence is though to be executed by a stack machine: each
   symbol of arity n pops n elements from the stack and pushes a new element.
   A sequence of function symbols is a term when the result of the execution is a stack
   with a single element and no stack underflow occurs.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Combinatorics.Vectors.
Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Algebra.Universal.Maybe.
Require Import UniMath.Algebra.Universal.MoreLists.
Require Import UniMath.Algebra.Universal.HVectors.
Require Import UniMath.Algebra.Universal.Signatures.

Local Open Scope stn.
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

  Local Lemma vecoplist2oplist_inj {n : list (sorts σ)} {v1 v2: Vector (oplist σ) (length n)}
        (v1status: ∏ (i: ⟦ length n ⟧), ∑ s: sorts σ, isaterm s (el v1 i))
        (v2status: ∏ (i: ⟦ length n ⟧), ∑ s: sorts σ, isaterm s (el v2 i))
    : vecoplist2oplist v1 = vecoplist2oplist v2 → v1 = v2.
  Proof.
    revert n v1 v2 v1status v2status.
    refine (list_ind _ _ _).
    - intros.
      induction v1.
      induction v2.
      apply idpath.
    - intros x xs IH v1 v2 v1status v2status eq.
      change v1 with (vcons (hd v1) (tl v1)) in *.
      change v2 with (vcons (hd v2) (tl v2)) in *.
      change (hd v1 ++ (vecoplist2oplist (tl v1)) = hd v2 ++ (vecoplist2oplist (tl v2))) in eq.
      apply (maponpaths (λ l, oplistsplit l 1)) in eq.
      pose (status1 := v1status firstelement).
      pose (status2 := v2status firstelement).
      rewrite (oplistsplit_concatenate _ _ 1 [pr1 status1] (pr2 status1) (isreflnatleh _)) in eq.
      rewrite (oplistsplit_concatenate _ _ 1 [pr1 status2] (pr2 status2) (isreflnatleh _)) in eq.
      do 2 change 1 with (length [pr1 status1]) in eq at 1.
      do 2 change 1 with (length [pr1 status2]) in eq at 1.
      rewrite (oplistsplit_self (pr2 status1)) in eq.
      rewrite (oplistsplit_self (pr2 status2)) in eq.
      cbn in eq.
      apply map_on_two_paths.
      + apply (maponpaths pr1 eq).
      + apply IH.
        * intro i.
          rewrite el_tl.
          apply v1status.
        * intro i.
          rewrite el_tl.
          apply v2status.
        * apply (maponpaths (λ l, pr2 l: oplist σ)) in eq.
          assumption.
  Defined.

  Local Lemma oplist2status_vecoplist2oplist {n: list (sorts σ)} {v: Vector (oplist σ) (length n)}
        (vstatus: ∏ (i: ⟦ length n ⟧), isaterm (nth n i) (el v i))
    : oplist2status (vecoplist2oplist v) = statusok n.
  Proof.
    revert n v vstatus.
    refine (list_ind _ _ _).
    - induction v.
      reflexivity.
    - intros x xs IH v vstatus.
      change v with (vcons (hd v) (tl v)).
      change (vecoplist2oplist (hd v ::: tl v)) with (hd v ++ (vecoplist2oplist (tl v))).
      rewrite oplist2status_concatenate.
      + rewrite IH.
        * change (hd v) with (el v firstelement).
          rewrite (vstatus firstelement).
          apply idpath.
        * intro.
          rewrite el_tl.
          apply vstatus.
      + change (hd v) with (el v firstelement).
        rewrite (vstatus firstelement).
        apply negpathsii1ii2.
  Defined.

  Local Definition oplist2vecoplist (l: oplist σ) {n: list (sorts σ)}
        (lstatus: oplist2status l = statusok n)
    : ∑ (v: Vector (oplist σ) (length n))
      , (∏ (i: ⟦ length n ⟧), isaterm (nth n i) (el v i))
          × (∏ (i: ⟦ length n ⟧), length (el v i) ≤ length l)
          × vecoplist2oplist v = l.
  Proof.
    revert n l lstatus.
    refine (list_ind _ _ _).
    - intros.
      exists vnil.
      repeat split.
      + intro i.
        apply fromstn0.
        assumption.
      + intro i.
        apply fromstn0.
        assumption.
      + apply oplist2status_zero_b in lstatus.
        rewrite lstatus.
        apply idpath.
    - intros x xs IH l lstatus.
      induction (oplist2status_oplistsplit l 1 lstatus (natleh0n 0)) 
         as [firststatus [reststatus [concstatus [firststatusp [reststatusp firstlen]]]]].
      set (first := pr1 (oplistsplit l 1)) in *.
      set (rest := pr2 (oplistsplit l 1)) in *.
      cbn in rest.
      apply length_one_back in firstlen.
      induction firstlen as [a firststatus'].
      induction (!firststatus').
      change ((a :: []) ++ reststatus) with (a :: reststatus) in concstatus.
      pose (concstatus' := concstatus).
      apply cons_inj1 in concstatus'.
      apply cons_inj2 in concstatus.
      induction (!concstatus).
      induction (!concstatus').
      induction (IH rest reststatusp) as [v [vstatus [vlen vflatten]]].
      exists (vcons first v).
      repeat split.
      + intro i.
        induction i as [i ilehsn].
        induction i.
        * change (isaterm a first).
          exact firststatusp.
        * change (S i ,, ilehsn) with (dni_firstelement (i,, ilehsn)).
          rewrite (el_vcons_tl v).
          exact (vstatus (i ,, ilehsn)).
      + intro i.
        induction i as [i ilehsn].
        induction i.
        * change (el (vcons first v) (0,, ilehsn)) with first.
          rewrite <- (concatenate_oplistsplit l 1).
          apply length_sublist1.
        * change (S i ,, ilehsn) with (dni_firstelement (i,, ilehsn)).
          rewrite (el_vcons_tl v).
          eapply istransnatleh.
          -- exact (vlen (i ,, ilehsn)).
          -- rewrite <- (concatenate_oplistsplit l 1).
             apply length_sublist2.
      + change ((concatenate first  (vecoplist2oplist v)) = l).
        rewrite vflatten.
        apply concatenate_oplistsplit.
  Defined.

  Local Definition oplist_build_term (nm: names σ) (v: Vector (oplist σ) (length (arity nm)))
    : oplist σ := cons nm (vecoplist2oplist v).

  Local Lemma oplist_build_term_status (nm: names σ) (v: Vector (oplist σ) (length (arity nm)))
        (vstatus: (∏ (i: ⟦ length (arity nm) ⟧), isaterm (nth (arity nm) i) (el v i)))
    : isaterm (sort nm) (oplist_build_term nm v).
  Proof.
    unfold oplist_build_term, isaterm.
    rewrite oplist2status_cons.
    rewrite oplist2status_vecoplist2oplist.
    - induction (statuscons_statusok_f (arity nm) (isprefix_self _)) as [rest [p1 p2]].
      rewrite prefix_remove_self in p2.
      apply just_injectivity in p2.
      induction p2.
      assumption.
    - exact vstatus.
  Defined.

  Local Definition oplist_decompose (l: oplist σ) (s: sorts σ) (l1status: isaterm s l):
    ∑ (nm:names σ) (v: Vector (oplist σ) (length (arity nm)))
    , (∏ (i: ⟦ length (arity nm) ⟧), isaterm (nth (arity nm) i) (el v i))
        × (∏ (i: ⟦ length (arity nm) ⟧), length (el v i) < length l)
        × oplist_build_term nm v = l.
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
      induction (oplist2vecoplist xs statusxs) as [vtail [vstatus [vlen vflatten]]].
      exists vtail.
      repeat split.
      + exact vstatus.
      + intro i.
        apply natlehtolthsn.
        apply vlen.
      + unfold oplist_build_term.
        rewrite vflatten.
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

  Local Lemma nth_el {A: UU} (l: list A) (i : ⟦ length l ⟧): nth l i = el (pr2 l) i.
  Proof.
    revert l i.
    refine (list_ind _ _ _).
    - reflexivity.
    - intros x xs IH i.
      induction i as [i iproof].
      induction i.
      + apply idpath.
      + unfold nth.
        change (length (x :: xs)) with (S (length xs)) in *.
        change ((S i,, iproof): ⟦ S (length xs) ⟧)   with (dni_firstelement (i,, iproof): ⟦ S (length xs) ⟧) at 2.
        change (pr2 (x :: xs)) with (vcons x (pr2 xs)).
        rewrite (el_vcons_tl (pr2 xs)).
        change ( (S i,, iproof): ⟦ S (length xs) ⟧) with (make_stn (S (length xs)) (S i)  iproof).
        rewrite nth'_step.
        exact (IH (i,, iproof)).
  Defined.
  
  Lemma term_extens {s: sorts σ} {t1 t2 : term σ s} (p : term2oplist t1 = term2oplist t2)
    : t1 = t2.
  Proof.
    apply subtypePairEquality'.
    2: apply isapropisaterm.
    exact p.
  Defined.

  (* [build_term] builds a term starting from its principal function symbols and its subterms *)

  Definition build_term (nm: names σ) (v: HVec (vector_map (λ s, term σ s) (pr2 (arity nm)))): term σ (sort nm).
  Proof.
    exists (oplist_build_term nm ((hmap_vector (λ x, term2oplist) v))).
    apply oplist_build_term_status.
    intro i.
    rewrite el_hmap_vector.
    rewrite nth_el.
    exact (term2proof (helfam v i)).
  Defined.
  
  Context {s: sorts σ}.

  (** [princop] returns the principal function symbol of a term *)

  Definition princop (t: term σ s): names σ
    := pr1 (oplist_decompose t s (term2proof t)).

  (** [subterms] retusn the subterms of a term term *)

  Definition subterms (t: term σ s): HVec (vector_map (λ s, term σ s) (pr2 (arity (princop t)))).
  Proof.
    unfold princop.
    induction (oplist_decompose t s (term2proof t)) as [nm [v [vstatus [vlen normalization]]]].
    
    exact (mk_vector (λ (i: ⟦ length (arity nm) ⟧), make_term  (el v i) (vstatus i))).
  Defined.

  Local Lemma subterms_length (t: term σ): ∏ (i: ⟦ arity (princop t) ⟧), length (el (subterms t) i) < length t.
  Proof.
    unfold subterms, princop.
    induction (oplist_decompose t (term2proof t)) as [nm [v [vstatus [vlen normalization]]]].
    intro i.
    rewrite el_mk_vector.
    cbn - [natlth].
    exact (vlen i).
  Defined.

  Local Lemma term_normalization (t: term σ): build_term (princop t) (subterms t) = t.
  Proof.
    unfold princop, subterms.
    induction (oplist_decompose t (term2proof t)) as [nm [v [vstatus [vlen normalization]]]].
    apply subtypePairEquality'.
    2: apply isapropisaterm.
    rewrite vector_map_mk_vector.
    unfold funcomp.
    cbn.
    rewrite mk_vector_el.
    apply normalization.
  Defined.

  Local Lemma princop_build_term (nm: names σ) (v: Vector (term σ) (arity nm))
    : princop (build_term nm v) = nm.
  Proof.
    apply idpath.
  Defined.

  Local Lemma subterms_build_term (nm: names σ) (v: Vector (term σ) (arity nm))
    : subterms (build_term nm v) = v.
  Proof.
    set (t := build_term nm v).
    set (v0norm := term_normalization t).
    unfold build_term in v0norm.
    unfold oplist_build_term in v0norm.
    set (v0norm_list := maponpaths pr1 v0norm).
    cbn [pr1] in v0norm_list.
    apply cons_inj2 in v0norm_list.
    apply vecoplist2oplist_inj in v0norm_list.
    unfold term2oplist in v0norm_list.
    - apply vector_extens.
      intro i.
      apply term_extens.
      apply (maponpaths (λ v, el v i)) in v0norm_list.
      do 2 rewrite el_vector_map in v0norm_list.
      apply v0norm_list.
    - intro i.
      rewrite el_vector_map.
      apply (el (subterms t) i).
    - intro i.
      rewrite el_vector_map.
      apply (el v i).
  Defined.

  Local Lemma length_term (t: term σ): length t > 0.
  Proof.
    induction t as [l statusl].
    induction (oplist2status_positive_b statusl) as [x [xs lstruct]].
    induction (! lstruct).
    cbn.
    apply idpath.
  Defined.

  Local Lemma term_notnil {X: UU} {t: term σ}: length t ≤ 0 → X.
  Proof.
    intro tlen.
    apply natlehneggth in tlen.
    contradicts tlen (length_term t).
  Defined.

End Term.

(** ** Term induction and recursion *)

Section TermInduction.

  Context {σ: signature}.

  Definition term_ind_HP (P: term σ → UU) :=
    ∏ (nm: names σ)
      (v: Vector (term σ) (arity nm))
      (IH: ∏ (i:  ⟦ arity nm ⟧), P (el v i))
    , P (build_term nm v).

  Local Lemma term_ind_onlength (P: term σ → UU) (R: term_ind_HP P)
    : ∏ (n: nat) (t: term σ), length t ≤ n →  P t.
  Proof.
    induction n.
    - intros t tlen.
      exact (term_notnil tlen).
    - intros t tlen.
      apply (transportf P (term_normalization t)).
      (* rewrite <- (term_normalization t).  *)
      (* induction (term_normalization t). *)
      apply (R (princop t) (subterms t)).
      intro i.
      apply (IHn (el (subterms t) i)).
      change (S (length (el (subterms t) i)) ≤ S n).
      eapply istransnatleh.
      -- apply natlthtolehsn.
         apply (subterms_length t).
      -- apply tlen.
  Defined.

  Theorem term_ind (P: term σ → UU) (R: term_ind_HP P) (t: term σ)
    : P t.
  Proof.
    exact (term_ind_onlength P R (length t) t (isreflnatleh _)).
  Defined.

  Local Lemma term_ind_onlength_nirrelevant (P: term σ → UU) (R: term_ind_HP P)
    : ∏ (n m1 m2: nat)
        (m1lehn: m1 ≤ n) (m2lehn: m2 ≤ n)
        (t: term σ)
        (lenm1: length t ≤ m1) (lenm2: length t ≤ m2)
      , term_ind_onlength P R m1 t lenm1 = term_ind_onlength P R m2 t lenm2.
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
          do 2 apply maponpaths.
          apply funextsec.
          intro i.
          apply IHn.
          -- apply m1lehn.
          -- apply m2lehn.
  Defined.

  Lemma term_ind_step (P: term σ → UU) (R: term_ind_HP P)
        (nm: names σ) (v: Vector (term σ) (arity nm))
    : term_ind P R (build_term nm v)
      = R nm v (λ i:  ⟦ arity nm ⟧, term_ind P R (el v i)).
  Proof.
    unfold term_ind.
    set (t := build_term nm v).
    simpl (length (term2oplist _)).
    unfold term_ind_onlength at 1.
    rewrite nat_rect_step.
    set (v0len := subterms_length t).
    set (v0norm := term_normalization t).
    clearbody v0len v0norm.  (* Needed to make induction work *)
    induction (! (subterms_build_term nm v: subterms t = v)).
    assert (v0normisid: v0norm = idpath _).
    {
      apply proofirrelevance.
      apply isasetterm.
    }
    rewrite v0normisid.
    rewrite idpath_transportf.
    apply maponpaths.
    apply funextsec.
    intro i.
    unfold term_ind_onlength.
    apply (term_ind_onlength_nirrelevant P R (length (vecoplist2oplist (vector_map pr1 v)))).
    - apply isreflnatleh.
    - apply natlthsntoleh.
      apply (v0len i).
  Defined.

  Definition depth: term σ → nat
    := term_ind (λ _, nat) (λ (nm: names σ) (vterm: Vector (term σ) (arity nm))
                (levels: ∏ i : ⟦ arity nm ⟧, (λ _ : term σ, nat) (el vterm i)),
                1 + vector_foldr max 0 (mk_vector levels)).

  Definition fromterm {A:UU}
             (op : ∏ (nm : names σ), Vector A (arity nm) → A)
    : term σ → A
    := term_ind (λ _, A) (λ nm _ rec, op nm (mk_vector rec)).

  Lemma fromtermstep {A: UU} (nm: names σ) (op : ∏ (nm : names σ), Vector A (arity nm) → A)
                     (v: Vector (term σ) (arity nm))
    : fromterm op (build_term nm v) = op nm (vector_map (fromterm op) v).
  Proof.
    unfold fromterm.
    rewrite term_ind_step.
    rewrite vector_map_as_mk_vector.
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

  Definition iterfun (A B: UU) (n: nat): UU
    := nat_rect (λ _, UU) B (λ (n: nat) (IH: UU), A → IH) n.

  Definition itercurry {A B: UU} {n: nat} (f: Vector A n → B): iterfun A B n.
  Proof.
    induction n.
    - cbn. exact (f vnil).
    - unfold iterfun.
      rewrite nat_rect_step.
      intro x.
      set (f' := λ (v: Vector A n), f (vcons x v)).
      apply (IHn f').
  Defined.

  Definition build_term_curried {σ: signature} (nm: names σ)
    : iterfun (term σ) (term σ) (arity nm)
    := itercurry (build_term nm).

End iterbuild.
