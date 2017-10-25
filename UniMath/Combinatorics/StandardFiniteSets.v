(** * Standard finite sets . Vladimir Voevodsky . Apr. - Sep. 2011 .

This file contains main constructions related to the standard finite sets defined as the initial intervals of [ nat ] and their properties . *)




(** ** Preamble *)

(** Settings *)

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)



(** Imports. *)

Require Export UniMath.Foundations.NaturalNumbers .
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.MoreFoundations.DecidablePropositions.

(** ** Standard finite sets [ stn ] . *)

Definition stn ( n : nat ) := ∑ m, m < n.
Definition stnpair n m (l:m<n) := (m,,l) : stn n.
Definition stntonat ( n : nat ) : stn n -> nat := @pr1 _ _ .
Coercion stntonat : stn >-> nat .
Lemma stnlt {n} (i:stn n) : i < n.
Proof. intros. exact (pr2 i). Defined.

(* old way:
   Notation " 'stnel' ( i , j ) " :=
      ( stnpair _ _  ( ctlong natlth isdecrelnatlth j i ( idpath true ) ) )
      ( at level 70 ) . *)
Notation " 'stnpr' j " := (j,,idpath _) ( at level 70 ) .
Notation " 'stnel' ( i , j ) " := ( (j,,idpath _) : stn i ) ( at level 70 ) .

Delimit Scope stn with stn.

Notation "⟦ n ⟧" := (stn n) (at level 50) : stn.
(* in agda-mode \[[ n \]] *)

Notation "● i" := (i ,, (idpath _ : natgtb _ _ = _)) (at level 35) : stn.

Lemma isinclstntonat ( n : nat ) : isincl ( stntonat n ) .
Proof. intro .  refine (isinclpr1 _ _) .  intro x .  apply ( pr2 ( natlth x n ) ) .  Defined.

Definition stntonat_incl n := inclpair (stntonat n) (isinclstntonat n).

Lemma isdecinclstntonat ( n : nat ) : isdecincl ( stntonat n ) .
Proof. intro . refine ( isdecinclpr1 _ _) .  intro x . apply isdecpropif . apply ( pr2 _ ) .   apply isdecrelnatgth .  Defined .

Lemma neghfiberstntonat ( n m : nat ) ( is : natgeh m n ) : neg ( hfiber ( stntonat n ) m ) .
Proof. intros . intro h . destruct h as [ j e ] .  destruct j as [ j is' ] .  simpl in e .  rewrite e in is' .  apply ( natgehtonegnatlth _ _ is is' ) . Defined .

Lemma iscontrhfiberstntonat ( n m : nat ) ( is : natlth m n ) : iscontr ( hfiber ( stntonat n ) m ) .
Proof. intros .  apply ( iscontrhfiberofincl ( stntonat n ) ( isinclstntonat n ) ( stnpair n m is ) ) .  Defined .

Local Open Scope nat.

Lemma stn_ne_iff_neq {n} (i j:stn n) : ¬ (i = j) <-> stntonat _ i ≠ stntonat _ j.
Proof.
  intros. split.
  - intro ne. apply nat_nopath_to_neq. Set Printing Coercions. idtac.
    intro e; apply ne; clear ne. now apply subtypeEquality_prop.
  - simpl. intros neq e. now apply (nat_neq_to_nopath neq), maponpaths.
  Unset Printing Coercions.
Defined.

Lemma stnneq {n} : neqReln (stn n).
Proof. (* here we use no axioms *)
  intros n i j. exists (i ≠ j)%nat. split.
  - apply propproperty.
  - apply stn_ne_iff_neq.
Defined.

Notation " x ≠ y " := ( stnneq x y ) (at level 70, no associativity) : stn.
Delimit Scope stn with stn.
Local Open Scope stn.


Lemma isisolatedinstn { n : nat } ( x : stn n ) : isisolated _ x.
Proof. intros . apply ( isisolatedinclb ( stntonat n ) ( isinclstntonat n ) x ( isisolatedn x ) ) .  Defined.

Lemma stnneq_iff_nopath {n} (i j:stn n) : ¬ (i = j) <-> i ≠ j.
Proof. intros. apply negProp_to_iff. Defined.

Definition stnneq_to_nopath {n} (i j:stn n) : ¬ (i = j) <- i ≠ j
  := pr2 (stn_ne_iff_neq i j).

Corollary isdeceqstn ( n : nat ) : isdeceq (stn n).
Proof. intro.  unfold isdeceq. intros x x' . apply (isisolatedinstn x x' ). Defined.

Lemma stn_eq_or_neq {n} (i j:stn n) : (i=j) ⨿ (i≠j).
Proof.
  intros. induction (nat_eq_or_neq i j) as [eq|ne].
  - now apply ii1, subtypeEquality_prop.
  - now apply ii2.
Defined.

Definition weqisolatedstntostn ( n : nat ) : ( isolated ( stn n ) ) ≃ ( stn n ) .
Proof . intro . apply weqpr1 . intro x .   apply iscontraprop1 .  apply ( isapropisisolated ) . set ( int := isdeceqstn n x  ) . assumption .  Defined .

Corollary isasetstn ( n : nat ) : isaset ( stn n ) .
Proof. intro . apply ( isasetifdeceq _ ( isdeceqstn n ) ) . Defined .

Definition stnset n := hSetpair (stn n) (isasetstn n).

Definition stn_to_nat n : stnset n -> natset := pr1.

Definition stnposet ( n : nat ) : Poset .
Proof.
  intro.
  unfold Poset.
  exists (_,,isasetstn n).
  unfold PartialOrder.
  exists (λ i j:stn n, i ≤ j)%dnat.
  unfold isPartialOrder.
  split.
  - unfold ispreorder.
    split.
    * intros i j k. refine istransnatleh.
    * intros i. apply isreflnatleh.
  - intros i j r s. apply (invmaponpathsincl _ ( isinclstntonat _ )).
    now apply isantisymmnatleh.
Defined.

Definition lastelement {n} : stn (S n) .
Proof. intro .   split with n .  apply ( natgthsnn n ) .  Defined .

Lemma lastelement_ge {n} : ∏ i : stn (S n), @lastelement n ≥ i.
Proof.
  intros. apply natlthsntoleh. unfold lastelement. apply stnlt.
Defined.

Definition firstelement {n} : stn(S n).
Proof. intro. exists 0. apply natgthsn0. Defined.

Lemma firstelement_le {n} : ∏ i : stn (S n), @firstelement n ≤ i.
Proof.
  reflexivity.
Defined.

Definition firstValue {X n} : (stn (S n) -> X) -> X
  := λ x, x firstelement.

Definition lastValue {X n} : (stn (S n) -> X) -> X
  := λ x, x lastelement.

(** Dual of i in stn n, is n - 1 - i *)
Local Lemma dualelement_0_empty {n : nat} (i : stn n) (e : 0 = n) : empty.
Proof.
  intros n i e. induction e. apply (negnatlthn0 _ (stnlt i)).
Qed.

Local Lemma dualelement_lt (i n : nat) (H : n > 0) : n - 1 - i < n.
Proof.
  intros i n H.
  rewrite natminusminus.
  apply (natminuslthn _ _ H).
  apply idpath.
Qed.

Definition dualelement {n : nat} (i : stn n) : stn n.
Proof.
  intros n i.
  induction (natchoice0 n) as [H | H].
  - exact (stnpair n (n - 1 - i) (fromempty (dualelement_0_empty i H))).
  - exact (stnpair n (n - 1 - i) (dualelement_lt i n H)).
Defined.

Definition stnmtostnn ( m n : nat ) (isnatleh: natleh m n ) : stn m -> stn n := λ x : stn m, match x with tpair _ i is => stnpair _ i ( natlthlehtrans i m n is isnatleh ) end .

Definition stn_left m n : stn m -> stn (m+n).
Proof.
  intros ? ? i. exists (pr1 i). apply (natlthlehtrans (pr1 i) m (m+n) (pr2 i)). apply natlehnplusnm.
Defined.

Definition stn_right m n : stn n -> stn (m+n).
  intros ? ? i. exists (m+pr1 i). apply natlthandplusl. exact (pr2 i).
Defined.

Definition stn_left_compute m n (i:stn m) : pr1 (stn_left m n i) = i.
  intros. reflexivity.
Defined.

Definition stn_right_compute m n (i:stn n) : pr1 (stn_right m n i) = m+i.
  intros. reflexivity.
Defined.

Lemma stn_left_0 {m i} (e:m=m+0) : stn_left m 0 i = transportf stn e i.
Proof.
  intros. apply subtypeEquality_prop. induction e. reflexivity.
Defined.

Definition stn_left' m n : m ≤ n -> stn m -> stn n.
Proof.
  intros ? ? le i.
  exact (stnpair _ _ (natlthlehtrans _ _ _ (stnlt i) le)).
Defined.

Definition stn_left'' {m n} : m < n -> stn m -> stn n.
Proof.
  intros ? ? le i.
  exact (stnpair _ _ (istransnatlth _ _ _ (stnlt i) le)).
Defined.

Lemma stn_left_compare m n (r : m ≤ m+n) : stn_left' m (m+n) r = stn_left m n.
Proof.
  intros.
  apply funextfun; intro i.
  now apply subtypeEquality_prop.
Defined.

(** ** "Boundary" maps [ dni : stn n -> stn ( S n ) ] and their properties . *)

Definition dni {n} ( i : stn ( S n ) ) : stn n -> stn ( S n ) .
Proof. intros n i x . exists (di i x). unfold di.
       induction (natlthorgeh x i) as [lt|ge].
       - apply natgthtogths. exact (pr2 x).
       - exact (pr2 x).
Defined.

Definition compute_pr1_dni_last n (i:stn n) : pr1 (dni lastelement i) = pr1 i.
Proof.
  intros. unfold dni,di; simpl. induction (natlthorgeh i n) as [q|q].
  - reflexivity.
  - contradicts (pr2 i) (natlehneggth q).
Defined.

Definition compute_pr1_dni_first n (i:stn n) : pr1 (dni firstelement i) = S (pr1 i).
Proof.
  reflexivity.
Defined.

Lemma dni_last {n} (i:stn n) : pr1 (dni lastelement i) = i.
Proof.
  intros. induction i as [i I]. unfold dni,di. simpl. induction (natlthorgeh i n) as [g|g].
  { reflexivity. }
  simpl. contradicts (natlehtonegnatgth _ _ g) I.
Defined.

Lemma dni_first {n} (i:stn n) : pr1 (dni firstelement i) = S i.
Proof.
  reflexivity.
Defined.

Definition dni_firstelement {n} : stn n -> stn (S n).
(* this definition is simpler than that of [dni n (firstelement n)], since no choice is involved, so it's useful in special situations *)
Proof. intros ? h. exact (S (pr1 h),, pr2 h). Defined.

Definition replace_dni_first n : dni (@firstelement n) = dni_firstelement.
Proof. intros. apply funextfun; intros i. apply subtypeEquality_prop. exact (compute_pr1_dni_first n i). Defined.

Definition dni_lastelement {n} : stn n -> stn (S n).
(* this definition is simpler than that of [dni lastelement], since no choice is involved, so it's useful in special situations *)
Proof.
  intros ? h. exists (pr1 h). exact (natlthtolths _ _ (pr2 h)).
Defined.

Definition replace_dni_last n : dni (@lastelement n) = dni_lastelement.
Proof.
  intros. apply funextfun; intros i. apply subtypeEquality_prop. exact (compute_pr1_dni_last n i).
Defined.

Lemma dni_lastelement_ord {n} : ∏ i j:stn n, i≤j -> dni_lastelement i ≤ dni_lastelement j.
Proof.
  intros ? ? ? e. exact e.
Defined.

Definition pr1_dni_lastelement {n} {i:stn n} : pr1 (dni_lastelement i) = pr1 i.
Proof. reflexivity. Defined.

Lemma dni_last_lt {n} (j : ⟦ n ⟧) : dni lastelement j < @lastelement n.
Proof.
  intros. induction j as [j J]. simpl. unfold di. induction (natlthorgeh j n) as [L|M].
  - exact J.
  - apply fromempty. exact (natlthtonegnatgeh _ _ J M).
Defined.

Lemma dnicommsq ( n : nat ) ( i : stn ( S n ) ) : commsqstr( dni i )  ( stntonat ( S n ) ) ( stntonat n ) ( di i )  .
Proof. intros . intro x . unfold dni . unfold di . destruct ( natlthorgeh x i ) .  simpl .  apply idpath . simpl .  apply idpath . Defined .

Theorem dnihfsq ( n : nat ) ( i : stn ( S n ) ) : hfsqstr ( di i ) ( stntonat ( S n ) ) ( stntonat n ) ( dni i ) .
Proof. intros . apply ( ishfsqweqhfibersgtof' ( di i ) ( stntonat ( S n ) ) ( stntonat n ) ( dni i ) ( dnicommsq _ _  ) ) . intro x . destruct ( natlthorgeh x n ) as [ g | l ] .

assert ( is1 : iscontr ( hfiber ( stntonat n ) x ) ) . apply iscontrhfiberstntonat . assumption .
assert ( is2 : iscontr ( hfiber ( stntonat ( S n ) ) ( di i x )  ) ) .    apply iscontrhfiberstntonat . apply ( natlehlthtrans _ ( S x ) ( S n ) ( natlehdinsn i x ) g ) .
apply isweqcontrcontr . assumption . assumption .

assert ( is1 : neg ( hfiber ( stntonat ( S n ) ) ( di i x ) ) ) . apply neghfiberstntonat . unfold di .   destruct ( natlthorgeh x i ) as [ l'' | g' ] .  destruct ( natgehchoice2 _ _ l ) as [ g' | e ] .   apply g' .  rewrite e in l'' .  assert ( int := natlthtolehsn _ _ l'' ) . contradicts (natgthnegleh (pr2 i)) int. apply l .  apply ( isweqtoempty2 _ is1 ) .
Defined .

Lemma dni_neq_i {n} i j : i ≠ @dni n i j.
Proof.
  intros. simpl. apply di_neq_i.
Defined.

Lemma weqhfiberdnihfiberdi ( n : nat ) ( i j : stn ( S n ) ) : ( hfiber ( dni i ) j ) ≃ ( hfiber ( di i ) j ) .
Proof.  intros . apply ( weqhfibersg'tof _ _ _ _ ( dnihfsq n i ) j ) . Defined .

Lemma neghfiberdni ( n : nat ) ( i : stn ( S n ) ) : ¬ ( hfiber ( dni i ) i ) .
Proof. intros . apply ( negf ( weqhfiberdnihfiberdi n i i ) ( neghfiberdi i ) ) . Defined .

Lemma iscontrhfiberdni ( n : nat ) ( i j : stn ( S n ) ) : i ≠ j -> iscontr ( hfiber ( dni i ) j ) .
Proof . intros ? ? ? ne . exact ( iscontrweqb ( weqhfiberdnihfiberdi n i j ) ( iscontrhfiberdi i j ne ) ) . Defined .

Lemma isdecincldni ( n : nat ) ( i : stn ( S n ) ) : isdecincl ( dni i ) .
Proof.  intros . intro j . induction ( stn_eq_or_neq i j ) as [eq|ne].
        - induction eq. apply ( isdecpropfromneg ( neghfiberdni n i ) ) .
        - apply ( isdecpropfromiscontr (iscontrhfiberdni _ _ _ ne) ) .
Defined .

Lemma isincldni ( n : nat ) ( i : stn ( S n ) ) : isincl ( dni i ) .
Proof. intros . apply ( isdecincltoisincl _  ( isdecincldni n i ) ) .  Defined .

(** ** The order-preserving functions [ sni n i : stn (S n) -> stn n ] that take the value [i] twice. *)

Definition sni {n} ( i : stn n ) : stn n <- stn ( S n ) .
Proof.
  intros ? ? j. exists (si i j). unfold si. induction (natlthorgeh i j) as [lt|ge].
  - induction j as [j J]. induction i as [i I]. simpl.
    induction j as [|j _].
    + contradicts (negnatlthn0 i) lt.
    + change (S j - 1 < n).
      change (S j) with (1 + j).
      rewrite natpluscomm.
      rewrite plusminusnmm.
      exact J.
  - induction i as [i I].
    exact (natlehlthtrans _ _ _ ge I).
Defined.

(** ** Weak equivalences between standard finite sets and constructions on these sets *)



(** *** The weak equivalence from [ stn n ] to the complement of a point [ j ] in [ stn ( S n ) ] defined by [ dni j ] *)

Definition stn_compl {n} (i:stn n) := compl_ne _ i (stnneq i).

Definition dnitocompl ( n : nat ) ( i : stn ( S n ) ) : stn n -> stn_compl i.
Proof. intros ? ? j. exists ( dni i j ) . apply dni_neq_i. Defined.

Lemma isweqdnitocompl  ( n : nat ) ( i : stn ( S n ) ) : isweq ( dnitocompl n i ) .
Proof.
  intros ? ? jni.
  assert ( w := samehfibers ( dnitocompl n i )  _ ( isinclpr1compl_ne _ i _ ) jni ) ; simpl in w .
  apply (iscontrweqb w). apply iscontrhfiberdni. exact (pr2 jni).
Defined.

Definition weqdnicompl {n} (i:stn(S n)): stn n ≃ stn_compl i.
Proof.
  intros.
  set (w := weqdicompl (stntonat _ i)).
  assert (eq : ∏ j, j < n <-> pr1 (w j) < S n).
  { simpl in w. intros j. unfold w.
    change (pr1 ((weqdicompl i) j)) with (di (stntonat _ i) j).
    unfold di.
    induction (natlthorgeh j i) as [lt|ge].
    - split.
      + apply natlthtolths.
      + intros _. exact (natlehlthtrans (S j) i (S n) lt (pr2 i)).
    - split; exact (idfun _). }
  refine (_ ∘ (weq_subtypes w (λ j, j < n) (λ j, pr1 j < S n) eq))%weq.
  refine (weqtotal2comm12 _ _).
Defined.

Definition weqdnicompl_compute {n} (j:stn (S n)) (i:stn n) : pr1 (weqdnicompl j i) = dni j i.
Proof.
  intros. apply subtypeEquality_prop. reflexivity.
Defined.

(** *** Weak equivalence from [ coprod ( stn n ) unit ] to [ stn ( S n ) ] defined by [ dni i ] *)

Definition weqdnicoprod_provisional n (j : stn(S n)) : stn n ⨿ unit ≃ stn (S n).
Proof.
  intros.
  apply (weqcomp (weqcoprodf (weqdnicompl j) (idweq unit))
                 (weqrecompl_ne (stn (S n)) j (isdeceqstn (S n) j) (stnneq j))).
Defined.

Opaque weqdnicoprod_provisional.

Definition weqdnicoprod_map {n} (j : stn(S n)) : stn n ⨿ unit -> stn (S n).
  intros n j x. induction x as [i|t].
    { exact (dni j i). }
    { exact j. }
Defined.

Definition weqdnicoprod_compute {n} (j : stn(S n)) : weqdnicoprod_provisional n j ~ weqdnicoprod_map j.
Proof.
  intros.
  intros i.
  induction i as [i|i].
  - apply subtypeEquality_prop. now induction i as [i I].
  - reflexivity.
Defined.

Definition weqdnicoprod n (j : stn(S n)) : stn n ⨿ unit ≃ stn (S n).
Proof.
  intros.
  apply (weqpair (weqdnicoprod_map j)).
  apply (isweqhomot _ _ (weqdnicoprod_compute _)).
  apply weqproperty.
Defined.

Definition weqoverdnicoprod {n} (P:⟦S n⟧→UU) :
  (∑ i, P i) ≃ (∑ j, P(dni lastelement j)) ⨿ P lastelement.
Proof.
  intros.
  simple refine (weqcomp (weqtotal2overcoprod' P (weqdnicoprod n lastelement)) _).
  apply weqcoprodf.
  - apply idweq.
  - apply weqtotal2overunit.
Defined.

Lemma weqoverdnicoprod_eq1 {n} (P:⟦S n⟧→UU) j p :
  invmap (weqoverdnicoprod P) (ii1 (j,,p)) = ( dni lastelement j ,, p ).
Proof.
  intros. simpl in p. reflexivity.
Defined.

Lemma weqoverdnicoprod_eq1' {n} (P:⟦S n⟧→UU) jp :
  invmap (weqoverdnicoprod P) (ii1 jp) = (total2_base_map (dni lastelement) jp).
Proof.
  intros. induction jp. reflexivity.
Defined.

Lemma weqoverdnicoprod_eq2 {n} (P:⟦S n⟧→UU) p :
  invmap (weqoverdnicoprod P) (ii2 p) = (lastelement ,, p ).
Proof.
  intros. reflexivity.
Defined.

Definition weqdnicoprod_invmap {n} (j : stn(S n)) : stn n ⨿ unit <- stn (S n).
  (* perhaps use this to improve weqdnicoprod *)
  intros n j i.
  induction (isdeceqstn (S n) i j) as [eq|ne].
  { exact (ii2 tt). }
  { apply ii1. induction i as [i I]. induction j as [j J].
    choose (i < j)%dnat a a.
    { exists i. exact (natltltSlt _ _ _ a J). }
    { exists (i - 1).
      induction (natlehchoice _ _ (negnatgthtoleh a)) as [b|b].
      { induction (natlehchoice4 _ _ I) as [c|c].
        { apply (natlehlthtrans (i - 1) i n).
          { apply natminuslehn. }
          { exact c. } }
        { induction c. apply natminuslthn.
          { apply (natlehlthtrans _ j _).
            { apply natleh0n. }
            { exact b. } }
          { apply natlthnsn. } } }
      { induction b.
        induction (ne (@subtypeEquality_prop _ _ (stnpair _ j I) (stnpair _ j J) (idpath j))). } } }
Defined.

(** *** Weak equivalences from [ stn n ] for [ n = 0 , 1 , 2 ] to [ empty ] , [ unit ] and [ bool ] ( see also the section on [ nelstruct ] in finitesets.v ) . *)

Definition negstn0 : neg ( stn 0 ) .
Proof . intro x .  destruct x as [ a b ] .  apply ( negnatlthn0 _ b ) . Defined .

Definition weqstn0toempty : weq ( stn 0 ) empty .
Proof .  apply weqtoempty . apply negstn0 . Defined .

Definition weqstn1tounit : weq ( stn 1 ) unit .
Proof. set ( f := λ x : stn 1, tt ) . apply weqcontrcontr .  split with lastelement .   intro t .  destruct t as [ t l ] . set ( e := natlth1tois0 _ l ) .   apply ( invmaponpathsincl _ ( isinclstntonat 1 ) ( stnpair _ t l ) lastelement e ) .  apply iscontrunit .  Defined .

Corollary iscontrstn1 : iscontr ( stn 1 ) .
Proof. apply iscontrifweqtounit . apply weqstn1tounit . Defined .

Corollary isconnectedstn1 : ∏ i1 i2 : stn 1, i1 = i2.
Proof.
  intros i1 i2.
  apply (invmaponpathsweq weqstn1tounit).
  apply isconnectedunit.
Defined.

Lemma isinclfromstn1 { X : UU } ( f : stn 1 -> X ) ( is : isaset X ) : isincl f .
Proof. intros . apply ( isinclbetweensets f ( isasetstn 1 ) is ) . intros x x' e . apply ( invmaponpathsweq weqstn1tounit x x' ( idpath tt ) )  .  Defined .

Definition weqstn2tobool : weq ( stn 2 ) bool .
Proof. set ( f := λ j : stn 2, match ( isdeceqnat j 0 ) with ii1 _ => false | ii2 _ => true end ) . set ( g := λ b : bool, match b with false => stnpair 2 0 ( idpath true ) | true => stnpair 2 1 ( idpath true ) end ) .  split with f .
assert ( egf : ∏ j : _ , paths ( g ( f j ) ) j ) . intro j . unfold f .  destruct ( isdeceqnat j 0 ) as [ e | ne ] .  apply ( invmaponpathsincl _ ( isinclstntonat 2 ) ) . rewrite e .   apply idpath .  apply ( invmaponpathsincl _ ( isinclstntonat 2 ) ) . destruct j as [ j l ] . simpl . set ( l' := natlthtolehsn _ _ l ) .  destruct ( natlehchoice _ _ l' ) as [ l'' | e ] . simpl in ne . destruct  ( ne ( natlth1tois0 _ l'' ) ) .  apply ( pathsinv0 ( invmaponpathsS _ _ e ) ) .
assert ( efg : ∏ b : _ , paths ( f ( g b ) ) b ) . intro b .  unfold g .  destruct b . apply idpath . apply idpath.
apply ( gradth _ _ egf efg ) . Defined .

Lemma isinjstntonat n : isInjectiveFunction (pr1 : stnset n -> natset).
Proof. intros ? i j. apply subtypeEquality_prop. Defined.

(** ***  Weak equivalence between the coproduct of [ stn n ] and [ stn m ] and [ stn ( n + m ) ] *)

Definition weqfromcoprodofstn_invmap (n m : nat) : (stn (n + m)) -> ((stn n) ⨿ (stn m)).
Proof.
  intros n m i.
  induction (natlthorgeh i n) as [i1 | i2].
  - exact (ii1 (stnpair n i i1)).
  - exact (ii2 (stnpair m (i - n) (nat_split (pr2 i) i2))).
Defined.

Lemma weqfromcoprodofstn_invmap_r0 n (i : stn (n+0)) :
  weqfromcoprodofstn_invmap n 0 i = ii1 (transportf stn (natplusr0 n) i).
Proof.
  intros.
  unfold weqfromcoprodofstn_invmap.
  simpl.
  induction (natlthorgeh i n) as [I|J].
  - simpl. apply maponpaths. apply subtypeEquality_prop. simpl.
    induction (natplusr0 n). reflexivity.
  - simpl. apply fromempty. induction (! natplusr0 n).
    exact (natgehtonegnatlth _ _ J (stnlt i)).
Defined.

Definition weqfromcoprodofstn_map (n m : nat) : ((stn n) ⨿ (stn m)) -> (stn (n + m)).
Proof.
  intros n m i.
  induction i as [i | i].
  - now apply stn_left.
  - now apply stn_right.
Defined.

Lemma weqfromcoprodofstn_eq1 (n m : nat) :
  ∏ x : stn n ⨿ stn m, weqfromcoprodofstn_invmap n m (weqfromcoprodofstn_map n m x) = x.
Proof.
  intros n m x.
  unfold weqfromcoprodofstn_map, weqfromcoprodofstn_invmap. unfold coprod_rect.
  induction x as [x | x].
  - induction (natlthorgeh (stn_left n m x) n) as [H | H].
    + apply maponpaths. apply isinjstntonat. apply idpath.
    + apply fromempty. apply (natlthtonegnatgeh x n (stnlt x) H).
  - induction (natlthorgeh (stn_right n m x) n) as [H | H].
    + apply fromempty.
      set (tmp := natlehlthtrans n (n + x) n (natlehnplusnm n x) H).
      use (isirrefl_natneq n (natlthtoneq _ _ tmp)).
    + apply maponpaths. apply isinjstntonat. cbn. rewrite natpluscomm. apply plusminusnmm.
Qed.

Lemma weqfromcoprodofstn_eq2 (n m : nat) :
  ∏ y : stn (n + m), weqfromcoprodofstn_map n m (weqfromcoprodofstn_invmap n m y) = y.
Proof.
  intros n m x.
  unfold weqfromcoprodofstn_map, weqfromcoprodofstn_invmap. unfold coprod_rect.
  induction (natlthorgeh x n) as [H | H].
  - apply isinjstntonat. apply idpath.
  - induction (natchoice0 m) as [H1 | H1].
    + apply fromempty. induction H1. induction (! (natplusr0 n)).
      use (natlthtonegnatgeh x n (stnlt x) H).
    + apply isinjstntonat. cbn. rewrite natpluscomm. apply minusplusnmm. apply H.
Qed.

(** A proof of weqfromcoprodofstn using gradth *)
Theorem weqfromcoprodofstn (n m : nat) : weq ((stn n) ⨿ (stn m )) (stn (n + m)).
Proof.
  intros n m.
  use (tpair _ (weqfromcoprodofstn_map n m)).
  use (gradth _ (weqfromcoprodofstn_invmap n m)).
  - exact (weqfromcoprodofstn_eq1 n m).
  - exact (weqfromcoprodofstn_eq2 n m).
Defined.

(** Associativity of [weqfromcoprodofstn] *)

Definition pr1_eqweqmap m n (e:m=n) (i:stn m) : pr1 (pr1weq (eqweqmap (maponpaths stn e)) i) = pr1 i.
Proof. intros. induction e. reflexivity. Defined.

Definition coprod_stn_assoc l m n : (
  eqweqmap (maponpaths stn (natplusassoc l m n))
           ∘ weqfromcoprodofstn (l+m) n
           ∘ weqcoprodf (weqfromcoprodofstn l m) (idweq _)
  ~
  weqfromcoprodofstn l (m+n)
           ∘ weqcoprodf (idweq _) (weqfromcoprodofstn m n)
           ∘ weqcoprodasstor _ _ _
  ) %weq.
Proof.
  intros.
  intros abc.
  rewrite 4? weqcomp_to_funcomp.
  apply (invmaponpathsincl pr1). apply isinclstntonat.
  rewrite <- funcomp_assoc. unfold funcomp at 1. rewrite pr1_eqweqmap.
  induction abc as [[a|b]|c].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. apply natplusassoc.
Defined.

(** *** Weak equivalence from the total space of a family [ stn ( f x ) ]  over [ stn n ] to [ stn ( stnsum n f ) ] *)

Definition stnsum {n : nat} (f : stn n -> nat) : nat.
Proof.
  intro n. induction n as [ | n IHn].
  - intro. exact 0.
  - intro f. exact (IHn (λ i, f (dni lastelement i)) + f lastelement).
Defined.

Lemma stnsum_step {n} (f:stn (S n) -> nat) : stnsum f = stnsum (f ∘ (dni lastelement)) + f lastelement.
Proof.
  intros. reflexivity.
Defined.

Lemma stnsum_eq {n} (f g:stn n->nat) : f ~ g -> stnsum f = stnsum g.
Proof.
  intros ? ? ? h. induction n as [|n IH].
  { reflexivity. }
  rewrite 2? stnsum_step. induction (h lastelement).
  apply (maponpaths (λ i, i + f lastelement)). apply IH. intro x. apply h.
Defined.

Lemma transport_stnsum {m n} (e:m=n) (g:stn n->nat) :
  stnsum g = stnsum (λ i, g(transportf stn e i)).
Proof. intros. induction e. reflexivity. Defined.

Lemma stnsum_le {n} (f g:stn n->nat) : (∏ i, f i ≤ g i) -> stnsum f ≤ stnsum g.
Proof.
  intros ? ? ? le. induction n as [|n IH]. { simpl. reflexivity. }
  apply natlehandplus. { apply IH. intro i. apply le. } apply le.
Defined.

Lemma transport_stn {m n} (e:m=n) (i:stn m) :
  transportf stn e i = stnpair n (pr1 i) (transportf (λ k, pr1 i < k) e (pr2 i)).
Proof.
  intros. induction e. apply subtypeEquality_prop. reflexivity.
Defined.

Lemma stnsum_left_right m n (f:stn(m+n)->nat) :
  stnsum f = stnsum (f ∘ stn_left m n) + stnsum (f ∘ stn_right m n).
Proof.
  (* why is this proof so obnoxious and fragile? *)
  intros. induction n as [|n IHn].
  { change (stnsum _) with 0 at 3. rewrite natplusr0.
    assert (e := ! natplusr0 m).
    rewrite (transport_stnsum e). apply stnsum_eq; intro i. unfold funcomp.
    apply maponpaths. apply pathsinv0. apply stn_left_0. }
  rewrite stnsum_step. assert (e : S (m+n) = m + S n).
  { apply pathsinv0. apply natplusnsm. }
  rewrite (transport_stnsum e).
  rewrite stnsum_step. rewrite <- natplusassoc. apply map_on_two_paths.
  { rewrite IHn; clear IHn. apply map_on_two_paths.
    { apply stnsum_eq; intro i. unfold funcomp. apply maponpaths. apply subtypeEquality_prop.
      rewrite stn_left_compute. induction e. rewrite idpath_transportf. rewrite dni_last.
      reflexivity. }
    { apply stnsum_eq; intro i. unfold funcomp. apply maponpaths. apply subtypeEquality_prop.
      rewrite stn_right_compute. unfold stntonat. induction e.
      rewrite idpath_transportf. rewrite 2? dni_last. reflexivity. } }
  unfold funcomp. apply maponpaths. apply subtypeEquality_prop. induction e. reflexivity.
Defined.

Corollary stnsum_left_le m n (f:stn(m+n)->nat) : stnsum (f ∘ stn_left m n) ≤ stnsum f.
Proof.
  intros. rewrite stnsum_left_right. apply natlehnplusnm.
Defined.

Corollary stnsum_left_le' {m n} (f:stn n->nat) (r:m≤n) : stnsum (f ∘ stn_left' m n r) ≤ stnsum f.
Proof.
  intros. assert (s := minusplusnmm n m r). rewrite (natpluscomm (n-m) m) in s.
  generalize r f; clear r f. rewrite <- s; clear s.
  set (k := n-m). generalize k; clear k; intros k r f.
  induction (natpluscomm m k). rewrite stn_left_compare. rewrite stnsum_left_right.
  apply natlehnplusnm.
Defined.

Lemma stnsum_dni {n} (f:stn (S n)->nat) (j:stn (S n)) : stnsum f = stnsum (f ∘ dni j) + f j.
Proof.
  intros.
  induction j as [j J].
  assert (e2 : j + (n - j) = n).
  { rewrite natpluscomm. apply minusplusnmm. apply natlthsntoleh. exact J. }
  assert (e : (S j) + (n - j) = S n).
  { change (S j + (n - j)) with (S (j + (n - j))). apply maponpaths. exact e2. }
  intermediate_path (stnsum (λ i, f (transportf stn e i))).
  { apply (transport_stnsum e). }
  rewrite (stnsum_left_right (S j) (n - j)); unfold funcomp.
  apply pathsinv0. rewrite (transport_stnsum e2). rewrite (stnsum_left_right j (n-j)); unfold funcomp.
  rewrite (stnsum_step (λ x, f (transportf stn e _))); unfold funcomp. apply pathsinv0.
  rewrite natplusassoc. rewrite (natpluscomm (f _)). rewrite <- natplusassoc.
  apply map_on_two_paths.
  { apply map_on_two_paths.
    { apply stnsum_eq; intro i. induction i as [i I]. apply maponpaths. apply subtypeEquality_prop.
      induction e. rewrite idpath_transportf. rewrite stn_left_compute. unfold dni,di, stntonat; simpl.
      induction (natlthorgeh i j) as [R|R].
      { unfold stntonat; simpl; repeat rewrite transport_stn; simpl.
        induction (natlthorgeh i j) as [a|b]. { simpl. reflexivity. } { simpl. contradicts R (natlehneggth b). }}
      { unfold stntonat; simpl; repeat rewrite transport_stn; simpl.
        induction (natlthorgeh i j) as [V|V]. { simpl. contradicts I (natlehneggth R). } { simpl. reflexivity. }}}
    { apply stnsum_eq; intro i. induction i as [i I]. apply maponpaths.
      unfold dni,di, stn_right, stntonat; repeat rewrite transport_stn; simpl.
      induction (natlthorgeh (j+i) j) as [X|X].
      { contradicts (negnatlthplusnmn j i) X. }
      { apply subtypeEquality_prop. simpl. reflexivity. }}}
  apply maponpaths. rewrite transport_stn; simpl. apply subtypeEquality_prop. reflexivity.
Defined.

Lemma stnsum_pos {n} (f:stn n->nat) (j:stn n) : f j ≤ stnsum f.
Proof.
  intros ? ? j.
  assert (m : 0 < n).
  { apply (natlehlthtrans _ j). { apply natleh0n. } exact (pr2 j). }
  assert (l : 1 ≤ n). { now apply natlthtolehsn. }
  assert (e : n = S (n - 1)).
  { change (S (n - 1)) with (1 + (n - 1)). rewrite natpluscomm.
    apply pathsinv0. now apply minusplusnmm. }
  rewrite (transport_stnsum (!e) f).
  rewrite (stnsum_dni _ (transportf stn e j)).
  unfold funcomp.
  generalize (stnsum (λ x, f (transportf stn (! e) (dni (transportf stn e j) x)))); intro s.
  induction e. apply natlehmplusnm.
Defined.

Corollary stnsum_pos_0 {n} (f:stn (S n)->nat) : f firstelement ≤ stnsum f.
Proof. intros. exact (stnsum_pos f firstelement). Defined.

Lemma stnsum_1 n : stnsum(λ i:stn n, 1) = n.
Proof.
  intros.
  induction n as [|n IH].
  { reflexivity. }
  simpl.
  simple refine (natpluscomm _ _ @ _).
  apply maponpaths.
  exact IH.
Defined.

Lemma stnsum_const {m c} : stnsum (λ i:⟦m⟧, c) = m*c.
Proof.
  intros.
  induction m as [|m I].
  - reflexivity.
  - exact (maponpaths (λ i, i+c) I).
Defined.

Lemma stnsum_last_le {n} (f:stn (S n) -> nat) : f lastelement ≤ stnsum f.
Proof.
  intros. rewrite stnsum_step. apply natlehmplusnm.
Defined.

Lemma stnsum_first_le {n} (f:stn (S n) -> nat) : f firstelement ≤ stnsum f.
Proof.
  intros. induction n as [|n IH].
  { apply isreflnatleh. }
  rewrite stnsum_step. assert (W := IH (f ∘ dni lastelement)).
  change ((f ∘ dni lastelement) firstelement) with (f firstelement) in W.
  apply (istransnatleh W); clear W. apply natlehnplusnm.
Defined.

Lemma _c_ {n} {m:⟦ n ⟧ → nat} (ij : ∑ i : ⟦ n ⟧, ⟦ m i ⟧) :
  stnsum (m ∘ stn_left'' (stnlt (pr1 ij))) + pr2 ij < stnsum m.
Proof.
  intros.
  set (m1 := m ∘ stn_left'' (stnlt (pr1 ij))).
  induction ij as [i j].
  induction i as [i I].
  induction j as [j J].
  simpl in m1.
  change (stnsum m1 + j < stnsum m).
  assert (s := stnsum_left_le' m (I : S i ≤ n)).
  simple refine (natlthlehtrans _ _ _ _ s).
  clear s.
  induction n as [|n _].
  { induction (negnatlthn0 _ I). }
  assert (t : stnsum m1 + j < stnsum m1 + m (i,,I)).
  { apply natlthandplusl. exact J. }
  apply (natlthlehtrans _ _ _ t).
  assert (K : ∏ m n, m = n -> m ≤ n).
  { intros a b e. induction e. apply isreflnatleh. }
  apply K; clear K.
  rewrite stnsum_step.
  clear j J t.
  unfold m1 ; clear m1.
  apply two_arg_paths.
  + apply stnsum_eq. intro l.
    unfold funcomp. apply maponpaths.
    apply subtypeEquality_prop; simpl.
    apply pathsinv0, di_eq1, stnlt.
  + unfold funcomp. apply maponpaths. apply subtypeEquality_prop. simpl. reflexivity.
Defined.

Local Definition weqstnsum_map { n : nat } (m : stn n -> nat) : (∑ i, stn (m i)) -> stn (stnsum m).
Proof.
  intros ? ? ij.
  exact (stnpair _ (stnsum (m ∘ stn_left'' (stnlt (pr1 ij))) + pr2 ij) (_c_ ij)).
Defined.

Local Definition weqstnsum_invmap {n : nat} (m : stn n -> nat) : stn (stnsum m) -> (∑ i, stn (m i)).
Proof.
  intros ?.
  induction n as [|n IH].
  { intros ? l. now apply fromempty, negstn0. }
  intros ? l.
  change (⟦ stnsum (m ∘ dni lastelement) + m lastelement ⟧) in l.
  (* we are careful to use weqfromcoprodofstn_invmap both here and in concatenate' *)
  assert (ls := weqfromcoprodofstn_invmap _ _ l).
  induction ls as [j|k].
  - exact (total2_base_map (dni lastelement) (IH _ j)).
  - exact (lastelement,,k).
Defined.

Definition weqstnsum_invmap_step1 {n} (f : stn (S n) -> nat)
           (j : stn (stnsum (λ x, f (dni lastelement x)))) :
  weqstnsum_invmap f (weqfromcoprodofstn_map (stnsum (λ x, f (dni lastelement x))) (f lastelement) (ii1 j))
  =
  total2_base_map (dni lastelement) (weqstnsum_invmap (f ∘ dni lastelement) j).
Proof.
  intros. unfold weqstnsum_invmap at 1. unfold nat_rect at 1.
  rewrite weqfromcoprodofstn_eq1. reflexivity.
Defined.

Definition weqstnsum_invmap_step2 {n} (f : stn (S n) -> nat)
           (k : stn (f lastelement)) :
  weqstnsum_invmap f (weqfromcoprodofstn_map (stnsum (λ x, f (dni lastelement x))) (f lastelement) (ii2 k))
  =
  (lastelement,,k).
Proof.
  intros. unfold weqstnsum_invmap at 1. unfold nat_rect at 1.
  rewrite weqfromcoprodofstn_eq1. reflexivity.
Defined.

Lemma partial_sum_prop {n : nat} {m : stn n → nat} l : l < stnsum m  ->
  isaprop (∑ (i:stn n) (j:stn(m i)), stnsum (m ∘ stn_left'' (stnlt i)) + j = l).
Proof.
Admitted.

Lemma partial_sum_slot {n : nat} {m : stn n → nat} l : l < stnsum m  ->
  ∃! (i:stn n) (j:stn(m i)), stnsum (m ∘ stn_left'' (stnlt i)) + j = l.
Proof.
  intros ? ? ? lt.
  set (len := stnsum m).
  induction n as [|n IH].
  { apply fromempty. change (hProptoType(l < 0)) in lt. exact (negnatlthn0 _ lt). }
  set (m' := m ∘ dni_lastelement).
  set (len' := stnsum m').
  induction (natlthorgeh l len') as [I|J].
  - assert (IH' := IH m' I); clear IH.
    induction IH' as [ijJ Q]. induction ijJ as [i jJ]. induction jJ as [j J].
    use tpair.
    + exists (dni_lastelement i). exists j.
      abstract (simple refine (_ @ J); apply (maponpaths (λ x, x+j)); apply stnsum_eq; intro r;
      unfold m'; unfold funcomp; apply maponpaths; now apply subtypeEquality_prop).
    + intro t. now apply partial_sum_prop.
  - clear IH. set (j := l - len').
    apply iscontraprop1.
    { now apply partial_sum_prop. }
    assert (K := minusplusnmm _ _ J). change (l-len') with j in K.
    exists lastelement.
    use tpair.
    * exists j. apply (natlthandpluslinv _ _ len'). rewrite natpluscomm.
      induction (!K); clear K J j.
      assert(C : len = len' + m lastelement).
      { simple refine (stnsum_step _ @ _). unfold len', m'; clear m' len'.
        rewrite replace_dni_last. reflexivity. }
      induction C. exact lt.
    * simpl. intermediate_path (stnsum m' + j).
      -- apply (maponpaths (λ x, x+j)). apply stnsum_eq; intro i.
         unfold m'. unfold funcomp. apply maponpaths. now apply subtypeEquality_prop.
      -- rewrite natpluscomm. exact (K).
Defined.

Lemma stn_right_first n i : stn_right i (S n) firstelement = stnpair (i + S n) i (natltplusS n i).
Proof.
  intros.
  apply subtypeEquality_prop.
  simpl.
  apply natplusr0.
Defined.

Lemma nat_rect_step (P : nat → UU) (p0 : P 0) (IH : ∏ n, P n → P (S n)) n :
  nat_rect P p0 IH (S n) = IH n (nat_rect P p0 IH n).
Proof.
  reflexivity.
Defined.

Definition weqstnsum1_prelim {n} (f : stn n -> nat) : (∑ i, stn (f i)) ≃ stn (stnsum f).
Proof.
  intros n.
  induction n as [ | n' IHn ].
  { intros f. apply weqempty.
    - exact (negstn0 ∘ pr1).
    - exact negstn0. }
  intros f. change (⟦ stnsum f ⟧) with (⟦ stnsum (f ∘ dni lastelement) + f lastelement ⟧).
  simple refine (weqcomp _ (weqfromcoprodofstn _ _)).
  simple refine (weqcomp (weqoverdnicoprod _) _).
  apply weqcoprodf1.
  apply IHn.
Defined.

Lemma weqstnsum1_step {n} (f : ⟦S n⟧ -> nat)
  : (
      weqstnsum1_prelim f
      =
      weqfromcoprodofstn (stnsum (funcomp (dni lastelement) f)) (f lastelement)
      ∘ (weqcoprodf1 (weqstnsum1_prelim (λ i, f (dni lastelement i)))
         ∘ weqoverdnicoprod (λ i, ⟦ f i ⟧))) % weq.
Proof.
  reflexivity.
Defined.

Lemma weqstnsum1_prelim_eq { n : nat } (f : stn n -> nat) : weqstnsum1_prelim f ~ weqstnsum_map f.
Proof.
  intros n.
  induction n as [|n I].
  - intros f ij. apply fromempty, negstn0. exact (pr1 ij).
  - intros f.
    rewrite weqstnsum1_step.
    intros ij.
    rewrite 2 weqcomp_to_funcomp_app.
    unfold weqcoprodf1.
    change (pr1weq (weqcoprodf (weqstnsum1_prelim (λ i, f (dni lastelement i)))
                               (idweq (⟦ f lastelement ⟧))))
    with (coprodf (weqstnsum1_prelim (λ i, f (dni lastelement i)))
                  (idfun (⟦ f lastelement ⟧))).
    intermediate_path
      ((weqfromcoprodofstn (stnsum (f ∘ dni lastelement)) (f lastelement))
         (coprodf (weqstnsum_map (λ i, f (dni lastelement i)))
                  (idfun (⟦ f lastelement ⟧)) ((weqoverdnicoprod (λ i, ⟦ f i ⟧)) ij))).
    + apply maponpaths.
      apply homotcoprodfhomot.
      * apply I.
      * intro x. reflexivity.
    + clear I.
      apply pathsinv0.
      generalize ij ; clear ij.
      apply (homotweqinv' (weqstnsum_map f)
                          (weqoverdnicoprod (λ i : ⟦ S n ⟧, ⟦ f i ⟧))
                          (λ c, pr1weq (weqfromcoprodofstn (stnsum (f ∘ dni lastelement)) (f lastelement))
                                       (coprodf (weqstnsum_map (λ i, f (dni lastelement i)))
                                                (idfun _) c))
            ).
      intros c.
      unfold funcomp.
      set (P := λ i, ⟦ f i ⟧).
      change (pr1weq (weqfromcoprodofstn (stnsum (λ x : ⟦ n ⟧, f (dni lastelement x))) (f lastelement)))
      with (weqfromcoprodofstn_map (stnsum (λ x : ⟦ n ⟧, f (dni lastelement x))) (f lastelement)).
      induction c as [jk|k].
      * unfold coprodf.
        induction jk as [j k].
        change (invmap (weqoverdnicoprod P) (ii1 (j,,k))) with (tpair P (dni lastelement j) k).
        unfold weqfromcoprodofstn_map. unfold coprod_rect. unfold weqstnsum_map.
        apply subtypeEquality_prop.
        induction k as [k K]. simpl.
        apply (maponpaths (λ x, x+k)). unfold funcomp. unfold stntonat. unfold di.
        clear K k.
        induction (natlthorgeh _ n) as [G|G'].
        -- simpl. apply stnsum_eq; intro k. apply maponpaths.
           apply subtypeEquality_prop. simpl.
           apply pathsinv0, di_eq1.
           exact (istransnatlth _ _ _ (stnlt k) G).
        -- apply fromempty. exact (natlthtonegnatgeh _ _ (stnlt j) G').
      * change (invmap (weqoverdnicoprod P) (ii2 k)) with (tpair P lastelement k).
        unfold coprodf, idfun. unfold weqfromcoprodofstn_map. unfold coprod_rect.
        unfold weqstnsum_map.
        apply subtypeEquality_prop.
        induction k as [k K]. simpl.
        apply (maponpaths (λ x, x+k)).
        apply maponpaths.
        apply funextfun; intro i. induction i as [i I].
        unfold funcomp. apply maponpaths.
        apply subtypeEquality_prop.
        simpl.
        now apply pathsinv0, di_eq1.
Defined.

Lemma weqstnsum1_prelim_eq' { n : nat } (f : stn n -> nat) : invweq (weqstnsum1_prelim f) ~ weqstnsum_invmap f.
Proof.
  intros n.
  induction n as [|n I].
  - intros f k. apply fromempty, negstn0. exact k.
  - intros f. rewrite weqstnsum1_step.
    intros k. rewrite 2 invweqcomp. rewrite 2 weqcomp_to_funcomp_app. rewrite 3 pr1_invweq.
    unfold weqcoprodf1.
    change (invmap (weqcoprodf (weqstnsum1_prelim (λ i, f (dni lastelement i))) (idweq (⟦ f lastelement ⟧))))
    with (coprodf (invweq (weqstnsum1_prelim (λ i, f (dni lastelement i)))) (idweq (⟦ f lastelement ⟧))).
    intermediate_path (invmap (weqoverdnicoprod (λ i : ⟦ S n ⟧, ⟦ f i ⟧))
                              (coprodf (weqstnsum_invmap (λ i : ⟦ n ⟧, f (dni lastelement i))) (idweq (⟦ f lastelement ⟧))
                                       (invmap (weqfromcoprodofstn (stnsum (f ∘ dni lastelement)) (f lastelement)) k))).
    + apply maponpaths.
      change (invmap _ k)
      with (invmap (weqfromcoprodofstn (stnsum (f ∘ dni lastelement)) (f lastelement)) k).
      generalize (invmap (weqfromcoprodofstn (stnsum (f ∘ dni lastelement)) (f lastelement)) k).
      intro c.
      apply homotcoprodfhomot.
      * apply I.
      * apply homotrefl.
    + clear I.
      generalize k; clear k.
      simple refine (homotweqinv
                (λ c, invmap (weqoverdnicoprod (λ i, ⟦ f i ⟧))
                             (coprodf (weqstnsum_invmap (λ i, f (dni lastelement i)))
                                      (idweq (⟦ f lastelement ⟧))
                                      c))
                (weqfromcoprodofstn (stnsum (f ∘ dni lastelement)) (f lastelement))
                _ _).
      unfold funcomp.
      intro c.
      induction c as [r|s].
      * unfold coprodf.
        change (pr1weq (weqfromcoprodofstn (stnsum (λ x, f (dni lastelement x))) (f lastelement)))
        with (weqfromcoprodofstn_map (stnsum (λ x, f (dni lastelement x))) (f lastelement)).
        set (P := (λ i : ⟦ S n ⟧, ⟦ f i ⟧)).
        rewrite weqstnsum_invmap_step1.
        change (λ i : ⟦ n ⟧, f (dni lastelement i)) with (f ∘ dni lastelement).
        generalize (weqstnsum_invmap (f ∘ dni lastelement) r); intro ij.
        induction ij as [i j].
        reflexivity.
      * unfold coprodf.
        change (pr1weq (idweq _) s) with s.
        set (P := (λ i : ⟦ S n ⟧, ⟦ f i ⟧)).
        change (pr1weq _)
        with (weqfromcoprodofstn_map (stnsum (λ x : ⟦ n ⟧, f (dni lastelement x))) (f lastelement)).
        rewrite weqstnsum_invmap_step2.
        reflexivity.
Defined.

Definition weqstnsum1 {n} (f : stn n -> nat) : (∑ i, stn (f i)) ≃ stn (stnsum f).
Proof.
  intros. simple refine (remakeweqboth (weqstnsum1_prelim_eq _) (weqstnsum1_prelim_eq' _)).
Defined.

Lemma weqstnsum1_eq {n} (f : stn n -> nat) : pr1weq (weqstnsum1 f) = weqstnsum_map f.
Proof.
  reflexivity.
Defined.

Lemma weqstnsum1_eq' {n} (f : stn n -> nat) : invmap (weqstnsum1 f) = weqstnsum_invmap f.
Proof.
  reflexivity.
Defined.

Theorem weqstnsum { n : nat } (P : stn n -> UU) (f : stn n -> nat) :
  (∏ i, stn (f i) ≃ P i) -> total2 P ≃ stn (stnsum f).
Proof.
  intros ? ? ? w.
  intermediate_weq (∑ i, stn (f i)).
  - apply invweq. now apply weqfibtototal.
  - apply weqstnsum1.
Defined.

Corollary weqstnsum2 { X : UU } {n} (f : stn n -> nat) (g : X -> stn n) :
  (∏ i, ⟦f i⟧ ≃ hfiber g i) -> X ≃ ⟦stnsum f⟧.
Proof.
  intros ? ? ? ? w.
  simple refine (weqcomp _ (weqstnsum _ _ w)).
  apply weqtococonusf.
Defined.

(** lexical enumeration of pairs of natural numbers *)

Definition lexicalEnumeration {n} (m:stn n->nat) := invweq (weqstnsum1 m) : stn (stnsum m) ≃ (∑ i : stn n, stn (m i)).

Definition inverse_lexicalEnumeration {n} (m:stn n->nat) := weqstnsum1 m : (∑ i : stn n, stn (m i)) ≃ stn (stnsum m).

(** two generalizations of stnsum, potentially useful *)

Definition foldleft {E} (e:E) (m:binop E) {n} (x:stn n -> E) : E.
Proof.
  intros.
  induction n as [|n foldleft].
  + exact e.
  + exact (m (foldleft (x ∘ (dni lastelement))) (x lastelement)).
Defined.

Definition foldright {E} (m:binop E) (e:E) {n} (x:stn n -> E) : E.
Proof.
  intros.
  induction n as [|n foldright].
  + exact e.
  + exact (m (x firstelement) (foldright (x ∘ dni firstelement))).
Defined.

(** *** Weak equivalence between the direct product of [ stn n ] and [ stn m ] and [ stn n * m ] *)

Theorem weqfromprodofstn ( n m : nat ) : stn n × stn m ≃ stn (n * m).
Proof.
  intros.
  induction ( natgthorleh m 0 ) as [ is | i ] .
  - assert ( i1 : ∏ i j : nat, i < n -> j < m -> j + i * m < n * m).
    + intros i j li lj.
      apply (natlthlehtrans ( j + i * m ) ( ( S i ) * m ) ( n * m )).
      * change (S i * m) with (i*m + m).
        rewrite natpluscomm.
        exact (natgthandplusl m j ( i * m ) lj ).
      * exact ( natlehandmultr ( S i ) n m ( natgthtogehsn _ _ li ) ).
    + set ( f := λ ij : stn n × stn m,
                   match ij
                   with tpair _ i j =>
                        stnpair ( n * m ) ( j + i * m ) ( i1 i j ( pr2 i ) ( pr2 j ) )
                   end ).
      split with f.
      assert ( isinf : isincl f ) .
      * apply isinclbetweensets .
        apply ( isofhleveldirprod 2 _ _ ( isasetstn n ) ( isasetstn m ) ) .
        apply ( isasetstn ( n * m ) ) .
        intros ij ij' e .  destruct ij as [ i j ] . destruct ij' as [ i' j' ] .
        destruct i as [ i li ] . destruct i' as [ i' li' ] .
        destruct j as [ j lj ] . destruct j' as [ j' lj' ] .
        simpl in e .
        assert ( e' := maponpaths ( stntonat ( n * m ) ) e )  . simpl in e' .
        assert ( eei : i = i' ) .
        { apply ( pr1 ( natdivremunique m i j i' j' lj lj' ( maponpaths ( stntonat _ ) e ) ) ) . }
        set ( eeis := invmaponpathsincl _ ( isinclstntonat _ ) ( stnpair _ i li ) ( stnpair _ i' li' ) eei ) .
        assert ( eej : j = j' ) .
        { apply ( pr2 ( natdivremunique m i j i' j' lj lj' ( maponpaths ( stntonat _ ) e ) ) ) . }
        set ( eejs := invmaponpathsincl _ ( isinclstntonat _ ) ( stnpair _ j lj ) ( stnpair _ j' lj' ) eej ) .
        apply ( pathsdirprod eeis eejs ) .
      * intro xnm .
        apply iscontraprop1 . apply ( isinf xnm ) .
        set ( e := pathsinv0 ( natdivremrule xnm m ( natgthtoneq _ _ is ) ) ) .
        set ( i := natdiv xnm m ) .   set ( j := natrem xnm m ) .
        destruct xnm as [ xnm lxnm ] .
        set ( li := natlthandmultrinv _ _ _ ( natlehlthtrans _ _ _ ( natlehmultnatdiv xnm m ( natgthtoneq _ _ is ) ) lxnm ) ) .
        set ( lj := lthnatrem xnm m ( natgthtoneq _ _ is ) ) .
        split with ( dirprodpair ( stnpair n i li ) ( stnpair m j lj ) ) .
        simpl .
        apply ( invmaponpathsincl _ ( isinclstntonat _ ) _ _ ) .  simpl .
        apply e .
  - set ( e := natleh0tois0 i ) .  rewrite e .  rewrite ( natmultn0 n ) . split with ( @pr2 _ _ ) .   apply ( isweqtoempty2 _ ( weqstn0toempty ) ) .
Defined.

(** *** Weak equivalences between decidable subsets of [ stn n ] and [ stn x ] *)

Theorem weqfromdecsubsetofstn { n : nat } ( f : stn n -> bool ) : total2 ( λ x : nat, ( hfiber f true ) ≃ ( stn x ) ) .
Proof . intro . induction n as [ | n IHn ] . intros .    split with 0 .  assert ( g : ( hfiber f true ) -> ( stn 0 ) ) . intro hf . destruct hf as [ i e ] .  destruct ( weqstn0toempty i ) .  apply ( weqtoempty2 g weqstn0toempty ) . intro . set ( g := weqfromcoprodofstn 1 n ) .   change ( 1 + n ) with ( S n ) in g .

set ( fl := λ i : stn 1, f ( g ( ii1 i ) ) ) .   set ( fh := λ i : stn n, f ( g ( ii2 i ) ) ) . assert ( w : ( hfiber f true ) ≃ ( hfiber ( sumofmaps fl fh ) true ) ) .  set ( int := invweq ( weqhfibersgwtog g f true  ) ) .  assert ( h : ∏ x : _ , paths ( f ( g x ) ) ( sumofmaps fl fh x ) ) . intro . destruct x as [ x1 | xn ] . apply idpath . apply idpath .   apply ( weqcomp int ( weqhfibershomot _ _ h true ) ) .  set ( w' := weqcomp w ( invweq ( weqhfibersofsumofmaps fl fh true ) ) ) .

set ( x0 := pr1 ( IHn fh ) ) . set ( w0 := pr2 ( IHn fh ) ) . simpl in w0 . destruct ( boolchoice ( fl lastelement ) ) as [ i | ni ] .

split with ( S x0 ) .  assert ( wi : ( hfiber fl true ) ≃ ( stn 1 ) ) . assert ( is : iscontr ( hfiber fl true ) ) . apply iscontraprop1 . apply ( isinclfromstn1 fl isasetbool true ) .  apply ( hfiberpair _ lastelement i ) . apply ( weqcontrcontr is iscontrstn1 ) .  apply ( weqcomp ( weqcomp w' ( weqcoprodf wi w0 ) ) ( weqfromcoprodofstn 1 _ ) ) .

split with x0 .  assert ( g' : neg ( hfiber fl true ) ) . intro hf . destruct hf as [ j e ] .  assert ( ee : j = lastelement ) . apply ( proofirrelevance _ ( isapropifcontr iscontrstn1 ) _ _ ) .  destruct ( nopathstruetofalse ( pathscomp0 ( pathscomp0 ( pathsinv0 e ) ( maponpaths fl ee ) ) ni ) ) .  apply ( weqcomp w' ( weqcomp ( invweq ( weqii2withneg _ g' ) ) w0 )  )  .  Defined .

(** *** Weak equivalences between hfibers of functions from [ stn n ] over isolated points and [ stn x ] *)

Theorem weqfromhfiberfromstn { n : nat } { X : UU } ( x : X ) ( is : isisolated X x ) ( f : stn n -> X ) : total2 ( λ x0 : nat, ( hfiber f x ) ≃ ( stn x0 ) ) .
Proof . intros .  set ( t := weqfromdecsubsetofstn ( λ i : _, eqbx X x is ( f i ) ) ) . split with ( pr1 t ) . apply ( weqcomp ( weqhfibertobhfiber f x is ) ( pr2 t ) ) .   Defined .





(** *** Weak equivalence between [ stn n -> stn m ] and [ stn ( natpower m n ) ] ( uses functional extensionality ) *)


Theorem weqfromfunstntostn ( n m : nat ) : weq ( stn n -> stn m ) ( stn ( natpower m n ) ) .
Proof. intro n . induction n as [ | n IHn ] . intro m .  apply weqcontrcontr . apply ( iscontrfunfromempty2 _ weqstn0toempty ) .  apply iscontrstn1 .
intro m . set ( w1 := weqfromcoprodofstn 1 n ) . assert ( w2 : weq ( stn ( S n ) -> stn m ) ( ((stn 1) ⨿ (stn n)) -> stn m ) ) .   apply ( weqbfun _ w1  ) .  set ( w3 := weqcomp w2 ( weqfunfromcoprodtoprod ( stn 1 ) ( stn n ) ( stn m ) ) ) .   set ( w4 := weqcomp w3 ( weqdirprodf ( weqfunfromcontr ( stn m ) iscontrstn1 ) ( IHn m ) ) ) .  apply ( weqcomp w4 ( weqfromprodofstn m ( natpower m n ) ) ) .  Defined .





(** *** Weak equivalence from the space of functions of a family [ stn ( f x ) ]  over [ stn n ] to [ stn ( stnprod n f ) ] ( uses functional extensionality ) *)


Definition stnprod { n : nat } ( f : stn n -> nat ) : nat .
Proof. intro n . induction n as [ | n IHn ] . intro. apply 1 . intro f . apply (  ( IHn ( λ i : stn n, f ( dni lastelement i ) ) ) * f lastelement ) . Defined .

Definition stnprod_step { n : nat } ( f : stn (S n) -> nat ) :
  stnprod f = stnprod (f ∘ dni lastelement) * f lastelement.
Proof. reflexivity. Defined.

Lemma stnprod_eq {n} (f g:stn n->nat) : f ~ g -> stnprod f = stnprod g.
Proof.
  intros ? ? ? h. induction n as [|n IH].
  { reflexivity. }
  rewrite 2? stnprod_step. induction (h lastelement).
  apply (maponpaths (λ i, i * f lastelement)). apply IH. intro x. apply h.
Defined.

Theorem weqstnprod { n : nat } ( P : stn n -> UU ) ( f : stn n -> nat ) ( ww : ∏ i : stn n , ( stn ( f i ) ) ≃ ( P i ) ) : weq ( ∏ x : stn n , P x  ) ( stn ( stnprod f ) ) .
Proof .
  intro n .
  induction n as [ | n IHn ] .
  - intros . simpl . apply ( weqcontrcontr ) .
    + apply ( iscontrsecoverempty2 _ ( negstn0 ) ) .
    + apply iscontrstn1 .
  - intros .
    set ( w1 := weqdnicoprod n lastelement ) .
    assert ( w2 := weqonsecbase P w1 ).
    assert ( w3 := weqsecovercoprodtoprod ( λ x : _, P ( w1 x ) ) ) .
    assert ( w4 := weqcomp w2 w3 ) ; clear w2 w3.
    assert ( w5 := IHn ( λ x : stn n, P ( w1 ( ii1 x ) ) ) ( λ x : stn n, f ( w1 ( ii1 x ) ) ) ( λ i : stn n, ww ( w1 ( ii1 i ) ) ) ) .
    assert ( w6 := weqcomp w4 ( weqdirprodf w5 ( weqsecoverunit _ ) ) ) ; clear w4 w5.
    simpl in w6 .
    assert ( w7 := weqcomp w6 ( weqdirprodf ( idweq _ ) ( invweq ( ww lastelement ) ) ) ) .
    refine ( _ ∘ w7 )%weq .
    unfold w1.
    exact (weqfromprodofstn _ _ ).
Defined .

(** *** Weak equivalence between [ ( stn n ) ≃ ( stn n ) ] and [ stn ( factorial n ) ] ( uses functional extensionality ) *)

Theorem weqweqstnsn ( n : nat ) : (stn(S n) ≃ stn (S n))  ≃  stn(S n) × ( stn n ≃ stn n ).
Proof.
  intro. assert ( l := @lastelement n ) .
  intermediate_weq ( isolated (stn (S n)) × (compl _ l ≃ compl _ l) ).
  { apply weqcutonweq. intro i. apply isdeceqstn. }
  apply weqdirprodf.
  - apply weqisolatedstntostn.
  - apply weqweq. apply invweq.
    intermediate_weq (compl_ne (stn (S n)) l (stnneq l)).
    + apply weqdnicompl.
    + apply compl_weq_compl_ne.
Defined .

Theorem weqfromweqstntostn ( n : nat ) : weq ( ( stn n ) ≃ ( stn n ) ) ( stn ( factorial n ) ) .
Proof . intro . induction n as [ | n IHn ] . simpl . apply ( weqcontrcontr ) . apply ( iscontraprop1 ) .    apply ( isapropweqtoempty2 _ ( negstn0 ) ) .  apply idweq . apply iscontrstn1 . change ( factorial ( S n ) ) with ( ( S n ) * ( factorial n ) ) .   set ( w1 := weqweqstnsn n ) . apply ( weqcomp w1 ( weqcomp ( weqdirprodf ( idweq _ ) IHn ) ( weqfromprodofstn _ _ ) ) ) .  Defined .


(* End of " weak equivalences between standard finite sets and constructions on these sets " . *)







(** ** Standard finite sets satisfy weak axiom of choice *)

Theorem ischoicebasestn ( n : nat ) : ischoicebase ( stn n ) .
Proof . intro . induction n as [ | n IHn ] .  apply ( ischoicebaseempty2 negstn0 ) .  apply ( ischoicebaseweqf ( weqdnicoprod n lastelement ) ( ischoicebasecoprod IHn ischoicebaseunit ) ) .  Defined .







(** ** Weak equivalence class of [ stn n ] determines [ n ] . *)


Lemma negweqstnsn0 (n:nat): neg (weq (stn (S n)) (stn O)).
Proof. unfold neg. intro. assert (lp: stn (S n)). apply lastelement.  intro X.  apply weqstn0toempty .  apply (pr1 X lp). Defined.

Lemma negweqstn0sn (n:nat): neg (weq (stn O) (stn (S n))).
Proof.  unfold neg. intro. assert (lp: stn (S n)). apply lastelement.  intro X.  apply weqstn0toempty .  apply (pr1 ( invweq X ) lp). Defined.

Lemma weqcutforstn ( n n' : nat ) : stn (S n) ≃ stn (S n') -> stn n ≃ stn n'.
Proof.
  intros ? ? w. assert ( k := @lastelement n  ).
  intermediate_weq (stn_compl k).
  - apply weqdnicompl.
  - intermediate_weq (stn_compl (w k)).
    + apply weqoncompl_ne.
    + apply invweq, weqdnicompl.
Defined.

Theorem weqtoeqstn { n n' : nat } : stn n ≃ stn n' -> n = n'.
Proof. intro.
       induction n as [ | n IHn ] .
       - intro. destruct n' as [ | n' ] .
         + reflexivity.
         + intro X. apply (fromempty (negweqstn0sn _ X)).
       - intro n'. destruct n' as [ | n' ] .
         + intro X. apply (fromempty ( negweqstnsn0 n X)).
         + intro X. apply maponpaths. apply IHn. now apply weqcutforstn.
Defined.

Corollary stnsdnegweqtoeq ( n n' : nat ) ( dw : dneg ((stn n) ≃ (stn n')) ) : n = n'.
Proof. intros n n' X. apply (eqfromdnegeq nat isdeceqnat _ _  (dnegf (@weqtoeqstn n n') X)). Defined.

(** ** Some results on bounded quantification *)


Lemma weqforallnatlehn0 ( F : nat -> hProp ) : ( ∏ n : nat , natleh n 0 -> F n ) ≃ ( F 0 ) .
Proof . intros .  assert ( lg : ( ∏ n : nat , natleh n 0 -> F n ) <-> ( F 0 ) ) . split . intro f .  apply ( f 0 ( isreflnatleh 0 ) ) .  intros f0 n l .  set ( e := natleh0tois0 l ) .  rewrite e .  apply f0 . assert ( is1 : isaprop ( ∏ n : nat , natleh n 0 -> F n ) ) . apply impred . intro n . apply impred .   intro l .  apply ( pr2 ( F n ) ) .  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) is1 ( pr2 ( F 0 ) ) ) . Defined .

Lemma weqforallnatlehnsn' ( n' : nat ) ( F : nat -> hProp ) : weq ( ∏ n : nat , natleh n ( S n' ) -> F n ) ( dirprod ( ∏ n : nat , natleh n n' -> F n ) ( F ( S n' ) ) ) .
Proof . intros . assert ( lg : ( ∏ n : nat , natleh n ( S n' ) -> F n ) <-> dirprod ( ∏ n : nat , natleh n n' -> F n ) ( F ( S n' ) ) ) .  split . intro f.  apply ( dirprodpair ( λ n, λ l, ( f n ( natlehtolehs _ _ l ) ) ) ( f ( S n' ) ( isreflnatleh _ ) ) ) .  intro d2 . intro n .  intro l .  destruct ( natlehchoice2 _ _ l ) as [ h | e ] . simpl in h .  apply ( pr1 d2 n h ) . destruct d2 as [ f2 d2 ] .  rewrite e .  apply d2 . assert ( is1 : isaprop ( ∏ n : nat , natleh n ( S n' ) -> F n ) ) . apply impred . intro n . apply impred . intro l . apply ( pr2 ( F n ) ) . assert ( is2 : isaprop ( dirprod ( ∏ n : nat , natleh n n' -> F n ) ( F ( S n' ) ) ) ) . apply isapropdirprod . apply impred . intro n . apply impred . intro l . apply ( pr2 ( F n ) ) .   apply ( pr2 ( F ( S n' ) ) ) .  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) is1 is2 ) . Defined .

Lemma weqexistsnatlehn0 ( P : nat -> hProp  ) : weq ( hexists ( λ n : nat, ( natleh n 0 ) × ( P n ) ) ) ( P 0 ) .
Proof . intro . assert ( lg : hexists ( λ n : nat, ( natleh n 0 ) × ( P n ) ) <-> P 0  ) . split .  simpl . apply ( @hinhuniv _ ( P 0 ) ) .  intro t2 .  destruct t2 as [ n d2 ] . destruct d2 as [ l p ] . set ( e := natleh0tois0 l ) . clearbody e .  destruct e . apply p . intro p . apply hinhpr . split with 0 .  split with ( isreflnatleh 0 ) .  apply p . apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) ( pr2 _ ) ( pr2 _ ) ) .  Defined .

Lemma weqexistsnatlehnsn' ( n' : nat ) ( P : nat -> hProp  ) : weq ( hexists ( λ n : nat, dirprod ( natleh n ( S n' ) ) ( P n ) ) ) ( hdisj ( hexists ( λ n : nat, ( natleh n n' ) × ( P n ) ) )  ( P ( S n' ) ) ) .
Proof . intros . assert ( lg : hexists ( λ n : nat, dirprod ( natleh n ( S n' ) ) ( P n ) )  <-> hdisj ( hexists ( λ n : nat, ( natleh n n' ) × ( P n ) ) )  ( P ( S n' ) )  ) . split . apply hinhfun .   intro t2 .  destruct t2 as [ n d2 ] . destruct d2 as [ l p ] . destruct ( natlehchoice2 _ _ l ) as [ h | nh ] . simpl in h . apply ii1 .  apply hinhpr . split with n .  apply ( dirprodpair h p ) . destruct nh .  apply ( ii2 p ) . simpl . apply ( @hinhuniv _ ( ishinh _ ) ) . intro c .  destruct c as [ t | p ] .  generalize t . simpl . apply hinhfun .  clear t . intro t . destruct t as [ n d2 ] . destruct d2 as [ l p ] . split with n .  split with ( natlehtolehs _ _ l ) .  apply p .  apply hinhpr . split with ( S n' ) .  split with ( isreflnatleh _ ) . apply p .  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) ( pr2 _ ) ( pr2 _ ) ) .  Defined .


Lemma isdecbexists ( n : nat ) ( P : nat -> UU ) ( is : ∏ n' , isdecprop ( P n' ) ) : isdecprop ( hexists ( λ n', ( natleh n' n ) × ( P n' ) ) ) .
Proof . intros .  set ( P' := λ n' : nat, hProppair _ ( is n' ) ) . induction n as [ | n IHn ] . apply ( isdecpropweqb ( weqexistsnatlehn0 P' ) ) . apply ( is 0 ) .   apply ( isdecpropweqb ( weqexistsnatlehnsn' _ P' ) ) . apply isdecprophdisj . apply IHn . apply ( is ( S n ) ) . Defined .

Lemma isdecbforall ( n : nat ) ( P : nat -> UU ) ( is : ∏ n' , isdecprop ( P n' ) ) : isdecprop ( ∏ n' , natleh n' n -> P n' )  .
Proof . intros .  set ( P' := λ n' : nat, hProppair _ ( is n' ) ) . induction n as [ | n IHn ] . apply ( isdecpropweqb ( weqforallnatlehn0 P' ) ) . apply ( is 0 ) .   apply ( isdecpropweqb ( weqforallnatlehnsn' _ P' ) ) . apply isdecpropdirprod . apply IHn . apply ( is ( S n ) ) . Defined .



(** The following lemma finds the largest [ n' ] such that [ neg ( P n' ) ] . It is a stronger form of ( neg ∏ ) -> ( exists neg ) in the case of bounded quantification of decidable propositions. *)

Lemma negbforalldectototal2neg ( n : nat ) ( P : nat -> UU ) ( is : ∏ n' : nat , isdecprop ( P n' ) ) : neg ( ∏ n' : nat , natleh n' n -> P n' ) -> total2 ( λ n', dirprod ( natleh n' n ) ( neg ( P n' ) ) ) .
Proof . intros n P is . set ( P' := λ n' : nat, hProppair _ ( is n' ) ) . induction n as [ | n IHn ] . intro nf . set ( nf0 := negf ( invweq ( weqforallnatlehn0 P' ) ) nf ) . split with 0 . apply ( dirprodpair ( isreflnatleh 0 ) nf0 ) .   intro nf . set ( nf2 := negf ( invweq ( weqforallnatlehnsn' n P' ) ) nf ) . set ( nf3 := fromneganddecy ( is ( S n ) ) nf2 ) . destruct nf3 as [ f1 | f2 ] . set ( int := IHn f1 ) .  destruct int as [ n' d2 ] . destruct d2 as [ l np ] . split with n' .  split with ( natlehtolehs _ _ l ) .  apply np . split with ( S n ) . split with ( isreflnatleh _ ) . apply f2 .  Defined .


(** ** Accessibility - the least element of an inhabited decidable subset of [nat] *)

Definition natdecleast ( F : nat -> UU ) ( is : ∏ n , isdecprop ( F n ) ) := total2 ( λ  n : nat, ( F n ) × ( ∏ n' : nat , F n' -> natleh n n' ) ) .

Lemma isapropnatdecleast ( F : nat -> UU ) ( is : ∏ n , isdecprop ( F n ) ) : isaprop ( natdecleast F is ) .
Proof . intros . set ( P := λ n' : nat, hProppair _ ( is n' ) ) . assert ( int1 : ∏ n : nat, isaprop ( ( F n ) × ( ∏ n' : nat , F n' -> natleh n n' ) ) ) .  intro n . apply isapropdirprod . apply ( pr2 ( P n ) ) .  apply impred . intro t .  apply impred .  intro .  apply ( pr2 ( natleh n t ) ) . set ( int2 := ( λ n : nat, hProppair _ ( int1 n ) ) : nat -> hProp ) .   change ( isaprop ( total2 int2 ) ) . apply isapropsubtype . intros x1 x2 .  intros c1 c2 . simpl in * . destruct c1 as [ e1 c1 ] . destruct c2 as [ e2 c2 ] . set ( l1 := c1 x2 e2 ) .  set ( l2 := c2 x1 e1 ) . apply ( isantisymmnatleh _ _ l1 l2 ) .  Defined .

Theorem accth ( F : nat -> UU ) ( is : ∏ n , isdecprop ( F n ) )  ( is' : hexists F ) : natdecleast F is .
Proof . intros F is . simpl . apply (@hinhuniv _ ( hProppair _ ( isapropnatdecleast F is ) ) ) . intro t2. destruct t2 as [ n l ] . simpl .

set ( F' := λ n' : nat, hexists ( λ n'', ( natleh n'' n' ) × ( F n'' ) ) ) .  assert ( X : ∏ n' , F' n' -> natdecleast F is ) .  intro n' .    induction n' as [ | n' IHn' ] . apply ( @hinhuniv _  ( hProppair _ ( isapropnatdecleast F is ) ) ) . intro t2 . destruct t2 as [ n'' is'' ] . destruct is'' as [ l'' d'' ] .  split with 0 .  split . set ( e := natleh0tois0 l'' ) . clearbody e . destruct e . apply d'' .  apply ( λ n', λ f : _, natleh0n n' ) .  apply ( @hinhuniv _  ( hProppair _ ( isapropnatdecleast F is ) ) ) . intro t2 .  destruct t2 as [ n'' is'' ] . set ( j := natlehchoice2 _ _ ( pr1 is'' ) ) .  destruct j as [ jl | je ] .  simpl .  apply ( IHn' ( hinhpr ( tpair _ n'' ( dirprodpair jl ( pr2 is'' ) ) ) ) ) .  simpl . rewrite je in is''  .  destruct is'' as [ nn is'' ] .  clear nn. clear je . clear n'' .

assert ( is' : isdecprop ( F' n' ) ) . apply ( isdecbexists n' F is ) .   destruct ( pr1 is' ) as [ f | nf ] .  apply ( IHn'  f ) .  split with ( S n' ) .  split with is'' . intros n0 fn0 . destruct ( natlthorgeh n0 ( S n' ) )  as [ l' | g' ] .  set ( i' := natlthtolehsn _ _ l' ) .  destruct ( nf ( hinhpr ( tpair _ n0 ( dirprodpair i' fn0 ) ) ) ) .   apply g' .

apply ( X n ( hinhpr ( tpair _ n ( dirprodpair ( isreflnatleh n ) l ) ) ) ) .  Defined .


Corollary dni_lastelement_is_inj {n : nat} {i j : stn n}
      (e : dni_lastelement i = dni_lastelement j) :
  i = j.
Proof.
  intros n i j e.
  apply isinjstntonat.
  unfold dni_lastelement in e.
  apply (maponpaths pr1) in e.
  exact e.
Defined.

Corollary dni_lastelement_eq : ∏ (n : nat) (i : stn (S n)) (ie : pr1 i < n),
    i = dni_lastelement (stnpair n (pr1 i) ie).
Proof.
  intros n i ie.
  apply isinjstntonat.
  apply idpath.
Defined.

Corollary lastelement_eq : ∏ (n : nat) (i : stn (S n)) (e : pr1 i = n),
    i = lastelement.
Proof.
  intros n i e.
  unfold lastelement.
  apply isinjstntonat.
  apply e.
Defined.

(* a tactic for proving things by induction over a finite number of cases *)
Ltac inductive_reflexivity i b :=
  (* Here i is a variable natural number and b is a bound on *)
  (*      i of the form i<k, where k is a numeral. *)
  induction i as [|i];
  [ try apply isinjstntonat ; reflexivity |
    contradicts (negnatlthn0 i) b || inductive_reflexivity i b ].

(** concatenation and flattening of functions *)

Definition concatenate' {X:UU} {m n} (f : stn m -> X) (g : stn n -> X) : stn (m+n) -> X.
Proof.
  intros ? ? ? ? ? i.
  (* we are careful to use weqfromcoprodofstn_invmap both here and in weqstnsum_invmap *)
  induction (weqfromcoprodofstn_invmap _ _ i) as [j | k].
  + exact (f j).
  + exact (g k).
Defined.

Definition concatenate'_r0 {X:UU} {m} (f : stn m -> X) (g : stn 0 -> X) :
  concatenate' f g = transportb (λ n, stn n -> X) (natplusr0 m) f.
Proof.
  intros. apply funextfun; intro i. unfold concatenate'.
  rewrite weqfromcoprodofstn_invmap_r0; simpl. clear g.
  apply transportb_fun'.
Defined.

Definition concatenate'_r0' {X:UU} {m} (f : stn m -> X) (g : stn 0 -> X) (i : stn (m+0)) :
  concatenate' f g i = f (transportf stn (natplusr0 m) i).
Proof.
  intros. unfold concatenate'. now rewrite weqfromcoprodofstn_invmap_r0.
Defined.

Definition flatten' {X n} {m:stn n->nat} : (∏ (i:stn n), stn (m i) -> X) -> (stn (stnsum m) -> X).
Proof.
  intros ? ? ? g. exact (uncurry g ∘ invmap (weqstnsum1 m)).
Defined.

Definition stn_predicate {n : nat} (P : stn n -> UU)
           (k : nat) (h h' : k < n) :
           P (k,,h) -> P (k,,h').
Proof.
  intros n P k h h' H.
  transparent assert (X : (h = h')).
  { apply propproperty. }
  exact (transportf (λ x, P (k,,x)) X H).
Defined.

Definition two := stn 2.

Definition two_rec {A : UU} (a b : A) : stn 2 -> A.
Proof.
  intros A a b.
  induction 1 as [n p].
  induction n as [|n _]; [apply a|].
  induction n as [|n _]; [apply b|].
  induction (nopathsfalsetotrue p).
Defined.

Definition two_rec_dep (P : two -> UU):
  P (● 0) -> P (● 1) -> ∏ n, P n.
Proof.
  intros P a b n.
  induction n as [n p].
  induction n as [|n _]. eapply stn_predicate. apply a.
  induction n as [|n _]. eapply stn_predicate. apply b.
  induction (nopathsfalsetotrue p).
Defined.

Definition three := stn 3.

Definition three_rec {A : UU} (a b c : A) : stn 3 -> A.
Proof.
  intros A a b c.
  induction 1 as [n p].
  induction n as [|n _]; [apply a|].
  induction n as [|n _]; [apply b|].
  induction n as [|n _]; [apply c|].
  induction (nopathsfalsetotrue p).
Defined.

Definition three_rec_dep (P : three -> UU):
  P (● 0) -> P (● 1) -> P (● 2) -> ∏ n, P n.
Proof.
  intros P a b c n.
  induction n as [n p].
  induction n as [|n _]. eapply stn_predicate. apply a.
  induction n as [|n _]. eapply stn_predicate. apply b.
  induction n as [|n _]. eapply stn_predicate. apply c.
  induction (nopathsfalsetotrue p).
Defined.

(** ordered bijections are unique *)

Definition is_stn_increasing {m} (f : ⟦m⟧→nat) := ∏ (i j:⟦m⟧), i ≤ j → f i ≤ f j.

Definition is_stn_strictly_increasing {m} (f : ⟦m⟧→nat) := ∏ (i j:⟦m⟧), i < j → f i < f j.

Lemma is_strincr_impl_incr {m} (f : ⟦m⟧→nat) :
  is_stn_strictly_increasing f -> is_stn_increasing f.
Proof.
  intros ? ? inc ? ? e. induction (natlehchoice _ _ e) as [I|J]; clear e.
  + apply natlthtoleh. apply inc. exact I.
  + assert (J' : i = j).
    { apply subtypeEquality_prop. exact J. }
    clear J. induction J'. apply isreflnatleh.
Defined.

Lemma is_incr_impl_strincr {m} (f : ⟦m⟧→nat) :
  isincl f -> is_stn_increasing f -> is_stn_strictly_increasing f.
Proof.
  intros ? ? incl incr i j e.
  assert (d : i ≤ j).
  { now apply natlthtoleh. }
  assert (c := incr _ _ d); clear d.
  assert (b : i != j).
  { intro p. induction p. exact (isirreflnatlth _ e). }
  induction (natlehchoice _ _ c) as [T|U].
  - exact T.
  - apply fromempty.
    unfold isincl,isofhlevel,isofhlevelf in incl.
    assert (V := invmaponpathsincl f incl i j U).
    induction V.
    exact (isirreflnatlth _ e).
Defined.

Lemma stnsum_ge1 {m} (f : ⟦m⟧ → nat) : ( ∏ i, f i ≥ 1 ) → stnsum f ≥ m.
Proof.
  intros ? ? G.
  set (g := λ i:⟦m⟧, 1).
  assert (E : stnsum g = m).
  { apply stnsum_1. }
  assert (F : stnsum g ≤ stnsum f).
  { apply stnsum_le. exact G. }
  generalize E F; generalize (stnsum g); clear E F g; intros s e i.
  induction e.
  exact i.
Defined.

Lemma stnsum_add {m} (f g : ⟦m⟧ → nat) : stnsum (λ i, f i + g i) = stnsum f + stnsum g.
Proof.
  intros.
  induction m as [|m I].
  - reflexivity.
  - rewrite 3 stnsum_step.
    change ((λ i : ⟦ S m ⟧, f i + g i) ∘ dni lastelement)
    with (λ y : ⟦ m ⟧, f (dni lastelement y) + g (dni lastelement y)).
    rewrite I. rewrite natplusassoc.
    rewrite natplusassoc. unfold funcomp. apply maponpaths. rewrite natpluscomm.
    rewrite natplusassoc. apply maponpaths. rewrite natpluscomm. reflexivity.
Defined.

Lemma stnsum_lt {m} (f g : ⟦m⟧ → nat) : ( ∏ i, f i < g i ) → stnsum g ≥ stnsum f + m.
Proof.
  intros. set (h := λ i, f i + 1).
  assert (E : stnsum h = stnsum f + m).
  { unfold h; clear h. rewrite stnsum_add. rewrite stnsum_1. reflexivity. }
  rewrite <- E. apply stnsum_le. intros i. unfold h. apply natlthtolehp1. apply X.
Defined.

Local Arguments dni {_} _ _.

Lemma stnsum_diffs {m} (f : ⟦S m⟧ → nat) : is_stn_increasing f ->
  stnsum (λ i, f (dni_firstelement i) - f (dni_lastelement i)) = f lastelement - f firstelement.
Proof.
  intros ? ? e.
  induction m as [|m I].
  - change (0 = f firstelement - f firstelement).
    apply pathsinv0.
    apply minuseq0'.
  - rewrite stnsum_step.
    change (f (dni_firstelement lastelement)) with (f lastelement).
    rewrite natpluscomm.
    simple refine (_ @ ! @natdiffplusdiff
                     (f lastelement)
                     (f (dni_lastelement lastelement))
                     (f firstelement) _ _).
    + apply maponpaths.
      simple refine (_ @ I (f ∘ dni_lastelement) _ @ _).
      * unfold funcomp. apply stnsum_eq; intros i. rewrite replace_dni_last. reflexivity.
      * intros i j s. unfold funcomp. apply e. apply s.
      * reflexivity.
    + apply e. apply lastelement_ge.
    + apply e. apply firstelement_le.
Defined.

Lemma stn_ord_incl {m} (f : ⟦S m⟧ → nat) :
  is_stn_strictly_increasing f  →  f lastelement ≥ f firstelement + m.
Proof.
  intros ? ? strinc.
  assert (inc := is_strincr_impl_incr _ strinc).
  set (d := λ i : ⟦ m ⟧, f (dni_firstelement i) - f (dni_lastelement i)).
  assert (E := stnsum_diffs f inc).
  change (stnsum d = f lastelement - f firstelement) in E.
  assert (F : ∏ i, f (dni_firstelement i) > f (dni_lastelement i)).
  { intros i. apply strinc. change (stntonat _ i < S(stntonat _ i)). apply natlthnsn. }
  assert (G : ∏ i, d i ≥ 1).
  { intros i. apply natgthtogehsn. apply minusgth0. apply F. }
  clear F.
  assert (H := stnsum_ge1 _ G). clear G.
  rewrite E in H. clear E d.
  assert (I : f lastelement ≥ f firstelement).
  { apply inc. reflexivity. }
  assert (J := minusplusnmm _ _ I); clear I.
  rewrite <- J; clear J.
  rewrite natpluscomm.
  apply natgehandplusl.
  exact H.
Defined.

Lemma stn_ord_bij {n} (f : ⟦ n ⟧ ≃ ⟦ n ⟧) :
  (∏ (i j:⟦n⟧), i ≤ j → f i ≤ f j) -> ∏ i, f i = i.
Proof.
  intros ? ? inc ?.
  assert (strincr : is_stn_strictly_increasing (pr1weq f)).
  { apply is_incr_impl_strincr.
    { simple refine (isinclcomp (weqtoincl _ _ f) (stntonat_incl _)). }
    { exact inc. } }
  induction n as [|n I].
  - apply fromempty. now apply negstn0.
  - assert (M : stntonat _ (f lastelement) = n).
    { apply isantisymmnatgeh.
      * assert (N : f lastelement ≥ f firstelement + n).
        { exact (stn_ord_incl (pr1weq f) strincr). }
        simple refine (istransnatgeh _ _ _ N _).
        apply natgehplusnmm.
      * exact (stnlt (f lastelement)). }
    assert (L : ∏ j, f (dni_lastelement j) < n).
    { intros. induction M. apply strincr. exact (stnlt j). }
    set (f' := λ j : ⟦n⟧, stnpair n (stntonat _ (f (dni_lastelement j))) (L j)).

Abort.
