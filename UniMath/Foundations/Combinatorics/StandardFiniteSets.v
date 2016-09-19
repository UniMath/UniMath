(** * Standard finite sets . Vladimir Voevodsky . Apr. - Sep. 2011 .

This file contains main constructions related to the standard finite sets defined as the initial intervals of [ nat ] and their properties . *)




(** ** Preamble *)

(** Settings *)

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)



(** Imports. *)

Require Export UniMath.Foundations.NumberSystems.NaturalNumbers .

(** ** Standard finite sets [ stn ] . *)

Definition stn ( n : nat ) := Σ m, m < n.
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

Notation "● x" := (x ,, idpath _) (at level 35) : stn.

Lemma isinclstntonat ( n : nat ) : isincl ( stntonat n ) .
Proof. intro .  refine (isinclpr1 _ _) .  intro x .  apply ( pr2 ( natlth x n ) ) .  Defined.

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

Definition weqisolatedstntostn ( n : nat ) : weq ( isolated ( stn n ) ) ( stn n ) .
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

Definition lastelement ( n : nat ) : stn ( S n ) .
Proof. intro .   split with n .  apply ( natgthsnn n ) .  Defined .

Definition firstelement (n:nat) : stn(S n).
Proof. intro. exists 0. apply natgthsn0. Defined.

Definition stnmtostnn ( m n : nat ) (isnatleh: natleh m n ) : stn m -> stn n := fun x : stn m => match x with tpair _ i is => stnpair _ i ( natlthlehtrans i m n is isnatleh ) end .

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

(** ** "Boundary" maps [ dni : stn n -> stn ( S n ) ] and their properties . *)

Definition dni ( n : nat ) ( i : stn ( S n ) ) : stn n -> stn ( S n ) .
Proof. intros n i x . exists (di i x). unfold di.
       induction (natlthorgeh x i) as [lt|ge].
       - apply natgthtogths. exact (pr2 x).
       - exact (pr2 x).
Defined.

Lemma dni_last n (i:stn n) : pr1 (dni n (lastelement n) i) = i.
Proof.
  intros. induction i as [i I]. unfold dni,di. simpl. induction (natlthorgeh i n) as [g|g].
  { reflexivity. }
  simpl. contradicts (natlehtonegnatgth _ _ g) I.
Defined.

Lemma dni_first n (i:stn n) : pr1 (dni n (firstelement n) i) = S i.
Proof.
  reflexivity.
Defined.

Definition dni_lastelement {n} : stn n -> stn (S n).
(* this definition is simpler than that of [dni n (lastelement n)], since no choice is involved, so it's useful in special situations *)
Proof. intros ? h. exists (pr1 h). exact (natlthtolths _ _ (pr2 h)). Defined.

Definition pr1_dni_lastelement {n} {i:stn n} : pr1 (dni_lastelement i) = pr1 i.
Proof. reflexivity. Defined.

Lemma dnicommsq ( n : nat ) ( i : stn ( S n ) ) : commsqstr( dni n i )  ( stntonat ( S n ) ) ( stntonat n ) ( di i )  .
Proof. intros . intro x . unfold dni . unfold di . destruct ( natlthorgeh x i ) .  simpl .  apply idpath . simpl .  apply idpath . Defined .

Theorem dnihfsq ( n : nat ) ( i : stn ( S n ) ) : hfsqstr ( di i ) ( stntonat ( S n ) ) ( stntonat n ) ( dni n i ) .
Proof. intros . apply ( ishfsqweqhfibersgtof' ( di i ) ( stntonat ( S n ) ) ( stntonat n ) ( dni n i ) ( dnicommsq _ _  ) ) . intro x . destruct ( natlthorgeh x n ) as [ g | l ] .

assert ( is1 : iscontr ( hfiber ( stntonat n ) x ) ) . apply iscontrhfiberstntonat . assumption .
assert ( is2 : iscontr ( hfiber ( stntonat ( S n ) ) ( di i x )  ) ) .    apply iscontrhfiberstntonat . apply ( natlehlthtrans _ ( S x ) ( S n ) ( natlehdinsn i x ) g ) .
apply isweqcontrcontr . assumption . assumption .

assert ( is1 : neg ( hfiber ( stntonat ( S n ) ) ( di i x ) ) ) . apply neghfiberstntonat . unfold di .   destruct ( natlthorgeh x i ) as [ l'' | g' ] .  destruct ( natgehchoice2 _ _ l ) as [ g' | e ] .   apply g' .  rewrite e in l'' .  assert ( int := natlthtolehsn _ _ l'' ) . contradicts (natgthnegleh (pr2 i)) int. apply l .  apply ( isweqtoempty2 _ is1 ) .
Defined .

Lemma dni_neq_i {n} i j : i ≠ dni n i j.
Proof.
  intros. simpl. apply di_neq_i.
Defined.

Lemma weqhfiberdnihfiberdi ( n : nat ) ( i j : stn ( S n ) ) : weq ( hfiber ( dni n i ) j ) ( hfiber ( di i ) j ) .
Proof.  intros . apply ( weqhfibersg'tof _ _ _ _ ( dnihfsq n i ) j ) . Defined .

Lemma neghfiberdni ( n : nat ) ( i : stn ( S n ) ) : ¬ ( hfiber ( dni n i ) i ) .
Proof. intros . apply ( negf ( weqhfiberdnihfiberdi n i i ) ( neghfiberdi i ) ) . Defined .

Lemma iscontrhfiberdni ( n : nat ) ( i j : stn ( S n ) ) : i ≠ j -> iscontr ( hfiber ( dni n i ) j ) .
Proof . intros ? ? ? ne . exact ( iscontrweqb ( weqhfiberdnihfiberdi n i j ) ( iscontrhfiberdi i j ne ) ) . Defined .

Lemma isdecincldni ( n : nat ) ( i : stn ( S n ) ) : isdecincl ( dni n i ) .
Proof.  intros . intro j . induction ( stn_eq_or_neq i j ) as [eq|ne].
        - induction eq. apply ( isdecpropfromneg ( neghfiberdni n i ) ) .
        - apply ( isdecpropfromiscontr (iscontrhfiberdni _ _ _ ne) ) .
Defined .

Lemma isincldni ( n : nat ) ( i : stn ( S n ) ) : isincl ( dni n i ) .
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



(** *** The weak equivalence from [ stn n ] to the complement of a point [ j ] in [ stn ( S n ) ] defined by [ dni n j ] *)

Definition stn_compl {n} (i:stn n) := compl_ne _ i (stnneq i).

Definition dnitocompl ( n : nat ) ( i : stn ( S n ) ) : stn n -> stn_compl i.
Proof. intros ? ? j. exists ( dni n i j ) . apply dni_neq_i. Defined.

Lemma isweqdnitocompl  ( n : nat ) ( i : stn ( S n ) ) : isweq ( dnitocompl n i ) .
Proof.
  intros ? ? jni.
  assert ( w := samehfibers ( dnitocompl n i )  _ ( isinclpr1compl_ne _ i _ ) jni ) ; simpl in w .
  apply (iscontrweqb w). apply iscontrhfiberdni. exact (pr2 jni).
Defined.

Definition weqdnicompl n (i:stn(S n)): stn n ≃ stn_compl i.
Proof.
  intros.
  set (w := weqdicompl (stntonat _ i)).
  assert (eq : Π j, j < n <-> pr1 (w j) < S n).
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

Definition weqdnicompl_compute_last n i : pr1 (pr1 (weqdnicompl n (lastelement n) i)) = pr1 i.
Proof.
  intros. induction i as [i b]. simpl. unfold di; simpl.
  induction (natlthorgeh i n) as [p|p].
  { reflexivity. }
  { contradicts (natlehneggth p) b. }
Defined.

Definition weqdnicompl_compute_first n i : pr1 (pr1 (weqdnicompl n (firstelement n) i)) = S (pr1 i).
Proof.
  intros. induction i as [i b]. simpl. unfold di; simpl. reflexivity.
Defined.

Definition inv_weqdnicompl_compute_last n i : pr1 (invweq (weqdnicompl n (lastelement n)) i) = pr1 (pr1 i).
Proof.
  intros.
  exact ( ! (weqdnicompl_compute_last _ _) @ (maponpaths pr1 (maponpaths pr1 (homotweqinvweq _ i)))).
Defined.

(** *** Weak equivalence from [ coprod ( stn n ) unit ] to [ stn ( S n ) ] defined by [ dni n i ] *)

Definition weqdnicoprod_provisional n (j : stn(S n)) : stn n ⨿ unit ≃ stn (S n).
Proof.
  intros.
  apply (weqcomp (weqcoprodf (weqdnicompl n j) (idweq unit))
                 (weqrecompl_ne (stn (S n)) j (isdeceqstn (S n) j) (stnneq j))).
Defined.

Opaque weqdnicoprod_provisional.

Definition weqdnicoprod_map {n} (j : stn(S n)) : stn n ⨿ unit -> stn (S n).
  intros n j x. induction x as [i|t].
    { exact (dni n j i). }
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

Definition weqdnicoprod_new n (j : stn(S n)) : stn n ⨿ unit ≃ stn (S n).
Proof.
  (* in progress *)
  (* this version might be more computable than weqdnicoprod *)
  intros n j.
  apply (weqgradth (weqdnicoprod_map j) (weqdnicoprod_invmap j)).
  { intro x. induction x as [i|t].
    { try reflexivity.
      induction i as [i I]. induction j as [j J].
      try reflexivity.
      unfold weqdnicoprod_map, dni, di; simpl.
      induction (natlthorgeh i j) as [a|a].
      { simpl. unfold weqdnicoprod_invmap.
        induction
          (isdeceqstn (S n) (stnpair (S n) i (natgthtogths n i I))
                      (@tpair nat
                              (fun m : nat =>
                                 @paths bool
                                        match m return bool with
                                          | O => true
                                          | S m0 => natgtb n m0
                                        end true) j J)) as [b|b].
        { simpl. assert (b' := maponpaths (stntonat _) b); simpl in b'.
          induction b'. induction (isirreflnatlth _ a). }
        {
Abort.

(** *** Weak equivalences from [ stn n ] for [ n = 0 , 1 , 2 ] to [ empty ] , [ unit ] and [ bool ] ( see also the section on [ nelstruct ] in finitesets.v ) . *)

Definition negstn0 : neg ( stn 0 ) .
Proof . intro x .  destruct x as [ a b ] .  apply ( negnatlthn0 _ b ) . Defined .

Definition weqstn0toempty : weq ( stn 0 ) empty .
Proof .  apply weqtoempty . apply negstn0 . Defined .

Definition weqstn1tounit : weq ( stn 1 ) unit .
Proof. set ( f := fun x : stn 1 => tt ) . apply weqcontrcontr .  split with ( lastelement 0 ) .   intro t .  destruct t as [ t l ] . set ( e := natlth1tois0 _ l ) .   apply ( invmaponpathsincl _ ( isinclstntonat 1 ) ( stnpair _ t l ) ( lastelement 0 ) e ) .  apply iscontrunit .  Defined .

Corollary iscontrstn1 : iscontr ( stn 1 ) .
Proof. apply iscontrifweqtounit . apply weqstn1tounit . Defined .

Corollary isconnectedstn1 : Π i1 i2 : stn 1, i1 = i2.
Proof.
  intros i1 i2.
  apply (invmaponpathsweq weqstn1tounit).
  apply isconnectedunit.
Defined.

Lemma isinclfromstn1 { X : UU } ( f : stn 1 -> X ) ( is : isaset X ) : isincl f .
Proof. intros . apply ( isinclbetweensets f ( isasetstn 1 ) is ) . intros x x' e . apply ( invmaponpathsweq weqstn1tounit x x' ( idpath tt ) )  .  Defined .

Definition weqstn2tobool : weq ( stn 2 ) bool .
Proof. set ( f := fun j : stn 2 => match ( isdeceqnat j 0 ) with ii1 _ => false | ii2 _ => true end ) . set ( g := fun b : bool => match b with false => stnpair 2 0 ( idpath true ) | true => stnpair 2 1 ( idpath true ) end ) .  split with f .
assert ( egf : Π j : _ , paths ( g ( f j ) ) j ) . intro j . unfold f .  destruct ( isdeceqnat j 0 ) as [ e | ne ] .  apply ( invmaponpathsincl _ ( isinclstntonat 2 ) ) . rewrite e .   apply idpath .  apply ( invmaponpathsincl _ ( isinclstntonat 2 ) ) . destruct j as [ j l ] . simpl . set ( l' := natlthtolehsn _ _ l ) .  destruct ( natlehchoice _ _ l' ) as [ l'' | e ] . simpl in ne . destruct  ( ne ( natlth1tois0 _ l'' ) ) .  apply ( pathsinv0 ( invmaponpathsS _ _ e ) ) .
assert ( efg : Π b : _ , paths ( f ( g b ) ) b ) . intro b .  unfold g .  destruct b . apply idpath . apply idpath.
apply ( gradth _ _ egf efg ) . Defined .






(** ***  Weak equivalence between the coproduct of [ stn n ] and [ stn m ] and [ stn ( n + m ) ] *)

Theorem weqfromcoprodofstn ( n m : nat ) : weq ( coprod ( stn n ) ( stn m ) ) ( stn ( n + m ) ) .
Proof. intros .

assert ( i1 : Π i : nat , natlth i n -> natlth i ( n + m ) ) . intros i1 l . apply ( natlthlehtrans _ _ _ l ( natlehnplusnm n m ) ) .
assert ( i2 : Π i : nat , natlth i m -> natlth ( n + i ) ( n + m ) ) .  intros i2 l .  apply natgthandplusl . assumption .
set ( f := fun ab : coprod ( stn n ) ( stn m ) => match ab with ii1 a =>  stnpair ( n + m ) a ( i1 a ( pr2 a ) ) | ii2 b => stnpair ( n + m ) ( n + b ) ( i2 b ( pr2 b ) ) end ) .
split with f .

assert ( is : isincl f ) .  apply  isinclbetweensets . apply ( isofhlevelssncoprod 0 _ _ ( isasetstn n ) ( isasetstn m ) ) .  apply ( isasetstn ( n + m ) ) .  intros x x' . intro e .   destruct x as [ xn | xm ] .

destruct x' as [ xn' | xm' ] . apply ( maponpaths (@ii1 _ _ ) ) .  apply ( invmaponpathsincl _ ( isinclstntonat n ) _ _ ) .  destruct xn as [ x ex ] . destruct xn' as [ x' ex' ] . simpl in e .  simpl .  apply ( maponpaths ( stntonat ( n + m ) ) e  )  .   destruct xn as [ x ex ] . destruct xm' as [ x' ex' ] . simpl in e . assert ( l : natleh n x ) . set ( e' := maponpaths ( stntonat _ ) e ) .   simpl in e' . rewrite e' .  apply ( natlehnplusnm n x' ) . destruct ( natlehtonegnatgth _ _ l ex ) .

destruct x' as [ xn' | xm' ] . destruct xm as [ x ex ] . destruct xn' as [ x' ex' ] . simpl in e .  assert ( e' := maponpaths ( stntonat _ ) e ) .  simpl in e' .  assert ( a : empty ) . clear e . rewrite ( pathsinv0 e' ) in ex' .  apply ( negnatgthnplusnm _ _ ex' )  .   destruct a . destruct xm as [ x ex ] . destruct xm' as [ x' ex' ] .  simpl in e .  apply ( maponpaths ( @ii2 _ _ ) ) .   simpl .  apply ( invmaponpathsincl _ ( isinclstntonat m ) _ _ ) .  simpl .  apply ( invmaponpathsincl _ ( isinclnatplusl n ) ) .  apply ( maponpaths ( stntonat _ ) e ).

intro jl . apply iscontraprop1 .  apply ( is jl ) .   destruct jl as [ j l ] . destruct ( natgthorleh n j ) as [ i | ni ] .

split with ( ii1 ( stnpair _ j i ) ) . simpl .   apply ( invmaponpathsincl _ ( isinclstntonat ( n + m ) )  (stnpair (n + m) j (i1 j i)) ( stnpair _ j l )  ( idpath j ) ) .

set ( jmn := pr1 ( iscontrhfibernatplusl n j ni ) ) .   destruct jmn as [ k e ] . assert ( is'' : natlth k m ) . rewrite ( pathsinv0 e ) in l .  apply ( natgthandpluslinv _ _ _ l ) . split with ( ii2 ( stnpair _ k is'' ) ) .  simpl .  apply ( invmaponpathsincl _ ( isinclstntonat _ ) (stnpair _ (n + k) (i2 k is'')) ( stnpair _ j l ) e ) . Defined .

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

Definition stnsum { n : nat } ( f : stn n -> nat ) : nat .
Proof. intro n . induction n as [ | n IHn ] . intro. apply 0 . intro f . apply (  ( IHn ( fun i : stn n => f ( dni n ( lastelement n ) i ) ) ) + f ( lastelement n ) ) . Defined .

Lemma stnsum_step {n} (f:stn (S n) -> nat) : stnsum f = stnsum (f ∘ (dni n (lastelement n))) + f (lastelement n).
Proof.
  intros. reflexivity.
Defined.

Lemma stnsum_eq {n} (f g:stn n->nat) : f ~ g -> stnsum f = stnsum g.
Proof.
  intros ? ? ? h. induction n as [|n IH].
  { reflexivity. }
  rewrite 2? stnsum_step. induction (h (lastelement _)).
  apply (maponpaths (λ i, i + f (lastelement _))). apply IH. intro x. apply h.
Defined.

Lemma transport_stnsum {m n} (e:m=n) (g:stn n->nat) :
  stnsum g = stnsum (λ i, g(transportf stn e i)).
Proof. intros. induction e. reflexivity. Defined.

Lemma stnsum_le {n} (f g:stn n->nat) : (Π i, f i ≤ g i) -> stnsum f ≤ stnsum g.
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
  { change (stnsum (f ∘ stn_right m 0)) with 0. rewrite natplusr0. assert (e := ! natplusr0 m).
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

Lemma stnsum_dni {n} (f:stn (S n)->nat) (j:stn (S n)) : stnsum f = stnsum (f ∘ dni n j) + f j.
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
  generalize (stnsum (λ x, f (transportf stn (! e) (dni _ (transportf stn e j) x)))); intro s.
  induction e. apply natlehmplusnm.
Defined.

Corollary stnsum_pos_0 {n} (f:stn (S n)->nat) : f (firstelement _) ≤ stnsum f.
Proof. intros. exact (stnsum_pos f (firstelement _)). Defined.

Lemma stnsum_1 n : stnsum(λ i:stn n, 1) = n.
Proof.
  intros. induction n as [|n IH]. { reflexivity. } simpl. rewrite natpluscomm. apply maponpaths.
  exact IH.
Defined.

Lemma stnsum_last_le {n} (f:stn (S n) -> nat) : f(lastelement _) ≤ stnsum f.
Proof.
  intros. rewrite stnsum_step. apply natlehmplusnm.
Defined.

Lemma stnsum_first_le {n} (f:stn (S n) -> nat) : f(firstelement _) ≤ stnsum f.
Proof.
  intros. induction n as [|n IH].
  { apply isreflnatleh. }
  rewrite stnsum_step. assert (W := IH (f ∘ dni _ (lastelement _))).
  change ((f ∘ dni _ (lastelement _)) (firstelement _)) with (f (firstelement _)) in W.
  apply (istransnatleh W); clear W. apply natlehnplusnm.
Defined.

Definition weqstnsum_invmap { n : nat } (f : stn n -> nat) : (Σ i, stn (f i)) <- stn (stnsum f).
Proof.
  intros ? ?. induction n as [|n IH].
  { intros l. induction (negstn0 l). }
  intros l. induction l as [l L].
  choose (l < f (firstelement _))%dnat a b.
  { exact (firstelement _,, (l,,a)). }
  assert (b' : f (firstelement _) ≤ l). { exact (negnatgthtoleh b). } clear b.
  rewrite (stnsum_dni _ (firstelement _)) in L.
  rewrite natpluscomm in L.
  assert ( c := minusplusnmm l (f (firstelement _)) b'); clear b'.
  rewrite natpluscomm in c.
  rewrite <- c in L; clear c.
  assert ( d := natlthandpluslinv _ _ _ L); clear L.
  set (l' := (l - f (firstelement n),,d) : stn _).
  assert ( e := IH (f ∘ dni n (firstelement n)) l' ).
  induction e as [r s].
  exact (dni _ (firstelement _) r,,s).
Defined.

Lemma stn_right_first n i : stn_right i (S n) (firstelement n) = stnpair (i + S n) i (natltplusS n i).
Proof.
  intros.
  apply subtypeEquality_prop.
  simpl.
  apply natplusr0.
Defined.

Definition weqstnsum_map { n : nat } (f : stn n -> nat) : (Σ i, stn (f i)) -> stn (stnsum f).
Proof.
  intros ? ? ij; induction ij as [i j]; induction i as [i I]; induction j as [j J].
  (* assert (I' := natlthtoleh _ _ I). *)
  assert (e : i + S (n - i - 1) = n).
  { intermediate_path (S i + (n - i - 1)).
    { change (S i) with (1+i). rewrite (natpluscomm 1 i). rewrite natplusassoc. reflexivity. }
    { change (S i) with (1 + i). rewrite (natpluscomm 1 i). rewrite natpluscomm.
      assert (t : n-i - 1 = n-(i+1)). { apply natsubsub. }
      rewrite t. apply minusplusnmm. rewrite natpluscomm. now apply natlthtolehsn. } }
  rewrite (transport_stnsum e).
  set (f' := λ l : stn (i + S(n - i - 1)), f (transportf stn e l)).
  exists (stnsum (f' ∘ (stn_left i (S(n - i - 1)))) + j).
  rewrite (stnsum_left_right _ _ f'). apply natlthandplusl.
  assert (K := stnsum_pos_0 (f' ∘ stn_right i (S (n - i - 1)))).
  assert (M : j < (f' ∘ stn_right i (S (n - i - 1))) (firstelement (n - i - 1))).
  { assert (D : f (i,, I) = (f' ∘ stn_right i (S (n - i - 1))) (firstelement (n - i - 1))).
    { unfold f', funcomp. apply maponpaths. apply subtypeEquality_prop. simpl.
      rewrite stn_right_first. rewrite transport_stn. simpl. reflexivity. }
    now rewrite (!D). }
  exact (natlthlehtrans j _ _ M K).
Defined.

Theorem weqstnsum1 { n : nat } (f : stn n -> nat) : (Σ i, stn (f i)) ≃ stn (stnsum f).
Proof.
  intros. induction n as [ | n IHn ].
  { simpl. apply weqtoempty2. { exact pr1. } exact negstn0. }
  refine (_ ∘ weqtotal2overcoprod _ ∘ invweq (weqfp (weqdnicoprod n (lastelement n)) (λ i, stn (f i))))%weq.
  intermediate_weq (stn (stnsum (λ i, f (weqdnicoprod n (lastelement n) (ii1 i)))) ⨿ stn (f(lastelement n))).
  { apply weqcoprodf.
    { apply IHn. }
    { apply weqtotal2overunit. } }
  exact (weqfromcoprodofstn _ _).
Defined.

Theorem weqstnsum { n : nat } (P : stn n -> UU) (f : stn n -> nat) :
  (Π i, stn (f i) ≃ P i) -> total2 P ≃ stn (stnsum f).
Proof.
  intros ? ? ? w.
  intermediate_weq (Σ i, stn (f i)).
  - apply invweq. now apply weqfibtototal.
  - apply weqstnsum1.
Defined.

Corollary weqstnsum2 { X : UU } ( n : nat ) ( f : stn n -> nat ) ( g : X -> stn n ) ( ww : Π i : stn n , weq ( stn ( f i ) ) ( hfiber g i ) ) : weq X ( stn ( stnsum f ) ) .
Proof. intros . assert ( w : weq X ( total2 ( fun i : stn n => hfiber g i ) ) ) . apply weqtococonusf . apply ( weqcomp w ( weqstnsum ( fun i : stn n => hfiber g i ) f ww ) ) .   Defined .

(** lexical enumeration of pairs of natural numbers *)

Definition lexicalEnumeration {n} (m:stn n->nat) := invweq (weqstnsum1 m) : stn (stnsum m) ≃ (Σ i : stn n, stn (m i)).
Definition inverse_lexicalEnumeration {n} (m:stn n->nat) := weqstnsum1 m : (Σ i : stn n, stn (m i)) ≃ stn (stnsum m).

Definition lex_curry {X n} (m:stn n->nat) : (stn (stnsum m) -> X) -> (Π (i:stn n), stn (m i) -> X).
Proof. intros ? ? ? f ? j. exact (f (inverse_lexicalEnumeration m (i,,j))). Defined.
Definition lex_uncurry {X n} (m:stn n->nat) : (Π (i:stn n), stn (m i) -> X) -> (stn (stnsum m) -> X).
Proof. intros ? ? ? g ij. exact (uncurry g (lexicalEnumeration m ij)). Defined.

(** two generalizations of stnsum, potentially useful *)

Definition foldleft {E} (e:E) (m:binop E) {n} (x:stn n -> E) : E.
Proof.
  intros.
  induction n as [|n foldleft].
  + exact e.
  + exact (m (foldleft (x ∘ (dni n (lastelement n)))) (x (lastelement n))).
Defined.

Definition foldright {E} (m:binop E) (e:E) {n} (x:stn n -> E) : E.
Proof.
  intros.
  induction n as [|n foldright].
  + exact e.
  + exact (m (x (firstelement _)) (foldright (x ∘ dni n (firstelement n)))).
Defined.

(** *** Weak equivalence between the direct product of [ stn n ] and [ stn m ] and [ stn n * m ] *)

Theorem weqfromprodofstn ( n m : nat ) : stn n × stn m ≃ stn (n * m).
Proof.
  intros.
  induction ( natgthorleh m 0 ) as [ is | i ] .
  - assert ( i1 : Π i j : nat, i < n -> j < m -> j + i * m < n * m).
    + intros i j li lj.
      apply (natlthlehtrans ( j + i * m ) ( ( S i ) * m ) ( n * m )).
      * change (S i * m) with (i*m + m).
        rewrite natpluscomm.
        exact (natgthandplusl m j ( i * m ) lj ).
      * exact ( natlehandmultr ( S i ) n m ( natgthtogehsn _ _ li ) ).
    + set ( f := fun ij : stn n × stn m =>
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
        assert ( eei : paths i i' ) .
        { apply ( pr1 ( natdivremunique m i j i' j' lj lj' ( maponpaths ( stntonat _ ) e ) ) ) . }
        set ( eeis := invmaponpathsincl _ ( isinclstntonat _ ) ( stnpair _ i li ) ( stnpair _ i' li' ) eei ) .
        assert ( eej : paths j j' ) .
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

Theorem weqfromdecsubsetofstn { n : nat } ( f : stn n -> bool ) : total2 ( fun x : nat => weq ( hfiber f true ) ( stn x ) ) .
Proof . intro . induction n as [ | n IHn ] . intros .    split with 0 .  assert ( g : ( hfiber f true ) -> ( stn 0 ) ) . intro hf . destruct hf as [ i e ] .  destruct ( weqstn0toempty i ) .  apply ( weqtoempty2 g weqstn0toempty ) . intro . set ( g := weqfromcoprodofstn 1 n ) .   change ( 1 + n ) with ( S n ) in g .

set ( fl := fun i : stn 1 => f ( g ( ii1 i ) ) ) .   set ( fh := fun i : stn n => f ( g ( ii2 i ) ) ) . assert ( w : weq ( hfiber f true ) ( hfiber ( sumofmaps fl fh ) true ) ) .  set ( int := invweq ( weqhfibersgwtog g f true  ) ) .  assert ( h : Π x : _ , paths ( f ( g x ) ) ( sumofmaps fl fh x ) ) . intro . destruct x as [ x1 | xn ] . apply idpath . apply idpath .   apply ( weqcomp int ( weqhfibershomot _ _ h true ) ) .  set ( w' := weqcomp w ( invweq ( weqhfibersofsumofmaps fl fh true ) ) ) .

set ( x0 := pr1 ( IHn fh ) ) . set ( w0 := pr2 ( IHn fh ) ) . simpl in w0 . destruct ( boolchoice ( fl ( lastelement 0 ) ) ) as [ i | ni ] .

split with ( S x0 ) .  assert ( wi : weq ( hfiber fl true ) ( stn 1 ) ) . assert ( is : iscontr ( hfiber fl true ) ) . apply iscontraprop1 . apply ( isinclfromstn1 fl isasetbool true ) .  apply ( hfiberpair _ ( lastelement 0 ) i ) . apply ( weqcontrcontr is iscontrstn1 ) .  apply ( weqcomp ( weqcomp w' ( weqcoprodf wi w0 ) ) ( weqfromcoprodofstn 1 _ ) ) .

split with x0 .  assert ( g' : neg ( hfiber fl true ) ) . intro hf . destruct hf as [ j e ] .  assert ( ee : paths j ( lastelement 0 ) ) . apply ( proofirrelevance _ ( isapropifcontr iscontrstn1 ) _ _ ) .  destruct ( nopathstruetofalse ( pathscomp0 ( pathscomp0 ( pathsinv0 e ) ( maponpaths fl ee ) ) ni ) ) .  apply ( weqcomp w' ( weqcomp ( invweq ( weqii2withneg _ g' ) ) w0 )  )  .  Defined .

(** *** Weak equivalences between hfibers of functions from [ stn n ] over isolated points and [ stn x ] *)

Theorem weqfromhfiberfromstn { n : nat } { X : UU } ( x : X ) ( is : isisolated X x ) ( f : stn n -> X ) : total2 ( fun x0 : nat => weq ( hfiber f x ) ( stn x0 ) ) .
Proof . intros .  set ( t := weqfromdecsubsetofstn ( fun i : _ => eqbx X x is ( f i ) ) ) . split with ( pr1 t ) . apply ( weqcomp ( weqhfibertobhfiber f x is ) ( pr2 t ) ) .   Defined .





(** *** Weak equivalence between [ stn n -> stn m ] and [ stn ( natpower m n ) ] ( uses functional extensionality ) *)


Theorem weqfromfunstntostn ( n m : nat ) : weq ( stn n -> stn m ) ( stn ( natpower m n ) ) .
Proof. intro n . induction n as [ | n IHn ] . intro m .  apply weqcontrcontr . apply ( iscontrfunfromempty2 _ weqstn0toempty ) .  apply iscontrstn1 .
intro m . set ( w1 := weqfromcoprodofstn 1 n ) . assert ( w2 : weq ( stn ( S n ) -> stn m ) ( (coprod (stn 1) (stn n)) -> stn m ) ) .   apply ( weqbfun _ w1  ) .  set ( w3 := weqcomp w2 ( weqfunfromcoprodtoprod ( stn 1 ) ( stn n ) ( stn m ) ) ) .   set ( w4 := weqcomp w3 ( weqdirprodf ( weqfunfromcontr ( stn m ) iscontrstn1 ) ( IHn m ) ) ) .  apply ( weqcomp w4 ( weqfromprodofstn m ( natpower m n ) ) ) .  Defined .





(** *** Weak equivalence from the space of functions of a family [ stn ( f x ) ]  over [ stn n ] to [ stn ( stnprod n f ) ] ( uses functional extensionality ) *)


Definition stnprod { n : nat } ( f : stn n -> nat ) : nat .
Proof. intro n . induction n as [ | n IHn ] . intro. apply 1 . intro f . apply (  ( IHn ( fun i : stn n => f ( dni n ( lastelement n ) i ) ) ) * f ( lastelement n ) ) . Defined .

Definition stnprod_step { n : nat } ( f : stn (S n) -> nat ) :
  stnprod f = stnprod (f ∘ dni n (lastelement n)) * f (lastelement n).
Proof. reflexivity. Defined.

Lemma stnprod_eq {n} (f g:stn n->nat) : f ~ g -> stnprod f = stnprod g.
Proof.
  intros ? ? ? h. induction n as [|n IH].
  { reflexivity. }
  rewrite 2? stnprod_step. induction (h (lastelement _)).
  apply (maponpaths (λ i, i * f (lastelement _))). apply IH. intro x. apply h.
Defined.

Theorem weqstnprod { n : nat } ( P : stn n -> UU ) ( f : stn n -> nat ) ( ww : Π i : stn n , weq ( stn ( f i ) )  ( P i ) ) : weq ( Π x : stn n , P x  ) ( stn ( stnprod f ) ) .
Proof .
  intro n .
  induction n as [ | n IHn ] .
  - intros . simpl . apply ( weqcontrcontr ) .
    + apply ( iscontrsecoverempty2 _ ( negstn0 ) ) .
    + apply iscontrstn1 .
  - intros .
    set ( w1 := weqdnicoprod n ( lastelement n ) ) .
    assert ( w2 := weqonsecbase P w1 ).
    assert ( w3 := weqsecovercoprodtoprod ( fun x : _ => P ( w1 x ) ) ) .
    assert ( w4 := weqcomp w2 w3 ) ; clear w2 w3.
    assert ( w5 := IHn ( fun x : stn n => P ( w1 ( ii1 x ) ) ) ( fun x : stn n => f ( w1 ( ii1 x ) ) ) ( fun i : stn n => ww ( w1 ( ii1 i ) ) ) ) .
    assert ( w6 := weqcomp w4 ( weqdirprodf w5 ( weqsecoverunit _ ) ) ) ; clear w4 w5.
    simpl in w6 .
    assert ( w7 := weqcomp w6 ( weqdirprodf ( idweq _ ) ( invweq ( ww ( lastelement n ) ) ) ) ) .
    refine ( _ ∘ w7 )%weq .
    unfold w1.
    exact (weqfromprodofstn _ _ ).
Defined .

(** *** Weak equivalence between [ weq ( stn n ) ( stn n ) ] and [ stn ( factorial n ) ] ( uses functional extensionality ) *)

Theorem weqweqstnsn ( n : nat ) : (stn(S n) ≃ stn (S n))  ≃  stn(S n) × ( stn n ≃ stn n ).
Proof.
  intro. assert ( l := lastelement n ) .
  intermediate_weq ( isolated (stn (S n)) × (compl _ l ≃ compl _ l) ).
  { apply weqcutonweq. intro i. apply isdeceqstn. }
  apply weqdirprodf.
  - apply weqisolatedstntostn.
  - apply weqweq. apply invweq.
    intermediate_weq (compl_ne (stn (S n)) l (stnneq l)).
    + apply weqdnicompl.
    + apply compl_weq_compl_ne.
Defined .

Theorem weqfromweqstntostn ( n : nat ) : weq ( weq ( stn n ) ( stn n ) ) ( stn ( factorial n ) ) .
Proof . intro . induction n as [ | n IHn ] . simpl . apply ( weqcontrcontr ) . apply ( iscontraprop1 ) .    apply ( isapropweqtoempty2 _ ( negstn0 ) ) .  apply idweq . apply iscontrstn1 . change ( factorial ( S n ) ) with ( ( S n ) * ( factorial n ) ) .   set ( w1 := weqweqstnsn n ) . apply ( weqcomp w1 ( weqcomp ( weqdirprodf ( idweq _ ) IHn ) ( weqfromprodofstn _ _ ) ) ) .  Defined .


(* End of " weak equivalences between standard finite sets and constructions on these sets " . *)







(** ** Standard finite sets satisfy weak axiom of choice *)

Theorem ischoicebasestn ( n : nat ) : ischoicebase ( stn n ) .
Proof . intro . induction n as [ | n IHn ] .  apply ( ischoicebaseempty2 negstn0 ) .  apply ( ischoicebaseweqf ( weqdnicoprod n ( lastelement n ) ) ( ischoicebasecoprod IHn ischoicebaseunit ) ) .  Defined .







(** ** Weak equivalence class of [ stn n ] determines [ n ] . *)


Lemma negweqstnsn0 (n:nat): neg (weq (stn (S n)) (stn O)).
Proof. unfold neg. intro. assert (lp: stn (S n)). apply lastelement.  intro X.  apply weqstn0toempty .  apply (pr1 X lp). Defined.

Lemma negweqstn0sn (n:nat): neg (weq (stn O) (stn (S n))).
Proof.  unfold neg. intro. assert (lp: stn (S n)). apply lastelement.  intro X.  apply weqstn0toempty .  apply (pr1 ( invweq X ) lp). Defined.

Lemma weqcutforstn ( n n' : nat ) : stn (S n) ≃ stn (S n') -> stn n ≃ stn n'.
Proof.
  intros ? ? w. assert ( k := lastelement n  ).
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

Corollary stnsdnegweqtoeq ( n n' : nat ) ( dw : dneg (weq (stn n) (stn n')) ) : paths n n'.
Proof. intros n n' X. apply (eqfromdnegeq nat isdeceqnat _ _  (dnegf (@weqtoeqstn n n') X)). Defined.

(** ** Some results on bounded quantification *)


Lemma weqforallnatlehn0 ( F : nat -> hProp ) : weq ( Π n : nat , natleh n 0 -> F n ) ( F 0 ) .
Proof . intros .  assert ( lg : ( Π n : nat , natleh n 0 -> F n ) <-> ( F 0 ) ) . split . intro f .  apply ( f 0 ( isreflnatleh 0 ) ) .  intros f0 n l .  set ( e := natleh0tois0 l ) .  rewrite e .  apply f0 . assert ( is1 : isaprop ( Π n : nat , natleh n 0 -> F n ) ) . apply impred . intro n . apply impred .   intro l .  apply ( pr2 ( F n ) ) .  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) is1 ( pr2 ( F 0 ) ) ) . Defined .

Lemma weqforallnatlehnsn' ( n' : nat ) ( F : nat -> hProp ) : weq ( Π n : nat , natleh n ( S n' ) -> F n ) ( dirprod ( Π n : nat , natleh n n' -> F n ) ( F ( S n' ) ) ) .
Proof . intros . assert ( lg : ( Π n : nat , natleh n ( S n' ) -> F n ) <-> dirprod ( Π n : nat , natleh n n' -> F n ) ( F ( S n' ) ) ) .  split . intro f.  apply ( dirprodpair ( fun n => fun l => ( f n ( natlehtolehs _ _ l ) ) ) ( f ( S n' ) ( isreflnatleh _ ) ) ) .  intro d2 . intro n .  intro l .  destruct ( natlehchoice2 _ _ l ) as [ h | e ] . simpl in h .  apply ( pr1 d2 n h ) . destruct d2 as [ f2 d2 ] .  rewrite e .  apply d2 . assert ( is1 : isaprop ( Π n : nat , natleh n ( S n' ) -> F n ) ) . apply impred . intro n . apply impred . intro l . apply ( pr2 ( F n ) ) . assert ( is2 : isaprop ( dirprod ( Π n : nat , natleh n n' -> F n ) ( F ( S n' ) ) ) ) . apply isapropdirprod . apply impred . intro n . apply impred . intro l . apply ( pr2 ( F n ) ) .   apply ( pr2 ( F ( S n' ) ) ) .  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) is1 is2 ) . Defined .

Lemma weqexistsnatlehn0 ( P : nat -> hProp  ) : weq ( hexists ( fun n : nat => dirprod ( natleh n 0 ) ( P n ) ) ) ( P 0 ) .
Proof . intro . assert ( lg : hexists ( fun n : nat => dirprod ( natleh n 0 ) ( P n ) ) <-> P 0  ) . split .  simpl . apply ( @hinhuniv _ ( P 0 ) ) .  intro t2 .  destruct t2 as [ n d2 ] . destruct d2 as [ l p ] . set ( e := natleh0tois0 l ) . clearbody e .  destruct e . apply p . intro p . apply hinhpr . split with 0 .  split with ( isreflnatleh 0 ) .  apply p . apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) ( pr2 _ ) ( pr2 _ ) ) .  Defined .

Lemma weqexistsnatlehnsn' ( n' : nat ) ( P : nat -> hProp  ) : weq ( hexists ( fun n : nat => dirprod ( natleh n ( S n' ) ) ( P n ) ) ) ( hdisj ( hexists ( fun n : nat => dirprod ( natleh n n' ) ( P n ) ) )  ( P ( S n' ) ) ) .
Proof . intros . assert ( lg : hexists ( fun n : nat => dirprod ( natleh n ( S n' ) ) ( P n ) )  <-> hdisj ( hexists ( fun n : nat => dirprod ( natleh n n' ) ( P n ) ) )  ( P ( S n' ) )  ) . split . apply hinhfun .   intro t2 .  destruct t2 as [ n d2 ] . destruct d2 as [ l p ] . destruct ( natlehchoice2 _ _ l ) as [ h | nh ] . simpl in h . apply ii1 .  apply hinhpr . split with n .  apply ( dirprodpair h p ) . destruct nh .  apply ( ii2 p ) . simpl . apply ( @hinhuniv _ ( ishinh _ ) ) . intro c .  destruct c as [ t | p ] .  generalize t . simpl . apply hinhfun .  clear t . intro t . destruct t as [ n d2 ] . destruct d2 as [ l p ] . split with n .  split with ( natlehtolehs _ _ l ) .  apply p .  apply hinhpr . split with ( S n' ) .  split with ( isreflnatleh _ ) . apply p .  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) ( pr2 _ ) ( pr2 _ ) ) .  Defined .


Lemma isdecbexists ( n : nat ) ( P : nat -> UU ) ( is : Π n' , isdecprop ( P n' ) ) : isdecprop ( hexists ( fun n' => dirprod ( natleh n' n ) ( P n' ) ) ) .
Proof . intros .  set ( P' := fun n' : nat => hProppair _ ( is n' ) ) . induction n as [ | n IHn ] . apply ( isdecpropweqb ( weqexistsnatlehn0 P' ) ) . apply ( is 0 ) .   apply ( isdecpropweqb ( weqexistsnatlehnsn' _ P' ) ) . apply isdecprophdisj . apply IHn . apply ( is ( S n ) ) . Defined .

Lemma isdecbforall ( n : nat ) ( P : nat -> UU ) ( is : Π n' , isdecprop ( P n' ) ) : isdecprop ( Π n' , natleh n' n -> P n' )  .
Proof . intros .  set ( P' := fun n' : nat => hProppair _ ( is n' ) ) . induction n as [ | n IHn ] . apply ( isdecpropweqb ( weqforallnatlehn0 P' ) ) . apply ( is 0 ) .   apply ( isdecpropweqb ( weqforallnatlehnsn' _ P' ) ) . apply isdecpropdirprod . apply IHn . apply ( is ( S n ) ) . Defined .



(** The following lemma finds the largest [ n' ] such that [ neg ( P n' ) ] . It is a stronger form of ( neg Π ) -> ( exists neg ) in the case of bounded quantification of decidable propositions. *)

Lemma negbforalldectototal2neg ( n : nat ) ( P : nat -> UU ) ( is : Π n' : nat , isdecprop ( P n' ) ) : neg ( Π n' : nat , natleh n' n -> P n' ) -> total2 ( fun n' => dirprod ( natleh n' n ) ( neg ( P n' ) ) ) .
Proof . intros n P is . set ( P' := fun n' : nat => hProppair _ ( is n' ) ) . induction n as [ | n IHn ] . intro nf . set ( nf0 := negf ( invweq ( weqforallnatlehn0 P' ) ) nf ) . split with 0 . apply ( dirprodpair ( isreflnatleh 0 ) nf0 ) .   intro nf . set ( nf2 := negf ( invweq ( weqforallnatlehnsn' n P' ) ) nf ) . set ( nf3 := fromneganddecy ( is ( S n ) ) nf2 ) . destruct nf3 as [ f1 | f2 ] . set ( int := IHn f1 ) .  destruct int as [ n' d2 ] . destruct d2 as [ l np ] . split with n' .  split with ( natlehtolehs _ _ l ) .  apply np . split with ( S n ) . split with ( isreflnatleh _ ) . apply f2 .  Defined .


(** ** Accessibility - the least element of an inhabited decidable subset of [nat] *)

Definition natdecleast ( F : nat -> UU ) ( is : Π n , isdecprop ( F n ) ) := total2 ( fun  n : nat => dirprod ( F n ) ( Π n' : nat , F n' -> natleh n n' ) ) .

Lemma isapropnatdecleast ( F : nat -> UU ) ( is : Π n , isdecprop ( F n ) ) : isaprop ( natdecleast F is ) .
Proof . intros . set ( P := fun n' : nat => hProppair _ ( is n' ) ) . assert ( int1 : Π n : nat, isaprop ( dirprod ( F n ) ( Π n' : nat , F n' -> natleh n n' ) ) ) .  intro n . apply isapropdirprod . apply ( pr2 ( P n ) ) .  apply impred . intro t .  apply impred .  intro .  apply ( pr2 ( natleh n t ) ) . set ( int2 := ( fun n : nat => hProppair _ ( int1 n ) ) : nat -> hProp ) .   change ( isaprop ( total2 int2 ) ) . apply isapropsubtype . intros x1 x2 .  intros c1 c2 . simpl in * . destruct c1 as [ e1 c1 ] . destruct c2 as [ e2 c2 ] . set ( l1 := c1 x2 e2 ) .  set ( l2 := c2 x1 e1 ) . apply ( isantisymmnatleh _ _ l1 l2 ) .  Defined .

Theorem accth ( F : nat -> UU ) ( is : Π n , isdecprop ( F n ) )  ( is' : hexists F ) : natdecleast F is .
Proof . intros F is . simpl . apply (@hinhuniv _ ( hProppair _ ( isapropnatdecleast F is ) ) ) . intro t2. destruct t2 as [ n l ] . simpl .

set ( F' := fun n' : nat => hexists ( fun n'' => dirprod ( natleh n'' n' ) ( F n'' ) ) ) .  assert ( X : Π n' , F' n' -> natdecleast F is ) .  intro n' .  simpl .    induction n' as [ | n' IHn' ] . apply ( @hinhuniv _  ( hProppair _ ( isapropnatdecleast F is ) ) ) . simpl .   intro t2 . destruct t2 as [ n'' is'' ] . destruct is'' as [ l'' d'' ] .  split with 0 .  split . set ( e := natleh0tois0 l'' ) . clearbody e . destruct e . apply d'' .  apply ( fun n' => fun f : _ => natleh0n n' ) .  apply ( @hinhuniv _  ( hProppair _ ( isapropnatdecleast F is ) ) ) . intro t2 .  destruct t2 as [ n'' is'' ] . set ( j := natlehchoice2 _ _ ( pr1 is'' ) ) .  destruct j as [ jl | je ] .  simpl .  apply ( IHn' ( hinhpr ( tpair _ n'' ( dirprodpair jl ( pr2 is'' ) ) ) ) ) .  simpl . rewrite je in is''  .  destruct is'' as [ nn is'' ] .  clear nn. clear je . clear n'' .

assert ( is' : isdecprop ( F' n' ) ) . apply ( isdecbexists n' F is ) .   destruct ( pr1 is' ) as [ f | nf ] .  apply ( IHn'  f ) .  split with ( S n' ) .  split with is'' . intros n0 fn0 . destruct ( natlthorgeh n0 ( S n' ) )  as [ l' | g' ] .  set ( i' := natlthtolehsn _ _ l' ) .  destruct ( nf ( hinhpr ( tpair _ n0 ( dirprodpair i' fn0 ) ) ) ) .   apply g' .

apply ( X n ( hinhpr ( tpair _ n ( dirprodpair ( isreflnatleh n ) l ) ) ) ) .  Defined .

Lemma isinjstntonat n : isInjectiveFunction (pr1 : stnset n -> natset).
Proof. intros ? i j. apply (invmaponpathsincl pr1). apply isinclstntonat. Defined.

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

Corollary dni_lastelement_eq : Π (n : nat) (i : stn (S n)) (ie : pr1 i < n),
    i = dni_lastelement (stnpair n (pr1 i) ie).
Proof.
  intros n i ie.
  apply isinjstntonat.
  apply idpath.
Defined.

Corollary lastelement_eq : Π (n : nat) (i : stn (S n)) (e : pr1 i = n),
    i = lastelement n.
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

(** general associativity for addition in nat *)

Theorem nat_plus_associativity {n} {m:stn n->nat} (k:Π (ij : Σ i, stn (m i)), nat) :
  stnsum (λ i, stnsum (curry k i)) = stnsum (k ∘ lexicalEnumeration m).
Proof.
  intros. apply weqtoeqstn.
  intermediate_weq (Σ i, stn (stnsum (curry k i))).
  { apply invweq. apply weqstnsum1. }
  intermediate_weq (Σ i j, stn (curry k i j)).
  { apply weqfibtototal; intro i. apply invweq. apply weqstnsum1. }
  intermediate_weq (Σ ij, stn (k ij)).
  { exact (weqtotal2asstol (stn ∘ m) (stn ∘ k)). }
  intermediate_weq (Σ ij, stn (k (lexicalEnumeration m ij))).
  { apply (weqbandf (inverse_lexicalEnumeration m)). intro ij. apply eqweqmap.
    apply (maponpaths stn), (maponpaths k). apply pathsinv0, homotinvweqweq. }
  { apply inverse_lexicalEnumeration. }
Defined.

Corollary nat_plus_associativity' n (m:stn n->nat) (k:Π i, stn (m i) -> nat) :
  stnsum (λ i, stnsum (k i)) = stnsum (uncurry k ∘ lexicalEnumeration m).
Proof. intros. exact (nat_plus_associativity (uncurry k)). Defined.

(** general commutativity for addition in nat *)

Theorem nat_plus_commutativity {n} (x:stn n -> nat)
        (f:stn n ≃ stn n) : stnsum x = stnsum (x∘f).
Proof.
  intros. apply weqtoeqstn. intermediate_weq (Σ i, stn (x i)).
  { apply invweq. apply weqstnsum1. }
  intermediate_weq (Σ i, stn (x(f i))).
  { apply invweq. apply (weqfp _ (stn∘x)). }
  apply weqstnsum1.
Defined.


Definition stn_predicate {n : nat} (P : stn n -> UU)
           (k : nat) (h h' : k < n) :
           P (k,,h) -> P (k,,h').
Proof.
  intros n P k h h' H.
  transparent assert (X : (h = h')).
  { apply propproperty. }
  exact (transportf (fun x => P (k,,x)) X H).
Defined.

Definition two := stn 2.

Definition two_rec {A : UU} (a b : A) : stn 2 -> A.
Proof.
  intros A a b.
  induction 1 as [n p].
  induction n as [_|n _]; [apply a|].
  induction n as [_|n _]; [apply b|].
  induction (nopathsfalsetotrue p).
Defined.

Definition two_rec_dep (P : two -> UU):
  P (● 0) -> P (● 1) -> Π n, P n.
Proof.
  intros P a b n.
  induction n as [n p].
  induction n as [_|n _]. eapply stn_predicate. apply a.
  induction n as [_|n _]. eapply stn_predicate. apply b.
  induction (nopathsfalsetotrue p).
Defined.

Definition three := stn 3.

Definition three_rec {A : UU} (a b c : A) : stn 3 -> A.
Proof.
  intros A a b c.
  induction 1 as [n p].
  induction n as [_|n _]; [apply a|].
  induction n as [_|n _]; [apply b|].
  induction n as [_|n _]; [apply c|].
  induction (nopathsfalsetotrue p).
Defined.

Definition three_rec_dep (P : three -> UU):
  P (● 0) -> P (● 1) -> P (● 2) -> Π n, P n.
Proof.
  intros P a b c n.
  induction n as [n p].
  induction n as [_|n _]. eapply stn_predicate. apply a.
  induction n as [_|n _]. eapply stn_predicate. apply b.
  induction n as [_|n _]. eapply stn_predicate. apply c.
  induction (nopathsfalsetotrue p).
Defined.
