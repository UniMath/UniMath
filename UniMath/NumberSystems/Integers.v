(** * Generalities on the type of integers and integer arithmetic. Vladimir Voevodsky . Aug. - Sep. 2011.

In this file we introduce the type [ hz ] of integers defined as the quotient set of [ dirprod nat nat ] by the standard equivalence relation and develop the main notions of the integer arithmetic using this definition .


*)



(** ** Preamble *)

(** Settings *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Unset Kernel Term Sharing.

(** Imports *)

Require Export UniMath.Foundations.NaturalNumbers .
Require Export UniMath.Algebra.Rigs_and_Rings.
Require Export UniMath.NumberSystems.NaturalNumbersAlgebra.


(** Upstream *)




(** ** The commutative ring [ hz ] of integres *)

(** *** General definitions *)


Definition hz : commrng := commrigtocommrng natcommrig .
Definition hzaddabgr : abgr := hz .
Definition hzmultabmonoid : abmonoid := rngmultabmonoid hz .

Definition natnattohz : nat -> nat -> hz := λ n m, setquotpr _ ( dirprodpair n m ) .

Definition hzplus : hz -> hz -> hz := @op1 hz.
Definition hzsign : hz -> hz := grinv hzaddabgr .
Definition hzminus : hz -> hz -> hz := λ x y, hzplus x ( hzsign y ) .
Definition hzzero : hz := unel hzaddabgr .

Definition hzmult : hz -> hz -> hz := @op2 hz .
Definition hzone : hz := unel hzmultabmonoid .

Bind Scope hz_scope with hz .
Notation " x + y " := ( hzplus x y ) : hz_scope .
Notation " 0 " := hzzero : hz_scope .
Notation " 1 " := hzone : hz_scope .
Notation " - x " := ( hzsign x ) : hz_scope .
Notation " x - y " := ( hzminus x y ) : hz_scope .
Notation " x * y " := ( hzmult x y ) : hz_scope .

Delimit Scope hz_scope with hz .


(** *** Properties of equlaity on [ hz ] *)

Theorem isdeceqhz : isdeceq hz .
Proof . change ( isdeceq ( abgrdiff ( rigaddabmonoid natcommrig ) ) ) . apply isdeceqabgrdiff . apply isinclnatplusr .  apply isdeceqnat .  Defined .
Opaque isdeceqhz.

Lemma isasethz : isaset hz .
Proof . apply ( setproperty hzaddabgr ) . Defined .
Opaque isasethz.

Definition hzeq ( x y : hz ) : hProp := hProppair ( x = y ) ( isasethz _ _  )  .
Definition isdecrelhzeq : isdecrel hzeq  := λ a b, isdeceqhz a b .
Definition hzdeceq : decrel hz := decrelpair isdecrelhzeq .

(* Canonical Structure hzdeceq. *)

Definition hzbooleq := decreltobrel hzdeceq .

Definition hzneq ( x y : hz ) : hProp := hProppair ( neg ( x = y ) ) ( isapropneg _  )  .
Definition isdecrelhzneq : isdecrel hzneq  := isdecnegrel _ isdecrelhzeq .
Definition hzdecneq : decrel hz := decrelpair isdecrelhzneq .

(* Canonical Structure hzdecneq. *)

Definition hzboolneq := decreltobrel hzdecneq .


Local Open Scope hz_scope .


(** *** [ hz ] is a non-zero ring *)

Lemma isnonzerornghz : isnonzerorng hz .
Proof . apply  ( ct ( hzneq , isdecrelhzneq, 1 , 0 ) ) . Defined .


(** *** Properties of addition and subtraction on [ hz ] *)

Definition hzminuszero : ( - 0 ) = 0 := rnginvunel1 hz .

Lemma hzplusr0 ( x : hz ) : ( x + 0 ) = x .
Proof . intro . apply ( rngrunax1 _ x ) .  Defined .

Lemma hzplusl0 ( x : hz ) : ( 0 + x ) = x .
Proof . intro . apply ( rnglunax1 _ x ) . Defined .

Lemma hzplusassoc ( x y z : hz ) : ( ( x + y ) + z ) = ( x + ( y + z ) ) .
Proof . intros . apply ( rngassoc1 hz x y z ) . Defined .

Lemma hzpluscomm ( x y : hz ) : ( x + y ) = ( y + x ) .
Proof . intros .  apply ( rngcomm1 hz x y ) . Defined .

Lemma hzlminus ( x : hz ) : ( -x + x ) = 0 .
Proof . intro. apply ( rnglinvax1 hz x ) . Defined .

Lemma hzrminus  ( x : hz ) : ( x - x ) = 0 .
Proof . intro. apply ( rngrinvax1 hz x ) . Defined .

Lemma isinclhzplusr ( n : hz ) : isincl ( λ m : hz, m + n ) .
Proof. intro . apply ( pr2 ( weqtoincl _ _ ( weqrmultingr hzaddabgr n ) ) ) . Defined.

Lemma isinclhzplusl ( n : hz ) : isincl ( λ m : hz, n + m ) .
Proof.  intro.  apply ( pr2 ( weqtoincl _ _ ( weqlmultingr hzaddabgr n ) ) ) . Defined .

Lemma hzpluslcan ( a b c : hz ) ( is : ( c + a ) = ( c + b ) ) : a = b .
Proof . intros . apply ( @grlcan hzaddabgr a b c is ) .  Defined .

Lemma hzplusrcan ( a b c : hz ) ( is : ( a + c ) = ( b + c ) ) : a = b .
Proof . intros . apply ( @grrcan hzaddabgr a b c is ) .  Defined .

Lemma hzplusradd (a b c : hz) (is : a = b) : (a + c) = (b + c).
Proof. intros. induction is. apply idpath. Defined.

Lemma hzplusladd (a b c : hz) (is : a = b) : (c + a) = (c + b).
Proof. intros. apply maponpaths. apply is. Defined.

Definition hzinvmaponpathsminus { a b : hz } ( e : ( - a ) = ( - b ) ) : a = b := grinvmaponpathsinv hzaddabgr e .

Lemma hzrplusminus (n m : hz) : n + m - m = n.
Proof.
  intros n m. unfold hzminus, hzplus, hzplus. rewrite rngassoc1.
  set (tmp := hzrminus m). unfold hzminus, hzplus in tmp. rewrite tmp. clear tmp.
  apply hzplusr0.
Defined.
Opaque hzrplusminus.

Lemma hzrplusminus' (n m : hz) : n = n + m - m.
Proof.
  intros n m. apply pathsinv0. apply hzrplusminus.
Defined.
Opaque hzrplusminus'.

Lemma hzrminusplus (n m : hz) : n - m + m = n.
Proof.
  intros n m. unfold hzplus, hzminus. rewrite rngassoc1.
  rewrite hzlminus. apply hzplusr0.
Defined.
Opaque hzrminusplus.


Lemma hzrminusplus' (n m : hz) : n = n - m + m.
Proof.
  intros n m. apply pathsinv0. apply hzrminusplus.
Defined.
Opaque hzrminusplus'.

(** *** Properties of multiplication on [ hz ] *)


Lemma hzmultr1 ( x : hz ) : ( x * 1 ) = x .
Proof . intro . apply ( rngrunax2 _ x ) .  Defined .

Lemma hzmultl1 ( x : hz ) : ( 1 * x ) = x .
Proof . intro . apply ( rnglunax2 _ x ) . Defined .

Lemma hzmult0x ( x : hz ) : ( 0 * x ) = 0 .
Proof . intro . apply ( rngmult0x _ x ) .  Defined .

Lemma hzmultx0 ( x : hz ) : ( x * 0 ) = 0 .
Proof . intro . apply ( rngmultx0 _ x ) . Defined .

Lemma hzmultassoc ( x y z : hz ) : ( ( x * y ) * z ) = ( x * ( y * z ) ) .
Proof . intros . apply ( rngassoc2 hz x y z ) . Defined .

Lemma hzmultcomm ( x y : hz ) : ( x * y ) = ( y * x ) .
Proof . intros .  apply ( rngcomm2 hz  x y ) . Defined .

Definition hzneq0andmultlinv ( n m : hz ) ( isnm : hzneq ( n * m ) 0 ) : hzneq n 0 := rngneq0andmultlinv hz n m isnm .

Definition hzneq0andmultrinv ( n m : hz ) ( isnm : hzneq ( n * m ) 0 ) : hzneq m 0 := rngneq0andmultrinv hz n m isnm .



(** ** Definition and properties of "greater", "less", "greater or equal" and "less or equal" on [ hz ] . *)


(** *** Definitions and notations *)

Definition hzgth : hrel hz := rigtorngrel natcommrig isplushrelnatgth .

Definition hzlth : hrel hz := λ a b, hzgth b a .

Definition hzleh : hrel hz := λ a b, hProppair ( neg ( hzgth a b ) ) ( isapropneg _ )  .

Definition hzgeh : hrel hz := λ a b, hProppair ( neg ( hzgth b a ) ) ( isapropneg _ )  .

(** *** Decidability *)


Lemma isdecrelhzgth : isdecrel hzgth .
Proof . apply ( isdecrigtorngrel natcommrig isplushrelnatgth  ) .  apply isinvplushrelnatgth . apply isdecrelnatgth . Defined .

Definition hzgthdec := decrelpair isdecrelhzgth .

(* Canonical Structure hzgthdec . *)

Definition isdecrelhzlth : isdecrel hzlth := λ x x', isdecrelhzgth x' x .

Definition hzlthdec := decrelpair isdecrelhzlth .

(* Canonical Structure hzlthdec . *)

Definition isdecrelhzleh : isdecrel hzleh := isdecnegrel _ isdecrelhzgth .

Definition hzlehdec := decrelpair isdecrelhzleh .

(* Canonical Structure hzlehdec . *)

Definition isdecrelhzgeh : isdecrel hzgeh := λ x x', isdecrelhzleh x' x .

Definition hzgehdec := decrelpair isdecrelhzgeh .

(* Canonical Structure hzgehdec . *)


(** *** Properties of individual relations *)

(** [ hzgth ] *)



Lemma istranshzgth ( n m k : hz ) : hzgth n m -> hzgth m k -> hzgth n k .
Proof. apply ( istransabgrdiffrel nataddabmonoid isplushrelnatgth )  .  unfold istrans .  apply istransnatgth .  Defined.

Lemma isirreflhzgth ( n : hz ) : neg ( hzgth n n ) .
Proof. apply ( isirreflabgrdiffrel nataddabmonoid isplushrelnatgth )  . unfold isirrefl .  apply isirreflnatgth .   Defined .

Lemma hzgthtoneq ( n m : hz ) ( g : hzgth n m ) : neg ( n = m ) .
Proof . intros . intro e . rewrite e in g . apply ( isirreflhzgth _ g ) . Defined .

Lemma isasymmhzgth ( n m : hz ) : hzgth n m -> hzgth m n -> empty .
Proof. apply ( isasymmabgrdiffrel nataddabmonoid isplushrelnatgth )  . unfold isasymm .  apply isasymmnatgth .  Defined .

Lemma isantisymmneghzgth ( n m : hz ) : neg ( hzgth n m ) -> neg ( hzgth m n ) -> n = m .
Proof . apply ( isantisymmnegabgrdiffrel nataddabmonoid isplushrelnatgth )  . unfold isantisymmneg .  apply isantisymmnegnatgth .   Defined .

Lemma isnegrelhzgth : isnegrel hzgth .
Proof . apply isdecreltoisnegrel . apply isdecrelhzgth . Defined .

Lemma iscoantisymmhzgth ( n m : hz ) : neg ( hzgth n m ) -> ( hzgth m n ) ⨿ ( n = m ) .
Proof . apply isantisymmnegtoiscoantisymm . apply isdecrelhzgth .  intros n m . apply isantisymmneghzgth . Defined .

Lemma iscotranshzgth ( n m k : hz ) : hzgth n k -> hdisj ( hzgth n m ) ( hzgth m k ) .
Proof . intros x y z gxz .  destruct ( isdecrelhzgth x y ) as [ gxy | ngxy ] . apply ( hinhpr ( ii1 gxy ) ) . apply hinhpr .   apply ii2 .  destruct ( isdecrelhzgth y x ) as [ gyx | ngyx ] . apply ( istranshzgth _ _ _ gyx gxz ) .  set ( e := isantisymmneghzgth _ _ ngxy ngyx ) . rewrite e in gxz .  apply gxz .  Defined .




(** [ hzlth ] *)


Definition istranshzlth ( n m k  : hz ) : hzlth n m -> hzlth m k -> hzlth n k := λ lnm lmk, istranshzgth _ _ _ lmk lnm .

Definition isirreflhzlth ( n : hz ) : neg ( hzlth n n ) := isirreflhzgth n .

Lemma hzlthtoneq ( n m : hz ) ( g : hzlth n m ) : neg ( n = m ) .
Proof . intros . intro e . rewrite e in g . apply ( isirreflhzlth _ g ) . Defined .

Definition isasymmhzlth ( n m : hz ) : hzlth n m -> hzlth m n -> empty := λ lnm lmn, isasymmhzgth _ _ lmn lnm .

Definition isantisymmneghztth  ( n m : hz ) : neg ( hzlth n m ) -> neg ( hzlth m n ) -> n = m := λ nlnm nlmn, isantisymmneghzgth _ _ nlmn nlnm .

Definition isnegrelhzlth : isnegrel hzlth := λ n m, isnegrelhzgth m n .

Definition iscoantisymmhzlth ( n m : hz ) : neg ( hzlth n m ) -> ( hzlth m n ) ⨿ ( n = m ) .
Proof . intros n m nlnm . destruct ( iscoantisymmhzgth m n nlnm ) as [ l | e ] . apply ( ii1 l ) . apply ( ii2 ( pathsinv0 e ) ) . Defined .

Definition iscotranshzlth ( n m k : hz ) : hzlth n k -> hdisj ( hzlth n m ) ( hzlth m k ) .
Proof . intros n m k lnk . apply ( ( pr1 islogeqcommhdisj ) ( iscotranshzgth _ _ _ lnk ) )  .  Defined .



(**  [ hzleh ] *)


Definition  istranshzleh ( n m k : hz ) : hzleh n m -> hzleh m k -> hzleh n k .
Proof. apply istransnegrel . unfold iscotrans. apply iscotranshzgth .  Defined.

Definition isreflhzleh ( n : hz ) : hzleh n n := isirreflhzgth n .

Definition isantisymmhzleh ( n m : hz ) : hzleh n m -> hzleh m n -> n = m := isantisymmneghzgth n m .

Definition isnegrelhzleh : isnegrel hzleh .
Proof . apply isdecreltoisnegrel . apply isdecrelhzleh . Defined .

Definition iscoasymmhzleh ( n m : hz ) ( nl : neg ( hzleh n m ) ) : hzleh m n := negf ( isasymmhzgth _ _ ) nl .

Definition istotalhzleh : istotal hzleh .
Proof . intros x y . destruct ( isdecrelhzleh x y ) as [ lxy | lyx ] . apply ( hinhpr ( ii1 lxy ) ) . apply hinhpr .   apply ii2 . apply ( iscoasymmhzleh _ _ lyx ) .   Defined .



(**  [ hzgeh ] . *)


Definition istranshzgeh ( n m k : hz ) : hzgeh n m -> hzgeh m k -> hzgeh n k := λ gnm gmk, istranshzleh _ _ _ gmk gnm .

Definition isreflhzgeh ( n : hz ) : hzgeh n n := isreflhzleh _ .

Definition isantisymmhzgeh ( n m : hz ) : hzgeh n m -> hzgeh m n -> n = m := λ gnm gmn, isantisymmhzleh _ _ gmn gnm .

Definition isnegrelhzgeh : isnegrel hzgeh := λ n m, isnegrelhzleh m n .

Definition iscoasymmhzgeh ( n m : hz ) ( nl : neg ( hzgeh n m ) ) : hzgeh m n := iscoasymmhzleh _ _ nl .

Definition istotalhzgeh : istotal hzgeh := λ n m, istotalhzleh m n .




(** *** Simple implications between comparisons *)

Definition hzgthtogeh ( n m : hz ) : hzgth n m -> hzgeh n m .
Proof. intros n m g . apply iscoasymmhzgeh . apply ( todneg _ g ) . Defined .

Definition hzlthtoleh ( n m : hz ) : hzlth n m -> hzleh n m := hzgthtogeh _ _ .

Definition hzlehtoneghzgth ( n m : hz ) : hzleh n m -> neg ( hzgth n m )  .
Proof. intros n m is is' . apply ( is is' ) .  Defined .

Definition  hzgthtoneghzleh ( n m : hz ) : hzgth n m -> neg ( hzleh n m ) := λ g l , hzlehtoneghzgth _ _ l g .

Definition hzgehtoneghzlth ( n m : hz ) : hzgeh n m -> neg ( hzlth n m ) := λ gnm lnm, hzlehtoneghzgth _ _ gnm lnm .

Definition hzlthtoneghzgeh ( n m : hz ) : hzlth n m -> neg ( hzgeh n m ) := λ gnm lnm, hzlehtoneghzgth _ _ lnm gnm .

Definition neghzlehtogth ( n m : hz ) : neg ( hzleh n m ) -> hzgth n m := isnegrelhzgth n m .

Definition neghzgehtolth ( n m : hz ) : neg ( hzgeh n m ) -> hzlth n m := isnegrelhzlth n m .

Definition neghzgthtoleh ( n m : hz ) : neg ( hzgth n m ) -> hzleh n m .
Proof . intros n m ng . destruct ( isdecrelhzleh n m ) as [ l | nl ] . apply l . destruct ( nl ng ) .  Defined .

Definition neghzlthtogeh ( n m : hz ) : neg ( hzlth n m ) -> hzgeh n m := λ nl, neghzgthtoleh _ _ nl .



(** *** Comparison alternatives *)


Definition hzgthorleh ( n m : hz ) : ( hzgth n m ) ⨿ ( hzleh n m ) .
Proof . intros . apply ( isdecrelhzgth n m ) .  Defined .

Definition hzlthorgeh ( n m : hz ) : ( hzlth n m ) ⨿ ( hzgeh n m ) := hzgthorleh _ _ .

Definition hzneqchoice ( n m : hz ) ( ne : neg ( n = m ) ) : ( hzgth n m ) ⨿ ( hzlth n m ) .
Proof . intros . destruct ( hzgthorleh n m ) as [ g | l ]  .  destruct ( hzlthorgeh n m ) as [ g' | l' ] . destruct ( isasymmhzgth _ _ g g' )  .  apply ( ii1 g ) . destruct ( hzlthorgeh n m ) as [ l' | g' ] . apply ( ii2 l' ) . destruct ( ne ( isantisymmhzleh _ _ l g' ) ) . Defined .

Definition hzlehchoice ( n m : hz ) ( l : hzleh n m ) : ( hzlth n m ) ⨿ ( n = m ) .
Proof .  intros . destruct ( hzlthorgeh n m ) as [ l' | g ] .   apply ( ii1 l' ) . apply ( ii2 ( isantisymmhzleh _ _ l g ) ) . Defined .

Definition hzgehchoice ( n m : hz ) ( g : hzgeh n m ) : ( hzgth n m ) ⨿ ( n = m ) .
Proof .  intros . destruct ( hzgthorleh n m ) as [ g' | l ] .  apply ( ii1 g' ) .  apply ( ii2 ( isantisymmhzleh _ _ l g ) ) .  Defined .




(** *** Mixed transitivities *)



Lemma hzgthgehtrans ( n m k : hz ) : hzgth n m -> hzgeh m k -> hzgth n k .
Proof. intros n m k gnm gmk . destruct ( hzgehchoice m k gmk ) as [ g' | e ] . apply ( istranshzgth _ _ _ gnm g' ) .  rewrite e in gnm  .  apply gnm . Defined.

Lemma hzgehgthtrans ( n m k : hz ) : hzgeh n m -> hzgth m k -> hzgth n k .
Proof. intros n m k gnm gmk . destruct ( hzgehchoice n m gnm ) as [ g' | e ] . apply ( istranshzgth _ _ _ g' gmk ) .  rewrite e .  apply gmk . Defined.

Lemma hzlthlehtrans ( n m k : hz ) : hzlth n m -> hzleh m k -> hzlth n k .
Proof . intros n m k l1 l2 . apply ( hzgehgthtrans k m n l2 l1 ) . Defined .

Lemma hzlehlthtrans ( n m k : hz ) : hzleh n m -> hzlth m k -> hzlth n k .
Proof . intros n m k l1 l2 . apply ( hzgthgehtrans k m n l2 l1 ) . Defined .




(** *** Addition and comparisons  *)



(** [ hzgth ] *)


Definition hzgthandplusl ( n m k : hz ) : hzgth n m -> hzgth ( k + n ) ( k + m ) .
Proof. apply ( pr1 ( isbinopabgrdiffrel nataddabmonoid isplushrelnatgth ) ) .   Defined .

Definition hzgthandplusr ( n m k : hz ) : hzgth n m -> hzgth ( n + k ) ( m + k ) .
Proof. apply ( pr2 ( isbinopabgrdiffrel nataddabmonoid isplushrelnatgth ) ) .  Defined .

Definition hzgthandpluslinv  ( n m k : hz ) : hzgth ( k + n ) ( k + m ) -> hzgth n m  .
Proof. intros n m k g . set ( g' := hzgthandplusl _ _ ( - k ) g ) . clearbody g' . rewrite ( pathsinv0 ( hzplusassoc _ _ n ) ) in g' . rewrite ( pathsinv0 ( hzplusassoc _ _ m ) ) in g' .  rewrite ( hzlminus k ) in g' . rewrite ( hzplusl0 _ ) in g' .   rewrite ( hzplusl0 _ ) in g' . apply g' .  Defined .

Definition hzgthandplusrinv ( n m k : hz ) :  hzgth ( n + k ) ( m + k ) -> hzgth n m  .
Proof. intros n m k l . rewrite ( hzpluscomm n k ) in l . rewrite ( hzpluscomm m k ) in l . apply ( hzgthandpluslinv _ _ _ l )  . Defined .

Lemma hzgthsnn ( n : hz ) : hzgth ( n + 1 ) n .
Proof . intro . set ( int := hzgthandplusl _ _ n ( ct ( hzgth , isdecrelhzgth, 1 , 0 ) ) ) . clearbody int . rewrite ( hzplusr0 _ ) in int .   apply int . Defined .


(** [ hzlth ] *)


Definition hzlthandplusl ( n m k : hz ) : hzlth n m -> hzlth ( k + n ) ( k + m )  := hzgthandplusl _ _ _ .

Definition hzlthandplusr ( n m k : hz ) : hzlth n m -> hzlth ( n + k ) ( m + k ) := hzgthandplusr _ _ _ .

Definition hzlthandpluslinv  ( n m k : hz ) : hzlth ( k + n ) ( k + m ) -> hzlth n m := hzgthandpluslinv _ _ _ .

Definition hzlthandplusrinv ( n m k : hz ) :  hzlth ( n + k ) ( m + k ) -> hzlth n m := hzgthandplusrinv _ _ _ .

Definition hzlthnsn ( n : hz ) : hzlth n ( n + 1 ) := hzgthsnn n .



(** [ hzleh ] *)


Definition hzlehandplusl ( n m k : hz ) : hzleh n m -> hzleh ( k + n ) ( k + m ) := negf ( hzgthandpluslinv n m k )  .

Definition hzlehandplusr ( n m k : hz ) : hzleh n m -> hzleh ( n + k ) ( m + k ) := negf ( hzgthandplusrinv n m k )  .

Definition hzlehandpluslinv  ( n m k : hz ) : hzleh ( k + n ) ( k + m ) -> hzleh n m := negf ( hzgthandplusl n m k )  .

Definition hzlehandplusrinv ( n m k : hz ) :  hzleh ( n + k ) ( m + k ) -> hzleh n m :=  negf ( hzgthandplusr n m k ) .



(** [ hzgeh ] *)


Definition hzgehandplusl ( n m k : hz ) : hzgeh n m -> hzgeh ( k + n ) ( k + m ) := negf ( hzgthandpluslinv m n k ) .

Definition hzgehandplusr ( n m k : hz ) : hzgeh n m -> hzgeh ( n + k ) ( m + k ) := negf ( hzgthandplusrinv m n k )  .

Definition hzgehandpluslinv  ( n m k : hz ) : hzgeh ( k + n ) ( k + m ) -> hzgeh n m := negf ( hzgthandplusl m n k )  .

Definition hzgehandplusrinv ( n m k : hz ) :  hzgeh ( n + k ) ( m + k ) -> hzgeh n m :=  negf ( hzgthandplusr m n k ) .




(** *** Properties of [ hzgth ] in the terminology of  algebra1.v (continued below)

Note: at the moment we do not need properties of [ hzlth ] , [ hzleh ] and [ hzgeh ] in terminology of algebra1 since the corresponding relations on [ hq ] are bulid from [ hqgth ] . *)

Lemma isplushrelhzgth : @isbinophrel hzaddabgr hzgth .
Proof . split . apply  hzgthandplusl .  apply hzgthandplusr .  Defined .

Lemma isinvplushrelhzgth : @isinvbinophrel hzaddabgr hzgth .
Proof . split . apply  hzgthandpluslinv .  apply hzgthandplusrinv .  Defined .

Lemma isrngmulthzgth : isrngmultgt _ hzgth .
Proof . apply ( isrngrigtorngmultgt natcommrig isplushrelnatgth isrigmultgtnatgth )  . Defined .

Lemma  isinvrngmulthzgth : isinvrngmultgt _ hzgth .
Proof . apply ( isinvrngrigtorngmultgt natcommrig isplushrelnatgth isinvplushrelnatgth isinvrigmultgtnatgth ) . Defined .



(** *** Negation and comparisons *)

(** [ hzgth ] *)

Lemma hzgth0andminus  { n : hz } ( is : hzgth n 0 ) : hzlth ( - n ) 0 .
Proof . intros . apply ( rngfromgt0 hz isplushrelhzgth ) . apply is . Defined .

Lemma hzminusandgth0  { n : hz } ( is : hzgth ( - n ) 0 ) : hzlth n 0 .
Proof . intros . apply ( rngtolt0 hz isplushrelhzgth ) . apply is . Defined .


(** [ hzlth ] *)

Lemma hzlth0andminus  { n : hz } ( is : hzlth n 0 ) : hzgth ( - n ) 0 .
Proof . intros . apply ( rngfromlt0 hz isplushrelhzgth ) . apply is . Defined .

Lemma hzminusandlth0  { n : hz } ( is : hzlth ( - n ) 0 ) : hzgth n 0 .
Proof . intros .  apply ( rngtogt0 hz isplushrelhzgth ) . apply is . Defined .

(* ??? Coq slows down on the proofs of these two lemmas for no good reason. *)


(** [ hzleh ] *)

Lemma hzleh0andminus  { n : hz } ( is : hzleh n 0 ) : hzgeh ( - n ) 0 .
Proof . intro n . apply ( negf ( @hzminusandlth0 n ) ) . Defined .

Lemma hzminusandleh0  { n : hz } ( is : hzleh ( - n ) 0 ) : hzgeh n 0 .
Proof . intro n . apply ( negf ( @hzlth0andminus n ) ) . Defined .



(** [ hzgeh ] *)

Lemma hzgeh0andminus  { n : hz } ( is : hzgeh n 0 ) : hzleh ( - n ) 0 .
Proof . intro n . apply ( negf ( @hzminusandgth0 n ) ) . Defined .

Lemma hzminusandgeh0  { n : hz } ( is : hzgeh ( - n ) 0 ) : hzleh n 0 .
Proof . intro n . apply ( negf ( @hzgth0andminus n ) ) . Defined .



(** *** Multiplication and comparisons  *)


(** [ hzgth ] *)


Definition hzgthandmultl ( n m k : hz ) ( is : hzgth k hzzero ) : hzgth n m -> hzgth ( k * n ) ( k * m ) .
Proof. apply ( isrngmultgttoislrngmultgt _ isplushrelhzgth isrngmulthzgth ) .   Defined .

Definition hzgthandmultr ( n m k : hz ) ( is : hzgth k hzzero ) : hzgth n m -> hzgth ( n * k ) ( m * k )  .
Proof . apply ( isrngmultgttoisrrngmultgt _ isplushrelhzgth isrngmulthzgth ) . Defined .

Definition  hzgthandmultlinv ( n m k : hz ) ( is : hzgth k hzzero ) : hzgth ( k * n ) ( k * m ) -> hzgth n m .
Proof . intros n m k is is' .  apply ( isinvrngmultgttoislinvrngmultgt hz isplushrelhzgth isinvrngmulthzgth n m k is is' ) .  Defined .

Definition hzgthandmultrinv ( n m k : hz ) ( is : hzgth k hzzero ) : hzgth ( n * k ) ( m * k ) -> hzgth n m .
Proof.   intros n m k is is' .  apply ( isinvrngmultgttoisrinvrngmultgt hz isplushrelhzgth isinvrngmulthzgth n m k is is' ) .  Defined .



(** [ hzlth ] *)


Definition hzlthandmultl ( n m k : hz ) ( is : hzgth k 0 ) : hzlth n m -> hzlth ( k * n ) ( k * m )  := hzgthandmultl _ _ _ is .

Definition hzlthandmultr ( n m k : hz ) ( is : hzgth k 0 ) : hzlth n m -> hzlth ( n * k ) ( m * k ) := hzgthandmultr _ _ _ is .

Definition hzlthandmultlinv ( n m k : hz ) ( is : hzgth k 0 ) : hzlth ( k * n ) ( k * m ) -> hzlth n m := hzgthandmultlinv _ _ _ is .

Definition hzlthandmultrinv ( n m k : hz ) ( is : hzgth k 0 ) : hzlth ( n * k ) ( m * k ) -> hzlth n m := hzgthandmultrinv _ _ _ is .


(** [ hzleh ] *)


Definition hzlehandmultl ( n m k : hz ) ( is : hzgth k 0 ) : hzleh n m -> hzleh ( k * n ) ( k * m ) := negf ( hzgthandmultlinv _ _ _ is ) .

Definition hzlehandmultr ( n m k : hz ) ( is : hzgth k 0 ) : hzleh n m -> hzleh ( n * k ) ( m * k ) := negf ( hzgthandmultrinv _ _ _ is ) .

Definition hzlehandmultlinv ( n m k : hz ) ( is : hzgth k 0 ) : hzleh ( k * n ) ( k * m ) -> hzleh n m := negf ( hzgthandmultl _ _ _ is )  .

Definition hzlehandmultrinv ( n m k : hz ) ( is : hzgth k 0 ) : hzleh ( n * k ) ( m * k ) -> hzleh n m := negf ( hzgthandmultr _ _ _ is ) .


(** [ hzgeh ] *)


Definition hzgehandmultl ( n m k : hz ) ( is : hzgth k 0 ) : hzgeh n m -> hzgeh ( k * n ) ( k * m ) := negf ( hzgthandmultlinv _ _ _ is ) .

Definition hzgehandmultr ( n m k : hz ) ( is : hzgth k 0 ) : hzgeh n m -> hzgeh ( n * k ) ( m * k )  := negf ( hzgthandmultrinv _ _ _ is ) .

Definition hzgehandmultlinv ( n m k : hz ) ( is : hzgth k 0 ) : hzgeh ( k * n ) ( k * m ) -> hzgeh n m := negf ( hzgthandmultl _ _ _ is )   .

Definition hzgehandmultrinv ( n m k : hz ) ( is : hzgth k 0 ) : hzgeh ( n * k ) ( m * k ) -> hzgeh n m := negf ( hzgthandmultr _ _ _ is )  .



(** Multiplication of positive with positive, positive with negative, negative with positive, two negatives etc. *)

Lemma hzmultgth0gth0 { m n : hz } ( ism : hzgth m 0 ) ( isn : hzgth n 0 ) : hzgth ( m * n ) 0 .
Proof . intros . apply isrngmulthzgth . apply ism . apply isn . Defined .

Lemma hzmultgth0geh0 { m n : hz } ( ism : hzgth m 0 ) ( isn : hzgeh n 0 ) : hzgeh ( m * n ) 0 .
Proof . intros .  destruct ( hzgehchoice _ _ isn ) as [ gn | en ] .

apply ( hzgthtogeh _ _ ( hzmultgth0gth0  ism gn ) ) .

rewrite en .  rewrite ( hzmultx0 m ) . apply isreflhzgeh . Defined .


Lemma hzmultgeh0gth0 { m n : hz } ( ism : hzgeh m 0 ) ( isn : hzgth n 0 ) : hzgeh ( m * n ) 0 .
Proof .  intros .  destruct ( hzgehchoice _ _ ism ) as [ gm | em ] .

apply ( hzgthtogeh _ _ ( hzmultgth0gth0 gm isn ) ) .

rewrite em .  rewrite ( hzmult0x _ ) . apply isreflhzgeh . Defined .


Lemma hzmultgeh0geh0 { m n : hz } ( ism : hzgeh m 0 ) ( isn : hzgeh n 0 ) : hzgeh ( m * n ) 0 .
Proof . intros .   destruct ( hzgehchoice _ _ isn ) as [ gn | en ] .

apply ( hzmultgeh0gth0 ism gn ) .

rewrite en .  rewrite ( hzmultx0 m ) . apply isreflhzgeh . Defined .


Lemma hzmultgth0lth0 { m n : hz } ( ism : hzgth m 0 ) ( isn : hzlth n 0 ) : hzlth ( m * n ) 0 .
Proof . intros . apply ( rngmultgt0lt0 hz isplushrelhzgth isrngmulthzgth ) . apply ism . apply isn . Defined .

Lemma hzmultgth0leh0 { m n : hz } ( ism : hzgth m 0 ) ( isn : hzleh n 0 ) : hzleh ( m * n ) 0 .
Proof . intros .  destruct ( hzlehchoice _ _ isn ) as [ ln | en ] .

apply ( hzlthtoleh _ _ ( hzmultgth0lth0  ism ln ) ) .

rewrite en .  rewrite ( hzmultx0 m ) . apply isreflhzleh . Defined .

Lemma hzmultgeh0lth0 { m n : hz } ( ism : hzgeh m 0 ) ( isn : hzlth n 0 ) : hzleh ( m * n ) 0 .
Proof .  intros .  destruct ( hzlehchoice _ _ ism ) as [ lm | em ] .

apply ( hzlthtoleh _ _ ( hzmultgth0lth0 lm isn ) ) .

destruct em .  rewrite ( hzmult0x _ ) . apply isreflhzleh . Defined .

Lemma hzmultgeh0leh0 { m n : hz } ( ism : hzgeh m 0 ) ( isn : hzleh n 0 ) : hzleh ( m * n ) 0 .
Proof . intros .   destruct ( hzlehchoice _ _ isn ) as [ ln | en ] .

apply ( hzmultgeh0lth0 ism ln ) .

rewrite en .  rewrite ( hzmultx0 m ) . apply isreflhzleh . Defined .



Lemma hzmultlth0gth0 { m n : hz } ( ism : hzlth m 0 ) ( isn : hzgth n 0 ) : hzlth ( m * n ) 0 .
Proof . intros . rewrite ( hzmultcomm ) .  apply hzmultgth0lth0 . apply isn . apply ism .  Defined .

Lemma hzmultlth0geh0 { m n : hz } ( ism : hzlth m 0 ) ( isn : hzgeh n 0 ) : hzleh ( m * n ) 0 .
Proof . intros . rewrite ( hzmultcomm ) .  apply hzmultgeh0lth0 . apply isn . apply ism .  Defined .


Lemma hzmultleh0gth0 { m n : hz } ( ism : hzleh m 0 ) ( isn : hzgth n 0 ) : hzleh ( m * n ) 0 .
Proof . intros . rewrite ( hzmultcomm ) .  apply hzmultgth0leh0 . apply isn . apply ism .  Defined .


Lemma hzmultleh0geh0 { m n : hz } ( ism : hzleh m 0 ) ( isn : hzgeh n 0 ) : hzleh ( m * n ) 0 .
Proof . intros . rewrite ( hzmultcomm ) .  apply hzmultgeh0leh0 . apply isn . apply ism .  Defined .


Lemma hzmultlth0lth0 { m n : hz } ( ism : hzlth m 0 ) ( isn : hzlth n 0 ) : hzgth ( m * n ) 0 .
Proof . intros . assert ( ism' := hzlth0andminus ism ) .  assert ( isn' := hzlth0andminus isn ) . assert ( int := isrngmulthzgth _ _ ism' isn' ) . rewrite ( rngmultminusminus hz ) in int .  apply int . Defined .

Lemma hzmultlth0leh0 { m n : hz } ( ism : hzlth m 0 ) ( isn : hzleh n 0 ) : hzgeh ( m * n ) 0 .
Proof . intros . intros .  destruct ( hzlehchoice _ _ isn ) as [ ln | en ] .

apply ( hzgthtogeh _ _ ( hzmultlth0lth0  ism ln ) ) .

rewrite en .  rewrite ( hzmultx0 m ) . apply isreflhzgeh . Defined .

Lemma hzmultleh0lth0 { m n : hz } ( ism : hzleh m 0 ) ( isn : hzlth n 0 ) : hzgeh ( m * n ) 0 .
Proof . intros . destruct ( hzlehchoice _ _ ism ) as [ lm | em ] .

apply ( hzgthtogeh _ _ ( hzmultlth0lth0 lm isn ) ) .

rewrite em .  rewrite ( hzmult0x _ ) . apply isreflhzgeh .  Defined .

Lemma hzmultleh0leh0 { m n : hz } ( ism : hzleh m 0 ) ( isn : hzleh n 0 ) : hzgeh ( m * n ) 0 .
Proof . intros .  destruct ( hzlehchoice _ _ isn ) as [ ln | en ] .

apply ( hzmultleh0lth0 ism ln ) .

rewrite en .  rewrite ( hzmultx0 m ) . apply isreflhzgeh .   Defined .




(** *** [ hz ] as an integral domain *)


Lemma isintdomhz : isintdom hz .
Proof . split with isnonzerornghz .  intros a b e0 .  destruct ( isdeceqhz a 0 ) as [ ea | nea ] .  apply ( hinhpr ( ii1 ea ) ) . destruct ( isdeceqhz b 0 ) as [ eb | neb ] . apply ( hinhpr ( ii2 eb ) ) .  destruct ( hzneqchoice _ _ nea ) as [ ga | la ] .  destruct ( hzneqchoice _ _ neb ) as [ gb | lb ] . destruct ( hzgthtoneq _ _ ( hzmultgth0gth0 ga gb ) e0 ) .  destruct ( hzlthtoneq _ _ ( hzmultgth0lth0 ga lb ) e0 ) .  destruct ( hzneqchoice _ _ neb ) as [ gb | lb ] .  destruct ( hzlthtoneq _ _ ( hzmultlth0gth0 la gb ) e0 ) .  destruct ( hzgthtoneq _ _ ( hzmultlth0lth0 la lb ) e0 ) .  Defined .


Definition hzintdom : intdom := tpair _ _ isintdomhz .

Definition hzneq0andmult ( n m : hz ) ( isn : hzneq n 0 ) ( ism : hzneq m 0 ) : hzneq ( n * m ) 0 := intdomneq0andmult hzintdom n m isn ism .

Lemma hzmultlcan ( a b c : hz ) ( ne : neg ( c = 0 ) ) ( e : ( c * a ) = ( c * b ) ) : a = b .
Proof . intros . apply ( intdomlcan hzintdom _ _ _ ne e ) . Defined .

Lemma hzmultrcan ( a b c : hz ) ( ne : neg ( c = 0 ) ) ( e : ( a * c ) = ( b * c ) ) : a = b .
Proof . intros . apply ( intdomrcan hzintdom _ _ _ ne e ) . Defined .

Lemma isinclhzmultl ( n : hz )( ne : neg ( n = 0 ) ) : isincl ( λ m : hz, n * m ) .
Proof.  intros .  apply ( pr1 ( intdomiscancelable hzintdom n ne ) ) . Defined .

Lemma isinclhzmultr ( n : hz )( ne : neg ( n = 0 ) ) : isincl ( λ m : hz, m * n ) .
Proof. intros . apply ( pr2 ( intdomiscancelable hzintdom n ne ) ) . Defined.






(** *** Comparisons and [ n -> n + 1 ] *)

Definition hzgthtogths ( n m : hz ) : hzgth n m -> hzgth ( n + 1 ) m  .
Proof. intros n m is . apply ( istranshzgth _ _ _ ( hzgthsnn n ) is ) . Defined .

Definition hzlthtolths ( n m : hz ) : hzlth n m -> hzlth n ( m + 1 ) := hzgthtogths _ _ .

Definition hzlehtolehs ( n m : hz ) : hzleh n m -> hzleh n ( m + 1 ) .
Proof . intros n m is . apply ( istranshzleh _ _ _ is ( hzlthtoleh _ _ ( hzlthnsn _ ) ) ) . Defined .

Definition hzgehtogehs ( n m : hz ) : hzgeh n m -> hzgeh ( n + 1 ) m := hzlehtolehs _ _  .



(** *** Two comparisons and [ n -> n + 1 ] *)

Lemma hzgthtogehsn ( n m : hz ) : hzgth n m -> hzgeh n ( m + 1 ) .
Proof. assert ( int : ∏ n m , isaprop ( hzgth n m -> hzgeh n ( m + 1 )  ) ) .
       { intros . apply impred . intro . apply ( pr2 _ ) . }
       unfold hzgth in * .  apply ( setquotuniv2prop _ ( λ n m, hProppair _ ( int n m ) ) ) . set ( R := abgrdiffrelint nataddabmonoid natgth ) .
       intros x x' .  change ( R x x' -> ( neg ( R ( @op ( abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig) ) x' ( dirprodpair 1%nat 0%nat ) ) x ) ) ) .
       unfold R . unfold abgrdiffrelint . simpl .
       apply ( @hinhuniv _  (hProppair ( neg ( ishinh_UU _ ) ) ( isapropneg _ ) ) ) .
       intro t2 . simpl . unfold neg .  apply ( @hinhuniv _ ( hProppair _ isapropempty ) ) .
       intro t2' .
       set ( x1 := pr1 x ) . set ( a1 := pr2 x ) . set ( x2 := pr1 x' ) .
       set ( a2 := pr2 x' ) . set ( c1 := pr1 t2 ) . assert ( r1 := pr2 t2 ) .
       change ( pr1 (  ( x1 + a2 + c1 ) > (  x2 + a1 + c1 ) ) ) in r1 .
       set ( c2 := pr1 t2' ) . assert ( r2 := pr2 t2' ) .
       change ( pr1 (  ( ( x2 + 1 ) + a1 + c2 ) > ( x1 + ( a2 + 0 ) + c2 ) ) ) in r2 .
       assert ( r1' := natgthandplusrinv _ _ c1 r1 ) .
       assert ( r2' := natgthandplusrinv _ _ c2 r2 ) .
       rewrite ( natplusr0 _ ) in r2' .
       rewrite ( natpluscomm _ 1 ) in r2' .
       rewrite ( natplusassoc _ _ _ ) in r2' .
       change (1 + (x2 + a1) > x1 + a2) with (x1 + a2 ≤ x2 + a1) in r2'.
       contradicts (natlehneggth r2') r1'.
Defined .

Lemma hzgthsntogeh ( n m : hz ) : hzgth ( n + 1 ) m -> hzgeh n m .
Proof. intros n m a . apply (hzgehandplusrinv n m 1) . apply ( hzgthtogehsn ( n + 1 ) m a ) . Defined. (* PeWa *)

Lemma hzlehsntolth ( n m : hz ) : hzleh ( n + 1 )  m -> hzlth n m .
Proof.  intros n m X . apply ( hzlthlehtrans _ _ _ ( hzlthnsn n ) X ) .  Defined .

Lemma hzlthtolehsn ( n m : hz ) : hzlth n m -> hzleh ( n + 1 )  m .
Proof. intros n m X . apply ( hzgthtogehsn m n X ) . Defined .

Lemma hzlthsntoleh ( n m : hz ) : hzlth n ( m + 1 ) -> hzleh n m .
Proof. intros n m a . apply (hzlehandplusrinv n m 1) . apply ( hzlthtolehsn n ( m + 1 ) a ) . Defined. (* PeWa *)

Lemma hzgehsntogth ( n m : hz ) : hzgeh n ( m + 1 ) -> hzgth n m .
Proof. intros n m X . apply ( hzlehsntolth m n X ) .  Defined .


(** *** Comparsion alternatives and [ n -> n + 1 ] *)


Lemma hzlehchoice2 ( n m : hz ) : hzleh n m -> coprod ( hzleh ( n + 1 )  m ) ( n = m ) .
Proof . intros n m l . destruct ( hzlehchoice n m l ) as [ l' | e ] .   apply ( ii1 ( hzlthtolehsn _ _ l' ) ) . apply ( ii2 e ) .  Defined .


Lemma hzgehchoice2 ( n m : hz ) : hzgeh n m -> coprod ( hzgeh n ( m + 1 ) ) ( n = m ) .
Proof . intros n m g . destruct ( hzgehchoice n m g ) as [ g' | e ] .   apply ( ii1 ( hzgthtogehsn _ _ g' ) ) . apply ( ii2 e ) . Defined .


Lemma hzgthchoice2 ( n m : hz ) : hzgth n m -> coprod ( hzgth n ( m + 1 ) ) ( n = ( m + 1 ) ) .
Proof.  intros n m g . destruct ( hzgehchoice _ _ ( hzgthtogehsn _ _ g ) ) as [ g' | e ] . apply ( ii1 g' ) .  apply ( ii2 e ) .  Defined .


Lemma hzlthchoice2 ( n m : hz ) : hzlth n m -> coprod ( hzlth ( n + 1 )  m ) ( ( n + 1 ) = m ) .
Proof.  intros n m l . destruct ( hzlehchoice _ _ ( hzlthtolehsn _ _ l ) ) as [ l' | e ] . apply ( ii1 l' ) .  apply ( ii2 e ) .   Defined .



(** *** Operations and comparisons on [ hz ] and [ natnattohz ] *)

Lemma natnattohzandgth ( xa1 xa2 : dirprod nat nat ) ( is : hzgth ( setquotpr _ xa1 ) ( setquotpr _ xa2 ) ) : natgth ( ( pr1 xa1 ) + ( pr2 xa2 ) ) ( ( pr1 xa2 ) + ( pr2 xa1 ) ) .
Proof . intros . change ( ishinh_UU ( total2  ( λ a0, natgth (pr1 xa1 + pr2 xa2 + a0) (pr1 xa2 + pr2 xa1 + a0) ) ) ) in is .  generalize is .  apply @hinhuniv .  intro t2 .  set ( a0 := pr1 t2 ) . assert ( g := pr2 t2 ) . change ( pr1 ( natgth (pr1 xa1 + pr2 xa2 + a0) (pr1 xa2 + pr2 xa1 + a0) ) ) in g . apply ( natgthandplusrinv _ _ a0 g ) . Defined .

Lemma natnattohzandlth ( xa1 xa2 : dirprod nat nat ) ( is : hzlth ( setquotpr _ xa1 ) ( setquotpr _ xa2 ) ) : natlth ( ( pr1 xa1 ) + ( pr2 xa2 ) ) ( ( pr1 xa2 ) + ( pr2 xa1 ) ) .
Proof . intros . apply ( natnattohzandgth xa2 xa1 is ) .  Defined .



(** *** Canonical rig homomorphism from [ nat ] to [ hz ] *)

Definition nattohz : nat -> hz := λ n, setquotpr _ ( dirprodpair n 0%nat ) .

Definition isinclnattohz : isincl nattohz := isincltorngdiff natcommrig ( λ n, isinclnatplusr n ) .

Definition nattohzandneq ( n m : nat ) ( is : natnegpaths n m ) : hzneq ( nattohz n ) ( nattohz m ) := negf ( invmaponpathsincl _ isinclnattohz n m ) is .

Definition nattohzand0 : ( nattohz 0%nat ) = 0 := idpath _ .

Definition nattohzandS ( n : nat ) : ( nattohz ( S n ) ) = ( 1 + nattohz n ) := isbinop1funtorngdiff natcommrig 1%nat n .

Definition nattohzand1 : ( nattohz 1%nat ) = 1 := idpath _ .

Lemma nattorig_nattohz :
  ∏ n : nat, nattorig (X := hz) n = nattohz n.
Proof.
  induction n as [|n IHn].
  - unfold nattorig, nattohz ; simpl.
    reflexivity.
  - rewrite nattorigS, IHn.
    apply pathsinv0, nattohzandS.
Qed.

Definition nattohzandplus ( n m : nat ) : ( nattohz ( n + m )%nat ) = ( nattohz n + nattohz m ) := isbinop1funtorngdiff natcommrig n m .

Definition nattohzandminus ( n m : nat ) ( is : natgeh n m ) : ( nattohz ( n - m )%nat ) = ( nattohz n - nattohz m ) .
Proof . intros .  apply ( hzplusrcan _ _ ( nattohz m ) ) . unfold hzminus .  rewrite ( hzplusassoc ( nattohz n ) ( - nattohz m ) ( nattohz m ) ) . rewrite ( hzlminus _ ) .   rewrite hzplusr0 .  rewrite ( pathsinv0 ( nattohzandplus _ _ ) ) .  rewrite ( minusplusnmm _ _ is ) . apply idpath . Defined .

Opaque nattohzandminus .

Definition nattohzandmult ( n m : nat ) : ( nattohz ( n * m )%nat ) = ( nattohz n * nattohz m ) .
Proof . intros . simpl . change nattohz with ( torngdiff natcommrig ) . apply ( isbinop2funtorngdiff natcommrig n m ) . Defined .

Definition nattohzandgth ( n m : nat ) ( is : natgth n m ) : hzgth ( nattohz n ) ( nattohz m ) := iscomptorngdiff natcommrig isplushrelnatgth n m is .

Definition nattohzandlth ( n m : nat ) ( is : natlth n m ) : hzlth ( nattohz n ) ( nattohz m ) := nattohzandgth m n is .

Definition nattohzandleh ( n m : nat ) ( is : natleh n m ) : hzleh ( nattohz n ) ( nattohz m ) .
Proof . intros . destruct ( natlehchoice _ _ is ) as [ l | e ] .   apply ( hzlthtoleh _ _ ( nattohzandlth _ _ l ) ) .  rewrite e .  apply ( isreflhzleh ) .  Defined .

Definition nattohzandgeh ( n m : nat ) ( is : natgeh n m ) : hzgeh ( nattohz n ) ( nattohz m ) := nattohzandleh _ _ is .

(** *** Addition and subtraction on [ nat ] and [ hz ] *)



(** *** Absolute value on [ hz ] *)

Definition hzabsvalint : ( dirprod nat nat ) -> nat .
Proof . intro nm . destruct ( natgthorleh ( pr1 nm ) ( pr2  nm ) ) .  apply ( minus ( pr1 nm ) ( pr2 nm ) ) . apply ( minus ( pr2 nm ) ( pr1 nm ) ) . Defined .

Lemma hzabsvalintcomp : @iscomprelfun ( dirprod nat nat ) nat ( hrelabgrdiff nataddabmonoid )  hzabsvalint .
Proof . unfold iscomprelfun .  intros x x' . unfold hrelabgrdiff . simpl . apply ( @hinhuniv _ ( hProppair _ ( isasetnat (hzabsvalint x) (hzabsvalint x') ) ) ) .  unfold hzabsvalint . set ( n := ( pr1 x ) : nat  ) . set ( m := ( pr2 x ) : nat ) . set ( n' := ( pr1 x' ) : nat ) . set ( m' := ( pr2 x' ) : nat ) .   set ( int := natgthorleh n m ) . set ( int' := natgthorleh n' m' ) .   intro tt0 . simpl .  destruct tt0 as [ x0 eq ] .  simpl in eq .  assert ( e' := invmaponpathsincl _ ( isinclnatplusr x0 ) _ _ eq ) .

destruct int as [isgt | isle ] . destruct int' as [ isgt' | isle' ] .

apply ( invmaponpathsincl _ ( isinclnatplusr ( m + m' ) ) ) .  rewrite ( pathsinv0 ( natplusassoc ( n - m )  m m' ) ) . rewrite ( natpluscomm m m' ) .  rewrite ( pathsinv0 ( natplusassoc ( n' - m' ) m' m ) ) . rewrite ( minusplusnmm n m ( natgthtogeh _ _ isgt ) ) . rewrite ( minusplusnmm n' m' ( natgthtogeh _ _ isgt' ) ) . apply e' .

assert ( e'' := natlehandplusl n' m' n isle' ) .  assert ( e''' :=  natgthandplusr n m n' isgt )  .  assert ( e'''' := natlthlehtrans _ _ _ e''' e'' ) .  rewrite e' in e'''' . rewrite ( natpluscomm m n' ) in e'''' . destruct ( isirreflnatgth _ e'''' ) .

destruct int' as [ isgt' | isle' ] .

destruct ( natpluscomm m n') . set ( e'' := natlehandplusr n m m' isle ) .  set ( e''' :=  natgthandplusl n' m' m isgt' )  .  set ( e'''' := natlehlthtrans _ _ _ e'' e''' ) .  rewrite e' in e'''' . destruct ( isirreflnatgth _ e'''' ) .

apply ( invmaponpathsincl _ ( isinclnatplusr ( n + n') ) ) . rewrite ( pathsinv0 ( natplusassoc ( m - n )  n n' ) ) . rewrite ( natpluscomm n n' ) .  rewrite ( pathsinv0 ( natplusassoc ( m' - n') n' n ) ) .  rewrite ( minusplusnmm m n isle ) . rewrite ( minusplusnmm m' n' isle' ) .  rewrite ( natpluscomm m' n ) .  rewrite ( natpluscomm m n' ) .  apply ( pathsinv0 e' ) .
Defined .

Definition hzabsval : hz -> nat := setquotuniv _ natset hzabsvalint hzabsvalintcomp .

Lemma hzabsval0 : ( hzabsval 0 ) = 0%nat .
Proof .  apply idpath .  Defined .

Lemma hzabsvalgth0 { x : hz } ( is : hzgth x 0 ) : ( nattohz ( hzabsval x ) ) = x .
Proof . assert ( int : ∏ x : hz , isaprop ( hzgth x 0 -> ( nattohz ( hzabsval x ) ) = x ) ) . intro . apply impred . intro . apply ( setproperty hz ) .  apply ( setquotunivprop _ ( λ x, hProppair _ ( int x ) ) ) . intros xa g . simpl in xa . assert ( g' := natnattohzandgth _ _ g ) . simpl in g' .  simpl .  change (( setquotpr (eqrelabgrdiff (rigaddabmonoid natcommrig)) ( dirprodpair ( hzabsvalint xa ) 0%nat ) ) = ( setquotpr (eqrelabgrdiff (rigaddabmonoid natcommrig)) xa ) ) . apply weqpathsinsetquot . simpl . apply hinhpr . split with 0%nat .  change ( pr1 ( natgth ( pr1 xa + 0%nat ) ( pr2 xa ) ) ) in g' . rewrite ( natplusr0 _ ) in g' .  change ((hzabsvalint xa + pr2 xa + 0)%nat = (pr1 xa + 0 + 0)%nat ) . rewrite ( natplusr0 _ ) .  rewrite ( natplusr0 _ ) .  rewrite ( natplusr0 _ ) . unfold hzabsvalint .   destruct ( natgthorleh (pr1 xa) (pr2 xa)  ) as [ g'' | l ] .

rewrite ( minusplusnmm _ _ ( natlthtoleh _ _ g'' ) ) . apply idpath .

contradicts (natlehneggth l) g'.
Defined .

Opaque hzabsvalgth0 .

Lemma hzabsvalgeh0 { x : hz } ( is : hzgeh x 0 ) : ( nattohz ( hzabsval x ) ) = x .
Proof .  intros . destruct ( hzgehchoice _ _ is ) as [ g | e ] .  apply ( hzabsvalgth0 g ) . rewrite e .  apply idpath .  Defined .

Lemma hzabsvallth0 { x : hz } ( is : hzlth x 0 ) : ( nattohz ( hzabsval x ) ) = ( - x ) .
Proof . assert ( int : ∏ x : hz , isaprop ( hzlth x 0 -> ( nattohz ( hzabsval x ) ) = ( - x ) ) ) . intro . apply impred . intro . apply ( setproperty hz ) .  apply ( setquotunivprop _ ( λ x, hProppair _ ( int x ) ) ) . intros xa l . simpl in xa . assert ( l' := natnattohzandlth _ _ l ) . simpl in l' .  simpl .  change (( setquotpr (eqrelabgrdiff (rigaddabmonoid natcommrig)) ( dirprodpair ( hzabsvalint xa ) 0%nat ) ) = ( setquotpr (eqrelabgrdiff (rigaddabmonoid natcommrig)) ( dirprodpair ( pr2 xa ) ( pr1 xa ) ) ) ) . apply weqpathsinsetquot . simpl . apply hinhpr . split with 0%nat .  change ( pr1 ( natlth ( pr1 xa + 0%nat ) ( pr2 xa ) ) ) in l' . rewrite ( natplusr0 _ ) in l' .  change ((hzabsvalint xa + pr1 xa + 0)%nat = (pr2 xa + 0 + 0)%nat). rewrite ( natplusr0 _ ) .  rewrite ( natplusr0 _ ) .  rewrite ( natplusr0 _ ) . unfold hzabsvalint .   destruct ( natgthorleh (pr1 xa) (pr2 xa)  ) as [ g | l'' ] .

destruct ( isasymmnatgth _ _ g l' ) .

rewrite ( minusplusnmm _ _ l'' ) . apply idpath . Defined .

Opaque hzabsvallth0 .

Lemma hzabsvalleh0 { x : hz } ( is : hzleh x 0 ) : ( nattohz ( hzabsval x ) ) = ( - x ) .
Proof .  intros . destruct ( hzlehchoice _ _ is ) as [ l | e ] .  apply ( hzabsvallth0 l ) . rewrite e .  apply idpath .  Defined .


Lemma hzabsvaleq0 { x : hz } ( e : ( hzabsval x ) = 0%nat ) : x = 0  .
Proof .  intros . destruct ( isdeceqhz x 0 ) as [ e0 | ne0 ] . apply e0 .  destruct ( hzneqchoice _ _ ne0 ) as [ g | l ] .

assert ( e' := hzabsvalgth0 g ) . rewrite e in e' . change ( 0 = x ) in e' .  apply ( pathsinv0 e' ) .

assert ( e' := hzabsvallth0 l ) . rewrite e in e' . change ( 0 = ( - x ) ) in e' . assert ( g := hzlth0andminus l ) .  rewrite e' in g .  destruct ( isirreflhzgth _ g ) . Defined .

Definition hzabsvalneq0 { x : hz } ne := neg_to_negProp (nP := natneq _ _) (negf ( @hzabsvaleq0 x ) ne).

Lemma hzabsvalandmult ( a b : hz ) : ( ( hzabsval a ) * ( hzabsval b ) )%nat = ( hzabsval ( a * b ) ) .
Proof . intros . apply ( invmaponpathsincl _ isinclnattohz ) . rewrite ( nattohzandmult _ _ ) .  destruct ( hzgthorleh a 0 ) as [ ga | lea ] . destruct ( hzgthorleh b 0 ) as [ gb | leb ] .

rewrite ( hzabsvalgth0 ga ) .  rewrite ( hzabsvalgth0 gb ) .  rewrite ( hzabsvalgth0 ( hzmultgth0gth0 ga gb ) ) . apply idpath .

rewrite ( hzabsvalgth0 ga ) .  rewrite ( hzabsvalleh0 leb ) . rewrite ( hzabsvalleh0 ( hzmultgth0leh0 ga leb ) ) .    apply ( rngrmultminus hz ) .  destruct ( hzgthorleh b 0 ) as [ gb | leb ] .

rewrite ( hzabsvalgth0 gb ) .  rewrite ( hzabsvalleh0 lea ) . rewrite ( hzabsvalleh0 ( hzmultleh0gth0 lea gb ) ) . apply ( rnglmultminus hz ) .

rewrite ( hzabsvalleh0 lea ) . rewrite ( hzabsvalleh0 leb ) . rewrite ( hzabsvalgeh0 ( hzmultleh0leh0 lea leb ) ) .  apply (rngmultminusminus hz ) . Defined .



(** *** Some common equalities on integers *)
(** These lemmas are used for example in Complexes.v to construct complexes. *)
Local Opaque hz isdecrelhzeq iscommrngops.

Lemma hzeqbooleqii (i : hz) : hzbooleq i i = true.
Proof.
  intros i.
  unfold hzbooleq. unfold decreltobrel. induction (pr2 hzdeceq i i) as [T | F].
  - apply idpath.
  - apply fromempty. apply F. apply idpath.
Qed.

Lemma hzbooleqisi (i : hz) : hzbooleq i (i + 1) = false.
Proof.
  intros i. apply negrtopaths.
  apply (negf (λ e, hzpluslcan _ _ _ (! (hzplusr0 i @ e)))); clear i.
  confirm_not_equal isdecrelhzeq.
Qed.

Lemma hzbooleqisi' (i : hz) : hzbooleq i (i + 1) = false.
Proof.
  (* prove it again, to illustrate how to avoid the tactic [confirm_not_equal] *)
  intros i. apply negrtopaths.
  apply (negf (λ e, hzpluslcan _ _ _ (! (hzplusr0 i @ e)))); clear i.
  simple refine (confirm_not_equal isdecrelhzeq _ _ _).
  reflexivity.
Qed.

Lemma hzbooleqissi (i : hz) : hzbooleq i (i + 1 + 1) = false.
Proof.
  intros i. apply negrtopaths.
  rewrite hzplusassoc.
  apply (negf (λ e, hzpluslcan _ _ _ (! (hzplusr0 i @ e)))); clear i.
  confirm_not_equal isdecrelhzeq.
Qed.

Lemma hzeqeisi {i i0 : hz} (e : hzeq i i0) (e' : hzeq i (i0 + 1)) : empty.
Proof.
  intros i i0 e e'.
  apply nopathstruetofalse.
  use (pathscomp0 _ (hzbooleqisi i0)).
  rewrite <- e'. rewrite <- e.
  apply (! (hzeqbooleqii i)).
Qed.

Lemma hzeqisi {i : hz} (e' : hzeq i (i + 1)) : empty.
Proof.
  intros i e'.
  apply nopathstruetofalse. rewrite <- (hzbooleqisi i). rewrite <- e'.
  apply (! (hzeqbooleqii i)).
Qed.

Lemma hzeqissi {i : hz} (e : hzeq i (i + 1 + 1)) : empty.
Proof.
  intros i e.
  set (tmp := hzbooleqissi i). cbn in e. rewrite <- e in tmp.
  rewrite (hzeqbooleqii i) in tmp. apply nopathstruetofalse. apply tmp.
Qed.

Lemma hzeqeissi {i i0 : hz} (e : hzeq i i0) (e' : hzeq i (i0 + 1 + 1)) : empty.
Proof.
  intros i e0 e e'.
  cbn in e. rewrite e in e'. apply (hzeqissi e').
Qed.

Lemma hzeqsnmnsm {n m : hz} (e : hzeq (n + 1) m) (e' : hzeq n (m + 1)) : empty.
Proof.
  intros n m e e'.
  cbn in e. rewrite <- e in e'. apply (hzeqissi e').
Qed.

Lemma hzeqnmplusr {n m i : hz} (e : n = m) (e' : ¬ (n + i = m + i)) : empty.
Proof.
  intros n m i e e'.
  apply e'. exact (hzplusradd _ _ i e).
Qed.

Lemma hzeqnmplusr' {n m i : hz} (e : ¬ (n = m)) (e' : n + i = m + i) : empty.
Proof.
  intros n m i e e'.
  apply e. exact (hzplusrcan _ _ i e').
Qed.

Lemma isdecrelhzeqi (i : hz) : isdecrelhzeq i i = ii1 (idpath _).
Proof.
  intros i.
  induction (isdecrelhzeq i i) as [T | F].
  - apply maponpaths. apply isasethz.
  - apply fromempty. apply F. apply idpath.
Qed.

Lemma isdecrelhzeqminusplus (i j : hz) : isdecrelhzeq i (i - j + j) = ii1 (hzrminusplus' i j).
Proof.
  intros i j.
  induction (isdecrelhzeq i (i - j + j)) as [T | F].
  - apply maponpaths. apply isasethz.
  - apply fromempty. apply F. apply (hzrminusplus' i j).
Qed.

Lemma isdecrelhzeqminusplus' (i j : hz) : isdecrelhzeq (i - j + j) i = ii1 (hzrminusplus i j).
Proof.
  intros i j.
  induction (isdecrelhzeq (i - j + j) i) as [T | F].
  - apply maponpaths. apply isasethz.
  - apply fromempty. apply F. apply (hzrminusplus i j).
Qed.

Lemma hzeqpii {i : hz} : i - 1 != i.
Proof.
  intros i.
  apply (negf (λ e, hzpluslcan _ _ _ (e @ ! hzplusr0 i))); clear i.
  confirm_not_equal isdecrelhzeq.
Qed.

Lemma isdecrelhzeqpii (i : hz) :
  isdecrelhzeq (i - 1) i = ii2 (fun (e : hzeq (i - 1) i) => hzeqpii e).
Proof.
  intros i.
  induction (isdecrelhzeq (i - 1) i) as [e | n].
  - apply fromempty. apply (hzeqpii e).
  - apply maponpaths. apply funextfun. intros e.
    apply fromempty. apply n. apply e.
Qed.

Local Transparent hz isdecrelhzeq iscommrngops.

(** *** [hz] is an archimedean ring *)

Local Open Scope hz_scope .

Lemma isarchhz : isarchrng (X := hz) hzgth.
Proof.
  simple refine (isarchrigtorng _ _ _ _ _ _).
  - reflexivity.
  - intros n m k.
    apply istransnatgth.
  - apply isarchrig_setquot_aux.
    + split.
      * apply natgthandpluslinv.
      * apply natgthandplusrinv.
    + apply isarchnat.
Qed.

Lemma isarchhz_one :
  ∏ x : hz, hzgth x 0 → ∃ n : nat, hzgth (nattohz n * x) 1.
Proof.
  intros x Hx.
  generalize (isarchrng_1 _ isarchhz x Hx).
  apply hinhfun.
  intros n.
  exists (pr1 n).
  rewrite <- nattorig_nattohz.
  exact (pr2 n).
Qed.

Lemma isarchhz_gt :
  ∏ x : hz, ∃ n : nat, hzgth (nattohz n) x.
Proof.
  intros x.
  generalize (isarchrng_2 _ isarchhz x).
  apply hinhfun.
  intros n.
  exists (pr1 n).
  rewrite <- nattorig_nattohz.
  exact (pr2 n).
Qed.


(** **** hz -> abgr, 1 ↦ x, n ↦ x + x + ... + x  (n times), [hz_abmonoid_monoidfun] *)

Definition nat_to_monoid_fun {X : monoid} (x : X) : natset -> X.
Proof.
  intros X x n. induction n as [ | n IHn].
  - exact (unel X).
  - exact (@op X x IHn).
Defined.

Lemma nat_to_monoid_fun_unel {X : monoid} (x : X) : nat_to_monoid_fun x O = (unel X).
Proof.
  intros X x. exact (idpath (unel X)).
Defined.

Lemma nat_to_monoid_fun_S {X : abmonoid} (x : X) (n : nat) :
  nat_to_monoid_fun x (S n) = (nat_to_monoid_fun x n * x)%multmonoid.
Proof.
  intros X x n. induction n as [ | n IHn].
  - exact (commax X x (unel X)).
  - cbn. rewrite (assocax X). use two_arg_paths.
    + use idpath.
    + exact (commax X x _).
Qed.

Lemma nat_to_abmonoid_fun_plus {X : monoid} (x : X) (n m : nat) :
  nat_to_monoid_fun x (n + m)%nat = @op X (nat_to_monoid_fun x n) (nat_to_monoid_fun x m).
Proof.
  intros X x n. induction n as [ | n IHn].
  - intros m. rewrite (lunax X). use idpath.
  - intros m. cbn. rewrite (assocax X). use two_arg_paths.
    + use idpath.
    + exact (IHn m).
Qed.

Definition nat_nat_to_monoid_fun {X : gr} (x : X) : natset × natset -> X.
Proof.
  intros X x n.
  exact (@op X (nat_to_monoid_fun x (dirprod_pr1 n))
             (nat_to_monoid_fun (grinv X x) (dirprod_pr2 n))).
Defined.

Lemma nat_to_monoid_unel' {X : abgr} (x : X) (n : nat) :
  ((nat_to_monoid_fun x n) * (nat_to_monoid_fun (grinv X x) n))%multmonoid = (unel X).
Proof.
  intros X x n. induction n as [ | n IHn].
  - use (runax X).
  - Opaque nat_to_monoid_fun. cbn in *.
    rewrite (@nat_to_monoid_fun_S X x). rewrite (@nat_to_monoid_fun_S X (grinv X x)).
    rewrite (commax X _ x). rewrite (assocax X).
    rewrite <- (assocax X (@nat_to_monoid_fun X x n)).
    use (pathscomp0 (maponpaths (λ xx : pr1 X, (x * (xx * (grinv X x))))%multmonoid IHn)).
    clear IHn. use (pathscomp0 _ (grrinvax X x)).
    use two_arg_paths.
    + use idpath.
    + use (lunax X).
Qed.
Transparent nat_to_monoid_fun.

Lemma nat_nat_to_monoid1 {X : gr} (x : X) {n1 n2 m2 : nat} (e : n2 = m2) :
  nat_nat_to_monoid_fun x (dirprodpair n1 n2) = nat_nat_to_monoid_fun x (dirprodpair n1 m2).
Proof.
  intros X x n1 n2 m2 e. induction e. use idpath.
Qed.

Lemma nat_nat_to_monoid2 {X : gr} (x : X) {n1 m1 n2 : nat} (e : n1 = m1) :
  nat_nat_to_monoid_fun x (dirprodpair n1 n2) = nat_nat_to_monoid_fun x (dirprodpair m1 n2).
Proof.
  intros X x n1 m1 n2 e. induction e. use idpath.
Qed.

Definition nataddabmonoid_nataddabmonoid_to_monoid_fun {X : gr} (x : X) :
  abmonoiddirprod nataddabmonoid nataddabmonoid -> X := nat_nat_to_monoid_fun x.

Opaque nat_to_monoid_fun.
Lemma nat_nat_monoid_fun_isbinopfun {X : abgr} (x : X) :
  isbinopfun (nataddabmonoid_nataddabmonoid_to_monoid_fun x).
Proof.
  intros X x.
  use mk_isbinopfun. intros n m. induction n as [n1 n2]. induction m as [m1 m2]. cbn.
  unfold nataddabmonoid_nataddabmonoid_to_monoid_fun. unfold nat_nat_to_monoid_fun. cbn.
  rewrite nat_to_abmonoid_fun_plus. rewrite nat_to_abmonoid_fun_plus.
  rewrite (assocax X). rewrite (assocax X).
  use two_arg_paths.
  - use idpath.
  - rewrite <- (assocax X). rewrite (commax X (nat_to_monoid_fun (grinv X x) n2) _).
    rewrite (assocax X). rewrite (assocax X).
    use two_arg_paths.
    + use idpath.
    + use (commax X).
Qed.
Transparent nat_to_monoid_fun.

Lemma nat_nat_to_monoid_plus1 {X : abgr} (x : X) {n1 m1 m2: nat} (e : m2 = (m1 + n1)%nat) :
  nat_to_monoid_fun (grinv X x) n1 =
  (nat_to_monoid_fun x m1 * nat_to_monoid_fun (grinv X x) m2)%multmonoid.
Proof.
  intros X x n1 m1 m2 e. rewrite e. clear e. rewrite nat_to_abmonoid_fun_plus.
  rewrite <- (assocax X). use pathsinv0.
  use (pathscomp0 (maponpaths (λ xx : X, (xx * (nat_to_monoid_fun (grinv X x) n1))%multmonoid)
                              (nat_to_monoid_unel' x m1))).
  use (lunax X).
Qed.

Lemma nat_nat_prod_abmonoid_fun_unel {X : abgr} (x : X) :
  (nataddabmonoid_nataddabmonoid_to_monoid_fun x)
    (unel (abmonoiddirprod nataddabmonoid nataddabmonoid)) = (unel X).
Proof.
  intros X x. use (pathscomp0 (lunax X _)). use idpath.
Qed.

Definition nat_nat_prod_abmonoid_monoidfun {X : abgr} (x : X) :
  monoidfun (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig)) X.
Proof.
  intros X x.
  use monoidfunconstr.
  - exact (nataddabmonoid_nataddabmonoid_to_monoid_fun x).
  - use mk_ismonoidfun.
    + exact (nat_nat_monoid_fun_isbinopfun x).
    + exact (nat_nat_prod_abmonoid_fun_unel x).
Defined.

Lemma hz_abmonoid_ismonoidfun :
  @ismonoidfun
    (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig))
    hzaddabgr (@setquotpr (abmonoiddirprod (rigaddabmonoid natcommrig)
                                           (rigaddabmonoid natcommrig))
                          (binopeqrelabgrdiff (rigaddabmonoid natcommrig))).
Proof.
  use mk_ismonoidfun.
  - use mk_isbinopfun. intros x x'. use idpath.
  - use idpath.
Qed.

Definition hz_abmonoid_monoidfun :
  monoidfun (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig)) hzaddabgr.
Proof.
  use monoidfunconstr.
  - use setquotpr.
  - exact hz_abmonoid_ismonoidfun.
Defined.

Definition nat_nat_fun_unel {X : abgr} (x : X) (n : nat) :
  nat_nat_to_monoid_fun x (dirprodpair n n) = unel X.
Proof.
  intros X x n. exact (nat_to_monoid_unel' x n).
Qed.

Opaque nat_to_monoid_fun.
Definition nat_nat_fun_ind {X : abgr} (x : X) (n m : nat) :
  nat_nat_to_monoid_fun x (dirprodpair (n + m)%nat m) = nat_nat_to_monoid_fun x (dirprodpair n O).
Proof.
  intros X x n m.
  use (pathscomp0 (nat_nat_monoid_fun_isbinopfun x (dirprodpair n O) (dirprodpair m m))).
  unfold nataddabmonoid_nataddabmonoid_to_monoid_fun.
  rewrite (nat_nat_fun_unel x m). rewrite (runax X). use idpath.
Qed.
Transparent nat_to_monoid_fun.

Opaque nat_to_monoid_fun.
Definition nat_nat_fun_ind2 {X : abgr} (x : X) (n1 n2 m k : nat) :
  nat_nat_to_monoid_fun x (dirprodpair n1 m) = nat_nat_to_monoid_fun x (dirprodpair n2 k) ->
  nat_nat_to_monoid_fun x (dirprodpair n1 (S m)) = nat_nat_to_monoid_fun x (dirprodpair n2 (S k)).
Proof.
  intros X x n1 n2 m k H.
  unfold nat_nat_to_monoid_fun in *. cbn in *.
  rewrite (@nat_to_monoid_fun_S X (grinv X x)).
  rewrite (@nat_to_monoid_fun_S X (grinv X x)).
  rewrite <- (assocax X). rewrite <- (assocax X).
  use two_arg_paths.
  - exact H.
  - use idpath.
Qed.
Transparent nat_to_monoid_fun.

Opaque nat_to_monoid_fun.
Definition abgr_precategory_integer_fun_iscomprelfun {X : abgr} (x : X) :
  iscomprelfun (binopeqrelabgrdiff (rigaddabmonoid natcommrig))
               (nat_nat_prod_abmonoid_monoidfun x).
Proof.
  intros X x. intros x1. induction x1 as [x1 e1].
  unfold nat_nat_prod_abmonoid_monoidfun. cbn.
  unfold nataddabmonoid_nataddabmonoid_to_monoid_fun.
  unfold nat_nat_to_monoid_fun. cbn.
  induction x1 as [ | x1 IHx1].
  - intros x2 H. use (squash_to_prop H (setproperty X _ _)). intros H'. cbn in H'.
    induction H' as [H1 H2]. clear H. induction x2 as [x2 e2].
    apply natplusrcan in H2. rewrite nat_to_monoid_fun_unel. rewrite (lunax X). cbn. cbn in H2.
    exact (nat_nat_to_monoid_plus1 x H2).
  - intros x2 H. use (squash_to_prop H (setproperty X _ _)). intros H'. cbn in H'.
    induction H' as [H1 H2]. clear H. induction x2 as [x2 e2]. cbn in H2. cbn.
    use (pathscomp0
           (maponpaths (λ xx : X, (xx * (nat_to_monoid_fun (grinv X x) e1))%multmonoid)
                       (@nat_to_monoid_fun_S X x x1))).
    rewrite (commax X _ x). rewrite (assocax X). cbn.
    assert (HH : ishinh_UU(∑ x0 : nat, (x1 + (S e2) + x0)%nat = (x2 + e1 + x0)%nat)).
    {
      use hinhpr. use tpair.
      - exact O.
      - cbn. rewrite natplusr0. rewrite natplusr0. cbn.
        rewrite natplusassoc in H2.
        rewrite plus_n_Sm in H2. rewrite plus_n_Sm in H2.
        rewrite natplusnsm in H2. rewrite <- natplusassoc in H2.
        apply natplusrcan in H2. exact H2.
    }
    set (tmp := IHx1 (dirprodpair x2 (S e2)) HH). cbn in tmp.
    use (pathscomp0 (maponpaths (λ xx : X, (x * xx)%multmonoid) tmp)).
    clear tmp. clear HH. clear H2. clear IHx1. rewrite (commax X x). rewrite (assocax X).
    use two_arg_paths.
    + use idpath.
    + use (pathscomp0
             (maponpaths (λ xx : X, (xx * x)%multmonoid)
                         (@nat_to_monoid_fun_S X (grinv X x) e2))).
      rewrite (assocax X). rewrite (grlinvax X x). use (runax X).
Qed.
Transparent nat_to_monoid_fun.

(** Construction of tha map \mathbb{Z} --> A, 1 ↦ x *)
Definition hz_abgr_fun {X : abgr} (x : X) : hzaddabgr -> X.
Proof.
  intros X x.
  use setquotuniv.
  - exact (nat_nat_prod_abmonoid_monoidfun x).
  - exact (abgr_precategory_integer_fun_iscomprelfun x).
Defined.

(** Hide ismonoidfun behind Qed. *)
Definition hz_abgr_fun_ismonoidfun {X : abgr} (x : X) : ismonoidfun (hz_abgr_fun x).
Proof.
  intros X x.
  use mk_ismonoidfun.
  - use isbinopfun_twooutof3b.
    + use (abmonoiddirprod (rigaddabmonoid natcommrig) (rigaddabmonoid natcommrig)).
    + use (hz_abmonoid_monoidfun).
    + use issurjsetquotpr.
    + use binopfunisbinopfun.
    + use binopfunisbinopfun.
  - use (runax X).
Qed.

(** Construction of the monoidfun \mathbb{Z} --> A, 1 ↦ x *)
Definition hz_abgr_fun_monoidfun {X : abgr} (x : X) : monoidfun hzaddabgr X.
Proof.
  intros X x.
  use monoidfunconstr.
  - exact (hz_abgr_fun x).
  - exact (hz_abgr_fun_ismonoidfun x).
Defined.

(** Commutativity of the following diagram

                          nat × nat --- nat_nat_prod_abmonoid_monoidfun --->  X
        hz_abgr_fun_monoidfun |                                               ||
                             hz -------- hz_abmonoid_monoidfun -------------> X
 *)
Lemma abgr_natnat_hz_X_comm {X : abgr} (x : X) :
  monoidfuncomp hz_abmonoid_monoidfun (hz_abgr_fun_monoidfun x) =
  nat_nat_prod_abmonoid_monoidfun x.
Proof.
  intros X x. use monoidfun_paths. use funextfun. intros n. use setquotunivcomm.
Qed.

Opaque nat_to_monoid_fun.
Lemma monoidfun_nat_to_monoid_fun {X Y : abgr} (f : monoidfun X Y) (x : X) (n : nat) :
  pr1 f (nat_to_monoid_fun x n) = nat_to_monoid_fun (f x) n.
Proof.
  intros X Y f x n. induction n as [ | n IHn].
  - use monoidfununel.
  - use (pathscomp0 (maponpaths (pr1 f) (@nat_to_monoid_fun_S X x n))).
    use (pathscomp0 (binopfunisbinopfun f _ _)).
    use (pathscomp0 _ (! (@nat_to_monoid_fun_S Y (f x) n))).
    use two_arg_paths.
    + exact IHn.
    + use idpath.
Qed.
Transparent nat_to_monoid_fun.


(* End of the file hz.v *)
