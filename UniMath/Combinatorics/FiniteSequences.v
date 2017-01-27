Require Export UniMath.Combinatorics.StandardFiniteSets.
Unset Automatic Introduction.

(* move upstream *)

Ltac set_id_type v := match goal with |- @paths ?ID _ _ => set (v := ID); simpl in v end.

Arguments dni {_} _.

Arguments firstelement {_}.

Arguments lastelement {_}.

Definition firstValue {X n} : (stn (S n) -> X) -> X
  := λ x, x firstelement.

Definition lastValue {X n} : (stn (S n) -> X) -> X
  := λ x, x lastelement.

Definition funcomp' {X Y: UU} {Z:Y->UU} (f : X -> Y) (g : Π y:Y, Z y) := λ i, g (f i). (* rename to funcomp when moving upstream *)

Definition concatenate' {X:UU} {m n} (f : stn m -> X) (g : stn n -> X) : stn (m+n) -> X.
Proof.
  intros ? ? ? ? ? i.
  induction (weqfromcoprodofstn_invmap _ _ i) as [j | k].
  + exact (f j).
  + exact (g k).
Defined.

(* end of move upstream *)

Definition Sequence X := Σ n, stn n -> X.

Definition NonemptySequence X := Σ n, stn (S n) -> X.

Definition length {X} : Sequence X -> nat := pr1.

Definition sequenceToFunction {X} (x:Sequence X) := pr2 x : stn (length x) -> X.

Coercion sequenceToFunction : Sequence >-> Funclass.

Definition length'{X} : NonemptySequence X -> nat := λ x, S(pr1 x).

Definition functionToSequence {X n} (f:stn n -> X) : Sequence X
  := (n,,f).

Definition NonemptySequenceToFunction {X} (x:NonemptySequence X) := pr2 x : stn (length' x) -> X.

Coercion NonemptySequenceToFunction : NonemptySequence >-> Funclass.

Definition NonemptySequenceToSequence {X} (x:NonemptySequence X) := functionToSequence (NonemptySequenceToFunction x) : Sequence X.

Coercion NonemptySequenceToSequence : NonemptySequence >-> Sequence.

Definition composeSequence {X m n} (f:stn n -> X) (g:stn m -> stn n) : Sequence X
  := functionToSequence (f ∘ g).

Definition transport_stn m n i (b:i<m) (p:m=n) :
  transportf stn p (i,,b) = (i,,transportf (λ m,i<m) p b).
Proof. intros. induction p. reflexivity. Defined.

Definition sequenceEquality {X m n} (f:stn m->X) (g:stn n->X) (p:m=n) :
  (Π i, f i = g (transportf stn p i))
  -> transportf (λ m, stn m->X) p f = g.
Proof. intros ? ? ? ? ? ? e. induction p. apply funextfun. exact e. Defined.

(** The following two lemmas are the key lemmas that allow to prove (transportational) equality of
 sequences whose lengths are not definitionally equal. In particular, these lemmas can be used in
the proofs of such results as associativity of concatenation of sequences and the right unity
axiom for the empty sequence. **)

Definition seq_key_eq_lemma {X :UU}( g g' : Sequence X)(e_len : length g = length g')
           (e_el : forall ( i : nat )(ltg : i < length g )(ltg' : i < length g' ),
               g (i ,, ltg) = g' (i ,, ltg')) : g=g'.
Proof.
  intros.
  induction g as [m g]; induction g' as [m' g']. simpl in e_len, e_el.
  intermediate_path (m' ,, transportf (λ i, stn i -> X) e_len g).
  - apply transportf_eq.
  - apply maponpaths.
    intermediate_path (g ∘ transportb stn e_len).
    + apply transportf_fun.
    + apply funextfun. intro x. induction x as [ i b ].
      simple refine (_ @ e_el _ _ _).
      * unfold funcomp.
        apply maponpaths.
        apply transport_stn.
Defined.

(** The following lemma requires in the assumption [ e_el ] only one comparison [ i < length g ]
 and one comparison [ i < length g' ] for each i instead of all such comparisons as in the
 original version [ seq_key_eq_lemma ] . **)

Definition seq_key_eq_lemma' {X :UU} (g g' : Sequence X) :
  length g = length g' ->
  (Π i, Σ ltg : i < length g, Σ ltg' : i < length g',
                                        g (i ,, ltg) = g' (i ,, ltg')) ->
  g=g'.
Proof.
  intros ? ? ? k r.
  apply seq_key_eq_lemma.
  * assumption.
  * intros.
    induction (r i) as [ p [ q e ]].
    simple refine (_ @ e @ _).
    - apply maponpaths, maponpaths. apply propproperty.
    - apply maponpaths, maponpaths. apply propproperty.
Defined.

Local Definition empty_fun {X} : stn 0 -> X.
Proof. intros ? i. contradicts i negstn0. Defined.

Notation fromstn0 := empty_fun.

Definition nil {X} : Sequence X.
Proof. intros. exact (0,, empty_fun). Defined.

Definition append_fun {X n} : (stn n -> X) -> X -> stn (S n) -> X.
Proof.
  intros ? ? x y i.
  induction (natlehchoice4 (pr1 i) n (pr2 i)) as [c|d].
  { exact (x (pr1 i,,c)). }
  { exact y. }
Defined.

Definition compute_pr1_dni_last n (i:stn n) : pr1 (dni lastelement i) = pr1 i.
Proof.
  intros. unfold dni,di; simpl. induction (natlthorgeh i n) as [q|q].
  - reflexivity.
  - contradicts (pr2 i) (natlehneggth q).
Defined.

Definition replace_dni_last n : dni lastelement = @dni_lastelement n.
Proof. intros. apply funextfun; intros i. apply isinjstntonat. exact (compute_pr1_dni_last n i). Defined.

Definition append_fun_compute_1 {X n} (s:stn n->X) (x:X) i : append_fun s x (dni_lastelement i) = s i.
Proof.
  intros.
  unfold dni_lastelement; simpl.
  induction i as [i b]; simpl.
  unfold append_fun; simpl.
  induction (natlehchoice4 i n (natlthtolths i n b)) as [p|p].
  - simpl. apply maponpaths. apply isinjstntonat; simpl. reflexivity.
  - simpl. destruct p. induction (isirreflnatlth i b).
Defined.

Definition append_fun_compute_2 {X n} (s:stn n->X) (x:X) : append_fun s x lastelement = x.
Proof.
  intros.
  unfold append_fun; simpl.
  induction (natlehchoice4 n n (natgthsnn n)) as [a|a].
  - simpl. contradicts a (isirreflnatlth n).
  - simpl. reflexivity.
Defined.

Definition append {X} : Sequence X -> X -> Sequence X.
Proof. intros ? x y. exact (S (length x),, append_fun (pr2 x) y).
Defined.

Local Notation "s □ x" := (append s x) (at level 64, left associativity).

Definition stn0_fun_iscontr X : iscontr (stn 0 -> X).
Proof.
  intros. apply (@iscontrweqb _ (empty -> X)).
  - apply invweq. apply weqbfun. apply weqstn0toempty.
  - apply iscontrfunfromempty.
Defined.

Definition nil_unique {X} (x : stn 0 -> X) : nil = (0,,x).
Proof.
  intros. apply pair_path_in2. apply isapropifcontr. apply stn0_fun_iscontr.
Defined.

Definition isaset_transportf {X : hSet} (P : X ->UU) {x : X} (e : x = x) (p : P x) :
  transportf P e p = p.
(* move upstream *)
Proof. intros ? ? ? ? ?.
       induction (pr1 ((setproperty _) _ _ (idpath _) e)).
       reflexivity.
Defined.

(* induction principle for contractible types, as a warmup *)

(* Three ways.  Use induction: *)

Definition iscontr_rect' X (i : iscontr X) (x0 : X) (P : X ->UU) (p0 : P x0) : Π x:X, P x.
Proof. intros. induction (pr1 (isapropifcontr i x0 x)). exact p0. Defined.

Definition iscontr_rect_compute' X (i : iscontr X) (x : X) (P : X ->UU) (p : P x) :
  iscontr_rect' X i x P p x = p.
Proof.
  intros.
  (* this step might be a problem in more complicated situations: *)
  unfold iscontr_rect'.
  induction (pr1 (isasetifcontr i x x (idpath _) (pr1 (isapropifcontr i x x)))).
  reflexivity.
Defined.

(* ... or use weqsecovercontr, but specializing x to pr1 i: *)

Definition iscontr_rect'' X (i : iscontr X) (P : X ->UU) (p0 : P (pr1 i)) : Π x:X, P x.
Proof. intros. exact (invmap (weqsecovercontr P i) p0 x). Defined.

Definition iscontr_rect_compute'' X (i : iscontr X) (P : X ->UU) (p : P(pr1 i)) :
  iscontr_rect'' X i P p (pr1 i) = p.
Proof. try reflexivity. intros. exact (homotweqinvweq (weqsecovercontr P i) p).
Defined.

(* .... or use transport explicitly: *)

Definition iscontr_adjointness X (is:iscontr X) (x:X) : pr1 (isapropifcontr is x x) = idpath x.
(* we call this adjointness, because if [unit] had η-reduction, then adjointness of
   the weq [unit ≃ X] would give it to us, in the case where x is [pr1 is] *)
Proof. intros. now apply isasetifcontr. Defined.

Definition iscontr_rect X (is : iscontr X) (x0 : X) (P : X ->UU) (p0 : P x0) : Π x:X, P x.
Proof. intros. exact (transportf P (pr1 (isapropifcontr is x0 x)) p0). Defined.

Definition iscontr_rect_compute X (is : iscontr X) (x : X) (P : X ->UU) (p : P x) :
  iscontr_rect X is x P p x = p.
Proof. intros. unfold iscontr_rect. now rewrite iscontr_adjointness. Defined.

Corollary weqsecovercontr':     (* reprove weqsecovercontr, move upstream *)
  Π (X:UU) (P:X->UU) (is:iscontr X), (Π x:X, P x) ≃ P (pr1 is).
Proof.
  intros.
  set (x0 := pr1 is).
  set (secs := Π x : X, P x).
  set (fib  := P x0).
  set (destr := (λ f, f x0) : secs->fib).
  set (constr:= iscontr_rect X is x0 P : fib->secs).
  exists destr.
  apply (gradth destr constr).
  - intros f. apply funextsec; intros x.
    unfold destr, constr.
    apply transport_section.
  - apply iscontr_rect_compute.
Defined.

(*  *)

Definition nil_length {X} (x : Sequence X) : length x = 0 <-> x = nil.
Proof.
  intros. split.
  - intro e. induction x as [n x]. simpl in e.
    induction (!e). apply pathsinv0. apply nil_unique.
  - intro h. induction (!h). reflexivity.
Defined.

Definition drop {X} (x:Sequence X) : length x != 0 -> Sequence X.
Proof.
  intros ? [n x] h.
  induction n as [|n].
  - simpl in h. contradicts h (idpath 0).
  - exact (n,,x ∘ dni_lastelement).
Defined.

Definition drop' {X} (x:Sequence X) : x != nil -> Sequence X.
Proof. intros ? ? h. exact (drop x (pr2 (logeqnegs (nil_length x)) h)). Defined.

Definition drop_and_append {X n} (x : stn (S n) -> X) :
  append (n,,x ∘ dni_lastelement) (x lastelement) = (S n,, x).
Proof.
  intros.
  apply (maponpaths (tpair _ (S n))).
  apply funextfun; intros [i b].
  simpl.
  induction (natlehchoice4 i n b) as [p|p].
  - unfold funcomp; simpl.
    unfold append_fun. simpl.
    induction (natlehchoice4 i n b) as [q|q].
    + simpl. apply maponpaths. apply isinjstntonat; simpl. reflexivity.
    + induction q. contradicts p (isirreflnatlth i).
  - induction p.
    unfold append_fun; simpl.
    induction (natlehchoice4 i i b) as [r|r].
    * simpl. unfold funcomp; simpl. apply maponpaths.
      apply isinjstntonat; simpl. reflexivity.
    * simpl. apply maponpaths. apply isinjstntonat; simpl. reflexivity.
Defined.

Definition drop_and_append' {X n} (x : stn (S n) -> X) :
  append (drop (S n,,x) (negpathssx0 _)) (x lastelement) = (S n,, x).
Proof. intros. apply drop_and_append. Defined.

Definition disassembleSequence {X} : Sequence X -> coprod unit (X × Sequence X).
Proof.
  intros ? x.
  induction x as [n x].
  induction n as [|n].
  - exact (ii1 tt).
  - exact (ii2(x lastelement,,(n,,x ∘ dni_lastelement))).
Defined.

Definition assembleSequence {X} : coprod unit (X × Sequence X) -> Sequence X.
Proof.
  intros ? co.
  induction co as [t|p].
  - exact nil.
  - exact (append (pr2 p) (pr1 p)).
Defined.

Lemma assembleSequence_ii2 {X} (p : X × Sequence X) :
  assembleSequence (ii2 p) = append (pr2 p) (pr1 p).
Proof. reflexivity. Defined.

Theorem SequenceAssembly {X} : Sequence X ≃ unit ⨿ (X × Sequence X).
Proof.
  intros. exists disassembleSequence. apply (gradth _ assembleSequence).
  { intros. induction x as [n x]. induction n as [|n].
    { apply nil_unique. }
    apply drop_and_append'. }
  intros co. induction co as [t|p].
  { unfold disassembleSequence; simpl. apply maponpaths.
    apply proofirrelevancecontr. apply iscontrunit. }
  induction p as [x y]. induction y as [n y].
  apply (maponpaths (@inr unit (X × Sequence X))).
  unfold append_fun, lastelement, funcomp; simpl.
  unfold append_fun. simpl.
  induction (natlehchoice4 n n (natgthsnn n)) as [e|e].
  { contradicts e (isirreflnatlth n). }
  simpl. apply maponpaths, maponpaths.
  apply funextfun; intro i. clear e. induction i as [i b].
  unfold funcomp, dni_lastelement; simpl.
  induction (natlehchoice4 i n (natlthtolths i n b)) as [d|d].
  { simpl. apply maponpaths. now apply isinjstntonat. }
  simpl. induction d; contradicts b (isirreflnatlth i).
Defined.

Definition Sequence_rect {X} {P : Sequence X ->UU}
           (p0 : P nil)
           (ind : Π (x : Sequence X) (y : X), P x -> P (append x y))
           (x : Sequence X) : P x.
Proof. intros. induction x as [n x]. induction n as [|n IH].
  - exact (transportf P (nil_unique x) p0).
  - exact (transportf P (drop_and_append x)
                      (ind (n,,x ∘ dni_lastelement)
                           (x lastelement)
                           (IH (x ∘ dni_lastelement)))).
Defined.

Lemma Sequence_rect_compute_nil {X} {P : Sequence X ->UU} (p0 : P nil)
      (ind : Π (s : Sequence X) (x : X), P s -> P (append s x)) :
  Sequence_rect p0 ind nil = p0.
Proof.
  intros.
  try reflexivity.
  unfold Sequence_rect; simpl.
  change p0 with (transportf P (idpath nil) p0) at 2.
  apply (maponpaths (λ e, transportf P e p0)).
  exact (maponpaths (maponpaths functionToSequence) (iscontr_adjointness _ _ _)).
Defined.

Lemma Sequence_rect_compute_cons
      {X} {P : Sequence X ->UU} (p0 : P nil)
      (ind : Π (s : Sequence X) (x : X), P s -> P (append s x))
      (p := Sequence_rect p0 ind) (x:X) (l:Sequence X) :
  p (append l x) = ind l x (p l).
Proof.
  intros.
  cbn.


  (* proof in progress... *)

Abort.

Lemma append_length {X} (x:Sequence X) (y:X) :
  length (append x y) = S (length x).
Proof. intros. reflexivity. Defined.

Definition concatenate {X : UU} : binop (Sequence X)
  := λ x y, functionToSequence (concatenate' x y).

Definition concatenate_length {X} (x y:Sequence X) :
  length (concatenate x y) = length x + length y.
Proof. intros. reflexivity. Defined.

(** Versions of concatenate_0 for the alternative concatenate *)
Definition concatenate_0 {X : UU} (s : Sequence X) (t : stn 0 -> X) : concatenate s (0,,t) = s.
Proof.
  intros.
  use seq_key_eq_lemma.
  - apply natplusr0.
  - intros i ltg ltg'. cbn. unfold coprod_rect.
    unfold concatenate', weqfromcoprodofstn_invmap.
    match goal with |- coprod_rect _ _ _ (coprod_rect _ _ _ ?x) = _ => induction x as [H | H]; cbn end.
    + apply maponpaths. now apply subtypeEquality_prop.
    + apply fromempty. apply (natlthtonegnatgeh _ _ ltg' H).
Qed.

Definition concatenate_0' {X : UU} (s : Sequence X) (t : stn 0 -> X) : concatenate (0,,t) s = s.
Proof.
  intros. apply pathsinv0. induction s as [s l].
  use seq_key_eq_lemma.
  - apply idpath.
  - intros i ltg ltg'. cbn. unfold coprod_rect.
    induction (natchoice0 s) as [H | H].
    + apply fromempty. cbn in ltg'. rewrite <- H in ltg'. apply (nopathsfalsetotrue ltg').
    + apply maponpaths.
      use total2_paths.
      * cbn. apply pathsinv0. apply natminuseqn.
      * apply proofirrelevance. apply propproperty.
Qed.

Definition concatenateStep {X : UU} (x : Sequence X) {n : nat} (y : stn (S n) -> X) :
  concatenate x (S n,,y) = append (concatenate x (n,,y ∘ dni_lastelement)) (y lastelement).
Proof.
  intros X x. induction x as [x l]. intros n y.
  use seq_key_eq_lemma.
  - cbn. apply natplusnsm.
  - intros i ltg ltg'. cbn. unfold append_fun. unfold coprod_rect. cbn.
    unfold concatenate'.
    unfold weqfromcoprodofstn_invmap. cbn. unfold coprod_rect.
    induction (natlthorgeh i x) as [H | H].
    + induction (natlehchoice4 i (x + n) ltg') as [H1 | H1].
      * apply idpath.
      * apply fromempty. rewrite H1 in H.
        set (tmp := natlehnplusnm x n).
        set (tmp2 := natlehlthtrans _ _ _ tmp H).
        use (isirrefl_natneq x). exact (natlthtoneq _ _ tmp2).
    + induction (natchoice0 (S n)) as [H2 | H2].
      * apply fromempty. use (negpaths0sx n). exact H2.
      * induction (natlehchoice4 i (x + n) ltg') as [H' | H'].
        -- induction (natchoice0 n) as [H3 | H3].
           ++ apply fromempty. induction H3. rewrite natplusr0 in H'.
              use (natlthtonegnatgeh i x H' H).
           ++ unfold funcomp. apply maponpaths.
              use total2_paths.
              ** apply idpath.
              ** apply proofirrelevance. apply propproperty.
        -- apply maponpaths.
           use total2_paths.
           ++ cbn. rewrite H'. rewrite natpluscomm. apply plusminusnmm.
           ++ apply proofirrelevance. apply propproperty.
Qed.

Definition partition {X : UU} {n : nat} (f : stn n -> nat) (x : stn (stnsum f) -> X) :
  Sequence (Sequence X).
Proof.
  intros. exists n. intro i. exists (f i). exact (lex_curry x i).
Defined.

Definition flatten {X : UU} : Sequence (Sequence X) -> Sequence X.
Proof.
  intros ? x. exists (stnsum (length ∘ x)). exact (lex_uncurry (funcomp' x sequenceToFunction)).
Defined.

Definition total2_step_f {n} (X:stn (S n) ->UU) :
  (Σ i, X i)
    ->
  (Σ (i:stn n), X (dni lastelement i)) ⨿ X lastelement.
Proof.
  intros ? ? [[j J] x].
  induction (natlehchoice4 j n J) as [J'|K].
  - apply ii1.
    exists (j,,J').
    assert (e : (dni lastelement (j,, J')) = (j,, J) ).
    { apply isinjstntonat. rewrite replace_dni_last. reflexivity. }
    exact (transportb _ e x).
  - apply ii2.
    induction (!K); clear K.
    assert (e : (n,, J) = lastelement).
    { apply isinjstntonat. reflexivity. }
    exact (transportf _ e x).
Defined.

Definition total2_step_b {n} (X:stnset (S n) ->UU) :
  (Σ (i:stn n), X (dni lastelement i)) ⨿ X lastelement
    ->
  (Σ i, X i).
Proof.
  intros ? ? x.
  induction x as [jx|x].
  - exact (dni lastelement (pr1 jx),,pr2 jx).
  - exact (lastelement,,x).
Defined.

Definition total2_step_bf {n} (X:stnset (S n) ->UU) :
   total2_step_b X ∘ total2_step_f X ~ idfun _.
Proof.
  intros.
  unfold homot, funcomp, idfun.
  intros [[j J] x].
  unfold total2_step_b, total2_step_f.
  induction (natlehchoice4 j n J) as [J'|K].
  + simpl.
    simple refine (total2_paths _ _).
    * simpl. rewrite replace_dni_last. apply isinjstntonat. reflexivity.
    * rewrite replace_dni_last. unfold dni_lastelement.  simpl.
      change (λ x0 : stn (S n), X x0) with X.
      rewrite transport_f_b. apply (isaset_transportf X).
  + induction (!K). simpl.
    simple refine (total2_paths _ _).
    * simpl. now apply isinjstntonat.
    * simpl. assert (d : idpath n = K).
      { apply isasetnat. }
      induction d. simpl. rewrite transport_f_f. apply (isaset_transportf X).
Defined.

Definition total2_step {n} (X:stnset (S n) ->UU) :
  (Σ i, X i) ≃ (Σ (i:stn n), X (dni lastelement i)) ⨿ X lastelement.
Proof.
  intros. set (f := weqdnicoprod n lastelement).
  intermediate_weq (Σ x : stn n ⨿ unit, X (f x)).
  { apply invweq. apply weqfp. }
  intermediate_weq ((Σ i, X (f (ii1 i))) ⨿ Σ t, X (f (ii2 t))).
  { apply weqtotal2overcoprod. }
  apply weqcoprodf. { apply weqfibtototal; intro i. apply idweq. }
  apply weqtotal2overunit.
Defined.

Lemma invweq_to_invmap {X Y x} (f:X≃Y) : invweq f x = invmap f x.
Proof. reflexivity. Defined.

Definition total2_step_compute_2 {n} (X:stnset (S n) ->UU) :
  invmap (total2_step X) ~ total2_step_b X.
Proof.
  intros. intros [[i x]|y]; reflexivity. (* amazingly easy, why? *)
Defined.

Definition total2_step_compute_1 {n} (X:stnset (S n) ->UU) :
  total2_step X ~ total2_step_f X.
Proof. intros. intros [i x].
       try reflexivity.
Abort.

Definition isinjinvmap {X Y} (v w:X≃Y) : invmap v ~ invmap w -> v ~ w.
Proof. intros ? ? ? ? h x.
  intermediate_path (w ((invmap w) (v x))).
  { apply pathsinv0. apply homotweqinvweq. }
  rewrite <- h. rewrite homotinvweqweq. reflexivity. Defined.

Definition isinjinvmap' {X Y} (v w:X->Y) (v' w':Y->X) : w ∘ w' ~ idfun Y -> v' ∘ v ~ idfun X -> v' ~ w' -> v ~ w.
Proof. intros ? ? ? ? ? ? p q h x .
  intermediate_path (w (w' (v x))).
  { apply pathsinv0. apply p. }
  apply maponpaths. rewrite <- h. apply q. Defined.

Definition total2_step_compute_1 {n} (X:stn (S n) ->UU) :
  total2_step X ~ total2_step_f X.
Proof.
  intros.
  apply invhomot.
  refine (isinjinvmap' (total2_step_f X) (total2_step X)
                       (total2_step_b X) (invmap (total2_step X))
                       _ _ _ ).
  { intro x. apply homotweqinvweq. }
  { apply total2_step_bf. }
  { apply invhomot. apply total2_step_compute_2. }
Defined.

Corollary total2_step' {n} (f:stn (S n) -> nat) :
  (Σ i, stn (f i))
    ≃
  (Σ (i:stn n), stn (f (dni lastelement i))) ⨿ stn (f lastelement).
Proof. intros. apply (total2_step (stn ∘ f)). Defined.

Definition weqstnsum1' {n} (f:stn (S n)->nat ) : (Σ i, stn (f i)) ≃ stn (stnsum f).
Proof. intros.
  intermediate_weq ((Σ (i:stn n), stn (f (dni lastelement i))) ⨿ stn (f lastelement)).
  { apply total2_step'. }
  intermediate_weq (stn (stnsum (f ∘ dni lastelement)) ⨿ stn (f lastelement)).
  { apply weqcoprodf. { apply weqstnsum1. } apply idweq. }
  apply weqfromcoprodofstn.
Defined.

Definition invmap_over_weqcomp {X Y Z} (g:Y≃Z) (f:X≃Y) :
  invmap (g∘f)%weq = invmap f ∘ invmap g.
Proof.
  intros.
  apply funextfun; intro z.
  set (a:=invmap (g ∘ f)%weq z).
  rewrite <- (homotweqinvweq (g∘f)%weq z).
  change a with (invmap (g ∘ f)%weq z).
  rewrite weqcomp_to_funcomp.
  unfold funcomp.
  rewrite (homotinvweqweq g).
  rewrite (homotinvweqweq f).
  reflexivity.
Defined.

Definition weqstnsum1_step {n} (f:stn (S n) -> nat) :
  weqstnsum1 f = weqstnsum1' f.
Proof.
  intros.
  apply isinjpr1weq.
  apply funextfun; intros [k p].
  unfold weqstnsum1'.
  unfold total2_step', total2_step.
  rewrite 4? weqcomp_to_funcomp.
  unfold funcomp.
  change (((invweq
                  (weqfp (weqdnicoprod n lastelement)
                         (λ i : stn (S n), stn (f i)))) (k,, p)))
            with ((invmap
                  (weqfp (weqdnicoprod n lastelement)
                     (λ i : stn (S n), stn (f i)))) (k,, p)).
  rewrite weqfp_compute_2.
  unfold weqdnicoprod at 11.
  unfold weqfp_invmap.
  change (pr2 (tpair (λ i, stn(f i)) k p)) with p.
  change (pr1 (tpair (λ i, stn(f i)) k p)) with k.

  (* perhaps also prove this is by equipping everything in sight with a well-ordering, preserved by all the equivalences involved *)
Abort.

Definition flattenStep {X} (x: NonemptySequence (Sequence X)) :
  flatten x = concatenate (flatten (composeSequence x dni_lastelement)) (lastValue x).
Proof.
  intros.
  rewrite <- replace_dni_last.  (* replace it, because stnsum doesn't use it *)
  (* we have arranged for the lengths to be definitionally equal, so check it: *)
  match goal with |- ?x = ?y => assert(E : length x = length y) end.
  { reflexivity. }
  (* thus it suffices to check the functions are equal, so let's work to get a clean statement about them *)
  induction x as [n x].
  set (xlens := λ i, length(x i)).
  set (xvals := λ i, λ j:stn (xlens i), x i j).
  Check (lex_uncurry xvals).
  set (xlens' := xlens ∘ dni lastelement).
  set (xvals' := λ j, xvals (dni lastelement j)).
  match goal with |- ?x = ?y => assert(F : sequenceToFunction x = sequenceToFunction y) end.
  {
    set_id_type W.              (* now the equation is between elements of type W *)
    change (stnsum _) with (stnsum xlens') in W.
    change ((length ∘ x) lastelement) with (lastValue xlens) in W.
    unfold flatten.
    change (lastValue _) with (lastValue x).
    unfold funcomp'.
    unfold sequenceToFunction.
    rewrite rewrite_pr2_tpair.
    change (lex_uncurry _) with (lex_uncurry xvals) at 1.
    change (lex_uncurry _) with (lex_uncurry xvals') at 2.
    unfold concatenate.
    unfold functionToSequence.
    rewrite rewrite_pr2_tpair.



(*     rewrite rewrite_pr2_tpair. *)
(*     change (length _) with (S n). *)
(*     unfold NonemptySequenceToSequence, functionToSequence, length'. *)
(*     Set Printing All. *)
(*     idtac. *)


(* rewrite (rewrite_pr1_tpair n). *)

(* rewrite rewrite_pr2_tpair. *)


(*   apply pair_path_in2. *)


(*   unfold flatten at 1. *)
(*   simpl. *)
(*   change (length _ + length _) with (length (flatten x)). *)

(*   apply funextfun; intros k. *)
(*   cbn. *)
(*   unfold length'. *)
(*   (* unfold weqfromcoprodofstn_invmap. *) *)
(*   cbn. *)


(*   match goal with |- _ = coprod_rect _ _ _ ?x => induction x as [p|q] end. (* oops, bad induction *) *)
(*   - cbn. *)
(*     induction x as [n x]. *)
(*     cbn. *)
(*     set (m := λ i, length(x i)). *)
(*     set (y := λ i, λ j:stn (m i), x i j). *)
(*     Check (lex_uncurry y). *)
(*     change (sequenceToFunction ∘ x) with y. *)
(*     match goal with |- lex_uncurry _ _ = lex_uncurry ?t _ => change t with (y ∘ dni lastelement) end. *)

(*     change (sequenceToFunction ∘ (x ∘ dni lastelement)) with (y ∘ dni lastelement). *)

(*     admit. *)
(*   - cbn. *)
(*     admit. *)
(* Defined. *)
Abort.

Definition isassoc_concatenate {X} (x y z:Sequence X) :
  concatenate (concatenate x y) z = concatenate x (concatenate y z).
Proof.
  intros.
  simple refine (total2_paths _ _).
  - simpl. apply natplusassoc.
  - apply sequenceEquality; intros i.


Abort.

Definition isassoc_concatenate {X : UU} (x y z : Sequence X) :
  concatenate (concatenate x y) z = concatenate x (concatenate y z).
Proof.
  intros X x y z.
  use seq_key_eq_lemma.
  - cbn. rewrite natplusassoc. apply idpath.
  - intros i ltg ltg'. cbn. unfold concatenate'. unfold weqfromcoprodofstn_invmap. unfold coprod_rect. cbn.
    induction (natlthorgeh i (length x + length y)) as [H | H].
    + induction (natlthorgeh (stnpair (length x + length y) i H) (length x)) as [H1 | H1].
      * induction (natlthorgeh i (length x)) as [H2 | H2].
        -- apply maponpaths. apply isinjstntonat. apply idpath.
        -- apply fromempty. exact (natlthtonegnatgeh i (length x) H1 H2).
      * induction (natchoice0 (length y)) as [H2 | H2].
        -- apply fromempty. induction H2. induction (! (natplusr0 (length x))).
           apply (natlthtonegnatgeh i (length x) H H1).
        -- induction (natlthorgeh i (length x)) as [H3 | H3].
           ++ apply fromempty. apply (natlthtonegnatgeh i (length x) H3 H1).
           ++ induction (natchoice0 (length y + length z)) as [H4 | H4].
              ** apply fromempty. induction (! H4).
                 use (isirrefl_natneq (length y)).
                 use natlthtoneq.
                 use (natlehlthtrans (length y) (length y + length z) (length y) _ H2).
                 apply natlehnplusnm.
              ** cbn. induction (natlthorgeh (i - length x) (length y)) as [H5 | H5].
                 --- apply maponpaths. apply isinjstntonat. apply idpath.
                 --- apply fromempty.
                     use (natlthtonegnatgeh (i - (length x)) (length y)).
                     +++ set (tmp := natlthandminusl i (length x + length y) (length x) H
                                                     (natlthandplusm (length x) _ H2)).
                         rewrite (natpluscomm (length x) (length y)) in tmp.
                         rewrite plusminusnmm in tmp. exact tmp.
                     +++ exact H5.
    + induction (natchoice0 (length z)) as [H1 | H1].
      * apply fromempty. cbn in ltg. induction H1. rewrite natplusr0 in ltg.
        exact (natlthtonegnatgeh i (length x + length y) ltg H).
      * induction (natlthorgeh i (length x)) as [H2 | H2].
        -- apply fromempty.
           use (natlthtonegnatgeh i (length x) H2).
           use (istransnatgeh i (length x + length y) (length x) H).
           apply natgehplusnmn.
        -- induction (natchoice0 (length y + length z)) as [H3 | H3].
           ++ apply fromempty. cbn in ltg'. induction H3. rewrite natplusr0 in ltg'.
              exact (natlthtonegnatgeh i (length x) ltg' H2).
           ++ cbn. induction (natlthorgeh (i - length x) (length y)) as [H4 | H4].
              ** apply fromempty.
                 use (natlthtonegnatgeh i (length x + length y) _ H).
                 apply (natlthandplusr _ _ (length x)) in H4.
                 rewrite minusplusnmm in H4.
                 --- rewrite natpluscomm in H4. exact H4.
                 --- exact H2.
              ** apply maponpaths. apply isinjstntonat. cbn. apply (! (natminusminus _ _ _)).
Qed.

(** Reverse *)

Definition reverse {X : UU} (x : Sequence X) : Sequence X :=
  functionToSequence (fun i : (stn (length x)) => x (dualelement i)).

Lemma reversereverse {X : UU} (x : Sequence X) : reverse (reverse x) = x.
Proof.
  intros X x.
  use seq_key_eq_lemma.
  - apply idpath.
  - intros i ltg ltg'. unfold reverse, dualelement, coprod_rect. cbn.
    set (e := natgthtogehm1 (length x) i ltg').
    induction (natchoice0 (length x)) as [H | H].
    + apply maponpaths. apply isinjstntonat. cbn. apply (minusminusmmn _ _ e).
    + apply maponpaths. apply isinjstntonat. cbn. apply (minusminusmmn _ _ e).
Qed.

Lemma reverse_index {X : UU} (x : Sequence X) (i : stn (length x)) :
  (reverse x) (dualelement i) = x i.
Proof.
  intros X x i. cbn. unfold dualelement, coprod_rect.
  set (e := natgthtogehm1 (length x) i (stnlt i)).
  induction (natchoice0 (length x)) as [H' | H'].
  - apply maponpaths. apply isinjstntonat. cbn. apply (minusminusmmn _ _ e).
  - apply maponpaths. apply isinjstntonat. cbn. apply (minusminusmmn _ _ e).
Qed.

Lemma reverse_index' {X : UU} (x : Sequence X) (i : stn (length x)) :
  (reverse x) i = x (dualelement i).
Proof.
  intros X x i. cbn. unfold dualelement, coprod_rect.
  induction (natchoice0 (length x)) as [H' | H'].
  - apply maponpaths. apply isinjstntonat. cbn. apply idpath.
  - apply maponpaths. apply isinjstntonat. cbn. apply idpath.
Qed.

(* End of the file *)
