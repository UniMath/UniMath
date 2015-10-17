Require Export UniMath.Foundations.StandardFiniteSets.
Unset Automatic Introduction.

(* move upstream *)

(* *)

Definition Sequence X := Σ n, stn n -> X.

Definition Sequence_to_function {X} (x:Sequence X) := pr2 x.
Coercion Sequence_to_function : Sequence >-> Funclass.

Definition sequencePair {X n} (f:stn n -> X) : Sequence X := (n,,f).

Definition transport_stn m n i (b:i<m) (p:m=n) :
  transportf stn p (i,,b) = (i,,transportf (λ m,i<m) p b).
Proof. intros. induction p. reflexivity. Defined.

Definition sequenceEquality {X m n} (f:stn m->X) (g:stn n->X) (p:m=n) :
  (∀ i, f i = g (transportf stn p i))
  -> transportf (λ m, stn m->X) p f = g.
Proof. intros ? ? ? ? ? ? e. induction p. apply funextfun. exact e. Defined.

Definition length {X} : Sequence X -> nat := pr1.

Local Definition empty_fun {X} : stn 0 -> X.
Proof. intros ? i. contradicts i negstn0. Defined.

Definition nil {X} : Sequence X.
Proof. intros. exact (0,, empty_fun). Defined.

Definition append_fun {X n} : (stn n -> X) -> X -> stn (S n) -> X.
Proof.
  intros ? ? x y i.
  induction (natlehchoice4 (pr1 i) n (pr2 i)) as [c|d].
  { exact (x (pr1 i,,c)). }
  { exact y. }
Defined.

Definition compute_pr1_dni_last n i : pr1 (dni n (lastelement _) i) = pr1 i.
Proof.
  intros. unfold dni; simpl. induction (natlthorgeh i n) as [q|q].
  - reflexivity.
  - contradicts (pr2 i) q.
Defined.

Definition replace_dni_last n : dni n (lastelement _) = dni_lastelement.
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

Definition append_fun_compute_2 {X n} (s:stn n->X) (x:X) : append_fun s x (lastelement _) = x.
Proof.
  intros.
  unfold append_fun; simpl.
  induction (natlehchoice4 n n (natgthsnn n)) as [a|a].
  - simpl. contradicts a (isirreflnatlth n).
  - simpl. reflexivity.
Defined.

Definition append {X} : Sequence X -> X -> Sequence X.
Proof.
  intros ? x y.
  exists (S (length x)).
  induction x as [n x]; simpl.
  exact (append_fun x y).
Defined.

Definition stn0_fun_iscontr X : iscontr (stn 0 -> X).
Proof.
  intros. apply (@iscontrweqb _ (empty -> X)).
  - apply invweq. apply weqbfun. apply weqstn0toempty.
  - apply iscontrfunfromempty.
Qed.  

Definition nil_unique {X} (x : stn 0 -> X) : nil = (0,,x).
Proof.
  intros. apply pair_path_in2. apply isapropifcontr. apply stn0_fun_iscontr.
Defined.

(* induction principle for contractible types, as a warmup *)

Definition isaset_transport (X : UU) (x : X) (P : X -> UU) (p : P x) (i : isaset X) (e : x = x) :
  transportf P e p = p.
Proof. intros. induction (pr1 (i x x (idpath _) e)). reflexivity. Defined.

(* Three ways.  Use induction: *)

Definition iscontr_rect' X (i : iscontr X) (x0 : X) (P : X -> UU) (p0 : P x0) : ∀ x:X, P x.
Proof. intros. induction (pr1 (isapropifcontr i x0 x)). exact p0. Defined.

Definition iscontr_rect_compute' X (i : iscontr X) (x : X) (P : X -> UU) (p : P x) :
  iscontr_rect' X i x P p x = p.
Proof.
  intros.
  (* this step might be a problem in more complicated situations: *)
  unfold iscontr_rect'.
  induction (pr1 (isasetifcontr i x x (idpath _) (pr1 (isapropifcontr i x x)))).
  reflexivity.
Defined.

(* ... or use weqsecovercontr, but specializing x to pr1 i: *)

Definition iscontr_rect'' X (i : iscontr X) (P : X -> UU) (p0 : P (pr1 i)) : ∀ x:X, P x.
Proof. intros. exact (invmap (weqsecovercontr P i) p0 x). Defined.
       
Definition iscontr_rect_compute'' X (i : iscontr X) (P : X -> UU) (p : P(pr1 i)) :
  iscontr_rect'' X i P p (pr1 i) = p.
Proof. try reflexivity. intros. exact (homotweqinvweq (weqsecovercontr _ i) _).
Defined.

(* .... or use transport explicitly: *)

Definition iscontr_adjointness X (is:iscontr X) (x:X) : pr1 (isapropifcontr is x x) = idpath x.
(* we call this adjointness, because if [unit] had η-reduction, then adjointness of
   the weq [unit ≃ X] would give it to us, in the case where x is [pr1 is] *)
Proof. intros. now apply isasetifcontr. Defined.

Definition iscontr_rect X (is : iscontr X) (x0 : X) (P : X -> UU) (p0 : P x0) : ∀ x:X, P x.
Proof. intros. exact (transportf P (pr1 (isapropifcontr is x0 x)) p0). Defined.

Definition iscontr_rect_compute X (is : iscontr X) (x : X) (P : X -> UU) (p : P x) :
  iscontr_rect X is x P p x = p.
Proof. intros. unfold iscontr_rect. now rewrite iscontr_adjointness. Defined.

Corollary weqsecovercontr':     (* reprove weqsecovercontr, move upstream *)
  ∀ (X:UU) (P:X->UU) (is:iscontr X), (∀ x:X, P x) ≃ P (pr1 is).
Proof.
  intros.
  set (x0 := pr1 is).
  set (secs := ∀ x : X, P x).
  set (fib  := P x0).
  set (destr := (λ f, f x0) : secs->fib).
  set (constr:= iscontr_rect X is x0 P : fib->secs).
  refine (destr,,gradth destr constr _ _).
  - intros f. apply funextsec; intros x. apply transport_section.
  - apply iscontr_rect_compute.
Defined.

(*  *)

Definition nil_length {X} (x : Sequence X) : length x = 0 <-> x = nil.
Proof.
  intros.
  split.
  - intro e.
    induction x as [n x].
    simpl in e.
    induction (!e).
    apply pathsinv0.
    apply nil_unique.
  - intro h.
    induction (!h).
    reflexivity.
Defined.

Definition drop {X} (x:Sequence X) : length x != 0 -> Sequence X.
Proof.
  intros ? [n x] h.
  induction n as [|n].
  - contradicts h (idpath 0).
  - exact (n,,x ∘ dni_lastelement).
Defined.

Definition drop' {X} (x:Sequence X) : x != nil -> Sequence X.
Proof. intros ? ? h. exact (drop x (pr2 (logeqnegs (nil_length x)) h)). Defined.

Definition drop_and_append {X n} (x : stn (S n) -> X) :
  append (n,,x ∘ dni_lastelement) (x (lastelement _)) = (S n,, x).
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
  append (drop (S n,,x) (negpathssx0 _)) (x (lastelement _)) = (S n,, x).
Proof. intros. apply drop_and_append. Defined.

Definition disassembleSequence {X} : Sequence X -> coprod unit (X × Sequence X).
Proof.
  intros ? x.
  induction x as [n x].
  induction n as [|n].
  - exact (ii1 tt).
  - exact (ii2(x(lastelement _),,(n,,x ∘ dni_lastelement))).
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

Theorem SequenceAssembly {X} : Sequence X ≃ coprod unit (X × Sequence X).
Proof.
  intros.
  refine (disassembleSequence,, gradth _ assembleSequence _ _).
  - intros.
    induction x as [n x].
    induction n as [|n].
    + apply nil_unique.
    + apply drop_and_append'.
  - intros co.
    (* maybe isolate this case as a lemma *)
    induction co as [t|p].
    + simpl. apply maponpaths. apply proofirrelevancecontr.
      apply iscontrunit.
    + induction p as [x y].
      induction y as [n y].
      apply (maponpaths (@inr unit (X × Sequence X))).
      simpl.
      induction (natlehchoice4 n n (natgthsnn n)) as [b|c].
      * contradicts (isirreflnatlth n) b.
      * clear c.
        unfold append_fun, lastelement, funcomp.
        simpl.
        induction (natlehchoice4 n n (natgthsnn n)) as [e|e].
        { contradicts e (isirreflnatlth n). }
        { simpl. apply maponpaths. apply maponpaths.
          apply funextfun; intro i.
          induction i as [i b].
          unfold funcomp, dni_lastelement.
          simpl.
          induction (natlehchoice4 i n (natlthtolths i n b)) as [d|d].
          { simpl. apply maponpaths. apply isinjstntonat; simpl. reflexivity. }
          { simpl. induction d; contradicts b (isirreflnatlth i). } }
Defined.

Definition Sequence_rect {X} {P : Sequence X -> UU}
           (p0 : P nil)
           (ind : ∀ (x : Sequence X) (y : X), P x -> P (append x y))
           (x : Sequence X) : P x.
Proof. intros. induction x as [n x]. induction n as [|n IH].
  - exact (transportf _ (nil_unique x) p0).
  - exact (transportf _
                      (drop_and_append x)
                      (ind (n,,x ∘ dni_lastelement)
                           (x (lastelement _))
                           (IH (x ∘ dni_lastelement)))).
Defined.

Lemma Sequence_rect_compute_nil {X} {P : Sequence X -> UU} (p0 : P nil)
      (ind : ∀ (s : Sequence X) (x : X), P s -> P (append s x)) :
  Sequence_rect p0 ind nil = p0.
Proof.
  intros.
  try reflexivity.
  unfold Sequence_rect; simpl.
  change p0 with (transportf P (idpath nil) p0) at 2.
  apply (maponpaths (λ e, transportf P e p0)).
  exact (maponpaths (maponpaths sequencePair) (iscontr_adjointness _ _ _)).
Defined.

Lemma Sequence_rect_compute_cons
      {X} {P : Sequence X -> UU} (p0 : P nil)
      (ind : ∀ (s : Sequence X) (x : X), P s -> P (append s x))
      (x:X) (l:Sequence X) :
  Sequence_rect p0 ind (append l x) = ind l x (Sequence_rect p0 ind l). 
Proof.
  intros.

Abort.

Lemma append_length {X} (x:Sequence X) (y:X) :
  length (append x y) = S (length x).
Proof. intros. reflexivity. Defined.

Definition concatenate {X} : binop (Sequence X).
Proof.
  intros ? x y.
  exists (length x + length y).
  intros i.
  induction (invweq (weqfromcoprodofstn (length x) (length y)) i) as [j|k].
  - exact (x j).
  - exact (y k).
Defined.

Definition concatenate_length {X} (x y:Sequence X) :
  length (concatenate x y) = length x + length y.
Proof. intros. reflexivity. Defined.

Definition concatenateStep {X}  (x : Sequence X) {n} (y : stn (S n) -> X) :
  concatenate x (S n,,y) = append (concatenate x (n,,y ∘ dni_lastelement)) (y (lastelement _)).
Proof. intros.

Abort.

Definition curry {X} {Y:X->UU} {Z} (f: (Σ x:X, Y x) -> Z) : ∀ x, Y x -> Z.
Proof. intros ? ? ? ? ? y. exact (f(x,,y)). Defined.
Definition uncurry {X} {Y:X->UU} {Z} (g:∀ x (y:Y x), Z) : (Σ x, Y x) -> Z.
Proof. intros ? ? ? ? xy. exact (g (pr1 xy) (pr2 xy)). Defined.
Lemma uncurry_curry {X} {Y:X->UU} {Z} (f:(Σ x:X, Y x) -> Z): uncurry (curry f) = f.
  intros. apply funextfun. intros [x y]. reflexivity. Defined.
Lemma curry_uncurry {X} {Y:X->UU} {Z} (g:∀ x (y:Y x), Z) : curry (uncurry g) = g.
  intros. apply funextsec. intros x. apply funextfun. intros y. reflexivity. Defined.

Definition lex_ordering {n} (m:stn n->nat) := invweq (weqstnsum_idweq m) : stn (stnsum m) ≃ (Σ i : stn n, stn (m i)).
Definition inverse_lex_ordering {n} (m:stn n->nat) := weqstnsum_idweq m : (Σ i : stn n, stn (m i)) ≃ stn (stnsum m).

Definition lex_curry {X n} (m:stn n->nat) : (stn (stnsum m) -> X) -> (∀ (i:stn n), stn (m i) -> X).
Proof. intros ? ? ? f ? j. exact (f (inverse_lex_ordering m (i,,j))). Defined.
Definition lex_uncurry {X n} (m:stn n->nat) : (∀ (i:stn n), stn (m i) -> X) -> (stn (stnsum m) -> X).
Proof. intros ? ? ? g ij. exact (uncurry g (lex_ordering m ij)). Defined.

Definition partition {X n} (f:stn n -> nat) (x:stn (stnsum f) -> X) : Sequence (Sequence X).
Proof. intros. exists n. intro i. exists (f i). intro j. exact (x(inverse_lex_ordering f (i,,j))).
Defined.

Definition flatten {X} : Sequence (Sequence X) -> Sequence X.
Proof. intros ? x. exists (stnsum (length ∘ x)). exact (λ j, uncurry (pr2 x) (lex_ordering _ j)).
Defined.

Definition total2_step {n} (f:stn (S n) -> nat) : (Σ i, stn (f i)) ≃ (Σ (i:stn n), stn (f (dni _ (lastelement _) i))) ⨿ stn (f (lastelement _)).
Admitted.

Definition weqstnsum_idweq_step {n} (f:stn (S n) -> nat) :
  weqstnsum_idweq f = ((weqfromcoprodofstn _ _) ∘ (weqcoprodf (weqstnsum_idweq _) (idweq _)) ∘ total2_step f)%weq.
Proof.
Admitted.

Definition flattenStep {X n} (x: stn (S n) -> Sequence X) :
  flatten (S n,,x) = concatenate (flatten (n,,x ∘ dni_lastelement)) (x (lastelement _)).
Proof.
  intros.
  rewrite <- replace_dni_last.  (* replace it, because stnsum doesn't use it *)
  unfold flatten.
  simpl.


  apply pair_path_in2.
  apply funextfun; intros i.
  simpl.



Admitted.


Definition isassoc_concatenate {X} (x y z:Sequence X) :
  concatenate (concatenate x y) z = concatenate x (concatenate y z).
Proof.
  intros.
  refine (total2_paths _ _).
  - simpl. apply natplusassoc.
  - apply sequenceEquality; intros i.


Abort.


