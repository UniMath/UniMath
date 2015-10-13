Require Export UniMath.Foundations.StandardFiniteSets.
Unset Automatic Introduction.

(* move upstream *)

(* *)

Definition Sequence X := Σ n, stn n -> X.

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

Definition append {X} : Sequence X -> X -> Sequence X.
Proof.
  intros ? x y.
  exists (S (length x)).
  induction x as [m x]; simpl.
  intros [i b].
  induction (natlehchoice4 i m b) as [c|d].
  { exact (x (i,,c)). }
  { exact y. }
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
  - exact (n,,x ∘ dni_allButLast _).
Defined.

Definition drop' {X} (x:Sequence X) : x != nil -> Sequence X.
Proof. intros ? ? h. exact (drop x (pr2 (logeqnegs (nil_length x)) h)). Defined.

Definition drop_and_append {X n} (x : stn (S n) -> X) :
  append (n,,x ∘ dni_allButLast _) (x (lastelement _)) = (S n,, x).
Proof.
  intros.
  apply (maponpaths (tpair _ (S n))).
  apply funextfun; intros [i b].
  simpl.
  induction (natlehchoice4 i n b) as [p|p].
  - unfold funcomp; simpl.
    apply maponpaths.
    apply pair_path_in2.
    apply isasetbool.
  - simpl.
    apply maponpaths.
    induction p.
    apply pair_path_in2.
    apply isasetbool.
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
  - exact (ii2(x(lastelement _),,(n,,x ∘ dni_allButLast _))).
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
      * simpl.
        apply maponpaths.
        apply maponpaths.
        apply funextfun; intro i.
        induction i as [i b].
        unfold funcomp, dni_allButLast.
        induction (natlehchoice4 i n (natlthtolths i n b)) as [d|d].
        { simpl. apply maponpaths. apply maponpaths. apply isasetbool. }
        { induction d. contradicts (isirreflnatlth i) b. }
Defined.

Definition Sequence_rect {X} {P : Sequence X -> UU}
           (p0 : P nil)
           (ind : ∀ (x : Sequence X) (y : X), P x -> P (append x y))
           (x : Sequence X) : P x.
Proof. intros. induction x as [n x]. induction n as [|n IH].
  - exact (transportf _ (nil_unique x) p0).
  - exact (transportf _
                      (drop_and_append x)
                      (ind (n,,x ∘ dni_allButLast _)
                           (x (lastelement _))
                           (IH (x ∘ dni_allButLast _)))).
Defined.

Lemma Sequence_rect_compute_nil {X} {P : Sequence X -> UU} (p0 : P nil)
      (ind : ∀ (s : Sequence X) (x : X), P s -> P (append s x)) :
  Sequence_rect p0 ind nil = p0.
Proof.
  intros.
  try reflexivity.
  unfold Sequence_rect, nil; simpl.
  change p0 with (transportf P (idpath nil) p0) at 2.
  apply (maponpaths (λ e, transportf P e p0)).
  (* now [stn 0 -> X] is contractible, so is a set, etc. *)
Abort.

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
  intros ? x [n y].
  induction n as [|n IH].
  { exact x. }
  { exact (append (IH (y ∘ dni_allButLast _)) (y (lastelement _))). }
Defined.

Definition concatenate_length {X} (x y:Sequence X) :
  length (concatenate x y) = length x + length y.
Proof.
  intros.
  try reflexivity.
Admitted.

Definition concatenateStep {X}  (x : Sequence X) {n} (y : stn (S n) -> X) :
  concatenate x (S n,,y) = append (concatenate x (n,,y ∘ dni_allButLast _)) (y (lastelement _)).
Proof. intros.
       Local Opaque append dni_allButLast lastelement.
       simpl. (* just so we can see why reflexivity is about to work *)
       reflexivity.
Defined.

Definition flatten {X} : Sequence (Sequence X) -> Sequence X.
Proof.
  intros ? [n x].
  induction n as [|n IH].
  { apply nil. }
  { exact (concatenate (IH (x ∘ dni_allButLast _)) (x (lastelement _))). }
Defined.

Lemma flatten_length {X} (x : Sequence (Sequence X)) :
  length (flatten x) = stnsum (λ i, length ((pr2 x) i)).
Proof.
  intros.
  try reflexivity.
Abort.

Definition flattenStep {X n} (x: stn (S n) -> Sequence X) :
  flatten (S n,,x) = concatenate (flatten (n,,x ∘ dni_allButLast _)) (x (lastelement _)).
Proof. intros. reflexivity. Defined.

Local Definition assoc1 {X} (x y:Sequence X) (z:X) :
  append (concatenate x y) z = concatenate x (append y z).
Proof.
  intros.
  induction x as [m x].
  induction y as [n y].
  refine (total2_paths _ _).
  - change pr1 with (@length X).
    repeat rewrite append_length.
    repeat rewrite concatenate_length.
    simpl.
    apply pathsinv0.
    apply natplusnsm.
  -                             (* working here *)

Admitted.

Definition isassoc_concatenate {X} (x y z:Sequence X) :
  concatenate (concatenate x y) z = concatenate x (concatenate y z).
Proof.
  intros.
  induction z as [n z].
  induction n as [|n IH].
  - reflexivity.
  - repeat rewrite concatenateStep.
    generalize (z (lastelement _)) as w; intros.
    generalize (z ∘ dni_allButLast n) as v; intros.
    rewrite <- assoc1.
    apply (maponpaths (λ t, append t w)).
    apply IH.
Defined.


