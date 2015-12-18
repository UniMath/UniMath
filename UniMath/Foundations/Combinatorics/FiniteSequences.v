Require Export UniMath.Foundations.Combinatorics.StandardFiniteSets.
Unset Automatic Introduction.

(* move upstream *)
(* end of move upstream *)


Definition Sequence X := Σ n, stn n -> X.

Definition length {X} : Sequence X -> nat := pr1.

Definition Sequence_to_function {X} (x:Sequence X) := pr2 x : stn (length x) -> X.
Coercion Sequence_to_function : Sequence >-> Funclass.

Definition sequencePair {X n} (f:stn n -> X) : Sequence X := (n,,f).

Definition transport_stn m n i (b:i<m) (p:m=n) :
  transportf stn p (i,,b) = (i,,transportf (λ m,i<m) p b).
Proof. intros. induction p. reflexivity. Defined.

Definition sequenceEquality {X m n} (f:stn m->X) (g:stn n->X) (p:m=n) :
  (∀ i, f i = g (transportf stn p i))
  -> transportf (λ m, stn m->X) p f = g.
Proof. intros ? ? ? ? ? ? e. induction p. apply funextfun. exact e. Defined.

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
  intros. unfold dni,di; simpl. induction (natlthorgeh i n) as [q|q].
  - reflexivity.
  - contradicts (pr2 i) (natlehneggth q).
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

Definition iscontr_rect' X (i : iscontr X) (x0 : X) (P : X ->UU) (p0 : P x0) : ∀ x:X, P x.
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

Definition iscontr_rect'' X (i : iscontr X) (P : X ->UU) (p0 : P (pr1 i)) : ∀ x:X, P x.
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

Definition iscontr_rect X (is : iscontr X) (x0 : X) (P : X ->UU) (p0 : P x0) : ∀ x:X, P x.
Proof. intros. exact (transportf P (pr1 (isapropifcontr is x0 x)) p0). Defined.

Definition iscontr_rect_compute X (is : iscontr X) (x : X) (P : X ->UU) (p : P x) :
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
           (ind : ∀ (x : Sequence X) (y : X), P x -> P (append x y))
           (x : Sequence X) : P x.
Proof. intros. induction x as [n x]. induction n as [|n IH].
  - exact (transportf P (nil_unique x) p0).
  - exact (transportf P (drop_and_append x)
                      (ind (n,,x ∘ dni_lastelement)
                           (x (lastelement _))
                           (IH (x ∘ dni_lastelement)))).
Defined.

Lemma Sequence_rect_compute_nil {X} {P : Sequence X ->UU} (p0 : P nil)
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
      {X} {P : Sequence X ->UU} (p0 : P nil)
      (ind : ∀ (s : Sequence X) (x : X), P s -> P (append s x))
      (x:X) (l:Sequence X) :
  Sequence_rect p0 ind (append l x) = ind l x (Sequence_rect p0 ind l).
Proof.
  intros.

  (* proof in progress... *)

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

Definition concatenate_0 {X} (s:Sequence X) (t:stn 0 -> X) : concatenate s (0,,t) = s.
Proof.
  intros.
  induction s as [n s].
  unshelve refine (total2_paths2 _ _).
  { simpl. apply natplusr0. }
  { simpl. generalize (natplusr0 n). intro e. apply funextsec; intro i.

    (* this should be easier! *)
Abort.

Definition concatenateStep {X}  (x : Sequence X) {n} (y : stn (S n) -> X) :
  concatenate x (S n,,y) = append (concatenate x (n,,y ∘ dni_lastelement)) (y (lastelement _)).
Proof. intros.

Abort.

Definition partition {X n} (f:stn n -> nat) (x:stn (stnsum f) -> X) : Sequence (Sequence X).
Proof. intros. exists n. intro i. exists (f i). intro j. exact (x(inverse_lexicalEnumeration f (i,,j))).
Defined.

Definition flatten {X} : Sequence (Sequence X) -> Sequence X.
Proof. intros ? x. exists (stnsum (length ∘ x)). exact (λ j, uncurry (pr2 x) (lexicalEnumeration _ j)).
Defined.

Definition total2_step_f {n} (X:stn (S n) ->UU) :
  (Σ i, X i)
    ->
  (Σ (i:stn n), X (dni _ (lastelement _) i)) ⨿ X (lastelement _).
Proof.
  intros ? ? [[j J] x].
  induction (natlehchoice4 j n J) as [J'|K].
  - apply ii1.
    exists (j,,J').
    assert (e : (dni n (lastelement n) (j,, J')) = (j,, J) ).
    { apply isinjstntonat. rewrite replace_dni_last. reflexivity. }
    exact (transportb _ e x).
  - apply ii2.
    induction (!K); clear K.
    assert (e : (n,, J) = (lastelement n)).
    { apply isinjstntonat. reflexivity. }
    exact (transportf _ e x).
Defined.

Definition total2_step_b {n} (X:stnset (S n) ->UU) :
  (Σ (i:stn n), X (dni _ (lastelement _) i)) ⨿ X (lastelement _)
    ->
  (Σ i, X i).
Proof.
  intros ? ? x.
  induction x as [jx|x].
  - exact (dni _ (lastelement _) (pr1 jx),,pr2 jx).
  - exact (lastelement _,,x).
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
    unshelve refine (total2_paths _ _).
    * simpl. rewrite replace_dni_last. apply isinjstntonat. reflexivity.
    * rewrite replace_dni_last. unfold dni_lastelement.  simpl.
      change (λ x0 : stn (S n), X x0) with X.
      rewrite transport_f_b. apply (isaset_transportf X).
  + induction (!K). simpl.
    unshelve refine (total2_paths _ _).
    * simpl. now apply isinjstntonat.
    * simpl. assert (d : idpath n = K).
      { apply isasetnat. }
      induction d. simpl. rewrite transport_f_f. apply (isaset_transportf X).
Defined.

Definition total2_step {n} (X:stnset (S n) ->UU) :
  (Σ i, X i) ≃ (Σ (i:stn n), X (dni _ (lastelement _) i)) ⨿ X (lastelement _).
Proof.
  intros. set (f := weqdnicoprod n (lastelement _)).
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
  (Σ (i:stn n), stn (f (dni _ (lastelement _) i))) ⨿ stn (f (lastelement _)).
Proof. intros. apply (total2_step (stn ∘ f)). Defined.

Definition weqstnsum1' {n} (f:stn (S n)->nat ) : (Σ i, stn (f i)) ≃ stn (stnsum f).
Proof. intros.
  intermediate_weq ((Σ (i:stn n), stn (f (dni _ (lastelement _) i))) ⨿ stn (f (lastelement _))).
  { apply total2_step'. }
  intermediate_weq (stn (stnsum (f ∘ dni n (lastelement n))) ⨿ stn (f (lastelement n))).
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
                  (weqfp (weqdnicoprod n (lastelement n))
                         (λ i : stn (S n), stn (f i)))) (k,, p)))
            with ((invmap
                  (weqfp (weqdnicoprod n (lastelement n))
                     (λ i : stn (S n), stn (f i)))) (k,, p)).
  rewrite weqfp_compute_2.
  unfold weqdnicoprod at 11.
  unfold weqfp_invmap.
  change (pr2 (tpair (λ i, stn(f i)) k p)) with p.
  change (pr1 (tpair (λ i, stn(f i)) k p)) with k.

  (* perhaps also prove this is by equipping everything in sight with a well-ordering, preserved by all the equivalences involved *)
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
  unshelve refine (total2_paths _ _).
  - simpl. apply natplusassoc.
  - apply sequenceEquality; intros i.


Abort.

(*
Local Variables:
compile-command: "make -C ../.. UniMath/Foundations/Sequences.vo"
End:
*)
