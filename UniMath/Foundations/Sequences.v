Require Export UniMath.Foundations.StandardFiniteSets.
Unset Automatic Introduction.

(* move upstream *)

(* *)


Definition Sequence X := Σ n, stn n -> X.

Definition length {X} : Sequence X -> nat := pr1.

Local Definition empty_fun {X} : stn 0 -> X.
Proof. intros ? i. contradicts i negstn0. Defined.

Definition nil {X} : Sequence X.
Proof. intros. exact (0,, empty_fun). Defined.

Definition append {X} : Sequence X -> X -> Sequence X.
Proof.
  intros ? [m x] y.
  exists (S m).
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

Definition nil_unique {X} (x : stn 0 -> X) : (0,,x) = nil.
Proof.
  intros. apply pair_path_in2. apply isapropifcontr. apply stn0_fun_iscontr.
Defined.

(* induction principle for contractible types, as a warmup *)

Definition isaset_transport (X : UU) (x : X) (P : X -> UU) (p : P x) (i : isaset X) (e : x = x) :
  transportf P e p = p.
Proof. intros. induction (pr1 (i x x (idpath _) e)). reflexivity. Defined.

(* Two ways.  Use induction: *)

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

(* .... or use transport explicitly: *)

Definition iscontr_rect X (is : iscontr X) (x0 : X) (P : X -> UU) (p0 : P x0) : ∀ x:X, P x.
Proof. intros. exact (transportf P (pr1 (isapropifcontr is x0 x)) p0). Defined.

Definition iscontr_rect_compute X (is : iscontr X) (x : X) (P : X -> UU) (p : P x) :
  iscontr_rect X is x P p x = p.
Proof. intros. apply isaset_transport. apply isasetifcontr. exact is. Defined.

Corollary weqsecovercontr':     (* reprove weqsecovercontr, move upstream *)
  ∀ (X:UU) (P:X->UU) (is:iscontr X), (∀ x:X, P x) ≃ P (pr1 is).
Proof.
  intros.
  set (x0 := pr1 is).
  set (secs := ∀ x : X, P x).
  set (fib  := P x0).
  set (destr := (λ f, f x0) : secs->fib).
  set (constr:= iscontr_rect X is x0 P).
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
  - exact (n,,x ∘ (dni_allButLast _)).
Defined.

Definition drop' {X} (x:Sequence X) : x != nil -> Sequence X.
Proof. intros ? ? h. exact (drop x (pr2 (logeqnegs (nil_length x)) h)). Defined.

Definition drop_and_append {X n} (x : stn (S n) -> X) :
  append (n,,x ∘ (dni_allButLast _)) (x (lastelement n)) = (S n,, x).
Proof.
  intros.
  apply (maponpaths (tpair _ (S n))).
  apply funextfun; intros [i b].
  induction (natlehchoice4 i n b) as [p|p].
  - simpl; unfold funcomp.
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
  append (drop (S n,,x) (negpathssx0 _)) (x (lastelement n)) = (S n,, x).
Proof. intros. apply drop_and_append. Defined.

Definition Sequence_rect {X} {P : Sequence X -> UU}
           (p0 : P nil)
           (ind : ∀ (x : Sequence X) (y : X), P x -> P (append x y))
           (x : Sequence X) : P x.
Proof.
  intros.
  induction x as [n x].
  induction n as [|n IH].
  - induction (nil_unique x). exact p0.
  - set (p := ind (n,,x ∘ (dni_allButLast _)) (x (lastelement _)) (IH (x ∘ dni_allButLast _))).
    induction (drop_and_append x).
    exact p.
Defined.

Lemma Sequence_rect_nil {X} {P : Sequence X -> UU} (p0 : P nil)
      (ind : ∀ (s : Sequence X) (x : X), P s -> P (append s x)) :
  Sequence_rect p0 ind nil = p0.
Proof.
  intros.
  try reflexivity.
  Opaque Sequence.
  simpl.


Abort.

Lemma Sequence_rect_cons
      {X} {P : Sequence X -> UU} (p0 : P nil)
      (ind : ∀ (s : Sequence X) (x : X), P s -> P (append s x))
      (x:X) (l:Sequence X) :
  Sequence_rect p0 ind (append l x) = ind l x (Sequence_rect p0 ind l). 
Proof.
  intros.

Abort.

Lemma append_length {X} (x:Sequence X) (y:X) :
  length (append x y) = S (length x).
Proof.
  intros.
  try reflexivity.
Admitted.

Definition concatenate {X} : binop (Sequence X).
Proof.
  intros ? x [n y].
  induction n as [|n IH].
  { exact x. }
  { exact (append (IH (y ∘ (dni_allButLast _))) (y (lastelement _))). }
Defined.

Definition concatenate_length {X} (x y:Sequence X) :
  length (concatenate x y) = length x + length y.
Proof.


Admitted.

Definition concatenateStep {X}  (x : Sequence X) {n} (y : stn (S n) -> X) :
  concatenate x (S n,,y) = append (concatenate x (n,,y ∘ (dni_allButLast _))) (y (lastelement _)).
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
  { exact (concatenate (IH (x ∘ (dni_allButLast _))) (x (lastelement _))). }
Defined.

Lemma flatten_length {X} (x : Sequence (Sequence X)) :
  length (flatten x) = stnsum (λ i, length ((pr2 x) i)).
Proof.

Abort.

Definition flattenStep {X n} (x: stn (S n) -> Sequence X) :
  flatten (S n,,x) = concatenate (flatten (n,,x ∘ (dni_allButLast _))) (x (lastelement n)).
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
  - 

Admitted.

Definition isassoc_concatenate {X} (x y z:Sequence X) :
  concatenate (concatenate x y) z = concatenate x (concatenate y z).
Proof.
  intros.
  induction z as [n z].
  induction n as [|n IH].
  - reflexivity.
  - repeat rewrite concatenateStep.
    generalize (z (lastelement n)) as w; intros.
    generalize (z ∘ dni_allButLast n) as v; intros.
    rewrite <- assoc1.
    apply (maponpaths (λ t, append t w)).
    apply IH.
Defined.


