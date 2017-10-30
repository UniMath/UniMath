
Unset Kernel Term Sharing.

(** * Construction of the circle *)

(** We will show that [B ℤ] has the universal property of the circle. *)

Require Import UniMath.Ktheory.AffineLine
               UniMath.Algebra.Monoids_and_Groups
               UniMath.Foundations.UnivalenceAxiom
               UniMath.Ktheory.GroupAction
               UniMath.NumberSystems.Integers
               UniMath.Ktheory.Nat
               UniMath.Ktheory.Integers
               UniMath.Ktheory.MoreEquivalences.
Require Import UniMath.Ktheory.Utilities.
Delimit Scope paths_scope with paths.
Open Scope paths_scope.
Open Scope action_scope.
Unset Automatic Introduction.
Local Notation "g + x" := (ac_mult _ g x) : action_scope.

Definition circle := B ℤ.

Theorem loops_circle : weq (Ω circle) ℤ.
Proof. apply loopsBG. Defined.

Definition circle_loop := ! invmap loops_circle 1 : Ω circle.

Lemma loop_compute t : castTorsor (!circle_loop) t = one + t.
Proof. intros. unfold circle_loop. rewrite pathsinv0inv0.
       exact (loopsBG_comp _ one t @ commax _ t one). Defined.

(** ** The total space of guided homotopies over BZ *)

Definition ZGuidedHomotopy {Y} {y:Y} (l:y = y) (T:Torsor ℤ) :=
  GuidedHomotopy (confun T y) (confun T l).

Definition GH {Y} {y:Y} (l:y = y) := ∑ T:Torsor ℤ, ZGuidedHomotopy l T.

Definition GHpair {Y} {y:Y} (l:y = y) (T:Torsor ℤ) (g:ZGuidedHomotopy l T) :=
  T,,g : GH l.

Definition pr1_GH {Y} {y:Y} {l:y = y} := pr1 : GH l -> Torsor ℤ.

Definition pr2_GH {Y} {y:Y} (l:y = y) (u:GH l)
  := pr2 u : ZGuidedHomotopy l (pr1_GH u).

Definition GH_path3 {Y} {y:Y} (l:y = y) {T:Torsor ℤ} {y':Y}
           {g g':GHomotopy (confun T y) (confun T l) y'} (u:g = g') :
  GHpair l T (y',, g) = GHpair l T (y',,g').
Proof. intros. destruct u. reflexivity. Defined.

Definition pr12_GH {Y} {y:Y} {l:y = y} (u:GH l) := pr1 (pr2_GH l u) : Y.

Definition pr22_GH {Y} {y:Y} {l:y = y} (u:GH l)
     := pr2 (pr2_GH l u)
     : GHomotopy (confun (pr1_GH u) y) (confun (pr1_GH u) l) (pr12_GH u).

Definition GH_path3_comp1 {Y} {y:Y} (l:y = y) {T:Torsor ℤ} {y':Y}
           {g g':GHomotopy (confun T y) (confun T l) y'} (u:g = g') :
  ap pr1_GH (GH_path3 l u) = idpath T.
Proof. intros. destruct u. reflexivity. Defined.

Definition GH_path3_comp2 {Y} {y:Y} (l:y = y) {T:Torsor ℤ} {y':Y}
           {g g':GHomotopy (confun T y) (confun T l) y'} (u:g = g') :
  ap pr12_GH (GH_path3 l u) = idpath y'.
Proof. intros. destruct u. reflexivity. Defined.

Local Definition irr {Y} {y:Y} (l:y = y) (T:Torsor ℤ) := proofirrGuidedHomotopy T (confun T y) (confun T l).

Local Definition sec {Y} {y:Y} (l:y = y) (T:Torsor ℤ) := makeGuidedHomotopy2 T (confun T y) (confun T l).

Definition pr1_GH_weq {Y} {y:Y} {l:y = y} : (GH l) ≃ (Torsor ℤ) := weqpr1_irr_sec (irr l) (sec l).

Definition homotinvweqweq_GH_comp {Y} {y:Y} {l:y = y}
           (T:Torsor ℤ) (gh:ZGuidedHomotopy l T) :
  @paths (@paths (GH l)
             (invweq (@pr1_GH_weq _ _ l) T) (T,,gh))
            (homotinvweqweq' (irr l) (sec l) (T,,gh))
            (@pair_path_in2 _ (ZGuidedHomotopy l)
                            _ (sec l T) gh
                            (irr l T (sec l T) gh)).
Proof. reflexivity.             (* don't change the proof *)
Defined.

Definition makeGH {Y} {y:Y} (l:y = y) (T:Torsor ℤ) (t:T) {y':Y} (h:y' = y) : GH l
  := GHpair l T (makeGuidedHomotopy _ _ t h).

Definition makeGH1 {Y} {y:Y} (l:y = y) (T:Torsor ℤ) (t:T) : GH l
  := makeGH l T t (idpath y).

Definition pr12_pair_path_in2 {Y} {y:Y} (l:y = y) (T:Torsor ℤ)
           {gh gh':ZGuidedHomotopy l T} (w : gh = gh') :
  ap pr12_GH (pair_path_in2 (ZGuidedHomotopy l) w) = ap pr1 w.
Proof. intros. destruct w. reflexivity. Defined.

Definition pr1_GH_weq_compute {Y} {y:Y} (l:y = y) :
  let T0 := trivialTorsor ℤ in
  let t0 := 0 : T0 in
    @paths (y = y)
              (ap pr12_GH (homotinvweqweq' (irr l) (sec l) (makeGH1 l T0 t0)))
              (idpath y).
Proof. intros.
       unfold makeGH1,makeGH,GHpair.
       refine (ap (ap pr12_GH)
                  (homotinvweqweq_GH_comp
                     T0
                     (makeGuidedHomotopy (λ _ : T0, y)
                                         (confun T0 l) t0 (idpath y)))
                  @ _).
       refine (pr12_pair_path_in2
                 l T0
                 (irr l T0 (sec l T0)
                      (makeGuidedHomotopy (λ _ : T0, y) (confun T0 l) t0 (idpath y)))
                 @ _).
       unfold sec.
       change (makeGuidedHomotopy (λ _ : T0, y) (confun T0 l) t0 (idpath y))
       with (sec l T0).
       change (makeGuidedHomotopy2 T0 (confun T0 y) (confun T0 l))
       with (sec l T0).
       change (idpath y) with (ap pr1 (idpath (sec l T0))).
       apply (ap (ap pr1)). apply irrel_paths. apply (irr l). Defined.

(** ** Various paths in GH *)

Definition makeGH_localPath {Y} {y:Y} (l:y=y) (T:Torsor ℤ) {t t':T} (r:t = t')
           {y'} {h h':y' = y} (q:h = h')
  : makeGH l T t h = makeGH l T t' h'.
Proof. intros. destruct q, r. reflexivity.
(* compare with [makeGuidedHomotopy_localPath] *)
Defined.

Definition makeGH_localPath_comp1 {Y} {y:Y} (l:y = y) (T:Torsor ℤ) {t t':T} (r:t = t')
           {y'} {h h':y' = y} (q:h = h') :
  ap pr1_GH (makeGH_localPath l T r q) = idpath T.
Proof. intros. destruct q,r. reflexivity. Defined.

Definition makeGH_localPath_comp2 {Y} {y:Y} (l:y = y) (T:Torsor ℤ) {t t':T} (r:t = t')
           {y'} {h h':y' = y} (q:h = h') :
  ap pr12_GH (makeGH_localPath l T r q) = idpath y'.
Proof. intros. destruct q,r. reflexivity. Defined.

Definition makeGH_verticalPath {Y} {y:Y} (l:y = y) {T:Torsor ℤ} (t:T)
           {y' y''} (h:y' = y) (p:y'' = y')
  : makeGH l T t (p@h) = makeGH l T t h.
Proof. intros. destruct p. reflexivity. Defined.
(* could also use [makeGuidedHomotopy_verticalPath] *)

Definition makeGH_verticalPath_comp1 {Y} {y:Y} (l:y = y) {T:Torsor ℤ} (t:T)
           {y' y''} (h:y' = y) (p:y'' = y')
  : ap pr1_GH (makeGH_verticalPath l t h p) = idpath T.
Proof. intros. destruct p. reflexivity. Defined.

Definition makeGH_verticalPath_comp2 {Y} {y:Y} (l:y = y) {T:Torsor ℤ} (t:T)
           {y' y''} (h:y' = y) (p:y'' = y')
  : ap pr12_GH (makeGH_verticalPath l t h p) = p.
Proof. intros. destruct p. reflexivity. Defined.

Definition makeGH_horizontalPath {Y} {y:Y} (l:y = y) {T T':Torsor ℤ} (q:T = T')
           (t:T) {y'} (h:y' = y)
  : makeGH l T t h = makeGH l T' (castTorsor q t) h.
Proof. intros. destruct q. reflexivity.
(* compare with [makeGuidedHomotopy_horizontalPath] *)
Defined.

Definition makeGH_horizontalPath_comp1 {Y} {y:Y} (l:y = y) {T T':Torsor ℤ} (q:T = T')
           (t:T) {y'} (h:y' = y)
  : ap pr1_GH (makeGH_horizontalPath l q t h) = q.
Proof. intros. destruct q. reflexivity. Defined.

Definition makeGH_horizontalPath_comp2 {Y} {y:Y} (l:y = y) {T T':Torsor ℤ} (q:T = T')
           (t:T) {y'} (h:y' = y)
  : ap pr12_GH (makeGH_horizontalPath l q t h) = idpath y'.
Proof. intros. destruct q. reflexivity. Defined.

Definition makeGH_transPath {Y} {y:Y} (l:y = y) {T:Torsor ℤ} (t:T) {y'} (h:y' = y)
  : makeGH l T t h = makeGH l T (one+t) (h@l).
Proof. intros. apply GH_path3.
       (* copied from the proof of [makeGuidedHomotopy_transPath] *)
       exact (ℤTorsorRecursion_transition_inv
                _ (λ t, weq_pathscomp0r y' l) _ _). Defined.

Definition makeGH_transPath_comp1 {Y} {y:Y} (l:y = y) {T:Torsor ℤ} (t:T) {y'} (h:y' = y)
  : ap pr1_GH (makeGH_transPath l t h) = idpath T.
Proof. intros. exact (GH_path3_comp1 l _). Defined.

Definition makeGH_transPath_comp2 {Y} {y:Y} (l:y = y) {T:Torsor ℤ} (t:T) {y'} (h:y' = y)
  : ap pr12_GH (makeGH_transPath l t h) = idpath y'.
Proof. intros. exact (GH_path3_comp2 l _). Defined.

Definition makeGH_diagonalLoop {Y} {y:Y} (l:y = y) {T:Torsor ℤ} (t:T)
           (q:T = T) (r:castTorsor q t = one + t) :
  makeGH1 l T t = makeGH1 l T t.
Proof. intros.
       assert (p2 := makeGH_transPath l t (idpath y)).
       assert (p0:= makeGH_localPath l T (!r) (idpath l)); clear r.
       assert (ph := makeGH_horizontalPath l q t l).
       assert (p1 := makeGH_localPath l T (idpath t) (! pathscomp0rid l)).
       assert (pv := makeGH_verticalPath l t (idpath y) l).
       assert (p := p2 @ p0 @ !ph @ p1 @ pv); clear p2 p0 ph p1 pv.
       exact p. Defined.

Definition makeGH_diagonalLoop_comp1 {Y} {y:Y} (l:y = y) {T:Torsor ℤ} (t:T)
           (q:T = T) (r:castTorsor q t = one + t) :
  ap pr1_GH (makeGH_diagonalLoop l t q r) = !q.
Proof. intros. unfold makeGH_diagonalLoop.
       refine (maponpaths_naturality (makeGH_transPath_comp1 _ _ _) _).
       refine (maponpaths_naturality (makeGH_localPath_comp1 _ _ _ _) _).
       rewrite <- (pathscomp0rid (paths_rect _ _ (λ b _, b = T) _ _ q)). (* Used to be "rewrite <- (pathscomp0rid (! q))", which was more perspicuous. *)
       refine (maponpaths_naturality' (makeGH_horizontalPath_comp1 _ _ _ _) _).
       rewrite <- (pathscomp0rid (idpath T)).
       refine (maponpaths_naturality (makeGH_localPath_comp1 _ _ _ _) _).
       exact (makeGH_verticalPath_comp1 _ _ _ _).
Defined.

Definition makeGH_diagonalLoop_comp2 {Y} {y:Y} (l:y = y) {T:Torsor ℤ} (t:T)
           (q:T = T) (r:castTorsor q t = one + t) :
  ap pr12_GH (makeGH_diagonalLoop l t q r) = l.
Proof. intros. unfold makeGH_diagonalLoop.
       refine (maponpaths_naturality (makeGH_transPath_comp2 _ _ _) _).
       refine (maponpaths_naturality (makeGH_localPath_comp2 _ _ _ _) _).
       refine (maponpaths_naturality' (makeGH_horizontalPath_comp2 _ _ _ _) _).
       refine (maponpaths_naturality (makeGH_localPath_comp2 _ _ _ _) _).
       exact (makeGH_verticalPath_comp2 _ _ _ _).
Defined.

(** ** The universal property of the circle *)

(** *** The recursion principle (non-dependent functions) *)

Definition circle_map {Y} {y:Y} (l:y = y) : circle -> Y.
Proof. intros ? ? ?. exact (funcomp (invmap (@pr1_GH_weq _ _ l)) pr12_GH). Defined.

Definition circle_map_check_values {Y} {y:Y} (l:y = y) :
  circle_map l (basepoint circle) = y.
Proof. reflexivity.              (* don't change the proof *)
(** This proof works because the trivial torsor has an
    actual point that provides the accompanying proof of nonemptiness. *)
Defined.

Definition circle_map_check_paths {Y} {y:Y} (l:y = y) :
  ap (circle_map l) circle_loop = l.
Proof. intros. assert (p := pr1_GH_weq_compute l).
       refine (_ @ loop_correspondence' (irr l) (sec l) pr12_GH
                      (makeGH_diagonalLoop_comp1 l _ _ (loop_compute 0))
                      (makeGH_diagonalLoop_comp2 l _ _ (loop_compute 0)) @ _).
       { intermediate_path (ap (circle_map l) circle_loop @ idpath y).
         { apply pathsinv0. apply pathscomp0rid. }
         { apply pathsinv0. rewrite pathsinv0inv0.
           exact (ap (λ r, ap (circle_map l) circle_loop @ r) p). } }
       { exact (ap (λ r, r @ l) p). } Defined.

(** *** The induction principle (dependent functions) *)


Definition circle_map' {Y:circle->Type} {y:Y(basepoint circle)}
           (l:circle_loop#y = y) : ∏ c:circle, Y c.
Proof. (** (not proved yet) *)
Abort.

(* One approach to the theorem above would be through the results of the paper
 "Higher Inductive Types as Homotopy-Initial Algebras", by Kristina Sojakova,
 http://arxiv.org/abs/1402.0761 *)

Lemma circle_map_check_paths'
      (circle_map': ∏ (Y:circle->UU) (y:Y(basepoint circle))
           (l:circle_loop#y = y) (c:circle), Y c)
      {Y} (f:circle->Y) :
  circle_map (ap f circle_loop) = f .
Proof. intros. apply funextsec.
       simple refine (circle_map' _ _ _).
       { reflexivity. }
       { set (y := f (basepoint circle)). set (l := ap f circle_loop).
         set (P := λ T : underlyingType circle, circle_map _ T = f T).
         apply transport_fun_path. rewrite pathscomp0rid.
         change (idpath y @ ap f circle_loop) with (ap f circle_loop).
         exact (! circle_map_check_paths l). } Defined.

(*
Local Variables:
compile-command: "make -C ../.. UniMath/Ktheory/Circle.vo"
End:
*)
