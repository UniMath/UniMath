(** * Construction of the circle *)

(** We will show that [B ℤ] has the universal property of the circle. *)

Unset Automatic Introduction.
Require Import AffineLine algebra1b funextfun Utilities auxiliary_lemmas_HoTT GroupAction hz.
Require pathnotations.
Import pathnotations.PathNotations Utilities.Notation.
Delimit Scope paths_scope with paths.
Open Scope paths_scope.
Local Notation "g + x" := (ac_mult _ g x) : action_scope.
Notation ℕ := nat.
Notation ℤ := hzaddabgr.

Theorem loops_circle : weq (Ω (B ℤ)) ℤ.
Proof. apply loopsBG. Defined.

Definition circle_loop := invmap loops_circle 1 : Ω (B ℤ).

Lemma loop_compute t : castTorsor circle_loop t == one + t.
Proof. intros.

       admit.

Defined.

(** * Powers of paths *) 

Definition loop_power_nat {Y} {y:Y} (l:y==y) (n:ℕ) : y==y.
Proof. intros. induction n as [|n p]. 
       { exact (idpath _). } { exact (p@l). } Defined.

Local Notation "l ^ n" := (loop_power_nat l n) : paths_nat_scope.

Definition loop_power {Y} {y:Y} (l:y==y) (n:ℤ) : y==y.
Proof. intros. assert (m := loop_power_nat l (hzabsval n)).
       destruct (hzlthorgeh n 0%hz). { exact (!m). } { exact m. } Defined.

Local Notation "l ^ n" := (loop_power l n) : paths_scope.

(** ** The total space of guided homotopies over BZ *)

Definition ZGuidedHomotopy {Y} {y:Y} (l:y==y) (T:Torsor ℤ) := 
  GuidedHomotopy (confun T y) (confun T l).

Definition GH {Y} {y:Y} (l:y==y) := total2 (ZGuidedHomotopy l).

Definition GHpair {Y} {y:Y} (l:y==y) (T:Torsor ℤ) (g:ZGuidedHomotopy l T) :=
  tpair (ZGuidedHomotopy l) T g.

Definition pr1_GH {Y} {y:Y} {l:y==y} := pr1 : GH l -> Torsor ℤ.

Definition pr2_GH {Y} {y:Y} (l:y==y) (u:GH l) 
  := pr2 u : ZGuidedHomotopy l (pr1_GH u).

Definition GH_path3 {Y} {y:Y} (l:y==y) {T:Torsor ℤ} {y':Y}
           {g g':GHomotopy (confun T y) (confun T l) y'} (u:g==g') :
  GHpair l T (tpair _ y' g ) == GHpair l T (tpair _ y' g' ).
Proof. intros. destruct u. reflexivity. Defined.

Definition pr12_GH {Y} {y:Y} {l:y==y} (u:GH l) := pr1 (pr2_GH l u) : Y.

Definition GH_path3_comp1 {Y} {y:Y} (l:y==y) {T:Torsor ℤ} {y':Y}
           {g g':GHomotopy (confun T y) (confun T l) y'} (u:g==g') :
  ap pr1_GH (GH_path3 l u) == idpath T.
Proof. intros. destruct u. reflexivity. Defined.

Definition GH_path3_comp2 {Y} {y:Y} (l:y==y) {T:Torsor ℤ} {y':Y}
           {g g':GHomotopy (confun T y) (confun T l) y'} (u:g==g') :
  ap pr12_GH (GH_path3 l u) == idpath y'.
Proof. intros. destruct u. reflexivity. Defined.

Lemma pr1_GH_isweq {Y} {y:Y} (l:y==y) : isweq (@pr1_GH Y y l).
Proof. intros. apply isweqpr1. intros T. apply iscontrGuidedHomotopy.
Defined.

Definition makeGH {Y} {y:Y} (l:y==y) (T:Torsor ℤ) (t:T) {y':Y} (h:y'==y) 
           : GH l
  := GHpair l T (makeGuidedHomotopy _ _ t h).

(** ** Various paths in GH *)

Definition makeGH_localPath {Y} {y:Y} (l:y==y) (T:Torsor ℤ) {t t':T} (r:t==t')
           {y'} {h h':y'==y} (q:h==h') 
  : makeGH l T t h == makeGH l T t' h'.
Proof. intros. destruct q, r. reflexivity. 
(* compare with [makeGuidedHomotopy_localPath] *)
Defined.

Definition makeGH_localPath_comp1 {Y} {y:Y} (l:y==y) (T:Torsor ℤ) {t t':T} (r:t==t')
           {y'} {h h':y'==y} (q:h==h') : 
  ap pr1_GH (makeGH_localPath l T r q) == idpath T.
Proof. intros. destruct q,r. reflexivity. Defined.

Definition makeGH_localPath_comp2 {Y} {y:Y} (l:y==y) (T:Torsor ℤ) {t t':T} (r:t==t')
           {y'} {h h':y'==y} (q:h==h') : 
  ap pr12_GH (makeGH_localPath l T r q) == idpath y'.
Proof. intros. destruct q,r. reflexivity. Defined.

Definition makeGH_verticalPath {Y} {y:Y} (l:y==y) {T:Torsor ℤ} (t:T)
           {y' y''} (h:y'==y) (p:y''==y')
  : makeGH l T t (p@h) == makeGH l T t h.
Proof. intros. destruct p. reflexivity. Defined.
(* could also use [makeGuidedHomotopy_verticalPath] *)

Definition makeGH_verticalPath_comp1 {Y} {y:Y} (l:y==y) {T:Torsor ℤ} (t:T)
           {y' y''} (h:y'==y) (p:y''==y')
  : ap pr1_GH (makeGH_verticalPath l t h p) == idpath T.
Proof. intros. destruct p. reflexivity. Defined.

Definition makeGH_verticalPath_comp2 {Y} {y:Y} (l:y==y) {T:Torsor ℤ} (t:T)
           {y' y''} (h:y'==y) (p:y''==y')
  : ap pr12_GH (makeGH_verticalPath l t h p) == p.
Proof. intros. destruct p. reflexivity. Defined.

Definition makeGH_horizontalPath {Y} {y:Y} (l:y==y) {T T':Torsor ℤ} (q:T==T')
           (t:T) {y'} (h:y'==y)
  : makeGH l T t h == makeGH l T' (castTorsor q t) h.
Proof. intros. destruct q. reflexivity. 
(* compare with [makeGuidedHomotopy_horizontalPath] *)
Defined.

Definition makeGH_horizontalPath_comp1 {Y} {y:Y} (l:y==y) {T T':Torsor ℤ} (q:T==T')
           (t:T) {y'} (h:y'==y)
  : ap pr1_GH (makeGH_horizontalPath l q t h) == q.
Proof. intros. destruct q. reflexivity. Defined.

Definition makeGH_horizontalPath_comp2 {Y} {y:Y} (l:y==y) {T T':Torsor ℤ} (q:T==T')
           (t:T) {y'} (h:y'==y)
  : ap pr12_GH (makeGH_horizontalPath l q t h) == idpath y'.
Proof. intros. destruct q. reflexivity. Defined.

Definition makeGH_transPath {Y} {y:Y} (l:y==y) {T:Torsor ℤ} (t:T) {y'} (h:y'==y)
  : makeGH l T t h == makeGH l T (one+t) (h@l).
Proof. intros. apply GH_path3.
       (* copied from the proof of [makeGuidedHomotopy_transPath] *)
       exact (ℤTorsorRecursion_transition_inv 
                _ (fun t => weq_pathscomp0r y' l) _ _). Defined.

Definition makeGH_transPath_comp1 {Y} {y:Y} (l:y==y) {T:Torsor ℤ} (t:T) {y'} (h:y'==y)
  : ap pr1_GH (makeGH_transPath l t h) == idpath T.
Proof. intros. exact (GH_path3_comp1 l _). Defined.

Definition makeGH_transPath_comp2 {Y} {y:Y} (l:y==y) {T:Torsor ℤ} (t:T) {y'} (h:y'==y)
  : ap pr12_GH (makeGH_transPath l t h) == idpath y'.
Proof. intros. exact (GH_path3_comp2 l _). Defined.

Definition makeGH1 {Y} {y:Y} (l:y==y) (T:Torsor ℤ) (t:T) : GH l
  := makeGH l T t (idpath y).

Definition makeGH_diagonalLoop {Y} {y:Y} (l:y==y) {T:Torsor ℤ} (t:T) 
           (q:T==T) (r:castTorsor q t == one + t) : 
  makeGH1 l T t == makeGH1 l T t.
Proof. intros.
       assert (p2 := makeGH_transPath l t (idpath y)).
       assert (p0:= makeGH_localPath l T (!r) (idpath l)); clear r.
       assert (ph := makeGH_horizontalPath l q t l).
       assert (p1 := makeGH_localPath l T (idpath t) (! pathscomp0rid l)).
       assert (pv := makeGH_verticalPath l t (idpath y) l).
       assert (p := p2 @ p0 @ !ph @ p1 @ pv); clear p2 p0 ph p1 pv.
       exact p. Defined.

Definition makeGH_diagonalLoop_comp1 {Y} {y:Y} (l:y==y) {T:Torsor ℤ} (t:T) 
           (q:T==T) (r:castTorsor q t == one + t) : 
  ap pr1_GH (makeGH_diagonalLoop l t q r) == !q.
Proof. intros. unfold makeGH_diagonalLoop.
       refine (ap_natl (makeGH_transPath_comp1 _ _ _) _).
       refine (ap_natl (makeGH_localPath_comp1 _ _ _ _) _).
       rewrite <- (pathscomp0rid (! q)).
       refine (ap_natl' (makeGH_horizontalPath_comp1 _ _ _ _) _).
       rewrite <- (pathscomp0rid (idpath T)).
       refine (ap_natl (makeGH_localPath_comp1 _ _ _ _) _).
       exact (makeGH_verticalPath_comp1 _ _ _ _).
Defined.

Definition makeGH_diagonalLoop_comp2 {Y} {y:Y} (l:y==y) {T:Torsor ℤ} (t:T) 
           (q:T==T) (r:castTorsor q t == one + t) : 
  ap pr12_GH (makeGH_diagonalLoop l t q r) == l.
Proof. intros. unfold makeGH_diagonalLoop.
       refine (ap_natl (makeGH_transPath_comp2 _ _ _) _).
       refine (ap_natl (makeGH_localPath_comp2 _ _ _ _) _).
       refine (ap_natl' (makeGH_horizontalPath_comp2 _ _ _ _) _).
       refine (ap_natl (makeGH_localPath_comp2 _ _ _ _) _).
       exact (makeGH_verticalPath_comp2 _ _ _ _).
Defined.

(** ** The universal property of the B ℤ *)

Definition circle_map {Y} {y:Y} (l:y==y) : B ℤ -> Y.
Proof. intros ? ? ? T. simpl in T.
       exact (affine_line_value (fun t:T => y) (fun t:T => l)). Defined.

Definition circle_map_check_values {Y} {y:Y} (l:y==y) : 
  circle_map l (basepoint (B ℤ)) == y.
Proof. reflexivity.              (* don't change the proof *)
Defined.

Definition check_paths2 {Y} {y:Y} (l:y==y) :
  ap (affine_line_map (T:=trivialTorsor ℤ) (fun _ => y) (fun _ => l))
     (affine_line_path
        (affine_line_point (trivialTorsor ℤ))
        (add_one (affine_line_point (trivialTorsor ℤ)))) == l.
Proof. intros. apply check_paths_any. Defined.

Definition circle_map_check_paths {Y} {y:Y} (l:y==y) : 
  ap (circle_map l) circle_loop == l.
Proof. intros.
       set (T := basepoint (B ℤ)); simpl in T.
       set (t0 := 0).
       set (n0 := pr1 (pr2 T)).
       change (pr1 T) with (underlyingAction T) in n0.
       change (pr1 (pr2 T)) with (squash_element 0) in n0.
       set (f := fun t:T => y). 
       set (s := fun t:T => l).
       assert (a := AffineLine.check_paths_any f s t0).
       change (s t0) with l in a.
       assert (r := ! ap_pr1_pr2 circle_loop).
       change (pr1 (pr2 (basepoint (B ℤ)))) with n0 in r.
       set (r1 := path_end r).
       change (pr1 (basepoint (B ℤ))) with (underlyingAction T) in r1.
       unfold path_end in r1.
       (* to do: identify r1, or redefine circle_loop so it makes that possible *)
       

       set (r2 := affine_line_map f s r1).
       unfold affine_line_map,r1,map in r2. 


       (* Check check_paths_any f s t0. *)

       admit.
Defined.

(*
Local Variables:
compile-command: "make -C ../.. UniMath/Ktheory/Circle.vo"
End:
*)
