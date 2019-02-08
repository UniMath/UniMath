(** * Equivalences *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.Notations.
Require Import UniMath.MoreFoundations.Tactics.

Definition post_cat {X} {x y z:X} {p:y = z} : x = y -> x = z.
Proof. intros q. exact (pathscomp0 q p). Defined.

Definition pre_cat {X} {x y z:X} {p:x = y} : y = z -> x = z.
Proof. intros q. exact (pathscomp0 p q). Defined.

Ltac maponpaths_pre_post_cat :=
  repeat rewrite path_assoc; repeat apply (maponpaths post_cat); repeat rewrite <- path_assoc;
  repeat apply (maponpaths pre_cat); repeat rewrite path_assoc; repeat rewrite maponpathsinv0;
  try reflexivity.

Definition isEquivalence {X Y:Type} (f:X->Y) :=
  ∑ (g:Y->X) (p:∏ y, f(g y) = y) (q:∏ x, g(f x) = x), ∏ x, maponpaths f (q x) = p(f x).

Definition isEquivalence_toInverseFunction {X Y} {f:X->Y} : isEquivalence f -> Y->X := pr1.

Definition isEquivalence_toTargetHomotopy {X Y} {f:X->Y} (i:isEquivalence f) : ∏ y, f (isEquivalence_toInverseFunction i y) = y := pr12 i.

Definition isEquivalence_toSourceHomotopy {X Y} {f:X->Y} (i:isEquivalence f) : ∏ x, isEquivalence_toInverseFunction i (f x) = x := pr122 i.

Definition isEquivalence_toAdjointness {X Y} {f:X->Y} (i:isEquivalence f)
  : ∏ x, maponpaths f (isEquivalence_toSourceHomotopy i x) = isEquivalence_toTargetHomotopy i (f x) := pr222 i.

Definition Equivalence X Y := ∑ (f:X->Y), isEquivalence f.

Notation "X ≅ Y" := (Equivalence X Y) (at level 60, no associativity) : type_scope.

Definition makeEquivalence X Y f g p q h := (f,,g,,p,,q,,h) : X ≅ Y.

Definition Equivalence_toFunction {X Y} : X≅Y -> X->Y := pr1.

Coercion Equivalence_toFunction : Equivalence >-> Funclass.

Definition Equivalence_to_isEquivalence {X Y} (w:X≅Y) : isEquivalence w := pr2 w.

Definition Equivalence_toInverseFunction {X Y} : X≅Y -> Y->X.
Proof. intros f. exact (pr1 (pr2 f)). Defined.

Definition Equivalence_toTargetHomotopy {X Y} (f:Equivalence X Y) : ∏ y, f (Equivalence_toInverseFunction f y) = y
  := pr1 (pr2 (pr2 f)).

Definition Equivalence_toSourceHomotopy {X Y} (f:Equivalence X Y) : ∏ x, Equivalence_toInverseFunction f (f x) = x
  := pr1 (pr2 (pr2 (pr2 f))).

Definition Equivalence_toAdjointness {X Y} (f:Equivalence X Y)
  : ∏ x, maponpaths f (Equivalence_toSourceHomotopy f x) = Equivalence_toTargetHomotopy f (f x)
  := pr2 (pr2 (pr2 (pr2 f))).

Lemma transportf_fun_idpath {X Y} {f:X->Y} x x' (w:x = x') (t:f x = f x) :
              transportf (λ x', f x' = f x) w (idpath (f x)) = maponpaths f (!w).
Proof. induction w. reflexivity. Qed.

Definition isEquivalence_to_isweq {X Y} {f:X->Y} : isEquivalence f -> isweq f.
Proof.
  intros i.
  set (g := isEquivalence_toInverseFunction i).
  set (p := isEquivalence_toTargetHomotopy i).
  set (q := isEquivalence_toSourceHomotopy i).
  set (h := isEquivalence_toAdjointness i).
  intro y.
  exists (g y,,p y).
  intros xe.
  simple refine (hfibertriangle2 _ _ _ _ _).
  - exact (! (q (pr1 xe)) @ maponpaths g (pr2 xe)).
  - induction xe as [x e]; simpl. induction e; simpl.
    rewrite pathscomp0rid.
    rewrite maponpathsinv0.
    rewrite h.
    now rewrite pathsinv0l.
Defined.

Definition Equivalence_to_weq {X Y} : X ≅ Y -> X ≃ Y.
Proof. intros w.
       exact (weqpair (Equivalence_toFunction w) (isEquivalence_to_isweq (Equivalence_to_isEquivalence w))).
Defined.

Definition weq_to_Equivalence {X Y} : X ≃ Y -> X ≅ Y.
  intros f.
  exact (makeEquivalence X Y f (invmap f)
                         (homotweqinvweq f) (homotinvweqweq f)
                         (homotweqinvweqweq f)).
Defined.

Lemma check1 X Y (w:X≅Y) :
  Equivalence_toFunction (weq_to_Equivalence (Equivalence_to_weq w)) = Equivalence_toFunction w.
Proof. reflexivity. Defined.

Lemma check2 X Y (w:X≅Y) :
  Equivalence_toInverseFunction (weq_to_Equivalence (Equivalence_to_weq w)) = Equivalence_toInverseFunction w.
Proof. reflexivity. Defined.

Lemma check3 X Y (w:X≅Y) :
  Equivalence_toTargetHomotopy (weq_to_Equivalence (Equivalence_to_weq w)) = Equivalence_toTargetHomotopy w.
Proof. reflexivity. Defined.

Lemma check4 X Y (w:X≅Y) :
  Equivalence_toSourceHomotopy (weq_to_Equivalence (Equivalence_to_weq w)) = Equivalence_toSourceHomotopy w.
Proof.
  try reflexivity.
  revert w.
  intros [f [g [p [q h]]]].
  unfold Equivalence_toSourceHomotopy; simpl.
  apply funextsec; intros x.
  try reflexivity.
Abort.


(* another proof *)
Definition weq_to_Equivalence' X Y : X ≃ Y -> Equivalence X Y.
  intros [f r].
  unfold isweq in r.
  set (g := λ y, hfiberpr1 f y (pr1 (r y))).
  set (p := λ y, pr2 (pr1 (r y))).
  simpl in p.
  set (L := λ x, pr2 (r (f x)) (hfiberpair f x (idpath (f x)))).
  set (q := λ x, maponpaths pr1 (L x)).
  set (q' := λ x, !q x).
  exact (makeEquivalence X Y f g p q'
             (λ x,
                 ! transportf_fun_idpath x (pr1 (pr1 (r (f x)))) (q x) (idpath (f x))
                 @ (fiber_paths (L x)))).
Defined.

Definition path_inv_rotate_lr {X} {a b c:X} (r:a = b) (p:b = c) (q:a = c) :
  q = r @ p -> q @ !p = r.
Proof. intros e. destruct p. destruct q. rewrite pathscomp0rid in e.
       exact e. Defined.

Definition path_inv_rotate_rr {X} {a b c:X} (r:a = b) (p:b = c) (q:a = c) :
  r @ p = q -> r = q @ !p.
Proof. intros e. destruct p. destruct q. rewrite pathscomp0rid in e.
       exact e. Defined.

Definition path_inv_rotate_ll {X} {a b c:X} (p:a = b) (r:b = c) (q:a = c) :
  q = p @ r -> !p @ q = r.
Proof. intros e. destruct p. destruct q. exact e. Defined.

Definition path_inv_rotate_rl {X} {a b c:X} (p:a = b) (r:b = c) (q:a = c) :
  p @ r = q -> r = !p @ q.
Proof. intros e. destruct p. destruct q. exact e. Defined.

Definition path_inverse_from_right {X} {x y:X} (p q:x = y) : !q@p = idpath _ -> p = q.
Proof. intros e. destruct q. exact e. Defined.

Definition path_inverse_from_right' {X} {x y:X} (p q:x = y) : p@!q = idpath _ -> p = q.
Proof. intros e. destruct q.
       intermediate_path (p @ idpath x).
       { apply pathsinv0. apply pathscomp0rid. } exact e. Defined.

Definition maponpaths_fun_fun_natl {X Y Z} {g g':X->Y} {f f':Y->Z}
           (q:homot g g') (p:homot f f') x :
  maponpaths f (q x) @ p (g' x) = p (g x) @ maponpaths f' (q x).
Proof. intros. destruct (q x). simpl. rewrite pathscomp0rid. reflexivity. Defined.

Definition maponpaths_fun_fun_fun_natl {X Y Z W} {g g':X->Y}
           (q:homot g g') (h:Y->Z) {f f':Z->W} (p:homot f f') x :
  maponpaths f (maponpaths h (q x)) @ p (h (g' x)) = p (h (g x)) @ maponpaths f' (maponpaths h (q x)).
Proof. intros. destruct (q x). simpl. rewrite pathscomp0rid. reflexivity. Defined.


Definition path_comp_inv_inv {X} {a b c:X} (p:a = b) (q:b = c) :
  ! q @ ! p = ! (p @ q).
Proof. intros. destruct p,q. reflexivity. Defined.

Local Notation "p @' q" := (pathscomp0 p q) (only parsing, at level 61, left associativity).
Local Arguments idpath {_ _}.

Lemma other_adjoint {X Y} (f : X -> Y) (g : Y -> X)
      (p : ∏ y : Y, f (g y) = y)
      (q : ∏ x : X, g (f x) = x)
      (h : ∏ x : X, maponpaths f (q x) = p (f x)) :
 ∏ y : Y, maponpaths g (p y) = q (g y).
Proof. intros. apply pathsinv0.
       intermediate_path (
            !(maponpaths g (p (f (g y))))
            @' maponpaths g (p (f (g y)))
            @' q (g y)).
       { rewrite pathsinv0l. reflexivity. }
       intermediate_path (
            !(maponpaths g (maponpaths f (q (g y))))
            @' maponpaths g (p (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. apply (maponpaths pathsinv0). apply (maponpaths (maponpaths g)).
         set (y' := g y). apply pathsinv0. exact (h y'). }
       intermediate_path (
            !(maponpaths g (maponpaths f (q (g y))))
            @' maponpaths g (p (f (g y)))
            @' ((!q (g (f (g y))))
                @' q (g (f (g y)))
                @' q (g y))).
       { rewrite pathsinv0l. reflexivity. }
       intermediate_path (
            !(maponpaths g (maponpaths f (q (g y))))
            @' maponpaths g (p (f (g y)))
            @' ((!q (g (f (g y))))
                @' (maponpaths g (p (f (g y)))
                    @' !(maponpaths g (p (f (g y))))
                    @' q (g (f (g y))))
                @' q (g y))).
       { maponpaths_pre_post_cat. apply path_inv_rotate_rr. reflexivity. }
       apply path_inverse_from_right.
       repeat rewrite path_assoc.
       intermediate_path (
            !(maponpaths g (p y))
            @' !(maponpaths g (maponpaths f (q (g y))))
            @' !(q (g (f (g (f (g y))))))
            @' maponpaths (funcomp f g) (maponpaths g (p (f (g y))))
            @' maponpaths g (p (f (g y)))
            @' !(maponpaths g (p (f (g y))))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat.
         apply path_inv_rotate_lr. rewrite <- path_assoc.
         apply path_inv_rotate_rl. apply pathsinv0.
         rewrite <- (maponpathscomp f g). set (y' := f (g y)).
         assert (r := maponpaths_fun_fun_fun_natl p g q y'). simpl in r.
         rewrite (maponpathscomp f). rewrite (maponpathscomp g).
         rewrite (maponpathscomp g (λ x : X, g (f x))) in r.
         rewrite maponpathsidfun in r. exact r. }
       intermediate_path (
            !(maponpaths g (p y))
            @' !(maponpaths g (maponpaths f (q (g y))))
            @' !(q (g (f (g (f (g y))))))
            @' maponpaths g (maponpaths f (maponpaths g (p (f (g y)))))
            @' maponpaths g (p (f (g y)))
            @' !(maponpaths g (p (f (g y))))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. rewrite <- (maponpathscomp f g). reflexivity. }
       intermediate_path (
            !(maponpaths g (p y))
            @' !(maponpaths g (maponpaths f (q (g y))))
            @' !(q (g (f (g (f (g y))))))
            @' maponpaths g (maponpaths f (maponpaths g (p (f (g y)))) @' p (f (g y)))
            @' !(maponpaths g (p (f (g y))))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. rewrite <- (maponpathscomp0 g).  reflexivity. }
       intermediate_path (
            !(maponpaths g (p y))
            @' !(maponpaths g (maponpaths f (q (g y))))
            @' !(q (g (f (g (f (g y))))))
            @' maponpaths g (maponpaths (funcomp g f) (p (f (g y))) @' p (f (g y)))
            @' !(maponpaths g (p (f (g y))))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. rewrite <- (maponpathscomp g f). reflexivity. }
       intermediate_path (
            !(maponpaths g (p y))
            @' !(maponpaths g (maponpaths f (q (g y))))
            @' !(q (g (f (g (f (g y))))))
            @' maponpaths g (p (f (g (f (g y)))) @' p (f (g y)))
            @' !(maponpaths g (p (f (g y))))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. rewrite <- (maponpathscomp g f).
         apply (maponpaths (maponpaths g)). generalize (f (g y)); clear y; intro y.
         assert (r := maponpaths_fun_fun_natl p p y); simpl in r.
         assert (s := maponpathsidfun (p y)); unfold idfun in s.
         rewrite s in r; clear s. rewrite (maponpathscomp g). exact r. }
       intermediate_path (
            !(maponpaths g (p y))
            @' !(maponpaths g (maponpaths f (q (g y))))
            @' !(q (g (f (g (f (g y))))))
            @' maponpaths g (p (f (g (f (g y)))))
            @' maponpaths g (p (f (g y)))
            @' !(maponpaths g (p (f (g y))))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. rewrite <- (maponpathscomp0 g). reflexivity. }
       intermediate_path (
            !(maponpaths g (p y))
            @' !(maponpaths g (maponpaths f (q (g y))))
            @' !(q (g (f (g (f (g y))))))
            @' maponpaths g (p (f (g (f (g y)))))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. repeat rewrite <- path_assoc.
         rewrite pathsinv0r. rewrite pathscomp0rid. reflexivity. }
       intermediate_path (
            maponpaths g ((!p y) @' maponpaths f (!q (g y)))
            @' !(q (g (f (g (f (g y))))))
            @' maponpaths g (p (f (g (f (g y)))))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. repeat rewrite <- maponpathsinv0.
         rewrite <- (maponpathscomp0 g). reflexivity. }
       intermediate_path (
            !(q (g y))
            @' maponpaths (funcomp f g) (maponpaths g ((!p y) @' maponpaths f (!q (g y))))
            @' maponpaths g (p (f (g (f (g y)))))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. repeat rewrite maponpathscomp0.
         repeat rewrite <- (maponpathscomp f g).
         repeat rewrite maponpathsinv0. repeat rewrite path_comp_inv_inv.
         apply (maponpaths pathsinv0).
         assert (r := ! maponpaths_fun_fun_fun_natl q (funcomp f g) q (g y)); simpl in r.
         rewrite maponpathsidfun in r. repeat rewrite <- (maponpathscomp f g) in r.
         unfold funcomp in r; simpl in r. repeat rewrite path_assoc.
         rewrite r. maponpaths_pre_post_cat. clear r.
         assert (r := ! maponpaths_fun_fun_fun_natl p g q y); simpl in r.
         rewrite maponpathsidfun in r. rewrite (maponpathscomp f).
         rewrite (maponpathscomp g). rewrite (maponpathscomp g) in r.
         exact r. }
       intermediate_path (
            !(q (g y))
            @' maponpaths g (maponpaths (funcomp g f) ((!p y) @' maponpaths f (!q (g y))))
            @' maponpaths g (p (f (g (f (g y)))))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. rewrite <- (maponpathscomp g f).
         rewrite <- (maponpathscomp f g). reflexivity. }
       intermediate_path (
            !(q (g y))
            @' maponpaths g (maponpaths (funcomp g f) ((!p y) @' maponpaths f (!q (g y)))
                  @' p (f (g (f (g y)))))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. rewrite <- maponpathscomp0. apply (maponpaths (maponpaths g)).
         reflexivity. }
       intermediate_path (
            !(q (g y))
            @' maponpaths g (p y @' ((!p y) @' maponpaths f (!q (g y))))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. rewrite <- (maponpathscomp g f).
         repeat rewrite maponpathscomp0. repeat rewrite maponpathsinv0.
         repeat rewrite <- path_assoc. repeat apply path_inv_rotate_ll.
         repeat rewrite path_assoc. repeat apply path_inv_rotate_rr.
         apply pathsinv0. repeat rewrite <- (maponpathscomp0 g).
         apply (maponpaths (maponpaths g)). rewrite h.
         assert (r := ! maponpaths_fun_fun_natl p p (f (g y))); simpl in r.
         rewrite maponpathsidfun in r. unfold funcomp in *; simpl in *.
         repeat rewrite <- (maponpathscomp g f) in r.
         repeat rewrite (path_assoc _ _ (p y)). rewrite r.
         repeat rewrite <- (path_assoc _ _ (p y)). apply (maponpaths pre_cat). clear r.
         assert (r := maponpaths_fun_fun_natl p p y); simpl in r.
         rewrite maponpathsidfun in r.
         repeat rewrite <- (maponpathscomp g f) in r. exact r. }
       intermediate_path (
            (!q (g y))
            @' maponpaths g (maponpaths f (!q (g y)))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. repeat rewrite <- maponpathsinv0.
         apply (maponpaths (maponpaths g)). rewrite pathsinv0r. reflexivity. }
       intermediate_path (
            (!q (g y))
            @' maponpaths (funcomp f g) (!q (g y))
            @' q (g (f (g y)))
            @' q (g y)).
       { maponpaths_pre_post_cat. rewrite <- (maponpathscomp f g).
         reflexivity. }
       intermediate_path ((!q (g y)) @' q (g y) @' (!q (g y)) @' q (g y)).
       { maponpaths_pre_post_cat. rewrite <- (maponpathscomp f g).
         apply path_inv_rotate_ll. repeat rewrite path_assoc.
         apply path_inv_rotate_rr.
         assert (r := ! maponpaths_fun_fun_natl q q (g y)); simpl in r.
         rewrite maponpathsidfun in r. rewrite (maponpathscomp f g).
         exact r. }
       rewrite pathsinv0l. simpl. rewrite pathsinv0l. reflexivity. Qed.

Definition inverseEquivalence {X Y} : Equivalence X Y -> Equivalence Y X.
Proof. intros [f [g [p [q h]]]]. simple refine (makeEquivalence Y X g f q p _).
       intro y. apply other_adjoint. assumption. Defined.
