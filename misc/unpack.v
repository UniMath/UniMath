Module Unpack4a.
  Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a.
  Arguments idpath {A a} , [A] a.
  Notation "x == y" := (paths x y) (at level 70, no associativity).
  Definition concat {A} {x y z : A} (p : x == y) (q : y == z) : x == z :=
    match p, q with idpath, idpath => idpath end.
  Arguments concat {A x y z} p q : simpl nomatch.
  Notation "p @ q" := (concat p q) (at level 60, right associativity).
  Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x == y) (u : P x) : P y :=
    match p with idpath => u end.
  Definition ap {A B} (f:A -> B) {x y:A} (p:x == y) : f x == f y
    := match p with idpath => idpath end.
  Definition reverse {X} {x y:X} : x==y -> y==x.
    intro p. destruct p. exact idpath. Defined.
  Notation "( x ; y )" := (existT _ x y).
  Notation pr1 := projT1.
  Notation pr2 := projT2.
  Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x == y }.
  Definition hfiberpr1 {X Y} (f:X->Y) (y:Y) := @pr1 _ (fun x:X => f x == y). 
  Definition iscontr (A : Type) := { a:A & forall b, a == b }.
  Definition isweq {A B : Type} (f : A -> B) := forall b, iscontr(hfiber f b).
  Definition weq A B := { f:A->B & isweq f }.
  Definition Sect {A B} (s : A -> B) (r : B -> A) := forall x : A, r (s x) == x.
  Record IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
    equiv_inv : B -> A ;
    eisretr : Sect equiv_inv f;
    eissect : Sect f equiv_inv;
    eisadj : forall x : A, eisretr (f x) == ap f (eissect x)
  }.
  Arguments BuildIsEquiv {A B} f _ _ _ _ .
  Record Equiv A B := BuildEquiv {
    equiv_fun : A -> B ;
    equiv_isequiv : IsEquiv equiv_fun
  }.
  Notation "A <~> B" := (Equiv A B) (at level 85).
  Definition proj2 {X} {P:X->Type} {w w':sigT P} (p:w==w') :
    transport P (ap (@pr1 X P) p) (pr2 w) == pr2 w'.
  Proof. destruct p. reflexivity. Defined.
  Definition transport_hfiber {X Y} (f:X->Y) x (w:hfiber f (f x)) (p: (x;idpath) == w) :
    transport (fun z : X => f z == f x)
        (ap (pr1 (P:=fun z : X => f z == f x)) p) idpath
        == 
    ap f (reverse (ap (fun w => (pr1 w)) p)).
  Proof. destruct p. reflexivity. Defined.
  Definition reverse_ap {A B} (f:A -> B) {x y:A} (p:x == y) :
    reverse (ap f (reverse p)) == ap f p.
  Proof. destruct p. reflexivity. Defined.
  Definition weq_to_AdjointEquivalence X Y : weq X Y -> X <~> Y.
    intros [f r].
    set (g := fun y => pr1 (pr1 (r y))). 
    set (p := fun y => pr2 (pr1 (r y)) : f (g y) == y). simpl in p.
    set (L := fun x => pr2 (r (f x)) (x; idpath (f x))).
    set (q := fun x => ap (@pr1 _ _) (L x) : g (f x) == x); simpl in q.
    exact (BuildEquiv _ _ f (BuildIsEquiv f g p q 
            (fun x => 
               reverse (proj2 (reverse (L x))) @ 
               transport_hfiber f x (pr1 (r (f x))) (reverse (L x)) @
               ap (ap f) (reverse_ap (fun w => pr1 w) (L x))))).
  Defined.
  Definition IsEquiv_sig {A B : Type} (f : A -> B) :=
    { g:B->A & { r:Sect g f & { s:Sect f g & forall x : A, r (f x) == ap f (s x) }}}.
  Definition pack {A B : Type} (f : A -> B) : IsEquiv_sig f -> IsEquiv f
    := fun X => BuildIsEquiv f (pr1 X) (pr1 (pr2 X)) (pr1 (pr2 (pr2 X))) (pr2 (pr2 (pr2 X))).
  Definition unpack {A B : Type} (f : A -> B) : IsEquiv f -> IsEquiv_sig f
    := fun Y => (equiv_inv f Y;(eisretr f Y;(eissect f Y;eisadj f Y))).
  Definition h {A B : Type} (f : A -> B) (X:IsEquiv_sig f) : unpack f (pack f X) == X
    := match X as t return (unpack f (pack f t) == t) 
       with (a;(b;(c;d))) => idpath (a;(b;(c;d))) end.
  Definition k {A B : Type} (f : A -> B) (Y:IsEquiv f) : pack f (unpack f Y) == Y
    := match Y as i return (pack f (unpack f i) == i) 
       with BuildIsEquiv _ equiv_inv eisretr eissect eisadj => idpath _ end.
  Lemma pack_weq {A B : Type} (f : A -> B) : weq (IsEquiv_sig f) (IsEquiv f).
  Proof. intros. exists (pack f). intros Y. exists (unpack f Y;k f Y). intros [X m].
         destruct m. assert (H := h f X). destruct H. reflexivity. Qed.
  Definition issig_isequiv_transparent {A B : Type} (f : A -> B) :
    IsEquiv_sig f <~> IsEquiv f.
  Proof.
    exact (weq_to_AdjointEquivalence _ _ (pack_weq f)).
  Defined.

  Definition ap' {A B} (f:A -> B) {x y:A} (p:x == y) : f x == f y
    := transport (fun z => f x == f z) p (idpath (f x)).
  Lemma apeq {A B} (f:A -> B) {x y:A} (p:x == y) : ap f p == ap' f p.
    destruct p. reflexivity. Defined.
  Definition proj2' {X} {P:X->Type} {w w':sigT P} (p:w==w') :
    transport P (ap' (@pr1 X P) p) (pr2 w) == pr2 w'.
  Proof. destruct p. reflexivity. Defined.
End Unpack4a.

Module Unpack4.
  Require Import Foundations.Generalities.uu0. (* Global Set Asymmetric Patterns. will persist *)
  Notation "a == b" := (paths a b) (at level 70, no associativity).
  Notation "x ,, y" := (tpair _ x y) (at level 69, right associativity).
  Variable A:Type.
  Variable B:A->Type.
  Variable C:forall a,B a->Type.
  Variable D:forall a b, C a b->Type.
  Record foo := make { a:A; b:B a; c:C a b; d:D a b c }.
  Definition bar := total2 (fun
         a:A => total2 ( fun
         b:B a => total2 ( fun
         c:C a b =>
           D a b c))).
  Definition pack : bar -> foo
    := fun X => make (pr1 X) (pr1 (pr2 X)) (pr1 (pr2 (pr2 X))) (pr2 (pr2 (pr2 X))).
  Definition unpack : foo -> bar
    := fun Y => (a Y,,(b Y,,(c Y,,d Y))).
  Definition h (X:bar) : unpack (pack X) == X
    := match X as t return (unpack (pack t) == t)
       with (a,,(b,,(c,,d))) => idpath (a,,(b,,(c,,d))) end.
  Definition k (Y:foo) : pack (unpack Y) == Y
    := match Y as i return (pack (unpack i) == i)
       with make a b c d => idpath _ end.
  Lemma pack_weq : weq bar foo.
  Proof. intros. exists pack. intros Y. exists (unpack Y,,k Y). intros [X m].
         destruct m. assert (H := h X). destruct H. reflexivity. Qed.
End Unpack4.

Module Isaprop.
  Require Import Foundations.Generalities.uu0. (* Global Set Asymmetric Patterns. will persist *)
  Notation "a == b" := (paths a b) (at level 70, no associativity).
  Notation "x ,, y" := (tpair _ x y) (at level 69, right associativity).
  Variable A:Type.
  Variable B:A->Type.
  Variable C:forall a,B a->Type.
  Variable D:forall a b, C a b->Type.
  Record foo := make { fa:A; fb:B fa; fc:C fa fb; fd:D fa fb fc }.
  Lemma isap (ia:isaprop A)
             (ib:forall a, isaprop(B a))
             (ic:forall a b, isaprop(C a b))
             (id:forall a b c, isaprop(D a b c)) : isaprop foo.
  Proof. apply invproofirrelevance.
         intros x y.
         destruct x as [xa xb xc xd], y as [ya yb yc yd].
         destruct (proofirrelevance _ ia xa ya).
         destruct (proofirrelevance _ (ib xa) xb yb).
         destruct (proofirrelevance _ (ic xa xb) xc yc).
         destruct (proofirrelevance _ (id xa xb xc) xd yd).
         reflexivity.
  Defined.
  Lemma isas (ia:isaset A)
             (ib:forall a, isaset(B a))
             (ic:forall a b, isaset(C a b))
             (id:forall a b c, isaset(D a b c)) : isaset foo.
  Proof. intros.
         intros x y.
         apply invproofirrelevance.
         intros p q.
         destruct x as [xa xb xc xd], y as [ya yb yc yd].
         set (r := maponpaths fa p). simpl in r.
         set (s := maponpaths fa q). simpl in s.
         set (t := pr1 (ia xa ya r s)); simpl in t.
   Abort.
End Isaprop.
