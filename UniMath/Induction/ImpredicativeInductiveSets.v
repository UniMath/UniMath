(** ** Impredicative Construction of Inductive Types that are Sets and Eliminate into Sets *)

(** This is based on Sam Speight's master's thesis *)

Require Import UniMath.Foundations.Init.
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.categories.Types.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.

Local Open Scope cat.
Local Open Scope functions.

Section BinaryProduct.

Variable A B: HSET.

Definition pre_prod: UU := ∏ (X: HSET), (pr1hSet A -> pr1hSet B -> pr1hSet X) -> pr1hSet X.

Lemma pre_prod_isaset: isaset pre_prod.
Proof.
  change (isofhlevel 2 pre_prod).
  apply impred.
  intro X.
  apply impred.
  intros _.
  apply setproperty.
Defined.

Definition pre_prod_as_set: HSET := hSetpair pre_prod pre_prod_isaset.

Definition nProduct (α: pre_prod): UU :=
  ∏(X Y : HSET) (f : pr1hSet X → pr1hSet Y) (h : pr1hSet A -> pr1hSet B -> pr1hSet X), f (α X h) = α Y (λ a b, f (h a b)).

Definition nProduct_isaset (α: pre_prod): isaset (nProduct α).
Proof.
  change (isofhlevel 2 (nProduct α)).
  apply impred.
  intro X.
  apply impred.
  intro Y.
  apply impred.
  intro f.
  apply impred.
  intro h.
  apply hlevelntosn.
  apply (setproperty Y).
Defined.

Definition nProduct_as_set (α: pre_prod): HSET := hSetpair _ (nProduct_isaset α).

Definition Product: UU := ∑ α: pre_prod, pr1hSet (nProduct_as_set α).

Definition Product_isaset: isaset Product.
Proof.
  apply (isaset_total2_hSet pre_prod_as_set).
Defined.

Definition Product_as_set: HSET := hSetpair _ Product_isaset.

Definition Pair (a : pr1hSet A) (b : pr1hSet B) : Product.
Proof.
  use tpair.
  - exact (λ X f, f a b).
  - cbn. red.
    intros; apply idpath.
Defined.

Definition Proj1: HSET ⟦Product_as_set, A⟧.
Proof.
  cbn.
  intro p.
  induction p as [α H].
  apply α.
  exact (fun x y => x).
Defined.

Definition Proj2: HSET ⟦Product_as_set, B⟧.
Proof.
  cbn.
  intro p.
  induction p as [α H].
  apply α.
  exact (fun x y => y).
Defined.

Definition Product_rec {C: HSET} (f: pr1hSet A -> pr1hSet B -> pr1hSet C) (p: Product) : pr1hSet C.
Proof.
  induction p.
  apply (pr1 C f).
Defined.

Lemma Product_beta (C: HSET) (f: pr1hSet A -> pr1hSet B -> pr1hSet C) (a: pr1hSet A) (b: pr1hSet B) : Product_rec f (Pair a b) = f a b.
Proof.
  apply idpath.
Defined.

Lemma Product_weak_η (x: Product) : Product_rec (C := Product_as_set) Pair x = x.
Proof.
  induction x as [P H].
  use total2_paths_f.
  - cbn.
    (* UniMath.MoreFoundations.Tactics.show_id_type. *)
    unfold pre_prod in P.
    apply funextsec.
    intro X.
    apply funextfun.
    intro f.
    cbn in H.
    red in H.
    exact (H Product_as_set X (fun x => pr1 x X f) Pair).
  - cbn.
    cbn in H.
    red in H.
    apply funextsec.
    intro X.
    apply funextsec.
    intro Y.
    apply funextsec.
    intro f.
    apply funextsec.
    intro h.
    apply (setproperty Y).
Defined.

Lemma Product_com_con {C D : HSET} (f : pr1hSet A → pr1hSet B → pr1hSet C) (g : pr1hSet C → pr1hSet D): Product_rec (λ a b, g (f a b)) = g ∘ Product_rec f.
Proof.
  apply funextfun.
  intro x.
  induction x as [p H].
  cbn in H. red in H.
  apply pathsinv0.
  exact (H C D g f).
Defined.

Lemma Product_η {C : HSET} (g : Product → pr1hSet C): Product_rec (λ a b, g (Pair a b)) = g.
Proof.
  eapply pathscomp0.
  - apply (Product_com_con (C := Product_as_set) Pair).
  - apply funextfun.
    intro x.
    unfold funcomp.
    apply maponpaths.
    apply Product_weak_η.
Defined.

Lemma Product_classical_η (p: Product) : Pair (Proj1 p) (Proj2 p) = p.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
  - apply pathsinv0.
    apply Product_weak_η.
  - set (Product_η_inst := Product_η (C := Product_as_set) (fun x => Pair (Proj1 x) (Proj2 x))).
    cbn in Product_η_inst.
    apply toforallpaths in Product_η_inst.
    apply Product_η_inst.
Defined.

(* still missing: universal property *)

(* copied from https://github.com/jonas-frey/Impredicative/blob/master/encode.hlean#L173 :
-- System F encoding
definition  preProduct (A B : USet) : USet :=
  tΠ (X : USet), (A ⇒ B ⇒ X) ⇒ X

-- naturality condition
definition nProduct {A B : USet} (α : preProduct A B) : UPrp
  := tΠ(X Y : USet) (f : X → Y) (h : A ⇒ B ⇒ X), f (α X h) == α Y (λ a, f ∘ h a)

-- refined encoding
definition  Product (A B : USet) : USet := σ(α : preProduct A B), nProduct α

-- constructor
definition Pair {A B : USet} (a : A) (b : B) : Product A B
  := ⟨λ X f, f a b, λ X Y f g, rfl⟩

-- eliminators
definition Proj1 {A B : USet} : Product A B → A
  := sigma.rec (λ alpha p, alpha A (λ x y, x))

definition Proj2 {A B : USet} : Product A B → B
  := sigma.rec (λ alpha p, alpha B (λ x y, y))

-- recursor
definition Product_rec {A B C : Set} (f : A ⇒ B ⇒ C) (p : Product A B) : C
  := p.1 C f

-- β rule
definition Product_β {A B C : USet} (f : A → B → C) (a : A) (b : B)
  :  Product_rec f (Pair a b) = f a b := rfl

-- weak η rule
definition Product_weak_η {A B : USet} (x : Product A B)
  :  Product_rec Pair x = x
  := begin induction x with p n, fapply sigma_eq, apply eq_of_homotopy2,
     intros X f, exact (n _ _ (Product_rec f) Pair), apply is_prop.elimo end

-- commuting conversion
definition Product_com_con {A B C D : USet} (f : A → B → C) (g : C → D)
  :  Product_rec (λ a b, g (f a b)) = g ∘ Product_rec f
  := (eq_of_homotopy (λ x, x.2 C D g f))⁻¹

-- strong η rule
definition Product_η {A B C : USet} (g : Product A B → C)
  :  Product_rec (λ a b, g (Pair a b)) = g
  := (Product_com_con Pair g) ⬝ eq_of_homotopy (λ x, ap g (Product_weak_η x))

-- classical η rule
definition Product_classical_η {A B : USet} (p : Product A B)
  :   Pair (Proj1 p) (Proj2 p) = p
  :=  ap (λ f, f p) (Product_η _)⁻¹ ⬝ (Product_weak_η p)

-- universal property
definition Product_univ_prop {A B C : USet} : is_equiv (@Product_rec A B C)
  := adjointify Product_rec
                (λ f a b, f (Pair a b))
                Product_η
                (λ g, eq_of_homotopy2 (Product_β g))
*)

End BinaryProduct.

Section BinaryCoproduct.

Variable A B: HSET.

Definition pre_sum: UU := ∏ (X: HSET), (pr1hSet A -> pr1hSet X) -> (pr1hSet B -> pr1hSet X) -> pr1hSet X.

Lemma pre_sum_isaset: isaset pre_sum.
Proof.
  change (isofhlevel 2 pre_sum).
  apply impred.
  intro X.
  apply impred.
  intros _.
  apply impred.
  intros _.
  apply setproperty.
Defined.

Definition pre_sum_as_set: HSET := hSetpair pre_sum pre_sum_isaset.

Definition nSum (α: pre_sum): UU :=
  ∏(X Y : HSET) (f : pr1hSet X → pr1hSet Y) (h : pr1hSet A -> pr1hSet X) (k: pr1hSet B -> pr1hSet X), f (α X h k) = α Y (f ∘ h) (f ∘ k).

Definition nSum_isaset (α: pre_sum): isaset (nSum α).
Proof.
  change (isofhlevel 2 (nSum α)).
  apply impred.
  intro X.
  apply impred.
  intro Y.
  apply impred.
  intro f.
  apply impred.
  intro h.
  apply impred.
  intro k.
  apply hlevelntosn.
  apply (setproperty Y).
Defined.

Definition nSum_as_set (α: pre_sum): HSET := hSetpair _ (nSum_isaset α).

Definition Sum: UU := ∑ α: pre_sum, pr1hSet (nSum_as_set α).

Definition Sum_isaset: isaset Sum.
Proof.
  apply (isaset_total2_hSet pre_sum_as_set).
Defined.

Definition Sum_as_set: HSET := hSetpair _ Sum_isaset.

Definition Sum_inl: HSET ⟦A, Sum_as_set⟧.
Proof.
  cbn.
  intro a.
  use tpair.
  - intros X f g.
    exact (f a).
  - cbn. red.
    intros ? ? ? ? k.
    apply idpath.
Defined.

Definition Sum_inr: HSET ⟦B, Sum_as_set⟧.
Proof.
  cbn.
  intro a.
  use tpair.
  - intros X f g.
    exact (g a).
  - cbn. red.
    intros ? ? ? ? k.
    apply idpath.
Defined.

Definition Sum_rec {C: HSET} (f: pr1hSet A -> pr1hSet C)
  (g: pr1hSet B -> pr1hSet C)(c: Sum) : pr1hSet C
  := pr1 c C f g.

Lemma Sum_β_l {C: HSET} (f: pr1hSet A -> pr1hSet C)
      (g: pr1hSet B -> pr1hSet C): (Sum_rec f g) ∘ Sum_inl = f.
Proof.
  apply idpath.
Defined.

Lemma Sum_β_r {C: HSET} (f: pr1hSet A -> pr1hSet C)
      (g: pr1hSet B -> pr1hSet C): (Sum_rec f g) ∘ Sum_inr = g.
Proof.
  apply idpath.
Defined.

Lemma Sum_weak_eta (x: Sum) : Sum_rec (C := Sum_as_set) Sum_inl Sum_inr x = x.
Proof.
  induction x as [c H].
  use total2_paths_f.
  - cbn.
    unfold pre_sum in c.
    apply funextsec.
    intro X.
    apply funextfun.
    intro f.
    apply funextfun.
    intro g.
    cbn in H.
    red in H.
    apply (H Sum_as_set X (fun x => pr1 x X f g)).
  - cbn.
    cbn in H.
    red in H.
    apply funextsec.
    intro X.
    apply funextsec.
    intro Y.
    apply funextsec.
    intro f.
    apply funextsec.
    intro h.
    apply funextsec.
    intro k.
    apply (setproperty Y).
Defined.

Lemma Sum_com_con {X Y: HSET} (f : pr1hSet A → pr1hSet X) (g : pr1hSet B → pr1hSet X) (h : pr1hSet X → pr1hSet Y): Sum_rec (h ∘ f) (h ∘ g) = h ∘ (Sum_rec f g).
Proof.
  apply funextfun.
  intro x.
  induction x as [c H].
  cbn in H. red in H.
  cbn.
  apply pathsinv0.
  apply H.
Defined.

Lemma Sum_η {X : HSET} (h : Sum → pr1hSet X)
  : Sum_rec (h ∘ Sum_inl) (h ∘ Sum_inr) = h.
Proof.
  eapply pathscomp0.
  apply Sum_com_con.
  apply funextfun.
  intro x.
  unfold funcomp.
  apply maponpaths.
  apply Sum_weak_eta.
Defined.

Lemma Sum_univ_prop {X: HSET} : (HSET ⟦Sum_as_set, X⟧) ≃ (Product (exponential_functor A X) (exponential_functor B X)).
Proof.
  use weq_iso.
  - intro h.
    apply Pair.
    + cbn. exact (h ∘ Sum_inl).
    + cbn. exact (h ∘ Sum_inr).
  - intro a. cbn.
    apply Sum_rec.
    + exact (Proj1 _ _ a).
    + exact (Proj2 _ _ a).
  - cbn. intro x.
    apply Sum_η.
  - cbn.  intro y.
    intermediate_path (Pair _ _ (Proj1 _ _ y) (Proj2 _ _ y)).
    + apply idpath.
    + apply Product_classical_η.
Defined.

(* copied from https://github.com/jonas-frey/Impredicative/blob/master/encode.hlean#L173:

definition  preSum (A B : USet) : USet :=
  tΠ(X : USet), (A ⇒ X) ⇒ (B ⇒ X) ⇒ X

-- naturality condition
definition nSum {A B : USet} (a : preSum A B) : UPrp
  := tΠ(X Y : USet) (f : X→Y) (h : A→X) (k : B→X), f(a X h k) == a Y (f∘h) (f∘k)

-- refined encoding
definition Sum (A B : USet) : USet := σ(α : preSum A B), nSum α

-- constructors
definition Sum_inl {A B : USet} (a : A) : Sum A B
  := ⟨λ X f g, f a, λ X Y f h k, rfl⟩

definition Sum_inr {A B : USet} (b : B) : Sum A B
  := ⟨λ X f g, g b, λ X Y f h k, rfl⟩

-- recursor
definition Sum_rec {A B X : USet} (f : A → X) (g : B → X) (c : Sum A B) : X
  := c.1 X f g

-- β rules
definition Sum_β_l {A B X : USet} (f : A → X) (g : B → X)
  : Sum_rec f g ∘ Sum_inl = f := rfl

definition Sum_β_r {A B X : USet} (f : A → X) (g : B → X)
  : Sum_rec f g ∘ Sum_inr = g := rfl

-- weak η
definition Sum_weak_η {A B : USet} (x : Sum A B)
  : Sum_rec Sum_inl Sum_inr x = x
  := begin induction x with α p, fapply sigma_eq,
     apply eq_of_homotopy3, intro X f g,  unfold Sum_rec, apply p,
     apply is_prop.elimo end

--commuting conversion
definition Sum_com_con {A B X Y : USet} (f : A → X) (g : B → X) (h : X → Y)
  :  Sum_rec (h ∘ f) (h ∘ g) = h ∘ Sum_rec f g
  := begin apply eq_of_homotopy, intro α, induction α with α p, symmetry, apply p end

-- strong η
definition Sum_η {A B X : USet} (h : Sum A B → X)
  :  Sum_rec (h∘Sum_inl) (h∘Sum_inr) = h
  := !Sum_com_con ⬝ eq_of_homotopy (λ x, ap h (Sum_weak_η x))

--universal property
definition Sum_univ_prop {A B X : USet}
  :  (Sum A B ⇒ X) ≃ (Product (A ⇒ X) (B ⇒ X))
  := equiv.MK (λ h, Pair (h ∘ Sum_inl) (h ∘ Sum_inr))
              (λ a, Sum_rec (Proj1 a) (Proj2 a))
              Product_classical_η
              Sum_η

*)

End BinaryCoproduct.

Section NaturalNumbers.

Definition pre_nat: UU := ∏ (X: HSET), (pr1hSet X -> pr1hSet X) -> pr1hSet X -> pr1hSet X.

Lemma pre_nat_isaset: isaset pre_nat.
Proof.
  change (isofhlevel 2 pre_nat).
  apply impred.
  intro X.
  apply impred.
  intros _.
  apply impred.
  intros _.
  apply setproperty.
Defined.

Definition pre_nat_as_set: HSET := hSetpair _ pre_nat_isaset.

Definition nNat (α: pre_nat): UU :=
  ∏(X Y : HSET) (x: pr1hSet X) (y: pr1hSet Y)(h: pr1hSet X → pr1hSet X)(k: pr1hSet Y → pr1hSet Y) (f : pr1hSet X -> pr1hSet Y), f x = y -> f ∘ h = k ∘ f -> f (α X h x) = α Y k y.

Definition nNat_isaset (α: pre_nat): isaset (nNat α).
Proof.
  change (isofhlevel 2 (nNat α)).
  apply impred.
  intro X.
  apply impred.
  intro Y.
  apply impred.
  intro x.
  apply impred.
  intro y.
  apply impred.
  intro h.
  apply impred.
  intro k.
  apply impred.
  intro f.
  apply impred.
  intros _.
  apply impred.
  intros _.
  apply hlevelntosn.
  apply (setproperty Y).
Defined.

Definition nNat_as_set (α: pre_nat): HSET := hSetpair _ (nNat_isaset α).

Definition Nat: UU := ∑ α: pre_nat, pr1hSet (nNat_as_set α).

Definition Nat_isaset: isaset Nat.
Proof.
  apply (isaset_total2_hSet pre_nat_as_set).
Defined.

Definition Nat_as_set: HSET := hSetpair _ Nat_isaset.

Definition Z: Nat.
Proof.
  use tpair.
  - exact (λ X f x, x).
  - cbn. red.
    intros; assumption.
Defined.

Definition S: HSET ⟦Nat_as_set,Nat_as_set⟧.
Proof.
  cbn.
  intro n.
  use tpair.
  - exact (λ X h x, h (pr1 n X h x)).
  - cbn. red.
    intros ? ? ? ? ? ? ? H1 H2.
    induction n as [n1 n2].
    cbn in n2. red in n2.
    cbn.
    eapply pathscomp0.
    2: { apply maponpaths.
         apply (n2 X Y x y h k f); assumption. }
    apply (toforallpaths _ _ _ H2).
Defined.

Definition Nat_rec {C: HSET} (h: pr1hSet C -> pr1hSet C)
  (x: pr1hSet C)(n: Nat) : pr1hSet C := pr1 n C h x.

Lemma Nat_β {C: HSET} (h: pr1hSet C -> pr1hSet C)
  (x: pr1hSet C): Nat_rec h x Z = x.
Proof.
  apply idpath.
Defined.

Lemma Nat_β' {C: HSET} (h: pr1hSet C -> pr1hSet C)
  (x: pr1hSet C) (n: Nat): Nat_rec h x (S n) = h (Nat_rec h x n).
Proof.
  apply idpath.
Defined.

Lemma Nat_weak_eta (n: Nat) : Nat_rec (C := Nat_as_set) S Z n = n.
Proof.
  induction n as [n0 H].
  use total2_paths_f.
  - cbn.
    unfold pre_nat in n0.
    apply funextsec.
    intro X.
    apply funextfun.
    intro h.
    apply funextfun.
    intro x.
    cbn in H.
    red in H.
    apply (H Nat_as_set X Z x S h (fun n => pr1 n X h x)); apply idpath.
  - cbn.
    cbn in H.
    red in H.
    apply funextsec.
    intro X.
    apply funextsec.
    intro Y.
    apply funextsec.
    intro x.
    apply funextsec.
    intro y.
    apply funextsec.
    intro h.
    apply funextsec.
    intro k.
    apply funextsec.
    intro f.
    apply funextfun.
    intro H1.
    apply funextfun.
    intro H2.
    apply (setproperty Y).
Defined.

Lemma Nat_η {C: HSET} (h: pr1hSet C -> pr1hSet C)
      (x: pr1hSet C) (f: Nat → pr1hSet C)
      (p : f Z = x) (q: funcomp S f = funcomp f h):
  f = Nat_rec h x.
Proof.
  apply funextfun.
  intro n.
  eapply pathscomp0.
  - apply maponpaths.
    apply pathsinv0.
    apply Nat_weak_eta.
  - unfold Nat_rec.
    induction n as [n0 H].
    cbn in H. red in H.
    cbn.
    apply H; assumption.
Defined.

(* copied from https://github.com/jonas-frey/Impredicative/blob/master/encode.hlean#L289:

definition preNat : USet := tΠ X : USet, (X ⇒ X) ⇒ X ⇒ X

-- naturality condition
definition nNat (α : preNat) : UPrp
  := tΠ (X Y : USet) (x : X) (y : Y) (h : X → X) (k : Y → Y) (f : X → Y),
         f x = y ⇒ f ∘ h = k ∘ f ⇒ f (α X h x) == α Y k y

-- refined encoding
definition Nat : USet := σ(α : preNat), nNat α

-- constructors
definition Z : Nat := ⟨λ X f x, x, λ X Y x y h k f u v, u⟩

definition S (n : Nat) : Nat
  := begin fconstructor, λ X h x, h (n.1 X h x), intros X Y x y h k f u v,
     refine (ap (λ f, f (n.1 X h x)) v) ⬝ _, apply ap k, apply n.2, exact u,
     assumption end

-- recursor
definition Nat_rec {X : USet} (h : X → X) (x : X) (n : Nat) : X := n.1 X h x

-- β rules
definition Nat_β {X : USet} (h : X → X) (x : X) : Nat_rec h x Z = x := rfl
definition Nat_β' {X : USet} (h : X → X) (x : X) (n : Nat)
  :  Nat_rec h x (S n) = h (Nat_rec h x n) := rfl

-- η rules
definition Nat_weak_η (n : Nat) : Nat_rec S Z n = n
  := begin
     induction n with n p,
     fapply sigma_eq, apply eq_of_homotopy3, intro X h x,
     apply p Nat X Z x S h (Nat_rec h x), reflexivity, apply eq_of_homotopy,
     intro, reflexivity, apply is_prop.elimo end

definition Nat_η {X:USet} (h:X→X) (x:X) (f:Nat→X) (p : f Z = x) (q:f∘S=h∘ f)
  :  f = Nat_rec h x
  := begin fapply eq_of_homotopy, intro n, refine (ap f (Nat_weak_η n))⁻¹ ⬝ _,
unfold Nat_rec, induction n with m k, apply k, assumption, assumption end

*)

End NaturalNumbers.

(* preparation for the general case:
Variable F: HSET ⟦A, A⟧.
*)
