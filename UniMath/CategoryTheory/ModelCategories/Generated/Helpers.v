Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Three.

Require Import UniMath.CategoryTheory.ModelCategories.NWFS.

Local Open Scope cat.

(* useful lemma in a lot of proofs where we transport
   arrows / three morphisms *)
Lemma pr1_transportf_const {A : UU} {B : UU} {P : ∏ (a : A), B -> UU}
    {a a' : A} (e : a = a') (xs : ∑ b : B, P a b) :
    pr1 (transportf (λ x, ∑ b : B, P _ b) e xs) = pr1 xs.
Proof.
  rewrite pr1_transportf.
  rewrite transportf_const.
  reflexivity.
Qed.

(* helper for showing section_disp_axioms *)
Lemma section_disp_on_eq_morphisms {C : category} 
    (F : section_disp (three_disp C))
    {f f' : arrow C} {γ γ': f --> f'} 
    (H00 : arrow_mor00 γ = arrow_mor00 γ')
    (H11 : arrow_mor11 γ = arrow_mor11 γ') :
  pr1 (section_disp_on_morphisms F γ) =
    pr1 (section_disp_on_morphisms F γ').
Proof.
  assert (Heq : γ = γ').
  {
    use arrow_mor_eq; assumption.
  }
  induction Heq.
  reflexivity.
Qed.

Lemma section_disp_on_eq_morphisms' {C : category} 
    (F : section_disp (three_disp C)) {f f' : arrow C} {γ : f --> f'} 
    (H : arrow_mor00 γ · f' = f · arrow_mor11 γ) :
  let alternate := ((arrow_mor00 γ,, arrow_mor11 γ),, H) : f --> f' in
  pr1 (section_disp_on_morphisms F alternate) =
    pr1 (section_disp_on_morphisms F γ).
Proof.
  use section_disp_on_eq_morphisms; reflexivity.
Qed.

Lemma pr1_section_disp_on_morphisms_comp {C : category}
    (F : section_disp (three_disp C))
    {f f' f'' : arrow C}
    (γ : f --> f') (γ' : f' --> f'') :
  pr1 (section_disp_on_morphisms F γ) · pr1 (section_disp_on_morphisms F γ') =
      pr1 (section_disp_on_morphisms F (γ · γ')).
Proof.
  apply pathsinv0.
  etrans. apply maponpaths.
          apply (section_disp_comp F).
  reflexivity.
Qed.

Lemma eq_section_disp_on_morphism {C : category}
    {F F' : section_disp (three_disp C)} :
  F = F' -> ∏ f, F f = F' f.
Proof.
  intro H.
  now induction H.
Qed.

Lemma eq_section_nat_trans_disp_on_morphism {C : category}
    {F F' : section_disp (three_disp C)}
    {γ γ' : section_nat_trans_disp F F'} :
  γ = γ' -> ∏ f, γ f = γ' f. 
Proof.
  intro H.
  now induction H.
Qed.

(* double pathscomp0 for rewriting equalities on either side *)
Definition pathscomp1 {X : UU} {a b x y : X} (e1 : a = b) (e2 : a = x) (e3 : b = y) : x = y.
Proof.
  induction e1. induction e2. apply e3.
Qed.

Lemma eq_section_nat_trans_component
    {C : category}
    {F F' : Ff C} 
    {γ γ' : F --> F'}
    (H : γ = γ') : 
  ∏ f, section_nat_trans γ f = section_nat_trans γ' f.
Proof.
  now induction H.
Qed.

(* the above equality, but on the middle morphisms *)
Lemma eq_section_nat_trans_component11
    {C : category}
    {F F' : Ff C} 
    {γ γ' : F --> F'}
    (H : γ = γ') : 
  ∏ f, three_mor11 (section_nat_trans γ f) = three_mor11 (section_nat_trans γ' f).
Proof.
  now induction H.
Qed.

(* specific version of the above that we need
   in a proof *)
Lemma eq_section_nat_trans_comp_component11
    {C : category}
    {F F' F'' : Ff C} 
    {γ : F --> F''}
    {γ' : F --> F'}
    {γ'' : F' --> F''}
    (H : γ' · γ'' = γ) : 
  ∏ f, 
    three_mor11 (section_nat_trans γ' f) 
    · three_mor11 (section_nat_trans γ'' f) 
    = three_mor11 (section_nat_trans γ f).
Proof.
  induction H.
  intro f.
  apply pathsinv0.
  etrans. apply pr1_transportf_const.
  reflexivity.
Qed.

(* composition of morphisms equality *)
Lemma compeq {C : category} {x y z : C} 
    {f f' : x --> y} {g g' : y --> z} :
  f = f' -> g = g' -> f · g = f' · g'.
Proof.
  intros Hf Hg.
  induction Hf.
  induction Hg.
  reflexivity.
Qed.

Lemma funeq {A B : UU} {f g : A -> B}
    (H : f = g) :
  ∏ (a : A), f a = g a.
Proof.
  induction H.
  reflexivity.
Qed.