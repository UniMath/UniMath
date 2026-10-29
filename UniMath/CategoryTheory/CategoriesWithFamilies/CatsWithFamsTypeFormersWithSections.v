
(**  CwF Type Formers in the Style of Comp Cat Type Formers

We can define the type formers of a categories with families in the style of the type formers of a comprehension
category using the terms as sections view. This helps when constructing the type former structure of a CwF
from that of a comprehension category, which is done in ComprehensionCategories.CwFFromCompCatWithUniv
We do this for Π- and Σ-types. The unit type works as is.

Contents:
1. Lemmas
2. Sigma Types
3. Pi Types

*)


Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Pullbacks.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.OppositeCategory.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.All.
Require Import UniMath.CategoryTheory.Core.Setcategories.

Require Import UniMath.CategoryTheory.CategoriesWithFamilies.CatsWithFams.

Local Open Scope cat.
Local Open Scope cwf.

(** * 1. Lemmas *)

(* First we need to make helper lemmas for treating CwF terms as sections of projections from extended contexts *)

Section lemmas.

  Definition cwf_section_to_tm
               {C : cwf} {Γ : C} {A : cwf_ty Γ}
  (t : Γ --> Γ & A) (h : t · p_ A = identity Γ)
  : cwf_tm A
  := transportf cwf_tm (cwf_subst_ty_id A)
       (transportf cwf_tm (cwf_subst_ty_eq A h)
          (cwf_qA_subst t)).

  Lemma cwf_section_to_tm_section_eq
          {C : cwf} {Γ : C} {A : cwf_ty Γ}
  (t : Γ --> Γ & A) (h : t · p_ A = identity Γ)
  : ⟨⟨ identity Γ , cwf_subst_tm_id (cwf_section_to_tm t h) ⟩⟩ = t.
Proof.
  rewrite cwf_pair_eta.
  rewrite (cwf_subst_pair_eq_subst h _).
  apply (maponpaths (λ t, ⟨⟨ identity Γ , t ⟩⟩)).
  unfold cwf_subst_tm_id, cwf_section_to_tm,
    cwf_qA_subst, cwf_subst_tm_comp.
  rewrite transportf_subst_tm_on_s_eq.
  rewrite !transport_f_f.
  apply (maponpaths (λ z, transportf cwf_tm z ((q_ A) [[ t ]]tm))).
  apply setproperty.
Qed.

Lemma cwf_section_to_tm_pair_eq
        {C : cwf} {Γ : C} {A : cwf_ty Γ}
  (a : cwf_tm A)
  : cwf_section_to_tm ( ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ )
      (cwf_pair_p (identity Γ) (cwf_subst_tm_id a))
    = a.
Proof.
  unfold cwf_section_to_tm, cwf_qA_subst, cwf_subst_tm_comp.
  etrans.
  { do 3 apply maponpaths. apply cwf_pair_q_subst. }
  unfold cwf_subst_tm_id.
  rewrite !transport_f_f.
  apply (transportf_set cwf_tm).
  apply setproperty.
Qed.

Lemma cwf_section_to_tm_eq
        {C : cwf} {Γ : C} {A : cwf_ty Γ}
  {σ σ' : Γ --> Γ & A}
  (e : σ = σ')
  (h : σ · p_ A = identity Γ)
  (h' : σ' · p_ A = identity Γ)
  : cwf_section_to_tm σ h = cwf_section_to_tm σ' h'.
Proof.
  induction e.
  unfold cwf_section_to_tm.
  apply maponpaths, maponpaths_2.
  apply setproperty.
Qed.

Definition cwf_tm_eq_to_mor
             {C : cwf} {Γ : C}
  {A A' : cwf_ty Γ} (eq : A = A')
  : Γ & A --> Γ & A'.
Proof.
  induction eq.
  exact (identity _).
Defined.


Lemma cwf_tm_eq_to_mor_inv
   {C : cwf} {Γ : C} {A A' : cwf_ty Γ} (e : A = A')
  : cwf_tm_eq_to_mor e · cwf_tm_eq_to_mor (! e) = identity _.
Proof.
  induction e.
  apply id_left.
Qed.

Lemma cwf_tm_eq_to_mor_inv'
  {C: cwf} {Γ : C} {A A' : cwf_ty Γ} (e : A = A')
  : cwf_tm_eq_to_mor (! e) · cwf_tm_eq_to_mor e = identity _.
Proof.
  induction e.
  apply id_left.
Qed.

Lemma cwf_subst_pb
  {C : cwf} {Γ Δ : C} {A : cwf_ty Γ} (s : Δ --> Γ) {Θ : C}
  (f g : Θ --> Δ & ( A [[ s ]] ) )
  (e : f · p_ (A [[s]]) = g · p_ (A [[s]]))
  (e' : f · cwf_lift s A = g · cwf_lift s A)
  : f = g.
Proof.
  use (cwf_pair_unique (g · p_ (A [[ s ]])) (cwf_qA_subst g)).
  - exact e.
  - apply idpath.
  - assert (Hq : q_ (A [[ s ]])
                 = transportf (cwf_tm)
                     (!(cwf_subst_ty_comp A s (p_ (A [[ s ]]))))
                     (transportf (cwf_tm)
                        (!(cwf_pair_q_subst_eq
                             (p_ (A [[ s ]]) · s)
                             (cwf_subst_tm_comp A s (p_ (A [[ s ]])) (q_ (A [[ s ]])))))
                        (q_ A [[ cwf_lift s A ]]tm))).
    { refine (!(transportbfinv (cwf_tm) _ _) @ _).
      apply maponpaths.
      exact (cwf_pair_q_subst'
               (p_ (A [[ s ]]) · s)
               (cwf_subst_tm_comp A s (p_ (A [[ s ]])) (q_ (A [[ s ]])))). }
    rewrite transportf_subst_tm_on_s_eq.
    unfold cwf_qA_subst, cwf_subst_tm_comp.
    rewrite transport_f_f.
    etrans.
    { apply maponpaths.
      exact (maponpaths (λ z, z [[ f ]]tm) Hq). }
    etrans.
    { apply maponpaths.
      etrans.
      { apply transportf_cwf_subst_tm. }
      apply maponpaths.
      apply transportf_cwf_subst_tm. }
    rewrite !transport_f_f.
    etrans.
    { apply maponpaths.
      exact (cwf_subst_tm_on_comp' f (cwf_lift s A) (q_ A)). }
    rewrite transport_f_f.
    refine (!_).
    etrans.
    { apply maponpaths.
      exact (maponpaths (λ z, z [[ g ]]tm) Hq). }
    etrans.
    { apply maponpaths.
      etrans.
      { apply transportf_cwf_subst_tm. }
      apply maponpaths.
      apply transportf_cwf_subst_tm. }
    rewrite !transport_f_f.
    etrans.
    { apply maponpaths.
      exact (cwf_subst_tm_on_comp' g (cwf_lift s A) (q_ A)). }
    rewrite transport_f_f.
    etrans.
    { apply maponpaths.
      exact (!(cwf_subst_tm_eq' (q_ A) e')). }
    rewrite transport_f_f.
    apply maponpaths_2.
    apply setproperty.
  - apply idpath.
Qed.

Lemma cwf_section_to_tm_subst
  {C : cwf} {Γ Δ : C} {A : cwf_ty Γ} (s : Δ --> Γ)
  (σ  : Γ --> Γ & A) (h : σ · p_ A = identity Γ)
  (σ' : Δ --> Δ & ( A [[ s ]] )) (h' : σ' · p_ (A [[s]]) = identity Δ)
  (comm : σ' · cwf_lift s A = s · σ)
  : (cwf_section_to_tm σ h) [[ s ]]tm = cwf_section_to_tm σ' h'.
Proof.
  etrans.
  { refine (!_).
    apply (cwf_section_to_tm_pair_eq ((cwf_section_to_tm σ h) [[ s ]]tm)). }
  apply cwf_section_to_tm_eq.
  refine (!_).
  apply (cwf_subst_pb s).
  - rewrite cwf_pair_p. exact h'.
  - rewrite comm.
    etrans.
    { apply maponpaths.
      refine (!_).
      apply cwf_section_to_tm_section_eq. }
    apply cwf_pair_subst_comm.
Qed.

Lemma cwf_subst_mor_transportf
  {C : cwf} {Γ Δ : C} (B : cwf_ty Γ) {s s' : Δ --> Γ}
  (e : s = s') (t : cwf_tm (B [[ s ]]))
  : transportf (λ X, cwf_tm (B [[ X ]])) e t
    = transportf cwf_tm (maponpaths (λ X : C ⟦ Δ, Γ ⟧, B [[ X ]]) e) t.
Proof.
  induction e. apply idpath.
Qed.

Lemma cwf_qA_subst_eq
  {C : cwf} {Γ Δ : C} {A : cwf_ty Γ} {s s' : Δ --> Γ & A} (e : s = s'):
  (transportf (λ X, cwf_tm (A [[ X ]])) (cancel_postcomposition _ _ _ e) (cwf_qA_subst s)
   = cwf_qA_subst s').
Proof.
  induction e. apply idpath.
Qed.

Lemma cwf_qA_subst_eq'
  {C : cwf} {Γ Δ : C} {A : cwf_ty Γ} {s s' : Δ --> Γ & A} (e : s = s'):
  cwf_qA_subst s
    = transportf (λ X : C ⟦ Δ, Γ ⟧, cwf_tm (A [[ X ]]))
        (! cancel_postcomposition _ _ _ e) (cwf_qA_subst s').
Proof.
  rewrite <- (cwf_qA_subst_eq e).
  rewrite transport_f_f.
  rewrite pathsinv0r.
  apply idpath.
Qed.

End lemmas.

(** * 2. Σ-Type *)
(* Constructing Sigma in the Style of Comp Cats using terms as sections*)

Section cwf_sigma_with_sections.


  Context (C : cwf).
  Context (Sig : sigma_form C).

  Definition sigma_pair_mor_sections
    : UU
    := ∏ (Γ : C) (A : cwf_ty Γ)
                        (B : cwf_ty (Γ & A)),
              ((Γ & A) & B) --> (Γ & Sig Γ A B).

  Context (pair_mor : sigma_pair_mor_sections).

  Definition sigma_pair_pi_sections : UU
    := ∏ (Γ : C) (A : cwf_ty Γ)
                      (B : cwf_ty (Γ & A)),
              pair_mor Γ A B · p_ (Sig Γ A B) =
                p_ B · p_ A.

  Context (pair_π : sigma_pair_pi_sections).

  Definition sigma_proj_mor_sections : UU
    :=  ∏ (Γ : C) (A : cwf_ty Γ)
                        (B : cwf_ty (Γ & A)),
              (Γ & Sig Γ A B) --> ((Γ & A) & B).

  Context (proj_mor : sigma_proj_mor_sections).

  Definition sigma_beta_law_sections : UU
    := ∏ (Γ : C) (A : cwf_ty Γ)
                     (B : cwf_ty (Γ & A)),
              pair_mor Γ A B · proj_mor Γ A B =
                identity _.

  Context (β_law :  sigma_beta_law_sections).

  Definition sigma_eta_law_sections : UU
                                        := ∏ (Γ : C) (A : cwf_ty Γ)
                     (B : cwf_ty (Γ & A)),
              proj_mor Γ A B · pair_mor Γ A B =
                identity _.

  Context (η_law : sigma_eta_law_sections).

  Context (Sig_sub : sigma_subst C Sig).

  Definition sigma_pair_sub_sections : UU
                                         := ∏ (Γ Δ : C) (s : Δ --> Γ)
                        (A : cwf_ty Γ)
                        (B : cwf_ty (Γ & A)),
              pair_mor Δ (A [[ s ]]) (B [[ cwf_lift s A ]]) ·
                cwf_tm_eq_to_mor (!(Sig_sub Γ Δ s A B)) ·
                cwf_lift s (Sig Γ A B)
              = cwf_lift (cwf_lift s A) B · pair_mor Γ A B.

  Context (pair_sub : sigma_pair_sub_sections).

  Definition cwf_proj_sections
    {Γ : C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
    (p : cwf_tm (Sig Γ A B))
    : Γ --> (Γ & A) & B
    := ⟨⟨ identity Γ , cwf_subst_tm_id p ⟩⟩ · proj_mor Γ A B.

  Lemma cwf_beta_sections
    {Γ : C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
    (p : cwf_tm (Sig Γ A B))
    : cwf_proj_sections p · p_ B · p_ A = identity Γ.
  Proof.
    unfold cwf_proj_sections.
    rewrite !assoc'.
    rewrite <- (pair_π _ _ _).
    rewrite (assoc (proj_mor _ _ _) _ _).
    rewrite η_law.
    rewrite id_left.
    apply cwf_pair_p.
  Qed.

  Definition cwf_sigma_pi1_sections : sigma_pi1 C Sig.
  Proof.
    intros Γ A B p.
    exact (cwf_section_to_tm
             (cwf_proj_sections p · p_ B)
             (cwf_beta_sections _ )).
  Defined.


  Lemma cwf_proj_pB_eq
    {Γ : C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
    (p : cwf_tm (Sig Γ A B))
    : cwf_proj_sections p · p_ B
      = ⟨⟨ identity Γ , cwf_subst_tm_id (cwf_sigma_pi1_sections Γ A B p) ⟩⟩.
  Proof.
    refine (!_).
    apply cwf_section_to_tm_section_eq.
  Qed.


  Definition cwf_sigma_pi2_sections : sigma_pi2 C Sig cwf_sigma_pi1_sections.
  Proof.
    intros Γ A B p.
    refine (transportf (λ X, cwf_tm (B [[ X ]])) _ _).
    exact (cwf_proj_pB_eq p).
    exact (cwf_qA_subst (cwf_proj_sections p)).
  Defined.

  Definition cwf_pair_sections
    {Γ : C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
    (a : cwf_tm A)
    (b : cwf_tm (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]]))
    : Γ --> Γ & Sig Γ A B
    := ⟨⟨ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ , b ⟩⟩ · pair_mor Γ A B.

  Lemma cwf_pair_sections_p_eq
    {Γ : C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
    (a : cwf_tm A)
    (b : cwf_tm (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]]))
    : cwf_pair_sections a b · p_ (Sig Γ A B) = identity Γ.
  Proof.
    unfold cwf_pair_sections.
    rewrite !assoc'.
    rewrite pair_π.
    rewrite assoc.
    rewrite !cwf_pair_p.
    apply idpath.
  Qed.

  Definition cwf_sigma_pair_sections : sigma_pair C Sig.
  Proof.
    intros Γ A B a b.
    exact (cwf_section_to_tm (cwf_pair_sections a b)
             (cwf_pair_sections_p_eq a b)).
  Defined.

  Lemma cwf_sigma_proj_pair_eq
    {Γ : C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)} {a a' : cwf_tm A}
    (ea : a = a')
    {b  : cwf_tm (B [[ ⟨⟨ identity Γ, cwf_subst_tm_id a  ⟩⟩ ]])}
    {b' : cwf_tm (B [[ ⟨⟨ identity Γ, cwf_subst_tm_id a' ⟩⟩ ]])}
    (eb : transportf (λ x, cwf_tm (B [[ ⟨⟨ identity Γ, cwf_subst_tm_id x ⟩⟩ ]])) ea b = b')
    : cwf_sigma_pair_sections Γ A B a b =  cwf_sigma_pair_sections Γ A B a' b'.
  Proof.
    induction ea, eb.
    apply idpath.
  Qed.

  Lemma cwf_proj_pair_pB_eq
    {Γ : C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
    (a : cwf_tm A)
    (b : cwf_tm (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]]))
    : cwf_proj_sections ( cwf_sigma_pair_sections Γ A B a b) · p_ B
      = ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩.
  Proof.
    unfold cwf_proj_sections,  cwf_sigma_pair_sections.
    refine (!_).
    rewrite cwf_section_to_tm_section_eq.
    unfold cwf_pair_sections.
    rewrite !assoc'.
    rewrite (assoc (pair_mor Γ A B) (proj_mor Γ A B) (p_ B)).
    rewrite β_law, id_left.
    rewrite cwf_pair_p.
    apply idpath.
  Qed.

  Lemma cwf_proj_section_pair_eta
    {Γ : C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
    (p : cwf_tm (Sig Γ A B))
    : cwf_proj_sections p
      = ⟨⟨ ⟨⟨ identity Γ , cwf_subst_tm_id (cwf_sigma_pi1_sections Γ A B p) ⟩⟩ ,
           cwf_sigma_pi2_sections Γ A B p ⟩⟩.
  Proof.
    refine (cwf_pair_eta _ @ _).
    exact (cwf_subst_pair_eq_subst (cwf_proj_pB_eq p) _).
  Qed.

  Lemma cwf_proj_section_pair_eq
    {Γ : C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
    (a : cwf_tm A)
    (b : cwf_tm (B [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]]))
    : cwf_proj_sections ( cwf_sigma_pair_sections Γ A B a b)
      = ⟨⟨ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ , b ⟩⟩.
  Proof.
    unfold cwf_proj_sections,  cwf_sigma_pair_sections.
    etrans.
    { apply maponpaths_2. apply cwf_section_to_tm_section_eq. }
    unfold cwf_pair_sections.
    rewrite assoc'.
    rewrite β_law.
    apply id_right.
  Qed.

  Definition cwf_sigma_beta1_sections
    : sigma_beta1 C Sig cwf_sigma_pi1_sections
        cwf_sigma_pi2_sections cwf_sigma_pair_sections.
  Proof.
    intros Γ A B a b.
    refine (_ @ cwf_section_to_tm_pair_eq a).
    apply cwf_section_to_tm_eq.
    exact (cwf_proj_pair_pB_eq a b).
  Defined.

  Lemma cwf_proj_sections_proj_pair
    (Γ : C) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
    (a : cwf_tm A) (b : cwf_tm (B [[ ⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩ ]]))
    : cwf_proj_sections ( cwf_sigma_pair_sections Γ A B a b)
    = ⟨⟨ ⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩, b ⟩⟩.
  Proof.
    unfold cwf_proj_sections.
    etrans.
    { apply maponpaths_2.
      apply (cwf_section_to_tm_section_eq (cwf_pair_sections a b)). }
    unfold cwf_pair_sections.
    rewrite <- assoc.
    etrans. {
      apply maponpaths.
      apply β_law. }
    apply id_right.
  Qed.

  Definition cwf_sigma_beta2_sections
    : sigma_beta2 C Sig cwf_sigma_pi1_sections
        cwf_sigma_pi2_sections  cwf_sigma_pair_sections
        cwf_sigma_beta1_sections.
  Proof.
    intros Γ A B a b.
    unfold cwf_sigma_pi2_sections.
    etrans.
    { do 2 apply maponpaths.
      apply (cwf_qA_subst_eq' (cwf_proj_sections_proj_pair Γ A B a b)).
    }
    rewrite !transport_f_f.
    unfold cwf_qA_subst.
    rewrite cwf_pair_q_subst.
    rewrite !cwf_subst_mor_transportf.
    unfold cwf_subst_tm_comp.
    rewrite !transport_f_f.
    apply (transportf_set cwf_tm).
    apply setproperty.
  Defined.

  Definition cwf_sigma_eta_sections
    : sigma_eta C Sig cwf_sigma_pi1_sections
        cwf_sigma_pi2_sections  cwf_sigma_pair_sections.
    intros Γ A B p.
    refine (_ @ cwf_section_to_tm_pair_eq p).
    apply cwf_section_to_tm_eq.
    unfold cwf_pair_sections.
    rewrite <- cwf_proj_section_pair_eta.
    unfold cwf_proj_sections.
    rewrite !assoc'.
    rewrite η_law.
    apply id_right.
  Defined.

  Lemma cwf_proj_sections_sub
  {Γ Δ : C} (s : Δ --> Γ) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
  : cwf_lift s (Sig Γ A B) · proj_mor Γ A B
    = cwf_tm_eq_to_mor (Sig_sub Γ Δ s A B)
        · proj_mor Δ (A [[ s ]]) (B [[ cwf_lift s A ]])
        · cwf_lift (cwf_lift s A) B.
  Proof.
    refine (!(id_right _) @ _ @ id_right _).
    etrans.
    2: {
      apply maponpaths.
      apply (β_law Γ A B). }
    rewrite !assoc.
    rewrite id_right.
    apply maponpaths_2.
    refine (!_).
    etrans.
    { rewrite !assoc'.
      do 2 apply maponpaths.
      exact (!(pair_sub Γ Δ s A B)). }
    rewrite !assoc.
    refine (_ @ id_left _).
    apply cancel_postcomposition.
    etrans.
    { apply cancel_postcomposition.
      rewrite assoc'.
      rewrite η_law.
      apply id_right. }
    apply cwf_tm_eq_to_mor_inv.
  Qed.

  Lemma cwf_tm_eq_from_lift_pair_eq
  {Γ Δ : C} (s : Δ --> Γ) (A : cwf_ty Γ) (u v : cwf_tm (A [[ s ]]))
  (p : ⟨⟨ identity Δ, cwf_subst_tm_id u ⟩⟩ · cwf_lift s A
       = ⟨⟨ identity Δ, cwf_subst_tm_id v ⟩⟩ · cwf_lift s A)
  : u = v.
  Proof.
    refine (!(cwf_section_to_tm_pair_eq u) @ _ @ cwf_section_to_tm_pair_eq v).
    apply cwf_section_to_tm_eq.
    use (cwf_subst_pb s).
    - etrans.
      { apply cwf_pair_p. }
      exact (!(cwf_pair_p _ _)).
    - exact p.
  Qed.

  Lemma cwf_pair_tm_eq
    {Γ : C} {A B : cwf_ty Γ} ( e : A = B ) (t : cwf_tm A) :
    ⟨⟨ identity Γ, cwf_subst_tm_id (transportf cwf_tm e t) ⟩⟩
    = ⟨⟨ identity Γ, cwf_subst_tm_id t ⟩⟩ · cwf_tm_eq_to_mor e.
  Proof.
    induction e.
    refine (!_).
    apply id_right.
  Qed.

  Lemma cwf_pB_nat
    {Γ Δ : C} {s : Δ --> Γ} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)} :
    cwf_lift (cwf_lift s A) B · p_ B = p_ (B [[ cwf_lift s A ]]) · cwf_lift s A.
  Proof.
    apply cwf_pair_p.
  Qed.

  Definition cwf_sigma_subst_pi1_sections
    : sigma_subst_pi1 C Sig cwf_sigma_pi1_sections Sig_sub.
  Proof.
    intros Γ Δ s A B p.
    apply (cwf_tm_eq_from_lift_pair_eq s A _ (_ [[ s ]]tm)).
    rewrite <- (cwf_proj_pB_eq).
    rewrite !assoc'.
    rewrite <- cwf_pB_nat.
    unfold cwf_proj_sections.
    rewrite cwf_pair_tm_eq.
    rewrite !assoc'.
    etrans.
    { apply maponpaths.
      rewrite !assoc.
      apply maponpaths_2.
      refine (!_).
      apply cwf_proj_sections_sub. }
    rewrite !assoc.
    rewrite <- (cwf_pair_subst_comm s A (cwf_sigma_pi1_sections Γ A B p)).
    rewrite !assoc'.
    etrans.
    2: {apply maponpaths.
        apply cwf_proj_pB_eq. }
    unfold cwf_proj_sections.
    rewrite !assoc.
    do 2 apply maponpaths_2.
    refine (!_).
    apply cwf_pair_subst_comm.
  Qed.

  Lemma cwf_proj_sections_sub_section
    {Γ Δ : C} (s : Δ --> Γ) {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
    (p : cwf_tm (Sig Γ A B))
    (p' := transportf (λ X, cwf_tm X) (Sig_sub Γ Δ s A B) (p [[ s ]]tm))
    : cwf_proj_sections p' · cwf_lift (cwf_lift s A) B = s · cwf_proj_sections p.
  Proof.
    unfold p'.
    unfold cwf_proj_sections.
    etrans.
    { do 2 apply cancel_postcomposition. apply cwf_pair_tm_eq. }
    rewrite !assoc'.
    etrans.
    { apply cancel_precomposition.
              rewrite assoc. apply (! cwf_proj_sections_sub s A B). }
    rewrite !assoc.
    etrans.
    { apply cancel_postcomposition.
      refine (!_).
      apply cwf_pair_subst_comm. }
    apply idpath.
  Qed.

  Definition cwf_sigma_subst_pi2_sections
    : sigma_subst_pi2 C Sig cwf_sigma_pi1_sections
        cwf_sigma_pi2_sections Sig_sub
        cwf_sigma_subst_pi1_sections.
  Proof.
    intros Γ Δ s A B p.
    unfold cwf_sigma_pi2_sections.
    rewrite cwf_subst_mor_transportf.
    unfold cwf_qA_subst.
    unfold cwf_subst_tm_comp.
    rewrite ! transportf_cwf_subst_tm.
    etrans.
    { do 3 apply maponpaths.
      apply transportf_cwf_subst_tm. }
    rewrite cwf_subst_tm_on_comp'.
    rewrite <- (cwf_subst_tm_eq  _ (cwf_proj_sections_sub_section s p)).
    rewrite cwf_subst_mor_transportf.
    rewrite cwf_subst_tm_on_comp.
    rewrite ! transport_f_f.
    etrans.
    { do 2 apply maponpaths.
      apply cwf_pair_q_subst. }
    unfold cwf_qA_subst.
    rewrite !transportf_cwf_subst_tm.
    rewrite !transport_f_f.
    unfold cwf_sigma_pi2_sections.
    rewrite cwf_subst_mor_transportf.
    unfold cwf_subst_tm_comp.
    etrans.
    { apply maponpaths.
      apply cwf_subst_tm_on_comp. }
    etrans.
    { do 3 apply maponpaths.
      apply transportf_cwf_subst_tm. }
    rewrite transportf_cwf_subst_tm.
    etrans.
    { do 3 apply maponpaths.
      apply cwf_subst_tm_on_comp'. }
    rewrite !transport_f_f.
    apply maponpaths_2.
    apply setproperty.
  Qed.

  Lemma cwf_pi2_sections_pair
    {Γ : C} {A : cwf_ty Γ} {B : cwf_ty (Γ & A)}
    (a : cwf_tm A) (b : cwf_tm (B [[ ⟨⟨ identity Γ, cwf_subst_tm_id a ⟩⟩ ]]))
    : cwf_sigma_pi2_sections Γ A B ( cwf_sigma_pair_sections Γ A B a b)
      = transportf cwf_tm
          (! maponpaths (λ x, B [[ ⟨⟨ identity Γ, cwf_subst_tm_id x ⟩⟩ ]])
             (cwf_sigma_beta1_sections Γ A B a b))
          b.
  Proof.
    refine (!_).
    etrans.
    { apply maponpaths.
      exact (!(cwf_sigma_beta2_sections Γ A B a b)). }
    rewrite transport_f_f.
    use (transportf_set cwf_tm).
    apply setproperty.
  Qed.

  Definition cwf_sigma_subst_pair_sections
    : sigma_subst_pair C Sig  cwf_sigma_pair_sections
        Sig_sub.
  Proof.
    intros Γ Δ s A B a b.
    etrans.
    { refine (!_).
      apply cwf_sigma_eta_sections. }
    use cwf_sigma_proj_pair_eq.
    - rewrite cwf_sigma_subst_pi1_sections.
      apply maponpaths.
      apply cwf_sigma_beta1_sections.
    - unfold cwf_sigma_pi2_sections, cwf_qA_subst , cwf_subst_tm_comp.
      etrans.
      { apply maponpaths.
        refine (!_).
        apply cwf_sigma_subst_pi2_sections. }
      rewrite cwf_pi2_sections_pair.
      rewrite transportf_cwf_subst_tm.
      rewrite (functtransportf
                 (λ x : cwf_tm (A [[s]]), ⟨⟨ identity Δ, cwf_subst_tm_id x ⟩⟩)
                 (λ X, cwf_tm ((B [[ cwf_lift s A ]]) [[ X ]]))
                 _).
      rewrite cwf_subst_mor_transportf.
      rewrite !transport_f_f.
      apply maponpaths_2.
      apply setproperty.
   Qed.

  Definition make_cwf_sigma_with_sections : cwf_sigma_structure C
    := make_cwf_sigma_structure _
         Sig
         cwf_sigma_pi1_sections
         cwf_sigma_pi2_sections
         cwf_sigma_pair_sections
         cwf_sigma_beta1_sections
         cwf_sigma_beta2_sections
         cwf_sigma_eta_sections
         Sig_sub
         cwf_sigma_subst_pi1_sections
         cwf_sigma_subst_pi2_sections
         cwf_sigma_subst_pair_sections.

End cwf_sigma_with_sections.

(** * 2. Π-Type *)

Section cwf_pi_with_sections.

  Context (C : cwf).
  Context (Pi : pi_form C).
  Context (lam : pi_lam C Pi).

  Definition pi_app_sections : UU
                                 :=  ∏ (Γ : C) (A : cwf_ty Γ) (B : cwf_ty (Γ & A)),
              cwf_tm (Pi Γ A B) -> cwf_tm B.

  Context (app : pi_app_sections).

  Definition pi_beta_sections : UU
    := ∏ (Γ : C) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
         (b : cwf_tm B),
      app Γ A B (lam Γ A B b) = b.

  Context (pi_beta : pi_beta_sections).

  Definition pi_eta_sections: UU
                                := ∏ (Γ : C) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
                      (f : cwf_tm (Pi Γ A B)),
              lam Γ A B (app Γ A B f) = f.
  Context (pi_eta : pi_eta_sections).
  Context (Pi_sub : pi_subst C Pi).
  Context (sub_lam : pi_subst_lam C Pi lam Pi_sub).

  Definition cwf_pi_app_sections : pi_app C Pi.
  Proof.
    intros Γ A B f a.
    exact ((app Γ A B f) [[ ⟨⟨ identity Γ , cwf_subst_tm_id a ⟩⟩ ]]tm).
  Defined.

  Definition cwf_pi_beta_sections
    : CatsWithFams.pi_beta _ _ lam cwf_pi_app_sections.
  Proof.
    intros Γ A B b a.
    exact (maponpaths _ (pi_beta Γ A B b)).
  Defined.

  Local Lemma app_sub
    (Γ Δ : C) (s : Δ --> Γ) (A : cwf_ty Γ) (B : cwf_ty (Γ & A))
    (f : cwf_tm (Pi Γ A B))
    : (app Γ A B f) [[ cwf_lift s A ]]tm
      = app Δ (A [[ s ]]) (B [[ cwf_lift s A ]])
          (transportf (λ X, cwf_tm X) (Pi_sub Γ Δ s A B) (f [[ s ]]tm)).
  Proof.
    refine (!_).
    rewrite <- (pi_eta _ _ _ f).
    rewrite sub_lam.
    rewrite transport_f_f.
    rewrite pathsinv0l.
    cbn.
    refine (_ @ pi_beta _ _ _ _).
    do 3 apply maponpaths.
    rewrite pi_eta.
    apply idpath.
  Qed.

  Definition cwf_pi_eta_sections
    : CatsWithFams.pi_eta C Pi lam cwf_pi_app_sections Pi_sub.
  Proof.
    intros Γ A B f.
    etrans.
    2: { apply pi_eta. }
    apply maponpaths.
    unfold pi_uncurry.
    unfold cwf_pi_app_sections.
    rewrite <- (app_sub Γ (Γ & A) (p_ A) A B f).
    rewrite cwf_subst_tm_on_comp'.
    etrans.
    { do 2 apply maponpaths.
      refine (!_).
      refine (cwf_subst_tm_eq' _ (! cwf_lift_p_q _)). }
    etrans.
    { do 3 apply maponpaths.
      apply cwf_subst_tm_on_id. }
    rewrite !transport_f_f.
    apply (transportf_set cwf_tm).
    apply setproperty.
  Defined.

  Definition cwf_pi_subst_app_sections
    : CatsWithFams.pi_subst_app C Pi cwf_pi_app_sections Pi_sub.
  Proof.
    intros Γ Δ s A B f a.
    unfold cwf_pi_app_sections.
    rewrite <- app_sub.
    rewrite cwf_subst_tm_on_comp'.
    etrans.
    { apply maponpaths.
      refine (!_).
      refine (cwf_subst_tm_eq _ (! cwf_pair_subst_comm s _ a)). }
    rewrite cwf_subst_mor_transportf.
    rewrite !transport_f_f.
    etrans.
    2: { apply maponpaths.
         refine (!_).
         apply cwf_subst_tm_on_comp'. }
    rewrite transport_f_f.
    apply maponpaths_2.
    apply setproperty.
  Qed.

  Definition make_cwf_pi_with_sections : cwf_pi_structure C
    := make_cwf_pi_structure C Pi
         lam
         cwf_pi_app_sections
         cwf_pi_beta_sections
         Pi_sub
         cwf_pi_eta_sections
         sub_lam
         cwf_pi_subst_app_sections.

End cwf_pi_with_sections.

Close Scope cwf.
Close Scope cat.
