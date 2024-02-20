
(** * The slice displayed category

- Definition of the slice displayed category
- Proof that a morphism is cartesian if and only if
  it is a pullback

*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.Limits.Pullbacks.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Isos.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Fibrations.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.

Local Open Scope cat.

(** ** The displayed codomain

The total category associated to this displayed category is going to be
isomorphic to the arrow category, but it won't be the same:
the components of the objects and morphisms will be arranged differently

*)

(* TODO: perhaps rename [slice_disp], and make [C] implicit? *)
Section Codomain_Disp.

Context (C : category).

Definition cod_disp_ob_mor : disp_cat_ob_mor C.
Proof.
  exists (λ x : C, ∑ y, y --> x).
  simpl; intros x y xx yy f.
    exact (∑ ff : pr1 xx --> pr1 yy, ff · pr2 yy = pr2 xx · f).
Defined.

Definition cod_id_comp : disp_cat_id_comp _ cod_disp_ob_mor.
Proof.
  split.
  - simpl; intros.
    exists (identity _ ).
    abstract (
        etrans; [apply id_left |];
        apply pathsinv0, id_right ).
  - simpl; intros x y z f g xx yy zz ff gg.
    exists (pr1 ff · pr1 gg).
    abstract (
        apply pathsinv0;
        etrans; [apply assoc |];
        etrans; [apply maponpaths_2, (! (pr2 ff)) |];
        etrans; [eapply pathsinv0, assoc |];
        etrans; [apply maponpaths, (! (pr2 gg))|];
        apply assoc).
Defined.

Definition cod_disp_data : disp_cat_data _
  := (cod_disp_ob_mor ,, cod_id_comp).

Proposition transportf_cod_disp
            {x y : C}
            {xx : cod_disp_data x}
            {yy : cod_disp_data y}
            {f g : x --> y}
            (p : f = g)
            (ff : xx -->[ f] yy)
  : pr1 (transportf
           (mor_disp xx yy)
           p
           ff)
    =
    pr1 ff.
Proof.
  refine (pr1_transportf (A := C⟦_,_⟧) _ _ @ _).
  rewrite transportf_const ; cbn.
  apply idpath.
Qed.

Proposition transportb_cod_disp
            {x y : C}
            {xx : cod_disp_data x}
            {yy : cod_disp_data y}
            {f g : x --> y}
            (p : g = f)
            (ff : xx -->[ f] yy)
  : pr1 (transportb
           (mor_disp xx yy)
           p
           ff)
    =
    pr1 ff.
Proof.
  apply transportf_cod_disp.
Qed.

Proposition eq_cod_mor
            {x y : C}
            {xx : cod_disp_data x}
            {yy : cod_disp_data y}
            {f : x --> y}
            {ff gg : xx -->[ f ] yy}
            (p : pr1 ff = pr1 gg)
  : ff = gg.
Proof.
  use subtypePath.
  {
    intro.
    apply homset_property.
  }
  exact p.
Qed.

Lemma cod_disp_axioms : disp_cat_axioms C cod_disp_data.
Proof.
  repeat apply tpair; intros; try apply homset_property.
  - use eq_cod_mor.
    rewrite transportb_cod_disp.
    cbn.
    apply id_left.
  - use eq_cod_mor.
    rewrite transportb_cod_disp.
    cbn.
    apply id_right.
  - use eq_cod_mor.
    rewrite transportb_cod_disp.
    cbn.
    apply assoc.
  - apply (isofhleveltotal2 2).
    + apply homset_property.
    + intro. apply isasetaprop. apply homset_property.
Qed.

Definition disp_codomain : disp_cat C
  := (cod_disp_data ,, cod_disp_axioms).

End Codomain_Disp.

Section PullbackToCartesian.
  Context {C : category}
          {x₁ x₂ : C}
          {f : x₁ --> x₂}
          {gy₁ : disp_codomain C x₁}
          {hy₂ : disp_codomain C x₂}
          (ff : gy₁ -->[ f ] hy₂)
          (H : isPullback (pr2 ff))
          {w : C}
          (φ : w --> x₁)
          (vψ : disp_codomain C w)
          (kp : vψ -->[ φ · f ] hy₂).

  Let y₁ : C := pr1 gy₁.
  Let y₂ : C := pr1 hy₂.
  Let v : C := pr1 vψ.
  Let g : y₁ --> x₁ := pr2 gy₁.
  Let h : y₂ --> x₂ := pr2 hy₂.
  Let ψ : v --> w := pr2 vψ.
  Let k : v --> y₂ := pr1 kp.
  Let l : y₁ --> y₂ := pr1 ff.

  Let P : Pullback h f := make_Pullback _ H.

  Proposition cartesian_cod_disp_unique
    : isaprop (∑ (gg : vψ -->[ φ] gy₁), (gg ;; ff)%mor_disp = kp).
  Proof.
    use invproofirrelevance.
    intros ζ₁ ζ₂.
    use subtypePath.
    {
      intro.
      apply disp_codomain.
    }
    use eq_cod_mor.
    pose (q₁ := maponpaths pr1 (pr2 ζ₁) @ !(maponpaths pr1 (pr2 ζ₂))).
    pose (pr21 ζ₁ @ !(pr21 ζ₂)) as q₂.
    cbn in q₁, q₂.
    use (MorphismsIntoPullbackEqual H).
    - exact q₁.
    - exact q₂.
  Qed.

  Definition cartesian_cod_disp_map
    : v --> y₁.
  Proof.
    refine (PullbackArrow P v k (ψ · φ) _).
    abstract
      (refine (pr2 kp @ _) ;
       apply assoc).
  Defined.

  Proposition cartesian_cod_disp_comm_pr1
    : cartesian_cod_disp_map · l = k.
  Proof.
    apply (PullbackArrow_PullbackPr1 P).
  Qed.

  Proposition cartesian_cod_disp_comm_pr2
    : cartesian_cod_disp_map · g = ψ · φ.
  Proof.
    apply (PullbackArrow_PullbackPr2 P).
  Qed.
End PullbackToCartesian.

Section Pullbacks_Cartesian.

Context {C:category}.

Definition isPullback_cartesian_in_cod_disp
           {x₁ x₂ : C }
           {f : x₁ --> x₂}
           {gy₁ : disp_codomain _ x₁}
           {hy₂ : disp_codomain _ x₂}
           (ff : gy₁ -->[ f ] hy₂)
           (H : isPullback (pr2 ff))
  : is_cartesian ff.
Proof.
  intros w φ vψ kp.
  use iscontraprop1.
  - exact (cartesian_cod_disp_unique ff H φ vψ kp).
  - simple refine ((_ ,, _) ,, _).
    + exact (cartesian_cod_disp_map ff H φ vψ kp).
    + exact (cartesian_cod_disp_comm_pr2 ff H φ vψ kp).
    + use subtypePath ; [ intro ; apply homset_property | ].
      exact (cartesian_cod_disp_comm_pr1 ff H φ vψ kp).
Defined.

Definition cartesian_isPullback_in_cod_disp
    { Γ Γ' : C } {f : Γ' --> Γ}
    {p : disp_codomain _ Γ} {p' : disp_codomain _ Γ'} (ff : p' -->[f] p)
  : (isPullback (pr2 ff)) <- is_cartesian ff.
Proof.
  intros cf c h k H.
  destruct p as [a x].
  destruct p' as [b y].
  destruct ff as [H1 H2].
  unfold is_cartesian in cf.
  simpl in *.
  eapply iscontrweqf.
  2: {
    use cf.
    + exact Γ'.
    + exact (identity _ ).
    + exists c. exact k.
    + cbn. exists h.
      etrans. apply H. apply maponpaths. apply (! id_left _ ).
  }
  eapply weqcomp.
  apply weqtotal2asstor.
  apply weq_subtypes_iff.

  - intro. apply (isofhleveltotal2 1).
    + apply homset_property.
    + intros.
      match goal with |[|- isofhlevel 1 (?x = _ )] =>
                       set (X := x) end.
      set (XR := @homsets_disp _ (disp_codomain C )).
      specialize (XR _ _ _ _ _ X).
      apply XR.
  - cbn. intro. apply isapropdirprod; apply homset_property.
  - intros gg; split; intros HRR.
    + split.
      * exact (maponpaths pr1 (pr2 HRR)).
      * etrans. apply (pr1 HRR). apply id_right.
    + use tpair.
      * rewrite id_right.
        exact (pr2 HRR).
      * apply subtypePath.
        intro; apply homset_property.
      exact (pr1 HRR).
Qed.


Definition cartesian_iff_isPullback
    { Γ Γ' : C } {f : Γ' --> Γ}
    {p : disp_codomain _ Γ} {p' : disp_codomain _ Γ'} (ff : p' -->[f] p)
  : (isPullback (pr2 ff)) <-> is_cartesian ff.
Proof.
  split.
  - apply isPullback_cartesian_in_cod_disp.
  - apply cartesian_isPullback_in_cod_disp.
Defined.

End Pullbacks_Cartesian.

(** * Cleaving for codomain *)
Definition disp_codomain_cleaving
           {C : category}
           (H : Pullbacks C)
  : cleaving (disp_codomain C).
Proof.
  intros x₁ x₂ f yg.
  pose (y := pr1 yg).
  pose (g := pr2 yg).
  pose (P := H _ _ _ g f).
  simple refine (_ ,, (_ ,, _) ,, _).
  - exact (PullbackObject P ,, PullbackPr2 P).
  - exact (PullbackPr1 P).
  - exact (PullbackSqrCommutes P).
  - use isPullback_cartesian_in_cod_disp.
    apply P.
Defined.

(** * Displayed functor between codomain displayed categories *)
Definition disp_codomain_functor_data
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : disp_functor_data F (disp_codomain C₁) (disp_codomain C₂).
Proof.
  simple refine (_ ,, _).
  - exact (λ x yf, F (pr1 yf) ,, #F (pr2 yf)).
  - refine (λ x₁ x₂ yf₁ yf₂ g hp, #F (pr1 hp) ,, _).
    abstract
      (cbn ;
       rewrite <- !functor_comp ;
       apply maponpaths ;
       exact (pr2 hp)).
Defined.

Proposition disp_codomain_functor_axioms
            {C₁ C₂ : category}
            (F : C₁ ⟶ C₂)
  : disp_functor_axioms (disp_codomain_functor_data F).
Proof.
  split.
  - intros x yf.
    use eq_cod_mor.
    rewrite transportb_cod_disp.
    cbn.
    rewrite functor_id.
    apply idpath.
  - intros x₁ x₂ y₃ yf₁ yf₂ yf₃ f₁ f₂ gp₁ gp₂.
    use eq_cod_mor.
    rewrite transportb_cod_disp.
    cbn.
    rewrite functor_comp.
    apply idpath.
Qed.

Definition disp_codomain_functor
           {C₁ C₂ : category}
           (F : C₁ ⟶ C₂)
  : disp_functor F (disp_codomain C₁) (disp_codomain C₂).
Proof.
  simple refine (_ ,, _).
  - exact (disp_codomain_functor_data F).
  - exact (disp_codomain_functor_axioms F).
Defined.

(** * Isos in the codomain *)
Section IsosCodomain.
  Context {C : category}
          {x : C}
          (fy gz : disp_codomain C x).

  Let y : C := pr1 fy.
  Let f : y --> x := pr2 fy.
  Let z : C := pr1 gz.
  Let g : z --> x := pr2 gz.

  Definition iso_to_disp_iso
             (h : z_iso y z)
             (p : f = h · g)
    : z_iso_disp (identity_z_iso x) fy gz.
  Proof.
    use make_z_iso_disp.
    - refine (pr1 h ,, _).
      abstract
        (cbn ;
         rewrite id_right ;
         exact (!p)).
    - simple refine (_ ,, _ ,, _).
      + refine (inv_from_z_iso h ,, _).
        abstract
          (cbn ;
           rewrite id_right ;
           use z_iso_inv_on_right ;
           exact p).
      + abstract
          (use eq_cod_mor ;
           rewrite transportb_cod_disp ;
           apply z_iso_after_z_iso_inv).
      + abstract
          (use eq_cod_mor ;
           rewrite transportb_cod_disp ;
           apply z_iso_inv_after_z_iso).
  Defined.

  Definition disp_iso_to_iso
             (ff : z_iso_disp (identity_z_iso x) fy gz)
    : ∑ (h : z_iso y z), f = h · g.
  Proof.
    simple refine (_ ,, _).
    - use make_z_iso.
      + exact (pr11 ff).
      + exact (pr1 (inv_mor_disp_from_z_iso ff)).
      + split.
        * abstract
            (refine (maponpaths pr1 (inv_mor_after_z_iso_disp ff) @ _) ;
             rewrite transportb_cod_disp ;
             apply idpath).
        * abstract
            (refine (maponpaths pr1 (z_iso_disp_after_inv_mor ff) @ _) ;
             rewrite transportb_cod_disp ;
             apply idpath).
    - abstract
        (refine (!(pr21 ff @ _)) ;
         apply id_right).
  Defined.

  Definition disp_iso_weq_iso
    : (∑ (h : z_iso y z), f = h · g)
      ≃
      z_iso_disp (identity_z_iso x) fy gz.
  Proof.
    use weq_iso.
    - exact (λ h, iso_to_disp_iso (pr1 h) (pr2 h)).
    - exact disp_iso_to_iso.
    - abstract
        (intro ff ;
         use subtypePath ; [ intro ; apply homset_property | ] ;
         use z_iso_eq ; cbn ;
         apply idpath).
    - abstract
        (intro ff ;
         use subtypePath ; [ intro ; apply isaprop_is_z_iso_disp | ] ;
         use eq_cod_mor ;
         cbn ;
         apply idpath).
  Defined.
End IsosCodomain.

Definition is_z_iso_disp_codomain
           {C : category}
           {x : C}
           {fy gz : disp_codomain C x}
           (φp : fy -->[ identity x ] gz)
           (H : is_z_isomorphism (pr1 φp))
  : is_z_iso_disp (identity_z_iso x) φp.
Proof.
  pose (h := (_ ,, H) : z_iso _ _).
  simple refine (_ ,, _ ,, _).
  - refine (inv_from_z_iso h ,, _).
    abstract
      (cbn ;
       use z_iso_inv_on_right ;
       rewrite id_right ;
       refine (_ @ !(pr2 φp)) ;
       rewrite id_right ;
       apply idpath).
  - abstract
      (use eq_cod_mor ;
       rewrite transportb_cod_disp ;
       apply z_iso_after_z_iso_inv).
  - abstract
      (use eq_cod_mor ;
       rewrite transportb_cod_disp ;
       apply (z_iso_inv_after_z_iso h)).
Defined.

Definition z_iso_disp_codomain
           {C : category}
           {x y : C}
           {f : z_iso x y}
           {h₁ : disp_codomain C x}
           {h₂ : disp_codomain C y}
           (g : z_iso (pr1 h₁) (pr1 h₂))
           (p : g · pr2 h₂ = pr2 h₁ · f)
  : z_iso_disp f h₁ h₂.
Proof.
  use make_z_iso_disp.
  - exact (pr1 g ,, p).
  - simple refine (_ ,, _ ,, _).
    + refine (inv_from_z_iso g ,, _).
      abstract
        (use z_iso_inv_on_right ;
         rewrite !assoc ;
         use z_iso_inv_on_left ;
         exact p).
    + abstract
        (use eq_cod_mor ;
         rewrite transportb_cod_disp ;
         cbn ;
         apply z_iso_after_z_iso_inv).
    + abstract
        (use eq_cod_mor ;
         rewrite transportb_cod_disp ;
         cbn ;
         apply z_iso_inv_after_z_iso).
Defined.

Definition from_z_iso_disp_codomain
           {C : category}
           {x y : C}
           {f : z_iso x y}
           {h₁ : disp_codomain C x}
           {h₂ : disp_codomain C y}
           (ff : z_iso_disp f h₁ h₂)
  : z_iso (pr1 h₁) (pr1 h₂).
Proof.
  use make_z_iso.
  - exact (pr11 ff).
  - exact (pr112 ff).
  - split.
    + abstract
        (refine (maponpaths pr1 (pr222 ff) @ _) ;
         rewrite transportb_cod_disp ;
         apply idpath).
    + abstract
        (refine (maponpaths pr1 (pr122 ff) @ _) ;
         rewrite transportb_cod_disp ;
         apply idpath).
Defined.

(** * The univalence *)
Section UnivalenceCodomain.
  Context (C : univalent_category).

  Proposition disp_univalent_disp_codomain
    : is_univalent_disp (disp_codomain C).
  Proof.
    use is_univalent_disp_from_fibers.
    intros x fy gz.
    use weqhomot.
    - refine (disp_iso_weq_iso _ _
              ∘ weqtotal2 (make_weq _ (univalent_category_is_univalent C _ _)) _
              ∘ total2_paths_equiv _ _ _)%weq.
      abstract
        (induction fy as [ y f ] ;
         induction gz as [ z g ] ;
         cbn ;
         intro p ;
         induction p ; cbn ;
         rewrite id_left ;
         exact (idweq _)).
    - intro p.
      induction p.
      use subtypePath.
      {
        intro.
        apply isaprop_is_z_iso_disp.
      }
      use eq_cod_mor.
      cbn.
      apply idpath.
  Qed.
End UnivalenceCodomain.
