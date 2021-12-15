Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctors.
Require Import UniMath.CategoryTheory.SimplicialSets.

(* This file defines: the augmented simplex category Δ or Δ_sd, in several different ways
    * as a precategory, [precat_Delta]
    * as a category, [category_Delta] := ([precat_Delta],, [Delta_has_homsets])
    * as a monoidal category, [AugmentedSimplexCategory] with tensor product [tensor_functor_ord] given by ordinal addition and unit [tensor_unit] the zero ordinal
    * as a strict monoidal category, [FinOrdStrict]

 Similarly, it defines the category of finite cardinals, [FinCard] or Δ_sdg,
    * as a precategory, [precat_fincard]
    * as a category, [category_fincard] := ([precat_fincard],, [fincard_has_homsets])
    * as a monoidal category, [FinCard] with tensor product [tensor_product_card] given by ordinal addition and unit [tensor_unit] the zero ordinal
    * as a strict monoidal category [FinCardStrict]

and the obvious forgetful functor between them,
    * as a functor [fget_monoton_functor]
    * as a lax monoidal functor [U_Mon_Lax]
    * as a strong monoidal functor [U_Mon_Strong]

  In addition the file contains some helper lemmas -

  - [iscontr_inequal],  (n > m) ⨿ (n ≤ m) is contractible for n, m : nat
  - [iscontr_inequal'], (n < m) ⨿ (n ≥ m) is contractible for n, m : nat
  - [natlthorgeh_left_branch] and [natlthorgeh_right_branch] which allow you to pursue the left branch or the right branch of the preceding proposition if you know which is true
  - [fincard_hom_extensionality], maps between finite cardinals agree iff they agree pointwise
  - [morphism_extensionality] same but for maps between finite ordinals
  - [U_Faithful], which says that the forgetful functor U is faithful
  - [mon_iso_mon_inv] - if f : n --> m  in Δ_sd and U(f) is an isomorphism, then U(f)^{-1} is monotonic
  - [U_reflects_isos] - if f : n--> m in Δ_sd and U(f) is an isomorphism, then so is f
  - computational lemmas and rules about the behavior of ordinal addition on morphisms, see for example [pr_n_m_l] and [proj_incl_r]
*)


Definition fincard_has_homsets (n m : nat) : isaset ((⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) :=
  (Propositions.funspace_isaset (isasetstn m)).

Proposition iscontr_inequal (n m : nat) : iscontr ((n > m) ⨿ (n ≤ m)).
Proof.
  unfold iscontr.
  exists (natgthorleh n m). intro t.
  induction t.
  - unfold natgthorleh.
    induction (isdecrelnatgth n m).
    + simpl. apply maponpaths. apply (pr2 (n > m)).
    + contradiction.
  - unfold natgthorleh.
    induction (isdecrelnatgth n m).
    + simpl. assert (¬ (n > m)). { apply natlehtonegnatgth. assumption. } contradiction.
    + simpl. apply maponpaths. apply (pr2 (n ≤ m)).
Defined.

Local Proposition iscontr_inequal' (n m : nat) : iscontr ((n < m) ⨿ (n ≥ m)).
Proof.
  change (n < m) with (m > n).
  change (n ≥ m) with (m ≤ n).
  exact (iscontr_inequal m n).
Defined.

Local Proposition fincard_hom_extensionality { n m : nat } { f g : (⟦ n ⟧)%stn → (⟦ m ⟧)%stn } : (∏ x  : (⟦ n ⟧)%stn, (pr1 (f x)= pr1 (g x))) -> f=g.
Proof.
  intro X. apply funextfun.
  intro x. apply subtypeInjectivity_prop.
  exact (X x).
Qed.

Definition ordconstr {n : nat} (k : nat) (bd : k < n) : stn n := k,,bd.

Definition precat_Delta_precategory_data : precategory_data.
(* This definition does differ from the one in CategoryTheory.SimplicialSets. The objects of that category are
 \[0\] = {0}
 \[1\] = {0,1}
 \[2\] = {0, 1, 2}
  and so on. I call this the "topologists' indexing" as calling the ordinal [2] reflects that it is 2-dimensional.
  The objects of the category in this file are
  0 = \emptyset
  1 = {0}
  2 = {0,1}
  and so on, as in the definition of the von Neumann ordinals. The category in CategoryTheory.SimplicialSets does not have the unit object which is necessary for the proposed addition functor. The reindexing / renaming of the objects allows us to define the addition bifunctor sensibly, so that n + m has the obvious meaning; in the category in CategoryTheory.SimplicialSets we have the unfortunate fact that [n] \oplus [m] = [n+m+1]. *)
Proof.
  use make_precategory_data.
  - exact (make_precategory_ob_mor nat monfunstn).
  - intros m. apply monfunstnid. (* defining identity and composition law *)
  -  intros l m n f g. exact (monfunstncomp f g).
Defined.

Definition precat_Delta_is_precategory : is_precategory precat_Delta_precategory_data.
Proof.
  unfold precat_Delta_precategory_data.
  unfold is_precategory. split. {
    split.
    - intros a b f. unfold "id". simpl in *. reflexivity.
    - intros a b f. unfold "id". simpl in *. reflexivity.
  }  {
    split.
    - reflexivity.
    - reflexivity.
  }
Qed.

Definition precat_Delta : precategory :=
  (precat_Delta_precategory_data,, precat_Delta_is_precategory).

Notation "C ⊠ D" := (precategory_binproduct C D) (at level 38).

Definition precat_fincard_data : precategory_data.
Proof.
  unshelve eapply (make_precategory_data _).
  - unshelve eapply (make_precategory_ob_mor _ _).
    * exact nat.
    * exact (λ n, λ m, (⟦n⟧%stn → ⟦m⟧%stn)). (* Morphisms *)
  - intro c. exact (idfun (⟦c⟧)%stn).        (* Identity *)
  - intros n m k f g. exact (g∘f).  (* Composition law *)
Defined.

Proposition precat_fincard_is_precategory : is_precategory precat_fincard_data.
Proof.
  unfold precat_Delta_precategory_data.
  unfold is_precategory. split. {
    split.
    - intros a b f. unfold "id". simpl in *. reflexivity.
    - intros a b f. unfold "id". simpl in *. reflexivity.
  }  {
    split.
    - reflexivity.
    - reflexivity.
  }
Qed.

Definition precat_fincard : precategory := (precat_fincard_data,, precat_fincard_is_precategory).

Proposition Delta_has_homsets : has_homsets precat_Delta.
Proof.
  unfold has_homsets. simpl. intros a b.
  apply isaset_total2.
  - exact (fincard_has_homsets a b).
  - intro f. apply impred_isaset. intro x. apply impred_isaset. intro y. apply impred_isaset.
    intro. exact (isasetaprop (propproperty (f x ≤ f y))).
Qed.

Definition category_Delta : category := (precat_Delta,, Delta_has_homsets).
Definition category_fincard : category := (precat_fincard,, fincard_has_homsets).

(* The notational convention here is that a subscript d means "has face maps"
   subscript s means "has degeneracies" and subscript g means "has permutations." *)

Notation Δ_sdg := category_fincard.
Notation Δ := category_Delta.
Notation Δ_sd := category_Delta.

Definition Δ_ob_constr ( n : nat) : Δ := n.
Definition Δ_sdg_ob_constr ( n : nat) : Δ_sdg := n.

Open Scope cat.

Definition Δ_mor_constr { n m : nat } ( f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn )
           ( pk : ∏ x y : (⟦ n ⟧)%stn, x ≤ y -> f x ≤ f y) : (Δ_ob_constr n) --> (Δ_ob_constr m)
:= (make_monfunstn f pk).

Definition Δ_sdg_mor_constr { n m : nat } ( f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn ) :
  Δ_sdg_ob_constr n -->   Δ_sdg_ob_constr m := f.

Definition fget_monoton_functor_data : functor_data category_Delta category_fincard.
Proof.
    use tpair. { exact (idfun nat). }
    intros a b f. exact (pr1 f).
Defined.

Proposition fget_monoton_is_functor : is_functor fget_monoton_functor_data.
Proof.
  use tpair.
  - unfold functor_idax. reflexivity.
  - unfold functor_compax. reflexivity.
Qed.

Definition fget_monoton_functor : functor category_Delta category_fincard :=
  (fget_monoton_functor_data,, fget_monoton_is_functor).

Local Notation U := fget_monoton_functor.

Local Proposition U_faithful { a b : Δ } (f g : a --> b) : (# U f = # U g) -> f = g.
Proof.
  apply subtypeInjectivity. unfold isPredicate.
  intro. apply impred_isaprop.
  intro. apply impred_isaprop.
  intro. apply impred_isaprop.
  intro. apply propproperty.
Qed.

Local Proposition morphism_extensionality { a b : Δ } (f g : a --> b) :
  (∏ x, (# U f) x  = (# U g) x) -> f = g.
Proof.
  intro ext_hypothesis.
  simpl in ext_hypothesis. apply U_faithful. simpl.
  apply fincard_hom_extensionality. intro x. apply maponpaths. exact (ext_hypothesis x).
Qed.

(* If f : n -> m is monotonic and has an inverse in fin_card, its inverse is also monotonic.*)
Lemma mon_iso_mon_inv {n m : Δ} {f : n --> m} (I : is_z_isomorphism ((# U) f)) :
  ∏ x y : (⟦m⟧)%stn, x ≤ y -> (is_z_isomorphism_mor I) x ≤ (is_z_isomorphism_mor I) y.
Proof.
  intros x y l.
  unfold is_z_isomorphism in I. simpl in I.
  induction I as [I_fn I_is_inverse_in_preord], f as [f_fn f_guarantee].
  induction (natlehchoice x y l) as [a | a'].
  - induction (natgthorleh (I_fn x) (I_fn y)).
    + (* We will derive a contradiction by proving x ≥ y in contradiction to a *)
      contradiction (natlthtonegnatgeh x y a).
      assert (∏ z , f_fn (I_fn z) = z) as X. {
        intro z. change (f_fn (I_fn z)) with (compose (C:=Δ_sdg) I_fn f_fn z).
        simpl. set (j := (pr2 I_is_inverse_in_preord)). simpl in j.
        rewrite j. reflexivity.
        }
      rewrite <- (X x), <- (X y); apply f_guarantee. exact (natlthtoleh _ _ a0).
    + exact b.
  - simpl is_z_isomorphism_mor. apply subtypeInjectivity_prop in a'.
    induction a'. exact (isreflnatleh (I_fn x)).
Qed.

Lemma fincard_inv_is_inverse_in_precat (n m : Δ) (f : n --> m ) (I : is_z_isomorphism ((# U) f)):
is_inverse_in_precat f (is_z_isomorphism_mor I,, mon_iso_mon_inv I).
Proof.
  unfold is_z_isomorphism in I. simpl in I.
  induction I as [g is_inverse], f as [ffun fguarantee].
  simpl in is_inverse. induction is_inverse as [l r].
  split.
  - apply morphism_extensionality. simpl. intro x.
    change ((@compose precat_fincard _ _ _ ffun g) x = x). simpl. rewrite l. reflexivity.
  - apply morphism_extensionality. intro x. simpl.
    change (ffun (g x)) with (compose (C:=Δ_sdg) g ffun x).
    simpl. rewrite r. unfold "id". reflexivity.
Qed.

Lemma U_reflects_isos (n m : Δ) ( f : n --> m ) : (is_z_isomorphism ((# U) f)) -> (is_z_isomorphism f).
Proof.
  intro I.
  use tpair. { exact (is_z_isomorphism_mor I,, mon_iso_mon_inv I). }
  cbv beta.
  exact (fincard_inv_is_inverse_in_precat n m f I).
Defined.

Local Proposition U_reflects_id (a : Δ) (f : a --> a) :
    (# U f) = id (U a) -> f = id a.
Proof.
  intro. apply U_faithful. assumption.
Qed.

Local Definition ordinal_addition : (Δ ⊠ Δ) → Δ.
Proof.
  simpl.
  intro nm. induction nm as [n m]. exact (n+m).
Defined.
Arguments ordinal_addition /.

Local Definition pr_n_m_l { n m : nat} ( x : (⟦ n + m⟧)%stn ) (s : x < n) : (⟦ n ⟧)%stn.
Proof.
  exists (stntonat _ x).
  exact s.
Defined.

Local Definition pr_n_m_r { n m : nat} ( x : (⟦ n + m⟧)%stn ) (s : x ≥ n) : (⟦ m ⟧)%stn.
Proof.
  exists (stntonat _ x - n).
  apply nat_split.
  - exact (stnlt x).
  - exact s.
Defined.

Local Definition sumfn {n n' m m' : nat} (f : (⟦ n ⟧)%stn → (⟦ m ⟧)%stn) ( g : (⟦ n' ⟧)%stn → (⟦ m' ⟧)%stn) : (⟦ n + n' ⟧)%stn → (⟦ m + m'⟧)%stn.
Proof.
  intro x.
  induction (natlthorgeh x n) as [less_n | geq_n].
  - set (x' := pr_n_m_l x less_n).
    refine (ordconstr (n:=m+m') (stntonat _ (f x')) _).
    apply (natgehgthtrans _ m _).
    + exact (natlehnplusnm m m').
    + exact (stnlt (f x')).
  - set (x' := pr_n_m_r x geq_n).
    refine (ordconstr (stntonat _ (g x')+m) _).
    rewrite natpluscomm. apply natlthandplusl. exact (stnlt (g x')).
Defined.

Local Proposition pr_n_m_l_compute { n m : nat}
      ( x : (⟦ n + m⟧)%stn ) (s : x < n) : stntonat _ (pr_n_m_l x s) = stntonat _ x.
Proof.
  reflexivity.
Qed.

Local Proposition pr_n_m_r_compute { n m : nat}
      ( x : (⟦ n + m⟧)%stn ) (s : x ≥ n) : stntonat _ (pr_n_m_r x s) = (stntonat _ x) - n.
Proof.
  reflexivity.
Qed.

Local Proposition proj_incl_l { n m : nat } ( x : (⟦ n + m⟧)%stn ) (s :  x < n) :
  (stn_left n m) (pr_n_m_l x s) = x.
Proof.
  unfold stn_left. simpl.
  apply subtypeInjectivity_prop.
  reflexivity.
Qed.

Local Proposition proj_incl_r { n m : nat } ( x : (⟦ n + m⟧)%stn ) (s : x ≥ n) :
  (stn_right n m) (pr_n_m_r x s) = x.
Proof.
  unfold stn_right. simpl.
  apply subtypeInjectivity_prop.
  simpl.
  rewrite natpluscomm. exact (minusplusnmm x n s).
Qed.

Definition natlthorgeh_left_branch {n m : nat} (s : n < m) (j : (n < m) ⨿ (n ≥ m)) : j = inl s
  := (proofirrelevancecontr (iscontr_inequal m n) j (inl s)).
Definition natlthorgeh_right_branch {n m : nat} (s : n ≥ m) (j : (n < m) ⨿ (n ≥ m)) : j = inr s
  := (proofirrelevancecontr (iscontr_inequal m n) j (inr s)).

Local Proposition sumfn_l { n n' m m' : nat}
      (f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) ( g : (⟦ n' ⟧)%stn -> (⟦ m' ⟧)%stn)
      (x : (⟦ n + n' ⟧)%stn) ( s : x < n) : (sumfn f g) x < m.
Proof.
  unfold sumfn.
  rewrite (natlthorgeh_left_branch s _).
  simpl.
  exact (stnlt (f (pr_n_m_l x s))).
Qed.

Local Proposition sumfn_r { n n' m m' : nat }
      (f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) (g : (⟦ n' ⟧)%stn -> (⟦ m' ⟧)%stn)
      (x : (⟦ n + n' ⟧)%stn) ( s : x ≥ n) : (sumfn f g) x ≥ m.
Proof.
  unfold sumfn. rewrite (natlthorgeh_right_branch s _).
  simpl. change (g (pr_n_m_r x s) + m ≥ m). exact (natlehmplusnm _ m).
Qed.

Local Proposition sumfn_l1 { n n' m m' : nat}
      (f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) ( g : (⟦ n' ⟧)%stn -> (⟦ m' ⟧)%stn)
      (x : (⟦ n + n' ⟧)%stn) ( s : x < n) :
  f (pr_n_m_l x s) = pr_n_m_l ((sumfn f g) x) (sumfn_l f g x s).
Proof.
  apply subtypeInjectivity_prop.
  simpl. unfold sumfn. rewrite (natlthorgeh_left_branch s _).
  simpl. reflexivity.
Qed.

Local Proposition sumfn_r1 { n n' m m' : nat}
      (f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) (g : (⟦ n' ⟧)%stn -> (⟦ m' ⟧)%stn)
      (x : (⟦ n + n' ⟧)%stn) ( s :x ≥ n) :
  g (pr_n_m_r x s) = pr_n_m_r ((sumfn f g) x) (sumfn_r f g x s).
Proof.
  apply subtypeInjectivity_prop.
  simpl. unfold sumfn. rewrite (natlthorgeh_right_branch s _).
  simpl. rewrite ( plusminusnmm _ m). reflexivity.
Qed.

Local Proposition sumfn_l2 { n n' m m' : nat}
      (f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) ( g : (⟦ n' ⟧)%stn -> (⟦ m' ⟧)%stn)
      (x : (⟦ n + n' ⟧)%stn) ( s : x < n) :
  (stn_left m m') (f (pr_n_m_l x s)) = (sumfn f g) x.
Proof.
  rewrite (sumfn_l1 f g x s). exact (proj_incl_l (sumfn f g x) (sumfn_l f g x s)).
Qed.

Local Proposition sumfn_r2 { n n' m m' : nat}
      (f : (⟦ n ⟧)%stn -> (⟦ m ⟧)%stn) ( g : (⟦ n' ⟧)%stn -> (⟦ m' ⟧)%stn)
      (x : (⟦ n + n' ⟧)%stn) ( s : x ≥ n) :
  (stn_right m m') (g (pr_n_m_r x s)) = (sumfn f g) x.
Proof.
  rewrite (sumfn_r1 f g x s). exact (proj_incl_r (sumfn f g x) (sumfn_r f g x s)).
Qed.

Local Proposition stn_left_monotonic ( n m : nat ) :
  ∏ x y : (⟦ n ⟧)%stn, (x ≤ y) -> ( stn_left n m x ) ≤ ( stn_left n m y).
Proof.
  intros x y l.
  exact l.
Qed.

Local Proposition stn_right_monotonic ( n m : nat ) :
  ∏ x y : (⟦ m ⟧)%stn, (x ≤ y) -> ( stn_right n m x ) ≤ ( stn_right n m y).
Proof.
  intros x y l. simpl.
  change (n + x ≤ n + y).
  rewrite natpluscomm. rewrite (natpluscomm n y). apply natlehandplusr.
  exact l.
Qed.

Definition monfunmonprop { n m : nat } (f : monfunstn n m) := pr2 f.

Local Arguments precategory_binproduct_mor /.

Local Definition ordinal_hom :
  ∏ a b : ob (Δ ⊠ Δ), a --> b -> (ordinal_addition a) --> (ordinal_addition b).
Proof.
  simpl. intros nn' mm'. induction nn' as [n n'], mm' as [m m'].
  intro fg. simpl in fg. induction fg as [f g].
  unshelve refine (make_monfunstn _ _).
  - exact (sumfn f g).
  - intros x y.
    induction f as [f_fun f_guarantee]. induction g as [g_fun g_guarantee].
    intro l. simpl. change (sumfn f_fun g_fun x ≤ sumfn f_fun g_fun y).
    unfold sumfn.
    induction natlthorgeh as [xl | xgth], (natlthorgeh y n) as [yl | ygth].
    + simpl. exact (f_guarantee (pr_n_m_l x xl) (pr_n_m_l y yl) l).
    + simpl. apply natlthtoleh. apply (natgehgthtrans _ m _ ).
      * exact (natlehmplusnm _ m).
      * exact (stnlt (f_fun _)).
    + contradiction (natgthnegleh yl). exact (istransnatleh xgth l).
    + simpl. change (g_fun (pr_n_m_r x xgth) + m ≤ g_fun (pr_n_m_r y ygth) +m ).
      apply natlehandplusr. apply g_guarantee. rewrite pr_n_m_r_compute.
      rewrite pr_n_m_r_compute. exact (natgehandminusr _ _ n l).
Defined.

Local Definition tensor_data_card : (functor_data (Δ_sdg ⊠ Δ_sdg) Δ_sdg).
Proof.
  use functor_data_constr.
  + exact ordinal_addition.
  + intros a b pr. induction pr as [f g]. exact (sumfn f g).
Defined.

Local Definition tensor_data_ord : (functor_data (Δ ⊠ Δ)  Δ).
Proof. use functor_data_constr.
       + exact ordinal_addition.
       + exact ordinal_hom.
Defined.

Local Proposition tensor_id_card : (functor_idax tensor_data_card).
Proof.
  intro a. induction a as [n m]. simpl. unfold sumfn. apply fincard_hom_extensionality.
  intro x.
  induction natlthorgeh.
  - simpl. unfold "id". reflexivity.
  - simpl. unfold "id". simpl. exact (minusplusnmm x n b).
Qed.

Local Proposition tensor_id_ord : (functor_idax tensor_data_ord).
Proof.
  intro a.
  apply U_reflects_id. unfold tensor_data_ord.
  apply (tensor_id_card).
Qed.

Local Proposition tensor_comp_card : (functor_compax tensor_data_card).
Proof.
  unfold functor_compax. unfold tensor_data_card. simpl.
  intros a b c f g.
  induction a as [a0 a1], b as [b0 b1], c as [c0 c1].
  simpl in f, g. induction f as [f0 f1], g as [g0 g1].

  apply fincard_hom_extensionality. simpl. intro x.
  unfold "·". simpl. unfold sumfn.

  induction natlthorgeh.
  - rewrite (natlthorgeh_left_branch (stnlt (f0 (ordconstr x a) )) _). simpl in *.
    apply maponpaths. apply maponpaths.
    apply subtypeInjectivity_prop.
                              reflexivity.
  - rewrite (natlthorgeh_right_branch (natgehplusnmm _ b0) _). simpl in *.
    apply (maponpaths (λ k : nat, k+c0)). apply maponpaths. apply maponpaths.
    apply subtypeInjectivity_prop.
                              simpl. exact (pathsinv0 (plusminusnmm _ b0)).
Qed.

Local Proposition tensor_comp_ord : (functor_compax tensor_data_ord).
Proof.
  unfold functor_compax, tensor_data_ord. intros a b c f g.
  induction f as [f0 f1], g as [g0 g1].
  set (Uf := make_dirprod (# U f0) (# U f1)).
  set (Ug := make_dirprod (# U g0) (# U g1)).
  apply U_faithful. exact (tensor_comp_card a b c Uf Ug).
Qed.

Local Proposition tensor_card_is_functor : is_functor tensor_data_card.
Proof.
  split.
  exact tensor_id_card.
  exact tensor_comp_card.
Qed.

Local Proposition tensor_ord_is_functor : is_functor tensor_data_ord.
Proof.
  split.
  exact tensor_id_ord.
  exact tensor_comp_ord.
Qed.

Local Definition tensor_functor_card : functor (Δ_sdg ⊠ Δ_sdg) Δ_sdg.
Proof. use make_functor.
       + exact tensor_data_card.
       + exact tensor_card_is_functor.
Defined.

Local Definition tensor_functor_ord : functor (Δ ⊠ Δ) Δ.
Proof. use make_functor.
       + exact tensor_data_ord.
       + exact tensor_ord_is_functor.
Defined.

Local Definition tensor_unit : Δ :=0.
Arguments tensor_unit /.

Local Definition tensor_left_unitor_card : left_unitor tensor_functor_card tensor_unit.
Proof.
  unfold left_unitor, I_pretensor, functor_fix_fst_arg,functor_identity,nat_z_iso.
  (* We construct the natural transformation. *)
  use tpair.
  - unfold "⟹". use tpair.
    + unfold nat_trans_data. intro x. exact (id x).
    + abstract (cbv beta;
      unfold is_nat_trans; intros n m f;
      apply fincard_hom_extensionality;
      simpl; unfold functor_fix_fst_arg_ob, tensor_functor_card;
      simpl; intro x;
      simpl; rewrite natplusr0; apply maponpaths, maponpaths, subtypeInjectivity_prop; simpl;
      exact (natminuseqn x)).
  - cbv beta.                     (* We prove that it's an isomorphism. *)
    unfold is_nat_z_iso, is_z_isomorphism, is_inverse_in_precat.
    intro c. exists (id c).
    abstract ( split; unfold tensor_functor_card, functor_fix_fst_arg_ob, tensor_data_card;
      simpl; exact (id_left (id c)); exact (id_left (id c))).
Defined.

Local Definition tensor_left_unitor_ord : left_unitor tensor_functor_ord tensor_unit.
Proof.
  unfold left_unitor, I_pretensor, functor_fix_fst_arg,functor_identity,nat_z_iso.
  (* We construct the natural transformation. *)
  use tpair.
  - unfold "⟹". use tpair.
    + unfold nat_trans_data. intro n. exact (id n).
    + abstract (cbv beta;
      unfold is_nat_trans; intros n m f; apply morphism_extensionality;
      unfold tensor_functor_ord; simpl;
      unfold functor_fix_fst_arg_ob, sumfn;  simpl;
      intro x;
      apply subtypeInjectivity_prop;
      simpl; rewrite natplusr0;
      apply maponpaths, maponpaths, subtypeInjectivity_prop; simpl; exact (natminuseqn x)).
  - cbv beta;                   (* We prove that it's an isomorphism. *)
    unfold is_nat_z_iso; intro c; unfold is_z_isomorphism.
    exists (id c). abstract (simpl; unfold is_inverse_in_precat;
    split;
    unfold tensor_functor_ord, functor_fix_fst_arg_ob, tensor_data_ord; simpl;
    exact (id_left (id c))).
Defined.

Local Definition tensor_right_unitor_card_nt_data : nat_trans_data (I_posttensor tensor_functor_card tensor_unit) (functor_identity Δ_sdg).
Proof.
  simpl. unfold "⟹". unfold nat_trans_data. simpl. intro x.
      unfold functor_fix_snd_arg_ob, tensor_functor_card, tensor_unit. simpl.
      rewrite natplusr0. exact (idfun _).
Defined.

Local Definition tensor_right_unitor_card_is_nat_trans : is_nat_trans (I_posttensor tensor_functor_card tensor_unit) (functor_identity Δ_sdg) tensor_right_unitor_card_nt_data.
Proof.
  unfold is_nat_trans, tensor_right_unitor_card_nt_data. simpl.
  intros n m f. unfold functor_fix_snd_arg_mor; simpl.
  apply fincard_hom_extensionality; unfold functor_fix_snd_arg_ob; simpl.
  intro x.
  unfold "·"; simpl.  unfold sumfn.
  assert (x < n) as j. { simpl; induction (natplusr0 n); exact (stnlt x). }
  rewrite (natlthorgeh_left_branch j _). simpl.
  generalize (natgehgthtrans (m+0) m), (! natplusr0 m). intros h p.
  intermediate_path (pr1 (f (ordconstr x j))).
  - induction (natplusr0 m).  reflexivity.
  - apply maponpaths, maponpaths, subtypeInjectivity_prop;
      simpl; induction (natplusr0 n); reflexivity.
Qed.

Local Definition tensor_right_unitor_card : right_unitor tensor_functor_card tensor_unit.
Proof.
  use tpair. { exact (tensor_right_unitor_card_nt_data,,tensor_right_unitor_card_is_nat_trans).  }
  cbv beta.
  unfold is_nat_z_iso, is_z_isomorphism. simpl. intro c.
  use tpair.
    +  simpl. unfold functor_fix_snd_arg_ob, tensor_functor_card. simpl.
       rewrite natplusr0. exact (idfun _).
    + abstract(cbv beta;
      unfold is_inverse_in_precat, tensor_right_unitor_card_nt_data;
      split;
      induction (natplusr0 c); unfold functor_fix_snd_arg_ob, tensor_functor_card;
        simpl;  exact (id_left (id Δ_sdg_ob_constr (c + 0)));
      induction (natplusr0 c); simpl; exact (id_left (id Δ_sdg_ob_constr (c + 0)))).
Defined.

Local Definition tensor_right_unitor_ord_nt_data : nat_trans_data (I_posttensor tensor_functor_ord tensor_unit) (functor_identity Δ_sd).
Proof.
  unfold nat_trans_data. intro n. use make_monfunstn.
  * simpl. unfold functor_fix_snd_arg_ob, tensor_functor_ord.
  simpl. rewrite natplusr0. exact (idfun _).
  * cbv beta. intros x y leq. induction (natplusr0 n). exact leq.
Defined.

Arguments tensor_right_unitor_ord_nt_data /.

Local Definition tensor_right_unitor_ord_is_nat_trans : is_nat_trans (I_posttensor tensor_functor_ord tensor_unit) (functor_identity Δ_sd) tensor_right_unitor_ord_nt_data.
Proof.
  unfold is_nat_trans. intros n m f.
      apply U_faithful. rewrite (functor_comp U). simpl.
      unfold "·". simpl.
      apply fincard_hom_extensionality.
      unfold functor_fix_snd_arg_ob, tensor_functor_ord. simpl.
      induction (natplusr0 m). simpl. intro x.

      unfold sumfn.
      assert (x < n) as xbd. { simpl in *. induction (pathsinv0 (natplusr0 n)). exact (stnlt x). }
      rewrite (natlthorgeh_left_branch xbd _). simpl.
      apply maponpaths. apply maponpaths. apply subtypeInjectivity_prop.
      induction (natplusr0 n). simpl. reflexivity.
Qed.

Local Proposition tensor_right_unitor_ord : right_unitor tensor_functor_ord tensor_unit.
Proof.
  unfold right_unitor.
  use tpair. { exact (tensor_right_unitor_ord_nt_data,,tensor_right_unitor_ord_is_nat_trans). }
  cbv beta. unfold is_nat_z_iso. simpl. intro c. unfold is_z_isomorphism.
  use tpair. { simpl. unfold functor_fix_snd_arg_ob. simpl.
               rewrite natplusr0. exact (monfunstnid c). }
  {
    abstract(cbv beta; unfold tensor_right_unitor_ord_nt_data;
             split;
               unfold functor_fix_snd_arg_ob; simpl;
               induction (natplusr0 c); simpl; reflexivity;
               induction (natplusr0 c); reflexivity).
  }
Defined.

Definition tensor_associator_card_nat_trans_data : nat_trans_data (assoc_left tensor_functor_card) (assoc_right tensor_functor_card).
Proof.
  unfold nat_trans_data. simpl. induction x as [nm k], nm as [n m].
   simpl. rewrite natplusassoc. exact (idfun _).
Defined.

Arguments tensor_associator_card_nat_trans_data /.

Definition tensor_associator_card_is_nat_trans : is_nat_trans _ _ tensor_associator_card_nat_trans_data.
Proof.
  unfold is_nat_trans. simpl.
  induction x as [nm k], nm as [n m], x' as [n'm' k'], n'm' as [n' m'].
  simpl. induction f as [fg h], fg as [f g].
  unfold "·". simpl.
  apply fincard_hom_extensionality. simpl.
  induction x as [xval xbd].
  simpl. induction (natplusassoc n' m' k'). simpl.
  (* We go by cases depending on the value of x *)
  unfold sumfn. simpl.

  set (QQ := internal_paths_rew_r nat (n + m + k ) (n + (m + k )) _ _ _).
  assert (xval < n + (m + k)) as xbd'. { rewrite (pathsinv0 (natplusassoc n m k)). exact xbd. }
  assert ((QQ (xval,, xbd)) = (xval,, xbd')) as j.
  { apply subtypeInjectivity_prop. induction (natplusassoc n m k). reflexivity. }
  simpl in j. rewrite j.
  induction (natlthorgeh _ _) as [INDXLN | INDXGTN].
  +  simpl.
     assert (xval < (n + m)) as leq by exact (natgehgthtrans _ n _ (natlehnplusnm n m) INDXLN).
     rewrite (natlthorgeh_left_branch leq _). simpl.
     reflexivity.
  + simpl. induction (natlthorgeh _ _) as [XNLM | XNGTM].
    * simpl.
      assert ((xval - n) < m) as SS by exact (nat_split XNLM INDXGTN).
      rewrite (natlthorgeh_left_branch SS _). simpl.
      apply (maponpaths (λ k, k + n')), maponpaths, maponpaths, subtypeInjectivity_prop.
      reflexivity.
    * simpl. assert (xval - n ≥ m) as SS.
      { rewrite (pathsinv0 (plusminusnmm m n)).
        apply natgehandminusr. rewrite natpluscomm. exact XNGTM.
      }
      rewrite (natlthorgeh_right_branch SS _). simpl.
      rewrite natplusassoc, (natpluscomm n' m').
      apply (maponpaths (λ k, k + (m' + n'))), maponpaths, maponpaths, subtypeInjectivity_prop.
      simpl. rewrite natminusminus. reflexivity.
Qed.

Definition tensor_associator_card_nat_trans : nat_trans (assoc_left tensor_functor_card) (assoc_right tensor_functor_card)
  := (tensor_associator_card_nat_trans_data,,tensor_associator_card_is_nat_trans).

Definition tensor_associator_ord_nat_trans_data :
  nat_trans_data (assoc_left tensor_functor_ord) (assoc_right tensor_functor_ord).
Proof.
  unfold nat_trans_data. intro x. induction x as [nm k], nm as [n m].
  unfold tensor_functor_ord. simpl.
  rewrite natplusassoc. exact (monfunstnid _).
Defined.

Arguments tensor_associator_ord_nat_trans_data /.

Definition tensor_associator_ord_is_nat_trans : is_nat_trans _ _ tensor_associator_ord_nat_trans_data.
Proof.
  cbv beta. unfold is_nat_trans, tensor_associator_ord_nat_trans_data. simpl.
  intros nmk  n'm'k' fgh. induction nmk as [nm k], nm as [n m].
  induction n'm'k' as [n'm' k'], n'm' as [n' m'].
  induction fgh as [fg h], fg as [f g].
  simpl in *. apply U_faithful. unfold U. simpl.
  apply fincard_hom_extensionality. intro x. simpl.
  induction (natplusassoc n' m' k'). simpl.
  unfold sumfn. simpl.
  set (QQ := internal_paths_rew_r nat (n + m + k ) (n + (m + k )) _ _ _).
  simpl in QQ.
  assert (x < n + (m + k)) as xbd'.
  { rewrite (pathsinv0 (natplusassoc n m k)). exact (stnlt x). }
  set (x' := ordconstr (stntonat _ x) xbd').
  assert (QQ x =x') as RW.
  { apply subtypeInjectivity_prop. induction (natplusassoc n m k). reflexivity. }
  rewrite RW. simpl.

  induction (natlthorgeh x n).
  + simpl. assert (x < (n + m)) as l.
    { apply (natgehgthtrans _ n _ ).
      * rewrite natpluscomm. exact (natlehmplusnm m n).
      * exact a.
    }
    rewrite (natlthorgeh_left_branch l _). simpl.
    apply maponpaths. apply maponpaths. apply subtypeInjectivity_prop. reflexivity.
  + simpl. induction x as [xval xbd]. simpl.
    induction (natlthorgeh (xval - n)  m).
    *  simpl. assert ( xval < n + m) as l. {
         rewrite (pathsinv0 (minusplusnmm xval n b)). rewrite (natpluscomm n m).
         exact (natlthandplusr _ _ n a).
       } simpl.
       rewrite (natlthorgeh_left_branch l _). simpl. apply (maponpaths (λ k, k + n')).
       apply maponpaths. apply maponpaths. apply subtypeInjectivity_prop. reflexivity.
    * simpl. assert (xval ≥ n + m) as geq. {
        rewrite (pathsinv0 (minusplusnmm xval n b)). rewrite (natpluscomm n m).
        exact (natlehandplusr _ _ _ b0).
      }
      rewrite (natlthorgeh_right_branch geq _). simpl. rewrite (natpluscomm n' m').
      rewrite natplusassoc. apply (maponpaths (λ k, k + (m'+n'))).
      apply maponpaths. apply maponpaths. apply subtypeInjectivity_prop. simpl.
      exact (pathsinv0 (natminusminus _ _ _)).
Qed.

Definition tensor_associator_ord_nat_trans :
  nat_trans (assoc_left tensor_functor_ord) (assoc_right tensor_functor_ord):=
  (tensor_associator_ord_nat_trans_data,, tensor_associator_ord_is_nat_trans).

Definition tensor_associator_card : associator tensor_functor_card.
Proof.
  unfold associator, nat_z_iso, is_nat_z_iso.
  exists tensor_associator_card_nat_trans.
  induction c as [nm k], nm as [n m].
  unfold is_z_isomorphism.
  use tpair.
  - simpl.
    rewrite natplusassoc. exact (monfunstnid _).
  - abstract(cbv beta;
    unfold is_inverse_in_precat;
    split;
      simpl; unfold tensor_associator_card_nat_trans_data; simpl;
        induction (natplusassoc n m k); simpl;
        apply fincard_hom_extensionality; reflexivity;
     simpl; unfold tensor_associator_card_nat_trans_data;
      induction (pathsinv0 (natplusassoc n m k));
      simpl; induction (natplusassoc n m k); simpl; apply fincard_hom_extensionality;
      reflexivity).
Defined.

Definition tensor_associator_ord : associator tensor_functor_ord.
  unfold associator, nat_z_iso.
  exists tensor_associator_ord_nat_trans.
  unfold is_nat_z_iso.
  intro c. induction c as [nm k]. induction nm as [n m].
  unfold is_z_isomorphism.
  use tpair. {                  (* We construct the inverse. *)
    simpl. rewrite natplusassoc. exact (monfunstnid _).
  }           (* We prove that it is an inverse. *)
  { abstract(cbv beta;
    unfold is_inverse_in_precat, tensor_associator_ord_nat_trans,
      tensor_associator_ord_nat_trans_data;
     split;
      simpl; induction (natplusassoc n m k); simpl;
        apply morphism_extensionality; reflexivity;
      simpl; induction (pathsinv0 (natplusassoc n m k));
        simpl; induction (natplusassoc n m k); simpl; apply morphism_extensionality;
        reflexivity).
    }
Defined.

Proposition triangle_eq_holds_card : triangle_eq tensor_functor_card tensor_unit tensor_left_unitor_card tensor_right_unitor_card tensor_associator_card.
Proof.
  unfold triangle_eq. simpl. intros a b. apply fincard_hom_extensionality.
  unfold tensor_functor_card, functor_fix_snd_arg_ob,
    tensor_right_unitor_card_nt_data, tensor_associator_card_nat_trans_data.
  simpl.
  intro x. induction x as [xval xbd].
  unfold sumfn. simpl.

  set (QJ := internal_paths_rew_r nat (a + 0 + b)  _ _ _ _ ). simpl in QJ.
  assert (xval < a + b) as XLAB'. { rewrite (pathsinv0 (natplusr0 a)). exact xbd. }
  set (x' := ordconstr xval XLAB'). unfold "·". simpl.
  assert ((QJ (xval,, xbd)) =  x') as RW.
  { apply subtypeInjectivity_prop. simpl in *.  unfold QJ. generalize (natplusassoc a 0 b).
    simpl. generalize (a + b). induction p.  reflexivity.
  } simpl in *. rewrite RW.
  induction (natlthorgeh xval _) as [XLA | XGA].
  - simpl. assert (xval < a) as XLA'. { rewrite (natplusr0 a) in XLA.  exact XLA. }
    rewrite (natlthorgeh_left_branch XLA' _). simpl in *. induction (natplusr0 a). reflexivity.
  - simpl. assert (xval ≥ a) as XGA'. { rewrite (natplusr0 a) in XGA.  exact XGA. }
    rewrite (natlthorgeh_right_branch XGA' _). simpl in *. rewrite (natplusr0 a). reflexivity.
Qed.

Proposition triangle_eq_holds_ord : triangle_eq tensor_functor_ord tensor_unit tensor_left_unitor_ord tensor_right_unitor_ord tensor_associator_ord.
Proof.
  unfold triangle_eq. simpl. intros a b. apply morphism_extensionality.
  unfold tensor_functor_ord, functor_fix_snd_arg_ob. simpl.
  unfold tensor_associator_ord_nat_trans_data. simpl.
  intro x. induction x as [xval xbd].
  unfold sumfn. simpl.
  set (QJ := internal_paths_rew_r nat (a + 0 + b)  _ _ _ _ ). simpl in QJ.
  assert (xval < a + b) as XLAB'. { rewrite (pathsinv0 (natplusr0 a)). exact xbd. }
  set (x' := ordconstr xval XLAB'). unfold "·". simpl.
  assert ((QJ (xval,, xbd)) =  x') as RW.
  { apply subtypeInjectivity_prop. simpl in *.  unfold QJ. generalize (natplusassoc a 0 b).
    simpl. generalize (a + b). induction p.  reflexivity.
  } simpl in *. rewrite RW.
  apply subtypeInjectivity_prop.
  induction (natlthorgeh xval _) as [XLA | XGA].
  - simpl. assert (xval < a) as XLA'. { rewrite (natplusr0 a) in XLA.  exact XLA. }
    rewrite (natlthorgeh_left_branch XLA' _). simpl in *.
    induction (natplusr0 a). reflexivity.
  - simpl. assert (xval ≥ a) as XGA'. { rewrite (natplusr0 a) in XGA.  exact XGA. }
    rewrite (natlthorgeh_right_branch XGA' _). simpl in *. rewrite (natplusr0 a). reflexivity.
Qed.

Proposition pentagon_eq_holds_card : pentagon_eq tensor_functor_card tensor_associator_card.
Proof.
  unfold pentagon_eq. intros. apply fincard_hom_extensionality. simpl.
  unfold tensor_associator_card_nat_trans_data. simpl.
  intro x. induction (natplusassoc b c d). simpl.
  induction (natplusassoc a b (c + d)). simpl.
  unfold "·". simpl.
  induction (natplusassoc (a + b) c d). simpl.
  unfold "id". simpl. set (k:=(tensor_id_card (make_dirprod a (b + c + d)))).
  unfold "id" in k. simpl in k. simpl.
  unfold "id" in k. simpl in k. unfold Δ_sdg_ob_constr. rewrite k.
  induction (natplusassoc a (b + c) d), (natplusassoc a b c). simpl.
  set (k':=(tensor_id_card (make_dirprod (a + b + c) d))).
  unfold "id" in k'. simpl in k'.
  unfold "id" in k'. simpl in k'. rewrite k'. reflexivity.
Qed.

Proposition pentagon_eq_holds_ord : pentagon_eq tensor_functor_ord tensor_associator_ord.
Proof.
  unfold pentagon_eq.
  intros. apply U_faithful. rewrite (functor_comp U), (functor_comp U), (functor_comp U).
  apply fincard_hom_extensionality.
  unfold tensor_associator_ord. simpl.
  unfold tensor_associator_ord_nat_trans_data. simpl.
  intro x. induction (natplusassoc b c d), (natplusassoc a b (c + d)).
  unfold "·". simpl.
  induction (natplusassoc (a + b) c d).
  set (j:= (tensor_id_card (make_dirprod a (b + c + d)))).
  unfold tensor_data_card in j. simpl in j. unfold "id" in j. simpl in j.
  unfold idfun. simpl. unfold idfun in j. rewrite j. induction (natplusassoc a (b + c) d).
  simpl.
  induction (natplusassoc a b c). simpl.
  set (j' := (tensor_id_card (make_dirprod (a + b + c) d))).

  unfold tensor_data_card in j'. simpl in j'.
  simpl in j'. unfold "id" in j'. simpl in j'. unfold idfun in *. rewrite j'.
  reflexivity.
Qed.

Definition AugmentedSimplexCategory : monoidal_cat.
Proof.
  use mk_monoidal_cat.
  + exact Δ.
  + exact tensor_functor_ord.
  + exact tensor_unit.
  + exact tensor_left_unitor_ord.
  + exact tensor_right_unitor_ord.
  + exact tensor_associator_ord.
  + exact triangle_eq_holds_ord.
  + exact pentagon_eq_holds_ord.
Defined.

Definition FinCard : monoidal_cat.
Proof.
  use mk_monoidal_cat.
  + exact Δ_sdg.
  + exact tensor_functor_card.
  + exact tensor_unit.
  + exact tensor_left_unitor_card.
  + exact tensor_right_unitor_card.
  + exact tensor_associator_card.
  + exact triangle_eq_holds_card.
  + exact pentagon_eq_holds_card.
Defined.

Definition U_ε : (monoidal_cat_unit FinCard) --> U (monoidal_cat_unit AugmentedSimplexCategory).
Proof.
  unfold U. simpl. unfold monoidal_cat_unit. simpl. exact (idfun (⟦ tensor_unit ⟧)%stn).
Defined.

Definition U_μ :  monoidal_functor_map AugmentedSimplexCategory FinCard U.
Proof.
  unfold monoidal_functor_map. simpl.
  unfold "⟹". use tpair.
  - unfold nat_trans_data. unfold precategory_binproduct_data.
    simpl. simpl. intro x. induction x as [n m].
    simpl. exact (idfun (⟦ n + m ⟧)%stn).
  - abstract(cbv beta;
      unfold is_nat_trans; simpl; intros x x'; induction x as [n m], x' as [n' m'];
      unfold precategory_binproduct_mor; intro fg; simpl in fg; induction fg as [f g];
      simpl;
    set (s:= id_left (Δ_sdg_mor_constr (AugmentedSimplexCategory.sumfn (pr1 f) (pr1 g))));
    unfold "id" in s; simpl in s; unfold Δ_sdg_mor_constr in s;
    unfold Δ_sdg_ob_constr in s; unfold idfun;
    simpl in s; simpl; induction f as [ffun fguarantee], g as [gfun gguarantee];
    simpl in s; simpl; unfold "·"; unfold "·" in s; simpl in s; simpl;
    unfold idfun in s; rewrite s; reflexivity).
Defined.

Definition U_α : monoidal_functor_associativity AugmentedSimplexCategory FinCard U U_μ.
Proof.
  unfold monoidal_functor_associativity.
  intros x y z. simpl.
  unfold MonoidalFunctors.α_D, MonoidalFunctors.α_C. simpl.
  unfold monoidal_cat_associator. simpl.
  (* We get rid of all the identity morphisms. *)
  change (idfun (⟦ x + y + z⟧)%stn) with (identity (C:=Δ_sdg) (x + y + z)).
  change (idfun (⟦ x + y ⟧)%stn) with (identity (C:=Δ_sdg)  (x + y)).
  change (idfun (⟦ x + (y + z) ⟧)%stn) with (identity (C:=Δ_sdg)  (x + (y+z))).
  change (idfun (⟦ y + z ⟧)%stn) with (identity (C:=Δ_sdg)  (y+z)).
  set (j':= (tensor_id_card (make_dirprod (x + y) z))). simpl in *. rewrite j'.
  set (j:= (tensor_id_card (make_dirprod x (y + z)))). simpl in *. rewrite j.
  simpl in *.
  rewrite (id_right (C:=Δ_sdg)), (id_right (C:=Δ_sdg)),
  (id_right (C:=Δ_sdg)), (id_left (C:=Δ_sdg)).
  (* Done. *)
  apply fincard_hom_extensionality. intro t. (* induction t as [tval tbd]. *)
  cbn. unfold tensor_associator_ord_nat_trans_data, tensor_associator_card_nat_trans_data.
  cbn.
  induction (nat_rect _ _). reflexivity.
Qed.

Local Proposition U_unitality : monoidal_functor_unitality AugmentedSimplexCategory FinCard U U_ε U_μ.
Proof.
  unfold monoidal_functor_unitality.
  simpl. intro x. unfold MonoidalFunctors.λ_D, monoidal_cat_left_unitor. simpl.
  split.
  - change (idfun (⟦x⟧)%stn) with (identity (C:=Δ_sdg) x).
    rewrite (id_right (C:=Δ_sdg)),  (id_right (C:=Δ_sdg)).
    cbn. unfold U_ε, sumfn. simpl. apply funextsec. intro A. simpl.
    apply subtypeInjectivity_prop. simpl. rewrite natminuseqn. rewrite natplusr0. reflexivity.
  - change (idfun (⟦x⟧)%stn) with (identity (C:=Δ_sdg) x).
    unfold MonoidalFunctors.I_C, monoidal_cat_unit. simpl.
    rewrite (id_right (C:=Δ_sdg)). cbn.
    unfold tensor_right_unitor_card_nt_data.
    induction (natplusr0 x). simpl.
    apply funextsec. intro y. simpl. unfold sumfn.
    induction y as [yval ybd]. simpl.
    assert (yval < x) as j. { rewrite (natplusr0 x) in ybd. exact ybd. }
    rewrite (natlthorgeh_left_branch j _). simpl.
    induction (! natplusr0 x). simpl. apply subtypeInjectivity_prop. reflexivity.
Qed.

Definition U_Mon_Lax : lax_monoidal_functor AugmentedSimplexCategory FinCard.
Proof.
  use mk_lax_monoidal_functor.
  + exact U.
  + exact U_ε.
  + exact U_μ.
  + exact U_α.
  + exact U_unitality.
Defined.

Definition U_Mon_Strong : strong_monoidal_functor AugmentedSimplexCategory FinCard.
Proof.
  exists U_Mon_Lax. split.
  - cbn. unfold is_z_isomorphism. use tpair.
    + simpl. exact (idfun (⟦ tensor_unit ⟧)%stn).
    + abstract(simpl; unfold is_inverse_in_precat; split;
        unfold U_ε; exact (id_right (C:=Δ_sdg) (idfun _));
        unfold U_ε; exact (id_right (C:=Δ_sdg) (idfun _))).
  - unfold is_nat_z_iso. simpl. intro c. induction c as [n m].
    unfold is_z_isomorphism. simpl. exists (idfun (⟦ n + m⟧)%stn).
    abstract(unfold is_inverse_in_precat; split;
      exact (id_right (C:=Δ_sdg) (idfun _));
      exact (id_right (C:=Δ_sdg) (idfun _))).
Defined.

Local Lemma functor_eq_to_object_eq_on_homs
  (C D : precategory) (F G  : functor C D) ( p : F = G) (c : C) (d : D) ( f : d --> G c) :
    internal_paths_rew_r (C ⟶ D) F G (λ H : C ⟶ D, D ⟦ d , H c⟧) f p =
      internal_paths_rew_r D (F c) (G c) (λ d' : D, D ⟦ d , d' ⟧) f
                           (maponpaths (λ H : C ⟶ D, H c) p).
Proof.
  induction p. reflexivity.
Defined.

Local Proposition tensor_card_is_strict_left_iso_id :
  ∏ eq_λ : I_pretensor (monoidal_cat_tensor FinCard)
         (monoidal_cat_unit FinCard) = functor_identity (pr1 FinCard),
  (is_nat_z_iso_id eq_λ (monoidal_cat_left_unitor FinCard)).
Proof.
  intro eq_λ.
  unfold is_nat_z_iso_id. intro c. unfold nat_comp_to_endo.
  rewrite functor_eq_to_object_eq_on_homs. set (j := maponpaths _ _). simpl in j. simpl in c.
  assert (j = idpath c) as RW by apply (setproperty natset); rewrite RW.
  reflexivity.
Qed.

Local Arguments monoidal_cat_tensor /.
Local Arguments monoidal_cat_unit /.
Local Arguments functor_fix_fst_arg /.
Local Arguments functor_fix_snd_arg /.
Local Arguments functor_fix_fst_arg_ob /.
Local Arguments functor_fix_snd_arg_ob /.

Local Definition right_unitor_id (c : Δ_sdg) :
           I_posttensor (monoidal_cat_tensor FinCard)
         (monoidal_cat_unit FinCard) c = functor_identity (pr1 FinCard) c.
Proof.
  simpl. exact (natplusr0 c).
Defined.

Local Proposition tensor_card_is_strict_right_iso_id :   ∏ eq_ρ : I_posttensor (monoidal_cat_tensor FinCard)
         (monoidal_cat_unit FinCard) = functor_identity (pr1 FinCard),
  is_nat_z_iso_id eq_ρ (monoidal_cat_right_unitor FinCard).
Proof.
  unfold is_nat_z_iso_id. intros eq_ρ c. unfold nat_comp_to_endo.
  set (Δ_sdg := (pr1 FinCard)).
  set (Rtensor0 := (I_posttensor _ _)).
  set (idfunctor := (functor_identity _)).
  rewrite functor_eq_to_object_eq_on_homs. set (j := maponpaths _ _).
  cbv beta in j.
  assert (j = right_unitor_id c) as RW by apply (setproperty natset); rewrite RW.
  unfold right_unitor_id, transportb. apply fincard_hom_extensionality.
  intro x. unfold Rtensor0 in x. simpl in x.
  simpl. unfold tensor_right_unitor_card_nt_data. simpl.
  induction (natplusr0 c). simpl. reflexivity.
Qed.

Local Proposition tensor_card_is_strict_associator_id :
  ∏ eq_α : assoc_left tensor_functor_card = assoc_right tensor_functor_card,
  is_nat_z_iso_id eq_α (monoidal_cat_associator FinCard).
Proof.
  unfold is_nat_z_iso_id. intro eq_α.
  intro c. simpl in c. induction c as [nm k]. induction nm as [n m].
  unfold nat_comp_to_endo. rewrite functor_eq_to_object_eq_on_homs.
  unfold assoc_left. simpl.
  set (j:= maponpaths _ _).
  assert (j = (natplusassoc n m k)) as RW by apply (pr2 natset). rewrite RW.
  simpl. generalize (natplusassoc n m k). induction p. simpl. reflexivity.
Qed.

Definition FinCardStrict : strict_monoidal_cat.
Proof.
  use tpair.  { exact FinCard. }
  cbv beta. intros eq_λ eq_ρ eq_α.
  use tpair. { exact (tensor_card_is_strict_left_iso_id eq_λ). }
  cbv beta. split. { exact (tensor_card_is_strict_right_iso_id eq_ρ). }
  exact (tensor_card_is_strict_associator_id eq_α).
Defined.

Local Proposition tensor_Δ_left_unitor_is_id :
  ∏ eq_λ : I_pretensor (monoidal_cat_tensor AugmentedSimplexCategory)
         (monoidal_cat_unit AugmentedSimplexCategory) = functor_identity (pr1 AugmentedSimplexCategory), (is_nat_z_iso_id eq_λ (monoidal_cat_left_unitor AugmentedSimplexCategory)).
Proof.
  unfold is_nat_z_iso_id. intros eq_λ c.
  unfold nat_comp_to_endo. set (Δ_sd := (pr1 FinCard)).
  set (Ltensor0 := (I_pretensor _ _)).
  set (idfunctor := (functor_identity _)).
  rewrite functor_eq_to_object_eq_on_homs. set (j := maponpaths _ _).
  unfold monoidal_cat_left_unitor. simpl pr1.
  unfold tensor_left_unitor_ord. simpl.
  unfold Ltensor0, idfunctor in j. simpl in j.
  assert (j = idpath c) as RW by apply (setproperty natset). rewrite RW.
  reflexivity.
Qed.

Local Proposition tensor_Δ_right_unitor_is_id :
  ∏ eq_ρ : I_posttensor (monoidal_cat_tensor AugmentedSimplexCategory)
                        (monoidal_cat_unit AugmentedSimplexCategory) =
             functor_identity (pr1 AugmentedSimplexCategory),
  is_nat_z_iso_id eq_ρ (monoidal_cat_right_unitor AugmentedSimplexCategory).
Proof.
  unfold is_nat_z_iso_id. intro eq_ρ. intro c.
  unfold nat_comp_to_endo.
  set (Rtensor0 := (I_posttensor _ _)).
  set (idfunctor := (functor_identity _)).
  rewrite functor_eq_to_object_eq_on_homs. set (j := maponpaths _ _).
  cbv beta in j.
  assert (j = right_unitor_id c) as RW. { apply (setproperty natset). } rewrite RW.
  simpl. unfold right_unitor_id. induction (natplusr0 c). simpl. reflexivity.
Qed.

Local Proposition tensor_ord_is_strict_associator_id :
  ∏ eq_α : assoc_left tensor_functor_ord = assoc_right tensor_functor_ord,
  is_nat_z_iso_id eq_α (monoidal_cat_associator AugmentedSimplexCategory).
Proof.
  unfold is_nat_z_iso_id. intro eq_α.
  intro c. simpl in c. induction c as [nm k],  nm as [n m].
  unfold nat_comp_to_endo. rewrite functor_eq_to_object_eq_on_homs.
  unfold assoc_left. simpl.
  set (j:= maponpaths _ _).
  assert (j = (natplusassoc n m k)) as RW by apply (setproperty natset); rewrite RW.
  simpl. generalize (natplusassoc n m k). induction p. reflexivity.
Qed.

Definition FinOrdStrict : strict_monoidal_cat.
Proof.
  use tpair.  { exact AugmentedSimplexCategory. }
  cbv beta. intros eq_λ eq_ρ eq_α.
  use tpair. { exact (tensor_Δ_left_unitor_is_id eq_λ). }
  split. { exact (tensor_Δ_right_unitor_is_id eq_ρ). }
  exact (tensor_ord_is_strict_associator_id eq_α).
Defined.
