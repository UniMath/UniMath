Require Import UniMath.MoreFoundations.All.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.limits.pullbacks.
Require Import UniMath.CategoryTheory.limits.pushouts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.Opp.

Require Import UniMath.CategoryTheory.Chains.Chains.

Require Import UniMath.CategoryTheory.DisplayedCats.Examples.Arrow.
Require Import UniMath.CategoryTheory.ModelCategories.Retract.
Require Import UniMath.CategoryTheory.ModelCategories.MorphismClass.
Require Import UniMath.CategoryTheory.ModelCategories.Lifting.


Local Open Scope cat.
Local Open Scope morcls.
Local Open Scope retract.

Section wfs.

(* Any map can be factored through maps in L and R *)
Definition wfs_fact_ax {C : category} (L R : morphism_class C) := 
  ∏ x y (f : x --> y), 
    ∃ ef (l : x --> ef) (r : ef --> y), 
      (L _ _) l × (R _ _) r × l · r = f.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L27 *)
Definition is_wfs {C : category} (L R : morphism_class C) :=
  (L = llp R) × (R = rlp L) × (wfs_fact_ax L R).

Definition make_is_wfs {C : category} {L R : morphism_class C}
    (llp : L = llp R) (rlp : R = rlp L) (fact : wfs_fact_ax L R) : is_wfs L R :=
  make_dirprod llp (make_dirprod rlp fact).

Definition wfs (C : category) :=
  ∑ (L R : morphism_class C), is_wfs L R.

Definition make_wfs {C : category} (L R : morphism_class C) (w : is_wfs L R) : wfs C :=
  tpair _ L (tpair _ R w).

Definition wfs_L {C : category} (w : wfs C) := (pr1 w).
Definition wfs_R {C : category} (w : wfs C) := pr1 (pr2 w).
Definition is_wfs_llp  {C : category} {L R : morphism_class C} (w : is_wfs L R) := pr1 w.
Definition is_wfs_rlp  {C : category} {L R : morphism_class C} (w : is_wfs L R) := pr1 (pr2 w).
Definition is_wfs_fact {C : category} {L R : morphism_class C} (w : is_wfs L R) := pr2 (pr2 w).
Definition wfs_is_wfs {C : category} (w : wfs C) := pr2 (pr2 w).
Definition wfs_llp  {C : category} (w : wfs C) := is_wfs_llp (wfs_is_wfs w).
Definition wfs_rlp  {C : category} (w : wfs C) := is_wfs_rlp (wfs_is_wfs w).
Definition wfs_fact {C : category} (w : wfs C) := is_wfs_fact (wfs_is_wfs w).

Lemma isaprop_is_wfs {C : category} (L R : morphism_class C) :
    isaprop (is_wfs L R).
Proof.
  apply isapropdirprod.
  - unfold isaprop.
    exact (isasetmorphism_class _ _).
  - apply isapropdirprod.
    * exact (isasetmorphism_class _ _).
    * do 3 (apply impred_isaprop; intro).
      apply propproperty.
Qed.

Context {C : category}.


(* Can't do dot notation like in lean (is_wfs.lp)*)
(* any two maps in a wfs have the lifting property with respect to each other *)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L33 *)
Lemma wfs'lp (w : wfs C)
    {x y a b} {f : x --> y} {g : a --> b} 
    (hf : (wfs_L w _ _) f) (hg : (wfs_R w _ _) g) : 
  lp f g.
Proof.
  unfold wfs_L in hf.
  rewrite (wfs_llp w) in hf.
  exact (hf _ _ _ hg). 
Qed.

(* if f' is a retract of f and f is in L for some WFS, then so is f' *)
(* proposition 14.1.13 in More Concise AT *)
(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L40 *)
Lemma wfs_L_retract (w : wfs C)
    {x y x' y'} {f : x --> y} {f' : x' --> y'}
    (r : retract f f') (hf : (wfs_L w _ _) f) : 
  (wfs_L w _ _) f'.
Proof.
  destruct r as [ia [ra [ib [rb [ha [hb [hi hr]]]]]]].

  unfold wfs_L.
  rewrite (wfs_llp w).
  intros a b g hg h k s.
  (* existence of lift in part of diagram *)
  use (wfs'lp w hf hg (h ∘ ra) (k ∘ rb) _).
  {
    rewrite <- assoc, s, assoc, assoc, hr.
    reflexivity.
  }
  (* extract lift *)
  intro hl.
  destruct hl as  [l [hlh hlk]].
  
  (* turn proof into normal ∑-type *)
  apply hinhpr.
  (* composition in diagram *)
  exists (l ∘ ib).
  (* diagram chasing *)
  split.
  * rewrite assoc, <- hi, <- assoc, hlh, assoc, ha, id_left.
    reflexivity.
  * rewrite <- assoc, hlk, assoc, hb, id_left.
    reflexivity.
Qed.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L52 *)
(* Lemma 14.1.9 in MCAT *)
Lemma llp_rlp_self (L : morphism_class C) : L ⊆ llp (rlp L).
Proof.
  intros a b f hf x y g hg.
  apply (hg _ _ _).
  exact hf.
Qed.

(* no counterpart in lean *)
Lemma rlp_llp_self (L : morphism_class C) : L ⊆ rlp (llp L).
Proof.
  intros a b f hf x y g hg.
  apply (hg _ _ _).
  exact hf.
Qed.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L55 *)
(* No counterpart in MCAT, (□(I□), I□) is a WFS *)
Lemma wfs_of_factorization (I : morphism_class C) 
    (h : ∏ (x y : C) (f : x --> y), ∃ z (g : x --> z) (h : z --> y), (llp (rlp I) _ _ g) × (rlp I _ _ h) × (h ∘ g = f)) :
  is_wfs (llp (rlp I)) (rlp I).
Proof.
  use make_is_wfs.
  - trivial.
  - apply morphism_class_subset_antisymm; intros x y g hg.
    * exact (rlp_llp_self _ _ _ _ hg).
    * intros a b f hf.
      apply (hg _ _ _).
      exact (llp_rlp_self _ _ _ _ hf).
  - exact h.
Qed.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L67 *)
(* same name as Lemma 14.1.12 in MCAT, but a different phrasing 
In MCAT, the statement is in reference of a single morphism, not a whole class
*)
Lemma retract_argument {L' : morphism_class C} (w : wfs C)
    (H : wfs_fact_ax L' (wfs_R w)) :
  ∏ {x y} (f : x --> y), 
    (wfs_L w _ _) f 
    -> ∃ {x' y'} (f' : x' --> y') (r : retract f' f), (L' _ _) f'.
Proof.
  intros x y f hf.

  (* rcases H f with ⟨z, g, h, hg, hh, hgh⟩, *)
  (* Get factorization for f from H *)
  specialize (H _ _ f) as eHf.
  simpl in eHf.
  use (hinhuniv _ eHf).
  intro Hf.
  destruct Hf as [z [g [h [hg [hh hgh]]]]].

  (* rcases w.lp hf hh g (𝟙 _) (by rw hgh; simp) with ⟨l, hl₁, hl₂⟩, *)
  (* Use lifting property to get map l in diagram *)
  use (wfs'lp w hf hh g (identity _)).
  {
    rewrite hgh, id_right.
    reflexivity.
  }
  intro hl.
  destruct hl as [l [hl1 hl2]].

  (* Show that f is a retract of g *)
  assert (r : retract g f).
  {
    use (make_retract (identity _) (identity _) l h).
    use make_is_retract.
    - now rewrite id_left.
    - assumption.
    - rewrite id_left. now symmetry.
    - rewrite id_left. now symmetry.
  }

  (* convert goal to normal ∑-type *)
  apply hinhpr.
  
  (* finish proof *)
  exists x, z, g, r.
  exact hg.
Qed.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L82 *)
Lemma lp_isos_univ {x y a b : C} (f : x --> y) (g : a --> b) : 
  (morphism_class_isos C _ _ f) -> lp f g.
Proof.
  intro H.
  set (fiso := make_iso _ H).
  (* change f to the isomorphism in the goal *)
  change (lp fiso g).
  
  intros h k s.
  (* lift we are looking for is h ∘ f^{-1} *)
  apply hinhpr.
  exists (h ∘ (inv_from_iso fiso)).
  (* diagram chasing *)
  split.
  * rewrite assoc, iso_inv_after_iso, id_left.
    reflexivity.
  * rewrite <- assoc, s, assoc.
    rewrite iso_after_iso_inv, id_left.
    reflexivity.
Qed.

Lemma lp_univ_isos {x y a b : C} (f : x --> y) (g : a --> b) : 
  (morphism_class_isos C _ _ f) -> lp g f.
Proof.
  intro H.
  set (fiso := make_iso _ H).
  (* change f to the isomorphism in the goal *)
  change (lp g fiso).
  
  intros h k s.
  (* lift we are looking for is h ∘ f^{-1} *)
  apply hinhpr.
  exists ((inv_from_iso fiso) ∘ k).
  (* diagram chasing *)
  split.
  * rewrite assoc, <- s, <- assoc, iso_inv_after_iso, id_right.
    reflexivity.
  * rewrite <- assoc, iso_after_iso_inv, id_right.
    reflexivity.
Qed.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L91 *)
Lemma llp_univ : llp (morphism_class_univ C) = morphism_class_isos C.
Proof.
  apply morphism_class_subset_antisymm; intros x y f H.
  - (* apply llp of f with itself *)
    specialize ((H _ _ f) tt).
    (* choose horizontal maps to be identity *)
    use (H (identity _) (identity _)).
    {
      (* commutativity of diagram *)
      rewrite id_left, id_right.
      reflexivity.
    }
    (* extract lift l from diagram *)
    intro hl.
    destruct hl as [l [hfl hlf]].
    unfold morphism_class_isos.
    
    (* show f is a z_iso (we have its inverse, the lift l) *)
    assert (is_z_isomorphism f) as f_z_iso.
    {
      exists l.
      split; assumption.
    }
    (* finish proof *)
    apply is_iso_from_is_z_iso.
    exact f_z_iso.
  - intros a b g _.
    (* other inclusion is exactly the previous Lemma *)
    exact (lp_isos_univ f g H).
Qed.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L101 *)
Lemma rlp_isos : rlp (morphism_class_isos C) = morphism_class_univ C.
Proof.
  (* This proof is slightly different *)
  apply morphism_class_subset_antisymm.
  - (* an iso is a morphism *)
    intros x y g H.
    unfold morphism_class_univ.
    exact tt.
  - (* other inclusion is easy with previous Lemmas *)
    rewrite <- llp_univ.
    exact (rlp_llp_self _).
Qed.

(* https://github.com/rwbarton/lean-model-categories/blob/e366fccd9aac01154da9dd950ccf49524f1220d1/src/category_theory/model/wfs.lean#L109 *)
Lemma wfs_isos_univ : is_wfs (morphism_class_isos C) (morphism_class_univ C).
Proof.
  (* apply symmetry to immediately exact the previous Lemmas *)
  use make_is_wfs; try symmetry.
  - exact llp_univ.
  - exact rlp_isos.
  - (* factorize a morphism through identity and itself *)
    intros x y f.
    apply hinhpr.
    exists x, (identity x), f.

    (* this solves the second subgoal, stating that f is a morphism *)
    repeat split.
    * exact (identity_is_iso C x).
    * rewrite id_left.
      reflexivity.
Qed.

Definition opp_is_wfs {L R : morphism_class C} (w : is_wfs L R) : 
    is_wfs (morphism_class_opp R) (morphism_class_opp L).
Proof.
  use make_is_wfs.
  - rewrite (is_wfs_rlp w).
    exact (opp_rlp_is_llp_opp _).
  - rewrite (is_wfs_llp w).
    exact (opp_llp_is_rlp_opp _).
  - intros x y f.
    specialize ((is_wfs_fact w) _ _ (rm_opp_mor f)) as H.
    use (hinhuniv _ H).
    clear H; intro H.
    destruct H as [z [g [h [? [? ?]]]]].
    apply hinhpr.
    exists (opp_ob z), (opp_mor h), (opp_mor g).
    repeat split; assumption.
Qed.

Definition opp_wfs (w : wfs C) : wfs (op_cat C).
Proof.
  exists (morphism_class_opp (wfs_R w)), (morphism_class_opp (wfs_L w)).
  exact (opp_is_wfs (wfs_is_wfs w)).
Defined.

End wfs. 

Section properties.

Lemma wfs_L_contains_isos {C : category} (w : wfs C) :
    (morphism_class_isos C) ⊆ (wfs_L w).
Proof.
  (* isos are the llp of univ *)
  rewrite <- llp_univ.
  (* rewrite llp property *)
  unfold wfs_L.
  rewrite (wfs_llp w).

  apply llp_anti.
  (* every morphism is a morphism *)
  intros x y f hf.
  exact tt.
Qed.

(* Dual statement *)
Lemma wfs_R_contains_isos {C : category} (w : wfs C) : 
    (morphism_class_isos C) ⊆ (wfs_R w).
Proof.
  intros x y f hf.
  set (opp_containment := wfs_L_contains_isos (opp_wfs w)).
  exact (opp_containment _ _ (opp_mor f) (opp_is_iso _ hf)).
Qed.

(* Dual statement of wfs_L_retract *)
Lemma wfs_R_retract {C : category} (w : wfs C)
    {a b a' b'} {f : a --> b} {f' : a' --> b'}
    (r : retract f f') (hf : (wfs_R w _ _) f) :
  (wfs_R w _ _) f'.
Proof.
  use (wfs_L_retract (opp_wfs w) (opp_retract r)).
  exact hf.
Qed.

(* https://ncatlab.org/nlab/show/weak+factorization+system#ClosuredPropertiesOfWeakFactorizationSystem *)
Lemma wfs_closed_pullbacks {C : category} (w : wfs C) 
    {x y z : C} {p : x --> y} {f : z --> y} 
    (Pb : Pullback f p) : 
  ((wfs_R w _ _) p) -> ((wfs_R w _ _) (PullbackPr1 Pb)).
Proof.
  intro p_r.

  destruct Pb as [[zfx [f'p p2]] [H isPb]].
  simpl in *.
  cbn.

  (* need to show that f'p has rlp w.r.t. all i ∈ L *)
  unfold wfs_R.
  rewrite (wfs_rlp w).
  intros a b i i_l.

  (* commutative diagram *)
  intros p1 g Hp1g.

  (* obtain diagram
      p1     p2
    a --> Pb --> x
   i|     |f'p   |p
    v     v      v
    b --> z  --> y
       g      f
  *)

  (* use rlp of p to get lift  in outer diagram*)
  unfold wfs_R in p_r.
  rewrite (wfs_rlp w) in p_r.

  use (p_r _ _ i i_l (p2 ∘ p1) (f ∘ g) _).
  {
    rewrite <- assoc, <- H, assoc, Hp1g, assoc.
    reflexivity. 
  }
  
  (* extract lift *)
  intro hl.
  destruct hl as [l [hl1 hl2]].
  symmetry in hl2.
  
  (* use pullback property to get lift gh in
          Pb --> x
    gh  /  |f'p  |p
      /    v     v
     b --> z --> y
        g     f
  *)
  destruct (isPb _ g l hl2) as [[gh [hgh1 hgh2]] _].
  
  (* gh is the lift in the inner diagram *)
  apply hinhpr.
  exists gh.
  split.
  - (* use uniqueness of maps into pullback to show commutativity
       in top triangle *)
    apply (MorphismsIntoPullbackEqual isPb).
    * rewrite <-assoc, hgh1, Hp1g.
      reflexivity.
    * rewrite <- assoc, hgh2, hl1.
      reflexivity.
  - (* commutativity in lower triangle is trivial by pullback property *)
    exact hgh1.
Qed.

(* Dual statement *)
Lemma wfs_closed_pushouts {C : category} (w : wfs C) 
    {x y z : C} {p : x --> y} {f : x --> z}
    (Po : Pushout f p) : 
  ((wfs_L w _ _) p) -> ((wfs_L w _ _) (PushoutIn1 Po)).
Proof.
  (* didn't expect Coq would be this powerful... *)
  apply (wfs_closed_pullbacks (opp_wfs _)).
Qed.

(* https://ncatlab.org/nlab/show/weak+factorization+system#ClosuredPropertiesOfWeakFactorizationSystem *)
(* map between coproducts is in L if all arrows between objects in coproduct are *)
Lemma wfs_closed_coproducts {C : category} {I : hSet} (w : wfs C)
    {a b : I -> C} 
    {f : ∏ (i : I), a i --> b i} (hf : ∀ (i : I), (wfs_L w _ _) (f i))
    (CCa : Coproduct _ _ a) (CCb : Coproduct _ _ b) 
    (aoc : AxiomOfChoice) : 
  (wfs_L w _ _) (CoproductOfArrows _ _ CCa CCb f).
Proof.
  unfold wfs_L in *.
  (* create square with g ∈ R *)
  rewrite (wfs_llp w) in *.
  intros x y g hg.
  intros h k s.

  (* obtain a square for all i ∈ I *)
  (* factor maps from A_i / B_i through coproduct object *)
  set (hi := λ i, (CoproductIn _ _ CCa i) · h).
  set (ki := λ i, (CoproductIn _ _ CCb i) · k).

  assert (∏ i, ∃ li, ((f i) · li = hi i) × (li · g = ki i)) as ilift.
  {
    intro i.
    (* extract lift in i-th diagram *)
    specialize (hf i _ _ g hg) as H.
    specialize (H (hi i) (ki i)).
    
    use H.
    
    unfold hi, ki.
    rewrite <- assoc, s, assoc, assoc.
    now rewrite (CoproductOfArrowsIn _ _).
  }

  (* we need the axiom of choice here 
     it is basically exactly the definition of the axiom of choice *)
  assert (∥∏ i, ∑ li, ((f i) · li = hi i) × (li · g = ki i)∥) as ilift_aoc.
  {
    set (aocI := aoc I).
    simpl in aocI.
    apply (aocI).
    exact ilift.
  }

  (* obtain lift in original diagram *)
  assert (∃ (li : (∏ i, (b i --> x))), (∏ i, (f i) · (li i) = hi i × ((li i) · g = ki i))) as ilifts.
  {
    use (hinhuniv _ ilift_aoc).
    intro ilift_aoc_sig.
    apply hinhpr.
    
    use tpair.
    - intro i.
      set (li := ilift_aoc_sig i).
      destruct li as [l hl].
      exact l.
    - intro i.
      set (li := ilift_aoc_sig i).
      simpl.
      destruct li as [l hl].
      exact hl.
  }

  use (hinhuniv _ ilifts).
  intro ilift_sig.
  destruct ilift_sig as [li hli].

  (* turn individual lifts into lift from coproduct *)
  set (hl := isCoproduct_Coproduct _ _ CCb x li).
  destruct hl as [[l hl] uniqueness].
  
  apply hinhpr.
  exists l.
  (* factor maps through coproduct object *)
  split; rewrite CoproductArrowEta, (CoproductArrowEta _ _ _ _ _ l).
  - (* factor f as well *)
    rewrite (precompWithCoproductArrow).

    (* maps are equal if maps through coproduct are equal *)
    apply CoproductArrowUnique.

    (* now we can reason in separate diagrams again *)
    intro i.
    rewrite CoproductInCommutes.

    (* this is basically exactly the relation we want to prove: *)
    destruct (hli i) as [hlicomm _].

    (* by definition *)
    change (CoproductIn _ _ _ _ · h) with (hi i).
    rewrite (hl i).
    exact hlicomm.
  - (* factor through coproduct object *)
    apply CoproductArrowUnique.

    (* reason about separate diagrams again *)
    intro i.
    rewrite assoc.
    rewrite CoproductInCommutes.

    (* the relation we want to prove *)
    destruct (hli i) as [_ klicomm].

    (* by definition *)
    change (CoproductIn _ _ _ _ · k) with (ki i).
    rewrite (hl i).
    exact klicomm.
Qed.

(* Dual statement *)
Lemma wfs_closed_products {C : category} {I : hSet} (w : wfs C)
    {a b : I -> C} {f : ∏ (i : I), b i --> a i} 
    (hf : ∀ (i : I), (wfs_R w _ _) (f i))
    (CCa : Product _ _ a) (CCb : Product _ _ b)
    (aoc : AxiomOfChoice) : 
  (wfs_R w _ _) (ProductOfArrows _ _ CCa CCb f).
Proof.
  (* again superpowers by Coq *)
  apply (wfs_closed_coproducts (opp_wfs w)).
  exact hf.
Qed.

Lemma wfs_closed_transfinite_composition 
    {C : category}
    {d : chain C}
    {w : wfs C}
    (CC : ColimCocone d)
    (Hd : ∏ {u v : vertex nat_graph} (e : edge u v), wfs_L w _ _ (dmor d e)) 
    (aoc : AxiomOfChoice) :
  wfs_L w _ _ (colimIn CC 0).
Proof.
  unfold wfs_L in *.
  (* create square with g ∈ R *)
  rewrite (wfs_llp w) in *.

  intros a b g Rg h k hkcomm.
  
  transparent assert (Hind : (∏ (v : vertex nat_graph), ∃ (va : dob d v --> a), va · g = colimIn CC v · k)).
  {
    intro v.
    induction v as [|v Hv].
    - apply hinhpr.
      exists h.
      exact hkcomm.
    - transparent assert (lpSv : (∃ (lp : dmor d (idpath (S v)) --> g), arrow_mor11 lp = colimIn CC (S v) · k)). 
      {
        use (hinhuniv _ Hv).
        intro Hv'.
        apply hinhpr.
        use tpair.
        - use mors_to_arrow_mor.
          * exact (pr1 Hv').
          * exact (colimIn CC (S v) · k).
          * abstract (
              etrans; [exact (pr2 Hv')|];
              apply pathsinv0;
              etrans; [apply assoc|];
              apply cancel_postcomposition;
              exact (colimInCommutes CC _ _ (idpath (S v)))
            ).
        - reflexivity.
      }
      use (hinhuniv _ lpSv).
      clear lpSv; intro lpSv.
      set (fillv := Hd _ _ (idpath (S v)) _ _ _ Rg _ _ (arrow_mor_comm (pr1 lpSv))).
      use (hinhuniv _ fillv).
      clear fillv; intro fillv.
      apply hinhpr.
      exists (pr1 fillv).
      etrans; [exact (pr22 fillv)|].
      exact (pr2 lpSv).
  }

  assert (∥∏ v : vertex nat_graph, ∑ va : dob d v --> a, va · g = colimIn CC v · k∥) as Hind_aoc.
  {
    set (aocI := aoc natset).
    simpl in aocI.
    apply (aocI).
    exact Hind.
  }
  use (hinhuniv _ Hind_aoc).
  clear Hind Hind_aoc; intro Hind.
  apply hinhpr.

  use tpair.
  - use colimArrow.
    use make_cocone.
    * intro v.
      exact (pr1 (Hind v)).
    * intros u v e.
      simpl in e.
      rewrite <- e.
      admit. (* also follows from definition of Hind... *)
  - split.
    * etrans. apply colimArrowCommutes.
      cbn.
      admit.  (* true by definition of Hind... *)
    * use colimArrowUnique'.
      intro v.
      etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              apply colimArrowCommutes.
      exact (pr2 (Hind v)).
Qed.

(*
(i)   wfs_<X>_contains_isos
(ii)  wfs_<X>_retract
(iii) wfs_closed_<co>products
(iv)  wfs_closed_<pushouts|pullbacks>
(v)   wfs_closed_transfinite_composition

prove that L is left saturated, and R is right saturated in a WFS
or lemma 14.1.8
*)

Lemma llp_iff_lift_with_R {C : category} (w : wfs C) {x y : C} (f : x --> y) 
  (H : ∑ z (g : x --> z) (h : z --> y), (wfs_L w _ _) g × (wfs_R w _ _) h × h ∘ g = f) :
    lp (pr12 H) f <-> (wfs_R w _ _) f.
Proof.
  destruct H as [z [g [h [Lg [Rh Hgh]]]]].

  split.
  - intro hf.
    unfold wfs_R.
    rewrite (wfs_rlp w).

    intros a b g' hg'.
    intros top bottom comm_total.

    (* extract lp of λ_f and f (assumption) *)
    (* this diagram has a lift
       x ==== x
  λ_f  |      | f
       |      |
       Mf --> y
          ρ_f
    *)
    use (hf (identity _) h).
    {
      rewrite id_left.
      apply pathsinv0.

      exact (Hgh).
    }
    intro h'.
    (* extract lift *)
    destruct h' as [lift_lff [comm_lff1 comm_lff2]].
    
    (* Since ρ_f ∈ R, this diagram has a lift
        top     λ_f
      a ---> x ---> Mf
    g |             | ρ_f
      |             |
      b ----------> y
           bottom
    *)
    (* g and rf indeed have the rlp *)
    assert (lp g' h) as lp_grf.
    {
      set (rf_r := Rh).
      unfold wfs_R in rf_r.
      rewrite (wfs_rlp w) in rf_r.
      exact (rf_r _ _ g' hg').
    }

    (* extract this lift *)
    use (lp_grf (g ∘ top) bottom).
    {
      rewrite <- assoc.
      (* unfold wfs_left_map, wfs_right_map. *)
      rewrite (Hgh).
      exact comm_total.
    }

    intro H.
    destruct H as [lift_grf [comm_grf1 comm_grf2]].

    (* Compose lifts to get total lift *)
    apply hinhpr.
    exists (lift_lff ∘ lift_grf).

    (* diagram chasing *)
    split.
    * etrans. apply assoc.
      etrans. apply cancel_postcomposition.
              exact comm_grf1.
      etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              exact comm_lff1.
      apply id_right.
    * etrans. apply assoc'.
      etrans. apply cancel_precomposition.
              exact comm_lff2.
      exact comm_grf2.
  - (* this side is easy, we know that f has a lift for all functions in L, 
       so also for its factorization *)
    intro hf.
    intros h' k Hk.
    
    (* get factorization of f *)
    unfold wfs_R in hf.
    rewrite wfs_rlp in hf.
    use hf.
    exact (Lg).
Qed.

End properties.
