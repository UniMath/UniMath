(** Authors:
 - Anthony Bordg, March-April 2017
 - Langston Barrett (@siddharthist), November-December 2017 *)

Require Import UniMath.Algebra.Rigs_and_Rings.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.Algebra.Modules.
Require Import UniMath.Algebra.Modules.Examples.
Require Import UniMath.CategoryTheory.limits.zero.

(** * Contents:

- The category of (left) R-modules ([mod_category])
- Mod is a univalent category ([is_univalent_mod])
- Abelian structure
 - Zero object and zero arrow
 - Preadditive structure
 - Additive structure
*)

Section Mod.

Local Open Scope cat.

Context {R : rng}.

(** * The category of (left) R-modules ([mod_category]) *)

Definition mod_precategory_ob_mor : precategory_ob_mor :=
  precategory_ob_mor_pair (module R) (λ M N, modulefun M N).

Definition mod_precategory_data : precategory_data :=
  precategory_data_pair
    mod_precategory_ob_mor (λ (M : module R), (idfun M,, id_modulefun M))
    (fun M N P => @modulefun_comp R M N P).

Lemma is_precategory_mod_precategory_data :
  is_precategory (mod_precategory_data).
Proof.
  apply dirprodpair.
  - apply dirprodpair.
    + intros M N f.
      use total2_paths_f.
      * apply funextfun. intro x. apply idpath.
      * apply isapropismodulefun.
    + intros M N f.
      use total2_paths_f.
      * apply funextfun. intro x. apply idpath.
      * apply isapropismodulefun.
  - intros M N P Q f g h.
    use total2_paths_f.
    + apply funextfun. intro x.
      unfold compose. cbn.
      rewrite funcomp_assoc.
      apply idpath.
    + apply isapropismodulefun.
Defined.

Definition mod_precategory : precategory :=
  mk_precategory (mod_precategory_data) (is_precategory_mod_precategory_data).

Definition has_homsets_mod : has_homsets mod_precategory := isasetmodulefun.

Definition mod_category : category := category_pair mod_precategory has_homsets_mod.

Definition mor_to_modulefun {M N : ob mod_category} : mod_category⟦M, N⟧ -> modulefun M N := idfun _.

(** Mod is a univalent category ([Mod_is_univalent]) *)

Definition modules_univalence_weq (M N : mod_precategory) : (M ╝ N) ≃ (moduleiso' M N).
Proof.
   use weqbandf.
   - apply abgr_univalence.
   - intro e.
     use invweq.
     induction M. induction N. cbn in e. induction e.
     use weqimplimpl.
     + intro i.
       use total2_paths2_f.
       * use funextfun. intro r.
         use total2_paths2_f.
           apply funextfun. intro x. exact (i r x).
           apply isapropismonoidfun.
       * apply isapropisrigfun.
     + intro i. cbn.
       intros r x.
       unfold idmonoidiso. cbn in i.
       induction i.
       apply idpath.
     + apply isapropislinear.
     + apply isasetrigfun.
Defined.

Definition modules_univalence_map (M N : mod_precategory) : (M = N) -> (moduleiso M N).
Proof.
   intro p.
   induction p.
   exact (idmoduleiso M).
Defined.

Definition modules_univalence_map_isweq (M N : mod_precategory) : isweq (modules_univalence_map M N).
Proof.
   use isweqhomot.
   - exact (weqcomp (weqcomp (total2_paths_equiv _ M N) (modules_univalence_weq M N)) (moduleiso'_to_moduleiso_weq M N)).
   - intro p.
     induction p.
     apply (pathscomp0 weqcomp_to_funcomp_app).
     apply idpath.
   - apply weqproperty.
Defined.

Definition modules_univalence (M N : mod_precategory) : (M = N) ≃ (moduleiso M N).
Proof.
   use weqpair.
   - exact (modules_univalence_map M N).
   - exact (modules_univalence_map_isweq M N).
Defined.

(** Equivalence between isomorphisms and moduleiso in Mod R *)

Lemma iso_isweq {M N : ob mod_precategory} (f : iso M N) :
  isweq (pr1modulefun (morphism_from_iso _ _ _ f)).
Proof.
   use (gradth (pr1modulefun (morphism_from_iso _ _ _ f))).
   - exact (pr1modulefun (inv_from_iso f)).
   - intro; set (T:= iso_inv_after_iso f).
     apply subtypeInjectivity in T.
     + apply (toforallpaths _ _ _ T).
     + intro; apply isapropismodulefun.
   - intro; set (T:= iso_after_iso_inv f).
     apply subtypeInjectivity in T.
     + apply (toforallpaths _ _ _ T).
     + intro; apply isapropismodulefun.
Defined.

Lemma iso_moduleiso (M N : ob mod_precategory) : iso M N -> moduleiso M N.
Proof.
   intro f.
   use mk_moduleiso.
   - use weqpair.
     + exact (pr1modulefun (morphism_from_iso _ _ _ f)).
     + exact (iso_isweq f).
   - exact (modulefun_ismodulefun (morphism_from_iso _ _ _ f)).
Defined.

Lemma moduleiso_is_iso {M N : ob mod_precategory} (f : moduleiso M N) :
  @is_iso _ M N (moduleiso_to_modulefun f).
Proof.
   apply (is_iso_qinv (C:= mod_precategory) _ (modulefunpair (invmoduleiso f) (pr2 (invmoduleiso f)))).
   split; use total2_paths_f.
    + apply funextfun. intro.
      unfold funcomp, idfun.
      apply homotinvweqweq.
    + apply isapropismodulefun.
    + apply funextfun. intro.
      apply homotweqinvweq.
    + apply isapropismodulefun.
Defined.

Lemma moduleiso_iso (M N : ob mod_precategory) : moduleiso M N -> iso M N.
Proof.
   intro f.
   use isopair.
   - exact (moduleiso_to_modulefun f).
   - exact (moduleiso_is_iso f).
Defined.

Lemma moduleiso_iso_isweq (M N : ob mod_precategory) : isweq (@moduleiso_iso M N).
Proof.
   apply (gradth _ (iso_moduleiso M N)).
   - intro.
     apply subtypeEquality.
     + intro; apply isapropismodulefun.
     + unfold moduleiso_iso, iso_moduleiso.
       use total2_paths_f.
       * apply idpath.
       * apply isapropisweq.
   - intro; unfold iso_moduleiso, moduleiso_iso.
     use total2_paths_f.
     + apply idpath.
     + apply isaprop_is_iso.
Defined.

Definition moduleiso_iso_weq (M N : mod_precategory) : (moduleiso M N) ≃ (iso M N) :=
   weqpair (moduleiso_iso M N) (moduleiso_iso_isweq M N).

Definition mod_precategory_idtoiso_isweq :
  ∏ M N : mod_precategory, isweq (fun p : M = N => idtoiso p).
Proof.
   intros M N.
   use (isweqhomot (weqcomp (modules_univalence M N) (moduleiso_iso_weq M N)) _).
   - intro p.
     induction p.
     use (pathscomp0 weqcomp_to_funcomp_app). cbn.
     use total2_paths_f.
     + apply idpath.
     + apply isaprop_is_iso.
   - apply weqproperty.
Defined.

Definition is_univalent_mod : is_univalent mod_precategory :=
  mk_is_univalent mod_precategory_idtoiso_isweq has_homsets_mod.

Definition univalent_category_mod_precategory : univalent_category := mk_category mod_precategory is_univalent_mod.

(** * Abelian structure *)

(** ** Zero object and zero arrow
- The zero object (0) is the zero abelian group, considered as a module.
- The type (hSet) Hom(0, M) is contractible, the center is the zero map.
- The type (hSet) Hom(M, 0) is contractible, the center is the zero map.
 *)

(** ** Zero in abelian category *)

(** The set of maps 0 -> M is contractible, it only contains the zero morphism. *)
Lemma iscontrfromzero_module (M : mod_category) : iscontr (mod_category⟦zero_module R, M⟧).
Proof.
  refine (unelmodulefun _ _,, _).
  intros f; apply modulefun_paths; intros x.
  unfold unelmodulefun; cbn.
  refine (!maponpaths (fun z => (pr1 f) z)
           (isProofIrrelevantUnit (@unel (zero_module R)) x) @ _).
  apply (monoidfununel (modulefun_to_monoidfun f)).
Defined.

(** The set of maps M -> 0 is contractible, it only contains the zero morphism. *)
Lemma iscontrtozero_module (M : mod_category) : iscontr (mod_category⟦M, zero_module R⟧).
Proof.
  refine (unelmodulefun _ _,, _).
  intros f; apply modulefun_paths.
  exact (fun x => isProofIrrelevantUnit _ _).
Defined.

Lemma isZero_zero_module : isZero mod_category (zero_module R).
Proof.
  exact (@mk_isZero mod_category (zero_module _)
                    iscontrfromzero_module iscontrtozero_module).
Defined.

Definition mod_category_Zero : Zero mod_category :=
  @mk_Zero mod_category (zero_module _) isZero_zero_module.

(** ** Preadditive structure *)

(** ** Additive structure *)

End Mod.
