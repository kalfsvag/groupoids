Require Import HoTT.
From HoTT.Categories Require Import Category Functor NaturalTransformation.
Require Import GR.bicategories.bicategories.
Require Import GR.bicategories.lax_functors.
Require Import GR.bicategories.lax_transformations.
Require Import GR.bicategories.modifications.
Require Import GR.bicategories.biadjunction.biadjunction.
(* From GR.groupoid Require Import *)
(*      groupoid_quotient.gquot *)
(*      groupoid_quotient.gquot_functor *)
(*      groupoid_quotient.gquot_principles *)
(*      grpd_bicategory.grpd_bicategory *)
(*      path_groupoid.path_groupoid *)
(*      adjunction.unit *)
(*      adjunction.counit. *)
Require Import cquot_functor cquot_unit cquot_counit path_category.
From GR.basics Require Import
     general.


Section BiAdjunction.
  Context `{Univalence}.

  Definition cquot_biadjunction_d
    : BiAdjunction_d PreCat one_types
    := Build_BiAdjunction_d
         cquot_functor
         _
         path_category_functor
         _
         unit_cq
         counit_cq.
  
  Definition cquot_triangle_l_map_help
             {G : PreCategory}
             {a₁ a₂ : C}
             (g : C a₁ a₂)
    : path_over
        (fun h : cquot C =>
           counit_map (cquot_functor_obj C) (cquot_functor_map (unit_map C) h)
           = h) 
        (gcleq C g)
        1%path
        1%path.
  Proof.
    apply map_path_over ; apply path_to_square.
    rewrite ap_idmap.
    rewrite ap_compose.
    rewrite !cquot_rec_beta_ccleq.
    rewrite concat_1p, concat_p1.
    reflexivity.
  Qed.
  
  Definition cquot_triangle_l_map (G : PreCat)
    : forall x : cquot C,
      counit_map (cquot_functor_obj C) (cquot_functor_map (unit_map C) x) = x.
  Proof.
    simple refine (cquot_ind_set _ _ _ _).
    - reflexivity.
    - intros.
      apply cquot_triangle_l_map_help.
  Defined.

  Definition cquot_triangle_l_d
    : Modification_d
        (triangle_l_lhs cquot_biadjunction_d)
        (identity_transformation cquot_functor).
  Proof.
    intros C ; cbn.
    funext x ; revert x ; simpl.
    apply cquot_triangle_l_map.
  Defined.

  Definition cquot_triangle_l_is_modification
    : is_modification cquot_triangle_l_d.
  Proof.
    intros C₁ C₂ F.
    cbn.
    rewrite !concat_1p, !concat_p1.
    rewrite <- !path_forall_pp.
    f_ap.
    refine (path_forall _ _ _).
    simple refine (cquot_ind_prop _ _ _).
    intros a ; simpl.
    rewrite !concat_1p, !ap10_path_forall.
    rewrite ap_idmap, !concat_1p.
    unfold cquot_triangle_l_map ; simpl.
    rewrite !concat_p1.
    rewrite cquot_rec_beta_ccleq.
    reflexivity.
  Qed.

  Definition cquot_triangle_l_modification
    : Modification
        (triangle_l_lhs cquot_biadjunction_d)
        (identity_transformation cquot_functor)
    := Build_Modification cquot_triangle_l_d cquot_triangle_l_is_modification.

  Definition cquot_triangle_l_is_iso
    : iso_modification cquot_triangle_l_modification.
  Proof.
    intros X ; cbn.
    apply one_types_is_21.
  Defined.

  Definition cquot_triangle_l
    : IsoModification
        (triangle_l_lhs cquot_biadjunction_d)
        (identity_transformation cquot_functor).
  Proof.
    make_iso_modification.
    - exact cquot_triangle_l_modification.
    - exact cquot_triangle_l_is_iso.
  Defined.
  
  Definition cquot_triangle_r_d
    : Modification_d
        (triangle_r_lhs cquot_biadjunction_d)
        (identity_transformation path_category_functor).
  Proof.
    intros A ; simpl.
    simple refine (Build_NaturalTransformation _ _ _ _).
    - reflexivity.
    - intros F C α ; cbn in *.
      refine (concat_p1 _ @ _ @ (concat_1p _)^).
      exact (cquot_rec_beta_ccleq _ _ _ _ _ _ _ _ _ _).
  Defined.

  Definition cquot_triangle_r_is_modification
    : is_modification cquot_triangle_r_d.
  Proof.
    intros A B f.
    apply path_natural_transformation.
    intros x.
    cbn.
    rewrite ge, !concat_1p.
    rewrite !ap10_path_forall ; simpl.
    rewrite !ge ; simpl.
    reflexivity.
  Qed.

  Definition cquot_triangle_r_modification
    : Modification
        (triangle_r_lhs cquot_biadjunction_d)
        (identity_transformation path_category_functor)
    := Build_Modification cquot_triangle_r_d cquot_triangle_r_is_modification.

  Global Instance cquot_triangle_r_is_iso
    : iso_modification cquot_triangle_r_modification.
  Proof.
    intros A ; simpl.
    unfold cquot_triangle_r_d ; simpl.
    apply _.
  Defined.

  Definition cquot_triangle_r
    : IsoModification
        (triangle_r_lhs cquot_biadjunction_d)
        (identity_transformation path_category_functor).
  Proof.
    make_iso_modification.
    - exact cquot_triangle_r_modification.
    - exact cquot_triangle_r_is_iso.
  Defined.
  
  Definition cquot_is_biadjunction
    : is_biadjunction cquot_biadjunction_d
    := Build_is_biadjunction _ _ cquot_triangle_l cquot_triangle_r.

  Definition cquot_biadjunction
    : BiAdjunction PreCat one_types
    := Build_BiAdjunction cquot_biadjunction_d cquot_is_biadjunction.
End BiAdjunction.