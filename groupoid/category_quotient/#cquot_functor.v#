Require Import HoTT.
From HoTT.Categories Require Import
     Functor NaturalTransformation.
Require Import GR.bicategories.bicategories.
Require Import GR.bicategories.lax_functors.
From GR.basics Require Import
     general.
(* From GR.groupoid.groupoid_quotient Require Export *)
(*      gquot. *)
From GR.groupoid Require Import
     grpd_bicategory.grpd_bicategory.
(*      groupoid_quotient.gquot_principles. *)
Require Export cquot.
Require Import cquot_principles.


Section CQuotFunctor.
  Context `{Univalence}.
  
  Definition cquot_functor_obj (C : PreCategory)
    : 1 -Type
    := BuildTruncType 1 (cquot C).

  Definition cquot_functor_map
             {C₁ C₂ : PreCat}
             (F : Functor C₁ C₂)
    : cquot_functor_obj C₁ -> cquot_functor_obj C₂.
  Proof.
    simple refine (cquot_rec _ _ _ _ _).
    - exact (fun c => ccl C₂ (F c)).
    - exact (fun _ _ c => ccleq C₂ (morphism_of F c)).
    - exact (fun a => ap (ccleq C₂) (identity_of F _) @ ce _ _).
    - exact (fun _ _ _ c₁ c₂ => ap (ccleq C₂) (composition_of F _ _ _ c₁ c₂)
                                   @ cconcat _ _ _).
  Defined.

  Definition cquot_functor_map_natural_po
             {C₁ C₂ : PreCategory}
             {F₁ F₂ : Functor C₁ C₂}
             (α : NaturalTransformation F₁ F₂)
             {x₁ x₂ : C₁}
             (c : C₁ x₁ x₂)
    : path_over
        (fun h : cquot C₁ => cquot_functor_map F₁ h = cquot_functor_map F₂ h)
        (ccleq C₁ c)
        (ccleq C₂ (α x₁))
        (ccleq C₂ (α x₂)).
  Proof.
    apply map_path_over.
    refine (whisker_square idpath
                           _
                           _
                           idpath
                           _).
    - exact (cquot_rec_beta_ccleq _ _ _ _ _ _ _ _ _ _)^.
    - exact (cquot_rec_beta_ccleq _ _ _ _ _ _ _ _ _ _)^.
    - apply path_to_square.
      refine ((cconcat _ _ _)^ @ ap (ccleq C₂) _ @ cconcat _ _ _).
      exact (commutes α _ _ c).
  Qed.

  Definition cquot_functor_map_natural
             {C₁ C₂ : PreCat}
             {F₁ F₂ : Functor C₁ C₂}
             (α : NaturalTransformation F₁ F₂)
    : forall (x : cquot C₁),
      cquot_functor_map F₁ x = cquot_functor_map F₂ x.
  Proof.
    simple refine (cquot_ind_set _ _ _ _).
    - exact (fun x => ccleq C₂ (α x)).
    - apply cquot_functor_map_natural_po.
  Defined.

  Definition cquot_functor_map_compose_po
             {C₁ C₂ C₃ : PreCategory}
             (F₂ : Functor C₂ C₃)
             (F₁ : Functor C₁ C₂)
             {x₁ x₂ : C₁}
             (c : C₁ x₁ x₂)
    : path_over
        (fun h : cquot C₁ =>
           (cquot_functor_map F₂ o cquot_functor_map F₁) h
           =
           cquot_functor_map (F₂ o F₁) h)
        (ccleq C₁ c)
        idpath
        idpath.
  Proof.
    apply map_path_over.
    refine (whisker_square idpath
                           _
                           _
                           idpath
                           _).
    - unfold cquot_functor_map.
      refine (_ @ (ap_compose _ _ _)^).
      refine (_ @ ap (ap _) (cquot_rec_beta_ccleq _ _ _ _ _ _ _ _ _ _)^).
      exact (cquot_rec_beta_ccleq _ _ _ _ _ _ _ _ _ _)^.
    - exact (cquot_rec_beta_ccleq _ _ _ _ _ _ _ _ _ _)^.
    - apply vrefl.
  Qed.
  
  Definition cquot_functor_map_compose
             {C₁ C₂ C₃ : PreCat}
             (F₂ : Functor C₂ C₃)
             (F₁ : Functor C₁ C₂)
    : forall (x : cquot C₁),
      (cquot_functor_map F₂ o cquot_functor_map F₁) x
      =
      cquot_functor_map (F₂ o F₁)%functor x.
  Proof.
    simple refine (cquot_ind_set _ _ _ _).
    - reflexivity.
    - apply cquot_functor_map_compose_po.
  Defined.

  Definition cquot_functor_map_id_po
             (C : PreCategory)
             {x₁ x₂ : C}
             (c : C x₁ x₂)
    : path_over
        (fun h : cquot C => h = cquot_functor_map 1 h)
        (ccleq C c)
        idpath
        idpath.
  Proof.
    apply map_path_over.
    refine (whisker_square idpath
                           ((ap_idmap _)^)
                           _
                           idpath
                           (vrefl _)).
    exact (cquot_rec_beta_ccleq _ _ _ _ _ _ _ _ _ _)^.
  Qed.

  Definition cquot_functor_map_id (C : PreCat)
    : forall (x : cquot C),
      x = cquot_functor_map 1%functor x.
  Proof.
    simple refine (cquot_ind_set _ _ _ _).
    - reflexivity.
    - apply cquot_functor_map_id_po.
  Defined.

  Definition cquot_functor_rd
    : PseudoFunctor_d PreCat one_types.
  Proof.
    make_pseudo_functor.
    - exact cquot_functor_obj.
    - intros ? ? F; cbn.
      exact (cquot_functor_map F).
    - intros C₁ C₂ F₁ F₂ α ; cbn in *.
      funext x ; revert x.
      exact (cquot_functor_map_natural α).
    - intros C₁ C₂ C₃ F₁ F₂ ; cbn.
      funext x ; revert x.
      exact (cquot_functor_map_compose F₁ F₂).
    - intros C ; cbn.
      funext x ; revert x.
      exact (cquot_functor_map_id C).
    - intros C₁ C₂ C₃ F₁ F₂ ; cbn.
      funext x.
      exact (cquot_functor_map_compose F₁ F₂ x)^.
    - intros C ; cbn.
      funext x.
      exact (cquot_functor_map_id C x)^.
  Defined.

  Definition cquot_functor_rd_is_pseudo
    : is_pseudo_functor_p cquot_functor_rd.
  Proof.
    make_is_pseudo.
    - intros X Y f ; cbn in *.
      rewrite <- path_forall_1.
      f_ap.
      funext x ; revert x.
      simple refine (cquot_ind_prop _ _ _).
      intros a ; simpl.
      apply ce.
    - intros C₁ C₂ F₁ F₂ F₃ α₁ α₂ ; cbn in *.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (cquot_ind_prop _ _ _).
      intros a ; simpl.
      apply cconcat.
    - intros C₁ C₂ C₃ F₁ F₂ F₃ F₄ α₁ α₂ ; cbn in *.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (cquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite !ap10_path_forall ; simpl.
      rewrite cquot_rec_beta_ccleq.
      rewrite concat_1p, concat_p1.
      rewrite <- cconcat.
      f_ap.
      apply α₂.
    - intros C₁ C₂ f ; cbn.
      rewrite <- !path_forall_pp.
      rewrite <- path_forall_1.
      f_ap.
      funext x ; revert x.
      simple refine (cquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite !concat_1p.
      rewrite ap10_path_forall ; simpl.
      rewrite concat_1p, ce.
      reflexivity.
    - intros C₁ C₂ F ; cbn.
      rewrite <- !path_forall_pp.
      rewrite <- path_forall_1.
      f_ap.
      funext x ; revert x.
      simple refine (cquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite ap10_path_forall ; simpl.
      rewrite ce.
      reflexivity.
    - intros C₁ C₂ C₃ C₄ F₁ F₂ F₃ ; cbn.
      rewrite <- path_forall_1.
      rewrite <- !path_forall_pp.
      f_ap.
      funext x ; revert x.
      simple refine (cquot_ind_prop _ _ _).
      intros a ; simpl.
      rewrite !ap10_path_forall ; simpl.
      rewrite ce.
      reflexivity.
    - intros C₁ C₂ C₃ F₁ F₂ ; cbn.
      rewrite path_forall_V.
      apply concat_pV.
    - intros C₁ C₂ C₃ F₁ F₂ ; cbn.
      rewrite path_forall_V.
      apply concat_Vp.
    - intros C ; cbn.
      rewrite path_forall_V.
      apply concat_Vp.
    - intros C ; cbn.
      rewrite path_forall_V.
      apply concat_pV.
  Qed.

  Definition cquot_functor
    : PseudoFunctor PreCat one_types
    := Build_PseudoFunctor cquot_functor_rd cquot_functor_rd_is_pseudo.
End CQuotFunctor.